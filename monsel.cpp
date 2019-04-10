//
// Created by mcangny on 2019-04-10.
//
#include "monsel.h"
#include "utils.h"
#include "logging.h"

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <argp.h>
#include <stdint.h>
#include <unistd.h>
#include <limits.h>
#include "hv.h"
// TODO: Use adjacency list in penalty?

// typedefs and structs



// HEADER

Fitness fitness(Individual *ind, NetworkModel *model);

int nreal;
int nbin;
int nobj;
int ncon;
int popsize;
int *nbits;
int random_immigrant_ratio;
double *min_binvar;
double *max_binvar;

#include "global.h"
#include <random>
// functions

/*
 * Calculates the standard deviation of an arbitrary long array
 * For performance reasons, the mean should be precalculated and given.
 */
double long_stdev(long *arr, int size, double mean)
{
    double sum = 0;
    for(int i=0; i<size; i++)
        sum += pow(arr[i] - mean, 2);
    return sqrt(sum / (double)size);
}

/*
 * Calculates mean of an arbitrary long array
 */
double long_mean(long *arr, int size)
{
    long sum = 0;
    for(int i=0; i<size; i++)
        sum += arr[i];
    return (sum / (double)size);
}

/*
 * Calculates the standard deviation of an arbitrary double array
 * For performance reasons, the mean should be precalculated and given.
 */
double double_stdev(double *arr, int size, double mean)
{
    double sum = 0;
    for(int i=0; i<size; i++)
        sum += pow(arr[i] - mean, 2);
    return sqrt(sum / (double)size);
}

/*
 * Calculates mean of an arbitrary double array
 */
double double_mean(double *arr, int size)
{
    double sum = 0;
    for(int i=0; i<size; i++)
        sum += arr[i];
    return (sum / (double)size);
}

/*
 * Creates an array of n distinct integer values in the range from 0 to size
 */
void distinct_random_values(int *values, long size)
{
    for(int i=0; i<size; i++)
        values[i] = i;
    for(int i=size-1; i>=0; i--)
    {
        int swapto = rand() % size;
        SWAP_LVALUE(int, tmp, values[swapto], values[i]);
    }
}

/*
 * Checks for the best individual in the population and returns the index to it.
 */
long best_individual_idx(Population *pop)
{
    int idx = 0;
    for(int j=1; j<pop->size; j++)
    {
        if(pop->ind[j].fitness < pop->ind[idx].fitness)
            idx = j;
    }
    return idx;
}

/*
 * Creates a random diff according to the level of
 * change given in the parameters.
 */
void create_diff(NetworkModel* model, struct ea_parameters* params)
{
    // Set all vertices/edges to active set active edge indices and increase model ID
    long vdiffcount = (int)(model->vcount * params->changelevel);
    for(int i=0; i<model->vcount; i++)
    {
        model->vertices[i].active = 1;
        model->active_vertex_idx[i] = i;
    }
    for(int i=0; i<model->ecount; i++)
    {
        model->edges[i].active = 1;
        model->active_edge_idx[i] = i;
    }
    model->id += 1;
    model->active_ecount = model->ecount;
    model->active_ecount_w = model->ecount_w;
    model->active_vcount = model->vcount;

    // Start diffing
    for(long i=0; i<vdiffcount; i++)
    {
        long idx = -1;
        do{
            idx = lrand48() % model->vcount;
        } while(!model->vertices[idx].active);
        model->vertices[idx].active = 0;
        model->active_vertex_idx[idx] = model->active_vertex_idx[--model->active_vcount];
        for(long j=0; j<model->adjlist[idx].size; j++)
        {
            long edge_idx = model->adjlist[idx].edge_indices[j];
            model->edges[edge_idx].active = 0;
            model->active_edge_idx[edge_idx] = model->active_edge_idx[--model->active_ecount];
            model->active_ecount_w -= model->edges[edge_idx].w;
        }
    }
}

/*
 * Reads the given file according to its filename and fills the edges into the NetworkModel.
 * The model will be filled with the number of vertices (vcount) the number of edges (ecount),
 * an array of edges containing edge information (src, dst, weight, active) and an array of vertices.
 * Returns the number of lines read or -1 in case of failure
 */
int read_base_file(NetworkModel *model, const char* fname)
{
    FILE *fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    long j=0, i=0, ecount = 0, vcount = 0;
    fp = fopen(fname, "r");
    if(fp == NULL)
        return -1;
    while ((read = getline(&line, &len, fp)) != -1) {
        if(line[0] == 'E')
            ecount++;
        else
            vcount++;
    }
    model->id = -1;
    model->ecount = ecount;
    model->active_ecount = ecount;
    model->vcount = vcount;
    model->active_vcount = vcount;
    model->ecount_w = 0;
    rewind(fp);
    Vertex *vertices;
    vertices = new Vertex[vcount];
    Edge *edges;
    edges = new Edge[ecount];
    model->adjlist = new AdjacencyList[model->vcount];
    model->active_edge_idx = new int[ecount];
    model->active_vertex_idx = new int[vcount];
    while ((read = getline(&line, &len, fp)) != -1) {
        char* classs = strtok(line, ",");
        if((*classs) == 'E')
        {
            edges[i].active = 1;
            edges[i].src = atoi(strtok(NULL, ","));
            edges[i].dst = atoi(strtok(NULL, ","));
            edges[i].w = atoi(strtok(NULL, ","));
            model->active_edge_idx[i] = i;
            model->ecount_w += edges[i].w;
            i++;
        }
        else if((*classs) == 'V')
        {
            vertices[j].active = 1;
            vertices[j].id = atoi(strtok(NULL, ","));
            model->active_vertex_idx[j] = j;
            j++;
        }
    }
    model->active_ecount_w = model->ecount_w;
    model->edges = edges;
    model->vertices = vertices;

    // build adjacencylist
    for(long i=0; i<model->vcount; i++)
    {
        int adjcount = 0;
        long *adjidx = new long[model->ecount];
        for(long j=0; j<model->ecount; j++)
        {
            if(model->edges[j].src == i || model->edges[j].dst == i)
            {
                adjidx[adjcount++] = j;
            }
        }
        model->adjlist[i].edge_indices = new unsigned long[ adjcount];
        for(long j=0; j<adjcount; j++)
        {
            model->adjlist[i].edge_indices[j] = adjidx[j];
        }
        model->adjlist[i].size = adjcount;
        free(adjidx);
    }
    fclose(fp);
    if (line) free(line);
    return ecount + vcount;
}

/*
 * Writes header containing timing and PI information to file.
 * If file exists, appending to existing file.
 * Returns 1 if successful, -1 if not
 */
int write_meta_header(time_t timing, int pi_trigger, char* fname)
{
    FILE *f;
    f = fopen(fname, "a");
    if(f==NULL)
    {
        printf("Unable to open file '%s' for writing.\n", fname);
        return -1;
    }
    fprintf(f, "%ld,%d\n", timing, pi_trigger);
    fclose(f);
    return 1;
}

/*
 * Writes given fitness values into given textfile, one per line.
 * If file exists, appending to existing file.
 * Returns 1 if successful, -1 if not
 */
int write_fitness(FitnessWrite *values, int size, char* fname, uint8_t extended, int generation)
{
    FILE *f;
    f = fopen(fname, "a");
    if(f==NULL)
    {
        printf("Unable to open file '%s' for writing.\n", fname);
        return -1;
    }
    fprintf(f, "generation it takes: %d\n", generation);

    if(extended)
    {
        fprintf(f, "fitness,active ecount,active ecount weighted,uncovered edges,uncovered edges weighted,active vcount,moncount\n");
        for(int i=0; i<size; i++)
            fprintf(f, "%ld,%ld,%ld,%ld,%ld,%ld,%ld\n", values[i].fitness, values[i].active_ecount, values[i].active_ecount_w, values[i].u_edges, values[i].u_edges_w, values[i].active_vcount, values[i].moncount);
    }
    else
    {
        for(int i=0; i<size; i++)
            fprintf(f, "%ld\n", values[i].fitness);
    }
    fclose(f);
    return 1;
}

/*
 * Writes all GenerationData values file as *.csv.
 * If file exists, appending to existing file.
 * Returns 1 if successful, -1 if not
 */
int write_generation_data(GenerationData* data, int size, char* fname)
{
    FILE *f;
    f = fopen(fname, "a");
    if(f==NULL)
    {
        printf("Unable to open file '%s' for writing.\n", fname);
        return -1;
    }
    fprintf(f, "mean edges,std edges,mean edges weighted,std edges weighted,mean moncount,std moncount\n");
    for(int i=0; i<size; i++)
    {
        fprintf(f, "%f,%f,%f,%f,%f,%f\n", data[i].mean_edges, data[i].std_edges, data[i].mean_edges_w, data[i].std_edges_w, data[i].mean_moncount, data[i].std_moncount);
    }
    fclose(f);
    return 1;
}


/*
 * Writes all fitness values of the given population to a file (in one line) as *.csv.
 * Evaluation is done on demand while writing and does not count to the evaluation count.
 * If file exists, appending to existing file.
 * Returns 1 if successful, -1 if not
 */
int write_generation_fitness(Population* pop, NetworkModel* model, char* fname)
{
    FILE *f;
    f = fopen(fname, "a");
    if(f==NULL)
    {
        printf("Unable to open file '%s' for writing.\n", fname);
        return -1;
    }
    for(int i=0; i<pop->size; i++)
    {
        if(i == (pop->size - 1))
            fprintf(f, "%ld\n", fitness(&pop->ind[i], model));
        else
            fprintf(f, "%ld,", fitness(&pop->ind[i], model));
    }
    fclose(f);
    return 1;
}

/*
 * Calculates and returns the number of uncovered edges according to the given edge model and individual.
 */
int uncovered_edges(Individual *ind, NetworkModel *model)
{
    int u_edges = 0;
    for(int i=0; i<model->active_ecount; i++)
    {
        if(ind->values[model->edges[model->active_edge_idx[i]].src] == 0 && ind->values[model->edges[model->active_edge_idx[i]].dst] == 0)
        {
            u_edges += 1;
        }
    }
    return u_edges;
}

/*
 * Calculates and returns the number of covered edges according to the given edge model and individual.
 */
int covered_edges(Individual *ind, NetworkModel *model)
{
    int u_edges = 0;
    for(int i=0; i<model->active_ecount; i++)
    {
        if(ind->values[model->edges[model->active_edge_idx[i]].src] == 0 && ind->values[model->edges[model->active_edge_idx[i]].dst] == 0)
        {
            u_edges += 1;
        }
    }

    int covered_edges = model->active_ecount - u_edges;

    return covered_edges;
}

/*
 * Calculates and returns the penalty according to the given edge model and individual.
 */
int penalty(Individual *ind, NetworkModel *model)
{
    int pen = 0;
    int factor = 2;
    for(int i=0; i<model->active_ecount; i++)
    {
        if(ind->values[model->edges[model->active_edge_idx[i]].src] == 0 && ind->values[model->edges[model->active_edge_idx[i]].dst] == 0)
        {
            pen += factor * model->edges[i].w;
        }
    }
    return pen;
}

/*
 * Fills the given variables with the amount of uncovered edges and the penalty value
 */
void uncovered_edges_and_penalty(Individual* ind, NetworkModel *model, unsigned long* u_edges, unsigned long* pen)
{
    (*u_edges) = 0;
    (*pen) = 0;
    int factor = 2;
    for(int i=0; i<model->active_ecount; i++)
    {
        if(ind->values[model->edges[model->active_edge_idx[i]].src] == 0 && ind->values[model->edges[model->active_edge_idx[i]].dst] == 0)
        {
            (*pen) += factor * model->edges[i].w;
            (*u_edges) += 1;
        }
    }
}


FitnessWrite fitness_ext(Individual *ind, NetworkModel *model)
{
    FitnessWrite retval;
    retval.moncount = 0;
    for(int i=0; i<ind->size; i++)
    {
        if(model->vertices[i].active)
            retval.moncount += ind->values[i];
    }
    uncovered_edges_and_penalty(ind, model, &retval.u_edges, &retval.u_edges_w);
    retval.fitness = retval.moncount + retval.u_edges_w;
    retval.active_vcount = model->active_vcount;
    retval.active_ecount = model->active_ecount;
    retval.active_ecount_w = model->active_ecount_w;

    ind->obj[0] = retval.moncount;
    ind->obj[1] = retval.u_edges_w;
    return retval;
}

/*
 * Calculates and returns the fitness values according to the given edge model and individual.
 * The fitness value already includes the penalty value.
 */
Fitness fitness(Individual *ind, NetworkModel *model)
{
    Fitness pen = 0, fit = 0;
    for(int i=0; i<model->active_vcount; i++)
        fit += ind->values[model->active_vertex_idx[i]];
    pen = penalty(ind, model);
    return fit + pen;

}

/*
 * Second objective function which is covered edges(weight)
 * The fitness value already includes the penalty value.
 */
Fitness fitness_covered_edges(Individual *ind, NetworkModel *model)
{
    Fitness pen = 0, fit = 0;
    for(int i=0; i<model->active_vcount; i++)
        fit += ind->values[model->active_vertex_idx[i]];
    //pen = penalty(ind, model);
    //return fit + pen;
    return fit;
}

/*
 * Creates an initialized individual with 0 values of'size' size and a fitness of -1 (unitialized).
 */
void create_null_individual(Individual *ind, int size)
{
    ind->values = new Gene[size];
    for(int i=0; i<size; i++)
    {
        ind->values[i] = 0;
    }
    ind->size = size;
    ind->fitness = -1;
    ind->obj = new double[nobj];
}

/*
 * Creates an initialized individual with random values of size 'size' and a fitness of -1 (unititialized).
 */
void create_random_individual(Individual *ind, int size)
{
    ind->values = new Gene[size];
    for(int i=0; i<size; i++)
    {
        ind->values[i] = rand() % 2;
    }
    ind->size = size;
    ind->fitness = -1;
    ind->obj = new double[nobj];
}

/*
 * Creates a GenerationData struct filled with the information about the given generation and network model
 */
GenerationData create_generation_data(Population* pop, NetworkModel* model)
{
    double edges[pop->size];
    double edges_w[pop->size];
    double moncount[pop->size];
    for(int i=0; i<pop->size; i++)
    {
        FitnessWrite tmp = fitness_ext(&pop->ind[i], model);
        edges[i] = 1 - (tmp.u_edges / (double)tmp.active_ecount);
        edges_w[i] = 1 - (tmp.u_edges_w / (double)tmp.active_ecount_w);
        moncount[i] = tmp.moncount / (double)tmp.active_vcount;
    }

    GenerationData data;
    data.mean_edges = double_mean(edges, pop->size);
    data.std_edges = double_stdev(edges, pop->size, data.mean_edges);
    data.mean_edges_w = double_mean(edges_w, pop->size);
    data.std_edges_w = double_stdev(edges_w, pop->size, data.mean_edges_w);
    data.mean_moncount = double_mean(moncount, pop->size);
    data.std_moncount = double_stdev(moncount, pop->size, data.mean_moncount);
    return data;
}

/*
 * Frees the memory of the given individual
 */
void free_individual(Individual *ind)
{
    free(ind->values);
}

/*
 * Frees the memory for the whole population
 */
void free_population(Population *pop)
{
    for(int i=0; i<pop->size; i++)
        free_individual(&pop->ind[i]);
    free(pop->ind);
}

/*
 * Frees the memory of the given NetworkModel
 */
void free_model(NetworkModel *model)
{
    for(long i=0; i<model->vcount; i++)
    {
        free(model->adjlist[i].edge_indices);
    }
    free(model->edges);
    free(model->vertices);
    free(model->active_edge_idx);
    free(model->active_vertex_idx);
    free(model->adjlist);
}

void print_config(struct ea_parameters *params)
{
    printf("<Experiment parameters>\n");
    printf("\tInputfile:\t\t%s\n", params->inputfname);
    printf("\tOutputfile fitness:\t%s\n", params->savefname ? params->savefname : "not saved");
    printf("\tOutputfile generation:\t%s\n", params->genfname ? params->genfname : "not saved");
    printf("\tExtended Write:\t\t%s\n", params->extended_write ? "yes" : "no");
    printf("\tPopsize:\t\t%ld\n", params->popsize);
    printf("\tTournsize:\t\t%ld\n", params->tournsize);
    printf("\tMutationprob:\t\t%.4f\n", params->mutpb);
    printf("\tMax evals:\t\t%ld\n", params->max_evals);
    printf("\tModel count:\t\t%ld\n", params->modelcount);
    printf("\tVerbose:\t\t%s\n", params->verbose ? "yes" : "no");
    printf("\tDon't reevaluate:\t%s\n", params->dont_reevaluate ? "yes" : "no");
    printf("\tSeed:\t\t\t%ld\n", params->seed);
    printf("\tChangelevel:\t\t%f\n", params->changelevel);
    printf("\tLocalsearch:\t\t%s\n", params->do_localsearch ? "yes" : "no");
    if(params->do_localsearch)
        printf("\tLocalsearch k-value:\t%ld\n", params->ls_k );
    printf("\tPopulation Injection:\t%s\n", params->do_pi ? "yes" : "no");
    if(params->do_pi)
    {
        printf("\tInjection width:\t%ld\n", params->pi_width);
        printf("\tInjection threshold:\t%.4f\n", params->pi_threshold);
        printf("\tInjection size:\t\t%ld\n", params->pi_size);
    }
    printf("\tRandom mode:\t\t%s\n", params->random ? "yes" : "no");
    if(params->tuning)
        printf("\tTuning iterations:\t%ld\n", params->tuning);
    printf("</Experiment parameters>\n");
}

/*
 * Prints the string representation of the individual including values and fitness value.
 */
void print_individual(Individual *ind)
{
    printf("Individual: [");
    for(int i=0; i<ind->size; i++)
    {
        if(i) printf(" ");
        printf("%d", ind->values[i]);
    }
    printf("], Fitness: %ld (%p)\n", ind->fitness, ind);
}

/*
 * Performs a bitflip mutation with probability 'p' on each gene of individual 'ind'.
 * Returns the number of flipped bits
 */
int bitflip_mutation(Individual *ind, float p)
{
    int c=0;
    for(int i=0; i<ind->size; i++)
    {
        if(frand(1.0) < p)
        {
            c++;
            ind->values[i] = !ind->values[i];
        }
    }
    return c;
}

/*
 * Performs an uniform crossover on parents 'p1' and 'p2' and saves the result in children 'c1' and 'c2'.
 */
void uniform_crossover(Individual *p1, Individual *p2, Individual *c1, Individual *c2)
{
    for(int i=0; i<p1->size; i++)
    {
        if(rand() % 2)
        {
            c1->values[i] = p1->values[i];
            c2->values[i] = p2->values[i];
        }
        else
        {
            c1->values[i] = p2->values[i];
            c2->values[i] = p1->values[i];
        }
    }
}

int tournament_selection_soga(Individual* pop, int popsize, int tournsize)
{
    if (popsize == 1)
        return 0;
    int best = rand() % popsize;
    for(int i=1; i<tournsize; i++)
    {
        int choice = rand() % popsize;
        if(pop[choice].fitness < pop[best].fitness)
            best = choice;
    }
    return best;
}
/*
 * Performs a tournament selection on population 'pop'.
 * Parameter 'tournsize' determines the size of the tournament in which the individuals participate.
 * Returns the index of the selected individual within the population.
 * TODO: implement using distinct individuals
 */
int tournament_selection_moga(Individual* pop, int popsize, int tournsize)
{
    if (popsize == 1)
        return 0;
    int best = rand() % popsize;
    int choice = 0;
    for(int i=1; i<tournsize; i++)
    {
        int flag;
        do{
            choice = rand() % popsize;
        }
        while(choice == best);

        flag = check_dominance (&pop[choice], &pop[best]);
        if (flag==1)
        {
            return (choice);
        }
        if (flag==-1)
        {
            return (best);
        }
        if (pop[choice].crowd_dist > pop[best].crowd_dist)
        {
            return(choice);
        }
        if (pop[best].crowd_dist > pop[choice].crowd_dist)
        {
            return(best);
        }
        if(pop[choice].fitness < pop[best].fitness)
            return (choice);
        else
            return (best);
//        if ((randomperc()) <= 0.5)
//        {
//            return(choice);
//        }
//        else
//        {
//            return(best);
//        }
    }
    return best;
}

/*
 * Calculates and returns the mean of the fitness of population 'pop' of size 'size'.
 */
double population_fitness_mean(Population *pop)
{
    Fitness sum = 0;
    for(int i=0; i<pop->size; i++)
        sum += pop->ind[i].fitness;
    return (sum / (double)pop->size);
}

/*
 * Calculates and returns the minimum of the fitness of population 'pop' of size 'size'.
 */
double population_fitness_min(Population *pop)
{
    double min = pop->ind[0].fitness;
    for(int i=1; i<pop->size; i++)
    {
        if(pop->ind[i].fitness < min)
            min = pop->ind[i].fitness;
    }
    return min;
}

/*
 * Calculates and returns the maximum of the fitness of population 'pop' of size 'size'.
 */
double population_fitness_max(Population *pop)
{
    double max = pop->ind[0].fitness;
    for(int i=1; i<pop->size; i++)
    {
        if(pop->ind[i].fitness > max)
            max = pop->ind[i].fitness;
    }
    return max;
}

/*
 * Calculates and returns the standard deviation of the fitness of population 'pop' of size 'size'.
 */
double population_fitness_stdev(Population *pop)
{
    double sum = 0;
    double m = population_fitness_mean(pop);
    for(int i=0; i<pop->size; i++)
        sum += pow(pop->ind[i].fitness - m, 2);
    return sqrt(sum / (double)pop->size);
}

/*
 * Returns the best found value in the array
 */
Fitness best_fitness_from(FitnessWrite* fitvals, int count)
{
    if(fitvals == NULL)
        return 0;
    FitnessWrite best = fitvals[0];
    for(int i=1; i<count; i++)
    {
        if(fitvals[i].fitness != 0 && fitvals[i].fitness < best.fitness)
            best = fitvals[i];
    }
    return best.fitness;
}

/*
 * Prints the statistics of the given population 'pop' of size 'size' for generation 'gen'
 */
void print_stats(Population *pop, int gen, long nevals, long nevals_ls, int print_ls, int print_pi)
{
    printf("gen %4d", gen);
    printf(" - nevals %4ld", nevals);
    if(print_ls)
        printf(" - ls nevals %4ld", nevals_ls);
    printf(" - mean %4.2f", population_fitness_mean(pop));
    printf(" - stdev %4.2f", population_fitness_stdev(pop));
    printf(" - min %4.2f", population_fitness_min(pop));
    printf(" - max %4.2f", population_fitness_max(pop));
    if(print_pi)
        printf(" - PI %4d", print_pi);
    printf("\n");
}

/*
 * Print the current network model
 */
void print_model(NetworkModel *model)
{
    printf("<NetworkModel>\n");
    printf("\t<ID>%ld</ID>\n", model->id);
    printf("\t<Vcount>%ld</Vcount>\n", model->vcount);
    printf("\t<Ecount>%ld</Ecount>\n", model->ecount);
    printf("\t<Vertices>\n");
    for(int i=0; i<model->vcount; i++)
        printf("\t\t<Vertex id=%ld active=%d />\n", model->vertices[i].id, model->vertices[i].active);
    printf("\t</Vertices>\n");
    printf("\t<Edges>\n");
    for(int i=0; i<model->ecount; i++)
        printf("\t\t<Edge src=%ld dst=%ld w=%d active=%d/>\n", model->edges[i].src, model->edges[i].dst, model->edges[i].w, model->edges[i].active);
    printf("\t</Edges>\n");
    printf("</NetworkModel>\n");
}

/*
 * Clean up the memory used by the population and the model
 */
int cleanup(Population *pop, NetworkModel *model, FitnessWrite *fitvals, Diversity *div)
{
    free_population(pop);
    free_model(model);
    if(fitvals)
        free(fitvals);
    if(div->values)
        free(div->values);
    return 1;
}

/*
 * Checks whether a model change occurs or not.
 * If yes, changes to the new model and also resets the countdown to the value calculated
 * from the provided parameters.
 * Returns 1 if model was changed, 0 if not
 *TODO: Remove nevals parameter as its just for debugging
 */
int decrement_change_countdown(long* countdown, NetworkModel* model, struct ea_parameters* params, long nevals)
{
    if(!--(*countdown))
    {
        create_diff(model, params);
        LOG_VERBOSE(params->verbose,
                    "Created diff having %ld/%ld active |V| and %ld/%ld active |E| @ %ld evals\n", model->active_vcount, model->vcount, model->active_ecount, model->ecount, nevals);
        (*countdown) = (long) (params->max_evals / params->modelcount);
        return 1;
    }
    return 0;
}

long inject_random_immigrants(Population* pop, NetworkModel* model, double mutptb,long* countdown, struct ea_parameters* params, long nevals, FitnessWrite * fitvals ){
    for (int i = 0; i < params->dnsga2prp; ++i) {

        Individual ind;
        create_random_individual(&ind, nbits[0]);
        fitvals[(nevals)++] = fitness_ext(&ind, model);
        int random_individual = rand() % popsize;
        copy_ind(&ind, &pop->ind[random_individual]);
        decrement_change_countdown(countdown, model, params, (nevals));
    }
    return (nevals);
}

long inject_mutated_individuals(Population* pop, NetworkModel* model, double mutptb,long* countdown, struct ea_parameters* params, long nevals, FitnessWrite * fitvals){
    for (int i = 0; i < params->dnsga2prp; ++i) {

        int random_individual = rand() % popsize;
        bitflip_mutation(&pop->ind[random_individual], mutptb);
        fitvals[(nevals)++] = fitness_ext(&pop->ind[random_individual], model);
        decrement_change_countdown(countdown, model, params, (nevals));
    }
    return (nevals);
}

static void decrement_change_countdown_and_maybe_reevaluate(
        long* change_countdown,
        NetworkModel* model,
        struct ea_parameters* params,
        long* nevals,
        Population* pop,
        GenerationData* gendata,
        long *gendatacount,
        FitnessWrite* fitvals)
{
    if (!decrement_change_countdown(change_countdown, model, params, *nevals))
        return;
    if (params->dont_reevaluate)
        return;

    int rest_nevals = pop->size;
    if (*nevals + pop->size > params->max_evals)
        rest_nevals = params->max_evals - *nevals - 1;

    for (int j = 0; j < rest_nevals; j++)
    {
        pop->ind[j].fitness = fitness(&pop->ind[j], model);
        decrement_change_countdown(change_countdown, model, params, *nevals);
        if (gendata)
            gendata[(*gendatacount)++] = create_generation_data(pop, model);
        if (fitvals)
            fitvals[(*nevals)++] = fitness_ext(&pop->ind[j], model);
    }

    if(params->dnsga2a){
        *nevals =  inject_random_immigrants(pop, model, params->mutpb, change_countdown, params, *nevals, fitvals);
    }else if(params->dnsga2b){
        *nevals = inject_mutated_individuals(pop, model, params->mutpb, change_countdown, params, *nevals, fitvals);
    }


}

/*
 * Checks whether population injection needs to be triggered
 * Returns 1 if yes, 0 if not
 */
int pi_necessary(Diversity *div, double threshold)
{
    return fitness_stdev(div->values, div->_memsize) < threshold;
}

/*
 * Writes the content of the payload for the CBR system to a file 'CBR.csv'.
 * For debugging purposes
 */
int CBR_write_payload(NetworkModel *model, Individual *ind, long nevals, struct ea_parameters* params)
{
    FILE *fp = fopen("CBR.csv", "a");
    if(fp == NULL)
    {
        printf("Could not open file '%s'\n", params->inputfname);
        return -1;
    }
    // Number of evaluations
    fprintf(fp, "%ld\n", nevals);
    // K-value
    fprintf(fp, "%ld\n", params->ls_k);
    // Individual
    fprintf(fp, "'(");
    for(int i=0; i<ind->size; i++)
    {
        if(i)
            fprintf(fp, " ");
        fprintf(fp, "%d", ind->values[i]);
    }
    fprintf(fp, ")\n");
    fprintf(fp, "%ld\n", ind->fitness);
    // Adjacency list
    for(int i=0; i<model->active_vcount; i++)
    {
        int v_idx = model->active_vertex_idx[i];
        fprintf(fp, "%d,'(", v_idx);
        for(int j=0; j<model->adjlist[v_idx].size; j++)
        {
            if(j)
                fprintf(fp, " ");
            fprintf(fp, "%ld", model->adjlist[v_idx].edge_indices[j]);
        }
        fprintf(fp, ")\n");
    }
    fclose(fp);
    return 0;
}

/*
 * Performs a local search on 1 individual.
 * For the neighborhood, 'k' individuals are considered.
 * The process is iteratively repeated until no better neighbor was found.
 * Returns the new number of evaluations to the caller, which can then calculate the
 * number of evaluations of the LS method or use it for further processing.
 * Returns in case we have a model change or the maximum number of allowed evaluations is hit.
 */
long localsearch(
        Individual *ind,
        Population* pop,
        NetworkModel *model,
        FitnessWrite *fitvals,
        GenerationData* gendata,
        long* gendatacount,
        long* nevals,
        struct ea_parameters* params,
        long* change_countdown)
{
    int k = params->ls_k;
    if(ind->size < k)
    {
        if(params->tuning)
            params->ls_k = ind->size;
        else
            LOG_WARN(params,
                     "k-value too large for element, "
                     "reducing to individuals genome size: %ld", ind->size);
        k = ind->size;
    }
    int neighbors[ind->size];
    int foundbetter;
    Fitness best_fitness = ind->fitness;
    do
    {
        //#######################
        //printf("WARNING: Debug code running writing CBR code to CBR.csv\n");
        //CBR_write_payload(model, ind, (*nevals), params);
        //#######################
        distinct_random_values(neighbors, ind->size);
        foundbetter = 0;
        for(int i=0; i<k; i++)
        {
            ind->values[neighbors[i]] = !ind->values[neighbors[i]];
            Fitness fit = fitness(ind, model);
            if(fitvals)
                fitvals[(*nevals)++] = fitness_ext(ind, model);
            if(params->genfname)
                gendata[(*gendatacount)++] = create_generation_data(pop, model);
            if(decrement_change_countdown(change_countdown, model, params, (*nevals)))
            {
                if(!params->dont_reevaluate)
                {
                    for(int j=0; j<pop->size; j++)
                    {
                        pop->ind[j].fitness = fitness(&pop->ind[j], model);
                        decrement_change_countdown(change_countdown, model, params, (*nevals));
                        if(params->genfname)
                            gendata[(*gendatacount)++] = create_generation_data(pop, model);
                        if(params->savefname || params->tuning)
                            fitvals[(*nevals)++] = fitness_ext(&pop->ind[j], model);
                        if((*nevals) >= params->max_evals)
                            return (*nevals);
                    }
                }
            }
            if(fit >= best_fitness)
                ind->values[neighbors[i]] = !ind->values[neighbors[i]];
            else
            {
                ind->fitness = fit;
                best_fitness = fit;
                foundbetter = 1;
            }
            if((*nevals) >= params->max_evals)
                return (*nevals);
        }
    }while(foundbetter);
    return (*nevals);
}

int update_memory(Population* memory, Individual* ind){

    for (int i = 0; i < memory->size; ++i) {
        if(check_dominance(&memory->ind[i], ind) == 1){
            return 0;
        }
    }
    for (int i = 0; i < memory->size; ++i) {
        if(check_dominance(ind, &memory->ind[i]) == 1){
            copy_ind(ind, &memory->ind[i]);
            return 1;
        }
    }

}

int check_if_still_exists_in_memory_and_set_explored(Population* pop, double obj1, double obj2, int size, int position_in_memory){
    if(pop->ind[position_in_memory].obj[0] == obj1 && pop->ind[position_in_memory].obj[1] == obj2)
    {
        pop->ind[position_in_memory].explored = 1;
        return 1;
    }

    return 0;
}

void re_init_first_front(Population* first_front, Population* memory){

    int size_of_unexplored = 0;
    for (int j = 0; j < memory->size; ++j) {
        if(memory->ind[j].explored == 0)
            size_of_unexplored+=1;

    }
    if(size_of_unexplored == 0) {
        first_front->size = 0;
        return;
    }

    for (int i = 0, k = 0; i < memory->size; ++i) {
        if(memory->ind[i].explored == 0){
            copy_ind(&memory->ind[i], &first_front->ind[k++]);
            return;
        }
    }

    first_front->size = size_of_unexplored;
}

typedef struct Node{
    int index;
    Individual* ind;
    struct Node* next;
} node_t;

void push(struct Node** head_ref, int new_data, Individual* ind)
{
    struct Node* new_node = (struct Node*) malloc(sizeof(struct Node));
    new_node->ind = (Individual*)malloc(sizeof(Individual));
    allocate_memory_ind(new_node->ind);
    copy_ind(ind, new_node->ind);
    new_node->index  = new_data;
    new_node->next = (*head_ref);
    (*head_ref)    = new_node;
}

void deleteNode(struct Node **head_ref, int key)
{
    // Store head node
    struct Node* temp = *head_ref, *prev;

    // If head node itself holds the key to be deleted
    if (temp != NULL && temp->index == key)
    {
        *head_ref = temp->next;   // Changed head
        free(temp);               // free old head
        return;
    }

    // Search for the key to be deleted, keep track of the
    // previous node as we need to change 'prev->next'
    while (temp != NULL && temp->index != key)
    {
        prev = temp;
        temp = temp->next;
    }

    // If key was not present in linked list
    if (temp == NULL) return;

    // Unlink the node from linked list
    prev->next = temp->next;

    free(temp);  // Free memory
}

void remove_from_list(node_t* list, Individual* ind){
    if(list->ind->obj[0] == ind->obj[0] && list->ind->obj[1] == ind->obj[1]){
        free(list->ind);
        free(list);
        return;
    }
    while(list->next != NULL){
        if(list->next->ind->obj[0] == ind->obj[0] && list->next->ind->obj[1] == ind->obj[1]){
            free(list->next->ind);
            free(list->next);
            list->next = list->next->next;
        }
    }
}

void add_to_list(node_t* list, Individual* ind){
    while(list->next != NULL){
        list = list->next;
    }
    list->next = malloc(sizeof(node_t));
    list->next->ind = (Individual*)malloc(sizeof(Individual));
    allocate_memory_ind(list->next->ind);
    copy_ind(ind, list->next->ind);
}

void min(Individual* ind, node_t* head){
    node_t* head2 = head;
    while (head->next != NULL){
        int flag = check_dominance(head->ind, ind);
        if(flag == 1){
            return;
        }
        head = head->next;

    }
    node_t* previous = head2;

    while (head2->next != NULL){
        int flag = check_dominance(ind,head2->ind );
        if(flag != 1)
            continue;
        node_t* temp = head2;
        *head2 = *head2->next;
        head2 = head2->next;
        free(temp->ind);
        free(temp);
    }
    add_to_list(previous, ind);

}

long dapls(
        Population* pop,
        NetworkModel *model,
        FitnessWrite *fitvals,
        GenerationData* gendata,
        long* gendatacount,
        long* nevals,
        struct ea_parameters* params,
        long* change_countdown)
{
    int k = 50;

    int count_ind_in_first_front = 0;
    for (int l = 0; l < popsize; ++l) {
        if(pop->ind[l].rank == 1)
            count_ind_in_first_front += 1;
    }

    if(count_ind_in_first_front  == 0)
        return *nevals;
    node_t* P = (node_t*)malloc(sizeof(node_t));
    P->ind = (Individual*)malloc(sizeof(Individual));
    allocate_memory_ind(P->ind);

    node_t* L = (node_t*)malloc(sizeof(node_t));
    L->ind = (Individual*)malloc(sizeof(Individual));
    allocate_memory_ind(L->ind);
    node_t* p_head = P;
    node_t* l_head = L;
    for (int m = 0, i = 0; m < popsize; ++m) {
        if(pop->ind[m].rank == 1){
            copy_ind(&pop->ind[m],p_head->ind);
            p_head->next = (node_t*)malloc(sizeof(node_t));
            p_head->next->ind = (Individual*)malloc(sizeof(Individual));
            allocate_memory_ind(p_head->next->ind);
            p_head = p_head->next;

            copy_ind(&pop->ind[m],l_head->ind);
            l_head->next = (node_t*)malloc(sizeof(node_t));
            l_head->next->ind = (Individual*)malloc(sizeof(Individual));
            allocate_memory_ind(l_head->next->ind);
            l_head = l_head->next;
        }
    }

    int count = count_ind_in_first_front;
    while(count != 0){
        Individual* ind = malloc(sizeof(Individual));
        allocate_memory_ind(ind);
        copy_ind(L->ind, ind);
        node_t* temp = L->next;
        remove_from_list(L, L->ind);
        L = L->next;
        count-=1;
        int ls_count = 0;
        while(ls_count < params->ls_k){
            Individual* neighboor = malloc(sizeof(Individual));
            allocate_memory_ind(neighboor);
            copy_ind(ind, neighboor);

            //Change an active vertex
            int random_gene = rand() % nbits[0];
            while(model->vertices[random_gene].active == 0){
                random_gene = rand() % nbits[0];
            }


            neighboor->values[random_gene] = !ind->values[random_gene];
            if(fitvals)
                fitvals[(*nevals)++] = fitness_ext(neighboor, model);

            decrement_change_countdown(change_countdown, model, params, (*nevals));
            node_t* p_head1 = P;
            int dominated = 0;


            min(neighboor, p_head1);

            ls_count+=1;
            deallocate_memory_ind(neighboor);
            free(neighboor);

        }

    }
    for (int l = 0; l < popsize; ++l) {
        if(pop->ind[l].rank == 1){
            copy_ind(P->ind, &pop->ind[l]);
            P = P->next;
        }

    }
    return *nevals;
}
typedef struct weights_of_f{
    double w1;
    double w2;
} weights_of_f;

double calculate_F(double* minlist, double* maxlist, double obj1, double obj2){

    double w1 = ((maxlist[0] - obj1) / (maxlist[0] - minlist[0])) /
                ((maxlist[0] - obj1) / (maxlist[0] - minlist[0])) + ((maxlist[1] - obj2) / (maxlist[1] - minlist[1]));

    double w2 = ((maxlist[1] - obj2) / (maxlist[1] - minlist[1])) /
                ((maxlist[0] - obj1) / (maxlist[0] - minlist[0])) + ((maxlist[1] - obj2) / (maxlist[1] - minlist[1]));

    return w1* obj1 + w2* obj2;
}

long nsls(
        Population* pop,
        NetworkModel *model,
        FitnessWrite *fitvals,
        GenerationData* gendata,
        long* gendatacount,
        long* nevals,
        struct ea_parameters* params,
        long* change_countdown,
        double* min_list,
        double* max_list) {

    Population *copy_pop = (Population *)malloc(sizeof(Population));
    allocate_memory_pop (copy_pop, pop->size);

    for (int m = 0 ; m < popsize; ++m) {
        copy_ind(&pop->ind[m],&copy_pop->ind[m]);
    }

    for (int i = 0; i < pop->size; ++i) {

        int rand1 = rand() % popsize;
        int rand2 = rand() % popsize;
        while(rand1 == rand2){
            rand2 = rand() % popsize;
        }

        Individual* neighboor1 = malloc(sizeof(Individual));
        allocate_memory_ind(neighboor1);
        copy_ind(&copy_pop->ind[rand1], neighboor1);

        Individual* neighboor2 = malloc(sizeof(Individual));
        allocate_memory_ind(neighboor2);
        copy_ind(&copy_pop->ind[rand2], neighboor2);


        int random_gene = rand() % nbits[0];
        while(model->vertices[random_gene].active == 0){
            random_gene = rand() % nbits[0];
        }

        neighboor1->values[random_gene] = !copy_pop->ind[rand1].values[random_gene];
        if(fitvals)
            fitvals[(*nevals)++] = fitness_ext(neighboor1, model);

        decrement_change_countdown(change_countdown, model, params, (*nevals));

        random_gene = rand() % nbits[0];
        while(model->vertices[random_gene].active == 0){
            random_gene = rand() % nbits[0];
        }

        neighboor2->values[random_gene] = !copy_pop->ind[rand2].values[random_gene];
        if(fitvals)
            fitvals[(*nevals)++] = fitness_ext(neighboor2, model);

        decrement_change_countdown(change_countdown, model, params, (*nevals));

        int flag1 = check_dominance(neighboor1, &copy_pop->ind[i]);
        int flag2 = check_dominance(neighboor2, &copy_pop->ind[i]);
        if(flag1 == 1 && flag2 == 1){
            if(rand() % 2){
                copy_ind(neighboor1, &copy_pop->ind[i]);
            }else{
                copy_ind(neighboor2, &copy_pop->ind[i]);
            }
        }else if(flag1 == 1){
            copy_ind(neighboor1, &copy_pop->ind[i]);
        }else if(flag2 == 1){
            copy_ind(neighboor2, &copy_pop->ind[i]);
        }else if(flag1 == 0 && flag2 == 0){
            if(rand() % 2){
                copy_ind(neighboor1, &copy_pop->ind[i]);
            }else{
                copy_ind(neighboor2, &copy_pop->ind[i]);
            }
        } else if(flag1 == 0){
            copy_ind(neighboor1, &copy_pop->ind[i]);
        }else if(flag2 == 0){
            copy_ind(neighboor2, &copy_pop->ind[i]);
        }

        deallocate_memory_ind(neighboor1);
        free(neighboor1);
        deallocate_memory_ind(neighboor2);
        free(neighboor2);

    }

    for (int j = 0; j < popsize; ++j) {
        pop->ind[pop->size++] = copy_pop->ind[j];
    }
    fill_nondominated_sort(pop);

    //deallocate_memory_pop(copy_pop, popsize);
    return (*nevals);
}


long ls_dnsga2(
        Population* pop,
        NetworkModel *model,
        FitnessWrite *fitvals,
        GenerationData* gendata,
        long* gendatacount,
        long* nevals,
        struct ea_parameters* params,
        long* change_countdown,
        double* min_list,
        double* max_list)
{
    int count_ind_in_first_front = 0;
    for (int l = 0; l < popsize; ++l) {
        if(pop->ind[l].rank == 1)
            count_ind_in_first_front += 1;
    }


    if(count_ind_in_first_front  == 0)
        return *nevals;

    Population *first_front = (Population *)malloc(sizeof(Population));
    allocate_memory_pop (first_front, count_ind_in_first_front);

    Population *memory = (Population *)malloc(sizeof(Population));
    allocate_memory_pop (memory, count_ind_in_first_front);

    //Filling  the pop with ind from first front
    for (int m = 0, i = 0; m < popsize; ++m) {
        if(pop->ind[m].rank == 1){
            copy_ind(&pop->ind[m],&first_front->ind[i++]);

        }
    }
    int foundbetter = 0;
    do{
        foundbetter = 0;
        for (int i = 0; i < params->ls_k; ++i) {
            int random = rand() % count_ind_in_first_front;

            double f = calculate_F(min_list, max_list, first_front->ind[random].obj[0], first_front->ind[random].obj[1]);

            Individual* neighboor = malloc(sizeof(Individual));
            allocate_memory_ind(neighboor);
            copy_ind(&first_front->ind[random], neighboor);
            int random_gene = rand() % nbits[0];
            while(model->vertices[random_gene].active == 0){
                random_gene = rand() % nbits[0];
            }
            neighboor->values[random_gene] = !first_front->ind[random].values[random_gene];
            if(fitvals)
                fitvals[(*nevals)++] = fitness_ext(neighboor, model);
            //Change an active vertex



            decrement_change_countdown(change_countdown, model, params, (*nevals));

            double f_neighbour = calculate_F(min_list, max_list, neighboor->obj[0], neighboor->obj[1]);

            if(f_neighbour < f){
                copy_ind(neighboor, &first_front->ind[random]);
                foundbetter = 1;
            }

            deallocate_memory_ind(neighboor);
            free(neighboor);
        }


    }while(foundbetter);


    for (int j = 0, i = 0; j < count_ind_in_first_front; ++j) {
        if(pop->ind->rank == 1){
            copy_ind(&first_front->ind[i], &pop->ind[j]);
            i++;
        }
    }
    deallocate_memory_pop(first_front, count_ind_in_first_front);
    return (*nevals);
}

long paretolocalsearch(
        Population* pop,
        NetworkModel *model,
        FitnessWrite *fitvals,
        GenerationData* gendata,
        long* gendatacount,
        long* nevals,
        struct ea_parameters* params,
        long* change_countdown)
{
    int k = 50;

    int count_ind_in_first_front = 0;
    for (int l = 0; l < popsize; ++l) {
        if(pop->ind[l].rank == 1)
            count_ind_in_first_front += 1;
    }


    if(count_ind_in_first_front  == 0)
        return *nevals;

    Population *first_front = (Population *)malloc(sizeof(Population));
    allocate_memory_pop (first_front, count_ind_in_first_front);

    Population *memory = (Population *)malloc(sizeof(Population));
    allocate_memory_pop (memory, count_ind_in_first_front);

    //Filling  the pop with ind from first front
    for (int m = 0, i = 0; m < popsize; ++m) {
        if(pop->ind[m].rank == 1){
            copy_ind(&pop->ind[m],&first_front->ind[i++]);

        }
    }

    //set all unexplored
    for (int m = 0, i = 0; m < count_ind_in_first_front; ++m) {
        first_front->ind[m].explored = 0;
    }


    for (int n = 0; n < count_ind_in_first_front; ++n) {
        copy_ind(&first_front->ind[n], &memory->ind[n]);
    }

    //Set pop size
    first_front->size = count_ind_in_first_front;
    memory->size = count_ind_in_first_front;
    int explore_count = 0;
    while(first_front->size > 0){

        int random = rand() % first_front->size;

        if(first_front->ind[random].explored == 0){

            int count = 0;
            double obj1 = 0, obj2 = 0;
            obj1 = first_front->ind[random].obj[0];
            obj2 = first_front->ind[random].obj[1];
            //int neighbors[first_front->ind[random].size];
            //distinct_random_values(neighbors, first_front->ind[random].size);
            while(count < params->ls_k){
                Individual* neighboor = malloc(sizeof(Individual));
                allocate_memory_ind(neighboor);
                copy_ind(&first_front->ind[random], neighboor);

                //Change an active vertex
                int random_gene = rand() % nbits[0];
                while(model->vertices[random_gene].active == 0){
                    random_gene = rand() % nbits[0];
                }


                neighboor->values[random_gene] = !memory->ind[random].values[random_gene];
                if(fitvals)
                    fitvals[(*nevals)++] = fitness_ext(neighboor, model);

                decrement_change_countdown(change_countdown, model, params, (*nevals));

                neighboor->explored = 0;
                int ret = update_memory(memory, neighboor);
                if(ret == 1)
                    break;
                count++;
                deallocate_memory_ind(neighboor);
                free(neighboor);

            }
            check_if_still_exists_in_memory_and_set_explored(memory, obj1, obj2, count_ind_in_first_front, random);

            re_init_first_front(first_front, memory);
        }
    }

    for (int j = 0, i = 0; j < count_ind_in_first_front; ++j) {
        if(pop->ind->rank == 1){
            copy_ind(&memory->ind[i], &pop->ind[j]);
            pop->ind[j].explored = 0;
            i++;
        }
    }

    deallocate_memory_pop(memory, count_ind_in_first_front);
    deallocate_memory_pop(first_front, count_ind_in_first_front);
    return (*nevals);
}

int unvisited_exists(struct Node* list){
    while(list->next != NULL){
        if(list->ind->explored == 0)
            return list->index;
        list = list->next;
    }

    return 0;
}

//void PLS(struct Node* A){
//    int i = 0;
//    struct Node* A_prime = NULL;
//    struct Node* A_double_prime = NULL;
//    A_prime = (struct Node*)malloc(sizeof(struct Node));
//    A_prime->ind = (Individual*)malloc(sizeof(Individual));
//    allocate_memory_ind(A_prime->ind);
//
//    A_double_prime = (struct Node*)malloc(sizeof(struct Node));
//    A_double_prime->ind = (Individual*)malloc(sizeof(Individual));
//    allocate_memory_ind(A_double_prime->ind);
//
//
//    while (A->next != NULL) {
//        copy_ind(&A->ind[i], A_prime->ind);
//        A_prime->next = (node_t *) malloc(sizeof(node_t));
//        A_prime->next->ind = (Individual *) malloc(sizeof(Individual));
//        allocate_memory_ind(A_prime->next->ind);
//        A_prime = A_prime->next;
//        i++;
//    }
//    int unvisited =0;
//    unvisited = unvisited_exists(A_prime);
//    do{
//
//
//
//
//        unvisited = unvisited_exists(A_prime);
//
//    }while(unvisited != 0;);
//
//
//}

//long mpls(
//        Population* pop,
//        NetworkModel *model,
//        FitnessWrite *fitvals,
//        GenerationData* gendata,
//        long* gendatacount,
//        long* nevals,
//        struct ea_parameters* params,
//        long* change_countdown)
//{
//    int k = 50;
//
//    int count_ind_in_first_front = 0;
//    for (int l = 0; l < popsize; ++l) {
//        if(pop->ind[l].rank == 1)
//            count_ind_in_first_front += 1;
//    }
//
//
//    if(count_ind_in_first_front  == 0)
//        return *nevals;
//
//
//
//    Population *first_front = (Population *)malloc(sizeof(Population));
//    allocate_memory_pop (first_front, count_ind_in_first_front);
//
//    Population *memory = (Population *)malloc(sizeof(Population));
//    allocate_memory_pop (memory, count_ind_in_first_front);
//
//    //Filling  the pop with ind from first front
//    for (int m = 0, i = 0; m < popsize; ++m) {
//        if(pop->ind[m].rank == 1){
//            copy_ind(&pop->ind[m],&first_front->ind[i++]);
//
//        }
//    }
//
//    //set all unexplored
//    for (int m = 0, i = 0; m < count_ind_in_first_front; ++m) {
//        first_front->ind[m].explored = 0;
//    }
//
//
//    for (int n = 0; n < count_ind_in_first_front; ++n) {
//        copy_ind(&first_front->ind[n], &memory->ind[n]);
//    }
//
//
//
//    //Set pop size
//    first_front->size = count_ind_in_first_front;
//    memory->size = count_ind_in_first_front;
//    int explore_count = 0;
//
//    struct Node* A = NULL;
//    struct Node* A_prime = NULL;
//    int counter = 0;
//    while(counter < params->ls_k){
//        int random_individual = rand() % popsize;
//
//        deactive(&pop->ind[random_individual], &A, &A_prime);
//        pls(A_prime)
//        pareto_merge(A, );
//
//        counter++;
//    }
//
//    while(first_front->size > 0){
//
//        int random = rand() % first_front->size;
//
//        if(first_front->ind[random].explored == 0){
//
//            int count = 0;
//            double obj1 = 0, obj2 = 0;
//            obj1 = first_front->ind[random].obj[0];
//            obj2 = first_front->ind[random].obj[1];
//            //int neighbors[first_front->ind[random].size];
//            //distinct_random_values(neighbors, first_front->ind[random].size);
//            while(count < params->ls_k){
//                Individual* neighboor = malloc(sizeof(Individual));
//                allocate_memory_ind(neighboor);
//                copy_ind(&first_front->ind[random], neighboor);
//
//                //Change an active vertex
//                int random_gene = rand() % nbits[0];
//                while(model->vertices[random_gene].active == 0){
//                    random_gene = rand() % nbits[0];
//                }
//
//
//                neighboor->values[random_gene] = !memory->ind[random].values[random_gene];
//                if(fitvals)
//                    fitvals[(*nevals)++] = fitness_ext(neighboor, model);
//
//                decrement_change_countdown(change_countdown, model, params, (*nevals));
//
//                neighboor->explored = 0;
//                int ret = update_memory(memory, neighboor);
//                if(ret == 1)
//                    break;
//                count++;
//                deallocate_memory_ind(neighboor);
//                free(neighboor);
//
//            }
//            check_if_still_exists_in_memory_and_set_explored(memory, obj1, obj2, count_ind_in_first_front, random);
//
//            re_init_first_front(first_front, memory);
//        }
//    }
//
//    for (int j = 0, i = 0; j < count_ind_in_first_front; ++j) {
//        if(pop->ind->rank == 1){
//            copy_ind(&memory->ind[i], &pop->ind[j]);
//            pop->ind[j].explored = 0;
//            i++;
//        }
//    }
//
//    deallocate_memory_pop(memory, count_ind_in_first_front);
//    deallocate_memory_pop(first_front, count_ind_in_first_front);
//    return (*nevals);
//}

void find_max_and_min_from_first_front(Population* pop, double* min_list, double* max_list){
    double mininum_x = 9999999;
    double mininum_y = 9999999;
    double maximum_x = 0;
    double maximum_y = 0;
    for (int i = 0; i < pop->size; ++i) {
        if(pop->ind[i].rank != 1)continue;

        if (pop->ind[i].obj[0] < mininum_x) {
            mininum_x = pop->ind[i].obj[0];
        }
        if (pop->ind[i].obj[1] < mininum_y) {
            mininum_y = pop->ind[i].obj[1];
        }

        if (pop->ind[i].obj[0] > maximum_x) {
            maximum_x = pop->ind[i].obj[0];
        }
        if (pop->ind[i].obj[1] > maximum_y) {
            maximum_y = pop->ind[i].obj[1];
        }

    }

    min_list[0]= mininum_x;
    min_list[1]= mininum_y;
    max_list[0] = maximum_x;
    max_list[1] = maximum_y;
}
/*
 * Runs the default version of the monitor selection optimizer.
 * Returns the best found value (of the last optimization window
 * in case dynamic optimization is used).
 */
Fitness run_default(struct ea_parameters* params)
{
    long nevals = 0;

    //initialize global parameter for problem specific
    nreal = 0;
    nbin = 1;
    nobj = 2;
    ncon = 0;
    popsize = params->popsize;
    random_immigrant_ratio = 30;
    // use new

    nbits = new int[nbin];
    min_binvar = new double[nbin];
    max_binvar = new double[nbin];

    double minimum[nobj];
    double maximum[nobj];
    FILE *fpt3;
    fpt3 = fopen("best_pop.out","w");
    FILE *fronts;
    fronts = fopen("fronts.out","w");
    FILE *hv_file;
    hv_file = fopen("hv.out","w");
    FILE *ss_file;
    ss_file = fopen("ss.out","w");

    long change_countdown = (long)(params->max_evals / params->modelcount) + 1;
    NetworkModel model;
    if(read_base_file(&model, params->inputfname) == -1)
    {
        LOG_WARN(params,
                 "Error reading file '%s', aborting", params->inputfname);
        exit(EXIT_FAILURE);
    }
    if(model.ecount == 0 || model.vcount == 0)
    {
        LOG_WARN(params,
                 "Either no edge or vertex in file '%s', aborting",
                 params->inputfname);
        exit(EXIT_FAILURE);
    }
    if(params->modelcount > 1)
    {
        create_diff(&model, params);
    }
    if(params->verbose)
    {
        print_config(params);
        printf("Read file '%s' having |V| = %ld (%ld active), |E| = %ld (%ld active) @ %d evals\n", params->inputfname, model.vcount, model.active_vcount, model.ecount, model.active_ecount, 0);
    }
    variables_param_to_global(params);
    nbits[0] = model.vcount; //TODO check if this is true
    FitnessWrite *fitvals = calloc(sizeof(FitnessWrite) , params->max_evals);
    GenerationData* gendata = NULL;
    long gendatacount = 0;
    if(params->genfname)
        gendata = calloc(sizeof(GenerationData) , params->max_evals);
    Population pop;
    pop._memsize = params->popsize + params->popsize + params->pi_size + 1;
    pop.size = 0;
    pop.ind = malloc(sizeof(Individual) * pop._memsize);
    time_t run_start_time = time(NULL);
    for(int i=0; i<params->popsize; i++)
    {
        Individual ind;
        create_random_individual(&ind, model.vcount);
        pop.ind[pop.size++] = ind;
    }
    for(int i=0; i<params->popsize; i++)
    {
        pop.ind[i].fitness = fitness(&pop.ind[i], &model);
        if(gendata)
            gendata[gendatacount++] = create_generation_data(&pop, &model);
        decrement_change_countdown_and_maybe_reevaluate(
                &change_countdown, &model, params, &nevals,
                &pop, gendata, &gendatacount, fitvals);
        fitvals[nevals++] = fitness_ext(&pop.ind[i], &model);
        //Fill objective values


    }
    // Variables for PI
    Diversity diversity;
    diversity.values = NULL;
    diversity._memsize = 0;
    if(params->do_pi)
    {
        diversity._memsize = params->pi_width;
        diversity.values = malloc(sizeof(Fitness) * diversity._memsize);
        for(int k=0; k<diversity._memsize; k++)
            diversity.values[k] = 0;
        diversity.next = 0;
    }

    // print initial population statistics
    if(params->verbose)
        print_stats(&pop, 0, nevals, 0, params->do_localsearch, 0);

    // start of the generational process
    long pi_triggered = 0;
    int injected = 0;
    int current_generation = 0;
    long ls_nevals = 0;
    for (;;)
    {
        current_generation++;
        injected = 0;
        ls_nevals = 0;
//TODO Implement a local search if needed


        if(params->do_paretolocalsearch){
            if(nevals >= params->max_evals)
                goto FINAL_REPORT;
            ls_nevals = nevals;
            nevals = ls_dnsga2(&pop, &model, fitvals, gendata, &gendatacount, &nevals, params, &change_countdown, minimum, maximum);
            //inject_random_immigrants(&pop, &model);
            ls_nevals = nevals - ls_nevals;
        }else if(params->do_localsearch){

            if(nevals >= params->max_evals)
                goto FINAL_REPORT;
            long idx = best_individual_idx(&pop);
            ls_nevals = nevals;
            nevals = localsearch(&pop.ind[idx], &pop, &model, fitvals, gendata, &gendatacount, &nevals, params, &change_countdown);
            ls_nevals = nevals - ls_nevals;

        }
//        // local search
//        if(params->do_paretolocalsearch)
//        {
//            if(nevals >= params->max_evals)
//                goto FINAL_REPORT;
//            ls_nevals = nevals;
//            paretolocalsearch(&pop, &model, fitvals, gendata, &gendatacount, &nevals, params, &change_countdown);
//            //inject_random_immigrants(&pop, &model);
//            ls_nevals = nevals - ls_nevals;
//        }
//        if(params->do_localsearch)
//        {
//            if(nevals >= params->max_evals)
//                goto FINAL_REPORT;
//            long idx = best_individual_idx(&pop);
//            ls_nevals = nevals;
//            nevals = localsearch(&pop.ind[idx], &pop, &model, fitvals, gendata, &gendatacount, &nevals, params, &change_countdown);
//            ls_nevals = nevals - ls_nevals;
//        }
        if(params->ls_only)
        {
            if(params->verbose)
                print_stats(&pop, current_generation, nevals, ls_nevals, params->do_localsearch, injected);
            continue;
        }
        // choose parents and perform crossover + mutation on children
        for(int j=0; j<params->popsize; j = j + 2)
        {
            if(nevals >= params->max_evals)
                goto FINAL_REPORT;
            int p1;
            int p2;
            do
            {
                /*
                 * pop->size changed with popsize
                 * changed to pick only parents not from childs
                 */

                p1 = tournament_selection_moga(pop.ind, pop.size, params->tournsize);
                p2 = tournament_selection_moga(pop.ind, pop.size, params->tournsize);


            }
            while(p1 == p2);
            Individual c1;
            Individual c2;
            create_null_individual(&c1, model.vcount);
            create_null_individual(&c2, model.vcount);
            uniform_crossover(&pop.ind[p1], &pop.ind[p2], &c1, &c2);

            Individual cs[] = {c1, c2};
            for (Individual* c = cs; c < cs + 2; c++)
            {
                bitflip_mutation(c, params->mutpb);
                c->fitness = fitness(c, &model);
                if (gendata)
                    gendata[gendatacount++] = create_generation_data(&pop, &model);
                decrement_change_countdown_and_maybe_reevaluate(
                        &change_countdown, &model, params, &nevals,
                        &pop, gendata, &gendatacount, fitvals);
                fitvals[nevals++] = fitness_ext(c, &model);
                //inject_random_immigrants(&pop, &model, params->mutpb, &change_countdown, params, &nevals, fitvals);
                //inject_mutated_individuals(&pop, &model, params->mutpb, &change_countdown, params, &nevals, fitvals);
                pop.ind[pop.size++] = *c;
                if (nevals >= params->max_evals)
                    goto FINAL_REPORT;
            }
        }

        //*************************************************************
        //FAST-NON-DOMINATED-SORT --------- STARTED
        //
        //*************************************************************




        fill_nondominated_sort(&pop);


        find_max_and_min_from_first_front(&pop, &minimum, &maximum);
        double reference[nobj];
        for (int i11 = 0; i11 < nobj; i11++) {
            /* default reference point is: */
            //reference[i11] = 1.2; // for FDA4 and FDA5
            //reference[i11] = 1.1; // for SJY4 and SJY5
            /* however, a better reference point is:
            reference[n] = maximum[n] + 0.1 * (maximum[n] - minimum[n]);
            so that extreme points have some influence. */

            reference[i11] = maximum[i11] + 0.1 * (maximum[i11] - minimum[i11]);
        }
        double data [nobj * popsize];
        for (int i10 = 0; i10 < popsize; i10++)
        {
            for(int i11 = 0; i11 < nobj; i11++)
            {
                int tin = (i10*nobj) + i11;
                data[tin] = pop.ind[i10].obj[i11];
            }
        }
        //printf("before HV \n");
        double HV = fpli_hv (data, nobj, popsize, reference);
        fprintf(hv_file, "%lf \n", HV);

        // Compute Scott's spacing metric
        float sum, min_d, d;
        float mindis [popsize];
        for (int i10 = 0; i10 < popsize; i10++) {
            min_d = 1.0e+10;
            for (int i11 = 0; i11 < popsize; i11++) {
                sum = 0;
                if(i10 == i11)
                    continue;
                for (int i12 = 0; i12 < nobj; i12++)
                {
                    sum +=   pow(pop.ind[i10].obj[i12] - pop.ind[i11].obj[i12],2);
                }
                d = sqrt(sum);

                if (d < min_d)
                    min_d = d;
            }
            mindis[i10] = min_d;
        }
        // compute average dis
        sum = 0;
        for (int i12 = 0; i12 < popsize; i12++)
        {
            sum += mindis[i12]  ;
        }
        float d_avg = sum/popsize;

        sum = 0;
        for (int i12 = 0; i12 < popsize; i12++)
        {
            sum += pow(mindis[i12] - d_avg,2);
        }
        float ss = pow(sum/popsize,0.5);
        fprintf(ss_file, "%lf\n", ss);


        //report_pop(&pop, fronts);
        report_pop_all(&pop, fronts);

//        // Determine survivor ;indices using selection operation.
//        // The survivors are moved to the front of the population,
//        // so that the tournament can continue for the remaining elements.
//        for(int j=0; j<params->popsize; j++)
//        {
//            int s = j + tournament_selection(
//                    pop.ind + j, pop.size - j, params->tournsize);
//            // move the selected individual to the front
//            SWAP_LVALUE(Individual, temp, pop.ind[j], pop.ind[s]);
//        }
//        // remove dying individuals -- the survivors are already at the front
//        while (pop.size > params->popsize)
//            free_individual(&pop.ind[--pop.size]);

        // Place for possible population injection
        if(params->do_pi)
        {
            diversity.values[diversity.next++] = population_fitness_stdev(&pop);
            diversity.next = diversity.next % diversity._memsize;
            if(pi_necessary(&diversity, params->pi_threshold))
            {
                pi_triggered += 1;
                for(int k=0; k<params->pi_size; k++)
                {
                    if(nevals >= params->max_evals)
                        break;
                    Individual ind;
                    create_random_individual(&ind, model.vcount);
                    ind.fitness = fitness(&ind, &model);
                    if(gendata)
                        gendata[gendatacount++] = create_generation_data(&pop, &model);
                    fitvals[nevals++] = fitness_ext(&ind, &model);
                    pop.ind[pop.size++] = ind;
                    injected++;
                    if(nevals >= params->max_evals)
                        break;
                    decrement_change_countdown_and_maybe_reevaluate(
                            &change_countdown, &model, params, &nevals,
                            &pop, NULL, NULL,
                            (params->savefname) ? fitvals : NULL);
                    fitvals[nevals++] = fitness_ext(&pop.ind[k], &model);
                }
            }
        }
        // print statistics of the generation
//        if(params->verbose)
//            print_stats(&pop, current_generation, nevals, ls_nevals, params->do_localsearch, injected);
    }

    FINAL_REPORT: ;

    report_feasible(&pop,fpt3);

    time_t elapsed_time = time(NULL) - run_start_time;
//    if (params->verbose)
//    {
//        printf("Final: ");
//        print_stats(&pop, current_generation, nevals, ls_nevals,
//                params->do_localsearch, injected);
//        printf("Reached %ld evaluations, quitting after %ld seconds\n",
//                nevals, elapsed_time);
//    }
    if (params->savefname)
    {
        write_meta_header(elapsed_time, pi_triggered, params->savefname);
        write_fitness(fitvals, nevals, params->savefname,
                      params->extended_write, current_generation);
    }
    if (params->genfname)
    {
        write_generation_data(gendata, gendatacount, params->genfname);
    }

    //Fitness best_fitness_value = best_fitness_from(fitvals, nevals);

    free(gendata);
    fflush(fpt3);
    fclose(fpt3);
    fflush(fronts);
    fclose(fronts);
    fflush(hv_file);
    fclose(hv_file);
    fflush(ss_file);
    fclose(ss_file);
    cleanup(&pop, &model, fitvals, &diversity);

    return 0;
}

/*
 * Runs the fully random version of the monitor selection optimizer.
 * WARNING: This does only pick random individuals without any optimization!
 */
int run_random(struct ea_parameters* params)
{
    long change_countdown = (long)(params->max_evals / params->modelcount) + 1;
    NetworkModel model;
    if(read_base_file(&model, params->inputfname) == -1)
    {
        LOG_WARN(params,
                 "Error reading file '%s', aborting", params->inputfname);
        exit(EXIT_FAILURE);
    }
    if(model.ecount == 0 || model.vcount == 0)
    {
        LOG_WARN(params,
                 "Either no edge or vertex in file '%s', aborting",
                 params->inputfname);
        exit(EXIT_FAILURE);
    }
    if(params->modelcount > 1)
    {
        create_diff(&model, params);
    }
    if(params->verbose)
    {
        print_config(params);
        printf("Read file '%s' having |V| = %ld (%ld active), |E| = %ld @ %d evals\n", params->inputfname, model.vcount, model.active_vcount, model.ecount, 0);
    }
    time_t run_start_time = time(NULL);
    FitnessWrite* fitvals = malloc(sizeof(FitnessWrite) * params->max_evals);
    for(int i=0; i<params->max_evals; i++)
    {
        Individual ind;
        create_random_individual(&ind, model.vcount);
        ind.fitness = fitness(&ind, &model);
        decrement_change_countdown(&change_countdown, &model, params, i);
        if(params->savefname)
            fitvals[i] = fitness_ext(&ind, &model);
        free_individual(&ind);
    }
    if(params->savefname)
    {
        if(params->verbose)
            printf("Saving %ld individuals' fitness values to file %s\n", params->max_evals, params->savefname);
        write_meta_header(time(NULL) - run_start_time, 0, params->savefname);
        write_fitness(fitvals, params->max_evals, params->savefname, params->extended_write, 0);
    }
    if(params->verbose)
        printf("Reached %ld evaluations, quitting after %ld seconds\n", params->max_evals, time(NULL) - run_start_time);
    if(fitvals)
        free(fitvals);
    free_model(&model);
    return 0;
}


