/* This file contains the variable and function declarations */
#include "monsel.h"
#include <stdio.h>
# ifndef _GLOBAL_H_
# define _GLOBAL_H_

# define INF 1.0e14
# define EPS 1.0e-14
# define E  2.71828182845905
# define PI 3.14159265358979
# define GNUPLOT_COMMAND "gnuplot -persist"

typedef struct FitnessWrite {
    Fitness fitness;
    unsigned long active_ecount;
    unsigned long active_ecount_w;
    unsigned long u_edges;
    unsigned long u_edges_w;
    unsigned long active_vcount;
    unsigned long moncount;
} FitnessWrite;

typedef struct GenerationData {
    double mean_edges;
    double std_edges;
    double mean_edges_w;
    double std_edges_w;
    double mean_moncount;
    double std_moncount;
} GenerationData;

typedef struct Vertex {
    unsigned long id;
    uint8_t active;
} Vertex;

typedef struct Edge {
    unsigned long src;
    unsigned long dst;
    uint8_t w;
    uint8_t active;
} Edge;

typedef struct AdjacencyList {
    unsigned long* edge_indices;
    unsigned int size;
} AdjacencyList;

typedef struct NetworkModel {
    unsigned long id;
    Edge *edges;
    Vertex *vertices;
    unsigned long ecount;
    unsigned long ecount_w;
    unsigned long active_ecount;
    unsigned long active_ecount_w;
    int *active_edge_idx;
    unsigned long vcount;
    unsigned long active_vcount;
    int *active_vertex_idx;
    AdjacencyList* adjlist;
} NetworkModel;

typedef struct Individual {
    Gene *values;
    int explored;
    unsigned long size;
    Fitness fitness;
    //Multi-Objective
    double constr_violation;
    double *xreal;
    double *constr;
    int rank;//rank for pareto front
    double *xbin; //corresponds to monitor count to minimize
    double *obj;
    double crowd_dist;

} Individual;

typedef struct Population {
    Individual* ind;
    unsigned long size;
    unsigned long _memsize;
    unsigned long maxsize;
} Population;

typedef struct Diversity {
    double *values;
    long next;
    long _memsize;
} Diversity;

typedef struct lists
{
    int index;
    struct lists *parent;
    struct lists *child;
}list;

extern int nreal;
extern int nbin;
extern int nobj;
extern int ncon;
extern int popsize;
extern double pcross_real;
extern double pcross_bin;
extern double pmut_real;
extern double pmut_bin;
extern double eta_c;
extern double eta_m;
extern int ngen;
extern int nbinmut;
extern int nrealmut;
extern int nbincross;
extern int nrealcross;
extern int *nbits;
extern double *min_realvar;
extern double *max_realvar;
extern double *min_binvar;
extern double *max_binvar;
extern int bitlength;
extern int choice;
extern int obj1;
extern int obj2;
extern int obj3;
extern int angle1;
extern int angle2;
extern int random_immigrant_ratio;

void allocate_memory_pop (Population *pop, int size);
void allocate_memory_ind (Individual *ind);
void deallocate_memory_pop (Population *pop, int size);
void deallocate_memory_ind (Individual *ind);

double maximum (double a, double b);
double minimum (double a, double b);

void crossover (Individual *parent1, Individual *parent2, Individual *child1, Individual *child2);
void realcross (Individual *parent1, Individual *parent2, Individual *child1, Individual *child2);
void bincross (Individual *parent1, Individual *parent2, Individual *child1, Individual *child2);

void assign_crowding_distance_list (Population *pop, list *lst, int front_size);
void assign_crowding_distance_indices (Population *pop, int c1, int c2);
void assign_crowding_distance (Population *pop, int *dist, int **obj_array, int front_size);

void decode_pop (Population *pop);
void decode_ind (Individual *ind);

void onthefly_display (Population *pop, FILE *gp, int ii);

int check_dominance (Individual *a, Individual *b);

void evaluate_pop (Population *pop);
void evaluate_ind (Individual *ind);

void fill_nondominated_sort (Population *mixed_pop);
void crowding_fill (Population *mixed_pop, Population *new_pop, int count, int front_size, list *cur);

void initialize_pop (Population *pop);
void initialize_ind (Individual *ind);

void insert (list *node, int x);
list* del (list *node);

void merge(Population *pop1, Population *pop2, Population *pop3);
void copy_ind (Individual *ind1, Individual *ind2);

void mutation_pop (Population *pop);
void mutation_ind (Individual *ind);
void bin_mutate_ind (Individual *ind);
void real_mutate_ind (Individual *ind);

void test_problem (double *xreal, double *xbin, int **gene, double *obj, double *constr);

void assign_rank_and_crowding_distance (Population *new_pop);

void report_pop (Population *pop, FILE *fpt);
void report_pop_all (Population *pop, FILE *fpt);
void report_feasible (Population *pop, FILE *fpt);
void report_ind (Individual *ind, FILE *fpt);

void quicksort_front_obj(Population *pop, int objcount, int obj_array[], int obj_array_size);
void q_sort_front_obj(Population *pop, int objcount, int obj_array[], int left, int right);
void quicksort_dist(Population *pop, int *dist, int front_size);
void q_sort_dist(Population *pop, int *dist, int left, int right);

void selection (Population *old_pop, Population *new_pop);
Individual* tournament (Individual *ind1, Individual *ind2);

# endif
