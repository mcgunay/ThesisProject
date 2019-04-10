cmake_minimum_required(VERSION 3.13)
project(ThesisProject)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_EXE_LINKER_FLAGS "-L/usr/local/lib/ -largp")
include_directories(/usr/local/include/)
set(resources monsel.h logging.h main.cpp monsel.cpp)

add_executable(ThesisProject ${resources})
target_include_directories(ThesisProject PUBLIC CMAKE_CURRENT_SOURCE_DIR)

target_link_libraries(ThesisProject m)

