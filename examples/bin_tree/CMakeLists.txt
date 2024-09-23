cmake_minimum_required(VERSION 3.10)
project(BinTreeProject)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include_directories(${CMAKE_SOURCE_DIR}/include)

add_executable(BinTreeTest bin_tree_test.c)
add_library(BinTreeDataType bin_tree_datatype.c)

target_link_libraries(BinTreeTest BinTreeDataType)