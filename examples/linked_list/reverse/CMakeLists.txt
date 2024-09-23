cmake_minimum_required(VERSION 3.20)
project(reverse LANGUAGES C)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include_directories(include)

add_executable(reverse reverse.c)
add_executable(reverse_test test/reverse_test.c include/src/reverse_datatype.c include/cstar.h)