cmake_minimum_required(VERSION 3.20)
project(reverse LANGUAGES C)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_compile_options(-Wno-attributes) # suppress non-standard attributes warning
set(CMAKE_C_STANDARD 23)

add_executable(reverse reverse.c)
add_executable(reverse_test test/reverse_test.c test/reverse_datatype.c)