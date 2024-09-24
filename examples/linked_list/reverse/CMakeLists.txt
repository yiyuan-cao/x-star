cmake_minimum_required(VERSION 3.20)
project(reverse LANGUAGES C)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_executable(reverse reverse.c)
add_executable(reverse_test test/reverse_test.c test/reverse_datatype.c test/cstar_test.h)
# add_executable(reverse_proof proof/reverse_proof.c proof/reverse_datatype.c proof/cstar_test.h)