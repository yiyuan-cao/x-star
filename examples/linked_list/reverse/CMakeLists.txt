cmake_minimum_required(VERSION 3.11.4)
project(reverse LANGUAGES C)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include(FetchContent)

FetchContent_Declare(
    datatype99
    URL https://github.com/Hirrolot/datatype99/archive/refs/tags/v1.6.4.tar.gz
)

FetchContent_MakeAvailable(datatype99)

add_executable(reverse reverse.c)
target_link_libraries(reverse datatype99)

# Disable full macro expansion backtraces for Metalang99.
if(CMAKE_C_COMPILER_ID STREQUAL "Clang")
  target_compile_options(reverse PRIVATE -fmacro-backtrace-limit=1)
elseif(CMAKE_C_COMPILER_ID STREQUAL "GNU")
  target_compile_options(reverse PRIVATE -ftrack-macro-expansion=0)
endif()