cmake_minimum_required(VERSION 2.6)

project(coreir)

set(EXECUTABLE_OUTPUT_PATH ${CMAKE_BINARY_DIR}/bin)
set(LIBRARY_OUTPUT_PATH ${CMAKE_BINARY_DIR}/lib)
set(INCLUDE_OUTPUT_PATH ${CMAKE_BINARY_DIR}/include)

add_subdirectory(${CMAKE_SOURCE_DIR}/src)
#file(GLOB_RECURSE sources "${CMAKE_SOURCE_DIR}/src/*.cpp")
#add_library(test ${sources})

