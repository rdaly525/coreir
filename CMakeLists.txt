cmake_minimum_required(VERSION 2.8)

project(coreir)




set(CMAKE_CXX_FLAGS "-std=c++11 -Wall -fPIC -Werror")
#CXXFLAGS = -std=c++11 -Wall -fPIC -Werror -ferror-limit=5


set(EXECUTABLE_OUTPUT_PATH ${CMAKE_BINARY_DIR}/bin)
set(LIBRARY_OUTPUT_PATH ${CMAKE_BINARY_DIR}/lib)
set(INCLUDE_OUTPUT_PATH ${CMAKE_BINARY_DIR}/include)

add_subdirectory(${CMAKE_SOURCE_DIR}/src)

install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/include/
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)


