cmake_minimum_required(VERSION 2.8)

project(coreir)
option(STATIC "Statically link everything" OFF)


if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    # require at least gcc 4.8
    if (CMAKE_CXX_COMPILER_VERSION VERSION_LESS 4.9)
        message(FATAL_ERROR "GCC version must be at least 4.9!")
    endif()
else()
    message(WARNING "You are using an untested compiler")
endif()

if (STATIC)
    if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
        set(STATIC_FLAGS "-static-libgcc -static-libstdc++")
        add_definitions(-D_GLIBCXX_USE_CXX11_ABI=0)
    endif()
endif()

if(NOT DEFINED $ENV{FUNCUBUF_PATH})
    message(STATUS "THING environment variable defined")
endif()

LINK_DIRECTORIES($ENV{FUNCUBUF_PATH}/bin)
TARGET_LINK_LIBRARIES(funcubuf)

set(CMAKE_CXX_FLAGS "-std=c++11 -Wall -fPIC -Werror ${STATIC_FLAGS}")

set(EXECUTABLE_OUTPUT_PATH ${CMAKE_BINARY_DIR}/bin)
set(LIBRARY_OUTPUT_PATH ${CMAKE_BINARY_DIR}/lib)
set(INCLUDE_OUTPUT_PATH ${CMAKE_BINARY_DIR}/include)

add_subdirectory(${CMAKE_SOURCE_DIR}/src)

install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/include/
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)

add_custom_target(uninstall
  "${CMAKE_COMMAND}" -P "${CMAKE_SOURCE_DIR}/tools/cmake/uninstall.cmake"
)

