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

set(CMAKE_CXX_FLAGS "-std=c++17 -Wall -fPIC -Werror ${STATIC_FLAGS}")

# Based on
# https://github.com/google/googletest/tree/master/googletest#incorporating-into-an-existing-cmake-project
# 
# Download and unpack verilogAST at configure time
configure_file(CMakeLists.txt.in verilogAST-download/CMakeLists.txt)
execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/verilogAST-download )
if(result)
    message(FATAL_ERROR "CMake step for verilogAST failed: ${result}")
endif()
execute_process(COMMAND ${CMAKE_COMMAND} --build .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/verilogAST-download )
if(result)
    message(FATAL_ERROR "Build step for verilogAST failed: ${result}")
endif()

# Add verilogAST directly to our build.
add_subdirectory(${CMAKE_CURRENT_BINARY_DIR}/verilogAST-src
                 ${CMAKE_CURRENT_BINARY_DIR}/verilogAST-build
                 EXCLUDE_FROM_ALL)
include_directories(${CMAKE_CURRENT_BINARY_DIR}/verilogAST-src/include)

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

