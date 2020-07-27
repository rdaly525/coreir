# Based on
# https://github.com/google/googletest/tree/master/googletest#incorporating-into-an-existing-cmake-project
# 
# Download and unpack gtest at configure time
configure_file(CMakeLists.txt.in gtest-download/CMakeLists.txt)
execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/gtest-download )
if(result)
    message(FATAL_ERROR "CMake step for gtest failed: ${result}")
endif()
execute_process(COMMAND ${CMAKE_COMMAND} --build .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/gtest-download )
if(result)
    message(FATAL_ERROR "Build step for gtest failed: ${result}")
endif()

# Add googletest directly to our build. This defines
# the gtest and gtest_main targets.
add_subdirectory(${CMAKE_CURRENT_BINARY_DIR}/googletest-src
                 ${CMAKE_CURRENT_BINARY_DIR}/googletest-build
                 EXCLUDE_FROM_ALL)

include_directories(${CMAKE_SOURCE_DIR}/include)

enable_testing()
add_executable(test_verilog test_verilog.cpp)
target_link_libraries(test_verilog gtest_main coreir coreir-commonlib)
add_test(NAME test_verilog COMMAND test_verilog WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)

add_executable(test_inline_wires test_inline_wires.cpp)
target_link_libraries(test_inline_wires gtest_main coreir coreir-commonlib)
add_test(NAME test_inline_wires COMMAND test_inline_wires WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)

add_executable(test_hierarchical_select test_hierarchical_select.cpp)
target_link_libraries(test_hierarchical_select gtest_main coreir coreir-commonlib)
add_test(NAME test_hierarchical_select COMMAND test_hierarchical_select WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)

add_executable(test_isolate test_isolate.cpp)
target_link_libraries(test_isolate gtest_main coreir coreir-commonlib)
add_test(NAME test_isolate COMMAND test_isolate WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)

add_executable(test_slice test_slice.cpp)
target_link_libraries(test_slice gtest_main coreir coreir-commonlib)
add_test(NAME test_slice COMMAND test_slice WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)

add_executable(test_if_reconstruction test_if_reconstruction.cpp)
target_link_libraries(test_if_reconstruction gtest_main coreir
                      coreir-commonlib)
add_test(NAME test_if_reconstruction COMMAND test_if_reconstruction
         WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)

add_executable(test_memory test_memory.cpp)
target_link_libraries(test_memory gtest_main coreir coreir-commonlib)
add_test(NAME test_memory COMMAND test_memory WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)

add_executable(test_flattentypes2 test_flattentypes2.cpp)
target_link_libraries(test_flattentypes2 gtest_main coreir coreir-commonlib)
add_test(NAME test_flattentypes2 COMMAND test_flattentypes2 WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests/gtest)
