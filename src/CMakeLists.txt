message(STATUS ${CMAKE_CURRENT_SOURCE_DIR})
file(GLOB SRC_FILES 
    ${CMAKE_CURRENT_SOURCE_DIR}/ir/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/analysis/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/transform/[^_]*.cpp
)

set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")

add_library(coreir SHARED ${SRC_FILES})
target_include_directories(coreir PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)

#message(STATUS ${SRC_FILES})
#message(STATUS "1")
#add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/ir)
#message(STATUS "2")
#message(STATUS ${SRC_FILES})
#message(STATUS "3")
#add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/passes)
#add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/simulator)
#add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/coreir-c)
#add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/libs)

