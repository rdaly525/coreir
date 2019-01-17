set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")


#Create libcoreir-c
project(coreir-c)
set(CSRC coreir-c.cpp types-c.cpp values-c.cpp)

add_library(coreir-c SHARED ${CSRC})
target_include_directories(coreir-c PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
target_link_libraries(coreir-c PUBLIC coreir)

#Create libcoreirsim-c
project(coreirsim-c)
set(CSIMSRC simulator-c.cpp)

add_library(coreirsim-c SHARED ${CSIMSRC})
target_include_directories(coreirsim-c PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
target_link_libraries(coreirsim-c PUBLIC coreir)
target_link_libraries(coreirsim-c PUBLIC coreirsim)


