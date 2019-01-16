project(coreirsim)

file(GLOB SRC_FILES 
    ${CMAKE_CURRENT_SOURCE_DIR}/[^_]*.cpp
)

#Create libcoreir
set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")

add_library(coreirsim SHARED ${SRC_FILES})
target_include_directories(coreirsim PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
find_library(COREIR_LIB coreir)
target_link_libraries(coreirsim PUBLIC ${COREIR_LIB})

