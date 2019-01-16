message(STATUS ${CMAKE_CURRENT_SOURCE_DIR})
file(GLOB SRC_FILES 
    ${CMAKE_CURRENT_SOURCE_DIR}/ir/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/analysis/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/transform/[^_]*.cpp
)



#Create libcoreir
set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")

add_library(coreir SHARED ${SRC_FILES})
target_include_directories(coreir PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)


#Create coreir executable
add_executable(coreir-bin ${CMAKE_CURRENT_SOURCE_DIR}/binary/coreir.cpp)
find_library(COREIR_LIB coreir)
target_link_libraries(coreir-bin PUBLIC ${COREIR_LIB})
target_include_directories(coreir-bin PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)
set_target_properties(coreir-bin
    PROPERTIES OUTPUT_NAME coreir
)



#Create the coreir libraries
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/libs)


#create simulator library
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/simulator)


#create interpreter executable
add_executable(coreir-interpreter ${CMAKE_CURRENT_SOURCE_DIR}/binary/interpreter.cpp)
find_library(COREIR_LIB coreir)
target_link_libraries(coreir-interpreter PUBLIC ${COREIR_LIB})
find_library(COREIRSIM_LIB coreirsim)
find_library(COMMONLIB coreir-commonlib)
target_link_libraries(coreir-interpreter PUBLIC ${COREIRSIM_LIB})
target_link_libraries(coreir-interpreter PUBLIC ${COMMONLIB})
target_include_directories(coreir-interpreter PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)

#create simulator executable
add_executable(coreir-simulator ${CMAKE_CURRENT_SOURCE_DIR}/binary/simulator.cpp)
find_library(COREIR_LIB coreir)
target_link_libraries(coreir-simulator PUBLIC ${COREIR_LIB})
find_library(COREIRSIM_LIB coreirsim)
find_library(COMMONLIB coreir-commonlib)
target_link_libraries(coreir-simulator PUBLIC ${COREIRSIM_LIB})
target_link_libraries(coreir-simulator PUBLIC ${COMMONLIB})
target_include_directories(coreir-simulator PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)
