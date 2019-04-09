message(STATUS ${CMAKE_CURRENT_SOURCE_DIR})
file(GLOB SRC_FILES 
    ${CMAKE_CURRENT_SOURCE_DIR}/ir/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/analysis/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/transform/[^_]*.cpp
)

#Create libcoreir
set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")

if (STATIC)
    add_library(coreir STATIC ${SRC_FILES})
else()
    add_library(coreir SHARED ${SRC_FILES})
endif()

target_include_directories(coreir PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)
target_link_libraries(coreir dl)

#Install libcoreir
install(
    TARGETS coreir
    DESTINATION lib
)

add_custom_command(
  TARGET coreir
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir>" "${CMAKE_SOURCE_DIR}/lib/"
  COMMENT "Copying to lib/"
)

#Create coreir executable
add_executable(coreir-bin ${CMAKE_CURRENT_SOURCE_DIR}/binary/coreir.cpp)
target_link_libraries(coreir-bin PUBLIC coreir)

target_include_directories(coreir-bin PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)
set_target_properties(coreir-bin
    PROPERTIES OUTPUT_NAME coreir
)
add_custom_command(
  TARGET coreir-bin
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir-bin>" "${CMAKE_SOURCE_DIR}/bin/"
  COMMENT "Copying to bin/"
)


install(
    TARGETS coreir-bin
    DESTINATION bin
)

#Create the coreir libraries
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/libs)

#create simulator library
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/simulator)

#create coreir-c libraries
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/coreir-c)


#create interpreter executable
add_executable(coreir-interpreter ${CMAKE_CURRENT_SOURCE_DIR}/binary/interpreter.cpp)
target_link_libraries(coreir-interpreter PUBLIC coreir)
target_link_libraries(coreir-interpreter PUBLIC coreirsim)
target_link_libraries(coreir-interpreter PUBLIC coreir-commonlib)
target_include_directories(coreir-interpreter PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)

#create simulator executable
add_executable(coreir-simulator ${CMAKE_CURRENT_SOURCE_DIR}/binary/simulator.cpp)
target_link_libraries(coreir-simulator PUBLIC coreir)
target_link_libraries(coreir-simulator PUBLIC coreirsim)
target_link_libraries(coreir-simulator PUBLIC coreir-commonlib)
target_include_directories(coreir-simulator PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)

install(
    TARGETS coreir-interpreter coreir-simulator
    DESTINATION bin
)

add_custom_command(
  TARGET coreir-interpreter
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir-interpreter>" "${CMAKE_SOURCE_DIR}/bin/"
  COMMENT "Copying to bin/"
)

add_custom_command(
  TARGET coreir-simulator
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir-simulator>" "${CMAKE_SOURCE_DIR}/bin/"
  COMMENT "Copying to bin/"
)
