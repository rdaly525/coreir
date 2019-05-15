##
## libcoreirsim
##
project(${COREIR_SIMLIB} LANGUAGES CXX)

file(GLOB SRC_FILES 
    ${CMAKE_CURRENT_SOURCE_DIR}/[^_]*.cpp
)

add_library(${COREIR_SIMLIB} ${SRC_FILES})

target_link_libraries(${COREIR_SIMLIB} PUBLIC ${COREIR_LIB_NAME})

coreir_set_compile_option(${COREIR_SIMLIB})

install(
  TARGETS ${COREIR_SIMLIB}
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

add_custom_command(
  TARGET ${COREIR_SIMLIB}
  POST_BUILD
  COMMAND 
    ${CMAKE_COMMAND} -E copy 
    "$<TARGET_FILE:${COREIR_SIMLIB}>" 
    "${CMAKE_SOURCE_DIR}/lib"
  COMMENT "Copying to lib/"
)

