##
## libcoreir-c
##
project(${COREIR_LIB_C} LANGUAGES CXX)
set(CSRC coreir-c.cpp types-c.cpp values-c.cpp)

add_library(${COREIR_LIB_C} ${CSRC})

target_link_libraries(${COREIR_LIB_C} PUBLIC ${COREIR_LIB_NAME})

coreir_set_compile_option(${COREIR_LIB_C})

install(
  TARGETS ${COREIR_LIB_C}
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

add_custom_command(
  TARGET ${COREIR_LIB_C}
  POST_BUILD
  COMMAND 
    ${CMAKE_COMMAND} -E copy 
    "$<TARGET_FILE:${COREIR_LIB_C}>" 
    "${CMAKE_SOURCE_DIR}/lib"
  COMMENT "Copying to lib/"
)

##
## libcoreirsim-c
##
project(${COREIR_SIMLIB_C} LANGUAGES CXX)
set(CSIMSRC simulator-c.cpp)

add_library(${COREIR_SIMLIB_C} ${CSIMSRC})

target_link_libraries(${COREIR_SIMLIB_C} PUBLIC ${COREIR_LIB_NAME})
target_link_libraries(${COREIR_SIMLIB_C} PUBLIC ${COREIR_SIMLIB})

coreir_set_compile_option(${COREIR_SIMLIB_C})

install(
  TARGETS ${COREIR_SIMLIB_C}
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)


add_custom_command(
  TARGET ${COREIR_SIMLIB_C}
  POST_BUILD
  COMMAND 
    ${CMAKE_COMMAND} -E copy 
    "$<TARGET_FILE:${COREIR_SIMLIB_C}>" 
    "${CMAKE_SOURCE_DIR}/lib"
  COMMENT "Copying to lib/"
)

