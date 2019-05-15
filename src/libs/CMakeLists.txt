##
## Macro for creating sub-units
##
macro(add_coreir_sub_lib CLIB)
  set(COREIR_SUB_LIB "${COREIR_SUBLIB_PREFIX}-${CLIB}")
  project(${COREIR_SUB_LIB} LANGUAGES CXX)

  set(SRC_FILES "${CMAKE_CURRENT_SOURCE_DIR}/${CLIB}.cpp")

  # create lib
  add_library(${COREIR_SUB_LIB} ${SRC_FILES})

  target_link_libraries(${COREIR_SUB_LIB} PUBLIC ${COREIR_LIB_NAME})

  # compile features/options
  coreir_set_compile_option(${COREIR_SUB_LIB})

  # install lib
  install(
    TARGETS ${COREIR_SUB_LIB}
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
  )

  # copy to source dir for tests (legacy)
  add_custom_command(
    TARGET ${COREIR_SUB_LIB}
    POST_BUILD
    COMMAND 
      ${CMAKE_COMMAND} -E copy 
      "$<TARGET_FILE:${COREIR_SUB_LIB}>" 
      "${CMAKE_SOURCE_DIR}/lib"
    COMMENT "Copying to lib/"
  )

endmacro()

add_coreir_sub_lib("commonlib")
add_coreir_sub_lib("rtlil")
add_coreir_sub_lib("aetherlinglib")
add_coreir_sub_lib("ice40")
add_coreir_sub_lib("float")

