##
## Macro for creating sub-units
##
macro(add_coreir_sub_lib CLIB)
  set(COREIR_SUB_LIB "${COREIR_SUBLIB_PREFIX}-${CLIB}")
  project(${COREIR_SUB_LIB} LANGUAGES CXX)

  set(SRC_FILES "${CMAKE_CURRENT_SOURCE_DIR}/${CLIB}.cpp")

  if(${COREIR_STATIC})
    add_library(${COREIR_SUB_LIB} STATIC ${SRC_FILES})
  else()
    add_library(${COREIR_SUB_LIB} SHARED ${SRC_FILES})
  endif()

  target_link_libraries(${COREIR_SUB_LIB} PUBLIC ${COREIR_LIB_NAME})

  install(
    TARGETS ${COREIR_SUB_LIB}
    #EXPORT 
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
  )

endmacro()

add_coreir_sub_lib("commonlib")
add_coreir_sub_lib("rtlil")
add_coreir_sub_lib("aetherlinglib")
add_coreir_sub_lib("ice40")
add_coreir_sub_lib("float")

