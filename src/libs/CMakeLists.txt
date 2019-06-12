

#Common things for  creating the libraries
#find_library(COREIR_LIB coreir)
#message(STATUS ${COREIR_LIB})
set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")

set(COREIRLIBS
    "commonlib"
    "rtlil"
    "aetherlinglib"
    "ice40"
    "float"
    "float_CW"
    "float_DW"
)
foreach(CLIB ${COREIRLIBS})
    #message(STATUS ${COREIRLIB})
    set(COREIRLIB "coreir-${CLIB}")
    project(${COREIRLIB})

    set(SRC_FILES "${CMAKE_CURRENT_SOURCE_DIR}/${CLIB}.cpp")

    add_library(${COREIRLIB} SHARED ${SRC_FILES})
    target_include_directories(${COREIRLIB} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
    target_link_libraries(${COREIRLIB} PUBLIC coreir)
    install(
        TARGETS ${COREIRLIB}
        DESTINATION lib
    )
  add_custom_command(
    TARGET ${COREIRLIB}
    POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:${COREIRLIB}>" "${CMAKE_SOURCE_DIR}/lib/"
    COMMENT "Copying to lib/"
  )

endforeach()


