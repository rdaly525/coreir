

#Common things for  creating the libraries
find_library(COREIR_LIB coreir)
set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")

set(COREIRLIBS
    "commonlib"
    "rtlil"
    "aetherlinglib"
    "ice40"
)
foreach(COREIRLIB ${COREIRLIBS})
    message(STATUS ${COREIRLIB})

    project(${COREIRLIB})

    set(SRC_FILES "${CMAKE_CURRENT_SOURCE_DIR}/${COREIRLIB}.cpp")

    add_library(${COREIRLIB} SHARED ${SRC_FILES})
    target_include_directories(${COREIRLIB} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
    target_link_libraries(${COREIRLIB} PUBLIC ${COREIR_LIB})
    set_target_properties(${COREIRLIB}
        PROPERTIES OUTPUT_NAME "coreir-${COREIRLIB}"
    )


endforeach()


