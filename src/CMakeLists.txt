message(STATUS ${CMAKE_CURRENT_SOURCE_DIR})

# ---------------------------------------------------------------------------- #
# TARGET
# archive library 
# ---------------------------------------------------------------------------- #
##
## source files
##
file(GLOB SRC_FILES 
    ${CMAKE_CURRENT_SOURCE_DIR}/ir/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/analysis/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/transform/[^_]*.cpp
)

##
## create lib
##
if(${COREIR_STATIC})
  add_library(${COREIR_LIB_NAME} STATIC ${SRC_FILES})
else()
  add_library(${COREIR_LIB_NAME} SHARED ${SRC_FILES})
endif()

add_library(${PROJECT_NAME}::${COREIR_LIB_NAME} ALIAS ${COREIR_LIB_NAME})

##
## compile features/options
##
target_compile_features(${COREIR_LIB_NAME} PUBLIC cxx_std_11)
coreir_set_compile_option(${COREIR_LIB_NAME})

##
## include paths
##
target_include_directories(${COREIR_LIB_NAME} 
  PUBLIC 
    $<INSTALL_INTERFACE:${COREIR_INCLUDE_INSTALL_DIR}>
    $<BUILD_INTERFACE:${COREIR_INCLUDE_BUILD_DIR}>
)


# ---------------------------------------------------------------------------- #
# LINK LIBRARIES
# external dependencies
# ---------------------------------------------------------------------------- #
target_link_libraries(${COREIR_LIB_NAME} PUBLIC dl)


# ---------------------------------------------------------------------------- #
# INSTALL
# install and export lib target
# ---------------------------------------------------------------------------- #
install(
  TARGETS ${COREIR_LIB_NAME}
  EXPORT  ${COREIR_TARGETS_EXPORT_NAME}
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
  RUNTIME DESTINATION bin
  INCLUDES DESTINATION ${COREIR_INCLUDE_INSTALL_DIR}
)

##
## copy to source dir for tests (legacy)
##
add_custom_command(
  TARGET ${COREIR_LIB_NAME}
  POST_BUILD
  COMMAND 
    ${CMAKE_COMMAND} -E copy 
    "$<TARGET_FILE:${COREIR_LIB_NAME}>" 
    "${CMAKE_SOURCE_DIR}/lib"
  COMMENT "Copying to lib/"
)

##
## include directory
##
install(
  DIRECTORY ${COREIR_INCLUDE_BUILD_DIR}
  #DESTINATION ${COREIR_INCLUDE_INSTALL_DIR}
  DESTINATION "." # XXX wrap the header in "coreir" to make this cleaner
  FILES_MATCHING PATTERN "*.h"
)


# ---------------------------------------------------------------------------- #
# TARGET
# coreir executable
# ---------------------------------------------------------------------------- #
add_executable(
  ${COREIR_EXE_NAME} 
  ${CMAKE_CURRENT_SOURCE_DIR}/binary/coreir.cpp
)
target_link_libraries(${COREIR_EXE_NAME} PUBLIC ${COREIR_LIB_NAME})
set_target_properties(${COREIR_EXE_NAME} PROPERTIES RUNTIME_OUTPUT_NAME coreir)

coreir_set_compile_option(${COREIR_EXE_NAME})


# ---------------------------------------------------------------------------- #
# INSTALL
# install coreir executable 
# ---------------------------------------------------------------------------- #
install(
  TARGETS ${COREIR_EXE_NAME}
  RUNTIME DESTINATION bin
)

##
## copy to source dir for tests (legacy)
##
add_custom_command(
  TARGET ${COREIR_EXE_NAME}
  POST_BUILD
  COMMAND 
    ${CMAKE_COMMAND} -E copy 
    "$<TARGET_FILE:${COREIR_EXE_NAME}>" 
    "${CMAKE_SOURCE_DIR}/bin"
  COMMENT "Copying to bin/"
)


#Create the coreir libraries
set(COREIR_SUBLIB_PREFIX ${COREIR_LIB_NAME})
add_subdirectory(libs)

#create simulator library
set(COREIR_SIMLIB coreirsim)
add_subdirectory(simulator)

#create coreir-c libraries
set(COREIR_LIB_C "${COREIR_LIB_NAME}-c")
set(COREIR_SIMLIB_C "${COREIR_SIMLIB}-c")
add_subdirectory(coreir-c)


# ---------------------------------------------------------------------------- #
# TARGET
# interpreter executable
# ---------------------------------------------------------------------------- #
add_executable(
  ${COREIR_ITP_NAME} 
  ${CMAKE_CURRENT_SOURCE_DIR}/binary/interpreter.cpp
)
target_link_libraries(${COREIR_ITP_NAME} PUBLIC ${COREIR_LIB_NAME})
target_link_libraries(${COREIR_ITP_NAME} PUBLIC ${COREIR_SIMLIB})
target_link_libraries(${COREIR_ITP_NAME} PUBLIC "${COREIR_SUBLIB_PREFIX}-commonlib")

coreir_set_compile_option(${COREIR_ITP_NAME})


# ---------------------------------------------------------------------------- #
# INSTALL
# install interpreter executable 
# ---------------------------------------------------------------------------- #
install(
  TARGETS ${COREIR_ITP_NAME}
  RUNTIME DESTINATION bin
)

##
## copy to source dir for tests (legacy)
##
add_custom_command(
  TARGET ${COREIR_ITP_NAME}
  POST_BUILD
  COMMAND 
    ${CMAKE_COMMAND} -E copy 
    "$<TARGET_FILE:${COREIR_ITP_NAME}>" 
    "${CMAKE_SOURCE_DIR}/bin"
  COMMENT "Copying to bin/"
)


# ---------------------------------------------------------------------------- #
# TARGET
# simulator executable
# ---------------------------------------------------------------------------- #
add_executable(
  ${COREIR_SIM_NAME} 
  ${CMAKE_CURRENT_SOURCE_DIR}/binary/simulator.cpp
)
target_link_libraries(${COREIR_SIM_NAME} PUBLIC ${COREIR_LIB_NAME})
target_link_libraries(${COREIR_SIM_NAME} PUBLIC ${COREIR_SIMLIB})
target_link_libraries(${COREIR_SIM_NAME} PUBLIC "${COREIR_SUBLIB_PREFIX}-commonlib")

coreir_set_compile_option(${COREIR_SIM_NAME})


# ---------------------------------------------------------------------------- #
# INSTALL
# install simulator executable 
# ---------------------------------------------------------------------------- #
install(
  TARGETS ${COREIR_SIM_NAME}
  RUNTIME DESTINATION bin
)

##
## copy to source dir for tests (legacy)
##
add_custom_command(
  TARGET ${COREIR_SIM_NAME}
  POST_BUILD
  COMMAND 
    ${CMAKE_COMMAND} -E copy 
    "$<TARGET_FILE:${COREIR_SIM_NAME}>" 
    "${CMAKE_SOURCE_DIR}/bin"
  COMMENT "Copying to bin/"
)

