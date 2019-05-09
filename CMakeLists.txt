cmake_minimum_required(VERSION 3.8)

if(${CMAKE_VERSION} VERSION_LESS 3.13)
  cmake_policy(VERSION ${CMAKE_MAJOR_VERSION}.${CMAKE_MINOR_VERSION})
else()
  cmake_policy(VERSION 3.13)
endif()


# ---------------------------------------------------------------------------- #
# PROJECT
# name version language
# ---------------------------------------------------------------------------- #
project(coreir VERSION     0.0.30
               LANGUAGES   CXX
)


# ---------------------------------------------------------------------------- #
# OPTION
# build configuration
# ---------------------------------------------------------------------------- #
option(COREIR_STATIC "Statically link everything"                           OFF)


# ---------------------------------------------------------------------------- #
# VARARIABLE
# alias and configurations
# ---------------------------------------------------------------------------- #
set(COREIR_TARGET_NAME                ${PROJECT_NAME})
set(COREIR_CONFIG_INSTALL_DIR         "lib/cmake/${PROJECT_NAME}" CACHE INTERNAL "")
set(COREIR_INCLUDE_INSTALL_DIR        "include")
set(COREIR_INCLUDE_BUILD_DIR          "${PROJECT_SOURCE_DIR}/include")
set(COREIR_INSTALL_RPATH              "${CMAKE_INSTALL_PREFIX}/lib")
set(COREIR_TARGETS_EXPORT_NAME        "${PROJECT_NAME}Targets")
set(COREIR_CMAKE_CONFIG_TEMPLATE      "cmake/config.cmake.in")
set(COREIR_CMAKE_CONFIG_DIR           "${CMAKE_CURRENT_BINARY_DIR}")
set(COREIR_CMAKE_PROJECT_TARGETS_FILE "${PROJECT_NAME}Targets.cmake")

set(COREIR_CMAKE_VERSION_CONFIG_FILE 
  "${COREIR_CMAKE_CONFIG_DIR}/${PROJECT_NAME}ConfigVersion.cmake")

set(COREIR_CMAKE_PROJECT_CONFIG_FILE
  "${COREIR_CMAKE_CONFIG_DIR}/${PROJECT_NAME}Config.cmake")


# ---------------------------------------------------------------------------- #
# External dependencies
# ---------------------------------------------------------------------------- #
##
## Make sure that custom modules can be found.
##
set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake" ${CMAKE_MODULE_PATH})


# ---------------------------------------------------------------------------- #
# Misc
# ---------------------------------------------------------------------------- #
##
## Compiler options
##
if(${CMAKE_COMPILER_IS_GNUCXX})

  # require at least gcc 4.8
  if(CMAKE_CXX_COMPILER_VERSION VERSION_LESS 4.9)
    message(FATAL_ERROR "GCC version must be at least 4.9!")
  endif()

else() 

  message(WARNING "You are using an untested compiler")

endif()

macro(coreir_set_compile_option IARG_TARGET_NAME)

  if(${CMAKE_COMPILER_IS_GUNCXX})
    target_compile_options(${IARG_TARGET_NAME} PRIVATE "-Wall")
    target_compile_options(${IARG_TARGET_NAME} PRIVATE "-Werror")
  endif()

  set_property(
    TARGET ${IARG_TARGET_NAME}
    PROPERTY POSITION_INDEPENDENT_CODE ON
  )

endmacro()


##
## RPATH for shared target
##
set(CMAKE_INSTALL_RPATH ${COREIR_INSTALL_RPATH})
set(CMAKE_MACOSX_RPATH TRUE)


# ---------------------------------------------------------------------------- #
# TARGET
# library target
# ---------------------------------------------------------------------------- #
set(COREIR_LIB_NAME ${COREIR_TARGET_NAME})
set(COREIR_EXE_NAME ${COREIR_TARGET_NAME}-bin)
set(COREIR_ITP_NAME ${COREIR_TARGET_NAME}-interpreter)
set(COREIR_SIM_NAME ${COREIR_TARGET_NAME}-simulator)
add_subdirectory(src)


# ---------------------------------------------------------------------------- #
# INSTALL
# project related
# ---------------------------------------------------------------------------- #
##
## forward version for find_package
##
include(CMakePackageConfigHelpers)
write_basic_package_version_file(
  ${COREIR_CMAKE_VERSION_CONFIG_FILE} 
  COMPATIBILITY SameMajorVersion # AnyNewVersion
)

##
## cmake config
##
configure_file(
  ${COREIR_CMAKE_CONFIG_TEMPLATE}
  ${COREIR_CMAKE_PROJECT_CONFIG_FILE}
  @ONLY
)

install(
  FILES ${COREIR_CMAKE_PROJECT_CONFIG_FILE} ${COREIR_CMAKE_VERSION_CONFIG_FILE}
  DESTINATION ${COREIR_CONFIG_INSTALL_DIR}
)

##
## project export
##
install(
  EXPORT ${COREIR_TARGETS_EXPORT_NAME}
  DESTINATION ${COREIR_CONFIG_INSTALL_DIR}
  NAMESPACE ${PROJECT_NAME}::
  FILE ${COREIR_CMAKE_PROJECT_TARGETS_FILE}
)

export(
  TARGETS ${COREIR_LIB_NAME}
  NAMESPACE ${PROJECT_NAME}::
  FILE ${COREIR_CMAKE_PROJECT_TARGETS_FILE}
)

if(${COREIR_EXPORT_PACKAGE})
  export(PACKAGE ${PROJECT_NAME})
endif()


# ---------------------------------------------------------------------------- #
# UNINSTALL
# uninstall files listed in install_manifest.txt
# ---------------------------------------------------------------------------- #
if(NOT TARGET uninstall)
  configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cmake_uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake/cmake_uninstall.cmake"
    IMMEDIATE @ONLY
  )

  add_custom_target(uninstall
    COMMAND 
      ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake/cmake_uninstall.cmake
  )

endif()

