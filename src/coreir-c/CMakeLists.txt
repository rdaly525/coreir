##
## libcoreir-c
##
project(${COREIR_LIB_C} LANGUAGES CXX)
set(CSRC coreir-c.cpp types-c.cpp values-c.cpp)

if(${COREIR_STATIC})
  add_library(${COREIR_LIB_C} STATIC ${CSRC})
else()
  add_library(${COREIR_LIB_C} SHARED ${CSRC})
endif()

target_link_libraries(${COREIR_LIB_C} PUBLIC ${COREIR_LIB_NAME})

install(
  TARGETS ${COREIR_LIB_C}
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)


##
## libcoreirsim-c
##
project(${COREIR_SIMLIB_C} LANGUAGES CXX)
set(CSIMSRC simulator-c.cpp)

if(${COREIR_STATIC})
  add_library(${COREIR_SIMLIB_C} STATIC ${CSIMSRC})
else()
  add_library(${COREIR_SIMLIB_C} SHARED ${CSIMSRC})
endif()

target_link_libraries(${COREIR_SIMLIB_C} PUBLIC ${COREIR_LIB_NAME})
target_link_libraries(${COREIR_SIMLIB_C} PUBLIC ${COREIR_SIMLIB})

install(
  TARGETS ${COREIR_SIMLIB_C}
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

