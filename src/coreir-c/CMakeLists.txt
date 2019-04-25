set(CMAKE_MACOSX_RPATH 1)
set(CMAKE_INSTALL_RPATH "${LIBRARY_OUTPUT_PATH}")


#Create libcoreir-c
project(coreir-c)
set(CSRC coreir-c.cpp types-c.cpp values-c.cpp)

if (STATIC)
    add_library(coreir-c STATIC ${SRC_FILES})
else()
    add_library(coreir-c SHARED ${SRC_FILES})
endif()
target_include_directories(coreir-c PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
target_link_libraries(coreir-c PUBLIC coreir)

#Create libcoreirsim-c
project(coreirsim-c)
set(CSIMSRC simulator-c.cpp)

if (STATIC)
    add_library(coreirsim-c STATIC ${SRC_FILES})
else()
    add_library(coreirsim-c SHARED ${SRC_FILES})
endif()
target_include_directories(coreirsim-c PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
target_link_libraries(coreirsim-c PUBLIC coreir)
target_link_libraries(coreirsim-c PUBLIC coreirsim)

#Install libcoreir
install(
    TARGETS coreir-c coreirsim-c
    DESTINATION lib
)
add_custom_command(
  TARGET coreir-c
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir-c>" "${CMAKE_SOURCE_DIR}/lib/"
  COMMENT "Copying to lib/"
)

add_custom_command(
  TARGET coreirsim-c
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreirsim-c>" "${CMAKE_SOURCE_DIR}/lib/"
  COMMENT "Copying to lib/"
)



