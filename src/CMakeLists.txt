message(STATUS ${CMAKE_CURRENT_SOURCE_DIR})
file(GLOB SRC_FILES 
    ${CMAKE_CURRENT_SOURCE_DIR}/ir/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/analysis/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/analysis/verilog/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/passes/transform/[^_]*.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/common/[^_]*.cpp
)

#Create libcoreir
# use, i.e. don't skip the full RPATH for the build tree
SET(CMAKE_SKIP_BUILD_RPATH  FALSE)

# when building, don't use the install RPATH already
# (but later on when installing)
SET(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)

set(CMAKE_MACOSX_RPATH 1)
SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")

# add the automatically determined parts of the RPATH
# which point to directories outside the build tree to the install RPATH
SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)


# the RPATH to be used when installing, but only if it's not a system directory
LIST(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${CMAKE_INSTALL_PREFIX}/lib" isSystemDir)
IF("${isSystemDir}" STREQUAL "-1")
   SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
ENDIF("${isSystemDir}" STREQUAL "-1")

if (STATIC)
    add_library(coreir STATIC ${SRC_FILES})
else()
    add_library(coreir SHARED ${SRC_FILES})
endif()

target_include_directories(coreir PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)
target_link_libraries(coreir dl)
target_link_libraries(coreir verilogAST)

if (COREIR_PROFILE)
    # requires gperftools, e.g. brew install gperftools
    set (Gperftools_DIR "${CMAKE_CURRENT_LIST_DIR}/../cmake/")
    find_package(Gperftools REQUIRED)
    target_link_libraries(coreir ${GPERFTOOLS_LIBRARIES})
endif()

#Install libcoreir
install(
    TARGETS coreir
    DESTINATION lib
)

add_custom_command(
  TARGET coreir
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir>" "${CMAKE_SOURCE_DIR}/lib/"
  COMMENT "Copying to lib/"
)

add_custom_command(
  TARGET coreir
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "${CMAKE_BINARY_DIR}/lib/libverilogAST${CMAKE_SHARED_LIBRARY_SUFFIX}" "${CMAKE_SOURCE_DIR}/lib/"
  COMMENT "Copying libverilogAST"
)

install(FILES "${CMAKE_SOURCE_DIR}/lib/libverilogAST${CMAKE_SHARED_LIBRARY_SUFFIX}" DESTINATION lib)

add_custom_command(
  TARGET coreir
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "${CMAKE_BINARY_DIR}/verilogAST-src/include/verilogAST.hpp" "${CMAKE_SOURCE_DIR}/include/"
  COMMENT "Copying verilogAST.hpp"
)

#Create coreir executable
add_executable(coreir-bin ${CMAKE_CURRENT_SOURCE_DIR}/binary/coreir.cpp)
target_link_libraries(coreir-bin PUBLIC coreir)
target_include_directories(coreir-bin PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)
set_target_properties(coreir-bin
    PROPERTIES OUTPUT_NAME coreir
    COMPILE_FLAGS "-DCOREIR_VERSION=\\\"${COREIR_VERSION}\\\" -DGIT_SHA1=\\\"${GIT_SHA1}\\\""
)
add_custom_command(
  TARGET coreir-bin
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir-bin>" "${CMAKE_SOURCE_DIR}/bin/"
  COMMENT "Copying to bin/"
)


install(
    TARGETS coreir-bin
    DESTINATION bin
)

#Create the coreir libraries
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/libs)

#create simulator library
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/simulator)

#create coreir-c libraries
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/coreir-c)


#create interpreter executable
add_executable(coreir-interpreter ${CMAKE_CURRENT_SOURCE_DIR}/binary/interpreter.cpp)
target_link_libraries(coreir-interpreter PUBLIC coreir)
target_link_libraries(coreir-interpreter PUBLIC coreirsim)
target_link_libraries(coreir-interpreter PUBLIC coreir-commonlib)
target_include_directories(coreir-interpreter PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)

#create simulator executable
add_executable(coreir-simulator ${CMAKE_CURRENT_SOURCE_DIR}/binary/simulator.cpp)
target_link_libraries(coreir-simulator PUBLIC coreir)
target_link_libraries(coreir-simulator PUBLIC coreirsim)
target_link_libraries(coreir-simulator PUBLIC coreir-commonlib)
target_include_directories(coreir-simulator PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../include)

install(
    TARGETS coreir-interpreter coreir-simulator
    DESTINATION bin
)

add_custom_command(
  TARGET coreir-interpreter
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir-interpreter>" "${CMAKE_SOURCE_DIR}/bin/"
  COMMENT "Copying to bin/"
)

add_custom_command(
  TARGET coreir-simulator
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy "$<TARGET_FILE:coreir-simulator>" "${CMAKE_SOURCE_DIR}/bin/"
  COMMENT "Copying to bin/"
)
