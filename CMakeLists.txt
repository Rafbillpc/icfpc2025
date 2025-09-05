cmake_minimum_required(VERSION 3.22)
message(STATUS "CMake version: ${CMAKE_VERSION}")
project(icfpc2025
  LANGUAGES CXX)

# Options
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_compile_options(
  -Wall -Wextra
  -Wno-unused-parameter -Wno-unused-function -Wno-unused-const-variable
)
add_compile_options(-march=native)

set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
add_link_options("-fuse-ld=mold")

IF(CMAKE_BUILD_TYPE MATCHES RelWithDebInfo)
  add_compile_options(-O3 -ffast-math)
ENDIF(CMAKE_BUILD_TYPE MATCHES RelWithDebInfo)

IF(CMAKE_BUILD_TYPE MATCHES Debug)
  add_link_options(-fsanitize=address)
  add_compile_options(-fsanitize=address)
ENDIF(CMAKE_BUILD_TYPE MATCHES Debug)

# CCache

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
  set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_PROGRAM}")
endif()

# Dependencies

find_package(OpenMP REQUIRED)

include(FetchContent)

FetchContent_Declare(json
  URL https://github.com/nlohmann/json/releases/download/v3.12.0/json.tar.xz)
FetchContent_MakeAvailable(json)

set(HTTPLIB_REQUIRE_ZSTD OFF CACHE BOOL "" FORCE)
set(HTTPLIB_USE_ZSTD_IF_AVAILABLE OFF CACHE BOOL "" FORCE)
FetchContent_Declare(httplib
  GIT_REPOSITORY https://github.com/yhirose/cpp-httplib
  GIT_TAG v0.26.0
)
FetchContent_MakeAvailable(httplib)

FetchContent_Declare(
  backward
  GIT_REPOSITORY https://github.com/bombela/backward-cpp
  GIT_TAG master
)
FetchContent_MakeAvailable(backward)

FetchContent_Declare(
  argparse
  GIT_REPOSITORY https://github.com/p-ranav/argparse.git
  GIT_TAG v3.2
)
FetchContent_MakeAvailable(argparse)

FetchContent_Declare(
  indicators
  GIT_REPOSITORY https://github.com/p-ranav/indicators.git
  GIT_TAG v2.3
)
FetchContent_MakeAvailable(indicators)

set(GLFW_BUILD_DOCS OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(GLFW_INSTALL OFF CACHE BOOL "" FORCE)
FetchContent_Declare(glfw GIT_REPOSITORY https://github.com/glfw/glfw.git GIT_TAG 3.4)
FetchContent_MakeAvailable(glfw)

FetchContent_Declare(
  imgui
  GIT_REPOSITORY https://github.com/ocornut/imgui.git
  GIT_TAG v1.92.2b
)
FetchContent_GetProperties(imgui)
if (NOT imgui_POPULATED)
  FetchContent_Populate(imgui)
  set(IMGUI_INCLUDE_DIR ${imgui_SOURCE_DIR}/)
  file(GLOB IMGUI_SOURCES ${imgui_SOURCE_DIR}/*.cpp)
  file(GLOB IMGUI_HEADERS ${imgui_SOURCE_DIR}/*.h)
  add_library(imgui STATIC ${IMGUI_SOURCES} ${imgui_SOURCE_DIR}/backends/imgui_impl_glfw.cpp ${imgui_SOURCE_DIR}/backends/imgui_impl_opengl3.cpp)
  target_include_directories(imgui PUBLIC ${imgui_SOURCE_DIR}/backends ${IMGUI_INCLUDE_DIR} ${OPENGL_INCLUDE_DIR} ${GLFW_INCLUDE_DIR} ${GLAD_INCLUDE_DIR})
  target_link_libraries(imgui ${OPENGL_LIBRARIES} glfw)
endif ()

# Common
add_library(common
  src/header.cpp
  src/api.cpp
)
target_include_directories(common PUBLIC
  src)
target_link_libraries(common PUBLIC
  OpenMP::OpenMP_CXX
  Backward::Interface
  argparse::argparse
  indicators::indicators
  nlohmann_json::nlohmann_json
  httplib::httplib
  cadical
)
target_precompile_headers(common PRIVATE src/header.hpp)

# Main
add_executable(main
  src/main.cpp
)
target_link_libraries(main PUBLIC common)
target_precompile_headers(main REUSE_FROM common)

# Vis
add_executable(vis
  src/vis.cpp
)
target_link_libraries(vis PUBLIC common imgui)
target_precompile_headers(vis REUSE_FROM common)
