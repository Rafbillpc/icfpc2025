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

# Common
add_library(common
  src/header.cpp
  src/api.cpp
)
target_link_directories(common PUBLIC
  kissat)
target_include_directories(common PUBLIC
  src kissat)
target_link_libraries(common PUBLIC
  nlohmann_json::nlohmann_json
  httplib::httplib
  kissat
)
target_precompile_headers(common PRIVATE src/header.hpp)

# Main
add_executable(main
  src/main.cpp
)
target_link_libraries(main PUBLIC common)
target_precompile_headers(main REUSE_FROM common)
