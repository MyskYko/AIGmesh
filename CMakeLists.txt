cmake_minimum_required(VERSION 3.8)
project(mesh CXX)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
add_compile_options(-g -O3)

add_subdirectory(glucose)

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

file(GLOB FILENAMES ${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp)
add_executable(mesh ${FILENAMES})
target_link_libraries(mesh glucose)
target_include_directories(mesh PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/glucose)
