cmake_minimum_required(VERSION 3.8)
project(bdd CXX C)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
add_compile_options(-g -O3)

add_subdirectory(glucose)

file(GLOB FILENAMES *.cpp)
add_executable(mesh ${FILENAMES})
target_link_libraries(mesh glucose)
target_include_directories(mesh PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/glucose)
