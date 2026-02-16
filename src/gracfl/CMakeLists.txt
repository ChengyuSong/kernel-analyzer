cmake_minimum_required(VERSION 3.26)
project(GraCFL)

set(LIB_NAME graCFLlib)

# Toggle to compare memory/behavior against the original std::unordered_set-based
# reachability representation.
option(GRACFL_USE_STD_UNORDERED_SET "Use std::unordered_set for reachability sets" OFF)

# C++ Standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED True)

# Default to Release build
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3")

# Source and include directories
set(SRC_DIR "${CMAKE_CURRENT_SOURCE_DIR}/src")
set(INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/include")
include_directories(${INCLUDE_DIR})
set(VENDORED_BOOST_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/..") # provides boost/* under src/boost

# Find OpenMP
find_package(OpenMP)

# External project support
include(ExternalProject)

# External jemalloc setup
find_library(JEMALLOC_LIB jemalloc)

if(NOT JEMALLOC_LIB)
    message(STATUS "jemalloc not found, downloading and building it...")

    ExternalProject_Add(
        jemalloc
        GIT_REPOSITORY https://github.com/jemalloc/jemalloc.git
        GIT_TAG 5.3.0
        CONFIGURE_COMMAND ./autogen.sh --prefix=${CMAKE_BINARY_DIR}/jemalloc_install --libdir=${CMAKE_BINARY_DIR}/jemalloc_install/lib --with-private-libpthread
        BUILD_COMMAND make
        INSTALL_COMMAND make install
        BUILD_IN_SOURCE 1
        PREFIX ${CMAKE_BINARY_DIR}/_deps/jemalloc
    )

    # Include jemalloc after install
    include_directories("${CMAKE_BINARY_DIR}/jemalloc_install/include")
    set(JEMALLOC_LIB "${CMAKE_BINARY_DIR}/jemalloc_install/lib/libjemalloc.a")
    set(JEMALLOC_LIBS ${JEMALLOC_LIB} pthread dl)

    # Dummy CMake target that depends on ExternalProject
    add_custom_target(libjemalloc)
    add_dependencies(libjemalloc jemalloc)
else()
    set(JEMALLOC_LIBS ${JEMALLOC_LIB})
endif()

# External TBB setup
find_package(TBB)

if(NOT TBB_FOUND)
    message(STATUS "TBB not found, downloading and building it...")

    ExternalProject_Add(
        tbb
        GIT_REPOSITORY https://github.com/oneapi-src/oneTBB.git
        GIT_TAG v2021.13.0
        CMAKE_ARGS -DCMAKE_INSTALL_PREFIX=${CMAKE_BINARY_DIR}/tbb_install -DCMAKE_INSTALL_LIBDIR=lib -DTBB_TEST=OFF
        BUILD_COMMAND ${CMAKE_COMMAND} --build . --target install
        INSTALL_COMMAND ""
        BUILD_IN_SOURCE 1
        PREFIX ${CMAKE_BINARY_DIR}/_deps/tbb
    )

    set(TBB_INCLUDE_DIRS "${CMAKE_BINARY_DIR}/tbb_install/include")
    set(TBB_LIB "${CMAKE_BINARY_DIR}/tbb_install/lib/libtbb${CMAKE_SHARED_LIBRARY_SUFFIX}")
    set(TBB_MALLOC_LIB "${CMAKE_BINARY_DIR}/tbb_install/lib/libtbbmalloc${CMAKE_SHARED_LIBRARY_SUFFIX}")
    set(TBB_MALLOC_PROXY_LIB "${CMAKE_BINARY_DIR}/tbb_install/lib/libtbbmalloc_proxy${CMAKE_SHARED_LIBRARY_SUFFIX}")

    include_directories(${TBB_INCLUDE_DIRS})
    set(TBB_LIBS ${TBB_LIB} ${TBB_MALLOC_LIB} ${TBB_MALLOC_PROXY_LIB})

    add_custom_target(libTBB)
    add_dependencies(libTBB tbb)
else()
    set(TBB_LIBS TBB::tbb TBB::tbbmalloc TBB::tbbmalloc_proxy)
endif()

# Collect source files
file(GLOB_RECURSE ALL_SOURCES "${SRC_DIR}/*.cpp")

set(LIB_SOURCES "")

foreach(source_file IN LISTS ALL_SOURCES)
    list(APPEND LIB_SOURCES ${source_file})
endforeach()

# Build the static library
add_library(${LIB_NAME} STATIC ${LIB_SOURCES})
target_include_directories(${LIB_NAME} PUBLIC ${INCLUDE_DIR})
target_include_directories(${LIB_NAME} PUBLIC ${VENDORED_BOOST_ROOT})

if(GRACFL_USE_STD_UNORDERED_SET)
    target_compile_definitions(${LIB_NAME} PUBLIC GRACFL_USE_STD_UNORDERED_SET=1)
endif()

# Add dependencies on external builds
if(TARGET libjemalloc)
    add_dependencies(${LIB_NAME} libjemalloc)
endif()

if(TARGET libTBB)
    add_dependencies(${LIB_NAME} libTBB)
endif()

# message(STATUS "→ graCFLlib will compile these sources:\n   ${LIB_SOURCES}")

# Link dependencies to the library (PUBLIC so they propagate to consumers)
target_link_libraries(${LIB_NAME} PUBLIC ${JEMALLOC_LIBS})
target_link_libraries(${LIB_NAME} PUBLIC ${TBB_LIBS})

if(OpenMP_CXX_FOUND)
    target_link_libraries(${LIB_NAME} PUBLIC OpenMP::OpenMP_CXX)
endif()

# Build the executable (disabled - using as library only)
# add_executable(${EXE_NAME} ${MAIN_SOURCE})
# target_link_libraries(${EXE_NAME} PRIVATE ${LIB_NAME})

# Ensure executable also depends on jemalloc/TBB builds
# if(TARGET libjemalloc)
#     add_dependencies(${EXE_NAME} libjemalloc)
# endif()

# if(TARGET libTBB)
#     add_dependencies(${EXE_NAME} libTBB)
# endif()
