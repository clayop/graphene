cmake_minimum_required(VERSION 2.8.11)

project(light_client)

# Find includes in corresponding build directories
set(CMAKE_INCLUDE_CURRENT_DIR ON)
# Instruct CMake to run moc automatically when needed.
set(CMAKE_AUTOMOC ON)

find_package(Qt5Core)
find_package(Qt5Widgets)
find_package(Qt5Quick)

file(GLOB QML qml/*)

qt5_add_resources(QML_QRC qml/qml.qrc)

add_executable(light_client ClientDataModel.cpp ClientDataModel.hpp main.cpp ${QML_QRC} ${QML})
add_dependencies(light_client gen_qrc)

target_link_libraries(light_client PRIVATE Qt5::Core Qt5::Widgets Qt5::Quick graphene_chain graphene_utilities fc graphene_app )