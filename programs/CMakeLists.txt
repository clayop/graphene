add_subdirectory( cli_wallet )
add_subdirectory( witness_node )
add_subdirectory( js_operation_serializer )
add_subdirectory( size_checker )


set(BUILD_QT_GUI FALSE CACHE BOOL "Build the Qt-based light client GUI")
if(BUILD_QT_GUI)
   add_subdirectory(light_client)
endif()
