set(SRCS
	interpret.cpp
	op_graph.cpp
	output.cpp
	print_c.cpp
	sim.cpp
	utils.cpp
	wire_node.cpp
)

add_library(simulator ${SRCS})

