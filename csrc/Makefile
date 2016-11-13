CC = clang++-3.5
CFLAGS = -std=c++11 

DEPS = types.hpp
OBJ = test.o types.o

all: main

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

main: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^
	
clean:
	-rm *.o main
