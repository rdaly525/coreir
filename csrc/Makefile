CC = clang++-3.5
CFLAGS = -std=c++11 -ferror-limit=5

DEPS = magmair.hpp types.hpp typeCache.hpp
OBJ = main.o magmair.o types.o typeCache.o

all: main

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

main: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^
	
clean:
	-rm *.o main
