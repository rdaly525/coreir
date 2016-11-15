CC = clang++-3.5
CFLAGS = -std=c++11 -ferror-limit=5 -g

DEPS = magmair.hpp types.hpp typeCache.hpp
OBJ = magmair.o types.o typeCache.o

.PHONY: clean all

all: addtree.run

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

%.run: %.o $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^


clean:
	-rm *.o
