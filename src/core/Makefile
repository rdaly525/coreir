CC = clang++
CFLAGS = -std=c++11 -Wall -ferror-limit=5 -g

DEPS = magmair.hpp types.hpp typeCache.hpp toNode.hpp
OBJS = magmair.o types.o typeCache.o toNode.o

all: magmair.a

run: addtree.run

clean:
	rm *.o *.a *.run

magmair.a: magmair.o $(OBJS)
	ar rcs $@ $^

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

%.run: %.o $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^



