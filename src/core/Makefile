CC = clang++
CFLAGS = -std=c++11 -Wall -ferror-limit=5 -g

DEPS = coreir.hpp types.hpp typeCache.hpp
OBJS = coreir.o typeconstructors.o types.o typeCache.o 

all: coreir.a

run: addtree.run

clean:
	-@rm *.o *.a *.run

coreir.a: $(OBJS)
	ar rcs $@ $^


#typeconstructors.o: typeconstructors.cpp
#	$(CC) $(CFLAGS) -c $<

coreir.o: coreir.cpp
	$(CC) $(CFLAGS) -c -o $@ $<

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

%.run: %.o $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^

fuck:
	echo $(CFLAGS)
	echo $(CXX)

