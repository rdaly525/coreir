.SUFFIXES:

CC = clang++
CFLAGS = -std=c++11 -Wall -ferror-limit=5 -fPIC

INCS = -I../src -I../libs
DEPS = common.hpp types.hpp typecache.hpp context.hpp 
OBJS = fileIO.o rungen.o typecheck.o namespace.o instantiable.o context.o types.o genargs.o typecache.o common.o


#all: context.a coreir.a
all: coreir.a

run: addtree.run

clean:
	-@rm *.o *.a *.run *.so *.dylib

context.a: $(OBJS)
	ar rcs $@ $^

coreir.a: coreir.o $(OBJS)
	ar rcs $@ $^

coreir.so: coreir.o $(OBJS)
	$(CC) -shared -o $@ $^

coreir.dylib: coreir.o $(OBJS)
	$(CC) -dynamiclib -o $@ $^

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<

%.run: %.o $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^

fuck:
	echo $(CFLAGS)
	echo $(CXX)

