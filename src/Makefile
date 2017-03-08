.SUFFIXES:

CC = clang++
CFLAGS = -std=c++11 -Wall -ferror-limit=5

CDIR = /Users/rdaly/coreir
INCS = -I$(CDIR)/src -I$(CDIR)/libs
DEPS = common.hpp types.hpp typecache.hpp context.hpp 
OBJS = fileIO.o rungen.o typecheck.o namespace.o instantiable.o context.o types.o genargs.o typecache.o common.o


#all: context.a coreir.a
all: coreir.a

run: addtree.run

clean:
	-@rm *.o *.a *.run

context.a: $(OBJS)
	ar rcs $@ $^

coreir.a: coreir.o $(OBJS)
	ar rcs $@ $^

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<

%.run: %.o $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^

fuck:
	echo $(CFLAGS)
	echo $(CXX)

