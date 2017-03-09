.SUFFIXES:

CC = clang++
CFLAGS = -std=c++11 -Wall -ferror-limit=5 -fPIC

INCS = -I../libs -I.
DEPS = common.hpp types.hpp typecache.hpp context.hpp 
#OBJS = fileIO.o rungen.o typecheck.o namespace.o instantiable.o context.o types.o genargs.o typecache.o common.o
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,../build/%.o,$(SRCFILES))
BUILD = build

all: coreir.a $(OBJS)

clean:
	-@rm *.o *.a *.run *.so *.dylib

coreir.a: $(OBJS)
	ar rcs $@ $^

coreir.so: $(OBJS)
	$(CC) -shared -o $@ $^

coreir.dylib: $(OBJS)
	$(CC) -dynamiclib -o $@ $^

../build/%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<
