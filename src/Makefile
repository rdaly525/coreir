.SUFFIXES:

CC = g++
CFLAGS = -std=c++11  -Wall  -fPIC

INCS = -I../libs -I.
DEPS = common.hpp types.hpp typecache.hpp context.hpp 
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,../build/%.o,$(SRCFILES))
BUILD = build

all: ../build/coreir.a $(OBJS)

clean:
	rm -rf ../build/*

../build/coreir.a: $(OBJS)
	ar rcs $@ $^

../build/coreir.so: $(OBJS)
	$(CC) -shared -o $@ $^

coreir.dylib: $(OBJS)
	$(CC) -dynamiclib -o $@ $^

../build/%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<
