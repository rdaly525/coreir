.SUFFIXES:

CXX = g++
#CXX = clang++
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
	$(CXX) -shared -o $@ $^

coreir.dylib: $(OBJS)
	$(CXX) -dynamiclib -o $@ $^

../build/%.o: %.cpp $(DEPS)
	$(CXX) $(CFLAGS) $(INCS) -c -o $@ $<
