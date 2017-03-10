.SUFFIXES:

CORECONFIG ?= g++

ifeq ($(CORECONFIG),g++)
CXX = g++
endif

ifeq ($(CORECONFIG),g++-4.9)
CXX = g++-4.9
endif

#CXX = clang++
CFLAGS = -std=c++11  -Wall  -fPIC

INCS = -I../libs -I.
DEPS = common.hpp types.hpp typecache.hpp context.hpp 
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,../build/%.o,$(SRCFILES))
BUILD = build

all: ../build/coreir.a $(OBJS)

echo:
	echo $(CXX)

clean:
	rm -rf ../build/*

../build/coreir.a: $(OBJS)
	ar rcs $@ $^

../build/coreir.so: $(OBJS)
	$(CXX) -shared -o $@ $^

../build/coreir.dylib: $(OBJS)
	$(CXX) -dynamiclib -o $@ $^

../build/%.o: %.cpp $(DEPS)
	$(CXX) $(CFLAGS) $(INCS) -c -o $@ $<
