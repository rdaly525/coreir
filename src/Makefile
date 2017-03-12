.SUFFIXES:


CORECONFIG ?= g++

ifeq ($(CORECONFIG),g++)
CXX = g++
endif

ifeq ($(CORECONFIG),g++-4.9)
CXX = g++-4.9
endif

CXXFLAGS = -std=c++11  -Wall  -fPIC 

ifdef COREDEBUG
CXXFLAGS += -g -D_GLIBCXX_DEBUG
endif

INCS = -I../libs -I.
DEPS = common.hpp types.hpp typecache.hpp context.hpp instantiable.hpp 
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,../build/%.o,$(SRCFILES))

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
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
