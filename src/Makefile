.SUFFIXES:

CORECONFIG ?= g++
CXX ?= g++

ifeq ($(CORECONFIG),g++)
CXX = g++
endif

ifeq ($(CORECONFIG),g++-4.9)
CXX = g++-4.9
endif

CXXFLAGS = -std=c++11  -Wall  -fPIC 

ifdef COREDEBUG
CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG
endif

INCS = -I../libs -I.
DEPS = common.hpp types.hpp typecache.hpp context.hpp instantiable.hpp 
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,../build/%.o,$(SRCFILES))
LIBFILES = $(wildcard ../libs/*.cpp)
LIBOBJS = $(patsubst ../libs/%.cpp,../build/%.o,$(LIBFILES))

all: ../build/coreir.a $(OBJS) $(LIBOBJS)
echo:
	echo $(CXX)

clean:
	rm -rf ../build/*

../build/coreir.a: $(OBJS) $(LIBOBJS)
	ar rcs $@ $^

../build/coreir.so: $(OBJS) $(LIBOBJS)
	$(CXX) -shared -o $@ $^

../build/coreir.dylib: $(OBJS) $(LIBOBJS)
	$(CXX) -dynamiclib -o $@ $^

../build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<

../build/%.o: ../libs/%.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
