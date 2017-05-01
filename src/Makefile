COREIRCONFIG ?= g++
CXX ?= g++

ifeq ($(COREIRCONFIG),g++)
CXX = g++
endif

ifeq ($(COREIRCONFIG),g++-4.9)
CXX = g++-4.9
endif

CXXFLAGS = -std=c++11  -Wall  -fPIC 

ifdef COREDEBUG
CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG
endif


BIN = ../bin
INCS = -I../include -I.
DEPS = context.hpp
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

all: build/coreir.dylib build/coreir.so

clean:
	rm -rf build/*

build/%.so: $(OBJS)
	$(CXX) -shared -o $@ $^
	cp $@ $(BIN)/lib$*.so

build/%.dylib: $(OBJS)
	$(CXX) -install_name "@rpath/lib$*.dylib" -dynamiclib -o $@ $^
	cp $@ $(BIN)/lib$*.dylib

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
