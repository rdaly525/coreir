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

HOME = ../../..
LPATH = -L$(HOME)/lib
INCS = -I$(HOME)/include -I.
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

DYLIBS = $(patsubst %.cpp,build/%.dylib,$(SRCFILES))
SOLIBS = $(patsubst %.cpp,build/%.so,$(SRCFILES))

all: $(DYLIBS) $(SOLIBS)

so: $(SOLIBS)

dylib: $(DYLIBS)

clean:
	rm -rf build/*

build/%.so: build/%.o
	$(CXX) -shared $(LPATH) -o $@ $^ -lcoreir 
	cp $@ $(HOME)/lib/libcoreir-$*.so

build/%.dylib: build/%.o
	$(CXX) -install_name "@rpath/libcoreir-$*.dylib" -dynamiclib $(LPATH) -lcoreir -o $@ $^
	cp $@ $(HOME)/lib/libcoreir-$*.dylib

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
