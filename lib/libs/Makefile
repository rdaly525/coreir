.SUFFIXES:


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

BIN = ../../bin
LPATH = -L$(BIN)
INCS = -I../../include -I.
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

DYLIBS = build/stdlib.dylib
SOLIBS = build/stdlib.so

all: $(DYLIBS) $(SOLIBS)

so: $(SOLIBS)

dylib: $(DYLIBS)

clean:
	rm -rf build/*

build/%.so: build/%.o
	$(CXX) -shared -lcoreir -o $@ $^
	cp $@ $(BIN)/lib$*.so

build/%.dylib: build/%.o
	$(CXX) -install_name "@loader_path/lib$*.dylib" -dynamiclib $(LPATH) -lcoreir -o $@ $^
	cp $@ $(BIN)/lib$*.dylib

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
