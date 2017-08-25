.SUFFIXES:
COREIRCONFIG ?= g++
CXX ?= g++

ifeq ($(COREIRCONFIG),g++)
CXX = g++
endif

ifeq ($(COREIRCONFIG),g++-4.9)
CXX = g++-4.9
endif

CXXFLAGS = -std=c++11  -Wall  -fPIC -Werror

ifdef COREDEBUG
CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG 
endif


HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
LIBS =  -Wl,-rpath,$(HOME)/lib -lcoreir
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = build/reductiontree

DYLIBS = build/treereductionpass.dylib
SOLIBS = build/treereductionpass.so

all: $(EXES) $(SOLIBS)
so: $(SOLIBS)
dylib: $(DYLIBS)

clean:
	rm -rf build/*
	rm -f _*.json

build/%: build/%.o 
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) 

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<


build/%.so: build/%.o
	$(CXX) -shared $(LPATH) -o $@ $^ -lcoreir 
	cp $@ $(HOME)/lib/$*.so

build/%.dylib: build/%.o
	$(CXX) -install_name "@rpath/$*.dylib" -dynamiclib $(LPATH) -lcoreir -o $@ $^
	cp $@ $(HOME)/lib/$*.dylib

.PHONY: graph graph.png
graph graph.png:
	dot -Tpng design.txt > graph.png
