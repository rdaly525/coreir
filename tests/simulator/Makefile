.SUFFIXES:
#COREIRCONFIG ?= g++
#CXX ?= g++
#
#ifeq ($(COREIRCONFIG),g++)
#CXX = g++
#endif
#
#ifeq ($(COREIRCONFIG),g++-4.9)
#CXX = g++-4.9
#endif
#
#CXXFLAGS = -std=c++11  -Wall  -fPIC -Werror
#
#ifdef COREDEBUG
#CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG 
#endif


HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
LIBS =  -Wl,-rpath,$(HOME)/lib -lcoreir -lcoreir-commonlib
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

ifdef COREIR_INCLUDE_PYTHON_TYPEGEN
	PYTHON_CONFIG ?= python-config
	PYTHONHOME = $(shell $(PYTHON_CONFIG) --prefix)
	PYTHON_LIBS = $(PYTHONHOME)/lib
	PYLDFLAGS = -L $(PYTHON_LIBS) $(shell $(PYTHON_CONFIG) --libs)
endif

#all: $(EXES)

all: build/simtests

build/simtests: $(OBJS)
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) $(PYLDFLAGS)

clean:
	rm -rf build/*
	rm -f _*.json

build/simtests: $(OBJS) #build/%.o 
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $(OBJS) $(LPATH) $(LIBS) $(PYLDFLAGS)

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $< $(PYLDFLAGS)
