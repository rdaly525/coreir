.SUFFIXES:

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
LIBS =  -Wl,-rpath,$(HOME)/lib -lcoreir -ldl -lcoreir-commonlib
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

ifdef COREIR_INCLUDE_PYTHON_TYPEGEN
	PYTHON_CONFIG ?= python-config
	PYTHONHOME = $(shell $(PYTHON_CONFIG) --prefix)
	PYTHON_LIBS = $(PYTHONHOME)/lib
	PYLDFLAGS = -L $(PYTHON_LIBS) $(shell $(PYTHON_CONFIG) --libs)
endif

all: $(EXES)

clean:
	rm -rf build/*

build/%: build/%.o 
	$(CXX) $(LDFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) $(PYLDFLAGS)
	cp $@ $(HOME)/bin

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
