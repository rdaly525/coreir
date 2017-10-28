.SUFFIXES:

LIBS = -lcoreir
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
	rm -f _*.json

build/%: build/%.o 
	$(CXX) $(CXXFLAGS) -o $@ $< $(LIBS) $(PYLDFLAGS)

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c -o $@ $<
