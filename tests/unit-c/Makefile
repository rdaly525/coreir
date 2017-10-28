.SUFFIXES:

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
#TODO Hacky to include coreir lib. Maybe I should generate coreir-c statically including all of coreir
LIBS = -Wl,-rpath,$(HOME)/lib -lcoreir-c -lcoreir
SRCFILES = $(wildcard [^_]*.c)
OBJS = $(patsubst %.c,build/%.o,$(SRCFILES))
EXES = $(patsubst %.c,build/%,$(SRCFILES))

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
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) $(PYLDFLAGS)

build/%.o: %.c
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<
