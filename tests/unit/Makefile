CORECONFIG ?= g++

ifeq ($(CORECONFIG),g++)
CXX = g++
endif

ifeq ($(CORECONFIG),g++-4.9)
CXX = g++-4.9
endif



CFLAGS = -std=c++11 -Wall
DEPS = 

SRCDIR = ../../src
LIBSDIR = ../../libs

INCS = -I$(SRCDIR) -I$(LIBSDIR)
LIBS = -L$(SRCDIR) -L$(LIBSDIR)

SRCFILES = $(wildcard [^_]*.cpp)
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

.SUFFIXES:


all: $(EXES)

#all: 
#	make -C $(SRCDIR)
#	make cpptest.run
#	make ctest.run
#	make add4.run
#	make jsontest.run
#	make gentest.run
#	make typetest.run

clean:
	rm -rf build/*

build/%: %.cpp ../../build/coreir.a
	make -C $(SRCDIR)
	$(CXX) $(CFLAGS) $(INCS)  -o $@ $< ../../build/coreir.a



#.PHONY: $(SRCDIR)/coreir.a

