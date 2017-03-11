CORECONFIG ?= g++

ifeq ($(CORECONFIG),g++)
CXX = g++
CC = gcc
endif

ifeq ($(CORECONFIG),g++-4.9)
CXX = g++-4.9
CC = gcc-4.9
endif



CXXFLAGS = -std=c++11  -Wall  -fPIC
CFLAGS = -Wall -fPIC
DEPS = 

SRCDIR = ../../src
LIBSDIR = ../../libs

INCS = -I$(SRCDIR) -I$(LIBSDIR)
LIBS = -L$(SRCDIR) -L$(LIBSDIR)

SRCFILES = $(wildcard [^_]*.c*)
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))
EXES = $(patsubst %.c,build/%,$(SRCFILES))

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

build/%: build/%.o ../../build/coreir.a
	make -C $(SRCDIR)
	$(CXX) $(CXXFLAGS) $(INCS)  -o $@ $< ../../build/coreir.a

build/%.o: %.cpp
	make -C $(SRCDIR)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<

build/%.o: %.c
	make -C $(SRCDIR)
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<

#.PHONY: $(SRCDIR)/coreir.a

