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
CFLAGS = -Wall -fPIC

ifdef COREDEBUG
CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG 
endif

BIN = ../../bin
INCS = -I../../include -I.
LPATH = -L$(BIN)
LIBS = -lcoreir-c
SRCFILES = $(wildcard *.c)
OBJS = $(patsubst %.c,build/%.o,$(SRCFILES))
EXES = $(patsubst %.c,build/%,$(SRCFILES))


all: $(EXES)

coreir:
	echo $(SRCFILES)
	echo $(EXES)
	make -C ../../src

clean:
	rm -rf build/*
	rm -f _*.json

build/%: build/%.o 
	$(CXX) $(CXXFLAGS) $(INCS) $(LPATH) $(LIBS) -o $@ $< 

build/%.o: %.c
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<

