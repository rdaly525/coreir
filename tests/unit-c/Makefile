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
CFLAGS = -Wall -fPIC

ifdef COREDEBUG
CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG 
endif

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
#TODO Hacky to include coreir lib. Maybe I should generate coreir-c statically including all of coreir
LIBS = -Wl,-rpath,$(HOME)/lib -lcoreir-stdlib -lcoreir-c -lcoreir
SRCFILES = $(wildcard *.c)
OBJS = $(patsubst %.c,build/%.o,$(SRCFILES))
EXES = $(patsubst %.c,build/%,$(SRCFILES))

all: $(EXES)

clean:
	rm -rf build/*
	rm -f _*.json

build/%: build/%.o 
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) 

build/%.o: %.c
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $<
