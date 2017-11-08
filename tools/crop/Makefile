.SUFFIXES:

CXX ?= g++
CXXFLAGS = -std=c++11 -Wall -fPIC -Werror

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
LIBS =  -Wl,-rpath,$(HOME)/lib -lcoreir -ldl -lcoreir-commonlib
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

all: $(EXES)

clean:
	rm -rf build/*

build/%: build/%.o 
	$(CXX) $(LDFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) 
	cp $@ $(HOME)/bin

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
