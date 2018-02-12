CXX ?= g++
CXXFLAGS = -std=c++11 -Wall -fPIC -Werror

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
LIBS =  -Wl,-rpath,$(HOME)/lib -lcoreir
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

all: $(EXES)

clean:
	rm -rf build/*
	rm -f _*.json

build/%: build/%.o 
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) 

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
