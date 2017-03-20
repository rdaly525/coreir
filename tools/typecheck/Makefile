SRCDIR = ../../src
LIBSDIR = ../../libs

INCS = -I$(SRCDIR) -I$(LIBSDIR)
LIBS = -L$(SRCDIR) -L$(LIBSDIR)

CXX ?= g++
CXXFLAGS = -std=c++11  -Wall  -fPIC 

all: ../build/typecheck

../build/typecheck: typecheck.cpp
	make -C ../../src
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $< ../../build/coreir.a