CC = g++
CFLAGS = -std=c++11 -Wall
DEPS = 

SRCDIR = ../../src
LIBSDIR = ../../libs

INCS = -I$(SRCDIR) -I$(LIBSDIR)
LIBS = -L$(SRCDIR) -L$(LIBSDIR)

SRCFILES = $(wildcard *.cpp)
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

.SUFFIXES:

all: $(EXES)


clean:
	rm -rf build/*

build/%: %.cpp ../../build/coreir.a
	make -C $(SRCDIR)
	$(CC) $(CFLAGS) $(INCS)  -o $@ $< ../../build/coreir.a


