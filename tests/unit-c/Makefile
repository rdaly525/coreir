.SUFFIXES:

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
#TODO Hacky to include coreir lib. Maybe I should generate coreir-c statically including all of coreir
LIBS = -Wl,-rpath,$(HOME)/lib -lcoreir-c -lcoreir
SRCFILES = $(wildcard [^_]*.c)
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
