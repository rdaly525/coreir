.SUFFIXES:

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
#TODO commonlib should not be a dependency here
CLIBS =  -Wl,-rpath,$(HOME)/lib -lcoreir -ldl 
CSIMLIBS =  -Wl,-rpath,$(HOME)/lib -lcoreir -lcoreirsim -lcoreir-commonlib
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

all: $(EXES)

clean:
	rm -rf build/*

build/coreir: build/coreir.o 
	$(CXX) $(LDFLAGS) $(INCS) -o $@ $< $(LPATH) $(CLIBS) 
	cp $@ $(HOME)/bin

build/simulator: build/simulator.o 
	$(CXX) $(LDFLAGS) $(INCS) -o $@ $< $(LPATH) $(CSIMLIBS) 
	cp $@ $(HOME)/bin

build/interpreter: build/interpreter.o 
	$(CXX) $(LDFLAGS) $(INCS) -o $@ $< $(LPATH) $(CSIMLIBS) 
	cp $@ $(HOME)/bin

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
