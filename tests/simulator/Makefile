.SUFFIXES:

HOME = ../..
INCS = -I$(HOME)/include -I.
LPATH = -L$(HOME)/lib
LIBS =  -Wl,-rpath,$(HOME)/lib -lverilogAST -lcoreir -lcoreirsim -lcoreir-commonlib -lcoreir-aetherlinglib -lcoreir-float
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))
CXXFLAGS += -Wno-unused-variable

#all: $(EXES)

all: build/simtests

build/simtests: $(OBJS)
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $< $(LPATH) $(LIBS) 

clean:
	rm -rf build/*
	rm -f _*.json

build/simtests: $(OBJS)
	$(CXX) $(CXXFLAGS) $(INCS) -o $@ $(OBJS) $(LPATH) $(LIBS) 

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
