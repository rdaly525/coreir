.SUFFIXES:

HOME = ../..
FUNCPATH = ${FUNCUBUF_PATH}
INCS = -I$(HOME)/include -I. -I$(FUNCPATH)/include
LPATH = -L$(HOME)/lib -L$(FUNCPATH)/bin
LIBS =  -Wl,-rpath,$(HOME)/lib -lfuncubuf -lcoreir -lcoreirsim -lcoreir-commonlib -lcoreir-aetherlinglib -lcoreir-float
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

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
