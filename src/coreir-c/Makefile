HOME = ../..
LPATH = -L$(HOME)/lib
INCS = -I$(HOME)/include -I.
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

CSRC = coreir-c.cpp types-c.cpp values-c.cpp
CSIMSRC = simulator-c.cpp
COBJS = $(patsubst %.cpp,build/%.o,$(CSRC))
CSIMOBJS = $(patsubst %.cpp,build/%.o,$(CSIMSRC))

DYLIBS = build/coreir-c.dylib build/coreirsim-c.dylib
SOLIBS = build/coreir-c.so build/coreirsim-c.so

all: $(DYLIBS) $(SOLIBS)

so: $(SOLIBS)

dylib: $(DYLIBS)

clean:
	rm -rf build/*

build/coreir-c.so: $(COBJS)
	$(CXX) -shared $(LPATH) -o $@ $^ -lcoreir
	cp $@ $(HOME)/lib/libcoreir-c.so

build/coreir-c.dylib: $(COBJS)
	$(CXX) -install_name "@rpath/libcoreir-c.dylib" -dynamiclib $(LPATH) -lcoreir -o $@ $^
	cp $@ $(HOME)/lib/libcoreir-c.dylib

build/coreirsim-c.so: $(CSIMOBJS)
	$(CXX) -shared $(LPATH) -o $@ $^ -lcoreirsim
	cp $@ $(HOME)/lib/libcoreirsim-c.so

build/coreirsim-c.dylib: $(CSIMOBJS)
	$(CXX) -install_name "@rpath/libcoreirsim-c.dylib" -dynamiclib $(LPATH) -lcoreirsim -o $@ $^
	cp $@ $(HOME)/lib/libcoreirsim-c.dylib

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
