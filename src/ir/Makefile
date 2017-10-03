HOME = ../..
INCS = -I$(HOME)/include -I. -I /Users/lenny/miniconda3/include/python3.6m
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES)) $(wildcard ../passes/analysis/build/*.o) $(wildcard ../passes/transform/build/*.o) $(wildcard ../simulator/build/*.o)

DYLIBS = build/coreir.dylib
SOLIBS = build/coreir.so

all: $(DYLIBS) $(SOLIBS)

so: $(SOLIBS)

dylib: $(DYLIBS)

clean:
	rm -rf build/*

build/%.so: $(OBJS)
	$(CXX) -shared -o $@ $^
	cp $@ $(HOME)/lib/lib$*.so

build/%.dylib: $(OBJS)
	$(CXX) -install_name "@rpath/lib$*.dylib" -dynamiclib -o $@ $^ -lpython -L /Users/lenny/miniconda3/lib
	cp $@ $(HOME)/lib/lib$*.dylib

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
