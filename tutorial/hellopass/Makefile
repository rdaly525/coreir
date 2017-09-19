HOME = ../..
LPATH = -L$(HOME)/lib
INCS = -I$(HOME)/include -I.
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

DYLIBS = $(patsubst %.cpp,build/%.dylib,$(SRCFILES))
SOLIBS = $(patsubst %.cpp,build/%.so,$(SRCFILES))

all: $(DYLIBS) $(SOLIBS)

so: $(SOLIBS)

dylib: $(DYLIBS)

clean:
	rm -rf build/*

build/%.so: build/%.o
	$(CXX) -shared $(LPATH) -o $@ $^ -lcoreir 
	cp $@ $(HOME)/lib/$*.so

build/%.dylib: build/%.o
	$(CXX) -install_name "@rpath/$*.dylib" -dynamiclib $(LPATH) -lcoreir -o $@ $^
	cp $@ $(HOME)/lib/$*.dylib

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
