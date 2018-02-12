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
	$(CXX) -shared $(LPATH) $(LDFLAGS) -o $@ $^ -lcoreir 
	cp $@ $(HOME)/lib/libcoreir-$*.so

build/%.dylib: build/%.o
	$(CXX) -install_name "@rpath/libcoreir-$*.dylib" -dynamiclib $(LPATH) $(LDFLAGS) -lcoreir -o $@ $^
	cp $@ $(HOME)/lib/libcoreir-$*.dylib

build/%.o: %.cpp $(DEPS) aetherlinglib/*.h
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
