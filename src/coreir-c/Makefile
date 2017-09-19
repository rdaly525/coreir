HOME = ../..
LPATH = -L$(HOME)/lib
INCS = -I$(HOME)/include -I.
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

DYLIBS = build/coreir-c.dylib
SOLIBS = build/coreir-c.so

all: $(DYLIBS) $(SOLIBS)

so: $(SOLIBS)

dylib: $(DYLIBS)

clean:
	rm -rf build/*

build/%.so: $(OBJS)
	$(CXX) -shared $(LPATH) -o $@ $^ -lcoreir
	cp $@ $(HOME)/lib/lib$*.so

build/%.dylib: $(OBJS)
	$(CXX) -install_name "@rpath/lib$*.dylib" -dynamiclib $(LPATH) -lcoreir -o $@ $^
	cp $@ $(HOME)/lib/lib$*.dylib

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
