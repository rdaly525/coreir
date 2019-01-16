HOME = ../..
INCS = -I$(HOME)/include -I.
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

LIBS = -ldl -lcoreir

DYLIBS = build/coreirsim.dylib
SOLIBS = build/coreirsim.so

all: $(DYLIBS) $(SOLIBS)

so: $(SOLIBS)

dylib: $(DYLIBS)

clean:
	rm -rf build/*

build/%.so: $(OBJS)
	$(CXX) -shared -o $@ $^ -L$(HOME)/lib/. $(LIBS)
	cp $@ $(HOME)/lib/lib$*.so

build/%.dylib: $(OBJS)
	$(CXX) -install_name "@rpath/lib$*.dylib" -dynamiclib -o $@ $^ -L$(HOME)/lib/. $(LIBS)
	cp $@ $(HOME)/lib/lib$*.dylib

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<

