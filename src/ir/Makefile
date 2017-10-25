HOME = ../..
INCS = -I$(HOME)/include -I.
ifdef COREIR_INCLUDE_PYTHON_TYPEGEN
	PYTHON_CONFIG ?= python-config
	CXXFLAGS += $(shell $(PYTHON_CONFIG) --includes) -DCOREIR_INCLUDE_PYTHON_TYPEGEN 
	PYTHON_LIBPATH = $(shell $(PYTHON_CONFIG) --prefix)/lib
	LDFLAGS += -L $(PYTHON_LIBPATH) $(shell $(PYTHON_CONFIG) --libs) -Wl,-rpath,$(PYTHON_LIBPATH)
endif
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
	$(CXX) $(LDFLAGS) -shared -o $@ $^
	cp $@ $(HOME)/lib/lib$*.so

build/%.dylib: $(OBJS)
	$(CXX) $(LDFLAGS) -install_name "@rpath/lib$*.dylib" -dynamiclib -o $@ $^
	cp $@ $(HOME)/lib/lib$*.dylib

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
