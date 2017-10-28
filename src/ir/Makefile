HOME = ../..
INCS = -I$(HOME)/include -I.
ifdef COREIR_INCLUDE_PYTHON_TYPEGEN
	PYTHON_CONFIG ?= python-config
	PYTHONHOME = $(shell $(PYTHON_CONFIG) --prefix)
	CXXFLAGS += $(shell $(PYTHON_CONFIG) --includes) -DCOREIR_INCLUDE_PYTHON_TYPEGEN -DPYTHON_HOME="L\"$(PYTHONHOME)\""
	PYTHON_LIBS = $(PYTHONHOME)/lib
	LDFLAGS += -L $(PYTHON_LIBS) $(shell $(PYTHON_CONFIG) --libs)
	DYLDFLAGS = -Wl,-rpath,$(PYTHON_LIBS)
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
	$(CXX) $(LDFLAGS) $(DYLDFLAGS) -install_name "@rpath/lib$*.dylib" -dynamiclib -o $@ $^
	cp $@ $(HOME)/lib/lib$*.dylib

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
