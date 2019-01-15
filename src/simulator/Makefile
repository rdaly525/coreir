# COREIRCONFIG ?= g++
# CXX ?= g++

# ifeq ($(COREIRCONFIG),g++)
# CXX = g++
# endif

# ifeq ($(COREIRCONFIG),g++-4.9)
# CXX = g++-4.9
# endif

# ifdef COREDEBUG
# CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG 
# endif

#HOME = ../../
#LPATH = -L$(HOME)/lib
#INCS = -I$(HOME)/include -I.
#SRCFILES = $(wildcard [^_]*.cpp)
#OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
#
#all: $(OBJS)
#
#clean:
#	rm -rf build/*
#
#build/%.o: %.cpp $(DEPS)
#	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<


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
	$(CXX) -shared -o $@ $^ $(LIBS)
	cp $@ $(HOME)/lib/lib$*.so

build/%.dylib: $(OBJS)
	echo "ROSS"
	$(CXX) -install_name "@rpath/lib$*.dylib" -dynamiclib -o $@ $^ -L$(HOME)/lib/. $(LIBS)
	cp $@ $(HOME)/lib/lib$*.dylib

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<

