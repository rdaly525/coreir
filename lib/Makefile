.SUFFIXES:

COREIRCONFIG ?= g++
CXX ?= g++

ifeq ($(COREIRCONFIG),g++)
CXX = g++
endif

ifeq ($(COREIRCONFIG),g++-4.9)
CXX = g++-4.9
endif

CXXFLAGS = -std=c++11  -Wall  -fPIC 

ifdef COREDEBUG
CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG
endif

INCS = -I../include -I.
DEPS = 
SRCFILES = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

all: build/stdlib.so $(OBJS)

clean:
	rm -rf build/*

build/%.so: $(OBJS)
	$(CXX) -shared -o $@ $^
	mv $@ ../bin/.

build/%.dylib: $(OBJS)
	$(CXX) -dynamiclib -o $@ $^
	mv $@ ../bin/.

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<


