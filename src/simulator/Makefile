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

HOME = ../../
LPATH = -L$(HOME)/lib
INCS = -I$(HOME)/include -I.
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

all: $(OBJS)

clean:
	rm -rf build/*

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
