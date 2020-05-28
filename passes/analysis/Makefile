HOME = ../../..
LPATH = -L$(HOME)/lib
INCS = -I$(HOME)/include -I.
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))

all: $(OBJS)

clean:
	rm -rf build/*

build/%.o: %.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(INCS) -c -o $@ $<
