.SUFFIXES:

LIBS = -lcoreir
SRCFILES = $(wildcard [^_]*.cpp)
OBJS = $(patsubst %.cpp,build/%.o,$(SRCFILES))
EXES = $(patsubst %.cpp,build/%,$(SRCFILES))

all: $(EXES)

clean:
	rm -rf build/*
	rm -f _*.json

build/%: build/%.o 
	$(CXX) $(CXXFLAGS) -o $@ $< $(LIBS) 

build/%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c -o $@ $<
