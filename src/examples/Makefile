CC = clang++
CFLAGS = -std=c++11 -Wall -g
CDIR = /Users/rdaly/coreir/src
INCS = -I$(CDIR)/core -I$(CDIR)/libs
LIBS = -L$(CDIR)/core -L$(CDIR)/libs
DEPS = 

all: add4.run

clean:
	$(MAKE) -C ../core clean
	$(MAKE) -C ../libs clean
	-@rm -rf *.o *.run* *.core


#$(LIBS) -lcoreir -lstdprims
#TODO hack. Cant figure out how to load libraries
%.run: %.o
	$(MAKE) -C ../core context.a
	$(MAKE) -C ../libs stdlib.a
	$(CC) $(CFLAGS)  -o $@ $^ ../core/context.a ../libs/stdlib.a
	#$(CC) $(CFLAGS)  -o $@ $^ ../core/context.a
	#./$@

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 
