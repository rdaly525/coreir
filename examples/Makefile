CC = clang++
CFLAGS = -std=c++11 -Wall -g
CDIR = /Users/rdaly/coreir
INCS = -I$(CDIR)/src -I$(CDIR)/libs
LIBS = -L$(CDIR)/src -L$(CDIR)/libs
DEPS = 

all: add4.run gentest.run typetest.run

clean:
	$(MAKE) -C ../src clean
	#$(MAKE) -C ../libs clean
	-@rm -rf *.o *.run* *.core


#$(LIBS) -lcoreir -lstdprims
#TODO hack. Cant figure out how to load libraries
%.run: %.o
	$(MAKE) -C ../src context.a
	#$(MAKE) -C ../libs stdlib.a
	#$(CC) $(CFLAGS)  -o $@ $^ ../src/context.a ../libs/stdlib.a
	$(CC) $(CFLAGS)  -o $@ $^ ../src/context.a
	#./$@

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 
