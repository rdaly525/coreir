CC = clang++
CFLAGS = -std=c++11 -Wall -g
CDIR = 
#INCS = -I$(CDIR)/src -I$(CDIR)/libs
#LIBS = -L$(CDIR)/src -L$(CDIR)/libs
INCS = -I../src -I../libs
LIBS = -L../src -L../libs
DEPS = 

.SUFFIXES:

all: 
	#add4.run gentest.run typetest.run jsontest.run
	make -C ../src
	make jsontest.run

clean:
	-@rm -rf *.o *.run* *.core

#$(LIBS) -lcoreir -lstdprims
#TODO hack. Cant figure out how to load libraries
%.run: %.o ../src/coreir.a
	#$(CC) $(CPPFLAGS)  -o $@ $^ ../src/context.a ../libs/stdlib.a
	$(CC) $(CFLAGS)  -o $@ $^ ../src/coreir.a
	#./$@

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 

.PHONY: ../src/coreir.a
