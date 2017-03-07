CC = clang++
CPPFLAGS = -std=c++11 -Wall -g
CFLAGS = -std=c -Wall -g
CDIR = /Users/rdaly/coreir
INCS = -I$(CDIR)/src -I$(CDIR)/libs
LIBS = -L$(CDIR)/src -L$(CDIR)/libs
DEPS = 

all: add4.run gentest.run typetest.run

clean:
	$(MAKE) -C ../src clean
	#$(MAKE) -C ../libs clean
	-@rm -rf *.o *.run* *.core

%.c.run: %.c.o
	$(MAKE) -C ../src coreir.a
	$(CC) $(FLAGS)  -o $@ $^ ../src/coreir.a
	

#$(LIBS) -lcoreir -lstdprims
#TODO hack. Cant figure out how to load libraries
%.run: %.o
	$(MAKE) -C ../src context.a
	#$(MAKE) -C ../libs stdlib.a
	#$(CC) $(CPPFLAGS)  -o $@ $^ ../src/context.a ../libs/stdlib.a
	$(CC) $(CPPFLAGS)  -o $@ $^ ../src/context.a
	#./$@

%.o: %.cpp 
	$(CC) $(CPPFLAGS) $(INCS) -c -o $@ $< 

%.c.o: %.c 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 

