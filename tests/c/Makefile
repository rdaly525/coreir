CC = clang
CPPC = clang++ -std=c++11
CFLAGS = -Wall -g
CDIR = /Users/rdaly/coreir
INCS = -I$(CDIR)/src -I$(CDIR)/libs
LIBS = -L$(CDIR)/src -L$(CDIR)/libs

all: test.run

clean:
	$(MAKE) -C ../src clean
	#$(MAKE) -C ../libs clean
	-@rm -rf *.o *.run* *.core


#TODO hack. Cant figure out how to load libraries
%.run: %.o
	$(MAKE) -C ../src coreir.a
	$(CPPC) -o $@ $^ ../src/coreir.a

%.o: %.c
	$(CC) $(INCS) -c -o $@ $< 
