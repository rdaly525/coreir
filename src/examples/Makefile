CC = clang++
CFLAGS = -std=c++11 -Wall -g
CDIR = /Users/rdaly/coreir/src
INCS = -I$(CDIR)/core -I$(CDIR)/libs
LIBS = -L$(CDIR)/core -L$(CDIR)/libs
DEPS = 

all: addtreeNS.run

clean:
	$(MAKE) -C ../core clean
	$(MAKE) -C ../libs clean
	-@rm *.o *.run


#$(LIBS) -lcoreir -lstdprims
#TODO hack. Cant figure out how to load libraries
%.run: %.o
	$(MAKE) -C ../core coreir.a
	$(MAKE) -C ../libs stdprims.a
	$(CC) $(CFLAGS)  -o $@ $^ ../core/coreir.a ../libs/stdprims.a

#../core/coreir.a ../libs/stdprims.a

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 
