CC = clang++
CFLAGS = -std=c++11 -Wall -g
DEPS = 

SRCDIR = ../../src
LIBSDIR = ../../libs

INCS = -I$(SRCDIR) -I$(LIBSDIR)
LIBS = -L$(SRCDIR) -L$(LIBSDIR)

.SUFFIXES:

all: 
	make -C $(SRCDIR)
	make add4.run
	make jsontest.run
	make gentest.run
	make typetest.run

clean:
	-@rm -rf *.o *.run* *.core

#$(LIBS) -lcoreir -lstdprims
#TODO hack. Cant figure out how to load libraries
%.run: %.o $(SRCDIR)/coreir.a
	#$(CC) $(CPPFLAGS)  -o $@ $^ ../src/context.a ../libs/stdlib.a
	$(CC) $(CFLAGS)  -o $@ $^ $(SRCDIR)/coreir.a
	#./$@

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 

.PHONY: $(SRCDIR)/coreir.a
