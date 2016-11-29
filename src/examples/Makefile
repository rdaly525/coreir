CC = clang++
CFLAGS = -std=c++11 -Wall -g
MAGMAIR_CORE = /Users/rdaly/magmair/src/core
INCS = -I$(MAGMAIR_CORE)
LIBS = -L$(MAGMAIR_CORE)
DEPS = 

all: addtree.run

clean:
	rm *.o *.run

#TODO hack. The fucking library loading wont fucking work
%.run: %.o ../core/magmair.a
	$(CC) $(CFLAGS) -o $@ $^ ../core/magmair.a

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 
