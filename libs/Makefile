CC = clang++ -g
CFLAGS = -std=c++11 -Wall -ferror-limit=5
COREIR_CORE = /Users/rdaly/coreir/src
INCS = -I$(COREIR_CORE)
LIBS = -L$(COREIR_CORE)
DEPS = 

all: stdlib.a

clean:
	-@rm *.o *.a

%.a: %.o 
	ar rcs $@ $^

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 
