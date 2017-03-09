CC = clang++ -g
CFLAGS = -std=c++11 -Wall -ferror-limit=5
INCS = -I../src/.
#LIBS = -L$(COREIR_CORE)
DEPS = 

all: stdlib.a

clean:
	-@rm *.o *.a

%.a: %.o 
	ar rcs $@ $^

%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -c -o $@ $< 
