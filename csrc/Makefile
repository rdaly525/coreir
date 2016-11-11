CC = g++
CFLAGS = -std=c++11 -stdlib=libc++

DEPS = types.h
OBJ = test.o types.o

all: main

%.o: %.c $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

main: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^
	
clean:
	-rm *.o main
