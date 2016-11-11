CC = g++
CFLAGS = -std=c++11 

DEPS = types.h
OBJ = test.o types.o

all: main

%.o: %.cpp $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

main: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^
	
clean:
	-rm *.o main
