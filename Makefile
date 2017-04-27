all:

test:
	make -C tests
	cd tests; ./run

install:
	make -C src build/coreir.so
	make -C lib so

installosx:
	make -C src build/coreir.dylib
	make -C lib dylib

clean:
	rm -rf bin/*
	make -C src clean
	make -C lib clean
	make -C tests clean
