all:

test:
	make -C tests
	cd tests; ./run
	
pytest:
	pip install -e bindings/python
	pip3 install -e bindings/python
	cd tests
	pytest;

install:
	make -C src build/coreir.so
	make -C src/lib so

osx:
	make -C src build/coreir.dylib
	make -C src/lib dylib

clean:
	rm -rf lib/*
	make -C src clean
	make -C src/lib clean
	make -C tests clean

travis:
	make clean
	make osx
	make test
	make pytest
