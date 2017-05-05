all:

test:
	$(MAKE) -C tests
	cd tests; ./run

pytest:
	pip install -e bindings/python
	pip3 install -e bindings/python
	cd tests
	pytest;

install:
	$(MAKE) -C src build/coreir.so
	$(MAKE) -C src/lib so

osx:
	$(MAKE) -C src build/coreir.dylib
	$(MAKE) -C src/lib dylib

clean:
	rm -rf lib/*
	$(MAKE) -C src clean
	$(MAKE) -C src/lib clean
	$(MAKE) -C tests clean

travis:
	$(MAKE) clean
	$(MAKE) osx
	$(MAKE) test
	$(MAKE) pytest
