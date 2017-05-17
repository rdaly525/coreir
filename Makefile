all:

.PHONY: test
test: install
	$(MAKE) -C tests
	cd tests; ./run

.PHONY: pytest
pytest: py
	cd tests
	pytest;

.PHONY: py
py: install
	pip install -e bindings/python
	pip3 install -e bindings/python


.PHONY: install
install:
	$(MAKE) -C src build/coreir.so
	$(MAKE) -C src/lib so

.PHONY: osx
osx:
	$(MAKE) -C src build/coreir.dylib
	$(MAKE) -C src/lib dylib

.PHONY: clean
clean:
	rm -rf lib/*
	$(MAKE) -C src clean
	$(MAKE) -C src/lib clean
	$(MAKE) -C tests clean

.PHONY: travis
travis: clean osx test pytest 
