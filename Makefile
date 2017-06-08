UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Linux)
TARGET = so
endif
ifeq ($(UNAME_S), Darwin)
TARGET = dylib
endif

all: install test

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
	$(MAKE) -C src build/coreir.$(TARGET)
	$(MAKE) -C src/lib $(TARGET)


.PHONY: clean
clean:
	rm -rf lib/*
	-rm _*json
	$(MAKE) -C src clean
	$(MAKE) -C src/lib clean
	$(MAKE) -C tests clean

.PHONY: travis
travis: 
	$(MAKE) clean
	$(MAKE) install
	$(MAKE) test
	$(MAKE) py
	$(MAKE) pytest
	
	
