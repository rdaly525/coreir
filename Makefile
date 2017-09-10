prefix=/usr/local

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Linux)
TARGET = so
endif
ifeq ($(UNAME_S), Darwin)
TARGET = dylib
endif

all: install coreir

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
	$(MAKE) -C src $(TARGET)
	install bin/coreir $(prefix)/bin
	install lib/* $(prefix)/lib
	install -d $(prefix)/include/coreir-c
	install -d $(prefix)/include/coreir-lib
	install -d $(prefix)/include/coreir-passes
	install -d $(prefix)/include/coreir-passes/analysis
	install -d $(prefix)/include/coreir-passes/transform
	install include/*.h $(prefix)/include
	install include/coreir-c/* $(prefix)/include/coreir-c
	install include/coreir-lib/* $(prefix)/include/coreir-lib
	install include/coreir-passes/*.h $(prefix)/include/coreir-passes
	install include/coreir-passes/analysis/* $(prefix)/include/coreir-passes/analysis
	install include/coreir-passes/transform/* $(prefix)/include/coreir-passes/transform

.PHONY: coreir
coreir: install
	$(MAKE) -C src/binary -B

.PHONY: clean
clean:
	rm -rf lib/*
	rm -rf bin/*
	-rm _*json
	-rm _*fir
	-rm _*v
	$(MAKE) -C src clean
	$(MAKE) -C tests clean

.PHONY: travis
travis:
	$(MAKE) clean
	$(MAKE) install
	$(MAKE) test
	$(MAKE) py
	$(MAKE) pytest
