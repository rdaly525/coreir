UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Linux)
TARGET = so
endif
ifeq ($(UNAME_S), Darwin)
TARGET = dylib
endif

all: install bin epass

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

.PHONY: bin
bin: install
	$(MAKE) -C src/binary -B

.PHONY: epass
epass: install
	$(MAKE) -C epasses -B $(TARGET)

.PHONY: clean
clean:
	rm -rf lib/*
	rm -rf bin/*
	-rm _*json
	-rm _*fir
	-rm _*v
	$(MAKE) -C src clean
	$(MAKE) -C tests clean
	$(MAKE) -C epasses clean

.PHONY: travis
travis: 
	$(MAKE) clean
	$(MAKE) install
	$(MAKE) test
	$(MAKE) py
	$(MAKE) pytest
	
	
