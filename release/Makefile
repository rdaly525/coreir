UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Linux)
TARGET = so
prefix?=/usr
endif
ifeq ($(UNAME_S), Darwin)
TARGET = dylib
prefix?=/usr/local
endif

.PHONY: install
install:
	install bin/coreir $(prefix)/bin
	install lib/libcoreir.$(TARGET) $(prefix)/lib
	install lib/libcoreir-* $(prefix)/lib
	install -d $(prefix)/include/coreir-c
	install -d $(prefix)/include/coreir/ir/casting
	install -d $(prefix)/include/coreir/libs
	install -d $(prefix)/include/coreir/passes/analysis
	install -d $(prefix)/include/coreir/passes/transform
	install -d $(prefix)/include/coreir/simulator
	install include/coreir.h $(prefix)/include
	install include/coreir-c/* $(prefix)/include/coreir-c
	install include/coreir/*.h $(prefix)/include/coreir
	install include/coreir/ir/*.h $(prefix)/include/coreir/ir
	install include/coreir/ir/casting/* $(prefix)/include/coreir/ir/casting
	install include/coreir/libs/* $(prefix)/include/coreir/libs
	install include/coreir/passes/*.h $(prefix)/include/coreir/passes
	install include/coreir/passes/analysis/* $(prefix)/include/coreir/passes/analysis
	install include/coreir/passes/transform/* $(prefix)/include/coreir/passes/transform
	install include/coreir/simulator/* $(prefix)/include/coreir/simulator

.PHONY: uninstall
uninstall:
	-rm $(prefix)/bin/coreir
	-rm $(prefix)/lib/libcoreir.*
	-rm $(prefix)/lib/libcoreir-*
	-rm $(prefix)/include/coreir.h
	-rm -r $(prefix)/include/coreir
	-rm -r $(prefix)/include/coreir-c
