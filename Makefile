
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Linux)
TARGET = so
prefix?=/usr
endif
ifeq ($(UNAME_S), Darwin)
TARGET = dylib
prefix?=/usr/local
endif


COREIRCONFIG ?= g++
CXX ?= g++


ifeq ($(COREIRCONFIG),g++)
CXX = g++
endif

ifeq ($(COREIRCONFIG),g++-4.9)
CXX = g++-4.9
endif

CFLAGS = -Wall -fPIC
#CXXFLAGS = -std=c++11 -Wall -fPIC -Werror -ferror-limit=5
CXXFLAGS = -std=c++11 -Wall -fPIC -Werror

ifdef COREDEBUG
CXXFLAGS += -O0 -g3 -D_GLIBCXX_DEBUG
endif

export CXX
export CFLAGS
export CXXFLAGS

all: build coreir

.PHONY: test
test: build
	$(MAKE) -C tests
	cd tests; ./run

installtest:
	$(MAKE) -C tests/install
	cd tests/install; ./run
	coreir -i examples/counters.json -p rungenerators,flatten,verifyconnectivity-onlyinputs

.PHONY: build
build:
	$(MAKE) -C src $(TARGET)

.PHONY: install
install: build coreir
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

.PHONY: coreir
coreir: build
	$(MAKE) -C src/binary

.PHONY: clean
clean:
	rm -rf lib/*
	rm -rf bin/*
	-rm _*json
	-rm _*fir
	-rm _*v
	-rm -rf release/include
	$(MAKE) -C src clean
	$(MAKE) -C tests clean
	$(MAKE) -C tests/install clean

.PHONY: release
release:
	-rm -rf release/include release/lib release/bin
	$(MAKE) -C src so
	$(MAKE) -C src dylib
	cp -r include release/.
	cp -r lib release/.
	cp -r bin release/.
	tar -zcvf coreir.tar.gz release

.PHONY: travis
travis:
	export COREIR=
	export DYLD_LIBRARY_PATH=
	$(MAKE) clean
	-sudo $(MAKE) uninstall
	$(MAKE) build
	sudo $(MAKE) install
	$(MAKE) installtest
	sudo $(MAKE) uninstall
	export COREIR=/Users/rdaly/coreir
	export DYLD_LIBRARY_PATH=$$DYLD_LIBRARY_PATH:$$COREIR/lib
	$(MAKE) test
