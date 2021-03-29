CXXFLAGS = -std=c++17 -Wall -fPIC -Werror

export CXX
export CFLAGS
export CXXFLAGS

.PHONY: test
test: 
	$(MAKE) -C tests
	cd tests; ./run
	$(MAKE) -C tutorial/hellocounter
	cd tutorial/hellocounter; ./run

installtest:
	coreir -i examples/counters.json -p "rungenerators; flatten; verifyconnectivity --onlyinputs"

#.PHONY: uninstall
#uninstall:
#	-rm $(prefix)/bin/coreir
#	-rm $(prefix)/lib/libcoreir.*
#	-rm $(prefix)/lib/libcoreir-*
#	-rm $(prefix)/include/coreir.h
#	-rm $(prefix)/include/coreirsim.h
#	-rm -r $(prefix)/include/coreir
#	-rm -r $(prefix)/include/coreir-c

.PHONY: testclean
testclean:
	$(MAKE) -C tests clean

.PHONY: release
release:
	-rm -rf release/include release/lib release/bin
	#$(MAKE) -C src so
	#$(MAKE) -C src dylib
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
