all:
	$(MAKE) -C ir
	$(MAKE) -C coreir-c
	$(MAKE) -C passes
	$(MAKE) -C libs

so:
	$(MAKE) -C ir so
	$(MAKE) -C coreir-c so
	$(MAKE) -C passes so
	$(MAKE) -C libs so

dylib:
	$(MAKE) -C ir dylib
	$(MAKE) -C coreir-c dylib
	$(MAKE) -C passes dylib
	$(MAKE) -C libs dylib


clean:
	$(MAKE) -C ir clean
	$(MAKE) -C coreir-c clean
	$(MAKE) -C passes clean
	$(MAKE) -C libs clean
