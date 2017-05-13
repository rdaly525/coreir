

all:
	$(MAKE) -C coreir-c
	$(MAKE) -C passes
	$(MAKE) -C libs

so:
	$(MAKE) -C coreir-c so
	$(MAKE) -C passes so
	$(MAKE) -C libs so

dylib:
	$(MAKE) -C coreir-c dylib
	$(MAKE) -C passes dylib
	$(MAKE) -C libs dylib


clean:
	$(MAKE) -C coreir-c clean
	$(MAKE) -C passes clean
	$(MAKE) -C libs clean
