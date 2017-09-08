all:
	$(MAKE) -C simulator
	$(MAKE) -C passes
	$(MAKE) -C ir
	$(MAKE) -C coreir-c
	$(MAKE) -C libs

so:
	$(MAKE) -C simulator
	$(MAKE) -C passes
	$(MAKE) -C ir so
	$(MAKE) -C coreir-c so
	$(MAKE) -C libs so

dylib:
	$(MAKE) -C simulator
	$(MAKE) -C passes
	$(MAKE) -C ir dylib
	$(MAKE) -C coreir-c dylib
	$(MAKE) -C libs dylib

clean:
	$(MAKE) -C simulator clean
	$(MAKE) -C passes clean
	$(MAKE) -C ir clean
	$(MAKE) -C coreir-c clean
	$(MAKE) -C libs clean
	$(MAKE) -C binary clean
