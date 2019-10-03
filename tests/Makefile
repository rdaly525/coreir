

all:
	$(MAKE) -C unit
	$(MAKE) -C unit-c
	$(MAKE) -C ext 
	$(MAKE) -C float
	$(MAKE) -C simulator
	# cd magma/inline && ls && ./run_tests.sh

clean:
	$(MAKE) -C unit clean
	$(MAKE) -C unit-c clean
	$(MAKE) -C ext clean
	$(MAKE) -C simulator clean
