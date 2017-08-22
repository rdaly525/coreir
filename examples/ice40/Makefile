.PHONY: all

all: FullAdder

FullAdder :: FullAdder.json
	../../bin/coreir -l ../../lib/libcoreir-ice40.dylib -i $< -o $@.v
	yosys -p 'synth_ice40 -top $@ -blif $@.blif' $@.v ../../tools/coreir_prims.v

clean:
	$(RM) fullAdder.v
