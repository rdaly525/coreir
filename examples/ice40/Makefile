.PHONY: all

all: fullAdder

% :: %.json
	../../bin/coreir -l lib/libcoreir-ice40.dylib -p verilog -i $< -o $@.v

clean:
	$(RM) fullAdder.v
