import coreir


context = coreir.Context()
coreir_primitives = context.get_namespace("coreir")
counter_type = context.Record({
    "en"  : context.BitIn(),
    "out" : context.Array(16, context.Bit()),
    "clk" : context.get_named_type("coreir", "clkIn")
})

counter = context.G.new_module("counter", counter_type)
counter_definition = counter.new_definition()

Add = coreir_primitives.generators["add"]
Reg = coreir_primitives.generators["reg"]
Const = coreir_primitives.generators["const"]

add_inst = counter_definition.add_generator_instance("add_inst", Add,
        context.newArgs({"width": 16}))

const_inst = counter_definition.add_generator_instance("const_inst", Const,
        context.newArgs({"width": 16}), context.newArgs({"value": 1}))

reg_inst = counter_definition.add_generator_instance("reg_inst", Reg,
        context.newArgs({"width": 16, "en": True, "clr": False, "rst": False}),
        context.newArgs({"init": 0}))

counter_definition.connect(add_inst.select("out"), reg_inst.select("in"))

counter_interface = counter_definition.interface

counter_definition.connect(counter_interface.select("en"),
        reg_inst.select("en"))

counter_definition.connect(counter_interface.select("clk"),
        reg_inst.select("clk"))

counter_definition.connect(counter_definition.select("const_inst.out"),
        counter_definition.select("add_inst.in0"))

counter_definition.connect(counter_definition.select("reg_inst.out"),
        counter_definition.select("add_inst.in1"))

counter_definition.connect(counter_definition.select("reg_inst.out"),
        counter_definition.select("self.out"))

counter.definition = counter_definition

counter.print_()
