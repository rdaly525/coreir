import coreir
import os


def test_genargs():
    context = coreir.Context()
    cgra = context.load_library("cgralib")
    mod = context.load_from_file(os.path.join(os.path.dirname(os.path.realpath(__file__)), "genargs.json"))
    for instance in mod.definition.instances:
        for name, arg in instance.generator_args.items():
            if name == "width":
                assert arg.value == 16
            elif name == "numdataports":
                assert instance.module_name == "PE"
                assert arg.value == 2
            elif name == "numbitports":
                assert instance.module_name == "PE"
                assert arg.value == 3
            elif name in {"en", "clr", "rst"}:
                assert instance.module_name == "reg"
                assert arg.value == False
            else:
                assert False, "Should not reach this statement, {}".format(name)


if __name__ == "__main__":
    test_genargs()
