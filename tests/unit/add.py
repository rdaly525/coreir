import coreir

def type_gen(context, args):
    assert isinstance(context, coreir.Context)
    assert isinstance(args, coreir.Args)
    print("Success")
