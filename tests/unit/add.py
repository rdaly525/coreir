import coreir

@coreir.type_gen
def add_type_gen(context, values):
    width = values['width'].value
    N = values['N'].value
    return context.Record({
        "in": context.Array(N, context.Array(width, context.BitIn())),
        "out": context.Array(width, context.Bit())
    })
