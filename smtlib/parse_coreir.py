import coreir

def load_core(f, *libs):
    context = coreir.Context()
    for lib in libs:
        context.load_library(lib)

    top_module = context.load_from_file(f)
#    top_def = top_module.definition
    
