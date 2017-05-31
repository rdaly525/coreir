import coreir.context

class CoreIRType(object):
    def __init__(self, ptr, context):
        self.ptr = ptr
        assert isinstance(context, coreir.context.Context)
        self.context = context
