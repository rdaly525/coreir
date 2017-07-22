class LazyDict:
    """
    Lazy object that implements the ``dict[key]`` interface. Instead
    of building the dictionary explicitly for every call to config, we wait for
    the indexing function to be called and then use the api function
    """
    def __init__(self, parent, return_type, api_function):
        self.parent = parent
        self.return_type = return_type
        self.api_function = api_function

    def __getitem__(self, key):
        return self.return_type(
                   self.api_function(self.parent.ptr,
                                     str.encode(key)),
                   self.parent.context)

    def __setitem__(self, key, value):
        raise NotImplementedError()
