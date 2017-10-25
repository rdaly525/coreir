# Python and coreir
## Bindings
`pycoreir` provides bindings to coreir's C-api using ctypes. 
```
pip install coreir
```

##
Using Python `typegen` support

Compile with `COREIR_INCLUDE_PYTHON_TYPEGEN` set
```
make install -j 8 COREIR_INCLUDE_PYTHON_TYPEGEN=1
```

If you have a non-standard Python installation such as `miniconda`, pass a specific `python-config` or `python3-config` to the `make` command via the `PYTHON_CONFIG` variable
```
make install -j 8 COREIR_INCLUDE_PYTHON_TYPEGEN=1 PYTHON_CONFIG=python3-config
```
