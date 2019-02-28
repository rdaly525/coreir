import pytest


@pytest.fixture(autouse=True)
def mantle_test():
    """
    Clear the circuit cache before running, allows name reuse across tests
    without collisions
    """
    import magma.config
    magma.config.set_compile_dir('callee_file_dir')

    from magma import clear_cachedFunctions
    clear_cachedFunctions()

    from magma.circuit import magma_clear_circuit_cache
    magma_clear_circuit_cache()

    magma.backend.coreir_.__reset_context()

