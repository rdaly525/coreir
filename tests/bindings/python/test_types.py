import coreir


def test_array_len():
    context = coreir.Context()
    array_type = context.Array(8, context.BitIn())
    assert len(array_type) == 8
    bit_type = context.BitIn()
    try:
        len(bit_type)
        assert False, "Calling len on a non array type should throw an exception"
    except Exception as e:
        assert str(e) == "`len` called on a non Array Type (BitIn)"
