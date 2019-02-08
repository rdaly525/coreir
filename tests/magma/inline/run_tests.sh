#!/bin/bash

../../../bin/coreir -i test_simple_top.json -o test_simple_top.v --inline
cmp test_simple_top.v gold/test_simple_top.v

../../../bin/coreir -i test_two_ops.json -o test_two_ops.v --inline
cmp test_two_ops.v gold/test_two_ops.v

../../../bin/coreir -i test_const.json -o test_const.v --inline
cmp test_const.v gold/test_const.v
