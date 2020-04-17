#!/bin/sh
find src/. include/. tests/. -name "*.h*" -or -name "*.c*" | xargs clang-format -i
