#!/bin/sh
find src/. -name "*.h" -or -name "*.cpp" | xargs clang-format -i
echo "Done with src"
find include/. -name "*.h" -or -name "*.cpp" | xargs clang-format -i
echo "Done with include"
find tests/. -iname *.h -o -iname *.cpp | xargs clang-format -i
echo "Done with test"
