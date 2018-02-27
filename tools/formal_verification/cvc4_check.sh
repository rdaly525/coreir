cvc4 $1 --dump-models | sed -E 's/\(\)| \(_ BitVec ([0-9]+)\) |\(define\-fun |\(_ |\)\)| [0-9]+|\(model|\)//g' | sed 's/__CURR__//g' | sed 's/__NEXT__/_N/g' | sed 's/bv/= /g'
