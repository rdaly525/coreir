import sys


usage = "Usage: %s smt2file k-steps > 0"%sys.argv[0]

if len(sys.argv) < 3:
    print(usage)
    exit(0)

k = int(sys.argv[2])

model = ""
with open(sys.argv[1]) as f:
    model = f.read()

setvals = []
curr_vars = []
next_vars = []
trans = []

CURR = "__CURR__"
NEXT = "__NEXT__"

for line in model.split("\n"):
    if ("declare-fun" in line):
        if (CURR in line):
            curr_vars.append(line)
        if (NEXT in line):
            next_vars.append(line)
    elif ("set" in line):
        setvals.append(line)
    else:
        trans.append(line)

def at(time):
    return "__AT%s"%time

# time 0

print("\n".join(setvals))
print(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;; TIME 0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;")
print("\n".join([x.replace(CURR, at(0)) for x in curr_vars]))
print("\n".join([x.replace(NEXT, at(1)) for x in next_vars]))
print("\n".join([x.replace(CURR, at(0)).replace(NEXT, at(1)) for x in trans]))

for t in xrange(k-1):
    print(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;; TIME %s ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"%(t+1))
    print("\n".join([x.replace(NEXT, at(t+2)) for x in next_vars]))
    print("\n".join([x.replace(CURR, at(t+1)).replace(NEXT, at(t+2)) for x in trans]))
    
print("(check-sat)")
