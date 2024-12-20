from rustsat import Lit, VarManager
from rustsat.encodings.pb import DynamicPolyWatchdog as Dpw

# Lit creates a literal object from an ipasir integer representation.  The
# encoding takes a list of (lit, weight) pairs as input.
input_lits = [
    (Lit(1), 5),
    (Lit(-2), 4),
    (Lit(3), 3),
    (Lit(-4), 2),
    (Lit(5), 1),
]

# Getting unused variables is handled by a VarManager. Create one that has 5
# variables already used.
vm = VarManager(n_used=5)

dpw = Dpw(input_lits)

# Build the CNF encoding. This purely builds the structure and does not enforce
# any bounds. The encode function takes a max and min bound. After encoding
# with max and min, bounds in the range max..=min can be enforced.
cnf = dpw.encode_ub(3, 5, vm)

# Add the CNF encoding to the SAT solver. For this example, we dump it in
# DIMACS format.
for cl in cnf:
    for l in cl:
        print(l.to_ipasir(), end=" ")
    print("0")

# Get assumptions to enforce an upper bound of 4 on the input literals. The
# assumptions are a list of literals.
assumps = dpw.enforce_ub(4)

# The following line would fail because we only encoded 3..=5.
# assumps = dpw.enforce_ub(7)

# The encoding can be incrementally extended to lower or higher bounds.
ext_cnf = dpw.encode_ub(6, 8, vm)
ext_cnf_2 = dpw.encode_ub(1, 2, vm)
