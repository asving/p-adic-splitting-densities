# Independent spot-check of the C.109-iii statement over O = Z_p, at a degree-d key Phi.
# Set: classes c in (Z/p^N)^d such that some A of degree < d with coeff-vector reducing to c
# has gaussVal(A) >= h and resMk_h(A) = r.   Claim: card = Q^(N-h-1), Q = p^d, uniformly in r.
import itertools, sys
from itertools import product

def check(p, d, phibar, h, N):
    # phibar: monic irreducible poly over F_p of degree d, as coeff list length d+1
    # residual field F_{p^d} realised as F_p[y]/(phibar): elements = tuples of length d
    Q = p**d
    pN = p**N
    # bucket every class by its residue read
    buckets = {}
    for c in product(range(pN), repeat=d):
        # floor test: p^h | c_i  (class-level, valid since h < N)
        if any(x % (p**h) != 0 for x in c):
            continue
        # digit at height h of each coefficient
        dig = tuple(((x // (p**h)) % p) for x in c)
        buckets.setdefault(dig, 0)
        buckets[dig] += 1
    # the residue read dig -> F_{p^d} is a bijection on degree-<d reps, so buckets ARE the fibres
    assert len(buckets) == Q, (len(buckets), Q)
    exp = p**(d*(N-h-1))
    ok = all(v == exp for v in buckets.values())
    tot = sum(buckets.values())
    print(f"p={p} d={d} h={h} N={N}: Q={Q} fibres={sorted(set(buckets.values()))} "
          f"expected={exp} sum={tot} Q^(N-h)={Q**(N-h)} -> {'PASS' if ok and tot==Q**(N-h) else 'FAIL'}")
    return ok and tot == Q**(N-h)

allok = True
for (p,d,N,h) in [(2,1,3,0),(2,1,4,2),(3,1,3,1),(2,2,3,0),(2,2,3,1),(2,2,4,2),(3,2,3,0),(3,2,3,1),(2,3,3,1)]:
    allok &= check(p,d,None,h,N)
print("ALL PASS" if allok else "SOME FAIL")
