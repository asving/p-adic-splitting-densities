#!/usr/bin/env python3
"""M01-track-count independent check: recentering count of the canonical
Newton-polygon walk on a quadratic p-adic cluster (x-a)(x-b).

Walk semantics (the note's D.10 recentering, one side read per node):
  center c starts at 0 (after the level-0 residual read puts both roots
  in the same residue class, WLOG 0 mod p).  At each node: the Newton
  polygon of f(y+c) on the followed quadratic cluster has one side of
  slope -lam, lam = v(a-c) = v(b-c), residual quadratic with roots =
  the level-lam digits of a-c, b-c.  Equal digits d != 0 => repeated
  linear residual factor => D.10 recentering  c += d*p^lam  (count += 1).
  Distinct digits or distinct valuations => the cluster separates
  (branch node, both members leaves) => stop.

CLAIM under test: #recenterings = #{positions lam < v(a-b) at which the
shared expansion of a,b has a NONZERO digit} -- unbounded in m := v(a-b)
at fixed degree n = 2, for every p.
"""

def vp(x, p, cap=10**6):
    if x == 0:
        return cap
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def digit(x, p, lam):
    return (x // p**lam) % p

def walk(a, b, p, maxsteps=10**4):
    """Returns (#recentering nodes, terminal reason)."""
    c, cnt = 0, 0
    for _ in range(maxsteps):
        va, vb = vp(a - c, p), vp(b - c, p)
        assert va >= 1 and vb >= 1, "cluster hypothesis violated"
        if va != vb:
            return cnt, "split-by-slope"
        lam = va
        da, db = digit(a - c, p, lam), digit(b - c, p, lam)
        if da != db:
            return cnt, "split-by-residual"
        # repeated linear residual factor: D.10 recentering
        assert da != 0  # da=0 would contradict lam = v(a-c)
        c += da * p**lam
        cnt += 1
    raise RuntimeError("no separation")

def main():
    print("family A: a = sum_{i=1..m} p^i + p^(m+2),  b = a + p^(m+1)")
    print("expected #rec = m (all m shared digits nonzero)")
    for p in (2, 3, 5):
        row = []
        for m in range(1, 11):
            a = sum(p**i for i in range(1, m + 1)) + p**(m + 2)
            b = a + p**(m + 1)
            cnt, why = walk(a, b, p)
            vd = 2 * vp(a - b, p)  # v_p(disc) of the quadratic factor
            row.append((m, cnt, why, vd))
            assert cnt == m, (p, m, cnt)
        print(f"  p={p}: " + ", ".join(f"m={m}:rec={c}(vdisc={vd})"
                                       for m, c, _, vd in row))
    print("family B (zero digits skipped): shared digits at positions "
          "1,3,5,...  a = sum p^(2i-1), i=1..k;  b = a + p^(2k)")
    for p in (2, 3):
        row = []
        for k in range(1, 8):
            a = sum(p**(2 * i - 1) for i in range(1, k + 1)) + p**(2 * k + 2)
            b = a + p**(2 * k)
            cnt, why = walk(a, b, p)
            row.append((k, cnt, why))
            assert cnt == k, (p, k, cnt)
        print(f"  p={p}: " + ", ".join(f"k={k}:rec={c}" for k, c, _ in row))
    print("family C (random shared digits, p=3): #rec == #nonzero shared "
          "digits, 200 trials")
    import random
    random.seed(7)
    p = 3
    for _ in range(200):
        m = random.randint(1, 20)
        digs = [random.randint(0, p - 1) for _ in range(2, m + 1)]
        # shared expansion: digit 1 at position 1 (cluster at 0 mod p^2 walkable),
        # then random digits at 2..m; b differs first at m+1
        a = p + sum(d * p**(i + 2) for i, d in enumerate(digs))
        a += p**(m + 3)  # generic continuation so a != center ever
        b = a + p**(m + 1)
        nz = 1 + sum(1 for d in digs if d != 0)
        cnt, why = walk(a, b, p)
        assert cnt == nz, (m, digs, cnt, nz)
    print("  all 200 trials: #rec == #nonzero shared digits  [OK]")
    print("\nALL CHECKS PASS: recentering count = #nonzero shared digit "
          "positions; grows without bound at n = 2, any p.")

if __name__ == "__main__":
    main()
