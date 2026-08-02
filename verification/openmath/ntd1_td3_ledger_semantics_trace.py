#!/usr/bin/env python3
"""
N-TD1 (blueprint B2DEF_LEAN_2026-08-08 §7) — TD-3 statement gate, run BEFORE proof effort.

TARGET STATEMENT (lean/LeanUrat/B2D/TD3_digitsProd.lean, unit TD-3):
  ledger_digitsProd : LedgerLawful L -> LedgerScope -> LedgerClean ->
                      DigitsProdLaw W P L.ledgerJoint
where (FreshLaws.lean) DigitsProdLaw demands, at q = q0, rho < rho0, in-range z:
  fiberDigits(rho, z)  =  PROD_{k in onLine} slotDigits(rho,k,z_k)
                        * PROD_{k in boxSlots \\ onLine} slotCount(rho,k)
and (TDDefs.lean) LedgerSemantics ties the LHS to
  Nat.card { x : Coord -> NAT  |  inStratum rho x  and  x(slotCoord k) = z_k }   (*)
with Coord = NAT x NAT (INFINITE index set, UNBOUNDED digit values), while
LedgerLawful ties the RHS factors to blockCount = #{ v : block -> Fin q0 | cond }
(FINITE) and forces their values positive (slot_count_val: q0^(mN - s(max beta g)) >= 1).

THE TRACE: at each instance below we compute, in exact integer arithmetic,
  [RHS]    the product side, from the blockCount enumerations the LedgerLawful
           clauses slot_sem / slotDigits_sem / slot_count_val pin;
  [LHS-L]  the landed Lean semantics (*): we certify Nat.card = 0 by the
           empty-or-infinite dichotomy — membership reads only the finite block
           union U (member_split + parent_support + slot_support), so one member
           yields infinitely many (vary any coordinate off U); we EXHIBIT the
           growth by enumerating members over widening support windows;
  [LHS-M]  the intended MOVES D.11 semantics: members of the finite level-N box
           (support inside the box, digit values < q0) — the accepted
           attainable-product count, expected to MATCH [RHS].

VERDICT expected if the E2 transcription seam is real: [LHS-M] == [RHS] > 0 at
every instance (the MATH holds) but [LHS-L] = 0 != [RHS] (the LEAN STATEMENT
fails) => per the discipline: STOP, build the countermodel, do not prove TD-3.
"""

from itertools import product

# ----- generic machinery ----------------------------------------------------

def block_count(q0, block, cond):
    """#{ v : block -> Fin q0 | cond(extension-by-zero of v) }  (TDDefs.blockCount)."""
    block = sorted(block)
    n = 0
    for vals in product(range(q0), repeat=len(block)):
        v = dict(zip(block, vals))
        x = lambda c, v=v: v.get(c, 0)
        if cond(x):
            n += 1
    return n

def members_on_window(inst, rho, z, window, vmax):
    """Members of the (*) set with support restricted to `window` and values < vmax.
    Every such member IS a genuine element of the Lean set (*): x : Coord -> NAT,
    zero off `window`.  Used to certify the infinite horn of the dichotomy."""
    window = sorted(window)
    out = []
    for vals in product(range(vmax), repeat=len(window)):
        v = dict(zip(window, vals))
        x = lambda c, v=v: v.get(c, 0)
        if inst["inStratum"](rho, x) and all(x(inst["slotCoord"][k]) == z[k] for k in inst["onLine"]):
            out.append(vals)
    return out

def rhs_product(inst, rho, z):
    q0 = inst["q0"]
    r = 1
    for k in inst["onLine"]:
        r *= block_count(q0, inst["slotBlock"][k],
                         lambda x, k=k: inst["slotCond"](rho, k, x) and x(inst["slotCoord"][k]) == z[k])
    for k in sorted(set(inst["boxSlots"]) - set(inst["onLine"])):
        r *= block_count(q0, inst["slotBlock"][k],
                         lambda x, k=k: inst["slotCond"](rho, k, x))
    return r

def lawfulness_spotchecks(inst):
    """The finitely-checkable LedgerLawful clauses at the instance (support and
    member_split hold BY CONSTRUCTION: conditions are functions of block values)."""
    q0, d = inst["q0"], inst["d"]
    msgs = []
    blocks = inst["slotBlock"]
    for k in blocks:
        for kk in blocks:
            if k != kk:
                assert not (set(blocks[k]) & set(blocks[kk])), "slots_disjoint FAILS"
    msgs.append("slots_disjoint OK")
    for k in inst["onLine"]:
        assert inst["slotCoord"][k] in blocks[k], "slot_coord_mem FAILS"
        assert not (set(inst["parentBlock"]) & set(blocks[k])) or k == inst["ks"], \
            "parent_interior_disjoint FAILS"
    msgs.append("slot_coord_mem / parent_interior_disjoint OK")
    for rho in range(inst["rho0"]):
        assert inst["pin"](rho) != 0 and inst["pin"](rho) < q0 ** d, "pin clauses FAIL"
        for k in inst["boxSlots"]:
            got = block_count(q0, blocks[k], lambda x, k=k: inst["slotCond"](rho, k, x))
            want = q0 ** inst["slot_val_exp"][k]     # slot_count_val's forced value
            assert got == want, f"slot_count_val FAILS at k={k}: {got} != {want}"
    msgs.append("hpin_ne/hpin_lt + slot_count_val OK (block enumerations exact)")
    return msgs

def run(inst):
    q0, d = inst["q0"], inst["d"]
    print(f"\n=== {inst['name']} ===  (q0={q0}, d={d}, boxSlots={inst['boxSlots']}, "
          f"onLine={inst['onLine']}, rho0={inst['rho0']})")
    for m in lawfulness_spotchecks(inst):
        print("   lawful:", m)
    rho = 0
    z = inst["z"]                    # the probed in-range digit vector
    assert all(z[k] < q0 ** d for k in inst["onLine"])
    rhs = rhs_product(inst, rho, z)

    # [LHS-L] the landed Lean semantics: empty-or-infinite certificate
    U = sorted(set(inst["parentBlock"]) | {c for k in inst["slotBlock"] for c in inst["slotBlock"][k]})
    base = members_on_window(inst, rho, z, U, q0)          # members supported on U
    growth = []
    off = [(99, 0), (99, 1)]                               # coordinates OFF the block union
    assert not (set(off) & set(U))
    for j in (0, 1, 2):
        w = U + off[:j]
        growth.append(len(members_on_window(inst, rho, z, w, q0 + j)))
    lhs_lean = 0 if base else 0     # nonempty => infinite => Nat.card = 0; empty => 0
    print(f"   [LHS-L] members on U: {len(base)}; on widening windows/value-caps: {growth}"
          f"  -> {'INFINITE set' if base else 'empty set'} -> Nat.card = {lhs_lean}")

    # [LHS-M] the intended MOVES D.11 finite level-N box count
    box = inst["box"]                # the level-N coefficient box (finite)
    assert set(U) <= set(box)
    lhs_moves = len(members_on_window(inst, rho, z, box, q0))
    print(f"   [LHS-M] intended finite-box count (support in box, digits < q0): {lhs_moves}")
    print(f"   [RHS]   product side (blockCount enumerations):                  {rhs}")

    ok_math = (lhs_moves % rhs == 0 if rhs else lhs_moves == 0)
    # free coordinates of the box outside all blocks contribute q0 each — divide out:
    free = len(box) - len(U)
    ok_math = lhs_moves == rhs * (q0 ** free)
    print(f"   [MATH]  box has {free} free off-block coords: product predicts "
          f"{rhs} * {q0}^{free} = {rhs * q0**free}  -> {'MATCH' if ok_math else 'MISMATCH'}")
    verdict = (lhs_lean == rhs)
    print(f"   [GATE]  DigitsProdLaw at the LEAN semantics: {lhs_lean} == {rhs} ? "
          f"{'holds' if verdict else 'FAILS'}")
    return verdict, ok_math

# ----- the three shallow instances ------------------------------------------
# Coordinates are pairs (slot, height).  All instances mirror compilable
# LedgerStratumData/LedgerLawful data (same clause shapes as TDDefs.lean).

INSTANCES = [
    # i1 — THE MINIMAL LAWFUL INSTANCE (mirrors the planned Lean countermodel):
    # census r=0, e=h=f=[1] => d=1, period=1, m=1, s==1; N=2; exponent mN-s = 1.
    # W: ell=1, n=1, monicTop=true (1|1 forced), boxSlots={0}, onLine={} (ks=1 erased).
    # slotCond 0 = True on block {(0,0)}; parentCond = True, parentBlock = {}.
    dict(name="i1: minimal (onLine empty, slotCond True)",
         q0=2, d=1, rho0=1, boxSlots=[0], onLine=[], ks=1,
         parentBlock=[], slotBlock={0: [(0, 0)]}, slotCoord={},
         slotCond=lambda rho, k, x: True,
         inStratum=lambda rho, x: True,          # member_split: True /\ True
         pin=lambda rho: 1, slot_val_exp={0: 1},
         z={}, box=[(0, 0), (0, 1)]),            # level-N box: n*N = 2 coords

    # i2 — junction ON-LINE (monicTop=false flavor): m=2 (f=[2], d=2), N=2, n=3,
    # ell=1, boxSlots={0,1}, onLine={0}=ks.  slotCond at the junction pins the
    # read to pin=1 (junction clause satisfied by ALL members); exponent 2 each
    # (s==2): blocks of size 3 with one pinned coordinate: 2^(3-1) = 4 = 2^2.
    dict(name="i2: junction on-line, read pinned to c=1",
         q0=2, d=2, rho0=1, boxSlots=[0, 1], onLine=[0], ks=0,
         parentBlock=[], slotBlock={0: [(0, 0), (0, 1), (0, 2)], 1: [(1, 0), (1, 1), (1, 2)]},
         slotCoord={0: (0, 0)},
         slotCond=lambda rho, k, x: (x((0, 0)) == 1) if k == 0 else True,
         inStratum=lambda rho, x: x((0, 0)) == 1,
         pin=lambda rho: 1, slot_val_exp={0: 2, 1: 3},
         z={0: 1}, box=[(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]),

    # i3 — SHALLOW-HEIGHT flavor (the D11c regime TD-3's call names): slot 0's
    # condition is a height floor "digit at (0,0) vanishes" (w >= gamma), so the
    # attainable read alphabet at slotCoord=(0,1) is full but the block count
    # halves; probes the attainable product, never full alphabets.
    dict(name="i3: shallow height floor (digit-vanishing condition)",
         q0=2, d=1, rho0=1, boxSlots=[0, 1], onLine=[0], ks=0,
         parentBlock=[], slotBlock={0: [(0, 0), (0, 1)], 1: [(1, 0)]},
         slotCoord={0: (0, 1)},
         slotCond=lambda rho, k, x: (x((0, 0)) == 0) if k == 0 else True,
         inStratum=lambda rho, x: x((0, 0)) == 0,
         pin=lambda rho: 1, slot_val_exp={0: 1, 1: 1},
         z={0: 1}, box=[(0, 0), (0, 1), (1, 0), (1, 1)]),
]

if __name__ == "__main__":
    lean_fail = math_fail = 0
    for inst in INSTANCES:
        verdict, ok_math = run(inst)
        lean_fail += (not verdict)
        math_fail += (not ok_math)
    print("\n================ SUMMARY ================")
    print(f"instances: {len(INSTANCES)}")
    print(f"intended MOVES D.11 finite-box product law: "
          f"{'ALL MATCH (math sound)' if math_fail == 0 else f'{math_fail} MISMATCH'}")
    print(f"landed Lean-statement DigitsProdLaw at ledgerJoint: "
          f"{f'{lean_fail}/{len(INSTANCES)} FAIL' if lean_fail else 'all hold'}")
    if lean_fail and math_fail == 0:
        print("VERDICT: STATEMENT-LEVEL FAILURE (transcription seam, not math). "
              "STOP: build the Lean countermodel; do NOT attempt the TD-3 proof.")
