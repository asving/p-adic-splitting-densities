/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H108

/-!
# Uniformity.ChapH.H113 — the drain census

**Chapter H, NODE H.113** [theorem] (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §3.2 N-2a's
`#DRAIN = Q^{(m−1)(N−1)}`, source `EFF.GENIND.08`).  Eighth node of **N-2**, the cluster event
grammar over `O`, and the recursion's HEAD leg.

* `card_drainState` — `#{c : ClusterState O m N // IsDrainState c} = q ^ ((m − 1) * (N − 1))`,
  with `q = residueCard O`.

The drain locus is the coordinate slice `a₀ = 0` (H.108's `IsDrainState`, at the inhabited
`0 < m`), so the census is H.106's census with one full coefficient's digits removed.  The proof
is a coordinate projection: writing `m = n + 1`, dropping coordinate `0` is an equivalence
`{c : ClusterState O (n+1) N // IsDrainState c} ≃ (Fin n → 𝔪 / 𝔪 ^ N)`, and H.106's
one-coordinate count `card_map_maximalIdeal` (`#(𝔪 / 𝔪 ^ N) = q ^ (N − 1)`) finishes it.
Everything is subtraction-safe: `m − 1` is never formed, only `n`.

**The head leg.**  Normalized against H.106's state census `q ^ (m (N − 1))` this is
`q ^ (−(N − 1))` EXACTLY — the battery's `P3 hhead as EQUALITY`.  The equality (not just a
bound) is reproduced in the numeric gate below.

DEPENDS: H.106 (`ClusterState`, `card_map_maximalIdeal`), H.108 (`IsDrainState`,
`isDrainState_iff`) · mathlib `Fin.cons`, `Nat.card_pi`, `Nat.card_congr`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `[Finite (ResidueField O)]` (this node counts),
every binder INLINE (the B.42 completeness-binder rule; §17 declares no section variables).
No `π`: the drain predicate is read off the class, and no uniformizer is consulted.

## TEETH (GC-8)

Battery `P1(b) drain count` of `verification/openmath/OM2_genindb_battery.py`, exhaustive over
28 cells × 2 rings:

```python
    check(f"P1(b) drain count [{cell}]", buckets['DRAIN'] == Q ** ((m - 1) * (W - 1)))
```

The theorem IS that count, proved.  The `#guard`s at the end of the file reproduce its cheap
arithmetic content at every cell of the battery's `part1` plan: the closed form agrees with the
enumeration `(q ^ (N − 1)) ^ (m − 1)` (one coefficient removed from H.106's product), and the
head-leg identity `#STATES = #DRAIN * q ^ (N − 1)` holds as an EQUALITY.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. Dropping the constant coordinate -/

/-- **The drain slice, coordinatized.**  A drain state of degree `n + 1` is exactly a free
choice of its `n` non-constant coordinates in the image ideal `𝔪 / 𝔪 ^ N`: the constant
coordinate is pinned to `0`. -/
def drainEquiv (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n N : ℕ) :
    {c : ClusterState O (n + 1) N // IsDrainState c} ≃
      ((_ : Fin n) → {x : Res O N //
        x ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}) where
  toFun c := fun i => ⟨c.1.1 i.succ, c.1.2 i.succ⟩
  invFun g :=
    ⟨⟨Fin.cons 0 (fun i => (g i).1), by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [Fin.cons_zero]
          exact Ideal.zero_mem _
        · intro j
          rw [Fin.cons_succ]
          exact (g j).2⟩, by
      intro h
      have hz : (⟨0, h⟩ : Fin (n + 1)) = 0 := rfl
      rw [hz]
      simp⟩
  left_inv c := by
    refine Subtype.ext (Subtype.ext (funext fun i => ?_))
    dsimp only
    refine Fin.cases ?_ ?_ i
    · rw [Fin.cons_zero]
      exact ((isDrainState_iff (by omega) c.1).1 c.2).symm
    · intro j
      rw [Fin.cons_succ]
  right_inv g := by
    refine funext fun i => Subtype.ext ?_
    dsimp only
    rw [Fin.cons_succ]

/-! ## 2. The census -/

/-- **H.113.**  `#DRAIN = q ^ ((m − 1) * (N − 1))`: the drain locus is the coordinate slice
`a₀ = 0`, one full coefficient's digits removed from H.106's state census. -/
theorem card_drainState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    Nat.card {c : ClusterState O m N // IsDrainState c}
      = residueCard O ^ ((m - 1) * (N - 1)) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.card_congr (drainEquiv O n N), Nat.card_pi]
  simp only [card_map_maximalIdeal hN, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Nat.add_sub_cancel]
  rw [Nat.mul_comm]

end Uniformity.Density.Induction

/-! ## 3. TEETH — the PART-1 drain inventory, reproduced

`drainCensus Q m N` is the closed form the theorem proves.  The battery enumerates the same
cell by bucket count (`buckets['DRAIN']`), whose combinatorial content is "one coordinate
pinned to zero, the other `m − 1` free in `𝔪 / 𝔪 ^ N`", i.e. `(Q ^ (N − 1)) ^ (m − 1)`.  The
plan below is the battery's own `part1` plan (its largest window per `(q, m)` row);
`clusterStateCensus` is H.106's state census, reused here for the head-leg identity. -/

section NumericDrain

/-- The drain census closed form of `card_drainState`, as a computable numeral function. -/
def drainCensus (Q m N : ℕ) : ℕ := Q ^ ((m - 1) * (N - 1))

-- battery `part1` plan: (q, m, N) at the largest window of each row
#eval [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)].map
  fun p => drainCensus p.1 p.2.1 p.2.2
  -- expect [32, 1024, 512, 81, 729, 729]

-- the bucket-count reading: one coordinate pinned, the rest free
#guard [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)].all
  fun p => drainCensus p.1 p.2.1 p.2.2 == (p.1 ^ (p.2.2 - 1)) ^ (p.2.1 - 1)

-- `P3 hhead as EQUALITY`: the head leg is `Q ^ (−(N − 1))` of the state census, exactly
#guard [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)].all
  fun p => clusterStateCensus p.1 p.2.1 p.2.2
    == drainCensus p.1 p.2.1 p.2.2 * p.1 ^ (p.2.2 - 1)

#guard (drainCensus 2 3 6, drainCensus 3 3 4) == (1024, 729)

-- the degenerate rows the theorem's binders exclude are NOT claimed: at `m = 0` the closed
-- form would read `Q ^ ((0 − 1) * (N − 1)) = Q ^ 0 = 1` in ℕ-subtraction, while every state is
-- vacuously a drain (H.108's convention), so the honest count there is the full census
#guard drainCensus 2 0 6 == 1
#guard clusterStateCensus 2 0 6 == 1

end NumericDrain

/-! ## 4. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.drainEquiv
#print axioms Uniformity.Density.Induction.card_drainState

end AxCheck
