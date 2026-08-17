/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B01
import Uniformity.ChapB.B16

/-!
# Uniformity.ChapC.C113 — Step 5, clause (i): depth strictly increases

**Chapter C, NODE C.113** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C3**.  `[signed: A-C.1; split → 2; clause (i) RE-SIGNED: A-C.5,
2026-08-16]`.

This file lands **clause (i) only**: `ht_depth_increase`, the convexity leg in cleared
argmin form — *every attained side slope of a conservative-cell member is `> s`* (C.55's
shape one level down).  Clause (ii) (`ht_leaf_certified`, the order-1 Ore certificate per
terminal side factor with the `B-BOX-1` inheritance as the inner hypothesis) is NOT here.

## The A-C.5 re-sign (why the statement differs from the A-C.1 freeze)

The A-C.1 frozen form is **machine-refuted**
(`leanfinal/Uniformity/ChapC/C113_REFUTATION.lean.txt`, `c113_clause1_frozen_false`,
Lean-core, re-run green at the repo pin 2026-08-16): its side hypothesis
`hne : (sideSet Φ G u ℓ).Nonempty` is VACUOUS — B.39b's landed `sideSet_nonempty_gen`
proves it unconditionally for every `φ, f, u, ℓ` (`suppVal` is an `inf` over a nonempty
range, hence attained) — so the frozen statement asserted `ℓ * s < u` for EVERY direction,
false already at `Φ = G = X`, `m = s = u = ℓ = 1`.  This was the THIRD occurrence of the
A-C.1 side-nonemptiness pattern (after C.111 and C.94); neither `0 < u` nor
`Nat.Coprime u ℓ` repairs it (the witness has both).

The re-signed form (A-C.5, 2026-08-16) makes the statement's own intent explicit — a
GENUINE side, one with a support point strictly below the top abscissa `m`:

* `hne` is replaced by a NAMED support point `{j : ℕ} (hj : j ∈ sideSet Φ G u ℓ)
  (hjm : j < m)`;
* the chapter's standing full-degree binder `hdeg : G.natDegree = m * Φ.natDegree`
  (already carried by `htCell` (C.108) and by C.110's `hGdeg`) is added — it is what puts
  the top abscissa `m` inside the index range of the `inf` defining `suppVal`;
* `hm : 0 < m` is redundant under `hjm` and KEPT for a minimal diff against the freeze.

The proof below transcribes `ht_depth_increase_repaired` from the refutation record — the
form the amendment certified as PROVED at signing (sorry-free, Lean-core): `suppVal ≤ u·m`
by `Finset.inf_le` at `m` + `htop`; the on-side equation at `j` gives
`ℓ·((m−j)·s + 1) + u·j ≤ u·m` in `ℕ`; with `d = m − j ≥ 1` that reads `ℓ·s·d + ℓ ≤ u·d`,
hence `ℓ·s < u`.

**NOT adopted** (recorded at the node): the alternative `2 ≤ (sideSet Φ G u ℓ).card` fence
(C.108's `IsSide` genuineness) — it needs a "development vanishes above the top" lemma that
no landed node supplies; a future re-sign preferring the `card` form must supply it.

## Blueprint position

**DEPENDS.** C.07/C.08 (argmin convexity arithmetic) · C.108 · **[A-C.5]** B.11 (`npHgt`) ·
B.16 (`OnSide`/`sideSet`/`suppVal` — the clause reads the on-side equation at the named
support point).  **SOURCE.** `EFF.W12.86` step 5 (verbatim), the convexity leg in cleared
argmin form.  Consumed by C.117 (finite depth: window-visibility bounds the depth via
`m_v·s_v + 1 ≤ P_v(0) ≤ N − 1`, so no root-to-leaf chain is infinite) and C.121 (the
finite-tree iteration).
-/

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density Uniformity.Density.Leaf Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- `hm : 0 < m` is redundant under the re-sign (it follows from `hjm : j < m`); kept by
-- A-C.5 for a minimal diff against the frozen signature.
set_option linter.unusedVariables false in
/-- **NODE C.113, clause (i) (A-C.5 re-signed form): depth strictly increases.**  On a
conservative-cell member — pins `(m−j)·s + 1` at every abscissa `j < m` (`hpins`), top vertex
at height `0` (`htop`), full degree `hdeg` — every direction `(u, ℓ)` with `ℓ > 0` whose side
has a NAMED support point `j` strictly below the top abscissa `m` satisfies `ℓ * s < u`: every
attained genuine side slope is `> s`, so an eligible `e = 1` child has `s_u ≥ s_v + 1`. -/
theorem ht_depth_increase {Φ : Polynomial O} (hΦ : IsKey Φ) {G : Polynomial O} {m s : ℕ}
    (hm : 0 < m) (hdeg : G.natDegree = m * Φ.natDegree)
    (hpins : ∀ j < m, (((m - j) * s + 1 : ℕ) : ℕ∞) ≤ npHgt Φ G j)
    (htop : npHgt Φ G m = (0 : ℕ∞))
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {j : ℕ} (hj : j ∈ sideSet Φ G u ℓ) (hjm : j < m) :
    ℓ * s < u := by
  classical
  -- the top abscissa is inside the index range of the `inf` defining `suppVal`
  have hmle : m ≤ G.natDegree := by
    rw [hdeg]; exact Nat.le_mul_of_pos_right _ hΦ.pos
  have hmem : m ∈ Finset.range (G.natDegree + 1) := Finset.mem_range.2 (by omega)
  -- so the support value is at most the value at the top, which `htop` makes `u * m`
  have hle : suppVal Φ G u ℓ ≤ ((u * m : ℕ) : ℕ∞) := by
    have h := Finset.inf_le (f := fun k => ℓ • npHgt Φ G k + ((u * k : ℕ) : ℕ∞)) hmem
    simpa [suppVal, htop] using h
  have hjon : OnSide Φ G u ℓ j := (Finset.mem_filter.mp hj).2
  set K : ℕ := (m - j) * s + 1 with hK
  have hpin : ((K : ℕ) : ℕ∞) ≤ npHgt Φ G j := hpins j hjm
  have hstep : ((ℓ * K : ℕ) : ℕ∞) ≤ ℓ • npHgt Φ G j := by
    rw [Nat.cast_mul, nsmul_eq_mul]
    gcongr
  have hchain : ((ℓ * K : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) ≤ ((u * m : ℕ) : ℕ∞) := by
    have h1 : ((ℓ * K : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞)
        ≤ ℓ • npHgt Φ G j + ((u * j : ℕ) : ℕ∞) :=
      add_le_add_left hstep (((u * j : ℕ) : ℕ∞))
    rw [hjon] at h1
    exact le_trans h1 hle
  -- everything in sight is finite, so the inequality descends to `ℕ`
  have hnat : ℓ * K + u * j ≤ u * m := by
    have hc : ((ℓ * K + u * j : ℕ) : ℕ∞) ≤ ((u * m : ℕ) : ℕ∞) := by
      rw [Nat.cast_add]; exact hchain
    exact_mod_cast hc
  have hsplit : u * m = u * j + u * (m - j) := by
    rw [← Nat.mul_add]; congr 1; omega
  have h2 : ℓ * K ≤ u * (m - j) := by
    rw [hsplit, Nat.add_comm (u * j) (u * (m - j))] at hnat
    exact Nat.add_le_add_iff_right.mp hnat
  -- `ℓ·((m−j)s + 1) = ℓ·s·(m−j) + ℓ`, and `ℓ > 0` makes the inequality strict
  have heq : ℓ * K = ℓ * s * (m - j) + ℓ := by rw [hK]; ring
  rw [heq] at h2
  exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le (Nat.lt_add_of_pos_right hℓ) h2)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_depth_increase

end AxCheck
