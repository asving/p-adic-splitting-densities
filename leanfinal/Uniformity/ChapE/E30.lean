/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Uniformity.ChapE.E30 — the realized-set arithmetic `T(k)`

**Chapter E, NODE E.30** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §6 — LEMMA HE7-L1's
combinatorial core, with the corrected thresholds), ENV-E1 (the arithmetic arena: no `O`, pure
exponent bookkeeping).

For coprime `e, h`, a residue-degree `f₁ ≥ 1`, `D′ = e·f₁`, a height `k`, and the class index
`i₀ = i₀(k) < e` (`i₀·h ≡ k (mod e)`, E.03's uniqueness at the base rung), the **reach set** is

  `T(k) := {t < f₁ : (i₀ + e·t)·h ≤ k}`   (`reachSet e h f₁ i₀ k : Finset (Fin f₁)`)

— the slots of the class that a height `k` can actually be fed from. Its three boundary clauses,
`EFF.HE7.19`'s display verbatim:

* **`reachSet_full_iff`** — `T(k)` is everything iff the DEEPEST slot reaches:
  `(i₀ + e·(f₁ − 1))·h ≤ k`. (One direction is membership of `t = f₁ − 1`, which exists because
  `1 ≤ f₁`; the other is monotonicity of `t ↦ (i₀ + e·t)·h`.)
* **`reachSet_full_of_uniform`** — the `k`-uniform sufficient bound `(D′ − 1)·h ≤ k`, via
  `i₀ ≤ e − 1 ⟹ i₀ + e(f₁ − 1) ≤ e·f₁ − 1 = D′ − 1`; this is HE7-L1's own
  `max_k (i₀(k) + e₁(f₁−1))·h = (D′−1)·h` computation, and it is exactly why the corpus can state
  a threshold that does not depend on which class `k` lands in.
* **`reachSet_empty_iff`** — `T(k)` is empty iff the SHALLOWEST slot `t = 0` fails, `k < i₀·h`
  ("If `T(k) = ∅` the height `k` is not attained at all").

The `ℕ`-subtractions `f₁ − 1` and `e·f₁ − 1` never truncate on the signed hypotheses (`1 ≤ f₁`,
and `i₀ < e` gives `1 ≤ e`, hence `1 ≤ e·f₁`); they are the corpus's own subtractions, not a
rounding.

⚠ **THE COSET CORRECTION AND THE TWO RIDERS — NOT IN THIS FILE.** The realized-set DISPLAY that
this arithmetic feeds was corrected twice: (a) the ϖ-read realized set is the COSET
`η_θ^{−q(k)}·{Σ_{t ∈ T(k)} c_t·η_θ^t : c_t ∈ F_Q, not all 0}` (HE6 PE2 F-1's external unit
factor; "both boundary clauses are twist-invariant"), and (b) the set inside the braces is the
NONZERO elements of a proper `F_Q`-linear subspace — a punctured proper subspace, NOT a
subgroup-coset (ANNEX R R5's rider; the two riders are both true, of different objects — HE7's
OPEN-CALL 2, wording only, no mathematics). E's Lean object composing (a)+(b) is **E.32's**
`realizedSet`, not anything here: this node lands the index arithmetic `T(k)` alone, and states
nothing about which field elements are realized. The sub-threshold clause is exercised by NO
sealed tooth at `q(k) ≠ 0` (the disclosed limitation of Q3's frames); E.66's gate supplies the
`q(k) ≠ 0` numeric witness (a proper `T(3) = {0}` at the `(2,3,2)` frame) and E.68 re-fires the
tables.

The signed hypothesis `hf : 1 ≤ f₁` is genuinely load-bearing in `reachSet_full_iff` and
`reachSet_empty_iff` — at `f₁ = 0` the type `Fin 0` is empty, so `reachSet = ∅ = Finset.univ`
and both `iff`s fail in one direction (e.g. `e = h = 1, i₀ = 0, k = 0, f₁ = 0` makes `T(k) = ∅`
while `¬ (k < i₀·h)`). In `reachSet_full_of_uniform` it is carried but unconsumed, since that
clause routes through `reachSet_full_iff`, which consumes it — the `f₁ = 0` case is
`Finset.univ = ∅` and true anyway (see the `linter.unusedVariables` note).

DEPENDS: E.03 (the class index `i₀`, conceptually — this node takes `i₀` as a bare argument and
never re-derives it, per the blueprint's standing "consumers take the exponents as explicit
arguments" instruction, so no import is needed) · mathlib `Finset.filter`, `Fin` arithmetic.

SOURCE: `EFF.HE7.19` (LEMMA HE7-L1: the display `T(k) := {t < f₁ : k ≥ (i₀ + e₁t)·h}`, the two
boundary clauses "it is ALL of K^× iff T(k) = {0,…,f₁−1} iff k ≥ (i₀(k) + e₁(f₁−1))·h; a
k-uniform sufficient condition is k ≥ (D′−1)h. If T(k) = ∅ the height k is not attained at
all"; the proof's threshold computation); `EFF.HE7.21` (FINDING HE7-F1's two counterexamples —
`(3,1,2)`: `k = 1` unattained; `(2,2,1)`: `k ∈ {0,1}` realise only `F_Q ⊊ K`); `EFF.T2.10` (the
T2-side fullness criteria).

TEETH: Q3 / HE7-LIFT1 (five level-1 frames, exhaustive reachable-height tables) +
HE7-T-LIFT2SHARP — this arithmetic is a Lean theorem here; the gate's `decide`d spot checks
(`leanspec/Leanspec/ChapE.lean`, E.66) run against the same `reachSet` body.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free. All four declarations report exactly the Lean-core triple
`{propext, Classical.choice, Quot.sound}` or less; no project axiom is touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- The **reach set** `T(k)` of LEMMA HE7-L1 (`EFF.HE7.19`): the slots `t < f₁` of the class
`i₀` whose floor `(i₀ + e·t)·h` is at or below the height `k`. Body verbatim from the
gate-verified leanspec stub. -/
def reachSet (e h f₁ i₀ k : ℕ) : Finset (Fin f₁) :=
  Finset.univ.filter fun t => (i₀ + e * (t : ℕ)) * h ≤ k

/-- **E.30 (i) — fullness iff the deepest slot reaches.** `T(k)` is all of `Fin f₁` exactly when
the last slot `t = f₁ − 1` clears the height. -/
theorem reachSet_full_iff {e h f₁ i₀ k : ℕ} (hf : 1 ≤ f₁) :
    reachSet e h f₁ i₀ k = Finset.univ ↔ (i₀ + e * (f₁ - 1)) * h ≤ k := by
  constructor
  · intro hfull
    have hmem : (⟨f₁ - 1, by omega⟩ : Fin f₁) ∈ reachSet e h f₁ i₀ k := by
      rw [hfull]; exact Finset.mem_univ _
    simpa [reachSet] using hmem
  · intro hk
    ext t
    simp only [reachSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    refine le_trans (Nat.mul_le_mul_right h (Nat.add_le_add_left ?_ i₀)) hk
    exact Nat.mul_le_mul_left e (by omega)

-- `hf : 1 ≤ f₁` is consumed only through `reachSet_full_iff`; the clause is true at `f₁ = 0`
-- too (`Fin 0` gives `∅ = univ`), so it is carried as the signed hypothesis, not as strength.
set_option linter.unusedVariables false in
/-- **E.30 (ii) — the `k`-uniform sufficient bound.** `(D′ − 1)·h ≤ k` with `D′ = e·f₁` forces
fullness whatever class `k` lands in, because `i₀ + e(f₁ − 1) ≤ D′ − 1` for every `i₀ < e`. -/
theorem reachSet_full_of_uniform {e h f₁ i₀ k : ℕ} (hi : i₀ < e) (hf : 1 ≤ f₁)
    (hk : (e * f₁ - 1) * h ≤ k) : reachSet e h f₁ i₀ k = Finset.univ := by
  rw [reachSet_full_iff hf]
  refine le_trans (Nat.mul_le_mul_right h ?_) hk
  -- `i₀ + e·(f₁−1) ≤ e·f₁ − 1`: HE7-L1's threshold computation, exact in `ℕ`
  have hstep : e * (f₁ - 1) + e = e * f₁ := by
    conv_rhs => rw [← Nat.sub_add_cancel hf]
    rw [Nat.mul_add, Nat.mul_one]
  have hlt : i₀ + e * (f₁ - 1) < e * f₁ := by omega
  exact Nat.le_pred_of_lt hlt

/-- **E.30 (iii) — emptiness iff the shallowest slot fails.** `T(k) = ∅` exactly when `k < i₀·h`
— "if `T(k) = ∅` the height `k` is not attained at all". -/
theorem reachSet_empty_iff {e h f₁ i₀ k : ℕ} (hf : 1 ≤ f₁) :
    reachSet e h f₁ i₀ k = ∅ ↔ k < i₀ * h := by
  constructor
  · intro hempty
    by_contra hcon
    have hcon' : i₀ * h ≤ k := Nat.le_of_not_lt hcon
    have hmem : (⟨0, by omega⟩ : Fin f₁) ∈ reachSet e h f₁ i₀ k := by
      simpa [reachSet] using hcon'
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · intro hk
    rw [Finset.eq_empty_iff_forall_notMem]
    intro t hmem
    simp only [reachSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact absurd hmem
      (not_le.mpr (lt_of_lt_of_le hk (Nat.mul_le_mul_right h (Nat.le_add_right _ _))))

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.reachSet
#print axioms Uniformity.Density.Ladder.reachSet_full_iff
#print axioms Uniformity.Density.Ladder.reachSet_full_of_uniform
#print axioms Uniformity.Density.Ladder.reachSet_empty_iff

end AxCheck
