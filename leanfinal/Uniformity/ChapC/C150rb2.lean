/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C98

/-!
# Uniformity.ChapC.C150rb2 — READY batch 2: pure/near-pure arithmetic wraps

Unit RB2. Lands four names from `runs/wave-b/verdict_CCUR.md`'s "Batch 2 — pure arithmetic,
zero chapter-C vocabulary" list:

* `window_consultation` (C.58) — a modular-arithmetic `ℕ` inequality.
* `level3_dead_at_mult2_three` (C.49) — a `ℕ` contradiction from a product floor exceeding a
  ceiling.
* `tower_termination_instance` (C.49) — a halving-floor `Fin`-indexed sequence forces a
  length-1 window.
* `gentow5_selffeed` (C.91, clauses (d)+(e)) — see the "Finding" section below: **the naked
  leanspec signature is FALSE**; landed here as a refutation plus the repaired form.

## Finding: `gentow5_selffeed`'s naked signature is refuted

The leanspec axiom (`blueprint/CHAP-C_tower_grammar.md` NODE C.91, `leanspec/Leanspec/ChapC.lean`
line 3888) omits the hypothesis `j < μ`. Without it, the endpoint `j = μ` is a legal
instantiation of `hOnSide`, and taking `u = 0` makes `hOnSide P μ 0 ℓ μ` hold **trivially**
for any `P` satisfying `hpins`/`htop` (since `P μ = 0` forces the objective at `j = μ` down to
`0`, which is also a lower bound for every other term once `u = 0`). The conclusion `ℓ * E < u`
then reads `ℓ * E < 0`, impossible in `ℕ`. `gentow5_selffeed_false` below exhibits this at the
smallest instance (`μ = 1`, `E = 0`, `u = 0`, `ℓ = 1`, `j = 1`).

The mathematical content the blueprint actually describes ("the induction feeds itself" — every
*interior* side of the level-`(i+1)` polygon has slope `> E_{i+1}`) is exactly the `j < μ` case,
which **is** true: `gentow5_selffeed_resigned` proves it, by the two-step telescoping argument
the blueprint's PROOF field names ("two-line convexity + floor-chain telescoping"): the point
`μ` is always in the support range with objective value `u * μ` (since `P μ = 0`), so
`hSupp ≤ u * μ`; combined with `hside`'s exact value at `j` and `hpins`'s floor
`P j ≥ (μ - j) * E + 1`, cancelling the common `u * j` term yields `ℓ * ((μ-j)*E+1) ≤ u*(μ-j)`,
i.e. `d * (ℓ*E) < d * u` for `d := μ - j > 0`, which cancels to `ℓ*E < u`.

Per this repo's standing statement-change authority (honest repairs proceed without per-item
sign-off; no fake axioms, no contradictions introduced), this is a same-shape repair to the
`blockDeg_eq`/`towerLocus_fibration` family already in the corpus (`C64.lean`, `C53b.lean`):
the naked name is refuted under its own name, and the true content is landed under a
`_resigned` name with the missing hypothesis restored. **Neither the naked `gentow5_selffeed`
statement nor a weakened substitute is claimed true** — this file proves no theorem under the
exact name `gentow5_selffeed`.

## Status

Sorry-free, axiom-free (Lean core only) throughout.
-/

namespace Uniformity.Density.Tower

/-! ### NODE C.58 — `window_consultation`: the mod-`d` residue-consultation inequality -/

/-- **NODE C.58 — `window_consultation`** (leanspec-signed, verbatim). If `m < d*N` and `m`,
`w` agree mod `d` with `w < d`, then `m` sits inside the last window `[d*(N-1), d*(N-1)+w]`. -/
theorem window_consultation (d N m w : ℕ) (hd : 0 < d) (hw : w < d) (hm : m < d * N)
    (hcong : m % d = w % d) : m ≤ d * (N - 1) + w := by
  have hwmod : w % d = w := Nat.mod_eq_of_lt hw
  have hmw : m % d = w := hcong.trans hwmod
  have hdm := Nat.div_add_mod m d
  have hlt : m / d < N := by
    by_contra h
    push_neg at h
    have hge : d * N ≤ d * (m / d) := Nat.mul_le_mul_left d h
    omega
  have hle : m / d ≤ N - 1 := by omega
  have hfinal : d * (m / d) ≤ d * (N - 1) := Nat.mul_le_mul_left d hle
  omega

/-! ### NODE C.49 (i) — `level3_dead_at_mult2_three`: the depth-3 mult-floor contradiction -/

/-- **NODE C.49 — `level3_dead_at_mult2_three`** (leanspec-signed, verbatim). At `μ₂ = 3`, a
depth-3 multiplicity `mr ≥ 2` times a jump `ℓ₃*d₃ ≥ 2` already exceeds any ceiling `L ≤ μ₂`. -/
theorem level3_dead_at_mult2_three (mr ℓ₃ d₃ L μ₂ : ℕ) (hμ : μ₂ = 3) (hm : 2 ≤ mr)
    (hjump : 2 ≤ ℓ₃ * d₃) (hL : mr * (ℓ₃ * d₃) ≤ L) (hLμ : L ≤ μ₂) : False := by
  have h4 : 2 * 2 ≤ mr * (ℓ₃ * d₃) := Nat.mul_le_mul hm hjump
  omega

/-! ### NODE C.49 (ii) — `tower_termination_instance`: the halving-floor length bound -/

/-- **NODE C.49 — `tower_termination_instance`** (leanspec-signed, verbatim). A sequence
`a : Fin (J+1) → ℕ` starting at `≤ 6`, floored below by `4` everywhere, and halving (times two)
at each step, can take at most one step: `J = 0`. -/
theorem tower_termination_instance (J : ℕ) (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ 6)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) : J = 0 := by
  by_contra hJ
  have hJpos : 0 < J := Nat.pos_of_ne_zero hJ
  set j0 : Fin J := ⟨0, hJpos⟩ with hj0
  have hd := hdrop j0
  have hf := hfloor j0.succ
  have hcast : (j0.castSucc : Fin (J + 1)) = (0 : Fin (J + 1)) := by
    apply Fin.ext
    simp [hj0, Fin.castSucc]
  rw [hcast] at hd
  omega

/-! ### NODE C.91 — `gentow5_selffeed`: naked form REFUTED, repaired form landed -/

/-- The naked leanspec statement of `gentow5_selffeed`, as a `Prop`, so it can be named and
refuted rather than silently skipped. -/
def Gentow5SelffeedStatement : Prop :=
  ∀ (P : ℕ → ℕ∞) (μ E : ℕ), 0 < μ →
    (∀ j < μ, (((μ - j) * E + 1 : ℕ) : ℕ∞) ≤ P j) → P μ = (0 : ℕ∞) →
    ∀ {u ℓ j : ℕ}, 0 < ℓ → hOnSide P μ u ℓ j → ℓ * E < u

/-- the smallest witness cloud: `P 0 = 1`, `P n = 0` otherwise. -/
private def selffeedWitP : ℕ → ℕ∞
  | 0 => 1
  | _ => 0

theorem gentow5_selffeed_false : ¬ Gentow5SelffeedStatement := by
  intro h
  have hside : hOnSide selffeedWitP 1 0 1 1 := by
    constructor
    · show hSupp selffeedWitP 1 0 1 = _
      rfl
    · simp [selffeedWitP]
  have := h selffeedWitP 1 0 (by norm_num)
    (by intro j hj; interval_cases j; simp [selffeedWitP])
    (by simp [selffeedWitP])
    (u := 0) (ℓ := 1) (j := 1) (by norm_num) hside
  omega

/-- **The repaired `gentow5_selffeed`**: with the missing `j < μ` hypothesis restored (the
side must be an INTERIOR side of the polygon, not the trivial endpoint at `μ` itself), the
signed conclusion holds — this is the honest content of leanspec clause (e), "the induction
feeds itself". -/
theorem gentow5_selffeed_resigned (P : ℕ → ℕ∞) (μ E : ℕ) (hμ : 0 < μ)
    (hpins : ∀ j < μ, (((μ - j) * E + 1 : ℕ) : ℕ∞) ≤ P j) (htop : P μ = (0 : ℕ∞))
    {u ℓ j : ℕ} (hℓ : 0 < ℓ) (hj : j < μ) (hside : hOnSide P μ u ℓ j) :
    ℓ * E < u := by
  obtain ⟨hEq, hPjTop⟩ := hside
  have hmem : μ ∈ Finset.range (μ + 1) := Finset.mem_range.mpr (Nat.lt_succ_self μ)
  have hle : hSupp P μ u ℓ ≤ ℓ • P μ + (u * μ : ℕ∞) := Finset.inf_le hmem
  rw [htop, smul_zero, zero_add] at hle
  rw [hEq] at hle
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hPjTop
  have hcast1 : ℓ • P j + (u * j : ℕ∞) = ((ℓ * m + u * j : ℕ) : ℕ∞) := by
    rw [← hm]; push_cast; ring
  rw [hcast1] at hle
  have hle_nat : ℓ * m + u * j ≤ u * μ := by exact_mod_cast hle
  have hfloor := hpins j hj
  rw [← hm] at hfloor
  have hfloor_nat : (μ - j) * E + 1 ≤ m := by exact_mod_cast hfloor
  set d := μ - j with hd_def
  have hμeq : μ = j + d := by omega
  have hdpos : 0 < d := by omega
  have heq : u * μ = u * j + u * d := by rw [hμeq]; ring
  have hstep1 : ℓ * m ≤ u * d := by omega
  have hstep2 : ℓ * (d * E + 1) ≤ ℓ * m := Nat.mul_le_mul_left ℓ hfloor_nat
  have hexpand : ℓ * (d * E + 1) = ℓ * d * E + ℓ := by ring
  rw [hexpand] at hstep2
  have hstep3 : ℓ * d * E + ℓ ≤ u * d := by omega
  by_contra hc
  push_neg at hc
  have hstep4 : u * d ≤ ℓ * E * d := Nat.mul_le_mul_right d hc
  have hcomm : ℓ * E * d = ℓ * d * E := by ring
  rw [hcomm] at hstep4
  omega

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.window_consultation
#print axioms Uniformity.Density.Tower.level3_dead_at_mult2_three
#print axioms Uniformity.Density.Tower.tower_termination_instance
#print axioms Uniformity.Density.Tower.Gentow5SelffeedStatement
#print axioms Uniformity.Density.Tower.gentow5_selffeed_false
#print axioms Uniformity.Density.Tower.gentow5_selffeed_resigned

end AxCheck
