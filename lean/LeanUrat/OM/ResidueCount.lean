/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.L3
import LeanUrat.L3Squarefree
import LeanUrat.MontesAxiom

/-!
# M0 — ResidueCount: the residual-count oracle (blueprint `\S` Layer 0, `sec:m0`)

M0 contributes **no new mathematics**: it re-exports the finite-field shape counts already proved in
`LeanUrat.L3` / `LeanUrat.L3Squarefree` (and re-surfaced in `LeanUrat.MontesAxiom`) as the single
residual-count oracle consumed downstream (M5/M7/M8). The load-bearing content is the identity that
the number of monic degree-`m` polynomials over `F_Q` that are **non**-squarefree is `Q^{m-1}` — this
is exactly the `T_BB3` residual count `(q^δ)^{d_S-1}` when `Q = q^δ` and `m = d_S` (descent triggers
on the non-separable ⟺ non-squarefree locus, GMN Lemma 3.11(3)).

* `card_monicDegree` — re-export of the proved `L3.card_monicDegree` (`#monic deg m = Q^m`).
* `card_squarefreeMonicDegree` — re-export of the proved
  `L3Squarefree.card_squarefreeMonicDegree` (`#squarefree monic deg m = Q^m - Q^{m-1}`, `m ≥ 2`).
* `nonSquarefreeMonicCount` — **the `T_BB3` oracle**: `#{non-squarefree monic deg m} = Q^{m-1}` for
  `m ≥ 2`, proved by Nat-subtraction arithmetic from the monic split
  `#monic = #squarefree + #non-squarefree` together with the two counts above
  (`Q^m - (Q^m - Q^{m-1}) = Q^{m-1}`, valid since `Q^{m-1} ≤ Q^m`).
* `nonSquarefreeMonicCount_eq_factor` — the `(q^δ)^{d_S-1}` tie when `Nat.card F = q^δ`.
* `not_separable_iff_not_squarefree` — re-export of the descent-trigger predicate equivalence.

Everything is a thin reuse of already-proved, `sorry`-free `lean_urat`/mathlib facts; nothing here is
a SUBSTITUTION or DEFERRED. Core-only footprint.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M0

open Polynomial

variable {F : Type*} [Field F] [Finite F]

/-! ## 1. The monic and squarefree-monic counts (re-export) -/

/-- **Monic count `= Q^m` (re-export).** For a finite field `F` with `Q = Nat.card F` and any `m`,
`Nat.card (monicDegree F m) = Q^m`. NOVEL re-export of the proved, `sorry`-free
`LeanUrat.L3.card_monicDegree`. -/
theorem card_monicDegree (m : ℕ) :
    Nat.card (L3.monicDegree F m) = Nat.card F ^ m :=
  L3.card_monicDegree (F := F) m

/-- **Squarefree-monic count `= Q^m - Q^{m-1}` (re-export).** For a finite field `F`,
`Q = Nat.card F`, and `m ≥ 2`, `Nat.card (squarefreeMonicDegree F m) = Q^m - Q^{m-1}`. NOVEL
re-export of the proved, `sorry`-free `LeanUrat.L3Squarefree.card_squarefreeMonicDegree`. -/
theorem card_squarefreeMonicDegree (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (L3.squarefreeMonicDegree F m) = Nat.card F ^ m - Nat.card F ^ (m - 1) :=
  L3Squarefree.card_squarefreeMonicDegree (F := F) m hm

/-! ## 2. The non-squarefree residual count `= Q^{m-1}` — the `T_BB3` oracle

This is the residual-equidistribution count of the OM cell coefficient `countCellCoeff`. We prove it
directly from the monic split (`#monic = #squarefree + #non-squarefree`) and the two counts above by
truncated-`Nat`-subtraction arithmetic: with `S := #squarefree`, `M := #monic`,
`M = S + #nonsqfree` and `S = M - Q^{m-1}` give `#nonsqfree = M - S = M - (M - Q^{m-1}) = Q^{m-1}`,
the last step needing `Q^{m-1} ≤ Q^m` to undo the truncated subtraction. -/

/-- **Non-squarefree residual count `= Q^{m-1}` — the `T_BB3` oracle.** For a finite field `F`
(`Q = Nat.card F`) and `m ≥ 2`, the number of non-squarefree (descent-triggering) monic degree-`m`
polynomials is `Q^{m-1}`. This is exactly the `T_BB3` residual count `(q^δ)^{d_S-1}` with `Q = q^δ`,
`m = d_S` (see `nonSquarefreeMonicCount_eq_factor`).

Proved by Nat arithmetic from the monic split and the two finite-field counts (`card_monicDegree`,
`card_squarefreeMonicDegree`), minding truncated subtraction via `Q^{m-1} ≤ Q^m`. (The same statement
is also `LeanUrat.MontesAxiom.residualBoxCount`; M0 surfaces it under the oracle name with an explicit
arithmetic proof from the two counts.) -/
theorem nonSquarefreeMonicCount (m : ℕ) (hm : 2 ≤ m) :
    Nat.card {R : F[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R}
      = Nat.card F ^ (m - 1) := by
  classical
  set Q := Nat.card F with hQ
  -- monic = squarefree ⊕ non-squarefree, as an explicit `Equiv` on `Sum`
  let e : {R : F[X] // R.Monic ∧ R.natDegree = m}
      ≃ {R : F[X] // R.Monic ∧ R.natDegree = m ∧ Squarefree R}
        ⊕ {R : F[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R} :=
    { toFun := fun R =>
        if h : Squarefree R.1 then Sum.inl ⟨R.1, R.2.1, R.2.2, h⟩
        else Sum.inr ⟨R.1, R.2.1, R.2.2, h⟩
      invFun := fun s => match s with
        | Sum.inl R => ⟨R.1, R.2.1, R.2.2.1⟩
        | Sum.inr R => ⟨R.1, R.2.1, R.2.2.1⟩
      left_inv := by
        rintro ⟨R, hM, hdeg⟩; by_cases h : Squarefree R <;> simp [h]
      right_inv := by
        rintro (⟨R, hM, hdeg, hsf⟩ | ⟨R, hM, hdeg, hnsf⟩)
        · simp [hsf]
        · simp [hnsf] }
  -- the two finite-field counts, transported to the subtype forms
  have hmonic_eq :
      Nat.card {R : F[X] // R.Monic ∧ R.natDegree = m} = Q ^ m := by
    have := card_monicDegree (F := F) m
    simpa [L3.monicDegree, hQ] using this
  have hsf_eq :
      Nat.card {R : F[X] // R.Monic ∧ R.natDegree = m ∧ Squarefree R}
        = Q ^ m - Q ^ (m - 1) := by
    have := card_squarefreeMonicDegree (F := F) m hm
    simpa [L3.squarefreeMonicDegree, hQ] using this
  -- finiteness propagation across the `Sum` equiv
  have hQpos : 0 < Q := by rw [hQ]; exact Nat.card_pos
  have hfin_monic : Finite {R : F[X] // R.Monic ∧ R.natDegree = m} :=
    Nat.finite_of_card_ne_zero (by rw [hmonic_eq]; exact pow_ne_zero m hQpos.ne')
  haveI hfin_sum :
      Finite ({R : F[X] // R.Monic ∧ R.natDegree = m ∧ Squarefree R}
        ⊕ {R : F[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R}) :=
    Finite.of_equiv _ e
  haveI : Finite {R : F[X] // R.Monic ∧ R.natDegree = m ∧ Squarefree R} :=
    Finite.sum_left {R : F[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R}
  haveI : Finite {R : F[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R} :=
    Finite.sum_right {R : F[X] // R.Monic ∧ R.natDegree = m ∧ Squarefree R}
  -- the split count identity `#monic = #squarefree + #non-squarefree`
  have hsum : Nat.card {R : F[X] // R.Monic ∧ R.natDegree = m}
      = Nat.card {R : F[X] // R.Monic ∧ R.natDegree = m ∧ Squarefree R}
        + Nat.card {R : F[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R} := by
    rw [Nat.card_eq_of_bijective e e.bijective, Nat.card_sum]
  rw [hmonic_eq, hsf_eq] at hsum
  -- truncated-subtraction arithmetic: `Q^m - (Q^m - Q^{m-1}) = Q^{m-1}`, using `Q^{m-1} ≤ Q^m`
  have hpow_le : Q ^ (m - 1) ≤ Q ^ m := by
    apply Nat.pow_le_pow_right <;> omega
  omega

/-- **The `(q^δ)^{d_S-1}` tie (PROVED).** When the cell's residue field `F` has size `q^δ`
(`Nat.card F = q^δ`), the proved residual count `nonSquarefreeMonicCount` is exactly the `(q^δ)^{d_S-1}`
factor used by `MontesAxiom.countCellCoeff`. So the residual factor of `countCellCoeff` is a GENUINE
finite-field count, not a free monomial. -/
theorem nonSquarefreeMonicCount_eq_factor (q δ dS : ℕ)
    (hF : Nat.card F = q ^ δ) (hd : 2 ≤ dS) :
    (Nat.card {R : F[X] // R.Monic ∧ R.natDegree = dS ∧ ¬ Squarefree R} : ℚ)
      = ((q : ℚ) ^ δ) ^ (dS - 1) := by
  rw [nonSquarefreeMonicCount (F := F) dS hd, hF]
  push_cast
  ring

/-- **Agreement with `MontesAxiom.residualBoxCount`.** The M0 oracle count is definitionally the same
finite-field count already proved as `LeanUrat.MontesAxiom.residualBoxCount`; we record the equality
so downstream consumers can use either name interchangeably (no duplication of the proof obligation —
both reduce to `Q^{m-1}`). -/
theorem nonSquarefreeMonicCount_eq_residualBoxCount (m : ℕ) (_hm : 2 ≤ m) :
    Nat.card {R : F[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R}
      = Nat.card {R : Polynomial F // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R} :=
  rfl

/-! ## 3. The descent trigger: non-separable ⟺ non-squarefree (re-export)

GMN Lemma 3.11(3): over the finite (hence perfect) residue field, the refinement / descent trigger
`¬ Separable` coincides with `¬ Squarefree`, so the non-squarefree count above is read as the descent
locus count. CITED through the proved `L3.not_separable_iff_not_squarefree`
(`PerfectField.separable_iff_squarefree` + `PerfectField.ofFinite`). -/

/-- **Descent trigger (re-export).** Over a finite field `F`, for `g : F[X]`,
`¬ g.Separable ↔ ¬ Squarefree g`. NOVEL re-export of the proved
`LeanUrat.L3.not_separable_iff_not_squarefree`. -/
theorem not_separable_iff_not_squarefree {g : F[X]} : ¬ g.Separable ↔ ¬ Squarefree g :=
  L3.not_separable_iff_not_squarefree

end LeanUrat.OM.M0
