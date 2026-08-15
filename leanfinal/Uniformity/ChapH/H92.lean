/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H92 — the `(CS-2)` bracket at the two quartic genres

**Chapter H, NODE H.92** (`blueprint/CHAP-H_general_induction.md` §12; source `EFF.GENH4.26`,
§S6.2). *The `(CS-2)` bracket at the two quartic genres, and the `GENIND`-normalization
reconciliation.* Three clauses:

* **(i) the subset-sum identity.** `∑_{H ⊆ D} L^{|H|} = (1 + L)^{|D|}` for a `Finset D` — the
  aggregation of §S6.1 over histories at a fixed leaf, `∏_{ladder points below the leaf}(1 + L_G)`.
* **(ii) genre E at `L = q − 1`.** `(1 + (q−1))^δ = q^δ`, with the interior points telescoping:
  `1 + ∑_{j=1}^{δ} (q−1)·q^{j−1} = q^δ` (the last step carries the `(q−1)`).
* **(iii) genre F at `L = q² − 1`.** `(1 + (q²−1))^μ = (q²)^μ`, and the macroscopic rate agreement
  `q^{2·Δμ} = (q²)^{Δμ}`.

One macroscopic rate `q^{e₁f₁·Δμ} = q^{deg φ₂·Δμ}`, two microscopic mechanisms (density versus
alphabet) — `QSCOUT22`'s S8 paragraph, here a theorem.

**⚠ THE `GENIND-5` COMPARISON IS A SHAPE MATCH, NOT A CONSUMPTION.** `EFF.GENH4.12`'s audit: at
genre E, `GENH4`'s `(q−1)q^{δ−1}` at `δ = 2μ` **is** `GENIND`'s mass form `(q−1)q^{2μ−1}`; at genre
F, `GENIND`'s mass form `(q²−1)(q²)^{2μ−1}` differs from `GENH4`'s `(q²−1)(q²)^{μ−1}` by exactly
`(q²)^μ`, *the ghost* — the declared normalization difference, not an error.  Chapter H's
`StageInterface.hbracket` is the **mass** form (H.09), so a genre-F instance must supply the ghost
factor; H.21 is the reconciliation check.  Nothing in this node consumes `GENIND-5`.

**ARITHMETIC AUDIT (recomputed fresh).** Clause (ii) at `q = 2`, `δ = 3`: `1 + (1 + 2 + 4) = 8 = 2³`;
at `q = 3`, `δ = 3`: `1 + (2 + 6 + 18) = 27 = 3³` — the `q = 3` cell, where the `(q−1)` factor is `2`
and the telescope is a genuine geometric sum.  Clause (iii) at `q = 2`, `Δμ = 2`: `2⁴ = 16 = (2²)²`.
Clause (i) at `|D| = 3`, `L = 2`: `1 + 3·2 + 3·4 + 8 = 27 = 3³`.  The last three are landed below as
`decide`-checked audit cells.

DEPENDS: H.45 · mathlib `Finset.prod_add`, `pow_mul`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.92 (i).** The subset-sum identity behind §S6.2's aggregation over histories at a fixed
leaf: summing `L^{|H|}` over all subsets of the ladder `D` is the product of `(1 + L)` over the
ladder points. -/
theorem subset_sum_pow {ι : Type*} [DecidableEq ι] (D : Finset ι) (L : ℕ) :
    ∑ H ∈ D.powerset, L ^ H.card = (1 + L) ^ D.card := by
  have h := Finset.prod_add (fun _ : ι => L) (fun _ : ι => (1 : ℕ)) D
  simpa [Finset.prod_const, add_comm] using h.symm

/-- **NODE H.92 (ii).** The genre-E telescope: the interior ladder points contribute
`(q−1)·q^{j}` each and collapse to the single power `q^δ` (the `1` is the empty history). -/
theorem bracket_telescope_E (q δ : ℕ) (hq : 1 ≤ q) :
    1 + ∑ j ∈ Finset.range δ, (q - 1) * q ^ j = q ^ δ := by
  induction δ with
  | zero => simp
  | succ d ih =>
    have hq1 : 1 + (q - 1) = q := by omega
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ih, pow_succ]
    calc q ^ d + (q - 1) * q ^ d = (1 + (q - 1)) * q ^ d := by ring
      _ = q * q ^ d := by rw [hq1]
      _ = q ^ d * q := by ring

/-- **NODE H.92 (iii).** The macroscopic rate agreement: the genre-E reading `q^{e₁f₁·Δμ}` with
`e₁f₁ = 2` and the genre-F reading `(q²)^{Δμ}` are the same rate. -/
theorem macroscopic_rate (q Δ μ : ℕ) : q ^ (2 * (Δ * μ)) = (q ^ 2) ^ (Δ * μ) :=
  pow_mul q 2 (Δ * μ)

/-! ## Audit cells (the recomputed arithmetic of the ⚠ note) -/

/-- Audit cell: clause (ii) at `q = 3`, `δ = 3` — `1 + (2 + 6 + 18) = 27 = 3³`. -/
theorem bracket_telescope_E_three_three :
    1 + ∑ j ∈ Finset.range 3, (3 - 1) * 3 ^ j = 27 := by decide

/-- Audit cell: clause (ii) at `q = 2`, `δ = 3` — `1 + (1 + 2 + 4) = 8 = 2³`. -/
theorem bracket_telescope_E_two_three :
    1 + ∑ j ∈ Finset.range 3, (2 - 1) * 2 ^ j = 8 := by decide

/-- Audit cell: clause (i) at `|D| = 3`, `L = 2` — `∑_{H ⊆ D} 2^{|H|} = 27 = 3³`. -/
theorem subset_sum_pow_three_two :
    ∑ H ∈ (Finset.range 3).powerset, 2 ^ H.card = 27 := by decide

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.subset_sum_pow
#print axioms Uniformity.Density.Induction.bracket_telescope_E
#print axioms Uniformity.Density.Induction.macroscopic_rate
#print axioms Uniformity.Density.Induction.bracket_telescope_E_three_three
#print axioms Uniformity.Density.Induction.bracket_telescope_E_two_three
#print axioms Uniformity.Density.Induction.subset_sum_pow_three_two

end AxCheck
