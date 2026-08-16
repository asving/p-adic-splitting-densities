/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapC.C98 — the normalization shear, repo side

**Chapter C, NODE C.98** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §10, the
dictionary-faithfulness layer; fragile no. 4 of the A-C.1 signing order), **ENV-C5** — pure
`ℕ∞`-linear argmin arithmetic, no local base `O`, no polygon carrier.  Two definitions and one
theorem:

* `hSupp P n u ℓ = inf_{j ≤ n} (ℓ • P j + u·j)` — the abstract CLEARED support value of a
  height function `P : ℕ → ℕ∞` against the side `(u, ℓ)`.  This is C.06/C.07's `dvSupp` shape
  with the carrier abstracted away, exactly so that the shear lemma is provable once and
  reused at every dictionary row.
* `hOnSide P n u ℓ j` — abscissa `j` lies ON the `(u, ℓ)`-side: it attains the support value,
  and its height is finite (`P j ≠ ⊤`, i.e. the abscissa is actually populated).
* `shear_onesided_iff` — the SHEAR MATCH: shearing the cloud by `P ↦ P + i·c` and reading the
  side `(u, ℓ)` is the same as leaving the cloud alone and reading the side `(u + ℓ·c, ℓ)`.

## The cleared form (what "cleared" means here, and why the statement has no `ℚ`)

The corpus's affine pin-cloud map is `(j, y) ↦ (j, y/e(µ₁) + j·w₂)`, which leaves the
rationals in the statement.  Multiplying the height coordinate through by `e(µ₁)` clears it to
`(j, y) ↦ (j, y + j·w₂·e(µ₁))`, i.e. to `P ↦ fun i => P i + i·c` with `c := w₂·e(µ₁) : ℕ`.
That is the form signed at A-C.1 and transcribed here; the slopes read off it are the cleared
slopes (`u/ℓ`), so the corpus's `λ₂ = 1/4` appears as the cleared `u/ℓ = 1/2`.

## Strength: POINTWISE, not just at the endpoints

The signed statement is the per-`j` iff (`argmin`-pointwise: `j` is on the sheared side iff it
is on the matched unsheared side), which is the strong reusable form.  The STATEMENT's
one-sidedness equivalence — "the whole cloud is one-sided at `κ₂` iff the sheared cloud is
one-sided at the corresponding slope" — is its two-endpoint instance, obtained by applying the
theorem at `j = 0` and at `j = n`; no separate declaration is needed for it.

The proof is termwise and needs neither `0 < ℓ` nor `j ≤ n`: the shear is an equality of the
two objective functions abscissa by abscissa,

    ℓ • (P i + i·c) + u·i  =  ℓ • P i + (u + ℓ·c)·i,

so the two infima are literally the same element of `ℕ∞` and the two attainment predicates are
the same proposition.  Both hypotheses are nevertheless kept: the signature is A-C.1-signed and
frozen (statement fence), and dropping them would be a strengthening the fleet is not
authorized to make.

## Witness (the audited row, `EFF.GENTOW2.06`)

`κ₂ = 5/2 ↔ λ₂ = 1/4` at the pins `(4,0), (2,7), (0,10)`, cleared shear `c = 2`
(`e(µ₁) = 2`, `w₂ = 1`): the sheared pins are `(4,8), (2,11), (0,10)` — the corpus's
`(4,4), (2,11/2), (0,5)` doubled.  Unsheared at `(u, ℓ) = (5, 2)` (slope `5/2`) the objective
reads `20, 24, 20`; sheared at `(u, ℓ) = (1, 2)` (cleared slope `1/2`, corpus `1/4`) it reads
`20, 24, 20` — the same list, one-sided with both endpoints on the side, matching
`u + ℓ·c = 1 + 2·2 = 5`.  Checked below as `example`s.

## Scope: what is cited, not proved

The FGMN-side gloss *"the sheared cloud IS `N₂(Φ₃)`"* is C.92-interface documentation (FGMN
Lemma 2.4) and is **cited, not proved**: nothing in this file mentions the FGMN side.  Both
sides of the iff live in C's own carriers.

**DEPENDS.** C.06/C.07 (the argmin carriers — by shape only; the signed signature is
carrier-free, so this file imports no chapter-C module).

**PROOF.** The affine map preserves the argmin comparisons termwise; the residual arithmetic is
`ring` after `push_cast` (the blueprint's "`omega` after clearing", at the `ℕ∞` carrier the
signature actually uses).

**SOURCE.** `EFF.GENTOW2.06` (verbatim, incl. the exact witness audit and the FGMN Lemma 2.4
gloss — the gloss stays a docstring cite).

**TEETH.** P-W1/W2/N1/N2 + TOOTH T1 (a floor-breaching recipe must come back NOT one-sided) →
retained at the numeric gates; the pointwise form above is what those gates read.

**ENVIRONMENT.** ENV-C5.

## Status

Sorry-free, axiom-free (Lean core only).  The `leanspec` twin carries this node as an `axiom`
(the standing stub lifecycle); it lands here PROVED, at the signed signature verbatim.
-/

namespace Uniformity.Density.Tower

/-- The abstract cleared support value of a height function on `[0, n]` (C.06/C.07's shape,
carrier-free): `inf_{j ≤ n} (ℓ • P j + u·j)`. -/
noncomputable def hSupp (P : ℕ → ℕ∞) (n u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (n + 1)).inf fun j => ℓ • P j + (u * j : ℕ∞)

/-- Membership of abscissa `j` in the `(u, ℓ)`-side of the abstract cloud: `j` attains the
support value, and `j` is populated (`P j ≠ ⊤`). -/
def hOnSide (P : ℕ → ℕ∞) (n u ℓ j : ℕ) : Prop :=
  hSupp P n u ℓ = ℓ • P j + (u * j : ℕ∞) ∧ P j ≠ ⊤

/-- The shear, termwise: the sheared objective at side `(u, ℓ)` IS the unsheared objective at
side `(u + ℓc, ℓ)`, abscissa by abscissa.  This is the whole content of C.98. -/
private theorem shear_objective (P : ℕ → ℕ∞) (c u ℓ i : ℕ) :
    ℓ • (P i + (i * c : ℕ∞)) + (u * i : ℕ∞)
      = ℓ • P i + (((u + ℓ * c : ℕ) : ℕ∞) * (i : ℕ∞)) := by
  rw [smul_add, add_assoc]
  congr 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

set_option linter.unusedVariables false in
/-- **NODE C.98 — `shear_onesided_iff`** (A-C.1-signed signature, verbatim).  The cleared
affine shear `P ↦ fun i => P i + i·c` matches the `(u, ℓ)`-side of the sheared cloud with the
`(u + ℓ·c, ℓ)`-side of the unsheared cloud, POINTWISE in the abscissa `j`.  The hypotheses
`0 < ℓ` and `j ≤ n` are part of the frozen signature and are not consumed by the proof (the
match is a termwise identity of objectives, valid at every `ℓ` and every `j`). -/
theorem shear_onesided_iff (P : ℕ → ℕ∞) (n c u ℓ j : ℕ) (hℓ : 0 < ℓ) (hj : j ≤ n) :
    hOnSide (fun i => P i + (i * c : ℕ∞)) n u ℓ j ↔ hOnSide P n (u + ℓ * c) ℓ j := by
  have hsupp : hSupp (fun i => P i + (i * c : ℕ∞)) n u ℓ = hSupp P n (u + ℓ * c) ℓ := by
    simp only [hSupp]
    exact Finset.inf_congr rfl fun i _ => shear_objective P c u ℓ i
  have htop : P j + (j * c : ℕ∞) ≠ ⊤ ↔ P j ≠ ⊤ := by
    rcases eq_or_ne (P j) ⊤ with h | h
    · simp [h]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
      have hcast : P j + (j * c : ℕ∞) = ((m + j * c : ℕ) : ℕ∞) := by
        rw [← hm]; push_cast; ring
      rw [hcast]
      exact iff_of_true (ENat.coe_ne_top _) h
  simp only [hOnSide, hsupp, shear_objective P c u ℓ j, htop]

end Uniformity.Density.Tower

/-! ## The audited witness row (`EFF.GENTOW2.06`)

`P` is the pin cloud `(0,10), (2,7), (4,0)` with the odd abscissae unpopulated (`⊤`); the
cleared shear is `c = 2`.  The two objective lists agree, so the matched sides carry the same
one-sidedness — the `κ₂ = 5/2 ↔ λ₂ = 1/4` row, cleared. -/

namespace Uniformity.Density.Tower

/-- the witness cloud of `EFF.GENTOW2.06`. -/
private def witP : ℕ → ℕ∞
  | 0 => 10
  | 2 => 7
  | 4 => 0
  | _ => ⊤

-- the unsheared objective at the side `(5, 2)`, slope `5/2`: `20, 24, 20` on the pins.
example : (2 : ℕ) • witP 0 + (5 * 0 : ℕ∞) = 20 := by norm_num [witP]
example : (2 : ℕ) • witP 2 + (5 * 2 : ℕ∞) = 24 := by norm_num [witP]
example : (2 : ℕ) • witP 4 + (5 * 4 : ℕ∞) = 20 := by norm_num [witP]

-- the sheared objective at the side `(1, 2)`, cleared slope `1/2` (corpus `λ₂ = 1/4`): the
-- SAME list, as `u + ℓ·c = 1 + 2·2 = 5` predicts.
example : (2 : ℕ) • (witP 0 + (0 * 2 : ℕ∞)) + (1 * 0 : ℕ∞) = 20 := by norm_num [witP]
example : (2 : ℕ) • (witP 2 + (2 * 2 : ℕ∞)) + (1 * 2 : ℕ∞) = 24 := by norm_num [witP]
example : (2 : ℕ) • (witP 4 + (4 * 2 : ℕ∞)) + (1 * 4 : ℕ∞) = 20 := by norm_num [witP]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.hSupp
#print axioms Uniformity.Density.Tower.hOnSide
#print axioms Uniformity.Density.Tower.shear_onesided_iff

end AxCheck
