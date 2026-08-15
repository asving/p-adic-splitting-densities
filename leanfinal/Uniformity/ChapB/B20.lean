/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B17
import Uniformity.ChapB.B18

/-!
# Uniformity.ChapB.B20 — the side's numerical data

**Chapter B, NODE B.20** [def] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

*The side's numerical data.*  For `0 < ℓ` and `Nat.Coprime u ℓ`, with `suppVal φ f u ℓ ≠ ⊤`,
the side of slope `−u/ℓ` has **left endpoint** `sideMin := (sideSet φ f u ℓ).min'`, **right
endpoint** `sideMax := (sideSet φ f u ℓ).max'`, **length** `sideMax − sideMin`, and **residual
degree** `sideDeg := (sideMax − sideMin) / ℓ`.  By B.17, `ℓ ∣ sideMax − sideMin`, so the length
is `ℓ * sideDeg` exactly (`sideMax_eq`); and every on-side abscissa is one of the lattice
points `sideMin + ℓ*k`, `k ≤ sideDeg` (`onSide_eq_add_mul`).

Five public declarations, three of them definitions.  Kept in **one file**, per the node's own
instruction: this is one *object* (the side's numerical data) and splitting it would force
every consumer to import three modules for one triple.  (The sanctioned split boundary, if the
merge queue ever objects, is `{sideMin, sideMax, sideDeg}` in `B20a.lean` and
`{sideMax_eq, onSide_eq_add_mul}` in `B20b.lean`.)

One non-signed auxiliary is added: `onSide_of_mem_sideSet`, the projection of B.16's
`sideSet` membership onto the `OnSide` predicate, used four times below.

Signed binders: `{ℓ u : ℕ}` on both theorems is the blueprint's `[repaired: A-F.3/B-D16]`
form — `ℓ` and `u` had no binder in the pre-repair text and survived only through
`autoImplicit`; the explicit binders are written in Lean's first-occurrence auto-bind order,
so the elaborated types are unchanged.

DEPENDS: B.16 (`OnSide`, `sideSet`) · B.17 (`onSide_modEq`) · B.18 (`sideSet_nonempty`, the
supplier of the `Nonempty` argument at every consumer) · mathlib `Finset.min'_mem`,
`Finset.max'_mem`, `Finset.min'_le`, `Finset.le_max'`, `Nat.modEq_iff_dvd'`,
`Nat.mul_div_cancel'`, `Nat.add_sub_cancel'`, `Nat.div_le_div_right`.

**PROOF.**
1. `sideMax_eq`: `sideMin ≤ sideMax` (both are members, `Finset.min'_le` at `sideMax`), and
   `ℓ ∣ (sideMax − sideMin)` by B.17 applied to the two members `sideMin`, `sideMax` (both are
   in `sideSet`, hence `OnSide`), so `Nat.mul_div_cancel'` and `Nat.add_sub_cancel'` give the
   identity.
2. `onSide_eq_add_mul`: for `j ∈ sideSet`, `sideMin ≤ j ≤ sideMax`, and `ℓ ∣ (j − sideMin)` by
   B.17; set `k := (j − sideMin)/ℓ`; then `j = sideMin + ℓ*k` by `Nat.mul_div_cancel'`, and
   `k ≤ sideDeg` from `j ≤ sideMax` by monotonicity of `Nat` division.

## Fragility note (blueprint §12 rule 6, in force)

All three definitions carry the dependent `Nonempty` argument `h` in their *type*, so a
consumer must keep one and the same proof term `h` in play across a chain of rewrites.  This
is deliberate — `min'`/`max'` have no junk value — and is why B.18's `sideSet_nonempty` is a
named lemma rather than an inline `by` block at each site.

## FAITHFULNESS (blueprint, verbatim in force) — **flagged for human review**

`EFF.HE3.13` verbatim: *"each side has a `dv`-slope `λ = u/ℓ` in lowest terms (`u, ℓ > 0`),
horizontal length `L_λ = ℓ·d_λ`, and a residual polynomial `R_λ ∈ K[Z]` of degree `d_λ`"* —
the length `sideMax − sideMin` is `L_λ` and `sideDeg` is `d_λ`.  `EFF.HE3.14` verbatim: *"the
side of `P(F)` with slope `λ = u/ℓ` in lowest terms, left endpoint `(j₀, κ₀)`, lattice
abscissas `j₀ + ℓk` (`k = 0, …, d_λ`)"* — `sideMin` is `j₀`, and `suppVal` is `ℓκ₀ + u j₀`.
`L_v` of `EFF.W12.83` (*"`L_v = #{j < m_v : P_v(j) ∈ ℤ}`"*, the "priced digits") is the
**count** `(sideSet φ f u ℓ).card`, which is `≤ sideDeg + 1` and equals it exactly when every
on-side lattice abscissa carries a point; the count is chapter C/H's object and the inequality
is all this chapter needs.

SOURCE: `EFF.HE3.13`; `EFF.HE3.14`; `EFF.W12.83`; `EFF.HE6.10`.

TEETH: `W12-SHAPE` (`EFF.W12.54`, 23 rows, both directions — every row is a
`(polygon, residual, count, σ)` tuple keyed by exactly this data) → executable regression
retained (not discharged here).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.20 (a) — the side's left endpoint.**  The smallest on-side abscissa; `EFF.HE3.14`'s
`j₀`.  The `Nonempty` argument is `Finset.min'`'s and is supplied by B.18's
`sideSet_nonempty`. -/
noncomputable def sideMin (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideSet φ f u ℓ).min' h

/-- **B.20 (b) — the side's right endpoint.**  The largest on-side abscissa. -/
noncomputable def sideMax (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideSet φ f u ℓ).max' h

/-- **B.20 (c) — the side's residual degree.**  `EFF.HE3.13`'s `d_λ`: the horizontal length
`L_λ = sideMax − sideMin` divided by `ℓ`.  The division is exact by B.17 (`sideMax_eq`), so
the `Nat` truncation below is never used. -/
noncomputable def sideDeg (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideMax φ f u ℓ h - sideMin φ f u ℓ h) / ℓ

/-- **B.20, auxiliary (not a signed node statement).**  Membership in B.16's `sideSet`
projects onto the `OnSide` predicate.  `sideSet` is a `Finset.filter` over
`Finset.range (f.natDegree + 1)` with `Classical` decidability, so this is `Finset.mem_filter`
modulo that instance. -/
theorem onSide_of_mem_sideSet {φ f : Polynomial O} {u ℓ j : ℕ} (hj : j ∈ sideSet φ f u ℓ) :
    OnSide φ f u ℓ j := by
  classical
  have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
  exact (Finset.mem_filter.mp hj').2

/-- **B.20 (d) — the side's length is `ℓ * sideDeg` exactly.**  The `Nat` division defining
`sideDeg` is exact, because B.17 makes `ℓ` divide `sideMax − sideMin`. -/
theorem sideMax_eq {ℓ u : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) :
    sideMax φ f u ℓ h = sideMin φ f u ℓ h + ℓ * sideDeg φ f u ℓ h := by
  have hmin : sideMin φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.min'_mem _ _
  have hmax : sideMax φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.max'_mem _ _
  have hle : sideMin φ f u ℓ h ≤ sideMax φ f u ℓ h := Finset.min'_le _ _ hmax
  have hdvd : ℓ ∣ sideMax φ f u ℓ h - sideMin φ f u ℓ h :=
    (Nat.modEq_iff_dvd' hle).mp
      (onSide_modEq hℓ hcop htop (onSide_of_mem_sideSet hmin) (onSide_of_mem_sideSet hmax))
  rw [sideDeg, Nat.mul_div_cancel' hdvd, Nat.add_sub_cancel' hle]

/-- **B.20 (e) — the on-side abscissae are the lattice points `sideMin + ℓ*k`.**  `EFF.HE3.14`
verbatim: *"lattice abscissas `j₀ + ℓk` (`k = 0, …, d_λ`)"*. -/
theorem onSide_eq_add_mul {ℓ u : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {j : ℕ}
    (hj : j ∈ sideSet φ f u ℓ) :
    ∃ k ≤ sideDeg φ f u ℓ h, j = sideMin φ f u ℓ h + ℓ * k := by
  have hmin : sideMin φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.min'_mem _ _
  have hminle : sideMin φ f u ℓ h ≤ j := Finset.min'_le _ _ hj
  have hjmax : j ≤ sideMax φ f u ℓ h := Finset.le_max' _ _ hj
  have hdvd : ℓ ∣ j - sideMin φ f u ℓ h :=
    (Nat.modEq_iff_dvd' hminle).mp
      (onSide_modEq hℓ hcop htop (onSide_of_mem_sideSet hmin) (onSide_of_mem_sideSet hj))
  refine ⟨(j - sideMin φ f u ℓ h) / ℓ, ?_, ?_⟩
  · exact Nat.div_le_div_right (Nat.sub_le_sub_right hjmax _)
  · rw [Nat.mul_div_cancel' hdvd, Nat.add_sub_cancel' hminle]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.sideMin
#print axioms Uniformity.Density.Leaf.sideMax
#print axioms Uniformity.Density.Leaf.sideDeg
#print axioms Uniformity.Density.Leaf.onSide_of_mem_sideSet
#print axioms Uniformity.Density.Leaf.sideMax_eq
#print axioms Uniformity.Density.Leaf.onSide_eq_add_mul
end AxCheck
