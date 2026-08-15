/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B15
import Uniformity.ChapB.B20

/-!
# Uniformity.ChapB.B70 — the development is scale-covariant at `φ = X`

**Chapter B, NODE B.70** (`blueprint/CHAP-B_leaf_layer.md` §11), ENV-A′. Two signed
declarations (`npHgt_scaleRoots` = B.70a, `sideSet_scaleRoots` = B.70b) and one auxiliary.

*Scaling the roots shears the polygon.* For `f` monic of degree `n` and `w : ℕ`:

* **B.70a** `npHgt X (f.scaleRoots (π ^ w)) j = npHgt X f j + w * (n - j)` — every polygon
  height is raised by `w` times its distance to the right endpoint, i.e. the `X`-adic Newton
  polygon of `f.scaleRoots (π ^ w)` is the polygon of `f` sheared so that all slopes drop by
  exactly `w`;
* `suppVal_scaleRoots` (auxiliary, the STATEMENT's middle clause) — the cleared support value
  therefore shifts by the *constant* `w·n`:
  `suppVal X (f.scaleRoots (π ^ w)) (u + w) 1 = suppVal X f u 1 + w * n`;
* **B.70b** `sideSet X (f.scaleRoots (π ^ w)) (u + w) 1 = sideSet X f u 1` — so the side of
  slope `−(u+w)` of the scaled polynomial occupies exactly the abscissae of the slope-`−u` side
  of `f`.

## The proof

1. At `φ = X` the polygon heights are the coefficient valuations (B.15's `npHgt_X`), and
   `(f.scaleRoots s).coeff j = f.coeff j * s ^ (n - j)` (mathlib's `Polynomial.coeff_scaleRoots`,
   unconditional). With `s = π ^ w`, `(π ^ w) ^ (n - j) = π ^ (w·(n-j))`, so
   `AddValuation`-multiplicativity (`IsDiscreteValuationRing.addVal_mul`) and
   `Irreducible.addVal_pow` give B.70a in one `rw`.
2. For `j ≤ n` the two weights differ by the constant `w·n`:
   `w·(n−j) + (u+w)·j = u·j + w·n` (this is the only place `j ≤ n` is used — it makes the
   truncated `n − j` honest). Since `(f.scaleRoots (π ^ w)).natDegree = n`
   (`Polynomial.natDegree_scaleRoots`), the two `suppVal` infima run over the *same* range, so
   the infimum shifts by the same constant: that is `suppVal_scaleRoots`, via the private
   `inf_add_natCast` (an infimum over a nonempty finset in the linear order `ℕ∞` is attained, so
   `inf (a · + K) = inf a + K` for finite `K`).
3. B.70b is then `Finset.filter_congr`: for `j` in the common range, `OnSide` at `(u+w, 1)` and
   `OnSide` at `(u, 1)` are the same equation with `w·n` added to both sides, and `w·n ≠ ⊤`
   cancels (`WithTop.add_right_inj`).

**Neither `hf : f.Monic` nor `hj : j ≤ f.natDegree` is consumed by B.70a.** Both are carried
from the frozen SIGNATURE. `hj` is genuinely redundant there: past the degree both sides are `⊤`
(`f.coeff j = 0` and `n − j = 0`), so the identity holds for every `j`; the linter is disabled
for that declaration alone. `hf` is likewise unused in B.70a — monicity is what makes the
statement *interesting* (it pins `natDegree_scaleRoots` and the right endpoint at height `0`),
and it is used in B.70b through B.70a's application there.

DEPENDS: B.11 (`npHgt`) · B.14 (`suppVal`) · B.15 (`npHgt_X`) · B.16 (`OnSide`, `sideSet`) ·
B.20 (imported for the side layer) · mathlib `Polynomial.coeff_scaleRoots`,
`Polynomial.natDegree_scaleRoots`, `IsDiscreteValuationRing.addVal_mul`,
`Irreducible.addVal_pow`, `Finset.exists_mem_eq_inf`, `Finset.inf_congr`,
`Finset.filter_congr`, `WithTop.add_right_inj`.

**Route note.** The blueprint lists the landed
`Uniformity.Density.dvd_sub_coeff_of_scaleRoots` (`ScaleExtraction.lean:61`) as a dependency.
The route above does not need it: `Polynomial.coeff_scaleRoots` is an exact coefficient formula,
which is strictly stronger than the divisibility that landed lemma records, so nothing is lost
and the import is dropped.

## ⚠ Why only `φ = X`

For a general key `φ`, `scaleRoots` does not act on the `φ`-development in a closed form (it
does not preserve `φ`), so no general statement is available or needed: the only consumer is
B.44/B.60's integral-slope extraction, which is at `φ = X` after B.69's shift. Recorded so that
nobody looks for the general statement.

## Faithfulness

`spec/CERTAIN_NODES_2026-08-14.md` CN-13; landed `ScaleExtraction.lean`; `EFF.W12.79` (the
`κ(T)` correction's level-0 decoration-orbit factor is the counting shadow of this shear).

SOURCE: CN-13; `EFF.W12.79`.

**TEETH.** `W12-L1X` (`EFF.W12.55`, 0/1,594,090, cross-implementation) → **executable
regression** retained; nothing here consumes it.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per
-- signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- Over the linear order `ℕ∞`, a finite nonempty infimum commutes with adding a finite
constant: the infimum is attained, so `inf (a · + K) = inf a + K`. Private helper. -/
private theorem inf_add_natCast {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (a : ι → ℕ∞)
    (K : ℕ) : s.inf (fun i => a i + (K : ℕ∞)) = s.inf a + (K : ℕ∞) := by
  refine le_antisymm ?_ (Finset.le_inf fun i hi => add_le_add (Finset.inf_le hi) le_rfl)
  obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_inf s hs a
  rw [hval]
  exact Finset.inf_le hi

/-- The shear arithmetic: for `j ≤ n`, `w·(n−j) + (u+w)·j = u·j + w·n`. The truncated
subtraction is honest exactly because `j ≤ n`. Private helper. -/
private theorem weight_shear_arith {n j : ℕ} (u w : ℕ) (hjn : j ≤ n) :
    w * (n - j) + (u + w) * j = u * j + w * n := by
  have hnj : n - j + j = n := Nat.sub_add_cancel hjn
  calc w * (n - j) + (u + w) * j = u * j + w * (n - j + j) := by ring
    _ = u * j + w * n := by rw [hnj]

set_option linter.unusedVariables false in
/-- **B.70 (a) — the heights shear.** Scaling the roots by `π ^ w` raises the `X`-adic polygon
height at abscissa `j` by `w` times the distance `n − j` to the right endpoint.

`hf` and `hj` are carried from the frozen SIGNATURE and are not consumed: past the degree both
sides are `⊤`. -/
theorem npHgt_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (w j : ℕ)
    (hj : j ≤ f.natDegree) :
    npHgt X (f.scaleRoots (π ^ w)) j = npHgt X f j + ((w * (f.natDegree - j) : ℕ) : ℕ∞) := by
  rw [npHgt_X, npHgt_X, Polynomial.coeff_scaleRoots, ← pow_mul,
    IsDiscreteValuationRing.addVal_mul, hπ.addVal_pow]

/-- **B.70, the STATEMENT's middle clause.** The cleared support value at the sheared slope
differs from the original by the constant `w · deg f`:
`suppVal X (f.scaleRoots (π ^ w)) (u + w) 1 = suppVal X f u 1 + w * f.natDegree`.

Not one of the two signed rows, but it is what B.70b's proof is made of, and it is the form
B.44/B.60 read the shear in. -/
theorem suppVal_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (u w : ℕ) :
    suppVal X (f.scaleRoots (π ^ w)) (u + w) 1
      = suppVal X f u 1 + ((w * f.natDegree : ℕ) : ℕ∞) := by
  have hnd : (f.scaleRoots (π ^ w)).natDegree = f.natDegree :=
    Polynomial.natDegree_scaleRoots f (π ^ w)
  have hne : (Finset.range (f.natDegree + 1)).Nonempty :=
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
  have hfun : ∀ j ∈ Finset.range (f.natDegree + 1),
      (1 : ℕ) • npHgt X (f.scaleRoots (π ^ w)) j + (((u + w) * j : ℕ) : ℕ∞)
        = ((1 : ℕ) • npHgt X f j + ((u * j : ℕ) : ℕ∞)) + ((w * f.natDegree : ℕ) : ℕ∞) := by
    intro j hj
    have hjn : j ≤ f.natDegree := by have := Finset.mem_range.1 hj; omega
    rw [one_smul, one_smul, npHgt_scaleRoots hπ hf w j hjn, add_assoc, ← Nat.cast_add,
      weight_shear_arith u w hjn, Nat.cast_add, ← add_assoc]
  simp only [suppVal, hnd]
  calc (Finset.range (f.natDegree + 1)).inf
        (fun j => (1 : ℕ) • npHgt X (f.scaleRoots (π ^ w)) j + (((u + w) * j : ℕ) : ℕ∞))
      = (Finset.range (f.natDegree + 1)).inf
          (fun j => ((1 : ℕ) • npHgt X f j + ((u * j : ℕ) : ℕ∞))
            + ((w * f.natDegree : ℕ) : ℕ∞)) := Finset.inf_congr rfl hfun
    _ = (Finset.range (f.natDegree + 1)).inf
          (fun j => (1 : ℕ) • npHgt X f j + ((u * j : ℕ) : ℕ∞))
        + ((w * f.natDegree : ℕ) : ℕ∞) := inf_add_natCast hne _ _

/-- **B.70 (b) — the side is unmoved, the slope shifts by `w`.** The `(u+w, 1)`-side of the
scaled polynomial occupies exactly the abscissae of the `(u, 1)`-side of `f`. -/
theorem sideSet_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (u w : ℕ) :
    sideSet X (f.scaleRoots (π ^ w)) (u + w) 1 = sideSet X f u 1 := by
  classical
  have hnd : (f.scaleRoots (π ^ w)).natDegree = f.natDegree :=
    Polynomial.natDegree_scaleRoots f (π ^ w)
  have hsupp := suppVal_scaleRoots hπ hf u w
  simp only [sideSet, hnd]
  refine Finset.filter_congr ?_
  intro j hj
  have hjn : j ≤ f.natDegree := by have := Finset.mem_range.1 hj; omega
  simp only [OnSide, one_smul, hsupp, npHgt_scaleRoots hπ hf w j hjn]
  rw [add_assoc, ← Nat.cast_add, weight_shear_arith u w hjn, Nat.cast_add, ← add_assoc]
  exact WithTop.add_right_inj (ENat.coe_ne_top _)

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.npHgt_scaleRoots
#print axioms Uniformity.Density.Leaf.suppVal_scaleRoots
#print axioms Uniformity.Density.Leaf.sideSet_scaleRoots
end AxCheck
