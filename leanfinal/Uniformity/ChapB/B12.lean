/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B04
import Uniformity.ChapB.B08
import Uniformity.ChapB.B11

/-!
# Uniformity.ChapB.B12 — the `⊤` corner of `npHgt`

**Chapter B, NODE B.12** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

The height function of B.11 takes the value `⊤` exactly at the abscissae that carry no
support point: `npHgt φ f j = ⊤ ↔ dev φ f j = 0`; and, for `φ` monic with `0 < deg φ`, this
happens at every `j > f.natDegree`. The tail clause is what lets B.14's `suppVal` take the
single range `range (f.natDegree + 1)` uniformly in `u` and `ℓ` without losing anything.

DEPENDS: B.04 (`dev_eq_zero_of_lt`) · B.08 (`gaussVal_eq_top_iff`) · B.11 (`npHgt`).

**PROOF.**

1. First claim: `npHgt φ f j` is by definition `gaussVal (dev φ f j)`, so this is B.08's
   `gaussVal_eq_top_iff`.
2. Second claim: `f.natDegree < j ≤ j * φ.natDegree` because `1 ≤ φ.natDegree`; B.04 gives
   `dev φ f j = 0` and the first claim converts it.

SOURCE: `EFF.HE6.09` (the `dv = ∞` corner: "a root `ρ` with `Φ′(ρ) = 0` has `dv(Φ′(ρ)) = ∞`
and carries NO finite side label").

TEETH: signed non-applicable.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The height at `j` is `⊤` exactly when the `j`-th development coefficient vanishes, i.e.
when the abscissa `j` carries no support point. -/
theorem npHgt_eq_top_iff {φ f : Polynomial O} {j : ℕ} : npHgt φ f j = ⊤ ↔ dev φ f j = 0 :=
  gaussVal_eq_top_iff

/-- Past the degree of `f` every abscissa is empty: `npHgt φ f j = ⊤` for `f.natDegree < j`.
-/
theorem npHgt_eq_top_of_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f : Polynomial O) {j : ℕ} (hj : f.natDegree < j) : npHgt φ f j = ⊤ :=
  npHgt_eq_top_iff.2
    (dev_eq_zero_of_lt hφ hd f j (lt_of_lt_of_le hj (Nat.le_mul_of_pos_right j hd)))

section AxCheck
#print axioms Uniformity.Density.Leaf.npHgt_eq_top_iff
#print axioms Uniformity.Density.Leaf.npHgt_eq_top_of_lt
end AxCheck

end Uniformity.Density.Leaf
