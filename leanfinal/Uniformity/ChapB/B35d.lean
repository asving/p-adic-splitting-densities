/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B35c

/-!
# Uniformity.ChapB.B35d — the support values add, and purity is preserved

**Chapter B, NODE B.35, part (d) of the mandated 4-way split**
(`blueprint/CHAP-B_leaf_layer.md` §5), ENV-A′ + `[Finite (ResidueField O)]`. The **first signed
contract theorem of B.35**, `suppVal_mul_of_pure` (the blueprint's PROOF step 7): for monic
`(u,ℓ)`-pure `f`, `g` of `φ.natDegree`-divisible degrees,

```
suppVal φ (f*g) u ℓ = suppVal φ f u ℓ + suppVal φ g u ℓ   and   IsPure φ (f*g) u ℓ.
```

Both clauses are read off B35c's normal form of the product. Clause 1 is a sandwich that needs no
digit calculus at all (B.33's superadditivity below, B.18's terminal-point bound above — for
full-degree pure factors both ends are `u·n`). Clause 2 does need the digit calculus, in exactly one
place: purity of the product asks that the polygon's point at abscissa `0` sit *on* the line, i.e.
that the product's leading digit not vanish, and that is B35b's master identity at `k = 0` together
with `resField φ` being a field (B35c's `npHgt_mul_of_pure`).

**The A-F.6 hypotheses.** `hfd`/`hgd` are load-bearing for clause 2: `IsPure`'s right endpoint is
the *truncated* `f.natDegree / φ.natDegree`, so without them `f = X` at `φ = X²+1` over `ℤ₃` is
`(1,1)`-pure while `X² = φ − 1` is not — the first machine-checked counterexample of amendment
A-F.6. `hu : 0 < u` is load-bearing through B35b's carry estimate (the second counterexample).

DEPENDS: B.18 (`sideSet_nonempty`) · B.17 (`npHgt_ne_top_of_onSide`) · B35b · B35c
(`suppVal_mul_eq_of_pure`, `isPure_mul_of_pure`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **B.35 (a) — the support values add and purity is preserved** (the signed contract theorem;
signature frozen at the A-F.6 form). -/
theorem suppVal_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O}
    (hf : f.Monic) (hg : g.Monic)
    (hfd : φ.natDegree ∣ f.natDegree) (hgd : φ.natDegree ∣ g.natDegree)
    (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ) :
    suppVal φ (f * g) u ℓ = suppVal φ f u ℓ + suppVal φ g u ℓ ∧ IsPure φ (f * g) u ℓ := by
  classical
  -- the divisibilities make the two degrees exact multiples of `m`
  have hfdeg0 : f.natDegree = (f.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hfd).symm
  have hgdeg0 : g.natDegree = (g.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hgd).symm
  have hf' : (sideSet φ f u ℓ).Nonempty :=
    sideSet_nonempty hφ.monic hφ.pos hf hfdeg0 u ℓ
  have hg' : (sideSet φ g u ℓ).Nonempty :=
    sideSet_nonempty hφ.monic hφ.pos hg hgdeg0 u ℓ
  have hftop : suppVal φ f u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ.monic hφ.pos hf hfdeg0 hfp]; exact ENat.coe_ne_top _
  have hgtop : suppVal φ g u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ.monic hφ.pos hg hgdeg0 hgp]; exact ENat.coe_ne_top _
  obtain ⟨H₀f, hHf⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ hftop hfp.1)
  obtain ⟨H₀g, hHg⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ hgtop hgp.1)
  -- the residual degrees, and the degrees in the `ℓ · d · m` form B35b/B35c consume
  have hnf : ℓ * sideDeg φ f u ℓ hf' = f.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hfp hf'
  have hng : ℓ * sideDeg φ g u ℓ hg' = g.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hg hgdeg0 hℓ hcop hgp hg'
  have hfdeg : f.natDegree = ℓ * sideDeg φ f u ℓ hf' * φ.natDegree := by
    rw [hnf]; exact hfdeg0
  have hgdeg : g.natDegree = ℓ * sideDeg φ g u ℓ hg' * φ.natDegree := by
    rw [hng]; exact hgdeg0
  have hdf : H₀f = u * sideDeg φ f u ℓ hf' :=
    height_eq_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hfp hf' hHf.symm
  have hdg : H₀g = u * sideDeg φ g u ℓ hg' :=
    height_eq_of_pure hφ.monic hφ.pos hg hgdeg0 hℓ hcop hgp hg' hHg.symm
  refine ⟨?_, isPure_mul_of_pure hπ hφ hu hℓ hcop hf hg hfdeg hgdeg hfp hgp hHf.symm hHg.symm
    hdf hdg⟩
  -- clause 1: the sandwich of B.33 and B.18
  rw [suppVal_mul_eq_of_pure hπ hφ hℓ hf hg hfdeg hgdeg hfp hgp,
    suppVal_of_pure hφ.monic hφ.pos hf hfdeg hfp, suppVal_of_pure hφ.monic hφ.pos hg hgdeg hgp]
  push_cast
  ring

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_mul_of_pure
end AxCheck
