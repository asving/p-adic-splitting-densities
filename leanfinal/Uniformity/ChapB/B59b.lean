/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B59a

/-!
# Uniformity.ChapB.B59b — the residual-to-reduction bridge at `φ = X`: the contract

**Chapter B, NODE B.59** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §7, the leaf layer), ENV-C,
**SPLIT 2 of 2** (`B59a` = PROOF steps 1–2, the digit identity; this file = step 3 and the signed
contract). One signed declaration.

*The residual-to-reduction bridge at integral slope — at the linear key `φ = X`.* For `0 < u` and
`g` monic `(u,1)`-pure at the key `X`, written as `g = G.scaleRoots (π^u)` with `G` monic of the
same degree (B.44's extraction),

```
Irreducible (G.map (residue O))  ↔  Irreducible (resPoly π X g u 1 _ H₀).
```

`B59a`'s digit identity makes the right-hand polynomial the image of the left-hand one under the
coefficient-field identification `ResidueField O ≃+* resField X` (`resFieldXEquiv`), and
`Irreducible` transports along the induced equivalence `Polynomial.mapEquiv` of polynomial rings.
That is PROOF step 3, and it is the whole content of this file.

## Provenance: A-F.7's re-signed form

The frozen general-key signature is REFUTED by a compiled witness
(`Uniformity/ChapB/B59_REFUTATION.lean.txt`, kept as provenance): `hscale` is `φ = X`-shaped, and
at `2 ≤ φ.natDegree` it forces `sideDeg = 0`, so `resPoly` degenerates to a nonzero constant —
never irreducible — while `Ḡ` is free to be irreducible (`g = G = X`). Amendment A-F.7 re-signed
the node at `φ = X`; the general-key `ℓ = 1, m ≥ 2, d ≥ 2` region moved to B.61's `B-BOX-1`.

## The signed hypotheses `hu` and `hG` are not consumed

Neither `0 < u` nor `G.Monic` is used: at the linear key the bridge is a coefficientwise identity
that holds at `u = 0` as well (there `scaleRoots (π^0)` is the identity and every line height is
`0`), and `G`'s monicity is already implied by `hg`+`hscale`+`hGdeg` where it matters. Both are
kept because the signature is frozen at A-F.7's form; the linters are silenced accordingly.

DEPENDS: B.59a (`resPoly_X_eq_map_of_scaleRoots`, `resFieldXEquiv`) · mathlib
`Polynomial.mapEquiv`, `MulEquiv.irreducible_iff`.

**No new axioms; no `sorry`.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus residue finiteness. Neither instance is consumed; they are
-- declared to reproduce the frozen stub's elaborated type (`[Finite (ResidueField O)]` is trimmed
-- there too — see the stub file's defect note B-D15).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
omit [Finite (ResidueField O)] in
/-- **B.59 — the residual-to-reduction bridge at integral slope, at the linear key `φ = X`.**
For `0 < u` and a monic `(u,1)`-pure `g` at the key `X` presented as `g = G.scaleRoots (π^u)`
with `G` monic of the same degree, the reduction of `G` is irreducible over `ResidueField O` iff
the residual polynomial of `g` is irreducible over `resField X`.

`B59a`'s digit identity says the two polynomials correspond under the coefficient-field
identification `ResidueField O ≃+* resField X`; `Irreducible` transports along the induced
equivalence of polynomial rings. -/
theorem irreducible_map_iff_irreducible_resPoly (hπ : Irreducible π)
    {u : ℕ} (hu : 0 < u) {g G : Polynomial O} (hg : g.Monic) (hG : G.Monic)
    (hGdeg : G.natDegree = g.natDegree) (hscale : g = G.scaleRoots (π ^ u))
    (hpure : IsPure X g u 1) (hne : (sideSet X g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X g 0 = (H₀ : ℕ∞)) :
    Irreducible (G.map (IsLocalRing.residue O)) ↔ Irreducible (resPoly π X g u 1 hne H₀) := by
  -- Steps 1–2 (B59a): the residual polynomial is the reduction of `G`, coefficientwise.
  rw [resPoly_X_eq_map_of_scaleRoots hπ hg hGdeg hscale hpure hne hH₀]
  -- Step 3: `Irreducible` transports along `Polynomial.mapEquiv (resFieldXEquiv O)`.
  have hmap : (G.map (residue O)).map (AdjoinRoot.of ((X : Polynomial O).map (residue O)))
      = Polynomial.mapEquiv (resFieldXEquiv O) (G.map (residue O)) := by
    rw [Polynomial.mapEquiv_apply, resFieldXEquiv_coe]
  rw [hmap]
  exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv (resFieldXEquiv O))).symm

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.irreducible_map_iff_irreducible_resPoly
end AxCheck
