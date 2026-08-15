/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B44
import Uniformity.ChapB.B59b
import Uniformity.Density.InertLeaf

/-!
# Uniformity.ChapB.B60 — THE LEAF THEOREM at integral slope, at the linear key

**Chapter B, NODE B.60** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §7, the `(e,f)` layer),
ENV-C. One signed declaration.

*THE LEAF THEOREM at integral slope — at the linear key `φ = X`, any `d`.* For `0 < u` and `g`
monic `(u,1)`-pure at the key `X` with `d = sideDeg X g u 1 > 0`, reduction `ḡ = X̄^d`, and
irreducible residual polynomial,

```
typeOf g = ⟨{(1, X.natDegree * d)}⟩   (i.e. ⟨{(1, d)}⟩: one inert factor of residue degree d).
```

The route is three landed steps: B.44 extracts the monic `G` with `g = G.scaleRoots (π^u)` and
`typeOf g = typeOf G` (the integral-slope shortcut, `ScaleExtraction`-only); B.59 turns the
irreducibility of the residual polynomial into the irreducibility of `Ḡ`; and the landed
`typeOf_inert_of_irreducible_map` (CN-21, `Density/InertLeaf.lean:179`) reads the inert leaf off
`Ḡ`.

## Provenance: A-F.7's re-signed form, and what is NOT proved here

This node was frozen at a general key `φ`. Amendment A-F.7 re-signed it **at `φ = X`** after two
machine-checked refutations: B.59's general-key form is FALSE (compiled witness, kept at
`Uniformity/ChapB/B59_REFUTATION.lean.txt`), and the conjectured general-`φ` extraction "B.44′"
is REFUTED as well (`φ = X²+1`, `u = 1`, `g = X²+4` over `ℤ₃`: the `dev`-shift extraction
`G = X²+2` has `typeOf g = ⟨{(1,2)}⟩ ≠ ⟨{(1,1),(1,1)}⟩ = typeOf G`, and `Ḡ` is reducible while
`resPoly g = Y+1` is irreducible) — no `O[X]`-level shift of the development data can encode the
key's own residue extension. So the `ℓ = 1, m ≥ 2, d ≥ 2` region is NOT covered here: it routes
to B.61's `hBOX` (`B-BOX-1`) and is recorded OPEN-MATH in chapter I's ledger. `d = 1` at any `m`
was always B.58's.

## Two signed hypotheses are not consumed

`hres` (the reduction `ḡ = X̄^d`) and `hd`'s companion data are not needed for the degree pin: at
the linear key, purity alone puts the whole abscissa range on the side, so
`sideDeg X g u 1 hne = g.natDegree` (B.59a's `sideData_X_of_isPure`) and `hd` supplies
`0 < g.natDegree` directly. `hres` is therefore signed but unused, as is `hu` (which B.59 also does
not consume). Both are kept because the signature is frozen at A-F.7's form.

DEPENDS: B.13b (through B.59a) · B.15 (through B.59a) · B.44
(`exists_scaleRoots_of_pure_integral`) · B.59 (`irreducible_map_iff_irreducible_resPoly`, the
A-F.7 re-signed form, and `sideData_X_of_isPure` from its first split file) · landed
`Uniformity.Density.typeOf_inert_of_irreducible_map` (`Density/InertLeaf.lean:179`).

**No new axioms; no `sorry`.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus residue finiteness. Completeness is genuinely consumed
-- (through the landed CN-21 inert leaf); residue finiteness is not, and the frozen stub trims it
-- too (the stub file's defect note B-D15).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
omit [Finite (ResidueField O)] in
/-- **B.60 — THE LEAF THEOREM at integral slope, at the linear key `φ = X`.** A monic
`(u,1)`-pure `g` at the key `X` with positive residual degree `d` and irreducible residual
polynomial has splitting type `⟨{(1, X.natDegree * d)}⟩` — one inert factor, ramification index
`1`, residue degree `d`.

B.44's extraction (`g = G.scaleRoots (π^u)`, `typeOf g = typeOf G`), B.59's bridge
(`Irreducible (resPoly …) ↔ Irreducible Ḡ`) and the landed inert leaf, composed. -/
theorem typeOf_leaf_integral_slope (hπ : Irreducible π)
    {u : ℕ} (hu : 0 < u) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure X g u 1) (hne : (sideSet X g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X g 0 = (H₀ : ℕ∞)) (hd : 0 < sideDeg X g u 1 hne)
    (hres : g.map (IsLocalRing.residue O)
      = ((X : Polynomial O).map (IsLocalRing.residue O)) ^ (sideDeg X g u 1 hne))
    (hirr : Irreducible (resPoly π X g u 1 hne H₀)) :
    typeOf g = ⟨{(1, (X : Polynomial O).natDegree * sideDeg X g u 1 hne)}⟩ := by
  -- Step 1a: the side geometry at the linear key (B.59a): the residual degree IS the degree.
  obtain ⟨-, hdeg, -⟩ := sideData_X_of_isPure hg hpure hne hH₀
  have hn : 0 < g.natDegree := hdeg ▸ hd
  -- Step 1b: B.44's remaining hypothesis — the on-side value at the polygon's terminal point.
  have hsupp : suppVal X g u 1 = ((u * g.natDegree : ℕ) : ℕ∞) := by
    have hXdeg : (X : Polynomial O).natDegree = 1 := natDegree_X
    have hend : OnSide X g u 1 g.natDegree := by
      have h := hpure.2
      rwa [hXdeg, Nat.div_one] at h
    have htop : npHgt X g g.natDegree = ((0 : ℕ) : ℕ∞) := by
      rw [npHgt_top monic_X (by rw [hXdeg]; exact Nat.zero_lt_one) hg (by rw [hXdeg, mul_one])]
      simp
    have h : (1 : ℕ) • npHgt X g g.natDegree + ((u * g.natDegree : ℕ) : ℕ∞)
        = suppVal X g u 1 := hend
    rw [htop] at h
    simpa using h.symm
  -- Step 1c: B.44 — the rescaling extraction, `typeOf`-preserving.
  obtain ⟨G, hG, hGdeg, hscale, hGtype, -⟩ :=
    exists_scaleRoots_of_pure_integral hπ hg hn hpure hsupp
  -- Step 2: B.59 — the residual polynomial's irreducibility is `Ḡ`'s.
  have hGirr : Irreducible (G.map (IsLocalRing.residue O)) :=
    (irreducible_map_iff_irreducible_resPoly hπ hu hg hG hGdeg hscale hpure hne hH₀).mpr hirr
  -- Step 3: the landed inert leaf (CN-21) at `G`.
  have hGt : typeOf G = ⟨{(1, G.natDegree)}⟩ :=
    Uniformity.Density.typeOf_inert_of_irreducible_map hG (hGdeg ▸ hn) hGirr
  -- Step 4: transport back along `typeOf g = typeOf G` and normalise `X.natDegree = 1`.
  rw [hGtype, hGt, hGdeg, natDegree_X, one_mul, hdeg]

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.typeOf_leaf_integral_slope
end AxCheck
