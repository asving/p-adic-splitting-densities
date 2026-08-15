/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B13b
import Uniformity.ChapB.B15
import Uniformity.ChapB.B20
import Uniformity.ChapB.B22
import Uniformity.ChapB.B29
import Uniformity.ChapB.B34
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapB.B59a — the residual-to-reduction bridge at `φ = X`: the digit identity

**Chapter B, NODE B.59** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §7, the leaf layer), ENV-C,
**SPLIT 1 of 2** (the node's own `SPLIT MANDATED → 2`: `B59a` = PROOF steps 1–2, the digit
identity; `B59b` = step 3 and the signed contract).

*The residual-to-reduction bridge at integral slope, at the linear key `φ = X`.* This file
carries the two computational steps: the side geometry of a `(u,1)`-pure `g` at the key `X`
(`sideMin = 0`, `sideDeg = g.natDegree`, `H₀ = u * g.natDegree`) and the coefficientwise
identity

```
resPoly π X g u 1 hne H₀ = (G.map (residue O)).map (AdjoinRoot.of (X.map (residue O)))
```

for `g = G.scaleRoots (π^u)`, i.e. the residual polynomial of `g` **is** the reduction of the
extracted `G`, read through the coefficient-field identification `ResidueField O ≃+* resField X`.

## Provenance: this node is A-F.7's re-signed form

The frozen general-key signature of B.59 is **REFUTED** by a compiled witness
(`Uniformity/ChapB/B59_REFUTATION.lean.txt`, kept as provenance): its `hscale` is `φ = X`-shaped
and at `2 ≤ φ.natDegree` forces `sideDeg = 0`, so `resPoly` degenerates to a nonzero constant
while `Ḡ` is free to be irreducible (`g = G = X` witnesses this at any such key). Amendment
A-F.7 re-signed the node **at `φ = X`**, where the bridge is coefficientwise — that is what this
file proves. The retired general-`φ` route (an ideal identification in the graded algebra) is
gone with the signature.

## The coefficient-field identification is built here, by hand

`resField X = AdjoinRoot ((X : Polynomial O).map (residue O))` and `X.map (residue O) = X`, so
the identification `ResidueField O ≃+* resField X` is "adjoin a root of `X`", i.e. nothing. The
pinned mathlib has no `AdjoinRoot X ≃ R`, so `adjoinRootXEquiv` below builds it from
`AdjoinRoot.of`/`AdjoinRoot.lift` (evaluation at `0`); the hypothesis is `q = X` rather than
`q = X` substituted, so that the equivalence is *definitionally* `AdjoinRoot.of q` on the nose
(that is what `B59b` needs to transport `Irreducible` along `Polynomial.mapEquiv`).

DEPENDS: B.13b (`npHgt_top`, the polygon's terminal point) · B.15 (`dev_X`, `npHgt_X`) ·
B.20 (`sideMin`/`sideMax`/`sideDeg`, `onSide_of_mem_sideSet`) · B.21/B.22 (`digAt`, `digAt_eq`) ·
B.23/B.25 (`digPoly`, `resField`, `resMk`) · B.28 (`resCoeff`) · B.29 (`resPoly`) ·
B.34 (`IsPure`) · landed `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow` ·
mathlib `Polynomial.coeff_scaleRoots`, `AdjoinRoot.lift`/`mk_eq_mk`, `Polynomial.X_dvd_iff`.

**No new axioms; no `sorry`.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

/-! ## The coefficient-field identification at the linear key -/

/-- **B.59, auxiliary (not a signed node statement).** For any presentation `q = X` of the linear
key, `R ≃+* AdjoinRoot q`: the ring map is `AdjoinRoot.of q` and its inverse is evaluation of a
representative at `0` (`AdjoinRoot.lift (RingHom.id R) 0`).

Stated with `(hq : q = X)` rather than at `q = X` literally so that the coercion
`↑(adjoinRootXEquiv hq) = AdjoinRoot.of q` holds by `rfl` at the `q` a consumer actually has
(here `q = X.map (residue O)`, which is only propositionally `X`). -/
noncomputable def adjoinRootXEquiv {R : Type*} [CommRing R] {q : Polynomial R} (hq : q = X) :
    R ≃+* AdjoinRoot q :=
  RingEquiv.ofRingHom (AdjoinRoot.of q)
    (AdjoinRoot.lift (RingHom.id R) 0 (by rw [hq]; simp))
    (by
      refine RingHom.ext fun x => ?_
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [RingHom.comp_apply, AdjoinRoot.lift_mk, eval₂_id, ← AdjoinRoot.mk_C,
        RingHom.id_apply, AdjoinRoot.mk_eq_mk, hq, X_dvd_iff]
      simp [coeff_zero_eq_eval_zero])
    (AdjoinRoot.lift_comp_of _)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **B.59, auxiliary (not a signed node statement).** B.44's declared identification
`resField X ≅ ResidueField O`, as a `RingEquiv` in the direction `ResidueField O ≃+* resField X`.
Its underlying ring map is `AdjoinRoot.of (X.map (residue O))` by `rfl`. -/
noncomputable def resFieldXEquiv (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : ResidueField O ≃+* resField (X : Polynomial O) :=
  adjoinRootXEquiv (Polynomial.map_X (residue O))

/-- **B.59, auxiliary.** The coercion of `resFieldXEquiv` is `AdjoinRoot.of`, by `rfl`. -/
theorem resFieldXEquiv_coe (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ((resFieldXEquiv O : ResidueField O ≃+* resField (X : Polynomial O)) :
        ResidueField O →+* resField (X : Polynomial O))
      = AdjoinRoot.of ((X : Polynomial O).map (residue O)) :=
  rfl

/-! ## PROOF step 1 — the side geometry at the linear key -/

/-- **B.59 PROOF step 1 (auxiliary).** At the key `X` a monic `(u,1)`-pure `g` has its whole
abscissa range on the side: `sideMin = 0`, `sideDeg = g.natDegree`, and the left height `H₀` is
`u * g.natDegree`.

The right endpoint of `IsPure` is `g.natDegree / X.natDegree = g.natDegree`, whose polygon height
is `0` (B.13b's `npHgt_top`), so the cleared support value is `u * g.natDegree`; the left endpoint
`0` then has height exactly that value. -/
theorem sideData_X_of_isPure {u : ℕ} {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure X g u 1) (hne : (sideSet X g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X g 0 = (H₀ : ℕ∞)) :
    sideMin X g u 1 hne = 0 ∧ sideDeg X g u 1 hne = g.natDegree ∧ H₀ = u * g.natDegree := by
  classical
  -- the two endpoints of `IsPure`, with the right one's abscissa normalised to `g.natDegree`
  have hXdeg : (X : Polynomial O).natDegree = 1 := natDegree_X
  have hstart : OnSide X g u 1 0 := hpure.1
  have hend : OnSide X g u 1 g.natDegree := by
    have := hpure.2
    rwa [hXdeg, Nat.div_one] at this
  -- the terminal height is `0` (B.13b at `μ = g.natDegree`, `φ = X`)
  have htop : npHgt X g g.natDegree = ((0 : ℕ) : ℕ∞) := by
    rw [npHgt_top monic_X (by rw [hXdeg]; exact Nat.zero_lt_one) hg (by rw [hXdeg, mul_one])]
    simp
  -- the two on-side equations, in `ℕ`
  have hnat : 1 * H₀ + u * 0 = 1 * 0 + u * g.natDegree :=
    onSide_nat_eq hH₀ htop hstart hend
  have hH : H₀ = u * g.natDegree := by omega
  -- both endpoints are members of the side set
  have hmem0 : (0 : ℕ) ∈ sideSet X g u 1 := by
    have : (0 : ℕ) ∈ Finset.filter (OnSide X g u 1) (Finset.range (g.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), hstart⟩
    exact this
  have hmemn : g.natDegree ∈ sideSet X g u 1 := by
    have : g.natDegree ∈ Finset.filter (OnSide X g u 1) (Finset.range (g.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self _), hend⟩
    exact this
  -- `sideMin = 0` and `sideMax = g.natDegree`
  have hmin : sideMin X g u 1 hne = 0 :=
    Nat.le_zero.mp (Finset.min'_le _ _ hmem0)
  have hmax : sideMax X g u 1 hne = g.natDegree := by
    refine le_antisymm ?_ (Finset.le_max' _ _ hmemn)
    have hmem : sideMax X g u 1 hne ∈ sideSet X g u 1 := Finset.max'_mem _ _
    have hmem' : sideMax X g u 1 hne ∈
        Finset.filter (OnSide X g u 1) (Finset.range (g.natDegree + 1)) := hmem
    have := Finset.mem_range.mp (Finset.mem_filter.mp hmem').1
    omega
  exact ⟨hmin, by rw [sideDeg, hmax, hmin, Nat.sub_zero, Nat.div_one], hH⟩

/-! ## PROOF step 2 — the coefficientwise digit identity -/

/-- **B.59 PROOF step 2 (auxiliary).** The digit polynomial of a constant is the constant of its
digit. -/
theorem digPoly_C (π : O) (k : ℕ) (a : O) :
    digPoly π k (Polynomial.C a) = Polynomial.C (digAt π k a) := by
  rw [digPoly, natDegree_C, Finset.sum_range_one, pow_zero, mul_one, coeff_C_zero]

/-- **B.59 PROOF step 2 (auxiliary).** The `k`-th residual coefficient of `g` at the key `X` is
the reduction of the `k`-th coefficient of the extracted `G`, pushed into `resField X`.

`g.coeff k = π^(u*(n−k)) * G.coeff k` by `coeff_scaleRoots`, so B.22's `digAt_eq` reads the digit
at the side's line height `H₀ − u*k = u*(n−k)` off `G` — B.44's third clause, here for the given
`G` rather than for the one B.44 constructs. -/
theorem resCoeff_X_eq {u : ℕ} {g G : Polynomial O} (hπ : Irreducible π) (hg : g.Monic)
    (hGdeg : G.natDegree = g.natDegree) (hscale : g = G.scaleRoots (π ^ u))
    (hpure : IsPure X g u 1) (hne : (sideSet X g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X g 0 = (H₀ : ℕ∞)) (k : ℕ) :
    resCoeff π X g u 1 hne H₀ k
      = AdjoinRoot.of ((X : Polynomial O).map (residue O)) (residue O (G.coeff k)) := by
  obtain ⟨hmin, -, hH⟩ := sideData_X_of_isPure hg hpure hne hH₀
  -- the coefficientwise rescaling identity
  have hcoeff : g.coeff k = π ^ (u * (g.natDegree - k)) * G.coeff k := by
    conv_lhs => rw [hscale]
    rw [coeff_scaleRoots, hGdeg, ← pow_mul]
    ring
  have hheight : H₀ - u * k = u * (g.natDegree - k) := by
    rw [hH, Nat.mul_sub]
  rw [resCoeff, hmin, zero_add, one_mul, dev_X, hheight, resMk, digPoly_C,
    digAt_eq hπ hcoeff, AdjoinRoot.mk_C]

/-- **B.59 PROOF steps 1–2 — THE DIGIT IDENTITY (auxiliary; `B59b` signs the contract).** At the
key `X`, for `0 < u`-integral slope and `g = G.scaleRoots (π^u)` with `G` monic of the same
degree, the residual polynomial of `g` is exactly the reduction of `G`, mapped into `resField X`
by the coefficient-field identification `AdjoinRoot.of (X.map (residue O))`.

Coefficientwise: below `g.natDegree + 1 = sideDeg + 1` this is `resCoeff_X_eq`; above it both
sides vanish (`resPoly`'s sum is truncated at `sideDeg`, and `G` has degree `g.natDegree`). -/
theorem resPoly_X_eq_map_of_scaleRoots {u : ℕ} {g G : Polynomial O} (hπ : Irreducible π)
    (hg : g.Monic) (hGdeg : G.natDegree = g.natDegree) (hscale : g = G.scaleRoots (π ^ u))
    (hpure : IsPure X g u 1) (hne : (sideSet X g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X g 0 = (H₀ : ℕ∞)) :
    resPoly π X g u 1 hne H₀
      = (G.map (residue O)).map (AdjoinRoot.of ((X : Polynomial O).map (residue O))) := by
  obtain ⟨-, hdeg, -⟩ := sideData_X_of_isPure hg hpure hne hH₀
  refine Polynomial.ext fun i => ?_
  rw [resPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, hdeg, coeff_map, coeff_map]
  by_cases hi : i < g.natDegree + 1
  · rw [if_pos hi, resCoeff_X_eq hπ hg hGdeg hscale hpure hne hH₀ i]
  · rw [if_neg hi,
      coeff_eq_zero_of_natDegree_lt (n := i) (by rw [hGdeg]; omega), map_zero, map_zero]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.adjoinRootXEquiv
#print axioms Uniformity.Density.Leaf.resFieldXEquiv
#print axioms Uniformity.Density.Leaf.resFieldXEquiv_coe
#print axioms Uniformity.Density.Leaf.sideData_X_of_isPure
#print axioms Uniformity.Density.Leaf.digPoly_C
#print axioms Uniformity.Density.Leaf.resCoeff_X_eq
#print axioms Uniformity.Density.Leaf.resPoly_X_eq_map_of_scaleRoots
end AxCheck
