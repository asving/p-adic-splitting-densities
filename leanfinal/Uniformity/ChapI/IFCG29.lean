/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG27
import Uniformity.MultiHensel
import Uniformity.Density.TypeOfAlgebra
import Uniformity.ChapB.B63a

/-!
# Uniformity.ChapI.IFCG29 — [UBC 2026-08-30] the unramified block count law

UBB (`IFCG27.lean`) reduced the census's bridge family to the single count law
`UnramifiedBlockCount δ e`: the equality between the `σ`-decided level-`N` census of
`p^e` over `O` at the scaled label `fScale δ s'` and the census of `(X − θ̄)^e` over the
concrete unramified extension `O' = AdjoinRoot φ` at `s'`.  This file builds the Hensel
block correspondence behind it:

* **§1 the roots package**: over `k' = ResidueField O'` the residual key `φ̄` splits with
  `δ` DISTINCT roots (`φ̄ ∣ X^{q^δ} − X`, whose roots are all of `k'`); each residual
  root Hensel-lifts to a genuine root of `φ` in `O'`, uniquely at its residue.
* **§2 the conjugation family**: one `O`-algebra endomorphism `τ_ᾱ` of `O'` per residual
  root (`AdjoinRoot.liftHom` at the lifted root), with composition closure
  (`τ_β ∘ τ_α = τ_{τ̄_β(ᾱ)}`) and the induced residual action.  This replaces the single
  Frobenius of the classical picture: no `σ^δ = id`, no Frobenius identification needed.
* **§3 invariants**: an element of `O'` fixed by EVERY `τ_ᾱ` lies in `O` — residue level
  by a degree count (a polynomial of degree `< δ` taking one value at `δ` distinct
  points is constant), then the coordinate Krull induction on the power basis.
* **§4 blocks**: the multi-Hensel block decomposition of any lift of the `p^e` stratum,
  block conjugacy (every block is the `τ`-image of the `θ̄`-block), and finite-level
  exactness from IFCG16's finite-precision Hensel uniqueness.
* **§5 the reduction**: `BlockTypeDescent δ e` — the ONE type-transport law
  `typeOf F = fScale δ (typeOf B)` at the ∃-pinned `θ̄`-block — implies
  `UnramifiedBlockCount δ e`.
* **§6–§7**: the descent itself — conjugate products of irreducibles are irreducible
  (orbit argument on `monicFactors`), and the inertia degree scales by `δ`
  (`normValues O G = δ · normValues O' C` via the CRT norm peel).

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG29

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG17
open Uniformity.Density.IFCG25 (fScale UnramifiedBlockBridge)
open Uniformity.Density.IFCG27
open Uniformity.Density.IFCG16 (factor_sub_mem_of_mul_sub_mem mem_coeffIdeal_pow_iff)
open Uniformity.Density.Leaf (IsKey keyIsDomain)
open Uniformity.Hensel

attribute [local instance] Classical.propDecidable

/-! ## §1 — the roots package: `φ̄` splits over `k'` with `δ` distinct roots -/

section Roots

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {φ : Polynomial O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- The structure map into the unramified extension is a local homomorphism
(`𝔪' = 𝔪·O'`). -/
theorem isLocalHom_algebraMap_adjoinRoot (hφ : IsKey φ) :
    IsLocalHom (algebraMap O (AdjoinRoot φ)) := by
  constructor
  intro a ha
  by_contra hu
  have hmem : algebraMap O (AdjoinRoot φ) a ∈ maximalIdeal (AdjoinRoot φ) := by
    rw [adjoinRoot_maximalIdeal_eq hφ]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).mpr hu)
  exact (mem_maximalIdeal _).mp hmem ha

/-- The residue-field embedding `k ↪ k'` induced by `O → O' = AdjoinRoot φ`. -/
noncomputable def resEmb (hφ : IsKey φ) :
    ResidueField O →+* ResidueField (AdjoinRoot φ) :=
  letI := isLocalHom_algebraMap_adjoinRoot hφ
  IsLocalRing.ResidueField.map (algebraMap O (AdjoinRoot φ))

theorem resEmb_residue (hφ : IsKey φ) (a : O) :
    resEmb hφ (residue O a) = residue (AdjoinRoot φ) (algebraMap O (AdjoinRoot φ) a) :=
  letI := isLocalHom_algebraMap_adjoinRoot hφ
  IsLocalRing.ResidueField.map_residue _ a

/-- Reducing after extending = extending the reduction. -/
theorem map_map_residue_adjoinRoot (hφ : IsKey φ) (P : Polynomial O) :
    (P.map (algebraMap O (AdjoinRoot φ))).map (residue (AdjoinRoot φ))
      = (P.map (residue O)).map (resEmb hφ) := by
  have hcomp : (residue (AdjoinRoot φ)).comp (algebraMap O (AdjoinRoot φ))
      = (resEmb hφ).comp (residue O) :=
    RingHom.ext fun a => (resEmb_residue hφ a).symm
  rw [Polynomial.map_map, Polynomial.map_map, hcomp]

/-- **The residual root multiset** of the key over the extension's residue field. -/
noncomputable def keyRoots (hφ : IsKey φ) : Multiset (ResidueField (AdjoinRoot φ)) :=
  ((φ.map (residue O)).map (resEmb hφ)).roots

/-- The extended residual key divides `X^{q^δ} − X` (its adjoined root is fixed by the
`q^δ`-power map of the degree-`δ` residue extension). -/
private theorem keyRes_dvd_X_pow_sub_X (hφ : IsKey φ) :
    (φ.map (residue O)).map (resEmb hφ)
      ∣ (X ^ (residueCard O ^ φ.natDegree) - X
          : Polynomial (ResidueField (AdjoinRoot φ))) := by
  -- first in `k[X]`, through the finite field `AdjoinRoot φ̄` of cardinality `q^δ`
  haveI : Fact (Irreducible (φ.map (residue O))) := ⟨hφ.irred⟩
  haveI : Finite (AdjoinRoot (φ.map (residue O))) :=
    finite_adjoinRoot_of_monic (hφ.monic.map _)
  haveI : Fintype (AdjoinRoot (φ.map (residue O))) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot (φ.map (residue O)))
      = residueCard O ^ φ.natDegree := by
    rw [← Nat.card_eq_fintype_card, natCard_adjoinRoot (hφ.monic.map _),
      hφ.monic.natDegree_map]
    rfl
  have hdvd : φ.map (residue O)
      ∣ (X ^ (residueCard O ^ φ.natDegree) - X : Polynomial (ResidueField O)) := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard]
    rw [FiniteField.pow_card]
    exact sub_self _
  have := Polynomial.map_dvd (resEmb hφ) hdvd
  rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] at this

private theorem natDegree_keyRes (hφ : IsKey φ) :
    ((φ.map (residue O)).map (resEmb hφ)).natDegree = φ.natDegree := by
  rw [(hφ.monic.map (residue O)).natDegree_map, hφ.monic.natDegree_map]

private theorem one_lt_qpow (hφ : IsKey φ) : 1 < residueCard O ^ φ.natDegree := by
  have h2 := two_le_residueCard O
  have hle : residueCard O ≤ residueCard O ^ φ.natDegree :=
    Nat.le_self_pow (by have := hφ.pos; omega) _
  omega

/-- `X^{q^δ} − X` splits over `k'` (its roots are all of `k'`). -/
private theorem splits_X_pow_sub_X (hφ : IsKey φ) :
    Splits
      ((X : Polynomial (ResidueField (AdjoinRoot φ))) ^ (residueCard O ^ φ.natDegree) - X) := by
  haveI : Fintype (ResidueField (AdjoinRoot φ)) := Fintype.ofFinite _
  have hcardk' : Fintype.card (ResidueField (AdjoinRoot φ)) = residueCard O ^ φ.natDegree := by
    rw [← Nat.card_eq_fintype_card]
    exact residueCard_adjoinRoot hφ
  rw [splits_iff_card_roots, ← hcardk', FiniteField.roots_X_pow_card_sub_X,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ Fintype.one_lt_card]
  simp

/-- **The residual key splits over `k'`**: it has exactly `δ` roots there. -/
theorem card_keyRoots (hφ : IsKey φ) : Multiset.card (keyRoots hφ) = φ.natDegree := by
  have hne : ((X : Polynomial (ResidueField (AdjoinRoot φ)))
      ^ (residueCard O ^ φ.natDegree) - X) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero _ (one_lt_qpow hφ)
  have hsp : Splits ((φ.map (residue O)).map (resEmb hφ)) :=
    (splits_X_pow_sub_X hφ).of_dvd hne (keyRes_dvd_X_pow_sub_X hφ)
  rw [keyRoots, splits_iff_card_roots.mp hsp, natDegree_keyRes hφ]

/-- **The residual roots are pairwise distinct** (they sit inside the squarefree
`X^{q^δ} − X`). -/
theorem nodup_keyRoots (hφ : IsKey φ) : (keyRoots hφ).Nodup := by
  haveI : Fintype (ResidueField (AdjoinRoot φ)) := Fintype.ofFinite _
  have hcardk' : Fintype.card (ResidueField (AdjoinRoot φ)) = residueCard O ^ φ.natDegree := by
    rw [← Nat.card_eq_fintype_card]
    exact residueCard_adjoinRoot hφ
  have hne : ((X : Polynomial (ResidueField (AdjoinRoot φ)))
      ^ (residueCard O ^ φ.natDegree) - X) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero _ (one_lt_qpow hφ)
  have hle : keyRoots hφ
      ≤ ((X : Polynomial (ResidueField (AdjoinRoot φ)))
          ^ (residueCard O ^ φ.natDegree) - X).roots :=
    Polynomial.roots.le_of_dvd hne (keyRes_dvd_X_pow_sub_X hφ)
  rw [← hcardk', FiniteField.roots_X_pow_card_sub_X] at hle
  exact Multiset.nodup_of_le hle Finset.univ.nodup

/-- The residual key is the product of its `δ` distinct linear factors. -/
theorem keyRes_eq_prod (hφ : IsKey φ) :
    ((keyRoots hφ).map (fun ᾱ => X - C ᾱ)).prod = (φ.map (residue O)).map (resEmb hφ) := by
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq ((hφ.monic.map _).map _)
  rw [show ((φ.map (residue O)).map (resEmb hφ)).roots = keyRoots hφ from rfl,
    card_keyRoots hφ, natDegree_keyRes hφ]

/-- The residue of any root of the extended key is a residual root. -/
theorem mem_keyRoots_of_isRoot (hφ : IsKey φ) {β : AdjoinRoot φ}
    (hβ : (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot β) :
    residue (AdjoinRoot φ) β ∈ keyRoots hφ := by
  rw [keyRoots, ← map_map_residue_adjoinRoot hφ, mem_roots']
  refine ⟨((hφ.monic.map _).map _).ne_zero, ?_⟩
  show ((φ.map (algebraMap O (AdjoinRoot φ))).map (residue (AdjoinRoot φ))).eval
    (residue (AdjoinRoot φ) β) = 0
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hβ.eq_zero, map_zero]

/-- The adjoined root is a root of the extended key. -/
theorem isRoot_map_root :
    (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot (AdjoinRoot.root φ) := by
  show (φ.map (algebraMap O (AdjoinRoot φ))).eval (AdjoinRoot.root φ) = 0
  rw [Polynomial.eval_map, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- `θ̄` is a residual root. -/
theorem residue_root_mem_keyRoots (hφ : IsKey φ) :
    residue (AdjoinRoot φ) (AdjoinRoot.root φ) ∈ keyRoots hφ :=
  mem_keyRoots_of_isRoot hφ isRoot_map_root

/-- Separability of the residual key, in derivative form at each residual root. -/
private theorem eval_derivative_keyRes_ne_zero (hφ : IsKey φ)
    {ᾱ : ResidueField (AdjoinRoot φ)} (h : ᾱ ∈ keyRoots hφ) :
    (((φ.map (residue O)).map (resEmb hφ)).derivative).eval ᾱ ≠ 0 := by
  have hsep : ((φ.map (residue O)).map (resEmb hφ)).Separable :=
    (PerfectField.separable_of_irreducible hφ.irred).map
  obtain ⟨u, v, huv⟩ := hsep
  have hroot : ((φ.map (residue O)).map (resEmb hφ)).eval ᾱ = 0 := (mem_roots'.mp h).2
  intro hzero
  have hone := congrArg (eval ᾱ) huv
  rw [eval_add, eval_mul, eval_mul, hroot, hzero, mul_zero, mul_zero, add_zero,
    eval_one] at hone
  exact zero_ne_one hone

/-- **Hensel lifting of a residual root** to a genuine root of the key in `O'`. -/
theorem exists_isRoot_of_mem_keyRoots (hφ : IsKey φ) {ᾱ : ResidueField (AdjoinRoot φ)}
    (h : ᾱ ∈ keyRoots hφ) :
    ∃ β : AdjoinRoot φ, (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot β
      ∧ residue (AdjoinRoot φ) β = ᾱ := by
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := AdjoinRoot φ) ᾱ
  have hres : ∀ P : Polynomial O,
      residue (AdjoinRoot φ) ((P.map (algebraMap O (AdjoinRoot φ))).eval a₀)
        = ((P.map (residue O)).map (resEmb hφ)).eval ᾱ := by
    intro P
    rw [← map_map_residue_adjoinRoot hφ, ← ha₀]
    conv_rhs => rw [Polynomial.eval_map]
    exact (Polynomial.eval₂_at_apply _ _).symm
  have heval : (φ.map (algebraMap O (AdjoinRoot φ))).eval a₀
      ∈ maximalIdeal (AdjoinRoot φ) := by
    rw [← residue_eq_zero_iff, hres φ]
    exact (mem_roots'.mp h).2
  have hderiv : IsUnit ((φ.map (algebraMap O (AdjoinRoot φ))).derivative.eval a₀) := by
    by_contra hu
    have hmem : (φ.map (algebraMap O (AdjoinRoot φ))).derivative.eval a₀
        ∈ maximalIdeal (AdjoinRoot φ) := (mem_maximalIdeal _).mpr hu
    rw [← residue_eq_zero_iff, Polynomial.derivative_map, hres, ← Polynomial.derivative_map,
      ← Polynomial.derivative_map] at hmem
    exact eval_derivative_keyRes_ne_zero hφ h hmem
  obtain ⟨β, hβroot, hβsub⟩ :=
    HenselianLocalRing.is_henselian _ (hφ.monic.map _) a₀ heval hderiv
  refine ⟨β, hβroot, ?_⟩
  rw [← ha₀]
  exact Ideal.Quotient.eq.mpr hβsub

/-- **Uniqueness of the root at a given residue** (simple roots do not collide). -/
theorem isRoot_unique (hφ : IsKey φ) {β β' : AdjoinRoot φ}
    (hβ : (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot β)
    (hβ' : (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot β')
    (hres : residue (AdjoinRoot φ) β = residue (AdjoinRoot φ) β') : β = β' := by
  obtain ⟨ψ, hψ⟩ := Polynomial.dvd_iff_isRoot.mpr hβ
  have h0 : (β' - β) * ψ.eval β' = 0 := by
    have he := hβ'.eq_zero
    rw [hψ, eval_mul, eval_sub, eval_X, eval_C] at he
    exact he
  -- the cofactor is a unit at `β'`: its residue is the derivative of the residual key
  -- at the residual root
  have hmem : residue (AdjoinRoot φ) β ∈ keyRoots hφ := mem_keyRoots_of_isRoot hφ hβ
  have hψbar : ((φ.map (residue O)).map (resEmb hφ))
      = (X - C (residue (AdjoinRoot φ) β)) * (ψ.map (residue (AdjoinRoot φ))) := by
    rw [← map_map_residue_adjoinRoot hφ, hψ, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
  have hψroot : (ψ.map (residue (AdjoinRoot φ))).eval (residue (AdjoinRoot φ) β) ≠ 0 := by
    intro hzero
    apply eval_derivative_keyRes_ne_zero hφ hmem
    rw [hψbar, Polynomial.derivative_mul, eval_add, eval_mul, eval_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      sub_zero, eval_one, one_mul, hzero, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      add_zero]
  have hunit : IsUnit (ψ.eval β') := by
    by_contra hu
    apply hψroot
    have hmem' : ψ.eval β' ∈ maximalIdeal (AdjoinRoot φ) := (mem_maximalIdeal _).mpr hu
    rw [← residue_eq_zero_iff] at hmem'
    calc (ψ.map (residue (AdjoinRoot φ))).eval (residue (AdjoinRoot φ) β)
        = residue (AdjoinRoot φ) (ψ.eval β') := by
          rw [hres, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      _ = 0 := hmem'
  rcases mul_eq_zero.mp h0 with hz | hz
  · exact (sub_eq_zero.mp hz).symm
  · exact absurd hz hunit.ne_zero

end Roots

/-! ## §2 — the conjugation family: one `O`-algebra endomorphism per residual root -/

section Tau

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {φ : Polynomial O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- The canonical Hensel lift of a residual root (junk `0` off the root set). -/
noncomputable def rootLift (_hφ : IsKey φ) (ᾱ : ResidueField (AdjoinRoot φ)) :
    AdjoinRoot φ :=
  if h : ∃ β : AdjoinRoot φ, (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot β
      ∧ residue (AdjoinRoot φ) β = ᾱ then h.choose else 0

theorem rootLift_isRoot (hφ : IsKey φ) {ᾱ : ResidueField (AdjoinRoot φ)}
    (h : ᾱ ∈ keyRoots hφ) :
    (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot (rootLift hφ ᾱ) := by
  rw [rootLift, dif_pos (exists_isRoot_of_mem_keyRoots hφ h)]
  exact (exists_isRoot_of_mem_keyRoots hφ h).choose_spec.1

theorem rootLift_residue (hφ : IsKey φ) {ᾱ : ResidueField (AdjoinRoot φ)}
    (h : ᾱ ∈ keyRoots hφ) :
    residue (AdjoinRoot φ) (rootLift hφ ᾱ) = ᾱ := by
  rw [rootLift, dif_pos (exists_isRoot_of_mem_keyRoots hφ h)]
  exact (exists_isRoot_of_mem_keyRoots hφ h).choose_spec.2

/-- The lift is CANONICAL: every root is the lift of its own residue. -/
theorem rootLift_eq_of_isRoot (hφ : IsKey φ) {β : AdjoinRoot φ}
    (hβ : (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot β) :
    rootLift hφ (residue (AdjoinRoot φ) β) = β := by
  have hmem := mem_keyRoots_of_isRoot hφ hβ
  exact isRoot_unique hφ (rootLift_isRoot hφ hmem) hβ (rootLift_residue hφ hmem)

theorem rootLift_residue_root (hφ : IsKey φ) :
    rootLift hφ (residue (AdjoinRoot φ) (AdjoinRoot.root φ)) = AdjoinRoot.root φ :=
  rootLift_eq_of_isRoot hφ isRoot_map_root

theorem aeval_rootLift (hφ : IsKey φ) {ᾱ : ResidueField (AdjoinRoot φ)}
    (h : ᾱ ∈ keyRoots hφ) : (Polynomial.aeval (rootLift hφ ᾱ)) φ = 0 := by
  have h2 := (rootLift_isRoot hφ h).eq_zero
  rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h2

/-- **The conjugation endomorphism at a residual root**: the `O`-algebra map of the
adjoined ring sending the adjoined root to the Hensel lift of the given residual root
(junk: the identity). -/
noncomputable def tau (hφ : IsKey φ) (ᾱ : ResidueField (AdjoinRoot φ)) :
    AdjoinRoot φ →ₐ[O] AdjoinRoot φ :=
  if h : (Polynomial.aeval (rootLift hφ ᾱ)) φ = 0
  then AdjoinRoot.liftAlgHom φ (Algebra.ofId O (AdjoinRoot φ)) (rootLift hφ ᾱ)
    (by rwa [Polynomial.aeval_def] at h)
  else AlgHom.id O (AdjoinRoot φ)

theorem tau_apply_root (hφ : IsKey φ) {ᾱ : ResidueField (AdjoinRoot φ)}
    (h : ᾱ ∈ keyRoots hφ) :
    tau hφ ᾱ (AdjoinRoot.root φ) = rootLift hφ ᾱ := by
  rw [tau, dif_pos (aeval_rootLift hφ h)]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Every `O`-algebra endomorphism moves roots of the extended key to roots. -/
theorem isRoot_algHom (ψ : AdjoinRoot φ →ₐ[O] AdjoinRoot φ) {γ : AdjoinRoot φ}
    (hγ : (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot γ) :
    (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot (ψ γ) := by
  have h : (ψ : AdjoinRoot φ →+* AdjoinRoot φ)
      ((φ.map (algebraMap O (AdjoinRoot φ))).eval γ) = 0 := by
    rw [hγ.eq_zero, map_zero]
  show (φ.map (algebraMap O (AdjoinRoot φ))).eval (ψ γ) = 0
  rw [Polynomial.eval_map] at h ⊢
  rw [Polynomial.hom_eval₂] at h
  rwa [AlgHom.comp_algebraMap] at h

/-- The conjugations are local homomorphisms (`τ(𝔪·O') ⊆ 𝔪·O'`). -/
theorem isLocalHom_tau (hφ : IsKey φ) (ᾱ : ResidueField (AdjoinRoot φ)) :
    IsLocalHom (tau hφ ᾱ).toRingHom := by
  constructor
  intro a ha
  by_contra hu
  have hmem : a ∈ maximalIdeal (AdjoinRoot φ) := (mem_maximalIdeal a).mpr hu
  rw [adjoinRoot_maximalIdeal_eq hφ] at hmem
  have hcomp : ((tau hφ ᾱ).toRingHom).comp (algebraMap O (AdjoinRoot φ))
      = algebraMap O (AdjoinRoot φ) := RingHom.ext fun r => (tau hφ ᾱ).commutes r
  have h2 : (tau hφ ᾱ) a ∈ (maximalIdeal O).map
      ((tau hφ ᾱ).toRingHom.comp (algebraMap O (AdjoinRoot φ))) := by
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hmem
  rw [hcomp, ← adjoinRoot_maximalIdeal_eq hφ] at h2
  exact (mem_maximalIdeal _).mp h2 ha

/-- The residual action of the conjugation at `ᾱ`. -/
noncomputable def resTau (hφ : IsKey φ) (ᾱ : ResidueField (AdjoinRoot φ)) :
    ResidueField (AdjoinRoot φ) →+* ResidueField (AdjoinRoot φ) :=
  letI := isLocalHom_tau hφ ᾱ
  IsLocalRing.ResidueField.map (tau hφ ᾱ).toRingHom

theorem resTau_residue (hφ : IsKey φ) (ᾱ : ResidueField (AdjoinRoot φ)) (x : AdjoinRoot φ) :
    resTau hφ ᾱ (residue (AdjoinRoot φ) x) = residue (AdjoinRoot φ) (tau hφ ᾱ x) :=
  letI := isLocalHom_tau hφ ᾱ
  IsLocalRing.ResidueField.map_residue _ x

/-- The residual action fixes the base residue field pointwise. -/
theorem resTau_resEmb (hφ : IsKey φ) (ᾱ : ResidueField (AdjoinRoot φ))
    (c : ResidueField O) : resTau hφ ᾱ (resEmb hφ c) = resEmb hφ c := by
  obtain ⟨a, rfl⟩ := residue_surjective (R := O) c
  rw [resEmb_residue, resTau_residue, AlgHom.commutes]

theorem resTau_apply_of_mem (hφ : IsKey φ) {ᾱ : ResidueField (AdjoinRoot φ)}
    (h : ᾱ ∈ keyRoots hφ) :
    resTau hφ ᾱ (residue (AdjoinRoot φ) (AdjoinRoot.root φ)) = ᾱ := by
  rw [resTau_residue, tau_apply_root hφ h, rootLift_residue hφ h]

/-- The residual key is fixed by every residual conjugation. -/
theorem keyRes_map_resTau (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ)) :
    ((φ.map (residue O)).map (resEmb hφ)).map (resTau hφ β)
      = (φ.map (residue O)).map (resEmb hφ) := by
  rw [Polynomial.map_map]
  have hcomp : (resTau hφ β).comp (resEmb hφ) = resEmb hφ :=
    RingHom.ext fun c => resTau_resEmb hφ β c
  rw [hcomp]

/-- The residual conjugations permute the residual roots. -/
theorem mem_keyRoots_resTau (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    {γ : ResidueField (AdjoinRoot φ)} (hγ : γ ∈ keyRoots hφ) :
    resTau hφ β γ ∈ keyRoots hφ := by
  have hroot : ((φ.map (residue O)).map (resEmb hφ)).IsRoot γ := (mem_roots'.mp hγ).2
  have h2 := hroot.map (f := resTau hφ β)
  rw [keyRes_map_resTau] at h2
  exact mem_roots'.mpr ⟨((hφ.monic.map _).map _).ne_zero, h2⟩

/-- The conjugation at the residue of the adjoined root is the identity. -/
theorem tau_residue_root (hφ : IsKey φ) :
    tau hφ (residue (AdjoinRoot φ) (AdjoinRoot.root φ)) = AlgHom.id O (AdjoinRoot φ) := by
  apply AdjoinRoot.algHom_ext
  rw [tau_apply_root hφ (residue_root_mem_keyRoots hφ), rootLift_residue_root hφ,
    AlgHom.id_apply]

/-- **Composition closure**: the conjugations compose along the residual action. -/
theorem tau_comp (hφ : IsKey φ) {ᾱ β : ResidueField (AdjoinRoot φ)}
    (hᾱ : ᾱ ∈ keyRoots hφ) :
    (tau hφ β).comp (tau hφ ᾱ) = tau hφ (resTau hφ β ᾱ) := by
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, tau_apply_root hφ hᾱ,
    tau_apply_root hφ (mem_keyRoots_resTau hφ β hᾱ)]
  have hroot : (φ.map (algebraMap O (AdjoinRoot φ))).IsRoot (tau hφ β (rootLift hφ ᾱ)) :=
    isRoot_algHom _ (rootLift_isRoot hφ hᾱ)
  have hres : residue (AdjoinRoot φ) (tau hφ β (rootLift hφ ᾱ)) = resTau hφ β ᾱ := by
    rw [← resTau_residue, rootLift_residue hφ hᾱ]
  rw [← hres]
  exact (rootLift_eq_of_isRoot hφ hroot).symm

/-- The residual action is transitive from the residue of the adjoined root; combined
with injectivity, every residual root is reachable, so each conjugation has a section. -/
theorem exists_resTau_eq (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    {δ : ResidueField (AdjoinRoot φ)} (hδ : δ ∈ keyRoots hφ) :
    ∃ γ ∈ keyRoots hφ, resTau hφ β γ = δ := by
  classical
  have himg : (keyRoots hφ).toFinset.image (resTau hφ β) = (keyRoots hφ).toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Multiset.mem_toFinset.mpr (mem_keyRoots_resTau hφ β (Multiset.mem_toFinset.mp hy))
    · rw [Finset.card_image_of_injective _ (resTau hφ β).injective]
  have hmem : δ ∈ (keyRoots hφ).toFinset.image (resTau hφ β) := by
    rw [himg]
    exact Multiset.mem_toFinset.mpr hδ
  obtain ⟨γ, hγ, h⟩ := Finset.mem_image.mp hmem
  exact ⟨γ, Multiset.mem_toFinset.mp hγ, h⟩

/-- The image of an irreducible of `O` stays irreducible in the unramified extension
(it generates the maximal ideal). -/
theorem irreducible_algebraMap_adjoinRoot (hφ : IsKey φ) {π : O} (hπ : Irreducible π) :
    Irreducible (algebraMap O (AdjoinRoot φ) π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    adjoinRoot_maximalIdeal_eq hφ, hπ.maximalIdeal_eq, Ideal.map_span]
  simp

/-- The conjugations are injective. -/
theorem tau_injective (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ)) :
    Function.Injective (tau hφ β) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ' := irreducible_algebraMap_adjoinRoot hφ hπ
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ'
  rw [hxu, map_mul, map_pow, AlgHom.commutes] at hx
  rcases mul_eq_zero.mp hx with hz | hz
  · exact (u.isUnit.map (tau hφ β)).ne_zero hz
  · exact pow_ne_zero n hπ'.ne_zero hz

/-- **The conjugations are automorphisms** (a two-sided section exists through the
transitive residual action). -/
theorem tau_bijective (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ)) :
    Function.Bijective (tau hφ β) := by
  refine ⟨tau_injective hφ β, ?_⟩
  obtain ⟨γ, hγ, hγeq⟩ := exists_resTau_eq hφ β (residue_root_mem_keyRoots hφ)
  have hcomp : (tau hφ β).comp (tau hφ γ) = AlgHom.id O (AdjoinRoot φ) := by
    rw [tau_comp hφ hγ, hγeq, tau_residue_root hφ]
  intro y
  refine ⟨tau hφ γ y, ?_⟩
  rw [← AlgHom.comp_apply, hcomp, AlgHom.id_apply]

/-- Polynomials with base coefficients are fixed by the conjugations. -/
theorem map_tau_map_algebraMap (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    (P : Polynomial O) :
    (P.map (algebraMap O (AdjoinRoot φ))).map (tau hφ β).toRingHom
      = P.map (algebraMap O (AdjoinRoot φ)) := by
  have hcomp : ((tau hφ β).toRingHom).comp (algebraMap O (AdjoinRoot φ))
      = algebraMap O (AdjoinRoot φ) := RingHom.ext fun r => (tau hφ β).commutes r
  rw [Polynomial.map_map, hcomp]

/-- Reduction intertwines the conjugation and its residual action, at the level of
polynomial maps. -/
theorem map_resTau_map_residue (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    (P : Polynomial (AdjoinRoot φ)) :
    (P.map (tau hφ β).toRingHom).map (residue (AdjoinRoot φ))
      = (P.map (residue (AdjoinRoot φ))).map (resTau hφ β) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  have hcomp : (residue (AdjoinRoot φ)).comp (tau hφ β).toRingHom
      = (resTau hφ β).comp (residue (AdjoinRoot φ)) :=
    RingHom.ext fun x => (resTau_residue hφ β x).symm
  rw [hcomp]

end Tau

/-! ## §3 — invariants: an element fixed by every conjugation lies in the base -/

section Invariants

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {φ : Polynomial O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- Every element of `k'` is a base-coefficient polynomial value at `θ̄`, of degree
below `δ`. -/
theorem exists_repr_lt (hφ : IsKey φ) (x : ResidueField (AdjoinRoot φ)) :
    ∃ P : Polynomial (ResidueField O), P.degree < (φ.natDegree : WithBot ℕ) ∧
      (P.map (resEmb hφ)).eval (residue (AdjoinRoot φ) (AdjoinRoot.root φ)) = x := by
  obtain ⟨w, rfl⟩ := residue_surjective (R := AdjoinRoot φ) x
  obtain ⟨W, rfl⟩ := AdjoinRoot.mk_surjective w
  refine ⟨(W %ₘ φ).map (residue O), ?_, ?_⟩
  · refine lt_of_le_of_lt Polynomial.degree_map_le ?_
    have h := Polynomial.degree_modByMonic_lt W hφ.monic
    rwa [Polynomial.degree_eq_natDegree hφ.monic.ne_zero] at h
  · rw [← map_map_residue_adjoinRoot hφ, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    have heval : ((W %ₘ φ).map (algebraMap O (AdjoinRoot φ))).eval (AdjoinRoot.root φ)
        = AdjoinRoot.mk φ W := by
      rw [Polynomial.eval_map, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
      conv_rhs => rw [← Polynomial.modByMonic_add_div W φ]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [heval]

/-- Ring homomorphisms out of the residue field commute with base-coefficient
polynomial evaluation. -/
theorem resTau_eval (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    (P : Polynomial (ResidueField O)) (x : ResidueField (AdjoinRoot φ)) :
    resTau hφ β ((P.map (resEmb hφ)).eval x)
      = (P.map (resEmb hφ)).eval (resTau hφ β x) := by
  rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.eval_map]
  have hcomp : (resTau hφ β).comp (resEmb hφ) = resEmb hφ :=
    RingHom.ext fun c => resTau_resEmb hφ β c
  rw [hcomp]

/-- **The residue-level invariants**: a residue fixed by every residual conjugation
lies in the base residue field (a polynomial of degree `< δ` with one value at `δ`
distinct points is constant). -/
theorem exists_resEmb_eq_of_forall_resTau (hφ : IsKey φ)
    {x : ResidueField (AdjoinRoot φ)}
    (hx : ∀ β ∈ keyRoots hφ, resTau hφ β x = x) :
    ∃ c : ResidueField O, resEmb hφ c = x := by
  obtain ⟨P, hdeg, hval⟩ := exists_repr_lt hφ x
  set Q : Polynomial (ResidueField (AdjoinRoot φ)) := P.map (resEmb hφ) - C x with hQ
  have hroots : ∀ β ∈ keyRoots hφ, Q.IsRoot β := by
    intro β hβ
    have hb : (P.map (resEmb hφ)).eval β = x := by
      rw [← resTau_apply_of_mem hφ hβ, ← resTau_eval hφ β, hval, hx β hβ]
    show Q.eval β = 0
    rw [hQ, Polynomial.eval_sub, hb, Polynomial.eval_C, sub_self]
  have hQ0 : Q = 0 := by
    by_contra hne
    have hle : keyRoots hφ ≤ Q.roots := by
      rw [Multiset.le_iff_count]
      intro a
      by_cases ha : a ∈ keyRoots hφ
      · calc Multiset.count a (keyRoots hφ) ≤ 1 :=
              (Multiset.nodup_iff_count_le_one.mp (nodup_keyRoots hφ)) a
          _ ≤ Multiset.count a Q.roots :=
              Multiset.one_le_count_iff_mem.mpr (mem_roots'.mpr ⟨hne, hroots a ha⟩)
      · rw [Multiset.count_eq_zero_of_notMem ha]
        omega
    have hcard : φ.natDegree ≤ Multiset.card Q.roots := by
      rw [← card_keyRoots hφ]
      exact Multiset.card_le_card hle
    have hdegQ : Q.degree < (φ.natDegree : WithBot ℕ) := by
      rw [hQ]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
      rw [max_lt_iff]
      constructor
      · exact lt_of_le_of_lt Polynomial.degree_map_le hdeg
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hφ.pos)
    have hnd : Q.natDegree < φ.natDegree :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hdegQ
    have hcr := Polynomial.card_roots' Q
    omega
  have hPC : P.map (resEmb hφ) = C x := by
    rw [hQ] at hQ0
    exact sub_eq_zero.mp hQ0
  refine ⟨P.coeff 0, ?_⟩
  have := congrArg (fun R => Polynomial.coeff R 0) hPC
  simpa [Polynomial.coeff_map] using this

/-- The structure map is injective. -/
theorem algebraMap_adjoinRoot_injective (hφ : IsKey φ) :
    Function.Injective (algebraMap O (AdjoinRoot φ)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp hφ.pos))

/-- **THE INVARIANTS THEOREM**: an element of the unramified extension fixed by every
conjugation lies in the base ring — residue level by the degree count, then the
coordinate Krull induction on the power basis. -/
theorem exists_algebraMap_eq_of_forall_tau (hφ : IsKey φ) {x : AdjoinRoot φ}
    (hx : ∀ β ∈ keyRoots hφ, tau hφ β x = x) :
    ∃ a : O, algebraMap O (AdjoinRoot φ) a = x := by
  classical
  set pb := AdjoinRoot.powerBasis' hφ.monic with hpb
  have h0 : 0 < pb.dim := hφ.pos
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- the zeroth basis vector is 1
  have hone : pb.basis ⟨0, h0⟩ = 1 := by
    rw [PowerBasis.coe_basis]
    exact pow_zero _
  -- the algebraMap coordinates at nonzero indices vanish
  have hcoord0 : ∀ (a : O) (j : Fin pb.dim), (j : ℕ) ≠ 0 →
      pb.basis.repr (algebraMap O (AdjoinRoot φ) a) j = 0 := by
    intro a j hj
    rw [Algebra.algebraMap_eq_smul_one, ← hone, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply]
    rw [if_neg (by intro h; exact hj (by rw [← h]))]
    simp
  -- the Krull induction: high coordinates of invariant elements sink into `𝔪^m`
  have hcoord : ∀ (m : ℕ) (y : AdjoinRoot φ), (∀ β ∈ keyRoots hφ, tau hφ β y = y) →
      ∀ j : Fin pb.dim, (j : ℕ) ≠ 0 → pb.basis.repr y j ∈ (maximalIdeal O) ^ m := by
    intro m
    induction m with
    | zero =>
      intro y _ j _
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ m ih =>
      intro y hy j hj
      have hyres : ∀ β ∈ keyRoots hφ, resTau hφ β (residue (AdjoinRoot φ) y)
          = residue (AdjoinRoot φ) y := by
        intro β hβ
        rw [resTau_residue, hy β hβ]
      obtain ⟨c, hc⟩ := exists_resEmb_eq_of_forall_resTau hφ hyres
      obtain ⟨a, ha⟩ := residue_surjective (R := O) c
      have hmem : y - algebraMap O (AdjoinRoot φ) a ∈ maximalIdeal (AdjoinRoot φ) := by
        rw [← residue_eq_zero_iff, map_sub]
        have h2 : residue (AdjoinRoot φ) (algebraMap O (AdjoinRoot φ) a)
            = residue (AdjoinRoot φ) y := by
          rw [← resEmb_residue hφ, ha, hc]
        rw [h2, sub_self]
      rw [(irreducible_algebraMap_adjoinRoot hφ hπ).maximalIdeal_eq,
        Ideal.mem_span_singleton] at hmem
      obtain ⟨z, hz⟩ := hmem
      have hzfix : ∀ β ∈ keyRoots hφ, tau hφ β z = z := by
        intro β hβ
        have h1 : algebraMap O (AdjoinRoot φ) π * tau hφ β z
            = algebraMap O (AdjoinRoot φ) π * z := by
          calc algebraMap O (AdjoinRoot φ) π * tau hφ β z
              = tau hφ β (algebraMap O (AdjoinRoot φ) π * z) := by
                rw [map_mul, AlgHom.commutes]
            _ = tau hφ β (y - algebraMap O (AdjoinRoot φ) a) := by rw [← hz]
            _ = y - algebraMap O (AdjoinRoot φ) a := by
                rw [map_sub, hy β hβ, AlgHom.commutes]
            _ = algebraMap O (AdjoinRoot φ) π * z := hz
        exact mul_left_cancel₀
          (irreducible_algebraMap_adjoinRoot hφ hπ).ne_zero h1
      have hy' : y = π • z + algebraMap O (AdjoinRoot φ) a := by
        rw [Algebra.smul_def, ← hz]
        ring
      have hrepr : pb.basis.repr y j = π * pb.basis.repr z j := by
        rw [hy', map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
          hcoord0 a j hj, add_zero, smul_eq_mul]
      rw [hrepr, pow_succ']
      exact Ideal.mul_mem_mul
        (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π)
        (ih z hzfix j hj)
  -- Krull intersection: the high coordinates vanish
  have hzero : ∀ j : Fin pb.dim, (j : ℕ) ≠ 0 → pb.basis.repr x j = 0 := by
    intro j hj
    have hbot : (⨅ m : ℕ, (maximalIdeal O) ^ m) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ (Ideal.IsMaximal.ne_top inferInstance)
    have hmem : pb.basis.repr x j ∈ (⨅ m : ℕ, (maximalIdeal O) ^ m) := by
      rw [Submodule.mem_iInf]
      exact fun m => hcoord m x hx j hj
    rw [hbot] at hmem
    exact hmem
  -- assemble: `x` is its zeroth coordinate
  refine ⟨pb.basis.repr x ⟨0, h0⟩, ?_⟩
  have hx' : x = ∑ i, pb.basis.repr x i • pb.basis i := (pb.basis.sum_repr x).symm
  rw [Algebra.algebraMap_eq_smul_one]
  conv_rhs => rw [hx']
  rw [Finset.sum_eq_single (⟨0, h0⟩ : Fin pb.dim)
    (fun j _ hjne => by rw [hzero j (fun h => hjne (Fin.ext h)), zero_smul])
    (fun h => absurd (Finset.mem_univ _) h), hone]

end Invariants

/-! ## §4 — the Hensel blocks and their conjugacy -/

section Blocks

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {φ : Polynomial O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- Distinct linear polynomials over a field are coprime. -/
private theorem isCoprime_X_sub_C_of_ne {K : Type*} [Field K] {a b : K} (hab : a ≠ b) :
    IsCoprime ((X : Polynomial K) - C a) (X - C b) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  refine ⟨C (b - a)⁻¹, -(C (b - a)⁻¹), ?_⟩
  have hC : (C (b - a)⁻¹ : Polynomial K) * C (b - a) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hne, C_1]
  calc C (b - a)⁻¹ * ((X : Polynomial K) - C a) + -(C (b - a)⁻¹) * (X - C b)
      = C (b - a)⁻¹ * (C b - C a) := by ring
    _ = C (b - a)⁻¹ * C (b - a) := by rw [← C_sub]
    _ = 1 := hC

/-- Multiset products over `keyRoots` read as `Finset` products over its
(nodup) `toFinset`. -/
private theorem prod_map_keyRoots (hφ : IsKey φ) {M : Type*} [CommMonoid M]
    (f : ResidueField (AdjoinRoot φ) → M) :
    ((keyRoots hφ).map f).prod = ∏ ᾱ ∈ (keyRoots hφ).toFinset, f ᾱ := by
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (nodup_keyRoots hφ)]

/-- The residual of a `p^e`-stratum lift over the extension, in split form. -/
theorem map_residue_map_algebraMap_pow (hφ : IsKey φ) {e : ℕ} {F : Polynomial O}
    (hres : F.map (residue O) = (φ.map (residue O)) ^ e) :
    (F.map (algebraMap O (AdjoinRoot φ))).map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset, (X - C ᾱ) ^ e := by
  rw [map_map_residue_adjoinRoot hφ, hres, Polynomial.map_pow, ← keyRes_eq_prod hφ,
    prod_map_keyRoots hφ, ← Finset.prod_pow]

/-- **The block family**: any lift of the `p^e` stratum splits over the extension into
one monic block per residual root, the block at `ᾱ` reducing to `(X − ᾱ)^e`. -/
theorem exists_block_family (hφ : IsKey φ) {e : ℕ} {F : Polynomial O} (hF : F.Monic)
    (hres : F.map (residue O) = (φ.map (residue O)) ^ e) :
    ∃ g : ResidueField (AdjoinRoot φ) → Polynomial (AdjoinRoot φ),
      (∀ ᾱ ∈ (keyRoots hφ).toFinset, (g ᾱ).Monic) ∧
      F.map (algebraMap O (AdjoinRoot φ)) = ∏ ᾱ ∈ (keyRoots hφ).toFinset, g ᾱ ∧
      (∀ ᾱ ∈ (keyRoots hφ).toFinset,
        (g ᾱ).map (residue (AdjoinRoot φ)) = (X - C ᾱ) ^ e) ∧
      (∀ ᾱ ∈ (keyRoots hφ).toFinset, (g ᾱ).natDegree = e) := by
  obtain ⟨g, hmon, hfeq, hgr, hgd⟩ := exists_monic_factorization_finset
    ((keyRoots hφ).toFinset) (hF.map (algebraMap O (AdjoinRoot φ)))
    (fun ᾱ => (X - C ᾱ) ^ e)
    (fun ᾱ _ => (monic_X_sub_C ᾱ).pow e)
    (fun ᾱ _ β _ hne => (isCoprime_X_sub_C_of_ne hne).pow)
    (map_residue_map_algebraMap_pow hφ hres)
  refine ⟨g, hmon, hfeq, hgr, fun ᾱ hᾱ => ?_⟩
  rw [hgd ᾱ hᾱ, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

/-- **Uniqueness at a root**: any two-block factorization pinning the `β`-block against
the product of the others agrees with the family. -/
theorem block_family_eq_at (hφ : IsKey φ) {e : ℕ} {F' : Polynomial (AdjoinRoot φ)}
    {g : ResidueField (AdjoinRoot φ) → Polynomial (AdjoinRoot φ)}
    (hmon : ∀ ᾱ ∈ (keyRoots hφ).toFinset, (g ᾱ).Monic)
    (hfeq : F' = ∏ ᾱ ∈ (keyRoots hφ).toFinset, g ᾱ)
    (hgr : ∀ ᾱ ∈ (keyRoots hφ).toFinset,
      (g ᾱ).map (residue (AdjoinRoot φ)) = (X - C ᾱ) ^ e)
    {β : ResidueField (AdjoinRoot φ)} (hβ : β ∈ keyRoots hφ)
    {B R : Polynomial (AdjoinRoot φ)} (hB : B.Monic) (hR : R.Monic)
    (hprod : F' = B * R)
    (hBres : B.map (residue (AdjoinRoot φ)) = (X - C β) ^ e)
    (hRres : R.map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase β, (X - C ᾱ) ^ e) :
    B = g β ∧ R = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase β, g ᾱ := by
  have hβ' : β ∈ (keyRoots hφ).toFinset := Multiset.mem_toFinset.mpr hβ
  have hpeel : F' = g β * ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase β, g ᾱ := by
    rw [hfeq, Finset.mul_prod_erase _ _ hβ']
  have hRmon : (∏ ᾱ ∈ (keyRoots hφ).toFinset.erase β, g ᾱ).Monic :=
    monic_prod_of_monic _ _ fun ᾱ hᾱ => hmon ᾱ (Finset.mem_of_mem_erase hᾱ)
  have hRres' : (∏ ᾱ ∈ (keyRoots hφ).toFinset.erase β, g ᾱ).map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase β, (X - C ᾱ) ^ e := by
    rw [Polynomial.map_prod]
    exact Finset.prod_congr rfl fun ᾱ hᾱ => hgr ᾱ (Finset.mem_of_mem_erase hᾱ)
  have hcop : IsCoprime ((X - C β) ^ e : Polynomial (ResidueField (AdjoinRoot φ)))
      (∏ ᾱ ∈ (keyRoots hφ).toFinset.erase β, (X - C ᾱ) ^ e) := by
    apply IsCoprime.prod_right
    intro ᾱ hᾱ
    exact (isCoprime_X_sub_C_of_ne (Ne.symm (Finset.ne_of_mem_erase hᾱ))).pow
  exact monic_factorization_unique hB hR (hmon β hβ') hRmon
    ((monic_X_sub_C β).pow e) (monic_prod_of_monic _ _ fun ᾱ _ => (monic_X_sub_C ᾱ).pow e)
    hcop hBres hRres (hgr β hβ') hRres' (by rw [← hprod, ← hpeel])

/-- The residual conjugations permute the residual root set. -/
theorem image_resTau_toFinset (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ)) :
    (keyRoots hφ).toFinset.image (resTau hφ β) = (keyRoots hφ).toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr (mem_keyRoots_resTau hφ β (Multiset.mem_toFinset.mp hy))
  · rw [Finset.card_image_of_injective _ (resTau hφ β).injective]

theorem image_resTau_erase (hφ : IsKey φ) {β : ResidueField (AdjoinRoot φ)}
    (hβ : β ∈ keyRoots hφ) :
    ((keyRoots hφ).toFinset.erase
        (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).image (resTau hφ β)
      = (keyRoots hφ).toFinset.erase β := by
  rw [Finset.image_erase (resTau hφ β).injective, image_resTau_toFinset hφ β,
    resTau_apply_of_mem hφ hβ]

/-- **Block conjugacy**: for a base-rational lift, the family's `β`-block is the
`τ_β`-image of the `θ̄`-block. -/
theorem block_family_conj (hφ : IsKey φ) {e : ℕ} {F : Polynomial O}
    {g : ResidueField (AdjoinRoot φ) → Polynomial (AdjoinRoot φ)}
    (hmon : ∀ ᾱ ∈ (keyRoots hφ).toFinset, (g ᾱ).Monic)
    (hfeq : F.map (algebraMap O (AdjoinRoot φ)) = ∏ ᾱ ∈ (keyRoots hφ).toFinset, g ᾱ)
    (hgr : ∀ ᾱ ∈ (keyRoots hφ).toFinset,
      (g ᾱ).map (residue (AdjoinRoot φ)) = (X - C ᾱ) ^ e)
    {β : ResidueField (AdjoinRoot φ)} (hβ : β ∈ keyRoots hφ) :
    g β = (g (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).map (tau hφ β).toRingHom := by
  have hθmem : residue (AdjoinRoot φ) (AdjoinRoot.root φ) ∈ keyRoots hφ :=
    residue_root_mem_keyRoots hφ
  have hθ' : residue (AdjoinRoot φ) (AdjoinRoot.root φ) ∈ (keyRoots hφ).toFinset :=
    Multiset.mem_toFinset.mpr hθmem
  have hpeel : F.map (algebraMap O (AdjoinRoot φ))
      = g (residue (AdjoinRoot φ) (AdjoinRoot.root φ))
        * ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
            (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), g ᾱ := by
    rw [hfeq, Finset.mul_prod_erase _ _ hθ']
  -- the τ_β image of the θ̄-peel is a second factorization of the SAME polynomial
  have hconj : F.map (algebraMap O (AdjoinRoot φ))
      = (g (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).map (tau hφ β).toRingHom
        * ((∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
            (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), g ᾱ).map (tau hφ β).toRingHom) := by
    conv_lhs => rw [← map_tau_map_algebraMap hφ β F, hpeel]
    rw [Polynomial.map_mul]
  have hBres : ((g (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).map
        (tau hφ β).toRingHom).map (residue (AdjoinRoot φ)) = (X - C β) ^ e := by
    rw [map_resTau_map_residue hφ, hgr _ hθ', Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, resTau_apply_of_mem hφ hβ]
  have hRres : ((∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
        (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), g ᾱ).map
          (tau hφ β).toRingHom).map (residue (AdjoinRoot φ))
      = ∏ γ ∈ (keyRoots hφ).toFinset.erase β, (X - C γ) ^ e := by
    rw [map_resTau_map_residue hφ, Polynomial.map_prod, Polynomial.map_prod]
    calc ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
          (residue (AdjoinRoot φ) (AdjoinRoot.root φ)),
            (((g ᾱ).map (residue (AdjoinRoot φ))).map (resTau hφ β))
        = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
            (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C (resTau hφ β ᾱ)) ^ e := by
          refine Finset.prod_congr rfl fun ᾱ hᾱ => ?_
          rw [hgr ᾱ (Finset.mem_of_mem_erase hᾱ), Polynomial.map_pow, Polynomial.map_sub,
            Polynomial.map_X, Polynomial.map_C]
      _ = ∏ γ ∈ ((keyRoots hφ).toFinset.erase
            (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).image (resTau hφ β),
              (X - C γ) ^ e :=
          (Finset.prod_image
            (s := (keyRoots hφ).toFinset.erase
              (residue (AdjoinRoot φ) (AdjoinRoot.root φ)))
            (g := ⇑(resTau hφ β))
            (f := fun γ => (X - C γ) ^ e)
            (fun x _ y _ h => (resTau hφ β).injective h)).symm
      _ = ∏ γ ∈ (keyRoots hφ).toFinset.erase β, (X - C γ) ^ e := by
          rw [image_resTau_erase hφ hβ]
  exact ((block_family_eq_at hφ hmon hfeq hgr hβ
    ((hmon _ hθ').map _) ((monic_prod_of_monic _ _ fun ᾱ hᾱ =>
      hmon ᾱ (Finset.mem_of_mem_erase hᾱ)).map _)
    hconj hBres hRres).1).symm

/-- **THE CONJUGACY DECOMPOSITION**: a base-rational lift of the `p^e` stratum is the
product of the `τ`-conjugates of its `θ̄`-block. -/
theorem map_algebraMap_eq_prod_tau (hφ : IsKey φ) {e : ℕ} {F : Polynomial O}
    (hF : F.Monic) (hres : F.map (residue O) = (φ.map (residue O)) ^ e)
    {B R : Polynomial (AdjoinRoot φ)} (hB : B.Monic) (hR : R.Monic)
    (hprod : F.map (algebraMap O (AdjoinRoot φ)) = B * R)
    (hBres : B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e)
    (hRres : R.map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
          (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e) :
    F.map (algebraMap O (AdjoinRoot φ))
      = ∏ β ∈ (keyRoots hφ).toFinset, B.map (tau hφ β).toRingHom := by
  obtain ⟨g, hmon, hfeq, hgr, hgd⟩ := exists_block_family hφ hF hres
  have hBθ : B = g (residue (AdjoinRoot φ) (AdjoinRoot.root φ)) :=
    (block_family_eq_at hφ hmon hfeq hgr (residue_root_mem_keyRoots hφ)
      hB hR hprod hBres hRres).1
  rw [hfeq]
  refine Finset.prod_congr rfl fun β hβ' => ?_
  rw [block_family_conj hφ hmon hfeq hgr (Multiset.mem_toFinset.mp hβ'), ← hBθ]

/-- **Block existence**, packaged with the pinned cofactor residual. -/
theorem exists_block (hφ : IsKey φ) {e : ℕ} {F : Polynomial O} (hF : F.Monic)
    (hres : F.map (residue O) = (φ.map (residue O)) ^ e) :
    ∃ B R : Polynomial (AdjoinRoot φ), B.Monic ∧ R.Monic ∧ B.natDegree = e ∧
      F.map (algebraMap O (AdjoinRoot φ)) = B * R ∧
      B.map (residue (AdjoinRoot φ))
        = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e ∧
      R.map (residue (AdjoinRoot φ))
        = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
            (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e := by
  obtain ⟨g, hmon, hfeq, hgr, hgd⟩ := exists_block_family hφ hF hres
  have hθ' : residue (AdjoinRoot φ) (AdjoinRoot.root φ) ∈ (keyRoots hφ).toFinset :=
    Multiset.mem_toFinset.mpr (residue_root_mem_keyRoots hφ)
  refine ⟨g _, ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
      (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), g ᾱ,
    hmon _ hθ', monic_prod_of_monic _ _ fun ᾱ hᾱ => hmon ᾱ (Finset.mem_of_mem_erase hᾱ),
    hgd _ hθ', ?_, hgr _ hθ', ?_⟩
  · rw [hfeq, Finset.mul_prod_erase _ _ hθ']
  · rw [Polynomial.map_prod]
    exact Finset.prod_congr rfl fun ᾱ hᾱ => hgr ᾱ (Finset.mem_of_mem_erase hᾱ)

end Blocks

/-! ## §5 — level exactness, the class correspondence, and the named descent law -/

section Descent

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {φ : Polynomial O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- The zeroth power-basis coordinate of the unramified extension. -/
noncomputable def coord0 (hφ : IsKey φ) (x : AdjoinRoot φ) : O :=
  (AdjoinRoot.powerBasis' hφ.monic).basis.repr x ⟨0, hφ.pos⟩

theorem coord0_algebraMap (hφ : IsKey φ) (a : O) :
    coord0 hφ (algebraMap O (AdjoinRoot φ) a) = a := by
  have hone : (AdjoinRoot.powerBasis' hφ.monic).basis ⟨0, hφ.pos⟩ = 1 := by
    rw [PowerBasis.coe_basis]
    exact pow_zero _
  rw [coord0, Algebra.algebraMap_eq_smul_one, ← hone, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem coord0_smul (hφ : IsKey φ) (a : O) (x : AdjoinRoot φ) :
    coord0 hφ (algebraMap O (AdjoinRoot φ) a * x) = a * coord0 hφ x := by
  rw [coord0, coord0, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- **Congruence descent**: a base element in the extension's `N`-th power of the
maximal ideal already lies in the base's. -/
theorem mem_pow_maximalIdeal_of_algebraMap (hφ : IsKey φ) {N : ℕ} {a : O}
    (h : algebraMap O (AdjoinRoot φ) a ∈ (maximalIdeal (AdjoinRoot φ)) ^ N) :
    a ∈ (maximalIdeal O) ^ N := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [adjoinRoot_maximalIdeal_eq hφ, ← Ideal.map_pow, hπ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.map_span] at h
  simp only [Set.image_singleton, Ideal.mem_span_singleton] at h
  obtain ⟨z, hz⟩ := h
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨coord0 hφ z, ?_⟩
  have h2 : coord0 hφ (algebraMap O (AdjoinRoot φ) a)
      = coord0 hφ (algebraMap O (AdjoinRoot φ) (π ^ N) * z) := by rw [hz, map_pow]
  rwa [coord0_algebraMap, coord0_smul] at h2

/-- `fScale δ` is injective at `δ ≥ 1`. -/
theorem fScale_injective {δ : ℕ} (hδ : 1 ≤ δ) :
    Function.Injective (fScale δ) := by
  intro s t hst
  refine Multiset.map_injective (f := fun ef : ℕ × ℕ => (ef.1, δ * ef.2)) ?_ hst
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext hxy.1 (Nat.eq_of_mul_eq_mul_left (by omega) hxy.2)

/-- Two base polynomials congruent in the extension are congruent in the base. -/
theorem sub_mem_coeffIdeal_of_map (hφ : IsKey φ) {N : ℕ} {F F' : Polynomial O}
    (h : F.map (algebraMap O (AdjoinRoot φ)) - F'.map (algebraMap O (AdjoinRoot φ))
      ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N)) :
    F - F' ∈ coeffIdeal ((maximalIdeal O) ^ N) := by
  rw [mem_coeffIdeal] at h ⊢
  intro i
  have hi := h i
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_map, ← map_sub] at hi
  rw [Polynomial.coeff_sub]
  exact mem_pow_maximalIdeal_of_algebraMap hφ hi

/-- Extension of a base congruence to the unramified extension. -/
theorem map_sub_mem_coeffIdeal (hφ : IsKey φ) {N : ℕ} {F F' : Polynomial O}
    (h : F - F' ∈ coeffIdeal ((maximalIdeal O) ^ N)) :
    F.map (algebraMap O (AdjoinRoot φ)) - F'.map (algebraMap O (AdjoinRoot φ))
      ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N) := by
  rw [mem_coeffIdeal] at h ⊢
  intro i
  have hi := h i
  rw [Polynomial.coeff_sub] at hi
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_map, ← map_sub,
    adjoinRoot_maximalIdeal_eq hφ, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hi

/-- The conjugations preserve congruences. -/
theorem map_tau_sub_mem_coeffIdeal (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    {N : ℕ} {B B' : Polynomial (AdjoinRoot φ)}
    (h : B - B' ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N)) :
    B.map (tau hφ β).toRingHom - B'.map (tau hφ β).toRingHom
      ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N) := by
  rw [mem_coeffIdeal] at h ⊢
  intro i
  have hi := h i
  rw [Polynomial.coeff_sub] at hi
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_map, ← map_sub]
  -- the conjugations fix the (base-rational) uniformizer, so they preserve `𝔪'^N`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ' := irreducible_algebraMap_adjoinRoot hφ hπ
  rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hi ⊢
  obtain ⟨z, hz⟩ := hi
  refine ⟨tau hφ β z, ?_⟩
  have hfix : (tau hφ β).toRingHom (algebraMap O (AdjoinRoot φ) π)
      = algebraMap O (AdjoinRoot φ) π := (tau hφ β).commutes π
  rw [hz, map_mul, map_pow, hfix]
  rfl

/-- The coprimality of the `θ̄`-block residual against the rest. -/
theorem isCoprime_block_residual (hφ : IsKey φ) (e : ℕ) :
    IsCoprime
      ((X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e)
      (∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
        (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e) := by
  apply IsCoprime.prod_right
  intro ᾱ hᾱ
  exact (isCoprime_X_sub_C_of_ne (Ne.symm (Finset.ne_of_mem_erase hᾱ))).pow

/-- ★ **LEVEL EXACTNESS**: congruent base lifts have congruent `θ̄`-blocks (IFCG16's
finite-precision Hensel uniqueness, applied over the extension). -/
theorem block_level_exact (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N) {F F' : Polynomial O}
    {B R B' R' : Polynomial (AdjoinRoot φ)}
    (hB : B.Monic) (hR : R.Monic) (hB' : B'.Monic) (hR' : R'.Monic)
    (hprod : F.map (algebraMap O (AdjoinRoot φ)) = B * R)
    (hprod' : F'.map (algebraMap O (AdjoinRoot φ)) = B' * R')
    (hBres : B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e)
    (hB'res : B'.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e)
    (hRres : R.map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
          (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e)
    (hR'res : R'.map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
          (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e)
    (hcong : F - F' ∈ coeffIdeal ((maximalIdeal O) ^ N)) :
    B - B' ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ' := irreducible_algebraMap_adjoinRoot hφ hπ
  have hmul : B * R - B' * R' ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N) := by
    rw [← hprod, ← hprod']
    exact map_sub_mem_coeffIdeal hφ hcong
  exact (factor_sub_mem_of_mul_sub_mem hπ' hN hB hB' hR hR'
    (by rw [Uniformity.Hensel.natDegree_eq_of_map_eq hB' hB'res,
      Uniformity.Hensel.natDegree_eq_of_map_eq hB hBres])
    (by rw [Uniformity.Hensel.natDegree_eq_of_map_eq hR' hR'res,
      Uniformity.Hensel.natDegree_eq_of_map_eq hR hRres])
    (by rw [hBres, hB'res]) (by rw [hRres, hR'res])
    (by rw [hBres, hRres]; exact isCoprime_block_residual hφ e) hmul).1

/-- **The conjugate product** of a block over the extension. -/
noncomputable def tauProd (hφ : IsKey φ) (B : Polynomial (AdjoinRoot φ)) :
    Polynomial (AdjoinRoot φ) :=
  ∏ β ∈ (keyRoots hφ).toFinset, B.map (tau hφ β).toRingHom

theorem tauProd_monic (hφ : IsKey φ) {B : Polynomial (AdjoinRoot φ)} (hB : B.Monic) :
    (tauProd hφ B).Monic :=
  monic_prod_of_monic _ _ fun _ _ => hB.map _

theorem tauProd_natDegree (hφ : IsKey φ) {B : Polynomial (AdjoinRoot φ)} (hB : B.Monic) :
    (tauProd hφ B).natDegree = φ.natDegree * B.natDegree := by
  rw [tauProd, Polynomial.natDegree_prod _ _ (fun β _ => (hB.map _).ne_zero),
    Finset.sum_congr rfl (fun β (_ : β ∈ (keyRoots hφ).toFinset) =>
      hB.natDegree_map (tau hφ β).toRingHom),
    Finset.sum_const, Multiset.card_toFinset,
    Multiset.dedup_eq_self.mpr (nodup_keyRoots hφ), card_keyRoots hφ, smul_eq_mul]

/-- **The conjugate product is `τ`-invariant** (composition closure permutes the
family). -/
theorem tauProd_map_tau (hφ : IsKey φ) (γ : ResidueField (AdjoinRoot φ))
    (B : Polynomial (AdjoinRoot φ)) :
    (tauProd hφ B).map (tau hφ γ).toRingHom = tauProd hφ B := by
  rw [tauProd, Polynomial.map_prod]
  calc ∏ β ∈ (keyRoots hφ).toFinset, (B.map (tau hφ β).toRingHom).map (tau hφ γ).toRingHom
      = ∏ β ∈ (keyRoots hφ).toFinset, B.map (tau hφ (resTau hφ γ β)).toRingHom := by
        refine Finset.prod_congr rfl fun β hβ => ?_
        rw [Polynomial.map_map]
        congr 1
        exact congrArg AlgHom.toRingHom (tau_comp hφ (Multiset.mem_toFinset.mp hβ))
    _ = ∏ β' ∈ (keyRoots hφ).toFinset.image (resTau hφ γ),
          B.map (tau hφ β').toRingHom :=
        (Finset.prod_image (s := (keyRoots hφ).toFinset) (g := ⇑(resTau hφ γ))
          (f := fun β' => B.map (tau hφ β').toRingHom)
          (fun x _ y _ h => (resTau hφ γ).injective h)).symm
    _ = tauProd hφ B := by rw [image_resTau_toFinset hφ γ, tauProd]

/-- ★ **THE DESCENT OF THE CONJUGATE PRODUCT**: the conjugate product of any monic block
is the extension of a monic base polynomial of degree `δ · deg B` (invariants theorem,
coefficientwise). -/
theorem exists_descent_tauProd (hφ : IsKey φ) {B : Polynomial (AdjoinRoot φ)}
    (hB : B.Monic) :
    ∃ F : Polynomial O, F.Monic ∧ F.natDegree = φ.natDegree * B.natDegree ∧
      F.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ B := by
  have hlift : tauProd hφ B ∈ Polynomial.lifts (algebraMap O (AdjoinRoot φ)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine exists_algebraMap_eq_of_forall_tau hφ (fun β _ => ?_)
    have h := congrArg (fun P => Polynomial.coeff P i) (tauProd_map_tau hφ β B)
    simpa [Polynomial.coeff_map] using h
  obtain ⟨F, hFmap, hFdeg, hFmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift (tauProd_monic hφ hB)
  exact ⟨F, hFmon, by rw [hFdeg, tauProd_natDegree hφ hB], hFmap⟩

/-- The conjugate product of a block reduces to `φ̄^e` extended, at a block residual. -/
theorem tauProd_map_residue (hφ : IsKey φ) {e : ℕ} {B : Polynomial (AdjoinRoot φ)}
    (hBres : B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e) :
    (tauProd hφ B).map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset, (X - C ᾱ) ^ e := by
  rw [tauProd, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun β hβ => ?_
  rw [map_resTau_map_residue hφ, hBres, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C,
    resTau_apply_of_mem hφ (Multiset.mem_toFinset.mp hβ)]

/-- The reduction of the descended conjugate product is `φ̄^e` over the BASE (the
residue-field embedding is injective on polynomials). -/
theorem map_residue_eq_pow_of_tauProd (hφ : IsKey φ) {e : ℕ} {F : Polynomial O}
    {B : Polynomial (AdjoinRoot φ)}
    (hFmap : F.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ B)
    (hBres : B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e) :
    F.map (residue O) = (φ.map (residue O)) ^ e := by
  have h1 : (F.map (residue O)).map (resEmb hφ)
      = ((φ.map (residue O)) ^ e).map (resEmb hφ) := by
    rw [← map_map_residue_adjoinRoot hφ, hFmap, tauProd_map_residue hφ hBres,
      Polynomial.map_pow, ← keyRes_eq_prod hφ, prod_map_keyRoots hφ, ← Finset.prod_pow]
  exact Polynomial.map_injective _ (resEmb hφ).injective h1

/-! ### The congruence dictionary at a level -/

section Congruence

variable {R : Type*} [CommRing R]

/-- Congruence mod `coeffIdeal J` is equality of the reductions. -/
theorem sub_mem_coeffIdeal_iff {J : Ideal R} {p q : Polynomial R} :
    p - q ∈ coeffIdeal J ↔
      p.map (Ideal.Quotient.mk J) = q.map (Ideal.Quotient.mk J) := by
  rw [← Uniformity.Hensel.map_mk_eq_zero_iff, Polynomial.map_sub, sub_eq_zero]

/-- Products of congruent families are congruent. -/
theorem prod_sub_mem_coeffIdeal {J : Ideal R} {ι : Type*} {s : Finset ι}
    {f g : ι → Polynomial R} (h : ∀ i ∈ s, f i - g i ∈ coeffIdeal J) :
    (∏ i ∈ s, f i) - (∏ i ∈ s, g i) ∈ coeffIdeal J := by
  rw [sub_mem_coeffIdeal_iff, Polynomial.map_prod, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun i hi => sub_mem_coeffIdeal_iff.mp (h i hi)

end Congruence

section ClassCongruence

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Two coefficient vectors in the same level-`N` class give congruent monic
polynomials. -/
theorem monicPoly_sub_mem_coeffIdeal {n N : ℕ} {a b : Fin n → O}
    (h : proj O n N a = proj O n N b) :
    monicPoly a - monicPoly b ∈ coeffIdeal ((maximalIdeal O) ^ N) := by
  rw [mem_coeffIdeal]
  intro i
  rw [Polynomial.coeff_sub]
  rcases lt_or_ge i n with hi | hi
  · rw [monicPoly_coeff_lt a hi, monicPoly_coeff_lt b hi]
    exact Ideal.Quotient.eq.mp (congrFun h ⟨i, hi⟩)
  · have hcoef : (monicPoly a).coeff i = (monicPoly b).coeff i := by
      rcases eq_or_lt_of_le hi with he | hlt
      · have e1 : (monicPoly a).coeff i = 1 := by
          have h1 := (monicPoly_monic a).coeff_natDegree
          rw [monicPoly_natDegree] at h1
          rwa [← he]
        have e2 : (monicPoly b).coeff i = 1 := by
          have h2 := (monicPoly_monic b).coeff_natDegree
          rw [monicPoly_natDegree] at h2
          rwa [← he]
        rw [e1, e2]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; exact hlt)]
    rw [hcoef, sub_self]
    exact Ideal.zero_mem _

/-- Congruent monic polynomials of the same degree have equal coefficient classes. -/
theorem proj_coeff_eq_of_sub_mem {n N : ℕ} {P Q : Polynomial O}
    (h : P - Q ∈ coeffIdeal ((maximalIdeal O) ^ N)) :
    proj O n N (fun i : Fin n => P.coeff (i : ℕ))
      = proj O n N (fun i : Fin n => Q.coeff (i : ℕ)) := by
  funext i
  have hi := mem_coeffIdeal.mp h (i : ℕ)
  rw [Polynomial.coeff_sub] at hi
  exact Ideal.Quotient.eq.mpr hi

theorem proj_eq_proj_coeff_monicPoly {n N : ℕ} (a : Fin n → O) :
    proj O n N a = proj O n N (fun i : Fin n => (monicPoly a).coeff (i : ℕ)) := by
  funext i
  exact congrArg _ (monicPoly_coeff_lt a i.isLt).symm

end ClassCongruence

/-! ### The class-level block correspondence -/

/-- **The block-class relation**: `c'` is the class of the `θ̄`-block of a lift of `c`. -/
def IsBlockClass (hφ : IsKey φ) {e N : ℕ} (c : Coeff O (φ.natDegree * e) N)
    (c' : Coeff (AdjoinRoot φ) e N) : Prop :=
  ∃ (a : Fin (φ.natDegree * e) → O) (B R : Polynomial (AdjoinRoot φ)),
    proj O (φ.natDegree * e) N a = c ∧ B.Monic ∧ R.Monic ∧
    (monicPoly a).map (algebraMap O (AdjoinRoot φ)) = B * R ∧
    B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e ∧
    R.map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
          (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e ∧
    proj (AdjoinRoot φ) e N (fun i : Fin e => B.coeff (i : ℕ)) = c'

/-- Blocks have degree exactly `e`. -/
theorem block_natDegree {e : ℕ} {B : Polynomial (AdjoinRoot φ)} (hB : B.Monic)
    (hBres : B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e) :
    B.natDegree = e := by
  rw [Uniformity.Hensel.natDegree_eq_of_map_eq hB hBres, Polynomial.natDegree_pow,
    Polynomial.natDegree_X_sub_C, mul_one]

/-- **Existence of the block class** for a class in the `p^e` stratum. -/
theorem exists_isBlockClass (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    {c : Coeff O (φ.natDegree * e) N}
    (hc : c ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e)) :
    ∃ c' : Coeff (AdjoinRoot φ) e N, IsBlockClass hφ c c' := by
  obtain ⟨a, ha, hres⟩ := (mem_levelZeroStratum_iff hN _ c).mp hc
  obtain ⟨B, R, hB, hR, hBdeg, hprod, hBres, hRres⟩ :=
    exists_block hφ (monicPoly_monic a) hres
  exact ⟨proj (AdjoinRoot φ) e N (fun i : Fin e => B.coeff (i : ℕ)),
    a, B, R, ha, hB, hR, hprod, hBres, hRres, rfl⟩

/-- **The block class is well defined** (level exactness). -/
theorem isBlockClass_unique (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    {c : Coeff O (φ.natDegree * e) N} {c₁ c₂ : Coeff (AdjoinRoot φ) e N}
    (h₁ : IsBlockClass hφ c c₁) (h₂ : IsBlockClass hφ c c₂) : c₁ = c₂ := by
  obtain ⟨a₁, B₁, R₁, ha₁, hB₁, hR₁, hp₁, hBr₁, hRr₁, hc₁⟩ := h₁
  obtain ⟨a₂, B₂, R₂, ha₂, hB₂, hR₂, hp₂, hBr₂, hRr₂, hc₂⟩ := h₂
  have hcong : monicPoly a₁ - monicPoly a₂ ∈ coeffIdeal ((maximalIdeal O) ^ N) :=
    monicPoly_sub_mem_coeffIdeal (by rw [ha₁, ha₂])
  have hBcong := block_level_exact hφ hN hB₁ hR₁ hB₂ hR₂ hp₁ hp₂ hBr₁ hBr₂ hRr₁ hRr₂ hcong
  rw [← hc₁, ← hc₂]
  exact proj_coeff_eq_of_sub_mem hBcong

/-- **Injectivity of the block class** (the conjugate product recovers the base class). -/
theorem isBlockClass_injective (hφ : IsKey φ) {e N : ℕ}
    {c₁ c₂ : Coeff O (φ.natDegree * e) N} {c' : Coeff (AdjoinRoot φ) e N}
    (hst₁ : c₁ ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e))
    (hst₂ : c₂ ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e))
    (h₁ : IsBlockClass hφ c₁ c') (h₂ : IsBlockClass hφ c₂ c') : c₁ = c₂ := by
  obtain ⟨a₁, B₁, R₁, ha₁, hB₁, hR₁, hp₁, hBr₁, hRr₁, hc₁⟩ := h₁
  obtain ⟨a₂, B₂, R₂, ha₂, hB₂, hR₂, hp₂, hBr₂, hRr₂, hc₂⟩ := h₂
  -- the blocks are congruent: their coefficient classes coincide
  have hd₁ : B₁.natDegree = e := block_natDegree hB₁ hBr₁
  have hd₂ : B₂.natDegree = e := block_natDegree hB₂ hBr₂
  have hB₁eq : monicPoly (fun i : Fin e => B₁.coeff (i : ℕ)) = B₁ :=
    monicPoly_coeff_eq_self hB₁ hd₁
  have hB₂eq : monicPoly (fun i : Fin e => B₂.coeff (i : ℕ)) = B₂ :=
    monicPoly_coeff_eq_self hB₂ hd₂
  have hBcong : B₁ - B₂ ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N) := by
    rw [← hB₁eq, ← hB₂eq]
    exact monicPoly_sub_mem_coeffIdeal (by rw [hc₁, hc₂])
  -- hence the conjugate products, hence the base lifts, are congruent
  have hres₁ : (monicPoly a₁).map (residue O) = (φ.map (residue O)) ^ e := hst₁ a₁ ha₁
  have hres₂ : (monicPoly a₂).map (residue O) = (φ.map (residue O)) ^ e := hst₂ a₂ ha₂
  have hF₁ : (monicPoly a₁).map (algebraMap O (AdjoinRoot φ)) = tauProd hφ B₁ :=
    map_algebraMap_eq_prod_tau hφ (monicPoly_monic a₁) hres₁ hB₁ hR₁ hp₁ hBr₁ hRr₁
  have hF₂ : (monicPoly a₂).map (algebraMap O (AdjoinRoot φ)) = tauProd hφ B₂ :=
    map_algebraMap_eq_prod_tau hφ (monicPoly_monic a₂) hres₂ hB₂ hR₂ hp₂ hBr₂ hRr₂
  have hprodcong : tauProd hφ B₁ - tauProd hφ B₂
      ∈ coeffIdeal ((maximalIdeal (AdjoinRoot φ)) ^ N) :=
    prod_sub_mem_coeffIdeal fun β _ => map_tau_sub_mem_coeffIdeal hφ β hBcong
  have hbase : monicPoly a₁ - monicPoly a₂ ∈ coeffIdeal ((maximalIdeal O) ^ N) := by
    refine sub_mem_coeffIdeal_of_map hφ ?_
    rw [hF₁, hF₂]
    exact hprodcong
  rw [← ha₁, ← ha₂, proj_eq_proj_coeff_monicPoly a₁, proj_eq_proj_coeff_monicPoly a₂]
  exact proj_coeff_eq_of_sub_mem hbase

/-- ★ **THE BASE LIFT OF A BLOCK**: every monic block over the extension with the
canonical linear residual is the `θ̄`-block of a monic BASE polynomial in the `p^e`
stratum (the conjugate product, descended by the invariants theorem). -/
theorem exists_baseLift_of_block (hφ : IsKey φ) {e : ℕ} {B : Polynomial (AdjoinRoot φ)}
    (hB : B.Monic)
    (hbres : B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e) :
    ∃ (F : Polynomial O) (R : Polynomial (AdjoinRoot φ)),
      F.Monic ∧ F.natDegree = φ.natDegree * e ∧
      F.map (residue O) = (φ.map (residue O)) ^ e ∧ R.Monic ∧
      F.map (algebraMap O (AdjoinRoot φ)) = B * R ∧
      R.map (residue (AdjoinRoot φ))
        = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
            (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e := by
  obtain ⟨F, hFmon, hFdeg, hFmap⟩ := exists_descent_tauProd hφ hB
  have hFres : F.map (residue O) = (φ.map (residue O)) ^ e :=
    map_residue_eq_pow_of_tauProd hφ hFmap hbres
  have hθ' : residue (AdjoinRoot φ) (AdjoinRoot.root φ) ∈ (keyRoots hφ).toFinset :=
    Multiset.mem_toFinset.mpr (residue_root_mem_keyRoots hφ)
  have hBid : B.map (tau hφ (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).toRingHom = B := by
    rw [tau_residue_root hφ]
    show B.map (RingHom.id (AdjoinRoot φ)) = B
    rw [Polynomial.map_id]
  refine ⟨F, ∏ β ∈ (keyRoots hφ).toFinset.erase
      (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), B.map (tau hφ β).toRingHom,
    hFmon, by rw [hFdeg, block_natDegree hB hbres], hFres,
    monic_prod_of_monic _ _ fun _ _ => hB.map _, ?_, ?_⟩
  · rw [hFmap, tauProd,
      ← Finset.mul_prod_erase _ (fun β => B.map (tau hφ β).toRingHom) hθ', hBid]
  · rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun β hβ => ?_
    rw [map_resTau_map_residue hφ, hbres, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C,
      resTau_apply_of_mem hφ (Multiset.mem_toFinset.mp (Finset.mem_of_mem_erase hβ))]

/-- **Surjectivity of the block class**: every class in the extension's linear-point
stratum is the block class of a (constructed) base class. -/
theorem exists_isBlockClass_of_stratum (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    {c' : Coeff (AdjoinRoot φ) e N}
    (hc' : c' ∈ levelZeroStratum (AdjoinRoot φ) e N
      ((X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e)) :
    ∃ c : Coeff O (φ.natDegree * e) N,
      c ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e) ∧
      IsBlockClass hφ c c' := by
  obtain ⟨b, hb, hbres⟩ := (mem_levelZeroStratum_iff hN _ c').mp hc'
  obtain ⟨F, R, hFmon, hFdeg, hFres, hR, hprod, hRres⟩ :=
    exists_baseLift_of_block hφ (monicPoly_monic b) hbres
  set a : Fin (φ.natDegree * e) → O := fun i => F.coeff (i : ℕ) with hadef
  have haF : monicPoly a = F := monicPoly_coeff_eq_self hFmon hFdeg
  refine ⟨proj O (φ.natDegree * e) N a, ?_, a, monicPoly b, R, rfl, monicPoly_monic b, hR,
    ?_, hbres, hRres, ?_⟩
  · rw [mem_levelZeroStratum_iff hN]
    exact ⟨a, rfl, by rw [haF]; exact hFres⟩
  · rw [haF]; exact hprod
  · rw [← hb]
    exact (proj_eq_proj_coeff_monicPoly b).symm

/-! ### The named type-descent law and the count equality -/

/-- ★★ **THE ONE OPEN TYPE-DESCENT LAW at `(O, φ, e)`**: the splitting type of a base
polynomial in the `p^e` stratum is the `fScale δ` of the type of its `θ̄`-block. -/
def BlockDescentAt (hφ : IsKey φ) (e : ℕ) : Prop :=
  ∀ (F : Polynomial O) (B R : Polynomial (AdjoinRoot φ)),
    F.Monic → F.map (residue O) = (φ.map (residue O)) ^ e →
    B.Monic → R.Monic →
    F.map (algebraMap O (AdjoinRoot φ)) = B * R →
    B.map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e →
    R.map (residue (AdjoinRoot φ))
      = ∏ ᾱ ∈ (keyRoots hφ).toFinset.erase
          (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), (X - C ᾱ) ^ e →
    (typeOf F).data = fScale φ.natDegree (typeOf B).data

/-- The block-class map (choice on the well-defined block class). -/
noncomputable def blockClassMap (hφ : IsKey φ) (e N : ℕ)
    (c : Coeff O (φ.natDegree * e) N) : Coeff (AdjoinRoot φ) e N :=
  if h : ∃ c' : Coeff (AdjoinRoot φ) e N, IsBlockClass hφ c c' then h.choose
  else fun _ => 0

theorem isBlockClass_blockClassMap (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    {c : Coeff O (φ.natDegree * e) N}
    (hst : c ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e)) :
    IsBlockClass hφ c (blockClassMap hφ e N c) := by
  rw [blockClassMap, dif_pos (exists_isBlockClass hφ hN hst)]
  exact (exists_isBlockClass hφ hN hst).choose_spec

/-- The block class lies in the extension's linear-point stratum. -/
theorem blockClass_mem_stratum (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    {c : Coeff O (φ.natDegree * e) N} {c' : Coeff (AdjoinRoot φ) e N}
    (hbc : IsBlockClass hφ c c') :
    c' ∈ levelZeroStratum (AdjoinRoot φ) e N
      ((X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e) := by
  obtain ⟨a, B, R, ha, hB, hR, hprod, hBres, hRres, hc'⟩ := hbc
  rw [mem_levelZeroStratum_iff hN]
  refine ⟨fun i : Fin e => B.coeff (i : ℕ), hc', ?_⟩
  rw [monicPoly_coeff_eq_self hB (block_natDegree hB hBres)]
  exact hBres

/-- ★ **Decidedness descends to the block** (uses the type-descent law and `fScale`
injectivity). -/
theorem decidedAt_block_of_base (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    (hdesc : BlockDescentAt hφ e) {s' : Multiset (ℕ × ℕ)}
    {c : Coeff O (φ.natDegree * e) N} {c' : Coeff (AdjoinRoot φ) e N}
    (hst : c ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e))
    (hbc : IsBlockClass hφ c c')
    (hdec : DecidedAt O (φ.natDegree * e) ⟨fScale φ.natDegree s'⟩ N c) :
    DecidedAt (AdjoinRoot φ) e ⟨s'⟩ N c' := by
  intro b hb
  -- the given block lift has the canonical residual (the block class is in the stratum)
  have hbres : (monicPoly b).map (residue (AdjoinRoot φ))
      = (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e :=
    blockClass_mem_stratum hφ hN hbc b hb
  -- its conjugate product descends to a base lift, whose class must be `c`
  obtain ⟨F, R, hFmon, hFdeg, hFres, hR, hprod, hRres⟩ :=
    exists_baseLift_of_block hφ (monicPoly_monic b) hbres
  set a : Fin (φ.natDegree * e) → O := fun i => F.coeff (i : ℕ) with hadef
  have haF : monicPoly a = F := monicPoly_coeff_eq_self hFmon hFdeg
  have hstF : proj O (φ.natDegree * e) N a
      ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e) := by
    rw [mem_levelZeroStratum_iff hN]
    exact ⟨a, rfl, by rw [haF]; exact hFres⟩
  have hbcF : IsBlockClass hφ (proj O (φ.natDegree * e) N a) c' :=
    ⟨a, monicPoly b, R, rfl, monicPoly_monic b, hR, by rw [haF]; exact hprod, hbres,
      hRres, by rw [← hb]; exact (proj_eq_proj_coeff_monicPoly b).symm⟩
  have hceq : proj O (φ.natDegree * e) N a = c :=
    isBlockClass_injective hφ hstF hst hbcF hbc
  -- the base type is decided, so the block type is pinned through `fScale`
  have hFty : typeOf F = ⟨fScale φ.natDegree s'⟩ := by
    rw [← haF]
    exact hdec a hceq
  have hdesc' := hdesc F (monicPoly b) R hFmon hFres (monicPoly_monic b) hR
    hprod hbres hRres
  rw [hFty] at hdesc'
  refine FactorizationType.ext ?_
  exact fScale_injective hφ.pos hdesc'.symm

/-- ★ **Decidedness rises from the block to the base.** -/
theorem decidedAt_base_of_block (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    (hdesc : BlockDescentAt hφ e) {s' : Multiset (ℕ × ℕ)}
    {c : Coeff O (φ.natDegree * e) N} {c' : Coeff (AdjoinRoot φ) e N}
    (hst : c ∈ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e))
    (hbc : IsBlockClass hφ c c')
    (hdec' : DecidedAt (AdjoinRoot φ) e ⟨s'⟩ N c') :
    DecidedAt O (φ.natDegree * e) ⟨fScale φ.natDegree s'⟩ N c := by
  intro a ha
  have hres : (monicPoly a).map (residue O) = (φ.map (residue O)) ^ e := hst a ha
  obtain ⟨B, R, hB, hR, hBdeg, hprod, hBres, hRres⟩ :=
    exists_block hφ (monicPoly_monic a) hres
  -- this block is a lift of the block class
  have hbcA : IsBlockClass hφ c (proj (AdjoinRoot φ) e N (fun i : Fin e => B.coeff (i : ℕ))) :=
    ⟨a, B, R, ha, hB, hR, hprod, hBres, hRres, rfl⟩
  have hc'eq : proj (AdjoinRoot φ) e N (fun i : Fin e => B.coeff (i : ℕ)) = c' :=
    isBlockClass_unique hφ hN hbcA hbc
  have hBty : typeOf B = ⟨s'⟩ := by
    rw [← monicPoly_coeff_eq_self hB hBdeg]
    exact hdec' _ hc'eq
  refine FactorizationType.ext ?_
  rw [hdesc (monicPoly a) B R (monicPoly_monic a) hres hB hR hprod hBres hRres, hBty]

/-- ★★ **THE COUNT EQUALITY from the type-descent law**: the base census of `p^e` at the
scaled label equals the extension census of `(X − θ̄)^e` at the label, at every finite
level.  Injectivity is level exactness, surjectivity is the conjugate-product
construction, and the label transport is the descent law. -/
theorem stratDecCount_eq_of_blockDescent (hφ : IsKey φ) {e N : ℕ} (hN : 1 ≤ N)
    (hdesc : BlockDescentAt hφ e) (s' : Multiset (ℕ × ℕ)) :
    stratDecCount O (φ.natDegree * e) ⟨fScale φ.natDegree s'⟩ N ((φ.map (residue O)) ^ e)
      = stratDecCount (AdjoinRoot φ) e ⟨s'⟩ N
          ((X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e) := by
  classical
  set n := φ.natDegree * e with hn
  set g : Polynomial (ResidueField O) := (φ.map (residue O)) ^ e with hg
  set g' : Polynomial (ResidueField (AdjoinRoot φ)) :=
    (X - C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e with hg'
  set S : Set (Coeff O n N) :=
    decidedSet O n ⟨fScale φ.natDegree s'⟩ N ∩ levelZeroStratum O n N g with hS
  set S' : Set (Coeff (AdjoinRoot φ) e N) :=
    decidedSet (AdjoinRoot φ) e ⟨s'⟩ N ∩ levelZeroStratum (AdjoinRoot φ) e N g' with hS'
  have hmemS : ∀ c ∈ S, IsBlockClass hφ c (blockClassMap hφ e N c) :=
    fun c hc => isBlockClass_blockClassMap hφ hN hc.2
  have hinj : Set.InjOn (blockClassMap hφ e N) S := by
    intro c₁ h₁ c₂ h₂ heq
    exact isBlockClass_injective hφ h₁.2 h₂.2 (hmemS c₁ h₁) (heq ▸ hmemS c₂ h₂)
  have himg : (blockClassMap hφ e N) '' S = S' := by
    apply Set.Subset.antisymm
    · rintro c' ⟨c, hc, rfl⟩
      exact ⟨decidedAt_block_of_base hφ hN hdesc hc.2 (hmemS c hc) hc.1,
        blockClass_mem_stratum hφ hN (hmemS c hc)⟩
    · intro c' hc'
      obtain ⟨c, hst, hbc⟩ := exists_isBlockClass_of_stratum hφ hN hc'.2
      have hdec : DecidedAt O n ⟨fScale φ.natDegree s'⟩ N c :=
        decidedAt_base_of_block hφ hN hdesc hst hbc hc'.1
      have hcS : c ∈ S := ⟨hdec, hst⟩
      refine ⟨c, hcS, ?_⟩
      exact isBlockClass_unique hφ hN (hmemS c hcS) hbc
  rw [stratDecCount, stratDecCount, ← hS, ← hS']
  calc Nat.card S = Nat.card ((blockClassMap hφ e N) '' S) :=
        (Nat.card_image_of_injOn hinj).symm
    _ = Nat.card S' := by rw [himg]

end Descent

/-! ## §7 — the factorization skeleton: the descent law from two PER-FACTOR legs -/

section Skeleton

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {φ : Polynomial O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- The canonical linear point of the extension is a key. -/
theorem isKey_linearPoint (_hφ : IsKey φ) :
    IsKey ((X : Polynomial (AdjoinRoot φ)) - Polynomial.C (AdjoinRoot.root φ)) := by
  refine ⟨monic_X_sub_C _, by rw [natDegree_X_sub_C]; omega, ?_⟩
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact irreducible_X_sub_C _

theorem map_residue_linearPoint (_hφ : IsKey φ) :
    ((X : Polynomial (AdjoinRoot φ)) - Polynomial.C (AdjoinRoot.root φ)).map
      (residue (AdjoinRoot φ))
      = X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ)) := by
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- **The residual shape of a block factor**: every monic irreducible factor of the
`θ̄`-block has residual exactly `(X − θ̄)^{deg}`. -/
theorem factor_residual_shape (hφ : IsKey φ) {e : ℕ} {B C : Polynomial (AdjoinRoot φ)}
    (hB : B.Monic)
    (hBres : B.map (residue (AdjoinRoot φ))
      = (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e)
    (hC : C ∈ monicFactors B) :
    C.map (residue (AdjoinRoot φ))
      = (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree := by
  have hres' : B.map (residue (AdjoinRoot φ))
      = ((((X : Polynomial (AdjoinRoot φ)) - Polynomial.C (AdjoinRoot.root φ))).map
          (residue (AdjoinRoot φ))) ^ e := by
    rw [map_residue_linearPoint hφ]; exact hBres
  obtain ⟨k, hk, hCres⟩ :=
    factor_residual_pow (isKey_linearPoint hφ) hB hres' hC
  have hCm : C.Monic := ((monicFactors_spec hB).1 C hC).1
  have hdeg : C.natDegree = k := by
    have hc := congrArg natDegree hCres
    rwa [hCm.natDegree_map, natDegree_pow,
      show ((((X : Polynomial (AdjoinRoot φ)) - Polynomial.C (AdjoinRoot.root φ))).map
        (residue (AdjoinRoot φ))).natDegree = 1 from by
          rw [map_residue_linearPoint hφ, natDegree_X_sub_C],
      mul_one] at hc
  rw [hdeg, hCres, map_residue_linearPoint hφ]

/-- `tauProd` is multiplicative. -/
theorem tauProd_mul (hφ : IsKey φ) (P Q : Polynomial (AdjoinRoot φ)) :
    tauProd hφ (P * Q) = tauProd hφ P * tauProd hφ Q := by
  rw [tauProd, tauProd, tauProd, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun β _ => Polynomial.map_mul _

theorem tauProd_one (hφ : IsKey φ) : tauProd hφ 1 = 1 := by
  rw [tauProd]
  simp

/-- `tauProd` over a multiset product. -/
theorem tauProd_multiset_prod (hφ : IsKey φ)
    (M : Multiset (Polynomial (AdjoinRoot φ))) :
    tauProd hφ M.prod = (M.map (tauProd hφ)).prod := by
  induction M using Multiset.induction with
  | empty => rw [Multiset.prod_zero, Multiset.map_zero, Multiset.prod_zero, tauProd_one]
  | cons C M ih =>
      rw [Multiset.prod_cons, tauProd_mul, ih, Multiset.map_cons, Multiset.prod_cons]

/-! ### The irreducibility leg -/

/-- The conjugation as a ring equivalence of the extension. -/
noncomputable def tauEquiv (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ)) :
    AdjoinRoot φ ≃+* AdjoinRoot φ :=
  RingEquiv.ofBijective (tau hφ β).toRingHom (tau_bijective hφ β)

/-- The induced equivalence on polynomials. -/
noncomputable def tauPolyEquiv (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ)) :
    Polynomial (AdjoinRoot φ) ≃+* Polynomial (AdjoinRoot φ) :=
  Polynomial.mapEquiv (tauEquiv hφ β)

theorem tauPolyEquiv_apply (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    (P : Polynomial (AdjoinRoot φ)) :
    tauPolyEquiv hφ β P = P.map (tau hφ β).toRingHom := rfl

/-- **The conjugations preserve irreducibility.** -/
theorem irreducible_map_tau (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    {P : Polynomial (AdjoinRoot φ)} (hP : Irreducible P) :
    Irreducible (P.map (tau hφ β).toRingHom) := by
  rw [← tauPolyEquiv_apply hφ β P]
  exact hP.map (tauPolyEquiv hφ β).toMulEquiv

/-- **Monic factorizations transport along the conjugations.** -/
theorem monicFactors_map_tau (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ))
    {P : Polynomial (AdjoinRoot φ)} (hP : P.Monic) :
    monicFactors (P.map (tau hφ β).toRingHom)
      = (monicFactors P).map (fun D => D.map (tau hφ β).toRingHom) := by
  obtain ⟨hfac, hprod⟩ := monicFactors_spec hP
  refine monicFactors_eq ⟨?_, ?_⟩
  · intro D hD
    obtain ⟨D₀, hD₀, rfl⟩ := Multiset.mem_map.mp hD
    exact ⟨(hfac D₀ hD₀).1.map _, irreducible_map_tau hφ β (hfac D₀ hD₀).2⟩
  · have h := Multiset.prod_hom (monicFactors P)
      (Polynomial.mapRingHom (tau hφ β).toRingHom).toMonoidHom
    rw [hprod] at h
    exact h

/-- The conjugate family of a positive-degree block factor is duplicate-free. -/
theorem nodup_conjugates (hφ : IsKey φ) {C : Polynomial (AdjoinRoot φ)}
    (hCpos : 0 < C.natDegree)
    (hCres : C.map (residue (AdjoinRoot φ))
      = (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree) :
    ((keyRoots hφ).toFinset.val.map (fun β => C.map (tau hφ β).toRingHom)).Nodup := by
  -- the residuals `(X − β)^d` determine `β`
  have hres : ∀ x : ResidueField (AdjoinRoot φ), x ∈ keyRoots hφ →
      (C.map (tau hφ x).toRingHom).map (residue (AdjoinRoot φ))
        = (X - Polynomial.C x) ^ C.natDegree := by
    intro x hx
    rw [map_resTau_map_residue hφ, hCres, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, resTau_apply_of_mem hφ hx]
  refine Multiset.Nodup.map_on ?_ (keyRoots hφ).toFinset.nodup
  intro β hβf γ hγf hβγ
  have hβ : β ∈ keyRoots hφ := Multiset.mem_toFinset.mp hβf
  have hγ : γ ∈ keyRoots hφ := Multiset.mem_toFinset.mp hγf
  have hβγ' : C.map (tau hφ β).toRingHom = C.map (tau hφ γ).toRingHom := hβγ
  have heq : ((X : Polynomial (ResidueField (AdjoinRoot φ))) - Polynomial.C β)
      ^ C.natDegree = (X - Polynomial.C γ) ^ C.natDegree := by
    rw [← hres β hβ, ← hres γ hγ, hβγ']
  have hev := congrArg (Polynomial.eval β) heq
  rw [Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C,
    sub_self, zero_pow (by omega)] at hev
  have hz : β - γ = 0 := pow_eq_zero_iff (by omega) |>.mp hev.symm
  exact sub_eq_zero.mp hz

/-- The conjugate family, as a multiset, IS the monic factorization of the descended
conjugate product. -/
theorem monicFactors_map_tauProd (hφ : IsKey φ) {C : Polynomial (AdjoinRoot φ)}
    (hCm : C.Monic) (hCi : Irreducible C) {G : Polynomial O}
    (hGmap : G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C) :
    monicFactors (G.map (algebraMap O (AdjoinRoot φ)))
      = (keyRoots hφ).toFinset.val.map (fun β => C.map (tau hφ β).toRingHom) := by
  refine monicFactors_eq ⟨?_, ?_⟩
  · intro D hD
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hD
    exact ⟨hCm.map _, irreducible_map_tau hφ β hCi⟩
  · rw [hGmap, tauProd, Finset.prod_eq_multiset_prod]

/-- ★ **THE IRREDUCIBILITY LEG, PROVED**: the descent of the conjugate product of a
monic irreducible block factor is irreducible over the base.  Mechanism: a proper monic
factor's factor-multiset over the extension is `τ`-invariant and contains `C` (the
`θ̄`-conjugate is the identity), hence contains the WHOLE duplicate-free conjugate
family, forcing the cofactor to be `1`. -/
theorem irreducible_descent_tauProd (hφ : IsKey φ) {C : Polynomial (AdjoinRoot φ)}
    (hCm : C.Monic) (hCi : Irreducible C)
    (hCres : C.map (residue (AdjoinRoot φ))
      = (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree)
    {G : Polynomial O} (hG : G.Monic)
    (hGmap : G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C) :
    Irreducible G := by
  classical
  have hCpos : 0 < C.natDegree := by
    rcases Nat.eq_zero_or_pos C.natDegree with h0 | h0
    · exact absurd ((hCm.natDegree_eq_zero).mp h0 ▸ isUnit_one) hCi.not_isUnit
    · exact h0
  set W := (keyRoots hφ).toFinset.val.map (fun β => C.map (tau hφ β).toRingHom) with hW
  have hWfac : monicFactors (G.map (algebraMap O (AdjoinRoot φ))) = W :=
    monicFactors_map_tauProd hφ hCm hCi hGmap
  have hGdeg : G.natDegree = φ.natDegree * C.natDegree := by
    have h := congrArg natDegree hGmap
    rwa [hG.natDegree_map, tauProd_natDegree hφ hCm] at h
  have hGpos : 0 < G.natDegree := by
    rw [hGdeg]; exact Nat.mul_pos hφ.pos hCpos
  -- `C` itself is a conjugate (the `θ̄`-conjugate is the identity)
  have hCmemW : C ∈ W := by
    refine Multiset.mem_map.mpr ⟨residue (AdjoinRoot φ) (AdjoinRoot.root φ), ?_, ?_⟩
    · exact Multiset.mem_toFinset.mpr (residue_root_mem_keyRoots hφ)
    · rw [tau_residue_root hφ]
      show C.map (RingHom.id (AdjoinRoot φ)) = C
      rw [Polynomial.map_id]
  -- the peel: a monic proper factorization would have a `τ`-invariant factor multiset
  have hkey : ∀ P Q : Polynomial O, P.Monic → Q.Monic → G = P * Q →
      C ∈ monicFactors (P.map (algebraMap O (AdjoinRoot φ))) → Q.natDegree = 0 := by
    intro P Q hP hQ hPQ hCmem
    set T₁ := monicFactors (P.map (algebraMap O (AdjoinRoot φ))) with hT₁
    set T₂ := monicFactors (Q.map (algebraMap O (AdjoinRoot φ))) with hT₂
    have hsplit : T₁ + T₂ = W := by
      rw [← hWfac, hPQ, Polynomial.map_mul, monicFactors_mul (hP.map _) (hQ.map _)]
    have hinv : ∀ γ : ResidueField (AdjoinRoot φ),
        T₁.map (fun D => D.map (tau hφ γ).toRingHom) = T₁ := by
      intro γ
      rw [hT₁, ← monicFactors_map_tau hφ γ (hP.map _), map_tau_map_algebraMap hφ γ P]
    have hWsub : ∀ D ∈ W, D ∈ T₁ := by
      intro D hD
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hD
      rw [← hinv β]
      exact Multiset.mem_map.mpr ⟨C, hCmem, rfl⟩
    have hle : W ≤ T₁ := by
      rw [Multiset.le_iff_count]
      intro D
      by_cases hD : D ∈ W
      · calc Multiset.count D W ≤ 1 :=
              Multiset.nodup_iff_count_le_one.mp (nodup_conjugates hφ hCpos hCres) D
          _ ≤ Multiset.count D T₁ := Multiset.one_le_count_iff_mem.mpr (hWsub D hD)
      · rw [Multiset.count_eq_zero_of_notMem hD]
        omega
    have hT₂zero : T₂ = 0 := by
      have h2 : T₁ + T₂ ≤ T₁ + 0 := by rw [hsplit, add_zero]; exact hle
      have h3 : T₂ ≤ 0 := (add_le_add_iff_left T₁).mp h2
      exact Multiset.le_zero.mp h3
    have hQone : Q.map (algebraMap O (AdjoinRoot φ)) = 1 := by
      have := (monicFactors_spec (hQ.map (algebraMap O (AdjoinRoot φ)))).2
      rw [← hT₂, hT₂zero, Multiset.prod_zero] at this
      exact this.symm
    have := congrArg natDegree hQone
    rwa [hQ.natDegree_map, natDegree_one] at this
  -- now the irreducibility argument itself
  constructor
  · intro hu
    have := natDegree_eq_zero_of_isUnit hu
    omega
  · intro G₁ G₂ hG12
    -- monicize both factors (their leading coefficients are units)
    have hu₁ : IsUnit G₁.leadingCoeff :=
      isUnit_leadingCoeff_of_dvd_monic hG ⟨G₂, hG12⟩
    have hu₂ : IsUnit G₂.leadingCoeff :=
      isUnit_leadingCoeff_of_dvd_monic hG ⟨G₁, by rw [hG12]; ring⟩
    set P := monicize G₁ with hPdef
    set Q := monicize G₂ with hQdef
    have hP : P.Monic := monicize_monic hu₁
    have hQ : Q.Monic := monicize_monic hu₂
    have hPQ : G = P * Q := by
      refine (eq_of_monic_of_associated hG (hP.mul hQ) ?_)
      rw [hG12]
      exact (associated_monicize hu₁).mul_mul (associated_monicize hu₂)
    have hPdeg : P.natDegree = G₁.natDegree := by
      rw [hPdef, monicize, Polynomial.natDegree_C_mul
        (isUnit_inverse_leadingCoeff hu₁).ne_zero]
    have hQdeg : Q.natDegree = G₂.natDegree := by
      rw [hQdef, monicize, Polynomial.natDegree_C_mul
        (isUnit_inverse_leadingCoeff hu₂).ne_zero]
    -- `C` sits in one of the two factor multisets
    have hCin : C ∈ monicFactors (P.map (algebraMap O (AdjoinRoot φ)))
        ∨ C ∈ monicFactors (Q.map (algebraMap O (AdjoinRoot φ))) := by
      have hsplit : monicFactors (P.map (algebraMap O (AdjoinRoot φ)))
          + monicFactors (Q.map (algebraMap O (AdjoinRoot φ))) = W := by
        rw [← hWfac, hPQ, Polynomial.map_mul, monicFactors_mul (hP.map _) (hQ.map _)]
      rw [← Multiset.mem_add, hsplit]
      exact hCmemW
    rcases hCin with hC1 | hC2
    · right
      have hQ0 : G₂.natDegree = 0 := by
        rw [← hQdeg]
        exact hkey P Q hP hQ hPQ hC1
      exact isUnit_of_natDegree_zero hQ0 hu₂
    · left
      have hP0 : G₁.natDegree = 0 := by
        rw [← hPdeg]
        exact hkey Q P hQ hP (by rw [hPQ]; ring) hC2
      exact isUnit_of_natDegree_zero hP0 hu₁

/-- ★★ **THE FACTORIZATION SKELETON**: given the two per-factor legs — irreducibility of
the descended conjugate product, and the inertia scaling `f_O(G) = δ · f_{O'}(C)` — the
type-descent law holds.  The bookkeeping is `typeOf`'s multiset algebra: the base monic
factorization of `F` is exactly the family of descended conjugate products of the block's
monic factors. -/
theorem blockDescentAt_of_legs (hφ : IsKey φ) {e : ℕ}
    (hinert : ∀ (C : Polynomial (AdjoinRoot φ)) (G : Polynomial O), C.Monic →
      Irreducible C →
      C.map (residue (AdjoinRoot φ))
        = (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree →
      G.Monic → G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C →
      inertiaDegOf G = φ.natDegree * inertiaDegOf C) :
    BlockDescentAt hφ e := by
  intro F B R hF hFres hB hR hprod hBres hRres
  -- the conjugacy decomposition of the base lift
  have hFmap : F.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ B :=
    map_algebraMap_eq_prod_tau hφ hF hFres hB hR hprod hBres hRres
  set M := monicFactors B with hM
  obtain ⟨hMfac, hMprod⟩ := monicFactors_spec hB
  -- the descents of the conjugate products of the block's factors
  have hex : ∀ C ∈ M, ∃ G : Polynomial O, G.Monic ∧
      G.natDegree = φ.natDegree * C.natDegree ∧
      G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C := by
    intro C hC
    obtain ⟨G, hGm, hGd, hGmap⟩ := exists_descent_tauProd hφ (hMfac C hC).1
    exact ⟨G, hGm, hGd, hGmap⟩
  choose! Gf hGmon hGdeg hGmap using hex
  -- `F` IS the product of the descents
  have hFprod : F = (M.map Gf).prod := by
    refine Polynomial.map_injective (algebraMap O (AdjoinRoot φ))
      (algebraMap_adjoinRoot_injective hφ) ?_
    rw [hFmap, ← hMprod, tauProd_multiset_prod]
    rw [show ((M.map Gf).prod).map (algebraMap O (AdjoinRoot φ))
        = ((M.map Gf).map (fun G => G.map (algebraMap O (AdjoinRoot φ)))).prod from
      (Multiset.prod_hom _ (Polynomial.mapRingHom
        (algebraMap O (AdjoinRoot φ))).toMonoidHom).symm]
    rw [Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun C hC => (hGmap C hC).symm)
  -- so it IS the monic factorization of `F` (legs: monic + irreducible)
  have hFfac : IsMonicFactorization F (M.map Gf) := by
    refine ⟨?_, hFprod.symm⟩
    intro G hG
    obtain ⟨C, hC, rfl⟩ := Multiset.mem_map.mp hG
    exact ⟨hGmon C hC, irreducible_descent_tauProd hφ (hMfac C hC).1 (hMfac C hC).2
      (factor_residual_shape hφ hB hBres hC) (hGmon C hC) (hGmap C hC)⟩
  -- and the per-factor `(e, f)` transport is the two legs plus the degree bookkeeping
  rw [typeOf_data, monicFactors_eq hFfac, Multiset.map_map,
    Uniformity.Density.IFCG25.fScale, typeOf_data, Multiset.map_map]
  refine Multiset.map_congr rfl ?_
  intro C hC
  have hCm : C.Monic := (hMfac C hC).1
  have hCi : Irreducible C := (hMfac C hC).2
  have hCpos : 0 < C.natDegree := by
    rcases Nat.eq_zero_or_pos C.natDegree with h0 | h0
    · exact absurd ((hCm.natDegree_eq_zero).mp h0 ▸ isUnit_one) hCi.not_isUnit
    · exact h0
  have hfC : inertiaDegOf (Gf C) = φ.natDegree * inertiaDegOf C :=
    hinert C (Gf C) hCm hCi (factor_residual_shape hφ hB hBres hC) (hGmon C hC)
      (hGmap C hC)
  have hfCpos : 0 < inertiaDegOf C :=
    inertiaDegOf_pos (normValues_nonempty hCm hCpos)
  show ((efPair (Gf C)).1, (efPair (Gf C)).2) = ((efPair C).1, φ.natDegree * (efPair C).2)
  refine Prod.ext ?_ hfC
  show ramIndexOf (Gf C) = ramIndexOf C
  rw [ramIndexOf, ramIndexOf, hfC, hGdeg C hC,
    Nat.mul_div_mul_left _ _ hφ.pos]

end Skeleton

/-! ## §6 — the uniform reduction: `UnramifiedBlockCount` from the type-descent law -/

/-- ★★ **THE NAMED UNIFORM TYPE-DESCENT LAW**: at every base, every degree-`δ` key and
every lift/block pair of the `p^e` stratum, the base type is the `fScale δ` of the block
type.  This is the ONE remaining input to UBB's count law. -/
def BlockTypeDescent (δ e : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (φ : Polynomial O) (hφ : IsKey φ), φ.natDegree = δ →
    letI := keyIsDomain hφ
    letI := adjoinRoot_isDVR hφ
    letI := adjoinRoot_isAdicComplete hφ
    letI := adjoinRoot_finite_residueField hφ
    BlockDescentAt hφ e

/-- ★★ **THE ONE REMAINING LEG — the inertia scaling.**  For a monic irreducible `C`
over the unramified extension whose residual is a power of the canonical linear point,
and `G` the base descent of its conjugate product `∏_β τ_β(C)`, the residue degree
multiplies by `δ`:

    inertiaDegOf_O G = δ · inertiaDegOf_{O'} C.

This is the `inertiaDegOf`-definition work of Chapter-B scale (B.51/B.52/B.54/B.55 are
the model): the norm from `O[X]/(G)` factors, after base change, into the `δ`
conjugate norms over `O'`, each of the same valuation.  Everything else in the census
bridge is discharged in this file. -/
def InertiaScaling (δ : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (φ : Polynomial O) (hφ : IsKey φ), φ.natDegree = δ →
    letI := keyIsDomain hφ
    letI := adjoinRoot_isDVR hφ
    letI := adjoinRoot_isAdicComplete hφ
    letI := adjoinRoot_finite_residueField hφ
    ∀ (C : Polynomial (AdjoinRoot φ)) (G : Polynomial O), C.Monic → Irreducible C →
      C.map (residue (AdjoinRoot φ))
        = (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree →
      G.Monic → G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C →
      inertiaDegOf G = δ * inertiaDegOf C

/-- ★★★ **THE DESCENT LAW FROM THE INERTIA LEG ALONE** (the irreducibility leg is
`irreducible_descent_tauProd`, proved above). -/
theorem blockTypeDescent_of_inertiaScaling {δ e : ℕ} (h : InertiaScaling δ) :
    BlockTypeDescent δ e := by
  intro O _ _ _ _ _ φ hφ hdeg
  letI i1 : IsDomain (AdjoinRoot φ) := keyIsDomain hφ
  letI i2 : IsDiscreteValuationRing (AdjoinRoot φ) := adjoinRoot_isDVR hφ
  letI i3 : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  letI i4 : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hφ
  have hleg := h O φ hφ hdeg
  subst hdeg
  exact blockDescentAt_of_legs hφ hleg

/-- ★★★ **THE COUNT LAW FROM THE DESCENT LAW**: `BlockTypeDescent δ e` implies UBB's
`UnramifiedBlockCount δ e` — the whole block correspondence (Frobenius-free conjugation
family, invariants, Hensel blocks, level exactness, the constructed surjectivity) is
discharged here; only the type transport remains. -/
theorem unramifiedBlockCount_of_blockTypeDescent {δ e : ℕ}
    (h : BlockTypeDescent δ e) : UnramifiedBlockCount δ e := by
  intro O _ _ _ _ _ φ hφ hdeg s' N hN
  letI i1 : IsDomain (AdjoinRoot φ) := keyIsDomain hφ
  letI i2 : IsDiscreteValuationRing (AdjoinRoot φ) := adjoinRoot_isDVR hφ
  letI i3 : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  letI i4 : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hφ
  have hdesc := h O φ hφ hdeg
  subst hdeg
  exact stratDecCount_eq_of_blockDescent hφ hN hdesc s'

/-- ★★★ **The bridge from the descent law** (composing UBB's reduction). -/
theorem unramifiedBlockBridge_of_blockTypeDescent {δ e : ℕ} (hδ : 1 ≤ δ)
    (h : BlockTypeDescent δ e) : UnramifiedBlockBridge δ e :=
  unramifiedBlockBridge_of_blockCount hδ (unramifiedBlockCount_of_blockTypeDescent h)

/-- ★★★ **THE COUNT LAW FROM THE INERTIA LEG** — at EVERY `e` from the single
`e`-independent leg. -/
theorem unramifiedBlockCount_of_inertiaScaling {δ : ℕ} (h : InertiaScaling δ) (e : ℕ) :
    UnramifiedBlockCount δ e :=
  unramifiedBlockCount_of_blockTypeDescent (blockTypeDescent_of_inertiaScaling h)

/-- ★★★ **The bridge from the inertia leg**, at every `e`. -/
theorem unramifiedBlockBridge_of_inertiaScaling {δ : ℕ} (hδ : 1 ≤ δ)
    (h : InertiaScaling δ) (e : ℕ) : UnramifiedBlockBridge δ e :=
  unramifiedBlockBridge_of_blockCount hδ (unramifiedBlockCount_of_inertiaScaling h e)

/-! ## §8 — ★★★ the census front, re-based on ONE ONE-PARAMETER LEG -/

/-- ★★★ **THE ALL-DEGREE DECIDED SLICE from the remainder laws and the inertia leg**:
composing IFCG27's capstone with this file's reduction, the whole fractional-slope census
front rests on exactly `ConeRemainderLaw e σ` (every `e ≥ 2`; `e = 2` closed) and the
ONE-PARAMETER inertia-scaling leg `InertiaScaling δ` (every `δ ≥ 2`).  The `(δ, e)`
count-law FAMILY is gone: one leg per base degree now covers every `e`, and the entire
block correspondence (conjugation family, invariants, Hensel blocks, level exactness,
conjugate-product irreducibility) is discharged. -/
theorem decidedSliceAt_all_of_remainder_inertiaScaling
    (hR : ∀ e : ℕ, 2 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k →
        Uniformity.Density.IFCG14.DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Uniformity.Density.IFCG14.Witnessed e σ →
        Uniformity.Density.IFCG24.ConeRemainderLaw e σ)
    (hIS : ∀ δ : ℕ, 2 ≤ δ → InertiaScaling δ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_remainder_blockCount hR
    (fun δ e h2δ _ => unramifiedBlockCount_of_inertiaScaling (hIS δ h2δ) e)

end Uniformity.Density.IFCG29

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG29.resEmb
#print axioms Uniformity.Density.IFCG29.map_map_residue_adjoinRoot
#print axioms Uniformity.Density.IFCG29.card_keyRoots
#print axioms Uniformity.Density.IFCG29.nodup_keyRoots
#print axioms Uniformity.Density.IFCG29.keyRes_eq_prod
#print axioms Uniformity.Density.IFCG29.exists_isRoot_of_mem_keyRoots
#print axioms Uniformity.Density.IFCG29.isRoot_unique
#print axioms Uniformity.Density.IFCG29.tau
#print axioms Uniformity.Density.IFCG29.tau_comp
#print axioms Uniformity.Density.IFCG29.tau_bijective
#print axioms Uniformity.Density.IFCG29.exists_resTau_eq
#print axioms Uniformity.Density.IFCG29.exists_resEmb_eq_of_forall_resTau
#print axioms Uniformity.Density.IFCG29.exists_algebraMap_eq_of_forall_tau
#print axioms Uniformity.Density.IFCG29.exists_block_family
#print axioms Uniformity.Density.IFCG29.block_family_conj
#print axioms Uniformity.Density.IFCG29.map_algebraMap_eq_prod_tau
#print axioms Uniformity.Density.IFCG29.exists_block
#print axioms Uniformity.Density.IFCG29.mem_pow_maximalIdeal_of_algebraMap
#print axioms Uniformity.Density.IFCG29.fScale_injective
#print axioms Uniformity.Density.IFCG29.block_level_exact
#print axioms Uniformity.Density.IFCG29.tauProd_map_tau
#print axioms Uniformity.Density.IFCG29.exists_descent_tauProd
#print axioms Uniformity.Density.IFCG29.exists_baseLift_of_block
#print axioms Uniformity.Density.IFCG29.exists_isBlockClass
#print axioms Uniformity.Density.IFCG29.isBlockClass_unique
#print axioms Uniformity.Density.IFCG29.isBlockClass_injective
#print axioms Uniformity.Density.IFCG29.exists_isBlockClass_of_stratum
#print axioms Uniformity.Density.IFCG29.decidedAt_block_of_base
#print axioms Uniformity.Density.IFCG29.decidedAt_base_of_block
#print axioms Uniformity.Density.IFCG29.stratDecCount_eq_of_blockDescent
#print axioms Uniformity.Density.IFCG29.factor_residual_shape
#print axioms Uniformity.Density.IFCG29.irreducible_map_tau
#print axioms Uniformity.Density.IFCG29.monicFactors_map_tau
#print axioms Uniformity.Density.IFCG29.nodup_conjugates
#print axioms Uniformity.Density.IFCG29.irreducible_descent_tauProd
#print axioms Uniformity.Density.IFCG29.blockDescentAt_of_legs
#print axioms Uniformity.Density.IFCG29.blockTypeDescent_of_inertiaScaling
#print axioms Uniformity.Density.IFCG29.unramifiedBlockCount_of_blockTypeDescent
#print axioms Uniformity.Density.IFCG29.unramifiedBlockCount_of_inertiaScaling
#print axioms Uniformity.Density.IFCG29.unramifiedBlockBridge_of_inertiaScaling
#print axioms Uniformity.Density.IFCG29.decidedSliceAt_all_of_remainder_inertiaScaling
