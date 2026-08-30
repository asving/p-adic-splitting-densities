/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG25
import Uniformity.ChapI.IFCG19
import Uniformity.Quarry.AdjoinRootDVR
import Uniformity.ChapB.B52
import Uniformity.ChapB.B53b

/-!
# Uniformity.ChapI.IFCG27 — [UBB 2026-08-30] the unramified extension package: the
bridge's scalar-extension clause closed, the vanishing half proved outright, and the
open heart reduced to ONE named count law

CN5 (IFCG25) re-based the census front on two open families; this file attacks the
second, `UnramifiedBlockBridge δ e`.  Its three open legs were: (a) `IsAdicComplete`
transport to the unramified extension `O' = AdjoinRoot φ`; (b) the residue-cardinality
count `q' = q^δ`; (c) THE HEART — the level-exact Hensel block correspondence with the
`fScale δ` inertia scaling.  Here:

* **§1–§2 legs (a) and (b) CLOSE.**  `natCard_adjoinRoot` counts `K[x]/(g)` over a
  finite field through the power basis; `isPrecomplete_of_basis` proves that ANY finite
  free module over a ring with `IsPrecomplete I R` is `I`-adically precomplete
  (coordinatewise, through `mem_smul_top_iff_repr`), and `adjoinRoot_isAdicComplete`
  assembles the full completeness of `AdjoinRoot φ` at its own maximal ideal via the
  Quarry's `𝔪' = 𝔪·O'` and mathlib's `IsAdicComplete.map_algebraMap_iff`.
* **§3 THE PACKAGE**: over any key `φ` (monic, positive degree, irreducible residual),
  `AdjoinRoot φ` is a complete DVR with finite residue field of cardinality
  `q ^ deg φ` — every instance the bridge's extension telescope demands, as named
  theorems (`adjoinRoot_isDVR`, `adjoinRoot_maximalIdeal_eq`, `adjoinRoot_isAdicComplete`,
  `adjoinRoot_finite_residueField`, `residueCard_adjoinRoot`).
* **§4 the degree-`δ` menu is inhabited**: `exists_monic_irreducible_natDegree` — over
  EVERY finite field and every `δ ≥ 1` there is a monic irreducible of degree exactly
  `δ` (positivity read off IFCG19's Möbius necklace identity; the `(1, δ)` term `q^δ`
  dominates the geometric tail).  Hence **the bridge's scalar-extension clause is a
  theorem** (`exists_scalarExtension`).
* **§5 ★ THE VANISHING HALF OF THE HEART, PROVED OUTRIGHT**
  (`stratDecCount_pow_eq_zero_of_not_fScale`): every label achieved on the stratum of
  `p^e` lies in `fScale δ`'s range — each monic irreducible factor of a lift has
  residual a positive power of `p`, so B.52's `key_natDegree_dvd_inertiaDegOf` forces
  `δ ∣ f` on every factor.  No Hensel blocks, no Frobenius: the bridge's vanishing
  clause carries no open content.
* **§6 ★★ THE HONEST REMAINDER, minimal**: `UnramifiedBlockCount δ e` — the count
  equality `stratDecCount O (δe) ⟨fScale δ s'⟩ N (p^e) = stratDecCount O' e ⟨s'⟩ N (p'^e)`
  at the CONCRETE extension `O' = AdjoinRoot φ` and the CANONICAL linear point
  `p' = X − θ̄` (`θ̄` the residue of the adjoined root), with no existential telescope
  left for the consumer.  `unramifiedBlockBridge_of_blockCount` PROVES
  `UnramifiedBlockCount δ e → UnramifiedBlockBridge δ e` (`δ, e ≥ 1`): the package
  supplies the telescope, §5 the vanishing clause.
* **§7 nonvacuity**: `unramifiedBlockCount_one` — the `e = 1` member holds at EVERY
  `δ ≥ 1` (both sides are the inert monomial census of IFCG19; the `fScale`
  bookkeeping `fScale δ {(1,1)} = {(1,δ)}` matches exactly).

## What remains open (the exact fence)

`UnramifiedBlockCount δ e` for `δ, e ≥ 2` — the level-exact Hensel block
correspondence itself (block decomposition over `O'`, Frobenius conjugacy/descent, and
the `typeOf` descent `typeOf_O F = fScale δ (typeOf_{O'} B₀)`).  This is the ONE open
statement; everything else in `UnramifiedBlockBridge` is closed here.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG27

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG17
open Uniformity.Density.IFCG25 (fScale UnramifiedBlockBridge)
open Uniformity.Density.Leaf (IsKey keyIsDomain key_natDegree_dvd_inertiaDegOf)

attribute [local instance] Classical.propDecidable

/-! ## §1 — counting `AdjoinRoot` over a finite field (leg (b)'s engine) -/

/-- `K[x]/(g)` is finite over a finite field (power-basis coordinates). -/
theorem finite_adjoinRoot_of_monic {K : Type*} [Field K] [Finite K] {g : Polynomial K}
    (hg : g.Monic) : Finite (AdjoinRoot g) :=
  Finite.of_equiv _ (AdjoinRoot.powerBasis' hg).basis.equivFun.toEquiv.symm

/-- **The point count of `K[x]/(g)`**: `#(AdjoinRoot g) = (#K) ^ deg g`. -/
theorem natCard_adjoinRoot {K : Type*} [Field K] [Finite K] {g : Polynomial K}
    (hg : g.Monic) : Nat.card (AdjoinRoot g) = Nat.card K ^ g.natDegree := by
  rw [Nat.card_congr (AdjoinRoot.powerBasis' hg).basis.equivFun.toEquiv]
  simp [Nat.card_fun]

/-! ## §2 — leg (a): adic completeness of finite free modules, coordinatewise -/

/-- Membership in `I • ⊤` of a finite free module reads coordinatewise on any basis. -/
theorem mem_smul_top_iff_repr {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      rw [map_smul]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro y z hy hz i
      rw [map_add]
      simp only [Finsupp.add_apply]
      exact I.add_mem (hy i) (hz i)
  · intro h
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/-- **Finite free modules inherit precompleteness**: if `R` is `I`-adically precomplete
then so is any module with a finite basis (limits taken coordinatewise). -/
theorem isPrecomplete_of_basis {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  constructor
  intro f hf
  have hsm : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = (I ^ n : Ideal R) := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hcoord : ∀ i : ι, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec ‹IsPrecomplete I R› ?_
    intro m n hmn
    have hmem := hf hmn
    rw [SModEq.sub_mem] at hmem ⊢
    rw [hsm m]
    have hcm := (mem_smul_top_iff_repr b (I ^ m) _).mp hmem i
    rwa [map_sub, Finsupp.sub_apply] at hcm
  choose L hL using hcoord
  refine ⟨∑ i, L i • b i, fun n => ?_⟩
  rw [SModEq.sub_mem]
  refine (mem_smul_top_iff_repr b (I ^ n) _).mpr fun i => ?_
  rw [map_sub, Finsupp.sub_apply]
  have hrepr : b.repr (∑ j, L j • b j) i = L i := by
    rw [map_sum]
    simp only [map_smul, Module.Basis.repr_self]
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  rw [hrepr]
  have hn := hL i n
  rw [SModEq.sub_mem, hsm n] at hn
  exact hn

/-! ## §3 — THE PACKAGE: `AdjoinRoot φ` is a complete DVR with `q' = q ^ deg φ` -/

section Package

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {φ : Polynomial O}

/-- The unramified extension is a DVR (Quarry backport, repackaged over a key). -/
theorem adjoinRoot_isDVR [IsDomain (AdjoinRoot φ)] (hφ : IsKey φ) :
    IsDiscreteValuationRing (AdjoinRoot φ) :=
  (AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hφ.monic
    (natDegree_pos_iff_degree_pos.mp hφ.pos).ne' hφ.irred).2.1

/-- The extension is unramified: `𝔪' = 𝔪 · O'`. -/
theorem adjoinRoot_maximalIdeal_eq [IsLocalRing (AdjoinRoot φ)] (hφ : IsKey φ) :
    maximalIdeal (AdjoinRoot φ) = (maximalIdeal O).map (algebraMap O (AdjoinRoot φ)) :=
  (eq_maximalIdeal (AdjoinRoot.isMaximal_map_maximalIdeal hφ.irred)).symm

/-- **Leg (a) closes**: the unramified extension of a complete DVR is complete at its
own maximal ideal.  `𝔪' = 𝔪·O'` (Quarry) turns the question into `𝔪`-adic completeness
of `O'` as an `O`-module (mathlib's `map_algebraMap_iff`), where Hausdorffness is the
Krull instance for finite modules and precompleteness is §2's coordinatewise limit. -/
theorem adjoinRoot_isAdicComplete [IsAdicComplete (maximalIdeal O) O]
    [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)] (hφ : IsKey φ) :
    IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) := by
  haveI : Module.Finite O (AdjoinRoot φ) := hφ.monic.finite_adjoinRoot
  rw [adjoinRoot_maximalIdeal_eq hφ, IsAdicComplete.map_algebraMap_iff]
  haveI : IsPrecomplete (maximalIdeal O) (AdjoinRoot φ) :=
    isPrecomplete_of_basis (AdjoinRoot.powerBasis' hφ.monic).basis _
  exact IsAdicComplete.mk

/-- The extension's residue field is finite (through the Quarry residue-field
equivalence and §1's finiteness). -/
theorem adjoinRoot_finite_residueField [IsLocalRing (AdjoinRoot φ)]
    [Finite (ResidueField O)] (hφ : IsKey φ) :
    Finite (ResidueField (AdjoinRoot φ)) := by
  haveI : Finite (AdjoinRoot (φ.map (residue O))) :=
    finite_adjoinRoot_of_monic (hφ.monic.map _)
  exact Finite.of_equiv _
    (AdjoinRoot.residueFieldEquiv (adjoinRoot_maximalIdeal_eq hφ)).toEquiv.symm

/-- **Leg (b) closes**: `q' = q ^ deg φ`. -/
theorem residueCard_adjoinRoot [IsDomain (AdjoinRoot φ)]
    [IsDiscreteValuationRing (AdjoinRoot φ)] [Finite (ResidueField (AdjoinRoot φ))]
    [Finite (ResidueField O)] (hφ : IsKey φ) :
    residueCard (AdjoinRoot φ) = residueCard O ^ φ.natDegree := by
  show Nat.card (ResidueField (AdjoinRoot φ)) = Nat.card (ResidueField O) ^ φ.natDegree
  rw [Nat.card_congr
    (AdjoinRoot.residueFieldEquiv (A := O) (adjoinRoot_maximalIdeal_eq hφ)).toEquiv,
    natCard_adjoinRoot (hφ.monic.map _), hφ.monic.natDegree_map]

end Package

/-! ## §4 — the degree-`δ` residual menu is inhabited; the scalar-extension clause -/

/-- **Existence of a monic irreducible of exact degree `δ` over every finite field.**
Positivity of the necklace count: in IFCG19's Möbius identity
`δ·N_δ = Σ_{ab=δ} μ(a) q^b`, the `(1,δ)` term contributes `q^δ` and the tail is
bounded by the geometric sum `q^δ − 1`. -/
theorem exists_monic_irreducible_natDegree (K : Type*) [Field K] [Finite K] {δ : ℕ}
    (hδ : 1 ≤ δ) : ∃ p : Polynomial K, p.Monic ∧ p.natDegree = δ ∧ Irreducible p := by
  haveI : Fintype K := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  haveI hempty : IsEmpty (IFCG4.IrredOfDeg K δ) :=
    ⟨fun f => hcon f.1 f.2.1 f.2.2.1 f.2.2.2⟩
  have hzero : Nat.card (IFCG4.IrredOfDeg K δ) = 0 := Nat.card_of_isEmpty
  have hmob := IFCG19.mul_natCard_irred_eq_moebius_sum (K := K) δ hδ
  rw [hzero] at hmob
  simp only [Nat.cast_zero, mul_zero] at hmob
  set q : ℤ := (Fintype.card K : ℤ) with hq
  have hq2 : (2 : ℤ) ≤ q := by
    have : 1 < Fintype.card K := Fintype.one_lt_card
    omega
  have hmem : ((1, δ) : ℕ × ℕ) ∈ δ.divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨one_mul δ, by omega⟩
  rw [← Finset.add_sum_erase _ _ hmem] at hmob
  simp only [ArithmeticFunction.moebius_apply_one, one_mul] at hmob
  set E := (δ.divisorsAntidiagonal).erase (1, δ) with hE
  -- the second coordinates of `E` inject into `range δ`
  have hinj : ∀ x ∈ E, ∀ y ∈ E, x.2 = y.2 → x = y := by
    intro x hx y hy hxy
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_of_mem_erase hx)).1
    have hyprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_of_mem_erase hy)).1
    have hx2 : x.2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hxprod
      omega
    refine Prod.ext ?_ hxy
    have hmm : x.1 * x.2 = y.1 * x.2 := by
      rw [hxprod, hxy]
      exact hyprod.symm
    exact Nat.eq_of_mul_eq_mul_right (by omega) hmm
  have hsub : E.image (fun x : ℕ × ℕ => x.2) ⊆ Finset.range δ := by
    intro j hj
    obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hj
    obtain ⟨hxne, hxs⟩ := Finset.mem_erase.mp hx
    rw [Finset.mem_range, ← hxj]
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp hxs).1
    have hx2δ : x.2 ≠ δ := by
      intro h2
      apply hxne
      have hx1 : x.1 = 1 := by
        rw [h2] at hxprod
        have hone : x.1 * δ = 1 * δ := by rw [one_mul]; exact hxprod
        exact Nat.eq_of_mul_eq_mul_right (by omega) hone
      exact Prod.ext hx1 h2
    have hle : x.2 ≤ δ := Nat.le_of_dvd (by omega) (Dvd.intro_left x.1 hxprod)
    omega
  -- the tail is bounded below by −(the full geometric sum below δ)
  have h3 : (∑ x ∈ E, q ^ x.2) ≤ ∑ j ∈ Finset.range δ, q ^ j := by
    rw [show (∑ x ∈ E, q ^ x.2)
        = ∑ j ∈ E.image (fun x : ℕ × ℕ => x.2), q ^ j from (Finset.sum_image hinj).symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun j _ _ => pow_nonneg (by omega) _
  have hterm : ∀ x ∈ E, -(q ^ x.2) ≤ (ArithmeticFunction.moebius x.1 : ℤ) * q ^ x.2 := by
    intro x _
    have hqpow : (0 : ℤ) ≤ q ^ x.2 := pow_nonneg (by omega) _
    have hmu3 : (ArithmeticFunction.moebius x.1 : ℤ) = 0
        ∨ (ArithmeticFunction.moebius x.1 : ℤ) = 1
        ∨ (ArithmeticFunction.moebius x.1 : ℤ) = -1 := by
      by_cases hsf : Squarefree x.1
      · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]
        rcases Nat.even_or_odd (ArithmeticFunction.cardFactors x.1) with hev | hod
        · right; left; exact hev.neg_one_pow
        · right; right; exact hod.neg_one_pow
      · left
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    rcases hmu3 with h0 | h1 | hm1
    · rw [h0, zero_mul]; omega
    · rw [h1, one_mul]; omega
    · rw [hm1, neg_one_mul]
  have htail : -(∑ j ∈ Finset.range δ, q ^ j)
      ≤ ∑ x ∈ E, (ArithmeticFunction.moebius x.1 : ℤ) * q ^ x.2 :=
    calc -(∑ j ∈ Finset.range δ, q ^ j)
        ≤ -(∑ x ∈ E, q ^ x.2) := neg_le_neg h3
      _ = ∑ x ∈ E, -(q ^ x.2) := by rw [← Finset.sum_neg_distrib]
      _ ≤ ∑ x ∈ E, (ArithmeticFunction.moebius x.1 : ℤ) * q ^ x.2 :=
          Finset.sum_le_sum hterm
  -- the geometric sum is at most `q^δ − 1`
  have hgeom : (∑ j ∈ Finset.range δ, q ^ j) ≤ q ^ δ - 1 := by
    have hmul := geom_sum_mul q δ
    have hnonneg : (0 : ℤ) ≤ ∑ j ∈ Finset.range δ, q ^ j :=
      Finset.sum_nonneg fun j _ => pow_nonneg (by omega) _
    nlinarith
  -- assemble: 0 = q^δ + tail ≥ q^δ − (q^δ − 1) = 1
  have hqδ : (1 : ℤ) ≤ q ^ δ := one_le_pow₀ (by omega)
  omega

/-- **The bridge's scalar-extension clause, proved**: for every complete DVR `O` with
finite residue field and every `δ ≥ 1`, SOME complete DVR with finite residue field of
cardinality `q^δ` exists — namely `AdjoinRoot φ` for `φ` a monic lift of a degree-`δ`
irreducible residual. -/
theorem exists_scalarExtension (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {δ : ℕ} (hδ : 1 ≤ δ) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (maximalIdeal O') O') (_ : Finite (ResidueField O')),
      residueCard O' = residueCard O ^ δ := by
  obtain ⟨p, hpm, hpd, hpi⟩ := exists_monic_irreducible_natDegree (ResidueField O) hδ
  obtain ⟨φ, hφm, hφmap, hφd⟩ := Uniformity.Hensel.exists_monic_lift hpm
  have hkey : IsKey φ := ⟨hφm, by rw [hφd, hpd]; omega, by rw [hφmap]; exact hpi⟩
  letI i1 : IsDomain (AdjoinRoot φ) := keyIsDomain hkey
  letI i2 : IsDiscreteValuationRing (AdjoinRoot φ) := adjoinRoot_isDVR hkey
  letI i3 : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hkey
  letI i4 : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hkey
  refine ⟨AdjoinRoot φ, inferInstance, i1, i2, i3, i4, ?_⟩
  rw [residueCard_adjoinRoot hkey, hφd, hpd]

/-! ## §5 — ★ THE VANISHING HALF, proved outright -/

section Vanish

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Every monic irreducible factor of a `p^e`-residual polynomial has residual a
POSITIVE power of `p` (unique factorization over the residue field). -/
theorem factor_residual_pow {φ : Polynomial O} (hφ : IsKey φ) {e : ℕ}
    {F g : Polynomial O} (hF : F.Monic)
    (hres : F.map (residue O) = (φ.map (residue O)) ^ e)
    (hg : g ∈ monicFactors F) :
    ∃ k, 0 < k ∧ g.map (residue O) = (φ.map (residue O)) ^ k := by
  obtain ⟨hfac, hprod⟩ := monicFactors_spec hF
  obtain ⟨hgm, hgi⟩ := hfac g hg
  have hdvd : g ∣ F := by
    rw [← hprod]
    exact Multiset.dvd_prod hg
  have hdvdmap : g.map (residue O) ∣ (φ.map (residue O)) ^ e := by
    rw [← hres]
    exact Polynomial.map_dvd _ hdvd
  have hp_prime : Prime (φ.map (residue O)) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hφ.irred
  obtain ⟨k, hk_le, hassoc⟩ := (dvd_prime_pow hp_prime e).mp hdvdmap
  have heq : g.map (residue O) = (φ.map (residue O)) ^ k :=
    Polynomial.eq_of_monic_of_associated (hgm.map _) ((hφ.monic.map _).pow _) hassoc
  refine ⟨k, ?_, heq⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso
    rw [hk, pow_zero] at heq
    have hdeg0 : g.natDegree = 0 := by
      have hcast := congrArg natDegree heq
      rwa [hgm.natDegree_map, natDegree_one] at hcast
    have hg1 : g = 1 := hgm.natDegree_eq_zero.mp hdeg0
    exact hgi.not_isUnit (hg1 ▸ isUnit_one)
  · exact hk

/-- **The achieved labels on the `p^e` stratum descend**: `typeOf F` lies in
`fScale (deg φ)`'s range — B.52 forces `deg φ ∣ f` on every irreducible factor. -/
theorem typeOf_mem_fScale_range {φ : Polynomial O} (hφ : IsKey φ) {e : ℕ}
    {F : Polynomial O} (hF : F.Monic)
    (hres : F.map (residue O) = (φ.map (residue O)) ^ e) :
    ∃ s' : Multiset (ℕ × ℕ), (typeOf F).data = fScale φ.natDegree s' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨(typeOf F).data.map (fun x => (x.1, x.2 / φ.natDegree)), ?_⟩
  simp only [Uniformity.Density.IFCG25.fScale, Multiset.map_map]
  symm
  conv_rhs => rw [← Multiset.map_id ((typeOf F).data)]
  refine Multiset.map_congr rfl ?_
  intro x hx
  rw [typeOf_data] at hx
  obtain ⟨g, hgmem, hgx⟩ := Multiset.mem_map.mp hx
  obtain ⟨hgm, hgi⟩ := (monicFactors_spec hF).1 g hgmem
  obtain ⟨k, hk, hgres⟩ := factor_residual_pow hφ hF hres hgmem
  have hgdeg : g.natDegree = k * φ.natDegree := by
    have hcast := congrArg natDegree hgres
    rwa [hgm.natDegree_map, natDegree_pow, hφ.monic.natDegree_map] at hcast
  have hdpos : 0 < g.natDegree := by
    rw [hgdeg]
    exact Nat.mul_pos hk hφ.pos
  have hdvd : φ.natDegree ∣ inertiaDegOf g :=
    key_natDegree_dvd_inertiaDegOf hπ hφ hgm hdpos hk hgres
  subst hgx
  show ((efPair g).1, φ.natDegree * ((efPair g).2 / φ.natDegree)) = id (efPair g)
  have h2 : (efPair g).2 = inertiaDegOf g := rfl
  rw [id_eq]
  exact Prod.ext rfl (by rw [h2]; exact Nat.mul_div_cancel' hdvd)

/-- ★ **The bridge's vanishing clause is a theorem**: off `fScale`'s range the
stratum-refined decided count of `p^e` vanishes at every level. -/
theorem stratDecCount_pow_eq_zero_of_not_fScale {φ : Polynomial O} (hφ : IsKey φ)
    {e : ℕ} {s : Multiset (ℕ × ℕ)} (hs : ∀ s', s ≠ fScale φ.natDegree s') (N : ℕ) :
    stratDecCount O (φ.natDegree * e) ⟨s⟩ N ((φ.map (residue O)) ^ e) = 0 := by
  by_contra hcon
  have hne : (decidedSet O (φ.natDegree * e) ⟨s⟩ N
      ∩ levelZeroStratum O (φ.natDegree * e) N ((φ.map (residue O)) ^ e)
      : Set (Coeff O (φ.natDegree * e) N)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [stratDecCount, hemp] at hcon
    simp at hcon
  obtain ⟨c, hcdec, hcstr⟩ := hne
  obtain ⟨a, ha⟩ := proj_surjective' O (φ.natDegree * e) N c
  have hty : typeOf (monicPoly a) = ⟨s⟩ := hcdec a ha
  have hstr : (monicPoly a).map (residue O) = (φ.map (residue O)) ^ e := hcstr a ha
  obtain ⟨s', hs'⟩ := typeOf_mem_fScale_range hφ (monicPoly_monic a) hstr
  rw [hty] at hs'
  exact hs s' hs'

end Vanish

/-! ## §6 — ★★ THE HONEST REMAINDER and the bridge consumption -/

/-- ★★ **THE ONE OPEN COUNT LAW** — the minimal named residue of the block bridge.
At the CONCRETE unramified extension `O' = AdjoinRoot φ` (all instances supplied by
§3's package) and the CANONICAL linear point `p' = X − θ̄` (`θ̄` the residue of the
adjoined root), the level-`N` `σ`-decided stratum census of `p^e` over `O` at the
scaled label `fScale δ s'` equals the census of `p'^e` over `O'` at `s'`.

Mathematically: Hensel splits any lift of the `p^e` stratum into `δ` conjugate blocks
over `O'`; the `θ̄`-block realizes the correspondence level-exactly, and the type
transport is `fScale δ`.  This is the exact content still open after this file. -/
def UnramifiedBlockCount (δ e : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (φ : Polynomial O) (hφ : IsKey φ), φ.natDegree = δ →
    ∀ (s' : Multiset (ℕ × ℕ)) (N : ℕ), 1 ≤ N →
    letI := keyIsDomain hφ
    letI := adjoinRoot_isDVR hφ
    letI := adjoinRoot_finite_residueField hφ
    stratDecCount O (δ * e) ⟨fScale δ s'⟩ N ((φ.map (residue O)) ^ e)
      = stratDecCount (AdjoinRoot φ) e ⟨s'⟩ N
          ((X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ e)

/-- ★★ **The bridge follows from the count law alone**: the scalar-extension clause is
§4's theorem, the extension telescope is §3's package at a monic lift of the given
point, and the vanishing clause is §5's theorem.  `UnramifiedBlockCount δ e` is the
ONLY open input. -/
theorem unramifiedBlockBridge_of_blockCount {δ e : ℕ} (hδ : 1 ≤ δ)
    (h : UnramifiedBlockCount δ e) : UnramifiedBlockBridge δ e := by
  intro O _ _ _ _ _
  refine ⟨exists_scalarExtension O hδ, ?_⟩
  intro p hpm hpd hpi
  obtain ⟨φ, hφm, hφmap, hφd⟩ := Uniformity.Hensel.exists_monic_lift hpm
  have hdeg : φ.natDegree = δ := hφd.trans hpd
  have hkey : IsKey φ := ⟨hφm, by omega, by rw [hφmap]; exact hpi⟩
  letI i1 : IsDomain (AdjoinRoot φ) := keyIsDomain hkey
  letI i2 : IsDiscreteValuationRing (AdjoinRoot φ) := adjoinRoot_isDVR hkey
  letI i3 : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hkey
  letI i4 : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hkey
  refine ⟨AdjoinRoot φ, inferInstance, i1, i2, i3, i4,
    X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ)), ?_,
    monic_X_sub_C _, natDegree_X_sub_C _, irreducible_X_sub_C _, ?_, ?_⟩
  · rw [residueCard_adjoinRoot hkey, hdeg]
  · intro s' N hN
    have hc := h O φ hkey hdeg s' N hN
    rwa [hφmap] at hc
  · intro s hsne N hN
    have hz := stratDecCount_pow_eq_zero_of_not_fScale hkey
      (fun s2 => by rw [hdeg]; exact hsne s2) N (e := e)
    rwa [hdeg, hφmap] at hz

/-! ## §7 — nonvacuity: the `e = 1` member at every base degree -/

/-- ★ **The count law holds at `e = 1`, every `δ ≥ 1`**: both sides are IFCG19's inert
monomial census (`q^{δ(N−1)}` at the inert label, `0` elsewhere), and
`fScale δ {(1,1)} = {(1,δ)}` matches the labels exactly. -/
theorem unramifiedBlockCount_one {δ : ℕ} (hδ : 1 ≤ δ) : UnramifiedBlockCount δ 1 := by
  intro O _ _ _ _ _ φ hφ hdeg s' N hN
  letI i1 : IsDomain (AdjoinRoot φ) := keyIsDomain hφ
  letI i2 : IsDiscreteValuationRing (AdjoinRoot φ) := adjoinRoot_isDVR hφ
  letI i3 : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  letI i4 : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hφ
  have hpm : (φ.map (residue O)).Monic := hφ.monic.map _
  have hpd : (φ.map (residue O)).natDegree = δ := by rw [hφ.monic.natDegree_map, hdeg]
  have hpi : Irreducible (φ.map (residue O)) := hφ.irred
  have hp'm : (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).Monic :=
    monic_X_sub_C _
  have hp'd : (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))).natDegree = 1 :=
    natDegree_X_sub_C _
  have hp'i : Irreducible (X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) :=
    irreducible_X_sub_C _
  rw [pow_one, pow_one, show δ * 1 = δ from Nat.mul_one δ]
  by_cases hs' : s' = {(1, 1)}
  · subst hs'
    have hfs : fScale δ ({((1 : ℕ), (1 : ℕ))} : Multiset (ℕ × ℕ)) = {(1, δ)} := by
      simp [Uniformity.Density.IFCG25.fScale]
    rw [hfs, IFCG19.stratDecCount_irreducible_inert (by omega : 0 < δ) hN hpm hpd hpi,
      IFCG19.stratDecCount_irreducible_inert (by omega : 0 < 1) hN hp'm hp'd hp'i,
      residueCard_adjoinRoot hφ, hdeg, one_mul, ← pow_mul]
  · have hne1 : (⟨fScale δ s'⟩ : FactorizationType) ≠ ⟨{(1, δ)}⟩ := by
      intro hEq
      apply hs'
      have hdata : fScale δ s' = {(1, δ)} := congrArg FactorizationType.data hEq
      obtain ⟨x, hxs, hxe⟩ := Multiset.map_eq_singleton.mp hdata
      have hx1 : x.1 = 1 := congrArg Prod.fst hxe
      have hx2 : δ * x.2 = δ := congrArg Prod.snd hxe
      have hδpos : 0 < δ := by omega
      have hx2' : x.2 = 1 := Nat.eq_of_mul_eq_mul_left hδpos (by rw [hx2, mul_one])
      rw [hxs]
      rw [show x = (1, 1) from Prod.ext hx1 hx2']
    have hne2 : (⟨s'⟩ : FactorizationType) ≠ ⟨{(1, 1)}⟩ := by
      intro hEq
      exact hs' (congrArg FactorizationType.data hEq)
    rw [IFCG19.stratDecCount_irreducible_ne (by omega : 0 < δ) hpi hne1,
      IFCG19.stratDecCount_irreducible_ne (by omega : 0 < 1) hp'i hne2]

/-! ## §8 — ★★★ the census front, re-based once more -/

/-- ★★★ **THE ALL-DEGREE DECIDED SLICE from remainder laws + count laws**: composing
IFCG25's capstone with this file's bridge reduction, the whole fractional-slope census
front now rests on exactly `ConeRemainderLaw e σ` (every `e ≥ 2`; `e = 2` closed) and
`UnramifiedBlockCount δ e` (every `δ, e ≥ 2`; the `e = 1` members closed here) — the
existential bridge telescope is GONE from the open surface. -/
theorem decidedSliceAt_all_of_remainder_blockCount
    (hR : ∀ e : ℕ, 2 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k →
        Uniformity.Density.IFCG14.DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Uniformity.Density.IFCG14.Witnessed e σ →
        Uniformity.Density.IFCG24.ConeRemainderLaw e σ)
    (hBC : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockCount δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG25.decidedSliceAt_all_of_remainder_bridge hR
    (fun δ e h2δ h2e =>
      unramifiedBlockBridge_of_blockCount (by omega) (hBC δ e h2δ h2e))

end Uniformity.Density.IFCG27

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG27.finite_adjoinRoot_of_monic
#print axioms Uniformity.Density.IFCG27.natCard_adjoinRoot
#print axioms Uniformity.Density.IFCG27.mem_smul_top_iff_repr
#print axioms Uniformity.Density.IFCG27.isPrecomplete_of_basis
#print axioms Uniformity.Density.IFCG27.adjoinRoot_isDVR
#print axioms Uniformity.Density.IFCG27.adjoinRoot_maximalIdeal_eq
#print axioms Uniformity.Density.IFCG27.adjoinRoot_isAdicComplete
#print axioms Uniformity.Density.IFCG27.adjoinRoot_finite_residueField
#print axioms Uniformity.Density.IFCG27.residueCard_adjoinRoot
#print axioms Uniformity.Density.IFCG27.exists_monic_irreducible_natDegree
#print axioms Uniformity.Density.IFCG27.exists_scalarExtension
#print axioms Uniformity.Density.IFCG27.factor_residual_pow
#print axioms Uniformity.Density.IFCG27.typeOf_mem_fScale_range
#print axioms Uniformity.Density.IFCG27.stratDecCount_pow_eq_zero_of_not_fScale
#print axioms Uniformity.Density.IFCG27.unramifiedBlockBridge_of_blockCount
#print axioms Uniformity.Density.IFCG27.unramifiedBlockCount_one
#print axioms Uniformity.Density.IFCG27.decidedSliceAt_all_of_remainder_blockCount
