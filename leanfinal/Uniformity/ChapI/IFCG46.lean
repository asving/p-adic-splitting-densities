/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG35
import Uniformity.ChapI.IFCG42
import Uniformity.ChapI.IFCG45
import Uniformity.Density.InertLeaf

/-!
# Uniformity.ChapI.IFCG46 — [UDR 2026-08-30] the σ-free drain REDUCED to the deep
collision tail: `UndecidedDrainAt n` from strong induction on the degree through the
IFCG41/42 resultant-depth engine, with the exact named remainder `DeepTailDrainAt n`

**Unit UDR** (verdict `runs/wave-c/verdict_UDR.md`).  DRN's IFCG45 dissected the capstone's
`a2` field: `(∀ n, DrainageAt n) ↔ (∀ n ≥ 4, UndecidedDrainAt n)` — the σ-free scalar rate
`undecidedSeq O n N → 0` at degrees ≥ 4 is the field's exact open remainder.  THIS file
reduces that remainder along the DEGREE: an undecided level-`N` class either admits a
*shallow split* — a monic factorization of a lift whose resultant depth `v` satisfies
`2v + 1 ≤ N` — or sits in the **deep collision tail**.  For the shallow classes the landed
IFCG41/42 engine is quantitative:

* the decidedness transfer (`decidedAt_mulClass_of_not_dvd_resultant`): a depth-`v` split
  with both factor classes decided at the SHIFTED level `N − v` decides the product at `N`
  — so an UNDECIDED product forces an undecided factor at level `N − v`;
* the q-power fiber law (`natCard_pairNbhd`): at exact depth `v` each product class carries
  `q^v` distinct factor-class pairs in its depth-`v` neighborhood, and the neighborhoods of
  DISTINCT products are disjoint (the product is pinned inside `pairNbhd`) — so the
  undecided-product count is beaten down by `q^{-v}` against the bad-pair count.

Together: `undecidedSeq O n N ≤ deepTailSeq + Σ_{n₁+n₂=n} Σ_{2v+1≤N} q^{-v} ·
(undecidedSeq O n₁ (N−v) + undecidedSeq O n₂ (N−v))` — a geometric convolution against
strictly smaller degrees.  Since the drain is landed at degrees ≤ 3 (IFCG45 §1), strong
induction closes every degree MODULO the tail:

    ★★★ `drainageAt_all_of_deepTailDrain :
          (∀ m, 4 ≤ m → DeepTailDrainAt m) → ∀ n, DrainageAt n`

The capstone's ENTIRE `a2` supply now rests on the single named Prop family
`DeepTailDrainAt n` (n ≥ 4): the proportion of level-`N` classes that are undecided AND
admit no shallow split tends to `0`.  This is the honest hard core — the deep-collision
(near-inseparable) locus — σ-free, factorization-free, and exactly where the H.124
cluster-rate campaign (`FullClusterRateBound`, gates HYP.36 &c.) operates.

**§6 sharpens the remainder further** (`deepTail_residue_primary`): a deep-tail class's
residue reduction is associated to `ψ^k`, `ψ` irreducible, `k ≥ 2` — irreducible
reduction decides the class (CN-21, packaged here as `decidedAt_of_irreducible_residue`),
and a coprime monic residue split IS a depth-`0` shallow split
(`hasShallowSplit_of_coprime_residue_split`, through the landed Hensel leg); the landed
primary classifier (IFCG35 §2c) excludes everything else.  So `DeepTailDrainAt` concerns
exactly the SINGLE-CLUSTER (primary) classes — the census recentring locus.

## Honesty

`DrainageAt`, `UndecidedDrainAt`, `undecidedSeq` are consumed byte-unchanged.  Every
theorem is uniform in `q`, `n`, `N`, over every complete DVR with finite residue field and
every uniformizer.  Nothing is weakened: the reduction is one-directional (tail drain ⟹
full drain) and the remainder is named, not hidden.  Axioms: Lean core only.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.IFCG46

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG41 (classRes classRes_proj mk_pow_dvd_mk_iff)
open Uniformity.Density.IFCG42 (pairNbhd natCard_pairNbhd decidedAt_mulClass_of_not_dvd_resultant)

/-! ## §0 The level-shift fiber count

The landed truncation `coeffFactor n (h : M ≤ N) : Coeff O n N →+ Coeff O n M` preserves
proportions EXACTLY (`card_preimage_coeffFactor`); here it is resolved into the closed
preimage count `#(coeffFactor⁻¹ S) = #S · q^{n(N−M)}`. -/

section Shift

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The fiber count**: the truncation-preimage of a set is exactly `q^{n(N−M)}` times
its size. -/
theorem card_preimage_coeffFactor_eq (n : ℕ) {M N : ℕ} (h : M ≤ N)
    (U : Set (Coeff O n M)) :
    Nat.card ((coeffFactor (O := O) n h) ⁻¹' U)
      = Nat.card U * residueCard O ^ (n * (N - M)) := by
  have h1 := card_preimage_coeffFactor (O := O) n h U
  rw [card_coeff, card_coeff] at h1
  have hsplit : n * N = n * (N - M) + n * M := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h]
  rw [hsplit, pow_add, ← mul_assoc] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero _ (residueCard_pos O).ne')) h1

end Shift

/-! ## §1 Degree-cast transport -/

section Cast

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Re-read a degree-`n` class at the split degree `n₁ + n₂ = n` (pure `Fin`-cast). -/
def castClass {n₁ n₂ n N : ℕ} (hn : n₁ + n₂ = n) (c : Coeff O n N) : Coeff O (n₁ + n₂) N :=
  fun i => c (Fin.cast hn i)

theorem castClass_rfl {m N : ℕ} (c : Coeff O m N) :
    castClass (n₁ := m) (n₂ := 0) rfl c = c := by
  funext i
  simp [castClass, Fin.cast]

theorem castClass_rfl' {n₁ n₂ N : ℕ} (c : Coeff O (n₁ + n₂) N) :
    castClass (hn := rfl) c = c := by
  funext i
  simp [castClass, Fin.cast]

theorem undecidedAt_castClass_iff {n₁ n₂ n N : ℕ} (hn : n₁ + n₂ = n) (c : Coeff O n N) :
    UndecidedAt O (n₁ + n₂) N (castClass hn c) ↔ UndecidedAt O n N c := by
  subst hn
  rw [castClass_rfl']

theorem card_castClass_preimage {n₁ n₂ n N : ℕ} (hn : n₁ + n₂ = n)
    (S : Set (Coeff O (n₁ + n₂) N)) :
    Nat.card {c : Coeff O n N | castClass hn c ∈ S} = Nat.card S := by
  subst hn
  have hset : {c : Coeff O (n₁ + n₂) N | castClass rfl c ∈ S} = S := by
    ext c
    rw [Set.mem_setOf_eq, castClass_rfl']
  rw [hset]

end Cast

/-! ## §2 The buckets and the packing bound

A *bucket* collects the undecided level-`N` classes of degree `n = n₁ + n₂` witnessing a
monic split at exact resultant depth `v`.  The `pairNbhd` fiber law packs each bucket class
`q^v`-to-one into pairs whose product is that class; the decidedness transfer forces every
such pair to carry an undecided factor at the shifted level `N − v`. -/

section Buckets

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The bucket at split degrees `(n₁, n₂)`, level `N`, exact resultant depth `v`. -/
def bucketSet (π : O) (n₁ n₂ N v : ℕ) : Set (Coeff O (n₁ + n₂) N) :=
  {c | UndecidedAt O (n₁ + n₂) N c ∧ ∃ (b₁ : Fin n₁ → O) (b₂ : Fin n₂ → O),
    mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) = c ∧
    π ^ v ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂ ∧
    ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂}

/-- Resultant non-divisibility is stable under coefficientwise congruence mod `π^k`
(`classRes` at level `k` through `classRes_proj`). -/
theorem resultant_not_dvd_congr {π : O} (hπ : Irreducible π) {n₁ n₂ : ℕ} (k : ℕ)
    {b₁ b₁' : Fin n₁ → O} {b₂ b₂' : Fin n₂ → O}
    (h₁ : ∀ i, π ^ k ∣ (b₁' i - b₁ i)) (h₂ : ∀ i, π ^ k ∣ (b₂' i - b₂ i))
    (h : ¬ π ^ k ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂) :
    ¬ π ^ k ∣ Polynomial.resultant (monicPoly b₁') (monicPoly b₂') n₁ n₂ := by
  intro hdvd
  have hspan : (maximalIdeal O) ^ k = Ideal.span {π ^ k} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hp₁ : proj O n₁ k b₁' = proj O n₁ k b₁ := by
    funext i
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (by rw [hspan]; exact Ideal.mem_span_singleton.mpr (h₁ i))
  have hp₂ : proj O n₂ k b₂' = proj O n₂ k b₂ := by
    funext i
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (by rw [hspan]; exact Ideal.mem_span_singleton.mpr (h₂ i))
  have hcr : Ideal.Quotient.mk ((maximalIdeal O) ^ k)
        (Polynomial.resultant (monicPoly b₁') (monicPoly b₂') n₁ n₂)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ k)
        (Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂) := by
    rw [← classRes_proj b₁' b₂', ← classRes_proj b₁ b₂, hp₁, hp₂]
  have h1 : (Ideal.Quotient.mk ((maximalIdeal O) ^ k) (π ^ k))
      ∣ Ideal.Quotient.mk ((maximalIdeal O) ^ k)
          (Polynomial.resultant (monicPoly b₁') (monicPoly b₂') n₁ n₂) :=
    (mk_pow_dvd_mk_iff hπ le_rfl _).mpr hdvd
  rw [hcr] at h1
  exact h ((mk_pow_dvd_mk_iff hπ le_rfl _).mp h1)

/-- The bad-pair reservoir: level-`N` class pairs one of whose shifted (level `N − v`)
components is undecided. -/
def badPairs (n₁ n₂ N v : ℕ) : Set (Coeff O n₁ N × Coeff O n₂ N) :=
  {p | UndecidedAt O n₁ (N - v) (coeffFactor n₁ (Nat.sub_le N v) p.1) ∨
       UndecidedAt O n₂ (N - v) (coeffFactor n₂ (Nat.sub_le N v) p.2)}

/-- **The packing step**: every pair in the depth-`v` neighborhood of a bucket witness is
bad — its product is the (undecided) bucket class, so by the decidedness transfer one of
its shifted components must be undecided. -/
theorem pairNbhd_subset_badPairs {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {b₁ : Fin n₁ → O} {b₂ : Fin n₂ → O}
    (hres : ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂)
    (hund : UndecidedAt O (n₁ + n₂) N (mulClass (proj O n₁ N b₁) (proj O n₂ N b₂))) :
    pairNbhd π N v b₁ b₂ ⊆ badPairs (O := O) n₁ n₂ N v := by
  rintro ⟨c₁, c₂⟩ ⟨hmul, ⟨b₁', hb₁', hcong₁⟩, ⟨b₂', hb₂', hcong₂⟩⟩
  by_contra hbad
  obtain ⟨hnb₁, hnb₂⟩ := not_or.mp hbad
  obtain ⟨σ₁, hσ₁⟩ := not_forall_not.mp hnb₁
  obtain ⟨σ₂, hσ₂⟩ := not_forall_not.mp hnb₂
  have hres' : ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly b₁') (monicPoly b₂') n₁ n₂ :=
    resultant_not_dvd_congr hπ (v + 1) hcong₁ hcong₂ hres
  have hd₁ : DecidedAt O n₁ σ₁ (N - v) (proj O n₁ (N - v) b₁') := by
    rw [← coeffFactor_proj n₁ (Nat.sub_le N v) b₁', hb₁']
    exact hσ₁
  have hd₂ : DecidedAt O n₂ σ₂ (N - v) (proj O n₂ (N - v) b₂') := by
    rw [← coeffFactor_proj n₂ (Nat.sub_le N v) b₂', hb₂']
    exact hσ₂
  have hdec := decidedAt_mulClass_of_not_dvd_resultant hπ hN hpos hres' hd₁ hd₂
  rw [hb₁', hb₂', hmul] at hdec
  exact hund _ hdec

/-- Bad pairs are few: at most `u_{n₁}(N−v)·q^{n₁v}·q^{n₂N} + q^{n₁N}·u_{n₂}(N−v)·q^{n₂v}`. -/
theorem card_badPairs_le (n₁ n₂ N v : ℕ) (hvN : v ≤ N) :
    Nat.card (badPairs (O := O) n₁ n₂ N v)
      ≤ undecidedCount O n₁ (N - v) * residueCard O ^ (n₁ * v + n₂ * N)
        + undecidedCount O n₂ (N - v) * residueCard O ^ (n₁ * N + n₂ * v) := by
  classical
  set h := Nat.sub_le N v
  -- the two one-sided reservoirs, as product sets
  have hsub : badPairs (O := O) n₁ n₂ N v
      ⊆ (((coeffFactor (O := O) n₁ h) ⁻¹' (undecidedSet O n₁ (N - v))) ×ˢ
          (Set.univ : Set (Coeff O n₂ N)))
        ∪ ((Set.univ : Set (Coeff O n₁ N)) ×ˢ
          ((coeffFactor (O := O) n₂ h) ⁻¹' (undecidedSet O n₂ (N - v)))) := by
    rintro ⟨c₁, c₂⟩ (hc | hc)
    · exact Or.inl ⟨hc, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, hc⟩
  have hcard : Nat.card (badPairs (O := O) n₁ n₂ N v)
      ≤ Nat.card (((coeffFactor (O := O) n₁ h) ⁻¹' (undecidedSet O n₁ (N - v))) ×ˢ
          (Set.univ : Set (Coeff O n₂ N)))
        + Nat.card ((Set.univ : Set (Coeff O n₁ N)) ×ˢ
          ((coeffFactor (O := O) n₂ h) ⁻¹' (undecidedSet O n₂ (N - v)))) := by
    refine le_trans (Nat.card_le_card_of_injective (Set.inclusion hsub)
      (Set.inclusion_injective _)) ?_
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_union_le _ _
  have hNv : N - (N - v) = v := by omega
  have huniv₁ : Nat.card ((Set.univ : Set (Coeff O n₁ N))) = residueCard O ^ (n₁ * N) := by
    rw [Nat.card_coe_set_eq, Set.ncard_univ, card_coeff]
  have huniv₂ : Nat.card ((Set.univ : Set (Coeff O n₂ N))) = residueCard O ^ (n₂ * N) := by
    rw [Nat.card_coe_set_eq, Set.ncard_univ, card_coeff]
  have hprod₁ : Nat.card (((coeffFactor (O := O) n₁ h) ⁻¹' (undecidedSet O n₁ (N - v))) ×ˢ
        (Set.univ : Set (Coeff O n₂ N)))
      = undecidedCount O n₁ (N - v) * residueCard O ^ (n₁ * v + n₂ * N) := by
    rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod,
      card_preimage_coeffFactor_eq n₁ h, hNv, huniv₂, undecidedCount,
      mul_assoc, ← pow_add]
  have hprod₂ : Nat.card ((Set.univ : Set (Coeff O n₁ N)) ×ˢ
        ((coeffFactor (O := O) n₂ h) ⁻¹' (undecidedSet O n₂ (N - v))))
      = undecidedCount O n₂ (N - v) * residueCard O ^ (n₁ * N + n₂ * v) := by
    rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod,
      card_preimage_coeffFactor_eq n₂ h, hNv, huniv₁, undecidedCount, pow_add]
    ring
  rw [hprod₁, hprod₂] at hcard
  exact hcard

/-- ★ **THE BUCKET BOUND** — the `q^v`-to-one packing: `q^v · #bucket ≤ #badPairs ≤ …`. -/
theorem card_bucketSet_mul_le {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hn₁ : n₁ ≠ 0) :
    Nat.card (bucketSet π n₁ n₂ N v) * residueCard O ^ v
      ≤ undecidedCount O n₁ (N - v) * residueCard O ^ (n₁ * v + n₂ * N)
        + undecidedCount O n₂ (N - v) * residueCard O ^ (n₁ * N + n₂ * v) := by
  classical
  -- choose a depth-`v` witness pair for every bucket class
  have hwit : ∀ c : bucketSet π n₁ n₂ N v, ∃ (b₁ : Fin n₁ → O) (b₂ : Fin n₂ → O),
      mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) = (c : Coeff O (n₁ + n₂) N) ∧
      (π ^ v ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂ ∧
       ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂) := by
    rintro ⟨c, -, b₁, b₂, hmul, hv, hv1⟩
    exact ⟨b₁, b₂, hmul, hv, hv1⟩
  choose w₁ w₂ hwmul hwres using hwit
  -- every neighborhood pair is bad
  have hmem : ∀ (c : bucketSet π n₁ n₂ N v) (p : pairNbhd π N v (w₁ c) (w₂ c)),
      (p : Coeff O n₁ N × Coeff O n₂ N) ∈ badPairs (O := O) n₁ n₂ N v := by
    intro c p
    refine pairNbhd_subset_badPairs hπ hN (Or.inl hn₁) (hwres c).2 ?_ p.2
    rw [hwmul c]
    exact c.2.1
  -- the sigma injection into the bad pairs
  have hinj : Function.Injective
      (fun x : (Σ c : bucketSet π n₁ n₂ N v, pairNbhd π N v (w₁ c) (w₂ c)) =>
        (⟨(x.2 : Coeff O n₁ N × Coeff O n₂ N), hmem x.1 x.2⟩ :
          badPairs (O := O) n₁ n₂ N v)) := by
    rintro ⟨c, p⟩ ⟨c', p'⟩ hpp
    have hpp' : (p : Coeff O n₁ N × Coeff O n₂ N) = (p' : Coeff O n₁ N × Coeff O n₂ N) :=
      congrArg Subtype.val hpp
    have hcc : (c : Coeff O (n₁ + n₂) N) = (c' : Coeff O (n₁ + n₂) N) := by
      have e1 : mulClass (p : Coeff O n₁ N × Coeff O n₂ N).1
          (p : Coeff O n₁ N × Coeff O n₂ N).2
          = mulClass (proj O n₁ N (w₁ c)) (proj O n₂ N (w₂ c)) := p.2.1
      have e2 : mulClass (p' : Coeff O n₁ N × Coeff O n₂ N).1
          (p' : Coeff O n₁ N × Coeff O n₂ N).2
          = mulClass (proj O n₁ N (w₁ c')) (proj O n₂ N (w₂ c')) := p'.2.1
      rw [← hwmul c, ← hwmul c', ← e1, ← e2, hpp']
    have hc : c = c' := Subtype.ext hcc
    subst hc
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hpp'))
  have hle := Nat.card_le_card_of_injective _ hinj
  -- resolve the sigma count: `#bucket · q^v`
  letI : Fintype (bucketSet π n₁ n₂ N v) := Fintype.ofFinite _
  rw [Nat.card_sigma] at hle
  have hfib : ∀ c : bucketSet π n₁ n₂ N v,
      Nat.card (pairNbhd π N v (w₁ c) (w₂ c)) = residueCard O ^ v := fun c =>
    natCard_pairNbhd hπ hN (Or.inl hn₁) (hwres c).1 (hwres c).2
  rw [Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const, smul_eq_mul,
    Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  exact hle.trans (card_badPairs_le n₁ n₂ N v (by omega))

end Buckets

/-! ## §3 The deep tail, the master decomposition, and the master inequality -/

section Master

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- `c` admits a **shallow split**: a monic factorization of (a lift of) `c` into positive
degrees whose resultant depth `v` satisfies `2v + 1 ≤ N`. -/
def HasShallowSplit (π : O) (n N : ℕ) (c : Coeff O n N) : Prop :=
  ∃ (n₁ n₂ : ℕ) (hn : n₁ + n₂ = n) (v : ℕ) (b₁ : Fin n₁ → O) (b₂ : Fin n₂ → O),
    n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ 2 * v + 1 ≤ N ∧
    mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) = castClass hn c ∧
    ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ n₂

/-- **The deep collision tail**: undecided AND no shallow split. -/
def deepTailSet (π : O) (n N : ℕ) : Set (Coeff O n N) :=
  {c | UndecidedAt O n N c ∧ ¬ HasShallowSplit π n N c}

/-- The tail proportion at level `N`. -/
noncomputable def deepTailSeq (π : O) (n N : ℕ) : ℝ :=
  (Nat.card (deepTailSet π n N) : ℝ) / (residueCard O : ℝ) ^ (n * N)

/-- The degree-`n` reading of the bucket (the split-degree cast folded in). -/
def bucketAt (π : O) (n₁ n N v : ℕ) : Set (Coeff O n N) :=
  {c | ∃ hn : n₁ + (n - n₁) = n, castClass hn c ∈ bucketSet π n₁ (n - n₁) N v}

/-- The admissible depth window at level `N`. -/
def depthWindow (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun v => 2 * v + 1 ≤ N)

/-- **The master decomposition**: every undecided class is in the tail or in a bucket. -/
theorem undecidedSet_subset_master (π : O) (n N : ℕ) :
    undecidedSet O n N
      ⊆ deepTailSet π n N ∪
        ⋃ p ∈ Finset.Ico 1 n ×ˢ depthWindow N, bucketAt π p.1 n N p.2 := by
  classical
  intro c hc
  by_cases hsplit : HasShallowSplit π n N c
  · right
    obtain ⟨n₁, n₂, hn, v, b₁, b₂, hn₁, hn₂, hvN, hmul, hres⟩ := hsplit
    have hn₂' : n₂ = n - n₁ := by omega
    subst hn₂'
    -- extract the exact depth `v₀ ≤ v`
    have hex : ∃ k, ¬ π ^ (k + 1) ∣
        Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ (n - n₁) := ⟨v, hres⟩
    set v₀ := Nat.find hex with hv₀def
    have hspec : ¬ π ^ (v₀ + 1) ∣
        Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ (n - n₁) := Nat.find_spec hex
    have hv₀le : v₀ ≤ v := Nat.find_min' hex hres
    have hdvd : π ^ v₀ ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂) n₁ (n - n₁) := by
      rcases Nat.eq_zero_or_pos v₀ with h0 | hpos
      · rw [h0, pow_zero]
        exact one_dvd _
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hpos
        have hmin := Nat.find_min hex (m := k) (by omega)
        rw [not_not] at hmin
        have hkv : k + 1 = v₀ := by omega
        rwa [hkv] at hmin
    have hmemI : ((n₁, v₀) : ℕ × ℕ) ∈ Finset.Ico 1 n ×ˢ depthWindow N := by
      refine Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
    exact Set.mem_biUnion hmemI
      ⟨hn, (undecidedAt_castClass_iff hn c).mpr hc, b₁, b₂, hmul, hdvd, hspec⟩
  · exact Or.inl ⟨hc, hsplit⟩

/-- Counting helper: a Finset-indexed union is beaten by the sum of the parts. -/
private theorem ncard_biUnion_le {α : Type*} [Finite α] {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (B : ι → Set α) :
    Nat.card (⋃ i ∈ I, B i : Set α) ≤ ∑ i ∈ I, Nat.card (B i) := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert j J hj ih =>
      rw [Finset.sum_insert hj, Finset.set_biUnion_insert]
      refine le_trans ?_ (Nat.add_le_add_left ih _)
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_union_le _ _

/-- Counting helper: a set inside a union is beaten by the sum of the parts. -/
theorem ncard_le_of_subset_union {α : Type*} [Finite α] {ι : Type*} (s t : Set α)
    (I : Finset ι) (B : ι → Set α) (h : s ⊆ t ∪ ⋃ i ∈ I, B i) :
    Nat.card s ≤ Nat.card t + ∑ i ∈ I, Nat.card (B i) := by
  classical
  have h1 : Nat.card s ≤ Nat.card ((t ∪ ⋃ i ∈ I, B i : Set α)) :=
    Nat.card_le_card_of_injective (Set.inclusion h) (Set.inclusion_injective _)
  have h2 : Nat.card ((t ∪ ⋃ i ∈ I, B i : Set α))
      ≤ Nat.card t + Nat.card ((⋃ i ∈ I, B i : Set α)) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_union_le _ _
  exact h1.trans (h2.trans (Nat.add_le_add_left (ncard_biUnion_le I B) _))

/-- **The master count**. -/
theorem undecidedCount_le_master (π : O) (n N : ℕ) :
    undecidedCount O n N
      ≤ Nat.card (deepTailSet π n N)
        + ∑ p ∈ Finset.Ico 1 n ×ˢ depthWindow N, Nat.card (bucketAt π p.1 n N p.2) :=
  ncard_le_of_subset_union _ _ _ _ (undecidedSet_subset_master π n N)

/-- The degree-`n` bucket count equals the split-degree bucket count (`castClass` is a
bijection). -/
theorem card_bucketAt_eq {π : O} {n₁ n N v : ℕ} (hn : n₁ + (n - n₁) = n) :
    Nat.card (bucketAt π n₁ n N v) = Nat.card (bucketSet π n₁ (n - n₁) N v) := by
  have hset : bucketAt π n₁ n N v
      = {c : Coeff O n N | castClass hn c ∈ bucketSet π n₁ (n - n₁) N v} := by
    ext c
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hn, h⟩⟩
  rw [hset, card_castClass_preimage hn]

/-- The count-to-proportion identity: `u_m(M) = undecidedSeq · q^{mM}`. -/
theorem undecidedCount_cast_eq (m M : ℕ) :
    (undecidedCount O m M : ℝ) = undecidedSeq O m M * (residueCard O : ℝ) ^ (m * M) := by
  rw [undecidedSeq, div_mul_cancel₀ _ (qpow_ne _)]

/-- Per-bucket, normalized: the bucket proportion is at most
`q^{-v} (undecidedSeq n₁ (N−v) + undecidedSeq n₂ (N−v))`. -/
theorem bucketAt_seq_le {π : O} (hπ : Irreducible π) {n₁ n N v : ℕ}
    (hn₁ : n₁ ≠ 0) (hlt : n₁ < n) (hN : 2 * v + 1 ≤ N) :
    (Nat.card (bucketAt π n₁ n N v) : ℝ) / (residueCard O : ℝ) ^ (n * N)
      ≤ ((residueCard O : ℝ)⁻¹) ^ v
          * (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v)) := by
  have hn : n₁ + (n - n₁) = n := by omega
  have hvN : v ≤ N := by omega
  -- the ℕ bound, cast to ℝ, with the count-to-proportion identities folded in
  have hexp₁ : n₁ * (N - v) + (n₁ * v + (n - n₁) * N) = n * N := by
    rw [← add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hvN, ← Nat.add_mul, hn]
  have hexp₂ : (n - n₁) * (N - v) + (n₁ * N + (n - n₁) * v) = n * N := by
    have h1 : (n - n₁) * (N - v) + (n - n₁) * v = (n - n₁) * N := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hvN]
    calc (n - n₁) * (N - v) + (n₁ * N + (n - n₁) * v)
        = ((n - n₁) * (N - v) + (n - n₁) * v) + n₁ * N := by ring
      _ = (n - n₁) * N + n₁ * N := by rw [h1]
      _ = n * N := by rw [← Nat.add_mul, Nat.add_comm (n - n₁) n₁, hn]
  have hℕ := card_bucketSet_mul_le hπ hN hn₁ (n₂ := n - n₁) (N := N) (v := v)
  rw [← card_bucketAt_eq (π := π) hn] at hℕ
  have hcast : (Nat.card (bucketAt π n₁ n N v) : ℝ) * (residueCard O : ℝ) ^ v
      ≤ (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v))
          * (residueCard O : ℝ) ^ (n * N) := by
    have h1 : ((Nat.card (bucketAt π n₁ n N v) * residueCard O ^ v : ℕ) : ℝ)
        ≤ ((undecidedCount O n₁ (N - v) * residueCard O ^ (n₁ * v + (n - n₁) * N)
            + undecidedCount O (n - n₁) (N - v) * residueCard O ^ (n₁ * N + (n - n₁) * v) : ℕ) : ℝ) := by
      exact_mod_cast hℕ
    push_cast at h1
    rw [undecidedCount_cast_eq, undecidedCount_cast_eq] at h1
    calc (Nat.card (bucketAt π n₁ n N v) : ℝ) * (residueCard O : ℝ) ^ v ≤ _ := h1
      _ = (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v))
            * (residueCard O : ℝ) ^ (n * N) := by
          rw [mul_assoc, ← pow_add, hexp₁, mul_assoc, ← pow_add, hexp₂]
          ring
  -- resolve the division against the multiplied form
  rw [div_le_iff₀ (qpow_pos _)]
  have hcancel : ((residueCard O : ℝ)⁻¹) ^ v * (residueCard O : ℝ) ^ v = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (qR_pos (O := O)).ne', one_pow]
  have h2 := mul_le_mul_of_nonneg_left hcast
    (pow_nonneg (inv_nonneg.2 (qR_pos (O := O)).le) v)
  calc (Nat.card (bucketAt π n₁ n N v) : ℝ)
      = ((residueCard O : ℝ)⁻¹) ^ v * (residueCard O : ℝ) ^ v
          * (Nat.card (bucketAt π n₁ n N v) : ℝ) := by rw [hcancel, one_mul]
    _ = ((residueCard O : ℝ)⁻¹) ^ v
          * ((Nat.card (bucketAt π n₁ n N v) : ℝ) * (residueCard O : ℝ) ^ v) := by ring
    _ ≤ ((residueCard O : ℝ)⁻¹) ^ v
          * ((undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v))
              * (residueCard O : ℝ) ^ (n * N)) := h2
    _ = ((residueCard O : ℝ)⁻¹) ^ v
          * (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v))
          * (residueCard O : ℝ) ^ (n * N) := by ring

/-- ★★ **THE MASTER INEQUALITY** — the σ-free drain against smaller degrees plus the tail. -/
theorem undecidedSeq_le_master {π : O} (hπ : Irreducible π) (n N : ℕ) :
    undecidedSeq O n N
      ≤ deepTailSeq π n N
        + ∑ n₁ ∈ Finset.Ico 1 n, ∑ v ∈ depthWindow N,
            ((residueCard O : ℝ)⁻¹) ^ v
              * (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v)) := by
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos _
  have hdiv : undecidedSeq O n N
      ≤ deepTailSeq π n N
        + ∑ p ∈ Finset.Ico 1 n ×ˢ depthWindow N,
            (Nat.card (bucketAt π p.1 n N p.2) : ℝ) / (residueCard O : ℝ) ^ (n * N) := by
    have hcast : (undecidedCount O n N : ℝ)
        ≤ (Nat.card (deepTailSet π n N) : ℝ)
          + ∑ p ∈ Finset.Ico 1 n ×ˢ depthWindow N,
              (Nat.card (bucketAt π p.1 n N p.2) : ℝ) := by
      exact_mod_cast undecidedCount_le_master π n N
    rw [undecidedSeq, deepTailSeq, ← Finset.sum_div, ← add_div]
    exact div_le_div_of_nonneg_right hcast hq.le
  refine hdiv.trans ?_
  rw [Finset.sum_product]
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum fun n₁ hn₁ => Finset.sum_le_sum fun v hv => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn₁
  obtain ⟨-, h3⟩ := Finset.mem_filter.mp hv
  exact bucketAt_seq_le hπ (by omega) h2 h3

end Master

/-! ## §4 The geometric-convolution drain (pure real analysis) -/

/-- A geometric convolution against a bounded null sequence drains: if `0 ≤ g ≤ C` and
`g → 0`, then `Σ_{2v+1 ≤ N} r^v g(N−v) → 0` for `0 ≤ r ≤ 1/2`. -/
theorem tendsto_geomConv_zero {r C : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) {g : ℕ → ℝ}
    (h0 : ∀ M, 0 ≤ g M) (hC : ∀ M, g M ≤ C) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun N => ∑ v ∈ depthWindow N, r ^ v * g (N - v)) atTop (𝓝 0) := by
  have hr1 : r ≤ 1 := hr.trans (by norm_num)
  have hCpos : (0 : ℝ) < C + 1 := lt_of_le_of_lt ((h0 0).trans (hC 0)) (lt_add_one C)
  have hterm : ∀ N v, 0 ≤ r ^ v * g (N - v) := fun N v =>
    mul_nonneg (pow_nonneg hr0 v) (h0 _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the geometric cutoff `V`
  obtain ⟨V, hV⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (by positivity : (0 : ℝ) < 4 * (C + 1))) (by norm_num : (1 / 2 : ℝ) < 1)
  -- choose the head threshold `N₁`
  have hδ : (0 : ℝ) < ε / (2 * (V + 1)) := by positivity
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hg) _ hδ
  refine ⟨N₁ + V + 1, fun N hN => ?_⟩
  have hS0 : 0 ≤ ∑ v ∈ depthWindow N, r ^ v * g (N - v) :=
    Finset.sum_nonneg fun v _ => hterm N v
  rw [Real.dist_0_eq_abs, abs_of_nonneg hS0]
  -- split the window at `V`
  rw [← Finset.sum_filter_add_sum_filter_not (depthWindow N) (fun v => v < V)]
  have hhead : ∑ v ∈ (depthWindow N).filter (fun v => v < V), r ^ v * g (N - v)
      ≤ (V : ℝ) * (ε / (2 * (V + 1))) := by
    have hcard : ((depthWindow N).filter (fun v => v < V)).card ≤ V := by
      have hsub : (depthWindow N).filter (fun v => v < V) ⊆ Finset.range V :=
        fun v hv => Finset.mem_range.mpr (Finset.mem_filter.mp hv).2
      calc ((depthWindow N).filter (fun v => v < V)).card
          ≤ (Finset.range V).card := Finset.card_le_card hsub
        _ = V := Finset.card_range V
    have hbound : ∀ v ∈ (depthWindow N).filter (fun v => v < V),
        r ^ v * g (N - v) ≤ ε / (2 * (V + 1)) := by
      intro v hv
      have hvV : v < V := (Finset.mem_filter.mp hv).2
      have hgN : dist (g (N - v)) 0 < ε / (2 * (V + 1)) := hN₁ (N - v) (by omega)
      rw [Real.dist_0_eq_abs, abs_of_nonneg (h0 _)] at hgN
      calc r ^ v * g (N - v) ≤ 1 * g (N - v) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1) (h0 _)
        _ = g (N - v) := one_mul _
        _ ≤ ε / (2 * (V + 1)) := hgN.le
    calc ∑ v ∈ (depthWindow N).filter (fun v => v < V), r ^ v * g (N - v)
        ≤ ((depthWindow N).filter (fun v => v < V)).card • (ε / (2 * (V + 1))) :=
          Finset.sum_le_card_nsmul _ _ _ hbound
      _ = (((depthWindow N).filter (fun v => v < V)).card : ℝ) * (ε / (2 * (V + 1))) := by
          rw [nsmul_eq_mul]
      _ ≤ (V : ℝ) * (ε / (2 * (V + 1))) := by
          have : (((depthWindow N).filter (fun v => v < V)).card : ℝ) ≤ (V : ℝ) := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this hδ.le
  have htail : ∑ v ∈ (depthWindow N).filter (fun v => ¬ v < V), r ^ v * g (N - v)
      ≤ (C + 1) * (2 * (1 / 2 : ℝ) ^ V) := by
    have hsub : (depthWindow N).filter (fun v => ¬ v < V) ⊆ Finset.Ico V N := by
      intro v hv
      obtain ⟨hw, hnv⟩ := Finset.mem_filter.mp hv
      obtain ⟨hr', -⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_Ico.mpr ⟨by omega, Finset.mem_range.mp hr'⟩
    calc ∑ v ∈ (depthWindow N).filter (fun v => ¬ v < V), r ^ v * g (N - v)
        ≤ ∑ v ∈ Finset.Ico V N, r ^ v * g (N - v) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hterm N v)
      _ ≤ ∑ v ∈ Finset.Ico V N, (C + 1) * (1 / 2 : ℝ) ^ v := by
          refine Finset.sum_le_sum fun v _ => ?_
          calc r ^ v * g (N - v) ≤ (1 / 2 : ℝ) ^ v * (C + 1) := by
                refine mul_le_mul (pow_le_pow_left₀ hr0 hr v)
                  ((hC _).trans (le_add_of_nonneg_right zero_le_one)) (h0 _)
                  (by positivity)
            _ = (C + 1) * (1 / 2 : ℝ) ^ v := mul_comm _ _
      _ = (C + 1) * ∑ v ∈ Finset.Ico V N, (1 / 2 : ℝ) ^ v := by
          rw [Finset.mul_sum]
      _ ≤ (C + 1) * (2 * (1 / 2 : ℝ) ^ V) := by
          refine mul_le_mul_of_nonneg_left ?_ hCpos.le
          rw [Finset.sum_Ico_eq_sum_range]
          calc ∑ j ∈ Finset.range (N - V), (1 / 2 : ℝ) ^ (V + j)
              = (1 / 2 : ℝ) ^ V * ∑ j ∈ Finset.range (N - V), (1 / 2 : ℝ) ^ j := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => pow_add _ _ _
            _ ≤ (1 / 2 : ℝ) ^ V * 2 := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                have hgeo := geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) (N - V)
                rw [hgeo]
                have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (N - V) := by positivity
                have : ((1 / 2 : ℝ) ^ (N - V) - 1) / (1 / 2 - 1)
                    = 2 * (1 - (1 / 2 : ℝ) ^ (N - V)) := by ring
                rw [this]
                nlinarith
            _ = 2 * (1 / 2 : ℝ) ^ V := mul_comm _ _
  -- combine
  have hVstep : (V : ℝ) * (ε / (2 * ((V : ℝ) + 1))) < ε / 2 := by
    have hV1 : (0 : ℝ) < (V : ℝ) + 1 := by positivity
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε, hV1]
  have hTstep : (C + 1) * (2 * (1 / 2 : ℝ) ^ V) < ε / 2 := by
    have h1 : (1 / 2 : ℝ) ^ V < ε / (4 * (C + 1)) := hV
    calc (C + 1) * (2 * (1 / 2 : ℝ) ^ V) < (C + 1) * (2 * (ε / (4 * (C + 1)))) := by
          refine mul_lt_mul_of_pos_left ?_ hCpos
          linarith
      _ = ε / 2 := by field_simp; ring
  linarith

/-! ## §5 The reduction and the capstone wiring -/

section Reduction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

theorem undecidedSeq_nonneg (n N : ℕ) : 0 ≤ undecidedSeq O n N :=
  div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le

theorem undecidedSeq_le_one (n N : ℕ) : undecidedSeq O n N ≤ 1 := by
  rw [undecidedSeq, div_le_one (qpow_pos _)]
  have h1 : undecidedCount O n N ≤ residueCard O ^ (n * N) := by
    rw [undecidedCount, ← card_coeff (O := O) n N]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  exact_mod_cast h1

/-- **The per-`O` reduction**: smaller-degree drains + the tail drain ⟹ the degree-`n`
drain. -/
theorem tendsto_undecidedSeq_of_tail {n : ℕ} {π : O} (hπ : Irreducible π)
    (hprev : ∀ m, m ≠ 0 → m < n → Tendsto (undecidedSeq O m) atTop (𝓝 0))
    (htail : Tendsto (fun N => deepTailSeq π n N) atTop (𝓝 0)) :
    Tendsto (undecidedSeq O n) atTop (𝓝 0) := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hhalf : ((residueCard O : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hq2
  -- each degree slice of the double sum drains by the geometric convolution
  have hslice : ∀ n₁ ∈ Finset.Ico 1 n,
      Tendsto (fun N => ∑ v ∈ depthWindow N,
        ((residueCard O : ℝ)⁻¹) ^ v
          * (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v))) atTop (𝓝 0) := by
    intro n₁ hn₁
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn₁
    have hg : Tendsto (fun M => undecidedSeq O n₁ M + undecidedSeq O (n - n₁) M)
        atTop (𝓝 0) := by
      have := (hprev n₁ (by omega) h2).add (hprev (n - n₁) (by omega) (by omega))
      simpa using this
    exact tendsto_geomConv_zero (r := (residueCard O : ℝ)⁻¹) (C := 2)
      (g := fun M => undecidedSeq O n₁ M + undecidedSeq O (n - n₁) M)
      (inv_nonneg.2 (qR_pos (O := O)).le) hhalf
      (fun M => add_nonneg (undecidedSeq_nonneg _ _) (undecidedSeq_nonneg _ _))
      (fun M => by
        have h1 := undecidedSeq_le_one (O := O) n₁ M
        have h2 := undecidedSeq_le_one (O := O) (n - n₁) M
        linarith) hg
  have hsum : Tendsto (fun N => ∑ n₁ ∈ Finset.Ico 1 n, ∑ v ∈ depthWindow N,
      ((residueCard O : ℝ)⁻¹) ^ v
        * (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.Ico 1 n) hslice
    simpa using h
  have hRHS : Tendsto (fun N => deepTailSeq π n N
      + ∑ n₁ ∈ Finset.Ico 1 n, ∑ v ∈ depthWindow N,
          ((residueCard O : ℝ)⁻¹) ^ v
            * (undecidedSeq O n₁ (N - v) + undecidedSeq O (n - n₁) (N - v)))
      atTop (𝓝 0) := by
    simpa using htail.add hsum
  exact squeeze_zero (fun N => undecidedSeq_nonneg n N)
    (fun N => undecidedSeq_le_master hπ n N) hRHS

end Reduction

/-- ★ **THE NAMED REMAINDER** — the deep-collision tail drains, at degree `n`: over every
complete DVR with finite residue field and every uniformizer, the proportion of level-`N`
classes that are undecided and admit NO shallow split tends to `0`.  σ-free and
factorization-free; this is the exact hard core left of the capstone's `a2` field. -/
def DeepTailDrainAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    ∀ π : O, Irreducible π → Tendsto (fun N => deepTailSeq π n N) atTop (𝓝 0)

/-- ★★ Strong induction on the degree: the tail drains at every degree ≥ 4 ⟹ the σ-free
drain at every positive degree (degrees 1–3 are landed unconditionally). -/
theorem undecidedDrainAt_all_pos_of_deepTail (h : ∀ m, 4 ≤ m → DeepTailDrainAt m) :
    ∀ n, n ≠ 0 → IFCG45.UndecidedDrainAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · -- the landed bases: degrees 1, 2, 3
      have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      interval_cases n
      · exact (IFCG45.drainageAt_iff_undecidedDrain 1).1 IFCG45.drainageAt_one
      · exact (IFCG45.drainageAt_iff_undecidedDrain 2).1 (fun _ _ _ _ _ _ σ => drainage_two σ)
      · exact (IFCG45.drainageAt_iff_undecidedDrain 3).1 drainageAt_three
    · -- `n ≥ 4`: the reduction against the strong-induction supply
      intro O _ _ _ _ _
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
      exact tendsto_undecidedSeq_of_tail hπ (fun m hm hmn => ih m hmn hm O)
        (h n h4 O π hπ)

/-- ★★★ **THE CAPSTONE FEED** — the entire `a2` field (`∀ n, DrainageAt n`, what
`drainage_of_capstoneHypotheses` consumes at every degree) from the deep-tail drain at
degrees ≥ 4 alone, through DRN's lossless dissection (IFCG45). -/
theorem drainageAt_all_of_deepTailDrain (h : ∀ m, 4 ≤ m → DeepTailDrainAt m) :
    ∀ n, DrainageAt n := by
  refine IFCG45.drainageAt_all_iff_undecidedDrain_from_four.2 (fun n hn => ?_)
  exact undecidedDrainAt_all_pos_of_deepTail h n (by omega)

/-! ## §6 BONUS — the tail structure: the deep collision tail is the CLUSTER locus

A deep-tail class's residue reduction cannot split into coprime monic factors (that
would be a depth-`0` shallow split by Hensel), and cannot be irreducible (that decides
the class inert, CN-21) — so by the landed primary classifier (IFCG35 §2c) it is
associated to `ψ^k` with `ψ` irreducible and `k ≥ 2`.  The named remainder
`DeepTailDrainAt` therefore concerns EXACTLY the primary (single-cluster) classes —
the locus where the H.124 cluster campaign and the census recentring machinery operate. -/

section TailStructure

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Lifts of the same level-`N ≥ 1` class share their residue reduction. -/
theorem map_residue_eq_of_proj_eq {n N : ℕ} (hN : N ≠ 0) {a b : Fin n → O}
    (hab : proj O n N a = proj O n N b) :
    (monicPoly a).map (residue O) = (monicPoly b).map (residue O) := by
  have hcoeff : ∀ i : Fin n, residue O (a i) = residue O (b i) := by
    intro i
    have hi := congrFun hab i
    have hmem : a i - b i ∈ (maximalIdeal O) ^ N :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hi
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.pow_le_self hN hmem)
  ext j
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  rcases lt_trichotomy j n with hj | hj | hj
  · rw [monicPoly_coeff_lt a hj, monicPoly_coeff_lt b hj]
    exact hcoeff ⟨j, hj⟩
  · have ha1 : (monicPoly a).coeff j = 1 := by
      subst hj
      have := (monicPoly_monic a).coeff_natDegree
      rwa [monicPoly_natDegree] at this
    have hb1 : (monicPoly b).coeff j = 1 := by
      subst hj
      have := (monicPoly_monic b).coeff_natDegree
      rwa [monicPoly_natDegree] at this
    rw [ha1, hb1]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; exact hj),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; exact hj)]

/-- **The `m = 1` leaf, class-level** (CN-21 packaged for the tail analysis): a class one
of whose lifts has IRREDUCIBLE residue reduction is decided inert-of-degree-`n` at every
level `N ≥ 1`. -/
theorem decidedAt_of_irreducible_residue {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0)
    {a : Fin n → O} (hirr : Irreducible ((monicPoly a).map (residue O))) :
    DecidedAt O n ⟨{(1, n)}⟩ N (proj O n N a) := by
  intro b hb
  have heq := map_residue_eq_of_proj_eq hN hb
  have hirrb : Irreducible ((monicPoly b).map (residue O)) := heq ▸ hirr
  have htype := typeOf_inert_of_irreducible_map (monicPoly_monic b)
    (by rw [monicPoly_natDegree]; omega) hirrb
  rwa [monicPoly_natDegree] at htype

/-- **Coprime residue splits are shallow** (the depth-`0` Hensel leg): if the residue
reduction of (a lift of) a class factors into two coprime monic nonconstant polynomials,
the class has a shallow split — at resultant depth `0`. -/
theorem hasShallowSplit_of_coprime_residue_split {π : O} (hπ : Irreducible π) {n N : ℕ}
    (hN : 1 ≤ N) {a : Fin n → O} {R₁ R₂ : Polynomial (ResidueField O)}
    (h₁ : R₁.Monic) (h₂ : R₂.Monic) (hd₁ : R₁.natDegree ≠ 0) (hd₂ : R₂.natDegree ≠ 0)
    (hcop : IsCoprime R₁ R₂) (hmul : (monicPoly a).map (residue O) = R₁ * R₂) :
    HasShallowSplit π n N (proj O n N a) := by
  -- the degree bookkeeping, then eliminate `n`
  have hdeg : n = R₁.natDegree + R₂.natDegree := by
    have h3 : ((monicPoly a).map (residue O)).natDegree = n := by
      rw [(monicPoly_monic a).natDegree_map, monicPoly_natDegree]
    rw [← h3, hmul, h₁.natDegree_mul h₂]
  subst hdeg
  -- coefficientwise monic lifts of the residue factors
  choose lift hlift using IsLocalRing.residue_surjective (R := O)
  have hmap : ∀ (m : ℕ) (R : Polynomial (ResidueField O)), R.Monic → m = R.natDegree →
      (monicPoly (fun i : Fin m => lift (R.coeff (i : ℕ)))).map (residue O) = R := by
    intro m R hR hm
    subst hm
    ext j
    rw [Polynomial.coeff_map]
    rcases lt_trichotomy j R.natDegree with hj | hj | hj
    · rw [monicPoly_coeff_lt _ hj]
      exact hlift _
    · subst hj
      have hb1 : (monicPoly (fun i : Fin R.natDegree => lift (R.coeff (i : ℕ)))).coeff
          R.natDegree = 1 := by
        have := (monicPoly_monic (fun i : Fin R.natDegree => lift (R.coeff (i : ℕ)))).coeff_natDegree
        rwa [monicPoly_natDegree] at this
      rw [hb1, map_one, hR.coeff_natDegree]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [monicPoly_natDegree]),
        map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hj]
  have hmap₁ := hmap R₁.natDegree R₁ h₁ rfl
  have hmap₂ := hmap R₂.natDegree R₂ h₂ rfl
  set b₁ : Fin R₁.natDegree → O := fun i => lift (R₁.coeff (i : ℕ)) with hb₁def
  set b₂ : Fin R₂.natDegree → O := fun i => lift (R₂.coeff (i : ℕ)) with hb₂def
  -- the base pair has UNIT resultant: reduce mod 𝔪 against the coprime residue resultant
  have hres : ¬ π ∣ Polynomial.resultant (monicPoly b₁) (monicPoly b₂)
      R₁.natDegree R₂.natDegree := by
    intro hdvd
    have h1 : Polynomial.resultant ((monicPoly b₁).map (residue O))
          ((monicPoly b₂).map (residue O)) R₁.natDegree R₂.natDegree
        = residue O (Polynomial.resultant (monicPoly b₁) (monicPoly b₂)
            R₁.natDegree R₂.natDegree) :=
      Polynomial.resultant_map_map (monicPoly b₁) (monicPoly b₂)
        R₁.natDegree R₂.natDegree (residue O)
    rw [hmap₁, hmap₂] at h1
    have h2 : residue O (Polynomial.resultant (monicPoly b₁) (monicPoly b₂)
        R₁.natDegree R₂.natDegree) = 0 := by
      have hmem : Polynomial.resultant (monicPoly b₁) (monicPoly b₂)
          R₁.natDegree R₂.natDegree ∈ maximalIdeal O := by
        rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
        exact hdvd
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact Polynomial.resultant_ne_zero R₁ R₂ hcop (h1.trans h2)
  -- the level-1 product identity: `a`'s residue class is the pair's product class
  have hcoeffs : ∀ j : ℕ, residue O ((monicPoly b₁ * monicPoly b₂).coeff j)
      = ((monicPoly a).map (residue O)).coeff j := by
    intro j
    rw [← Polynomial.coeff_map, Polynomial.map_mul, hmap₁, hmap₂, ← hmul]
  have hclass1 : proj O (R₁.natDegree + R₂.natDegree) 1 a
      = mulClass (proj O R₁.natDegree 1 b₁) (proj O R₂.natDegree 1 b₂) := by
    rw [← mulClass_proj]
    funext i
    show Ideal.Quotient.mk ((maximalIdeal O) ^ 1) (a i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ 1) ((monicPoly b₁ * monicPoly b₂).coeff (i : ℕ))
    have hres_eq : residue O (a i)
        = residue O ((monicPoly b₁ * monicPoly b₂).coeff (i : ℕ)) := by
      rw [hcoeffs (i : ℕ), Polynomial.coeff_map, monicPoly_coeff_lt a i.isLt]
    have hmem : a i - (monicPoly b₁ * monicPoly b₂).coeff (i : ℕ) ∈ maximalIdeal O :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hres_eq
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    rwa [pow_one]
  -- fire the landed depth-0 Hensel leg at level 1, then read the split at level N
  have hLF := Uniformity.Density.IFCG42.liftsFactor_of_not_dvd_resultant hπ
    (v := 0) (N := 1) (by omega) (Or.inl hd₁) (by simpa using hres)
  obtain ⟨c₁, c₂, hfact, hcong₁, hcong₂⟩ := hLF a hclass1
  have hres_c : ¬ π ^ (0 + 1) ∣ Polynomial.resultant (monicPoly c₁) (monicPoly c₂)
      R₁.natDegree R₂.natDegree := by
    refine resultant_not_dvd_congr hπ (0 + 1) hcong₁ hcong₂ ?_
    simpa using hres
  have hmulN : mulClass (proj O R₁.natDegree N c₁) (proj O R₂.natDegree N c₂)
      = proj O (R₁.natDegree + R₂.natDegree) N a := by
    rw [← mulClass_proj]
    funext i
    show Ideal.Quotient.mk ((maximalIdeal O) ^ N) ((monicPoly c₁ * monicPoly c₂).coeff (i : ℕ))
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a i)
    have hco : (monicPoly c₁ * monicPoly c₂).coeff (i : ℕ) = a i := by
      rw [← hfact, monicPoly_coeff_lt a i.isLt]
    rw [hco]
  exact ⟨R₁.natDegree, R₂.natDegree, rfl, 0, c₁, c₂, hd₁, hd₂, by omega,
    by rw [castClass_rfl']; exact hmulN, hres_c⟩

/-- ★ **THE TAIL IS THE CLUSTER LOCUS**: a deep-tail class's residue reduction is
associated to `ψ^k` for a single irreducible `ψ` and `k ≥ 2`.  (Irreducible reduction
would decide the class — CN-21; a coprime split would be a shallow split — the depth-`0`
Hensel leg; the landed primary classifier IFCG35 §2c excludes everything else.)  So the
named remainder `DeepTailDrainAt` concerns exactly the single-cluster (primary) classes. -/
theorem deepTail_residue_primary {π : O} (hπ : Irreducible π) {n N : ℕ}
    (hn : n ≠ 0) (hN : 1 ≤ N) {c : Coeff O n N} (hc : c ∈ deepTailSet π n N)
    {a : Fin n → O} (ha : proj O n N a = c) :
    ∃ (ψ : Polynomial (ResidueField O)) (k : ℕ), Irreducible ψ ∧ 2 ≤ k ∧
      Associated ((monicPoly a).map (residue O)) (ψ ^ k) := by
  obtain ⟨hund, hnos⟩ := hc
  have hR0 : 0 < ((monicPoly a).map (residue O)).natDegree := by
    rw [(monicPoly_monic a).natDegree_map, monicPoly_natDegree]
    omega
  by_contra hnp
  have hni : ¬ Irreducible ((monicPoly a).map (residue O)) := by
    intro hirr
    have hdec := decidedAt_of_irreducible_residue (N := N) hn (by omega) hirr
    rw [ha] at hdec
    exact hund _ hdec
  obtain ⟨G, H, hG, hH, hG0, hH0, hcop, hassoc⟩ :=
    IFCG35.exists_coprime_split_of_not_primary hR0 hni hnp
  have hReq : (monicPoly a).map (residue O) = G * H :=
    Polynomial.eq_of_monic_of_associated ((monicPoly_monic a).map _) (hG.mul hH) hassoc
  have hss := hasShallowSplit_of_coprime_residue_split hπ hN hG hH
    (by omega) (by omega) hcop hReq
  rw [ha] at hss
  exact hnos hss

end TailStructure

end Uniformity.Density.IFCG46

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG46.card_preimage_coeffFactor_eq
#print axioms Uniformity.Density.IFCG46.card_bucketSet_mul_le
#print axioms Uniformity.Density.IFCG46.undecidedSeq_le_master
#print axioms Uniformity.Density.IFCG46.tendsto_geomConv_zero
#print axioms Uniformity.Density.IFCG46.tendsto_undecidedSeq_of_tail
#print axioms Uniformity.Density.IFCG46.undecidedDrainAt_all_pos_of_deepTail
#print axioms Uniformity.Density.IFCG46.drainageAt_all_of_deepTailDrain
#print axioms Uniformity.Density.IFCG46.decidedAt_of_irreducible_residue
#print axioms Uniformity.Density.IFCG46.hasShallowSplit_of_coprime_residue_split
#print axioms Uniformity.Density.IFCG46.deepTail_residue_primary
