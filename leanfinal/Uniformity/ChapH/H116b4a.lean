/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H116b1
import Uniformity.ChapH.H102
import Uniformity.ChapH.H114

/-!
# Uniformity.ChapH.H116b4a — ghost images and cofactor admissibility

**Chapter H, NODE H.116b4, preparatory rows GR-1/2 and GR-3/3b**
(`docs/in-progress/H116B4_MAP_2026-08-26.md`, 2026-08-26).

This file lands only the two supply/fireable rows preceding the open gauge-resultant count:
the raw-child-to-factor-image boundary and the mechanical cofactor/admissibility boundary.
It does not state the signed uniform presentation count and does not construct a map between
fibres (fence A-H.7/F1).
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

section Ghost

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The level-`N` coefficient class of the planted factor belonging to a raw child class. -/
noncomputable def plantedFactorClass (π : O) (μ N k : ℕ) (z : ResidueField O)
    (d : ClusterState O μ N) : Coeff O μ N :=
  proj O μ N (alphaParentCoeff π (classSect O μ N d.1) k (resSect O z))

/-- The image carrier of planted factor classes. -/
abbrev PlantedFactorImage (π : O) (μ N k : ℕ) (z : ResidueField O) :=
  Set.range (plantedFactorClass (O := O) π μ N k z)

/-- Equality of planted factor images is exactly equality at the graded child windows. -/
theorem plantedFactorClass_eq_iff {π : O} (hπ : Irreducible π) {μ N k : ℕ}
    (hμ : 1 ≤ μ) (hw : μ * k ≤ N) (z : ResidueField O)
    (d d' : ClusterState O μ N) :
    plantedFactorClass π μ N k z d = plantedFactorClass π μ N k z d' ↔
      ∀ j : Fin μ,
        Ideal.Quotient.mk ((maximalIdeal O) ^ (N - μ * k + k * (j : ℕ)))
            (classSect O μ N d.1 j) =
          Ideal.Quotient.mk ((maximalIdeal O) ^ (N - μ * k + k * (j : ℕ)))
            (classSect O μ N d'.1 j) := by
  rw [plantedFactorClass, plantedFactorClass, proj_alphaParentCoeff_eq_iff hπ hμ hw]
  constructor
  · intro h j
    exact Ideal.Quotient.eq.2
      ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ _ _).2 (h j))
  · intro h j
    exact (mem_maximalIdeal_pow_iff_dvd_of_irr hπ _ _).1 (Ideal.Quotient.eq.1 (h j))

variable [Finite (ResidueField O)]

/-- The dependent box of visible graded windows of one planted factor. -/
abbrev PlantedWindowBox (μ N k : ℕ) :=
  (j : Fin μ) → Res O (N - μ * k + k * (j : ℕ))

/-- Truncate every raw child coordinate to the window visible after planting. -/
noncomputable def plantedWindowMap {μ N k : ℕ} (hw : μ * k ≤ N) :
    Coeff O μ N →+ PlantedWindowBox (O := O) μ N k where
  toFun d j := resFactor (O := O) (by
      have hj : k * (j : ℕ) ≤ k * μ := Nat.mul_le_mul_left k (Nat.le_of_lt j.isLt)
      rw [Nat.mul_comm k μ] at hj
      omega) (d j)
  map_zero' := by ext j; rfl
  map_add' d d' := by ext j; exact map_add _ _ _

/-- Every compatible tuple of visible windows lifts to a raw child state. -/
theorem plantedWindowMap_surjective {μ N k : ℕ} (hw : μ * k ≤ N) :
    Function.Surjective (plantedWindowMap (O := O) hw) := by
  classical
  intro y
  have hlift : ∀ j : Fin μ, ∃ x : Res O N,
      resFactor (O := O) (by
        have hj : k * (j : ℕ) ≤ k * μ := Nat.mul_le_mul_left k (Nat.le_of_lt j.isLt)
        rw [Nat.mul_comm k μ] at hj
        omega) x = y j := by
    intro j
    exact resFactor_surjective (O := O) _ (y j)
  choose x hx using hlift
  refine ⟨x, ?_⟩
  funext j
  exact hx j

/-- The window map and the actual planted-factor class have exactly the same fibres. -/
theorem plantedFactorClass_eq_iff_windowMap {π : O} (hπ : Irreducible π) {μ N k : ℕ}
    (hμ : 1 ≤ μ) (hw : μ * k ≤ N) (z : ResidueField O)
    (d d' : ClusterState O μ N) :
    plantedFactorClass π μ N k z d = plantedFactorClass π μ N k z d' ↔
      plantedWindowMap (O := O) hw d.1 = plantedWindowMap (O := O) hw d'.1 := by
  rw [plantedFactorClass_eq_iff hπ hμ hw]
  have hwin : ∀ j : Fin μ, N - μ * k + k * (j : ℕ) ≤ N := by
    intro j
    have hjle : k * (j : ℕ) ≤ k * μ := Nat.mul_le_mul_left k (Nat.le_of_lt j.isLt)
    rw [Nat.mul_comm k μ] at hjle
    omega
  constructor
  · intro h
    funext j
    change resFactor (O := O) (hwin j) (d.1 j) = resFactor (O := O) (hwin j) (d'.1 j)
    calc
      _ = resFactor (O := O) (hwin j) (proj O μ N (classSect O μ N d.1) j) := by
        rw [proj_classSect O μ N d.1]
      _ = Ideal.Quotient.mk _ (classSect O μ N d.1 j) := by rw [proj, resFactor_mk]
      _ = Ideal.Quotient.mk _ (classSect O μ N d'.1 j) := h j
      _ = resFactor (O := O) (hwin j) (proj O μ N (classSect O μ N d'.1) j) := by
        rw [proj, resFactor_mk]
      _ = resFactor (O := O) (hwin j) (d'.1 j) := by rw [proj_classSect O μ N d'.1]
  · intro h j
    have hj := congrFun h j
    change resFactor (O := O) (hwin j) (d.1 j) = resFactor (O := O) (hwin j) (d'.1 j) at hj
    have hd : Ideal.Quotient.mk _ (classSect O μ N d.1 j) =
        resFactor (O := O) (hwin j) (d.1 j) := by
      simpa only [proj, resFactor_mk] using congrArg (resFactor (O := O) (hwin j))
        (congrFun (proj_classSect O μ N d.1) j)
    have hd' : Ideal.Quotient.mk _ (classSect O μ N d'.1 j) =
        resFactor (O := O) (hwin j) (d'.1 j) := by
      simpa only [proj, resFactor_mk] using congrArg (resFactor (O := O) (hwin j))
        (congrFun (proj_classSect O μ N d'.1) j)
    exact hd.trans (hj.trans hd'.symm)

set_option maxHeartbeats 4000000 in
/-- Over positive visible windows, passing from the coefficient box back to cluster states
does not remove any member of a planted-factor fibre. -/
noncomputable def plantedFactorFiberEquivWindowFiber {π : O} (hπ : Irreducible π)
    {μ N k : ℕ} (hμ : 1 ≤ μ) (hN : 1 ≤ N) (hw : μ * k ≤ N - 1)
    (hfull : μ * k ≤ N)
    (z : ResidueField O) (d₀ : ClusterState O μ N) :
    {d : ClusterState O μ N //
        plantedFactorClass π μ N k z d = plantedFactorClass π μ N k z d₀} ≃
      {x : Coeff O μ N //
        plantedWindowMap (O := O) hfull x = plantedWindowMap (O := O) hfull d₀.1} where
  toFun d := ⟨d.1.1, (plantedFactorClass_eq_iff_windowMap hπ hμ hfull z d d₀).1 d.2⟩
  invFun x := by
    have hmem : ∀ j, x.1 j ∈ (maximalIdeal O).map
        (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
      intro j
      have hW : 1 ≤ N - μ * k + k * (j : ℕ) := by omega
      have hj := congrFun x.2 j
      obtain ⟨ax, hax⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) (x.1 j)
      obtain ⟨b, hb, hbd⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (d₀.2 j)
      have hj' := hj
      have hWle : N - μ * k + k * (j : ℕ) ≤ N := by
        have hjle : k * (j : ℕ) ≤ k * μ := Nat.mul_le_mul_left k (Nat.le_of_lt j.isLt)
        rw [Nat.mul_comm k μ] at hjle
        omega
      change resFactor (O := O) hWle (x.1 j) = resFactor (O := O) hWle (d₀.1 j) at hj'
      rw [← hax, ← hbd, resFactor_mk, resFactor_mk] at hj'
      have hdiff : ax - b ∈ (maximalIdeal O) ^ (N - μ * k + k * (j : ℕ)) :=
        Ideal.Quotient.eq.1 hj'
      have hdiff' : ax - b ∈ maximalIdeal O := Ideal.pow_le_self (Nat.ne_of_gt hW) hdiff
      refine (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).2
        ⟨ax, ?_, hax⟩
      have hident : ax = (ax - b) + b := by ring
      rw [hident]
      exact Ideal.add_mem _ hdiff' hb
    let d : ClusterState O μ N := ⟨x.1, hmem⟩
    exact ⟨d, (plantedFactorClass_eq_iff_windowMap hπ hμ hfull z d d₀).2 x.2⟩
  left_inv d := by ext; rfl
  right_inv x := by ext; rfl

/-- **GR-1.** Every nonempty planted-factor image fibre has one positive cardinal, independent
of the image.  The kernel is the landed shear's dependent graded-window kernel. -/
theorem card_plantedFactor_fiber {π : O} (hπ : Irreducible π) {μ N k : ℕ}
    (hN : 1 ≤ N) (hμ : 1 ≤ μ) (hw : μ * k ≤ N - 1)
    (z : ResidueField O) :
    ∃ ghost : ℕ, 0 < ghost ∧
      ∀ y ∈ Set.range (plantedFactorClass (O := O) π μ N k z),
        Nat.card {d : ClusterState O μ N // plantedFactorClass π μ N k z d = y}
          = ghost := by
  classical
  let f := plantedWindowMap (O := O) (by omega : μ * k ≤ N)
  refine ⟨Nat.card f.ker, Nat.card_pos, ?_⟩
  intro y hy
  obtain ⟨d₀, rfl⟩ := hy
  rw [Nat.card_congr (plantedFactorFiberEquivWindowFiber hπ hμ hN hw (by omega) z d₀)]
  have hf := card_preimage_of_surjective f (plantedWindowMap_surjective (O := O) (by omega))
    ({f d₀.1} : Set (PlantedWindowBox (O := O) μ N k))
  change Nat.card {x : Coeff O μ N // f x = f d₀.1} = Nat.card f.ker
  have he : {x : Coeff O μ N // f x = f d₀.1} ≃ (f ⁻¹' {f d₀.1}) :=
    Equiv.subtypeEquivRight (fun x => by simp)
  rw [Nat.card_congr he]
  simpa only [Nat.card_unique, mul_one] using hf

/-- The elementary reverse-range sum used by the closed ghost exponent. -/
theorem sum_range_reverse (n : ℕ) :
    (∑ j ∈ Finset.range n, (n - j)) = n * (n + 1) / 2 := by
  have hc : (∑ j ∈ Finset.range n, (n - j)) = Nat.choose (n + 1) 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hshift : (∑ j ∈ Finset.range n, (n + 1 - j)) =
          (∑ j ∈ Finset.range n, (n - j)) + n := by
        calc
          _ = ∑ j ∈ Finset.range n, ((n - j) + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact Nat.succ_sub (Nat.le_of_lt (Finset.mem_range.1 hj))
          _ = (∑ j ∈ Finset.range n, (n - j)) +
              ∑ _j ∈ Finset.range n, 1 := Finset.sum_add_distrib
          _ = _ := by simp
      rw [hshift, ih]
      have hp : Nat.choose (n + 2) 2 = (n + 1) + Nat.choose (n + 1) 2 := by
        simpa only [Nat.succ_eq_add_one, Nat.choose_one_right] using
          Nat.choose_succ_succ (n + 1) 1
      rw [hp]
      omega
  rw [hc, Nat.choose_two_right, Nat.add_sub_cancel]
  congr 1
  exact Nat.mul_comm _ _

/-- The kernel cardinal in GR-1, in the closed form read off from the graded windows. -/
theorem card_ker_plantedWindowMap {μ N k : ℕ} (hw : μ * k ≤ N) :
    Nat.card (plantedWindowMap (O := O) hw).ker =
      residueCard O ^ (k * (μ * (μ + 1) / 2)) := by
  classical
  let f := plantedWindowMap (O := O) hw
  let S := ∑ j : Fin μ, (N - μ * k + k * (j : ℕ))
  let E := k * (μ * (μ + 1) / 2)
  have hthick : E = ∑ j : Fin μ, k * (μ - (j : ℕ)) := by
    dsimp [E]
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range, sum_range_reverse]
  have hES : E + S = μ * N := by
    rw [hthick]
    dsimp [S]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _j : Fin μ, N := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : k * (j : ℕ) ≤ μ * k := by
          rw [← Nat.mul_comm k μ]
          exact Nat.mul_le_mul_left k (Nat.le_of_lt j.isLt)
        rw [Nat.mul_sub_left_distrib, Nat.mul_comm k μ]
        omega
      _ = μ * N := by simp
  have hsource : Nat.card (Coeff O μ N) = residueCard O ^ (μ * N) := by
    rw [Nat.card_pi]
    simp only [card_res, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    rw [Nat.mul_comm]
  have htarget : Nat.card (PlantedWindowBox (O := O) μ N k) = residueCard O ^ S := by
    rw [Nat.card_pi]
    simp only [card_res]
    rw [Finset.prod_pow_eq_pow_sum]
  have hprod := card_preimage_of_surjective f (plantedWindowMap_surjective (O := O) hw) Set.univ
  have hdom : Nat.card (f ⁻¹' Set.univ) = Nat.card (Coeff O μ N) :=
    Nat.card_congr (Equiv.Set.univ _)
  have hcod : Nat.card (Set.univ : Set (PlantedWindowBox (O := O) μ N k)) =
      Nat.card (PlantedWindowBox (O := O) μ N k) := Nat.card_congr (Equiv.Set.univ _)
  rw [hdom, hcod] at hprod
  rw [hsource, htarget] at hprod
  have hsplit : residueCard O ^ (μ * N) =
      residueCard O ^ E * residueCard O ^ S := by rw [← pow_add, hES]
  rw [hsplit] at hprod
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) S) hprod.symm

/-- Closed-value form of GR-1. -/
theorem card_plantedFactor_fiber_closed {π : O} (hπ : Irreducible π) {μ N k : ℕ}
    (hN : 1 ≤ N) (hμ : 1 ≤ μ) (hw : μ * k ≤ N - 1)
    (z : ResidueField O) (y : Coeff O μ N)
    (hy : y ∈ Set.range (plantedFactorClass (O := O) π μ N k z)) :
    Nat.card {d : ClusterState O μ N // plantedFactorClass π μ N k z d = y} =
      residueCard O ^ (k * (μ * (μ + 1) / 2)) := by
  obtain ⟨ghost, -, hg⟩ := card_plantedFactor_fiber hπ hN hμ hw z
  rw [hg y hy]
  obtain ⟨d₀, rfl⟩ := hy
  rw [← hg _ ⟨d₀, rfl⟩, Nat.card_congr
    (plantedFactorFiberEquivWindowFiber hπ hμ hN hw (by omega) z d₀)]
  have hf := card_preimage_of_surjective (plantedWindowMap (O := O) (by omega : μ * k ≤ N))
    (plantedWindowMap_surjective (O := O) (by omega))
    ({plantedWindowMap (O := O) (by omega : μ * k ≤ N) d₀.1} :
      Set (PlantedWindowBox (O := O) μ N k))
  change Nat.card {x : Coeff O μ N //
    plantedWindowMap (O := O) (by omega : μ * k ≤ N) x =
      plantedWindowMap (O := O) (by omega : μ * k ≤ N) d₀.1} = _
  have he : {x : Coeff O μ N //
      plantedWindowMap (O := O) (by omega : μ * k ≤ N) x =
        plantedWindowMap (O := O) (by omega : μ * k ≤ N) d₀.1} ≃
      ((plantedWindowMap (O := O) (by omega : μ * k ≤ N)) ⁻¹'
        {plantedWindowMap (O := O) (by omega : μ * k ≤ N) d₀.1}) :=
    Equiv.subtypeEquivRight (fun x => by simp)
  rw [Nat.card_congr he]
  simpa only [Nat.card_unique, mul_one, card_ker_plantedWindowMap] using hf

/-! ### GR-2: finite constant-fibre bookkeeping -/

/-- A finite map whose nonempty fibres all have size `ghost` has total cardinality
`ghost` times the cardinality of its image. -/
theorem card_domain_eq_ghost_mul_range {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (ghost : ℕ)
    (hf : ∀ y ∈ Set.range f, Nat.card {a : A // f a = y} = ghost) :
    Nat.card A = ghost * Nat.card (Set.range f) := by
  classical
  let f' : A → Set.range f := fun a => ⟨f a, ⟨a, rfl⟩⟩
  have hfin : Finite (Set.range f) := Set.toFinite _
  letI : Fintype (Set.range f) := Fintype.ofFinite _
  calc
    Nat.card A = Nat.card ((y : Set.range f) × {a : A // f' a = y}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f')).symm
    _ = ∑ y : Set.range f, Nat.card {a : A // f' a = y} := Nat.card_sigma
    _ = ∑ _y : Set.range f, ghost := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← hf y.1 y.2]
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun a => by simp only [f']; exact Subtype.ext_iff)
    _ = ghost * Nat.card (Set.range f) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Finset.card_univ]
      exact Nat.mul_comm _ _

/-- Raw child classes, one for each member of `L`. -/
abbrev RawFactors (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Finset (ℕ × ℕ × ResidueField O)) (N : ℕ) :=
  ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N

/-- Forget precisely the shear ghosts in every raw child coordinate. -/
noncomputable def rawFactorImages (π : O) {N : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (bb : RawFactors O L N) :
    ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      PlantedFactorImage (O := O) π p.1.1 N p.1.2.1 p.1.2.2 :=
  fun p => ⟨plantedFactorClass π p.1.1 N p.1.2.1 p.1.2.2 (bb p), ⟨bb p, rfl⟩⟩

/-- A fibre of the dependent product map is the dependent product of its coordinate fibres. -/
noncomputable def rawFactorFiberEquiv (π : O) {N : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O))
    (y : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      PlantedFactorImage (O := O) π p.1.1 N p.1.2.1 p.1.2.2) :
    {bb : RawFactors O L N // rawFactorImages π L bb = y} ≃
      (∀ p, {d : ClusterState O p.1.1 N //
        plantedFactorClass π p.1.1 N p.1.2.1 p.1.2.2 d = (y p).1}) where
  toFun bb p := ⟨bb.1 p, congrArg Subtype.val (congrFun bb.2 p)⟩
  invFun d := ⟨fun p => (d p).1, by
    funext p
    apply Subtype.ext
    exact (d p).2⟩
  left_inv bb := by ext; rfl
  right_inv d := by ext; rfl

/-- **GR-2, dependent-product form.** The raw-to-image map has the product of the closed
per-factor ghost sizes at every image tuple. -/
theorem card_rawFactorImages_fiber {π : O} (hπ : Irreducible π)
    {N : ℕ} (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O))
    (hL : ∀ p ∈ L, 1 ≤ p.1 ∧ p.1 * p.2.1 ≤ N - 1)
    (y : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      PlantedFactorImage (O := O) π p.1.1 N p.1.2.1 p.1.2.2) :
    Nat.card {bb : RawFactors O L N // rawFactorImages π L bb = y} =
      ∏ p ∈ L, residueCard O ^ (p.2.1 * (p.1 * (p.1 + 1) / 2)) := by
  rw [Nat.card_congr (rawFactorFiberEquiv π L y), Nat.card_pi]
  rw [← Finset.prod_attach L
    (fun p => residueCard O ^ (p.2.1 * (p.1 * (p.1 + 1) / 2)))]
  apply Finset.prod_congr rfl
  intro p _
  exact card_plantedFactor_fiber_closed hπ hN (hL p.1 p.2).1 (hL p.1 p.2).2
    p.1.2.2 (y p).1 (y p).2

end Ghost

/-! ## GR-3: eliminate the monic cofactor over the quotient ring -/

section Fit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `monicPoly` is monic over any nontrivial commutative ring; the older API carries an
unneeded domain parameter. -/
theorem monicPoly_monic_ring {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) : (monicPoly a).Monic := by
  unfold monicPoly
  apply (monic_X_pow n).add_of_left
  have hXn : (X ^ n : Polynomial R).degree = (n : WithBot ℕ) := by
    simpa using (degree_X_pow (R := R) n)
  rw [hXn]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro i _
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le (i : ℕ) (a i)) ?_
  exact_mod_cast i.isLt

theorem monicPoly_natDegree_ring {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) : (monicPoly a).natDegree = n := by
  have hd : (monicPoly a).degree = (n : WithBot ℕ) := by
    unfold monicPoly
    rw [degree_add_eq_left_of_degree_lt]
    · simpa using (degree_X_pow (R := R) n)
    · have hXn : (X ^ n : Polynomial R).degree = (n : WithBot ℕ) := by
        simpa using (degree_X_pow (R := R) n)
      rw [hXn]
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
      intro i _
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le (i : ℕ) (a i)) (by exact_mod_cast i.isLt)
  rw [natDegree, hd]
  rfl

theorem monicPoly_coeff_lt_ring {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) {i : ℕ} (hi : i < n) : (monicPoly a).coeff i = a ⟨i, hi⟩ := by
  unfold monicPoly
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hi), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbi
    have hne : i ≠ (b : ℕ) := fun heq => hbi (Fin.ext heq.symm)
    rw [coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]
  · simp

/-- Reading back the low coefficients of a monic degree-`n` polynomial is valid over any
commutative ring. -/
theorem monicPoly_coeff_self_ring {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} {F : Polynomial R} (hF : F.Monic) (hd : F.natDegree = n) :
    monicPoly (fun i : Fin n => F.coeff (i : ℕ)) = F := by
  apply ext_of_monic_of_coeff_lt (monicPoly_monic_ring _) hF
    (monicPoly_natDegree_ring _) hd
  intro i hi
  rw [monicPoly_coeff_lt_ring _ hi]

/-- A tuple of level-`N` planted-factor image classes. -/
abbrev ImageFactors (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (L : Finset (ℕ × ℕ × ResidueField O)) (N : ℕ) :=
  ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
    PlantedFactorImage (O := O) π p.1.1 N p.1.2.1 p.1.2.2

/-- The monic product represented by a tuple of factor images, now over `O/𝔪^N`. -/
noncomputable def imageFactorProduct (π : O) {N : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (P : ImageFactors O π L N) :
    Polynomial (Res O N) :=
  ∏ p ∈ L.attach, monicPoly (P p).1

theorem imageFactorProduct_monic (π : O) {N : ℕ}
    (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O)) (P : ImageFactors O π L N) :
    (imageFactorProduct π L P).Monic :=
  letI := nontrivial_res O hN
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => monicPoly_monic_ring _)

theorem imageFactorProduct_natDegree (π : O) {N : ℕ}
    (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O)) (P : ImageFactors O π L N) :
    (imageFactorProduct π L P).natDegree = ∑ p ∈ L, p.1 := by
  letI := nontrivial_res O hN
  rw [imageFactorProduct, Polynomial.natDegree_prod_of_monic _ _
    (fun p _ => monicPoly_monic_ring (P p).1)]
  rw [Finset.sum_congr rfl (fun p _ => monicPoly_natDegree_ring (P p).1)]
  exact Finset.sum_attach L (fun p => p.1)

/-- The level-`N` target coefficient vector of image factors times a cofactor class. -/
noncomputable def imageProductClass (π : O) {m N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (P : ImageFactors O π L N)
    (Qc : ClusterState O r N) : Coeff O m N :=
  fun i => ((imageFactorProduct π L P) * monicPoly Qc.1).coeff (i : ℕ)

/-- Image presentations retain the uniquely recoverable cofactor coordinate. -/
abbrev ImgPres (π : O) {m N : ℕ} (L : Finset (ℕ × ℕ × ResidueField O))
    (r : ℕ) (c : ClusterState O m N) :=
  {x : ImageFactors O π L N × ClusterState O r N //
    imageProductClass π L x.1 x.2 = c.1}

/-- `Fit` remembers exactly those factor-image tuples for which a cluster cofactor exists. -/
abbrev Fit (π : O) {m N : ℕ} (L : Finset (ℕ × ℕ × ResidueField O))
    (r : ℕ) (c : ClusterState O m N) :=
  {P : ImageFactors O π L N // ∃ Qc : ClusterState O r N,
    imageProductClass π L P Qc = c.1}

/-- Monic division uniqueness in the form needed here: once the image factors are fixed, two
cofactor cluster classes giving the same degree-`m` target are equal. -/
theorem cofactor_eq_of_imageProductClass_eq {π : O} (hπ : Irreducible π)
    {m N r : ℕ} (hN : 1 ≤ N)
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hdeg : (∑ p ∈ L, p.1) + r = m) (P : ImageFactors O π L N)
    (Q Q' : ClusterState O r N)
    (h : imageProductClass π (m := m) L P Q = imageProductClass π L P Q') : Q = Q' := by
  letI := nontrivial_res O hN
  have hA := imageFactorProduct_monic π hN L P
  have hF : ((imageFactorProduct π L P) * monicPoly Q.1).Monic :=
    hA.mul (monicPoly_monic_ring _)
  have hF' : ((imageFactorProduct π L P) * monicPoly Q'.1).Monic :=
    hA.mul (monicPoly_monic_ring _)
  have hdF : ((imageFactorProduct π L P) * monicPoly Q.1).natDegree = m := by
    rw [hA.natDegree_mul (monicPoly_monic_ring _),
      imageFactorProduct_natDegree π hN, monicPoly_natDegree_ring, hdeg]
  have hdF' : ((imageFactorProduct π L P) * monicPoly Q'.1).natDegree = m := by
    rw [hA.natDegree_mul (monicPoly_monic_ring _),
      imageFactorProduct_natDegree π hN, monicPoly_natDegree_ring, hdeg]
  have hprod : (imageFactorProduct π L P) * monicPoly Q.1 =
      (imageFactorProduct π L P) * monicPoly Q'.1 := by
    rw [← monicPoly_coeff_self_ring hF hdF, ← monicPoly_coeff_self_ring hF' hdF']
    exact congrArg monicPoly h
  have hQ : monicPoly Q.1 = monicPoly Q'.1 := hA.isRegular.left hprod
  apply Subtype.ext
  funext i
  have hi := congrArg (fun F : Polynomial (Res O N) => F.coeff (i : ℕ)) hQ
  simpa only [monicPoly_coeff_lt_ring _ i.isLt] using hi

/-- **GR-3.** Monic quotient mechanics eliminate the cofactor coordinate from an image
presentation.  No cancellation in the quotient ring is assumed; regularity comes from the
monicity of the factor product. -/
noncomputable def imagePresentation_equiv_fit {π : O} (hπ : Irreducible π)
    {m N r : ℕ} (hN : 1 ≤ N)
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hdeg : (∑ p ∈ L, p.1) + r = m) (c : ClusterState O m N) :
    ImgPres π L r c ≃ Fit π L r c where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun P := ⟨⟨P.1, P.2.choose⟩, P.2.choose_spec⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (cofactor_eq_of_imageProductClass_eq hπ hN L hdeg x.1.1 _ _
      ((Classical.choose_spec
        (show ∃ Qc : ClusterState O r N, imageProductClass π L x.1.1 Qc = c.1 from
          ⟨x.1.2, x.2⟩)).trans x.2.symm))
  right_inv P := by ext; rfl

end Fit

/-! ### GR-2 at the planted-presentation fibre -/

section RawPresentation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The raw pair fibre used by the signed H.116b4 statement. -/
abbrev Pres (π : O) {m N : ℕ} (L : Finset (ℕ × ℕ × ResidueField O))
    (r : ℕ) (c : ClusterState O m N) :=
  {x : RawFactors O L N × ClusterState O r N //
    proj O m N (fun i : Fin m => (plantedPoly π L x.1 x.2).coeff (i : ℕ)) = c.1}

theorem monicPoly_proj_eq_map {n N : ℕ} (a : Fin n → O) :
    monicPoly (proj O n N a) =
      (monicPoly a).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
  exact (map_monicPoly (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) a).symm

/-- Reducing a raw planted polynomial modulo `𝔪^N` is exactly multiplication of its
factor-image polynomials and its cofactor class polynomial. -/
theorem imagePolynomial_raw_eq_map_plantedPoly (π : O) {N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (bb : RawFactors O L N)
    (Qc : ClusterState O r N) :
    imageFactorProduct π L (rawFactorImages π L bb) * monicPoly Qc.1 =
      (plantedPoly π L bb Qc).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
  rw [plantedPoly, Polynomial.map_mul, imageFactorProduct, Polynomial.map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    change monicPoly (proj O p.1.1 N
      (alphaParentCoeff π (classSect O p.1.1 N (bb p).1) p.1.2.1 (resSect O p.1.2.2))) = _
    rw [monicPoly_proj_eq_map, monicPoly_alphaParentCoeff]
  · calc
      monicPoly Qc.1 = monicPoly (proj O r N (classSect O r N Qc.1)) := by
        rw [proj_classSect O r N Qc.1]
      _ = _ := monicPoly_proj_eq_map _

theorem imageProductClass_rawFactorImages (π : O) {m N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (bb : RawFactors O L N)
    (Qc : ClusterState O r N) :
    imageProductClass π (m := m) L (rawFactorImages π L bb) Qc =
      proj O m N (fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ)) := by
  funext i
  have h := congrArg (fun F : Polynomial (Res O N) => F.coeff (i : ℕ))
    (imagePolynomial_raw_eq_map_plantedPoly π L bb Qc)
  simpa only [imageProductClass, coeff_map, proj] using h

/-- Forget the raw child ghosts in a presentation, retaining its cofactor. -/
noncomputable def rawPresentationToImage (π : O) {m N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (c : ClusterState O m N) :
    Pres π L r c → ImgPres π L r c := fun x =>
  ⟨⟨rawFactorImages π L x.1.1, x.1.2⟩,
    (imageProductClass_rawFactorImages π L x.1.1 x.1.2).trans x.2⟩

/-- Every image presentation admits a raw lift, coordinatewise. -/
theorem rawPresentationToImage_surjective (π : O) {m N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (c : ClusterState O m N) :
    Function.Surjective (rawPresentationToImage π (r := r) L c) := by
  classical
  intro y
  have hlift : ∀ p, ∃ d : ClusterState O p.1.1 N,
      plantedFactorClass π p.1.1 N p.1.2.1 p.1.2.2 d = (y.1.1 p).1 :=
    fun p => (y.1.1 p).2
  choose bb hbb using hlift
  have himg : rawFactorImages π L bb = y.1.1 := by
    funext p
    apply Subtype.ext
    exact hbb p
  have hraw : proj O m N (fun i : Fin m => (plantedPoly π L bb y.1.2).coeff (i : ℕ)) = c.1 := by
    rw [← imageProductClass_rawFactorImages, himg]
    exact y.2
  refine ⟨⟨⟨bb, y.1.2⟩, hraw⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext himg rfl

/-- A raw-presentation fibre over an image presentation is just the corresponding raw-factor
fibre; the cofactor coordinate is injective and the target equation depends only on the image. -/
noncomputable def rawPresentationFiberEquiv (π : O) {m N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O)) (c : ClusterState O m N)
    (y : ImgPres π L r c) :
    {x : Pres π L r c // rawPresentationToImage π (r := r) L c x = y} ≃
      {bb : RawFactors O L N // rawFactorImages π L bb = y.1.1} where
  toFun x := ⟨x.1.1.1, congrArg (fun q => q.1.1) x.2⟩
  invFun bb := by
    have hraw : proj O m N
        (fun i : Fin m => (plantedPoly π L bb.1 y.1.2).coeff (i : ℕ)) = c.1 := by
      rw [← imageProductClass_rawFactorImages, bb.2]
      exact y.2
    refine ⟨⟨⟨bb.1, y.1.2⟩, hraw⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact bb.2
    · rfl
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (congrArg (fun q => q.1.2) x.2).symm
  right_inv bb := by ext <;> rfl

/-- **GR-2, planted-presentation form.** Raw leaf count equals the product ghost times image
multiplicity, with the cofactor contributing no ghost. -/
theorem card_rawPres_eq_ghost_mul_imagePres {π : O} (hπ : Irreducible π)
    {m N r : ℕ} (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O))
    (hL : ∀ p ∈ L, 1 ≤ p.1 ∧ p.1 * p.2.1 ≤ N - 1)
    (c : ClusterState O m N) :
    Nat.card (Pres π L r c) =
      (∏ p ∈ L, residueCard O ^ (p.2.1 * (p.1 * (p.1 + 1) / 2))) *
        Nat.card (ImgPres π L r c) := by
  let f := rawPresentationToImage π (r := r) L c
  have hsurj : Function.Surjective f := rawPresentationToImage_surjective π L c
  let e : Set.range f ≃ ImgPres π L r c := Equiv.ofBijective
    (fun y => y.1) ⟨Subtype.val_injective, fun y => by
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨⟨f x, x, rfl⟩, hx⟩⟩
  rw [← Nat.card_congr e]
  apply card_domain_eq_ghost_mul_range f
  intro y hy
  obtain ⟨y₀, rfl⟩ := hy
  rw [Nat.card_congr (rawPresentationFiberEquiv π L c (f y₀))]
  exact card_rawFactorImages_fiber hπ hN L hL (f y₀).1.1

end RawPresentation

/-! ## GR-3b: reverse admissibility from the exact frame profile -/

section Admissibility

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **GR-3b.** Every cofactor which actually occurs in a planted presentation of a target
with exact child set `L` is child-free and root-free at the occupied frames; its content is
forced by the planted frame floor. -/
theorem cofactor_admissible_of_plantedPresentation {π : O} (hπ : Irreducible π)
    {m N r : ℕ} (hm : 2 ≤ m) (hN : 1 ≤ N)
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hdeg : (∑ p ∈ L, p.1) + r = m)
    (D : ℕ × ℕ × ResidueField O → ℕ)
    (c : ClusterState O m N) (h0 : ¬ IsDrainState c)
    (hchildren : ∀ p : ℕ × ℕ × ResidueField O,
      HasChildAt π c p.1 p.2.1 p.2.2 ↔ p ∈ L)
    (hcontent : ∀ p ∈ L, betaContent c p.2.1 = D p)
    (bb : ∀ p : {y : ℕ × ℕ × ResidueField O // y ∈ L},
      ClusterState O p.1.1 N)
    (Qc : ClusterState O r N)
    (hc : proj O m N (fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ)) = c.1) :
    (∀ ν k z, ¬ HasChildAt π Qc ν k z) ∧
      (∀ p ∈ L, ∀ aQ : Fin r → O, proj O r N aQ = Qc.1 →
        ¬ π ^ (betaContent Qc p.2.1 + 1) ∣
          ((monicPoly aQ).comp
            (C (π ^ p.2.1) * (X + C (resSect O p.2.2)))).coeff 0) ∧
      ∀ p ∈ L, D p =
        (∑ p' ∈ L, p'.1 * min p'.2.1 p.2.1) + betaContent Qc p.2.1 := by
  classical
  have hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0 := by
    intro p hp
    have hch := (hchildren p).2 hp
    exact ⟨hch.1, hch.2.1, hch.2.2.1⟩
  have hLsep : ∀ p ∈ L, ∀ p' ∈ L, p.2 = p'.2 → p = p' := by
    intro p hp p' hp' heq
    have hk : p.2.1 = p'.2.1 := congrArg Prod.fst heq
    have hz : p.2.2 = p'.2.2 := congrArg Prod.snd heq
    have hch' : HasChildAt π c p'.1 p.2.1 p.2.2 := by
      rw [hk, hz]
      exact (hchildren p').2 hp'
    have hmulteq := hasChildAt_mult_unique ((hchildren p).2 hp) hch'
    exact Prod.ext hmulteq heq
  have hQnd : r = 0 ∨ ¬ IsDrainState Qc := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · exact Or.inl hr
    · refine Or.inr fun hd => h0 ?_
      refine (isDrainState_iff (by omega) c).2 ?_
      have hQ0 : Qc.1 ⟨0, hr⟩ = 0 := (isDrainState_iff hr Qc).1 hd
      have hmk0 : Ideal.Quotient.mk ((maximalIdeal O) ^ N)
          (classSect O r N Qc.1 ⟨0, hr⟩) = 0 := by
        have hx := congrFun (proj_classSect O r N Qc.1) (⟨0, hr⟩ : Fin r)
        rwa [hQ0] at hx
      have hdvd : π ^ N ∣ classSect O r N Qc.1 ⟨0, hr⟩ :=
        (mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).1
          (Ideal.Quotient.eq_zero_iff_mem.1 hmk0)
      have hconst : π ^ N ∣ (plantedPoly π L bb Qc).coeff 0 := by
        rw [plantedPoly, Polynomial.mul_coeff_zero,
          monicPoly_coeff_lt (classSect O r N Qc.1) hr]
        exact Dvd.dvd.mul_left hdvd _
      have hcoord : c.1 ⟨0, by omega⟩ =
          Ideal.Quotient.mk _ ((plantedPoly π L bb Qc).coeff 0) :=
        (congrFun hc ⟨0, by omega⟩).symm
      rw [hcoord]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).2 hconst)
  let a : Fin m → O := fun i => (plantedPoly π L bb Qc).coeff (i : ℕ)
  have hPdeg : (plantedPoly π L bb Qc).natDegree = m := by
    rw [plantedPoly_natDegree, hdeg]
  have haPoly : monicPoly a = plantedPoly π L bb Qc :=
    monicPoly_coeff_self (plantedPoly_monic π L bb Qc) hPdeg
  have htarget_of_profile : ∀ {k : ℕ} {z : ResidueField O} (hk : 1 ≤ k) (hz : z ≠ 0)
      (μ' : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ)
      (hown : ∀ p, p.1.2.1 = k → p.1.2.2 = z → μ' p = p.1.1)
      (hfor : ∀ p, ¬ (p.1.2.1 = k ∧ p.1.2.2 = z) → μ' p = 0)
      (A : ℕ)
      (hA1 : ∀ j < A, π ^ (betaContent Qc k + 1) ∣
        ((monicPoly (classSect O r N Qc.1)).comp
          (C (π ^ k) * (X + C (resSect O z)))).coeff j)
      (hA2 : ¬ π ^ (betaContent Qc k + 1) ∣
        ((monicPoly (classSect O r N Qc.1)).comp
          (C (π ^ k) * (X + C (resSect O z)))).coeff A),
      2 ≤ (∑ p ∈ L.attach, μ' p) + A →
        betaContent c k =
            (∑ p ∈ L, p.1 * min p.2.1 k) + betaContent Qc k ∧
          HasChildAt π c ((∑ p ∈ L.attach, μ' p) + A) k z := by
    intro k z hk hz μ' hown hfor A hA1 hA2 hmult
    obtain ⟨g1, g2, g3⟩ := plantedPoly_frame_profile hπ hN L hLchild bb Qc hz
      (residue_resSect O z) μ' hown hfor A hA1 hA2
    rw [← haPoly] at g1 g2 g3
    have hD : betaContent c k =
        (∑ p ∈ L, p.1 * min p.2.1 k) + betaContent Qc k :=
      betaContent_eq_of_recentre_exact hπ (by omega) hN c h0 k hc (resSect O z) g1
        (fun hall => g3 (hall _))
    refine ⟨hD, hasChildAt_of_exists hπ hN h0 hmult hk hz a (resSect O z) hc
      (residue_resSect O z) ?_ ?_ ?_⟩
    · rw [hD]; exact g1
    · rw [hD]; exact g2
    · rw [hD]; exact g3
  have hoccupied : ∀ p ∈ L,
      D p = (∑ p' ∈ L, p'.1 * min p'.2.1 p.2.1) + betaContent Qc p.2.1 ∧
      ¬ π ^ (betaContent Qc p.2.1 + 1) ∣
        ((monicPoly (classSect O r N Qc.1)).comp
          (C (π ^ p.2.1) * (X + C (resSect O p.2.2)))).coeff 0 := by
    intro p hp
    obtain ⟨A, hA1, hA2, -⟩ := exists_cofactor_abscissa hπ hN Qc hQnd
      (hLchild p hp).2.1 (hLchild p hp).2.2
    let μ' : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ :=
      fun q => if q.1 = p then q.1.1 else 0
    have hown : ∀ q, q.1.2.1 = p.2.1 → q.1.2.2 = p.2.2 → μ' q = q.1.1 := by
      intro q hk hz
      have hqp : q.1 = p := hLsep q.1 q.2 p hp (by ext <;> assumption)
      simp [μ', hqp]
    have hfor : ∀ q, ¬ (q.1.2.1 = p.2.1 ∧ q.1.2.2 = p.2.2) → μ' q = 0 := by
      intro q hq
      have hne : q.1 ≠ p := fun heq => hq ⟨by rw [heq], by rw [heq]⟩
      simp [μ', hne]
    have hsum : (∑ q ∈ L.attach, μ' q) = p.1 := by
      rw [Finset.sum_eq_single_of_mem (⟨p, hp⟩ : {x // x ∈ L})
        (Finset.mem_attach _ _) ]
      · simp [μ']
      · intro q _ hq
        have hne : q.1 ≠ p := fun heq => hq (Subtype.ext heq)
        simp [μ', hne]
    obtain ⟨hD, hch⟩ := htarget_of_profile (hLchild p hp).2.1 (hLchild p hp).2.2
      μ' hown hfor A hA1 hA2 (by rw [hsum]; exact le_trans (hLchild p hp).1 (Nat.le_add_right _ _))
    have hA0 : A = 0 := by
      have hmulteq := hasChildAt_mult_unique hch ((hchildren p).2 hp)
      rw [hsum] at hmulteq
      omega
    refine ⟨(hcontent p hp).symm.trans hD, ?_⟩
    simpa [hA0] using hA2
  refine ⟨?_, ?_, fun p hp => (hoccupied p hp).1⟩
  · intro ν k z hq
    by_cases hex : ∃ p ∈ L, p.2.1 = k ∧ p.2.2 = z
    · obtain ⟨p, hp, hpk, hpz⟩ := hex
      let μ' : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ :=
        fun q => if q.1 = p then q.1.1 else 0
      have hown : ∀ q, q.1.2.1 = k → q.1.2.2 = z → μ' q = q.1.1 := by
        intro q hk hz
        have hqp : q.1 = p := hLsep q.1 q.2 p hp (by
          exact Prod.ext (hk.trans hpk.symm) (hz.trans hpz.symm))
        simp [μ', hqp]
      have hfor : ∀ q, ¬ (q.1.2.1 = k ∧ q.1.2.2 = z) → μ' q = 0 := by
        intro q hq
        have hne : q.1 ≠ p := fun heq => hq ⟨by rw [heq, hpk], by rw [heq, hpz]⟩
        simp [μ', hne]
      have hsum : (∑ q ∈ L.attach, μ' q) = p.1 := by
        rw [Finset.sum_eq_single_of_mem (⟨p, hp⟩ : {x // x ∈ L})
          (Finset.mem_attach _ _)]
        · simp [μ']
        · intro q _ hne
          have hne' : q.1 ≠ p := fun heq => hne (Subtype.ext heq)
          simp [μ', hne']
      obtain ⟨-, htarget⟩ := htarget_of_profile hq.2.1 hq.2.2.1 μ' hown hfor ν
        (hq.2.2.2 (classSect O r N Qc.1) (resSect O z)
          (proj_classSect O r N Qc.1) (residue_resSect O z)).2.1
        (hq.2.2.2 (classSect O r N Qc.1) (resSect O z)
          (proj_classSect O r N Qc.1) (residue_resSect O z)).2.2
        (by rw [hsum]; exact le_trans hq.1 (Nat.le_add_left _ _))
      have hpchild : HasChildAt π c p.1 k z := by
        simpa [hpk, hpz] using (hchildren p).2 hp
      have heq := hasChildAt_mult_unique htarget hpchild
      rw [hsum] at heq
      have hpos : 0 < ν := Nat.zero_lt_of_lt hq.1
      exact (Nat.ne_of_gt (Nat.lt_add_of_pos_right hpos)) heq
    · let μ' : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ := fun _ => 0
      have hown : ∀ q, q.1.2.1 = k → q.1.2.2 = z → μ' q = q.1.1 := by
        intro q hk hz
        exact absurd ⟨q.1, q.2, hk, hz⟩ hex
      have hfor : ∀ q, ¬ (q.1.2.1 = k ∧ q.1.2.2 = z) → μ' q = 0 := by simp [μ']
      obtain ⟨-, htarget⟩ := htarget_of_profile hq.2.1 hq.2.2.1 μ' hown hfor ν
        (hq.2.2.2 (classSect O r N Qc.1) (resSect O z)
          (proj_classSect O r N Qc.1) (residue_resSect O z)).2.1
        (hq.2.2.2 (classSect O r N Qc.1) (resSect O z)
          (proj_classSect O r N Qc.1) (residue_resSect O z)).2.2 (by simp [μ']; exact hq.1)
      have htarget' : HasChildAt π c ν k z := by simpa [μ'] using htarget
      exact hex ⟨(ν, k, z), (hchildren (ν, k, z)).1 htarget', rfl, rfl⟩
  · intro p hp aQ haQ hroot
    have hcanon := (hoccupied p hp).2
    by_cases hr : r = 0
    · subst r
      have haeq : monicPoly aQ = monicPoly (classSect O 0 N Qc.1) := by
        rw [monicPoly, monicPoly]
        simp
      exact hcanon (by rwa [haeq] at hroot)
    · have hQN : betaContent Qc p.2.1 + 1 ≤ N := by
        have hnd : ¬ IsDrainState Qc := hQnd.resolve_left hr
        have := betaContent_le (by omega : 1 ≤ r) hN Qc hnd p.2.1
        omega
      have hswap := pow_dvd_coeff_comp_sub hπ
        (haQ.trans (proj_classSect O r N Qc.1).symm)
        (C (π ^ p.2.1) * (X + C (resSect O p.2.2))) 0
      have hdiff : π ^ (betaContent Qc p.2.1 + 1) ∣
          (((monicPoly aQ).comp (C (π ^ p.2.1) * (X + C (resSect O p.2.2)))) -
            ((monicPoly (classSect O r N Qc.1)).comp
              (C (π ^ p.2.1) * (X + C (resSect O p.2.2))))).coeff 0 :=
        (pow_dvd_pow π hQN).trans hswap
      apply hcanon
      rw [coeff_sub] at hdiff
      simpa only [sub_sub_cancel] using dvd_sub hroot hdiff

end Admissibility

end Uniformity.Density.Induction

section AxCheck

#print axioms Uniformity.Density.Induction.plantedFactorClass
#print axioms Uniformity.Density.Induction.plantedFactorClass_eq_iff
#print axioms Uniformity.Density.Induction.card_plantedFactor_fiber
#print axioms Uniformity.Density.Induction.card_ker_plantedWindowMap
#print axioms Uniformity.Density.Induction.card_plantedFactor_fiber_closed
#print axioms Uniformity.Density.Induction.card_rawFactorImages_fiber
#print axioms Uniformity.Density.Induction.card_rawPres_eq_ghost_mul_imagePres
#print axioms Uniformity.Density.Induction.cofactor_eq_of_imageProductClass_eq
#print axioms Uniformity.Density.Induction.imagePresentation_equiv_fit
#print axioms Uniformity.Density.Induction.cofactor_admissible_of_plantedPresentation

end AxCheck
