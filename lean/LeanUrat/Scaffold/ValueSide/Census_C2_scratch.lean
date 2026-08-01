import Mathlib
import LeanUrat.Scaffold.ValueSide.Census

namespace LeanUrat.Scaffold

namespace C2R1Salvage

/-- Counting helper 1: over the two-stage pi carrier, a predicate reading only
    stage 1 counts with multiplicity `card (G 0)`. -/
theorem card_filter_pi_two {G : Fin 2 → Type} [∀ i, Fintype (G i)]
    (Q : G 1 → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun j : (i : Fin 2) → G i => Q (j 1))).card
      = Fintype.card (G 0) * (Finset.univ.filter Q).card := by
  classical
  calc (Finset.univ.filter (fun j : (i : Fin 2) → G i => Q (j 1))).card
      = ∑ j : (i : Fin 2) → G i, if Q (j 1) then 1 else 0 :=
        Finset.card_filter _ _
    _ = ∑ p : G 0 × G 1, if Q p.2 then 1 else 0 :=
        Fintype.sum_equiv (piFinTwoEquiv G) _ _ (fun _ => rfl)
    _ = ∑ _x : G 0, ∑ y : G 1, if Q y then 1 else 0 := Fintype.sum_prod_type _
    _ = Fintype.card (G 0) * ∑ y : G 1, if Q y then 1 else 0 := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    _ = Fintype.card (G 0) * (Finset.univ.filter Q).card := by
        rw [Finset.card_filter]

/-- Counting helper 2: pinning the first coordinate of a product costs nothing. -/
theorem card_filter_prod_fst_eq {α β' : Type} [Fintype α] [Fintype β']
    [DecidableEq α] (a0 : α) (R : β' → Prop) [DecidablePred R] :
    (Finset.univ.filter (fun p : α × β' => p.1 = a0 ∧ R p.2)).card
      = (Finset.univ.filter R).card := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.card_filter]
  simp [ite_and]

/-- Counting helper 3: a monotone window over `Fin F1` is full iff its top
    element clears. -/
theorem card_filter_window {F1 : ℕ} (hF1 : 1 ≤ F1) (g : ℕ → ℕ) (hg : Monotone g)
    (β : ℕ) :
    (Finset.univ.filter (fun b : Fin F1 => g b.1 ≤ β)).card = F1
      ↔ g (F1 - 1) ≤ β := by
  constructor
  · intro hcard
    have huniv : (Finset.univ.filter (fun b : Fin F1 => g b.1 ≤ β))
        = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard, Fintype.card_fin]
    have hmem : (⟨F1 - 1, by omega⟩ : Fin F1)
        ∈ Finset.univ.filter (fun b : Fin F1 => g b.1 ≤ β) := by
      rw [huniv]; exact Finset.mem_univ _
    simpa using (Finset.mem_filter.mp hmem).2
  · intro htop
    have hall : ∀ b : Fin F1, g b.1 ≤ β := fun b =>
      le_trans (hg (by have := b.2; omega : b.1 ≤ F1 - 1)) htop
    rw [Finset.filter_true_of_mem (fun b _ => hall b), Finset.card_univ,
      Fintype.card_fin]

/-- Congruence helper: for `a < e₁` and `h₁` a unit mod `e₁`, the slot weight
    `(a + e₁·b)·h₁` is `≡ β (mod e₁)` iff `a` is the canonical class digit
    `(h₁⁻¹·β mod e₁)`. -/
theorem weight_mod_iff {E1 H1 : ℕ} [NeZero E1] (hcop : Nat.Coprime H1 E1)
    (β aa bb : ℕ) (ha : aa < E1) :
    ((aa + E1 * bb) * H1) % E1 = β % E1
      ↔ aa = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
          * (β : ZMod E1) : ZMod E1).val := by
  have hu : ((ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : ZMod E1)
      = (H1 : ZMod E1) := ZMod.coe_unitOfCoprime H1 hcop
  have hcast : (((aa + E1 * bb) * H1 : ℕ) : ZMod E1)
      = (aa : ZMod E1) * (H1 : ZMod E1) := by
    push_cast
    rw [ZMod.natCast_self]
    ring
  constructor
  · intro hmod
    have h1 : (((aa + E1 * bb) * H1 : ℕ) : ZMod E1) = ((β : ℕ) : ZMod E1) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rw [hcast, ← hu] at h1
    have h3 : (aa : ZMod E1)
        = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
            * (β : ZMod E1) : ZMod E1) := by
      calc (aa : ZMod E1)
          = (aa : ZMod E1) * (ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ)
            * ((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) :=
            (Units.mul_inv_cancel_right _ _).symm
        _ = (β : ZMod E1) * ((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) := by
            rw [h1]
        _ = _ := mul_comm _ _
    calc aa = ((aa : ℕ) : ZMod E1).val := (ZMod.val_cast_of_lt ha).symm
      _ = _ := by rw [h3]
  · intro haa
    have h3 : (aa : ZMod E1)
        = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
            * (β : ZMod E1) : ZMod E1) := by
      rw [haa]
      exact ZMod.natCast_zmod_val _
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [hcast, h3, ← hu]
    calc (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) * (β : ZMod E1))
          * ((ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : ZMod E1)
        = (β : ZMod E1) * ((ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : ZMod E1)
          * ((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) := by ring
      _ = (β : ZMod E1) := Units.mul_inv_cancel_right _ _

end C2R1Salvage

/-- C2 SALVAGE core (pointwise form): at r = 1 with the O9 stage-0 scope
    e₀ = 1, a slot β is FULLY attained iff it clears `r1Bound`. -/
theorem attainDim_eq_d_iff_r1Bound_le {D : CensusData} (hr : D.r = 1)
    (he0 : D.e 0 = 1) (β : ℕ) :
    D.attainDim β = D.d ↔ r1Bound D β ≤ β := by
  obtain ⟨r, e, h, f, he, hf, htri, hcop⟩ := D
  dsimp only at hr he0
  subst hr
  set Dm : CensusData := ⟨1, e, h, f, he, hf, htri, hcop⟩ with hDm
  haveI : NeZero (e 1) := ⟨by have := he 1; omega⟩
  set A : ℕ := (((ZMod.unitOfCoprime (h 1) (hcop 1))⁻¹ : (ZMod (e 1))ˣ)
      * (β : ZMod (e 1)) : ZMod (e 1)).val with hA
  -- the displayed RHS, unfolded
  have hrb : r1Bound Dm β = h 1 * (A + (f 1 - 1) * e 1) := by
    simp only [hA]
    rfl
  -- the degree and the period
  have hd : Dm.d = f 0 * f 1 := Fin.prod_univ_two f
  have hperiod : Dm.period = e 1 := by
    have h2 : Dm.period = e 0 * e 1 := Fin.prod_univ_two e
    rw [h2, he0, one_mul]
  -- the stage weights
  have hwphi0 : Dm.wphi 0 = 0 := rfl
  have hwphi1 : Dm.wphi 1 = h 1 := by
    have h2 : Dm.wphi 1 = e 1 * 0 + h 1 := rfl
    omega
  -- the slot weight at r = 1
  have hwt : ∀ j : Dm.J, Dm.wt j = ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 := by
    intro j
    have h2 : Dm.wt j
        = ((j 0).1.1 + e 0 * (j 0).2.1) * Dm.wphi 0
          + ((j 1).1.1 + e 1 * (j 1).2.1) * Dm.wphi 1 :=
      Fin.sum_univ_two _
    rw [h2, hwphi0, hwphi1, mul_zero, zero_add]
  -- reduce the census count to a stage-1 count
  have hattain : Dm.attainDim β
      = (Finset.univ.filter (fun j : Dm.J =>
          (((j 1).1.1 + e 1 * (j 1).2.1) * h 1) % e 1 = β % e 1
            ∧ ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 ≤ β)).card := by
    unfold CensusData.attainDim CensusData.Gset
    congr 1
    refine Finset.filter_congr ?_
    intro j _
    rw [hwt j, hperiod]
  have hstep : (Finset.univ.filter (fun j : Dm.J =>
        (((j 1).1.1 + e 1 * (j 1).2.1) * h 1) % e 1 = β % e 1
          ∧ ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 ≤ β)).card
      = Fintype.card (Fin (e 0) × Fin (f 0))
        * (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
            ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
              ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)).card :=
    C2R1Salvage.card_filter_pi_two (G := fun i => Fin (e i) × Fin (f i))
      (fun y => ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
        ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)
  rw [hattain, hstep, hd, hrb, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, he0, one_mul]
  by_cases hzero : h 1 = 0
  · -- degenerate stage: h₁ = 0 forces e₁ = 1; both sides hold
    have he1 : e 1 = 1 := by
      have hc := hcop 1
      rw [hzero] at hc
      exact (Nat.coprime_zero_left _).mp hc
    have hQtrue : ∀ y : Fin (e 1) × Fin (f 1),
        (((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
          ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β) := by
      intro y
      rw [hzero, mul_zero, he1]
      omega
    apply iff_of_true
    · rw [Finset.filter_true_of_mem (fun y _ => hQtrue y), Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, he1, one_mul]
    · rw [hzero, zero_mul]
      exact Nat.zero_le β
  · -- live stage: pin the class digit and count the window
    have hAlt : A < e 1 := by
      rw [hA]
      exact ZMod.val_lt _
    have hQiff : ∀ y : Fin (e 1) × Fin (f 1),
        ((((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
            ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)
          ↔ (y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ (A + e 1 * y.2.1) * h 1 ≤ β)) := by
      intro y
      constructor
      · rintro ⟨hc, hle⟩
        have h1y : y.1.1 = A := by
          rw [hA]
          exact (C2R1Salvage.weight_mod_iff (hcop 1) β y.1.1 y.2.1 y.1.2).mp hc
        refine ⟨Fin.ext h1y, ?_⟩
        rw [← h1y]
        exact hle
      · rintro ⟨hfst, hle⟩
        have h1y : y.1.1 = A := by rw [hfst]
        refine ⟨(C2R1Salvage.weight_mod_iff (hcop 1) β y.1.1 y.2.1 y.1.2).mpr
            (by rw [h1y, hA]), ?_⟩
        rw [h1y]
        exact hle
    have hcard2 : (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
          ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = β % e 1
            ∧ (y.1.1 + e 1 * y.2.1) * h 1 ≤ β)).card
        = (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
            y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ (A + e 1 * y.2.1) * h 1 ≤ β)).card :=
      congrArg Finset.card (Finset.filter_congr (fun y _ => hQiff y))
    have hcard3 : (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
          y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ (A + e 1 * y.2.1) * h 1 ≤ β)).card
        = (Finset.univ.filter (fun b : Fin (f 1) =>
            (A + e 1 * b.1) * h 1 ≤ β)).card :=
      C2R1Salvage.card_filter_prod_fst_eq (⟨A, hAlt⟩ : Fin (e 1))
        (fun b : Fin (f 1) => (A + e 1 * b.1) * h 1 ≤ β)
    rw [hcard2, hcard3]
    have hmono : Monotone (fun t => (A + e 1 * t) * h 1) := by
      intro x y hxy
      show (A + e 1 * x) * h 1 ≤ (A + e 1 * y) * h 1
      gcongr
    have hf0 : 0 < f 0 := by have := hf 0; omega
    calc f 0 * (Finset.univ.filter (fun b : Fin (f 1) =>
            (A + e 1 * b.1) * h 1 ≤ β)).card = f 0 * f 1
        ↔ (Finset.univ.filter (fun b : Fin (f 1) =>
            (A + e 1 * b.1) * h 1 ≤ β)).card = f 1 := by
          constructor
          · exact Nat.eq_of_mul_eq_mul_left hf0
          · intro hh
            rw [hh]
      _ ↔ (A + e 1 * (f 1 - 1)) * h 1 ≤ β :=
          C2R1Salvage.card_filter_window (hf 1)
            (fun t => (A + e 1 * t) * h 1) hmono β
      _ ↔ h 1 * (A + (f 1 - 1) * e 1) ≤ β := by
          rw [show (A + e 1 * (f 1 - 1)) * h 1
              = h 1 * (A + (f 1 - 1) * e 1) from by ring]

/-- C2 SALVAGE: the r = 1 criterion IS true on the O9 stage-0 scope e₀ = 1. -/
theorem admFull_r1_iff_of_e0_eq_one {D : CensusData} (hr : D.r = 1)
    (he0 : D.e 0 = 1) :
    ADMFull D ↔ ∀ β ∈ D.onLineSlots, r1Bound D β ≤ β :=
  ⟨fun hFull β hβ => (attainDim_eq_d_iff_r1Bound_le hr he0 β).mp
      (hFull.full_attained β hβ),
   fun hB => ⟨fun β hβ => (attainDim_eq_d_iff_r1Bound_le hr he0 β).mpr (hB β hβ)⟩⟩

end LeanUrat.Scaffold
