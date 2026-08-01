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
  rw [← Finset.univ_product_univ, Finset.filter_product, Finset.card_product,
    Finset.filter_eq', if_pos (Finset.mem_univ a0), Finset.card_singleton, one_mul]

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
    have h2 : (aa : ZMod E1)
        = (β : ZMod E1) * ((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) :=
      Units.eq_mul_inv_iff_mul_eq.mpr h1
    have h3 : (aa : ZMod E1)
        = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
            * (β : ZMod E1) : ZMod E1) := by
      rw [h2]; ring
    calc aa = ((aa : ℕ) : ZMod E1).val := (ZMod.val_cast_of_lt ha).symm
      _ = _ := by rw [h3]
  · intro haa
    have h3 : (aa : ZMod E1)
        = (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
            * (β : ZMod E1) : ZMod E1) := by
      rw [haa]
      exact ZMod.natCast_rightInverse _
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [hcast, h3, ← hu]
    calc (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ) * (β : ZMod E1))
          * ((ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : ZMod E1)
        = (β : ZMod E1) * (((ZMod.unitOfCoprime H1 hcop)⁻¹ : (ZMod E1)ˣ)
            * (ZMod.unitOfCoprime H1 hcop : (ZMod E1)ˣ) : (ZMod E1)ˣ) := by
          push_cast
          ring
      _ = (β : ZMod E1) := by rw [inv_mul_cancel]; simp

end C2R1Salvage

/-- C2 SALVAGE core (pointwise form): at r = 1 with the O9 stage-0 scope
    e₀ = 1, a slot β is FULLY attained iff it clears `r1Bound`. -/
theorem attainDim_eq_d_iff_r1Bound_le {D : CensusData} (hr : D.r = 1)
    (he0 : D.e 0 = 1) (β : ℕ) :
    D.attainDim β = D.d ↔ r1Bound D β ≤ β := by
  obtain ⟨r, e, h, f, he, hf, htri, hcop⟩ := D
  dsimp only at hr he0
  subst hr
  sorry

end LeanUrat.Scaffold
