import LeanUrat.Scaffold.DictIII.GDOrder1

namespace LeanUrat.Scaffold.DictIII

-- Probe C: instance landscape for the display's arithmetic (all EXIST).
#synth SMul ℤ (WithTop ℤ)
#synth Mul (WithTop ℤ)
#synth SubNegMonoid (WithTop ℤ)

-- Probe D: compiled witness that a gaussW at the DISPLAYED signature (DVR
-- carrier) can never serve w1's use site: FractionRing O is a field.
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ¬ IsDiscreteValuationRing (FractionRing O) :=
  fun h => @IsDiscreteValuationRing.not_isField (FractionRing O) _ _ h
    (Field.toIsField _)

-- Probe D': gaussW at the DISPLAYED signature, minimally repaired body;
-- then w1 verbatim against it → expect instance-synthesis failure.
namespace ProbeDVRSig

open Classical in
noncomputable def gaussW {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B : Polynomial O) : WithTop ℤ :=
  if hB : B = 0 then ⊤ else
    Finset.min' (B.support.image fun _ => ((0 : ℤ) : WithTop ℤ))
      (by simpa [Polynomial.support_nonempty] using hB)

noncomputable def w1 {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun t =>
    (e : ℤ) • gaussW (devCoeff (Polynomial.map (algebraMap O (FractionRing O)) Φ₀) B t) +
      ((t : ℤ) * (h : ℤ))

end ProbeDVRSig

-- Probe E: gaussW carrier-generalized (the display body consumes no DVR
-- structure); w1 + w1_posg VERBATIM against it; provability validation.
namespace ProbeRepair

open Classical in
noncomputable def gaussW {K : Type*} [CommRing K] (B : Polynomial K) : WithTop ℤ :=
  if hB : B = 0 then ⊤ else
    Finset.min' (B.support.image fun _ => ((0 : ℤ) : WithTop ℤ))
      (by simpa [Polynomial.support_nonempty] using hB)

@[simp] theorem gaussW_zero {K : Type*} [CommRing K] :
    gaussW (0 : Polynomial K) = ⊤ := by simp [gaussW]

theorem gaussW_of_ne_zero {K : Type*} [CommRing K] {B : Polynomial K}
    (hB : B ≠ 0) : gaussW B = 0 := by
  rw [gaussW, dif_neg hB]
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr hB
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  · refine Finset.le_min' _ _ _ fun y hy => ?_
    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
    exact le_rfl

theorem gaussW_eq_top_or_zero {K : Type*} [CommRing K] (B : Polynomial K) :
    gaussW B = ⊤ ∨ gaussW B = 0 := by
  by_cases hB : B = 0
  · exact Or.inl (by simp [hB])
  · exact Or.inr (gaussW_of_ne_zero hB)

theorem gaussW_nonneg {K : Type*} [CommRing K] (B : Polynomial K) :
    0 ≤ gaussW B := by
  rcases gaussW_eq_top_or_zero B with h | h <;> simp [h]

-- w1 VERBATIM (against the carrier-generalized gaussW)
noncomputable def w1 {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun t =>
    (e : ℤ) • gaussW (devCoeff (Polynomial.map (algebraMap O (FractionRing O)) Φ₀) B t) +
      ((t : ℤ) * (h : ℤ))

-- per-slot nonnegativity core
theorem w1_slot_nonneg {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (e h : ℕ) (C : Polynomial (FractionRing O))
    (t : ℕ) : (0 : WithTop ℤ) ≤ (e : ℤ) • gaussW C + ((t : ℤ) * (h : ℤ)) := by
  refine add_nonneg ?_ ?_
  · rw [natCast_zsmul]
    exact nsmul_nonneg (gaussW_nonneg C) e
  · exact_mod_cast mul_nonneg (Int.natCast_nonneg t) (Int.natCast_nonneg h)

-- w1_posg VERBATIM (against the carrier-generalized gaussW)
theorem w1_posg {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    0 ≤ w1 Φ₀ e h B ∨ w1 Φ₀ e h B = ⊤ := by
  left
  exact Finset.le_inf' _ _ fun t _ => w1_slot_nonneg e h _ t

end ProbeRepair

end LeanUrat.Scaffold.DictIII
