/- A0C scratch: prototype the §8 fixed-point extractor + §10 law conversion
   against landed lemmas only. -/
import Uniformity.ChapH.H97b
import Uniformity.ChapG.G46

noncomputable section

namespace A0CScratch

open Uniformity Uniformity.Density IsLocalRing Polynomial Filter Topology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- §8 prototype: solve `D ≥ b + q⁻⁵ D` in the limit, with an `M`-dependent base term
converging to `b` (the DBL steps carry a `decidedSeq O 2 σ' M` inside their base). -/
theorem density_ge_of_step {σ : FactorizationType} {bs : ℕ → ℝ} {b : ℝ}
    (hb : Tendsto bs atTop (𝓝 b))
    (hstep : ∀ M, bs M + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 σ M
      ≤ decidedSeq O 3 σ (M + 3)) :
    b * (residueCard O : ℝ) ^ 5 / ((residueCard O : ℝ) ^ 5 - 1)
      ≤ decidedDensity O 3 σ := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq5 : (1 : ℝ) < (residueCard O : ℝ) ^ 5 :=
    one_lt_pow₀ (by linarith) (by norm_num)
  -- limits of both sides of the step
  have hL : Tendsto (fun M => decidedSeq O 3 σ (M + 3)) atTop
      (𝓝 (decidedDensity O 3 σ)) :=
    (decidedSeq_tendsto (O := O) 3 σ).comp (tendsto_add_atTop_nat 3)
  have hR : Tendsto (fun M => bs M + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 σ M) atTop
      (𝓝 (b + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedDensity O 3 σ)) :=
    hb.add ((decidedSeq_tendsto (O := O) 3 σ).const_mul _)
  have hfix : b + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedDensity O 3 σ
      ≤ decidedDensity O 3 σ :=
    le_of_tendsto_of_tendsto' hR hL hstep
  -- algebra
  have hpos : (0 : ℝ) < (residueCard O : ℝ) ^ 5 := by linarith
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < (residueCard O : ℝ) ^ 5 - 1)]
  have h2 : (((residueCard O : ℝ) ^ 5)⁻¹ * decidedDensity O 3 σ) * (residueCard O : ℝ) ^ 5
      = decidedDensity O 3 σ := by field_simp
  have h3 := mul_le_mul_of_nonneg_right hfix hpos.le
  rw [add_mul, h2] at h3
  linarith

/-- §7 prototype: seq-level injection bound. -/
theorem seq_ge_of_inj {n N : ℕ} {σ : FactorizationType} {P : Type*} [Finite P]
    (F : P → ↥(decidedSet O n σ N)) (hF : Function.Injective F) :
    (Nat.card P : ℝ) / (residueCard O : ℝ) ^ (n * N) ≤ decidedSeq O n σ N := by
  have h : Nat.card P ≤ decidedCount O n σ N := Nat.card_le_card_of_injective F hF
  unfold decidedSeq
  gcongr
  -- `gcongr` discharges both side goals (positivity + the cast of `h` from context)

/-- §7 prototype: two injections with disjoint ranges + a subset, all counted. -/
theorem card_add_le_of_disjoint {α : Type*} [Finite α] {S A : Set α} (hA : A ⊆ S)
    {P : Type*} [Finite P] (f : P → α) (hf : Function.Injective f) (hfS : ∀ p, f p ∈ S)
    (hdisj : ∀ p, f p ∉ A) : Nat.card A + Nat.card P ≤ Nat.card S := by
  classical
  set F : A ⊕ P → S := Sum.elim (fun a => ⟨a.1, hA a.2⟩) (fun p => ⟨f p, hfS p⟩) with hF
  have hinj : Function.Injective F := by
    rintro (a | p) (a' | p') h
    · simp only [hF, Sum.elim_inl, Subtype.mk.injEq] at h
      exact congrArg Sum.inl (Subtype.ext h)
    · simp only [hF, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      exact absurd (h ▸ a.2) (hdisj p')
    · simp only [hF, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      exact absurd (h.symm ▸ a'.2) (hdisj p)
    · simp only [hF, Sum.elim_inr, Subtype.mk.injEq] at h
      exact congrArg Sum.inr (hf h)
  have hcard := Nat.card_le_card_of_injective F hinj
  rwa [Nat.card_sum] at hcard

/-- §7 prototype: the generic step arithmetic. `T` = total base-family count (ℝ),
`cPre` = loop-box count with its mixed-precision identity, `cN3` = the big decided count. -/
theorem step_arith (x : ℝ) (hx0 : 0 < x) (M : ℕ) (T cPre cM cN3 : ℝ)
    (hpre : cPre * x ^ (3 * M) = cM * x ^ (3 * M + 3))
    (hcount : T + x * cPre ≤ cN3) :
    T / x ^ (3 * (M + 3)) + (x ^ 5)⁻¹ * (cM / x ^ (3 * M)) ≤ cN3 / x ^ (3 * (M + 3)) := by
  have hxne : x ≠ 0 := hx0.ne'
  have hpre' : cPre = cM * x ^ 3 := by
    have h4 : cPre * x ^ (3 * M) = (cM * x ^ 3) * x ^ (3 * M) := by
      rw [hpre, ← pow_add]
      ring_nf
    exact mul_right_cancel₀ (pow_ne_zero _ hxne) h4
  rw [le_div_iff₀ (pow_pos hx0 _), add_mul]
  have e1 : T / x ^ (3 * (M + 3)) * x ^ (3 * (M + 3)) = T :=
    div_mul_cancel₀ _ (pow_ne_zero _ hxne)
  have e2 : ((x ^ 5)⁻¹ * (cM / x ^ (3 * M))) * x ^ (3 * (M + 3)) = cM * x ^ 4 := by
    rw [show 3 * (M + 3) = 3 * M + 9 from by omega, pow_add]
    field_simp
    ring
  rw [e1, e2]
  calc T + cM * x ^ 4 = T + x * cPre := by rw [hpre']; ring
    _ ≤ cN3 := hcount

/-- §7 prototype: off-diagonal pair census, subtraction-free. -/
theorem card_ne_pairs (K : Type*) [Finite K] [DecidableEq K] :
    Nat.card {p : K × K // p.1 ≠ p.2} + Nat.card K = Nat.card K ^ 2 := by
  classical
  have h1 : Nat.card {p : K × K // p.1 = p.2} = Nat.card K := by
    refine Nat.card_congr ⟨fun p => p.1.1, fun k => ⟨(k, k), rfl⟩, fun p => ?_, fun k => rfl⟩
    ext
    · rfl
    · exact p.2
  have h2 : Nat.card ({p : K × K // p.1 = p.2} ⊕ {p : K × K // p.1 ≠ p.2})
      = Nat.card (K × K) :=
    Nat.card_congr (Equiv.sumCompl (fun p : K × K => p.1 = p.2))
  rw [Nat.card_sum, h1, Nat.card_prod] at h2
  rw [← h2]
  ring

/-- §10 prototype (inert): the law conversion, from a sorry'd exact value. -/
theorem law_inert_proto
    (hval : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      genuineDensity O 3 c3inert
        = (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) + 1)
          / (3 * ((residueCard O : ℝ) ^ 4 + (residueCard O : ℝ) ^ 3
            + (residueCard O : ℝ) ^ 2 + (residueCard O : ℝ) + 1))) :
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O 3 c3inert
            = ((num.eval ((residueCard O : ℕ) : ℚ)
              / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
  refine ⟨Polynomial.X ^ 4 + Polynomial.X ^ 3,
    3 * (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1),
    ?_, ?_⟩
  · intro h
    have h0 := congrArg (Polynomial.eval (0 : ℚ)) h
    simp at h0
  · intro O _ _ _ _ _
    have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by
      exact_mod_cast two_le_residueCard O
    have hden : (3 * (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2
        + Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
        = 3 * (((residueCard O : ℕ) : ℚ) ^ 4 + ((residueCard O : ℕ) : ℚ) ^ 3
          + ((residueCard O : ℕ) : ℚ) ^ 2 + ((residueCard O : ℕ) : ℚ) + 1) := by
      simp
    have hnum : (Polynomial.X ^ 4 + Polynomial.X ^ 3 : Polynomial ℚ).eval
        ((residueCard O : ℕ) : ℚ)
        = ((residueCard O : ℕ) : ℚ) ^ 4 + ((residueCard O : ℕ) : ℚ) ^ 3 := by
      simp
    have hdenpos : (0 : ℚ) < ((residueCard O : ℕ) : ℚ) ^ 4 + ((residueCard O : ℕ) : ℚ) ^ 3
        + ((residueCard O : ℕ) : ℚ) ^ 2 + ((residueCard O : ℕ) : ℚ) + 1 := by nlinarith
    refine ⟨by rw [hden]; positivity, ?_⟩
    rw [hval O, hden, hnum]
    push_cast
    have hqR : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast two_le_residueCard O
    have hd : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) ^ 4 + ((residueCard O : ℕ) : ℝ) ^ 3
        + ((residueCard O : ℕ) : ℝ) ^ 2 + ((residueCard O : ℕ) : ℝ) + 1 := by nlinarith
    rw [div_eq_div_iff (by nlinarith) (by nlinarith)]
    ring

end A0CScratch
