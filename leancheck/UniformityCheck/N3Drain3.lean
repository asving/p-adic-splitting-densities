/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Recur

/-!
# UniformityCheck.N3Drain3 — the triple-root count, and UNCONDITIONAL `n = 3` drainage

Unit `UNIFORMITY-CHECK-N3C`, layer 4 (`notes/N3_CHECK_2026-08-13.md` §13.4). `N3Recur.lean`'s step
lemma says every undecided triple-root class at level `M + 3` is a legal `X = πY` extraction of an
undecided class at level `M`. This file counts that correspondence and takes the limit.

* `card_undecidedTriple_le` — `#(undecided ∩ triple at M+3) ≤ q⁷ · undecidedCount M`, from the
  injection `c ↦ (γ̄, level-(M+2) class of the extraction)`;
* `tripleUndecidedSeq_le_shift` — the recursion `tripleUndecidedSeq (M+3) ≤ q^(-2)·undecidedSeq M`;
* **`undecidedSeq_three_tendsto_zero`**, **`drainage_three`**,
  **`genuineDensity_three_eq_decidedDensity`** — the payoff: the `n = 3` ambiguity gap drains and
  THE density equals the certified one, unconditionally, for every splitting type;
* `tripleUndecidedSeq_tendsto_zero` — the hypothesis of `N3Drain.drainage_three_of_triple`,
  discharged, so that reduction now fires too (`drainage_three_via_reduction`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial Filter Topology

/-! ## 4. The count and the recursion -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **THE COUNT (§13.4).** `#(undecided ∩ triple at level M+3) ≤ q⁷ · undecidedCount M`. The map
`c ↦ (γ̄, level-(M+2) class of the extraction)` is injective: `γ̄` fixes the recentring point
through `resSect`, and `π^(M+2) ∣ d' i - d i` gives `π^(M+3) ∣ B' i - B i` for every `i`, which
un-recentres to `π^(M+3) ∣ a' i - a i`. -/
theorem card_undecidedTriple_le {π : O} (hπ : Irreducible π) (M : ℕ) :
    Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
        Set (Coeff O 3 (M + 3)))
      ≤ residueCard O ^ 7 * undecidedCount O 3 M := by
  classical
  simp only [undecidedCount]
  have hM2 : M ≤ M + 2 := by omega
  -- (a) every undecided triple-root class at level `M + 3` records a residue, a lift, and an
  -- extraction whose level-`M` class is undecided
  have key : ∀ c : (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
      Set (Coeff O 3 (M + 3))),
      ∃ p : ResidueField O × (Fin 3 → O) × (Fin 3 → O),
        proj O 3 (M + 3) p.2.1 = (c : Coeff O 3 (M + 3)) ∧
        shiftVec p.2.1 (resSect O p.1) 0 = π ^ 3 * p.2.2 0 ∧
        shiftVec p.2.1 (resSect O p.1) 1 = π ^ 2 * p.2.2 1 ∧
        shiftVec p.2.1 (resSect O p.1) 2 = π * p.2.2 2 ∧
        UndecidedAt O 3 M (proj O 3 M p.2.2) := by
    rintro ⟨c, hcu, a, γ, ha, hγ⟩
    have hres : resVec a = cubeCoeff (residue O (resSect O (residue O γ))) := by
      rw [residue_resSect]; exact hγ
    have hmem : ∀ i, shiftVec a (resSect O (residue O γ)) i ∈ maximalIdeal O :=
      (shiftVec_mem_iff a (resSect O (residue O γ))).2 hres
    obtain ⟨d, e0, e1, e2, hd⟩ := undecided_triple_step hπ hmem (by rw [ha]; exact hcu)
    exact ⟨(residue O γ, a, d), ha, e0, e1, e2, hd⟩
  choose f hf1 hf2 hf3 hf4 hf5 using key
  -- (c) the extraction's level-`(M+2)` class lands in the preimage of the undecided set
  have hmemS : ∀ c, proj O 3 (M + 2) (f c).2.2
      ∈ (coeffFactor (O := O) 3 hM2) ⁻¹' (undecidedSet O 3 M) := by
    intro c
    show coeffFactor (O := O) 3 hM2 (proj O 3 (M + 2) (f c).2.2) ∈ undecidedSet O 3 M
    rw [coeffFactor_proj]
    exact hf5 c
  -- (d) the injection `c ↦ (γ̄, level-(M+2) class of the extraction)`
  have hinj : Function.Injective
      (fun c : (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
          Set (Coeff O 3 (M + 3))) =>
        (((f c).1, (⟨proj O 3 (M + 2) (f c).2.2, hmemS c⟩ :
            ((coeffFactor (O := O) 3 hM2) ⁻¹' (undecidedSet O 3 M) :
              Set (Coeff O 3 (M + 2))))) :
          ResidueField O × ((coeffFactor (O := O) 3 hM2) ⁻¹' (undecidedSet O 3 M) :
            Set (Coeff O 3 (M + 2))))) := by
    intro c c' hcc
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcc
    obtain ⟨e1, e2⟩ := hcc
    have hγ' : resSect O (f c').1 = resSect O (f c).1 := by rw [e1]
    have hd : ∀ i, π ^ (M + 2) ∣ ((f c').2.2 i - (f c).2.2 i) :=
      (proj_eq_iff_dvd hπ _ _).1 e2
    -- multiply the three coordinates back up: the slack is `+2`, `+1`, `0`
    have k0 : shiftVec (f c').2.1 (resSect O (f c).1) 0 = π ^ 3 * (f c').2.2 0 := by
      rw [← hγ']; exact hf2 c'
    have k1 : shiftVec (f c').2.1 (resSect O (f c).1) 1 = π ^ 2 * (f c').2.2 1 := by
      rw [← hγ']; exact hf3 c'
    have k2 : shiftVec (f c').2.1 (resSect O (f c).1) 2 = π * (f c').2.2 2 := by
      rw [← hγ']; exact hf4 c'
    have hB0 : π ^ (M + 3) ∣ (shiftVec (f c').2.1 (resSect O (f c).1) 0
        - shiftVec (f c).2.1 (resSect O (f c).1) 0) := by
      rw [k0, hf2 c]
      obtain ⟨t, ht⟩ := hd 0
      exact ⟨π ^ 2 * t, by rw [← mul_sub, ht]; ring⟩
    have hB1 : π ^ (M + 3) ∣ (shiftVec (f c').2.1 (resSect O (f c).1) 1
        - shiftVec (f c).2.1 (resSect O (f c).1) 1) := by
      rw [k1, hf3 c]
      obtain ⟨t, ht⟩ := hd 1
      exact ⟨π * t, by rw [← mul_sub, ht]; ring⟩
    have hB2 : π ^ (M + 3) ∣ (shiftVec (f c').2.1 (resSect O (f c).1) 2
        - shiftVec (f c).2.1 (resSect O (f c).1) 2) := by
      rw [k2, hf4 c]
      obtain ⟨t, ht⟩ := hd 2
      exact ⟨t, by rw [← mul_sub, ht]; ring⟩
    have hB : ∀ i, π ^ (M + 3) ∣ (shiftVec (f c').2.1 (resSect O (f c).1) i
        - shiftVec (f c).2.1 (resSect O (f c).1) i) := by
      intro i
      fin_cases i
      · exact hB0
      · exact hB1
      · exact hB2
    -- un-recentre
    have hun := dvd_shiftVec_sub (π := π) (N := M + 3) (-(resSect O (f c).1)) hB
    simp only [shiftVec_shiftVec_neg] at hun
    have hfin : proj O 3 (M + 3) (f c).2.1 = proj O 3 (M + 3) (f c').2.1 :=
      (proj_eq_iff_dvd hπ _ _).2 hun
    rw [hf1 c, hf1 c'] at hfin
    exact Subtype.ext hfin
  -- (e) the count
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hle
  have hcp := card_preimage_coeffFactor (O := O) 3 hM2 (undecidedSet O 3 M)
  rw [card_coeff, card_coeff, show 3 * (M + 2) = 3 * M + 6 from by ring] at hcp
  have hScard : Nat.card ((coeffFactor (O := O) 3 hM2) ⁻¹' (undecidedSet O 3 M) :
      Set (Coeff O 3 (M + 2)))
      = Nat.card (undecidedSet O 3 M) * residueCard O ^ 6 := by
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) (3 * M)) ?_
    rw [hcp]
    ring
  rw [hScard] at hle
  have hres : Nat.card (ResidueField O) = residueCard O := rfl
  rw [hres] at hle
  calc Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
        Set (Coeff O 3 (M + 3)))
      ≤ residueCard O * (Nat.card (undecidedSet O 3 M) * residueCard O ^ 6) := hle
    _ = residueCard O ^ 7 * Nat.card (undecidedSet O 3 M) := by ring

/-- **THE RECURSION.** `tripleUndecidedSeq (M+3) ≤ q^(-2) · undecidedSeq M` — §9.4's recursion
`u(N) ≤ q^(-N/2) + q^(-5)·u(N-3)` with the second constant at the rung `q^(-2)` (§13.4). -/
theorem tripleUndecidedSeq_le_shift (M : ℕ) :
    tripleUndecidedSeq (O := O) (M + 3)
      ≤ (1 / (residueCard O : ℝ) ^ 2) * undecidedSeq O 3 M := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : (residueCard O : ℝ) ≠ 0 := ne_of_gt qR_pos
  have hcast : (Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
      Set (Coeff O 3 (M + 3))) : ℝ)
      ≤ (residueCard O : ℝ) ^ 7 * (undecidedCount O 3 M : ℝ) := by
    exact_mod_cast card_undecidedTriple_le (O := O) hπ M
  calc tripleUndecidedSeq (O := O) (M + 3)
      = (Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
            Set (Coeff O 3 (M + 3))) : ℝ)
          / ((residueCard O : ℝ) ^ (3 * M) * (residueCard O : ℝ) ^ 9) := by
        rw [tripleUndecidedSeq, show 3 * (M + 3) = 3 * M + 9 from by ring, pow_add]
    _ ≤ ((residueCard O : ℝ) ^ 7 * (undecidedCount O 3 M : ℝ))
          / ((residueCard O : ℝ) ^ (3 * M) * (residueCard O : ℝ) ^ 9) := by
        gcongr
    _ = (1 / (residueCard O : ℝ) ^ 2) * undecidedSeq O 3 M := by
        rw [undecidedSeq]
        field_simp

end Count

/-! ## 5. Drainage at `n = 3`, unconditional -/

section Drain

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- The recursion in the form the limit argument consumes: for `M ≥ 2`,
`s(2M) ≤ q^(-M) + q^(-2)·s(2M-3)`. -/
theorem undecidedSeq_three_step {M : ℕ} (hM : 2 ≤ M) :
    undecidedSeq O 3 (2 * M)
      ≤ (1 / (residueCard O : ℝ)) ^ M
        + (1 / (residueCard O : ℝ) ^ 2) * undecidedSeq O 3 (2 * M - 3) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h1 := UniformityCheck.undecidedSeq_three_le (O := O) hπ (M := M) (by omega)
  have h2 := tripleUndecidedSeq_le_shift (O := O) (2 * M - 3)
  rw [show 2 * M - 3 + 3 = 2 * M from by omega] at h2
  linarith

/-- **THE `n = 3` UNDECIDED MASS DRAINS.** Unconditional, general complete DVR with finite residue
field. The limit `S = ⨅ N, undecidedSeq O 3 N` exists because `undecidedSeq` is antitone and
nonnegative; the recursion gives `S ≤ q^(-2)·S` with `q^(-2) ≤ 1/4`, so `S = 0`. -/
theorem undecidedSeq_three_tendsto_zero :
    Tendsto (fun N => undecidedSeq O 3 N) atTop (𝓝 0) := by
  have hanti := UniformityCheck.undecidedSeq_antitone (O := O) 3
  have hbdd : BddBelow (Set.range (undecidedSeq O 3)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨N, rfl⟩
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (qpow_pos _))
  have hlim : Tendsto (undecidedSeq O 3) atTop (𝓝 (⨅ N, undecidedSeq O 3 N)) :=
    tendsto_atTop_ciInf hanti hbdd
  have h2M3 : Tendsto (fun M : ℕ => 2 * M - 3) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b + 2, fun a ha => by omega⟩)
  have hA : Tendsto (fun M : ℕ => undecidedSeq O 3 (2 * M)) atTop
      (𝓝 (⨅ N, undecidedSeq O 3 N)) := hlim.comp tendsto_two_mul_atTop
  have hB : Tendsto (fun M : ℕ => undecidedSeq O 3 (2 * M - 3)) atTop
      (𝓝 (⨅ N, undecidedSeq O 3 N)) := hlim.comp h2M3
  have hgeom : Tendsto (fun M : ℕ => (1 / (residueCard O : ℝ)) ^ M) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [div_lt_one qR_pos]
    exact_mod_cast one_lt_residueCard O
  have hrhs : Tendsto (fun M : ℕ => (1 / (residueCard O : ℝ)) ^ M
      + (1 / (residueCard O : ℝ) ^ 2) * undecidedSeq O 3 (2 * M - 3)) atTop
      (𝓝 (0 + (1 / (residueCard O : ℝ) ^ 2) * (⨅ N, undecidedSeq O 3 N))) :=
    hgeom.add (hB.const_mul (1 / (residueCard O : ℝ) ^ 2))
  have hbd : (fun M : ℕ => undecidedSeq O 3 (2 * M)) ≤ᶠ[atTop]
      (fun M : ℕ => (1 / (residueCard O : ℝ)) ^ M
        + (1 / (residueCard O : ℝ) ^ 2) * undecidedSeq O 3 (2 * M - 3)) := by
    filter_upwards [eventually_ge_atTop 2] with M hM
    exact undecidedSeq_three_step hM
  have hkey := le_of_tendsto_of_tendsto hA hrhs hbd
  have hSnn : (0 : ℝ) ≤ ⨅ N, undecidedSeq O 3 N :=
    le_ciInf (fun N => div_nonneg (Nat.cast_nonneg _) (le_of_lt (qpow_pos _)))
  have h2q : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq2 : (1 / (residueCard O : ℝ) ^ 2) ≤ 1 / 4 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    nlinarith
  have hSzero : (⨅ N, undecidedSeq O 3 N) = (0 : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_right hq2 hSnn
    linarith
  rw [hSzero] at hlim
  exact hlim

/-- **DRAINAGE AT `n = 3`, UNCONDITIONAL.** For every complete DVR `O` with finite residue field
and every splitting type `σ`, the level-`N` ambiguity gap of monic cubics drains to `0`. The
`n = 3` analogue of `drainage_two`, and the discharge of `N3Drain.drainage_three_of_triple`'s
hypothesis. -/
theorem drainage_three (σ : FactorizationType) : UndecidedVanishes O 3 σ :=
  drainage_of_undecided_comp (φ := id) tendsto_id undecidedSeq_three_tendsto_zero σ

/-- **THE `n = 3` TIE.** THE density equals the certified one, for every type: the `1/q²` slack of
`genuineDensity_three_le` is gone. -/
theorem genuineDensity_three_eq_decidedDensity (σ : FactorizationType) :
    genuineDensity O 3 σ = decidedDensity O 3 σ :=
  genuineDensity_eq_of_drainage (drainage_three σ)

/-- The triple-root undecided mass drains — the hypothesis of `drainage_three_of_triple`,
discharged. -/
theorem tripleUndecidedSeq_tendsto_zero :
    Tendsto (fun M : ℕ => tripleUndecidedSeq (O := O) (2 * M)) atTop (𝓝 0) := by
  have h2M3 : Tendsto (fun M : ℕ => 2 * M - 3) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b + 2, fun a ha => by omega⟩)
  have hsub : Tendsto (fun M : ℕ => undecidedSeq O 3 (2 * M - 3)) atTop (𝓝 0) :=
    (undecidedSeq_three_tendsto_zero (O := O)).comp h2M3
  have hlim : Tendsto (fun M : ℕ =>
      (1 / (residueCard O : ℝ) ^ 2) * undecidedSeq O 3 (2 * M - 3)) atTop (𝓝 0) := by
    have h := hsub.const_mul (1 / (residueCard O : ℝ) ^ 2)
    rwa [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall (fun M => ?_)) ?_ hlim
  · rw [tripleUndecidedSeq]
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (qpow_pos _))
  · filter_upwards [eventually_ge_atTop 2] with M hM
    have h := tripleUndecidedSeq_le_shift (O := O) (2 * M - 3)
    rwa [show 2 * M - 3 + 3 = 2 * M from by omega] at h

/-- `drainage_three_of_triple` fires: the reduction of `N3Drain.lean` is now unconditional. (Same
conclusion as `drainage_three`, reached through the landed reduction rather than around it.) -/
theorem drainage_three_via_reduction (σ : FactorizationType) : UndecidedVanishes O 3 σ :=
  drainage_three_of_triple tripleUndecidedSeq_tendsto_zero σ

end Drain

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.card_undecidedTriple_le
#print axioms UniformityCheck.tripleUndecidedSeq_le_shift
#print axioms UniformityCheck.undecidedSeq_three_step
#print axioms UniformityCheck.undecidedSeq_three_tendsto_zero
#print axioms UniformityCheck.drainage_three
#print axioms UniformityCheck.genuineDensity_three_eq_decidedDensity
#print axioms UniformityCheck.tripleUndecidedSeq_tendsto_zero
#print axioms UniformityCheck.drainage_three_via_reduction

end AxCheck

end UniformityCheck
