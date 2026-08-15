/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3CertRam
import UniformityCheck.N3CertLinRam
import UniformityCheck.N3Drain

/-!
# UniformityCheck.N3Recur — the triple-root recursion, and UNCONDITIONAL `n = 3` drainage

Unit `UNIFORMITY-CHECK-N3C`, layer 3 (`notes/N3_CHECK_2026-08-13.md` §§13.3–13.4). `N3Drain.lean`
reduced `n = 3` drainage to the triple-root stratum (`drainage_three_of_triple`); this file
discharges that stratum.

**The step (§13.3, HYP.08).** For a class that is undecided at level `M + 3` and residually a
perfect cube, recentre at a lift `γ` of the residual centre. Cases **E** (`v(B₀) = 1`), **L**
(`v(B₁) = 1`, `v(B₀) ≥ 2`) and **R** (`v(B₀) = 2`, `v(B₁) ≥ 2`) each DECIDE the class — every
condition is readable mod `π³`, so the certificate applies to every lift — so the surviving case
is **S**: `π³ ∣ B₀`, `π² ∣ B₁`, `π ∣ B₂`. Then the extraction `d = (B₀/π³, B₁/π², B₂/π)` has the
same type (`typeOf_scale`, unit P5) and its level-`M` class is undecided again.

**The recursion (§13.4).** Recording `(γ̄, level-(M+2) class of d)` is injective, so

    tripleUndecidedSeq (M + 3)  ≤  q^(-2) · undecidedSeq M .

With the landed branch-(b) bound `undecidedSeq (2M) ≤ q^(-M) + tripleUndecidedSeq (2M)` and the
antitonicity of `undecidedSeq`, the limit `S = ⨅ N, undecidedSeq O 3 N` satisfies
`S ≤ q^(-2)·S`, hence `S = 0`:

* `undecidedSeq_three_tendsto_zero` — the whole undecided proportion drains;
* **`drainage_three`** — `UndecidedVanishes O 3 σ` for every `σ`, UNCONDITIONALLY, general `O`;
* **`genuineDensity_three_eq_decidedDensity`** — the `n = 3` bracket CLOSES;
* `tripleUndecidedSeq_tendsto_zero` — the hypothesis of `drainage_three_of_triple`, now
  discharged (that theorem is kept as a second, redundant route).

The constant is `q^(-2)`, not §9.4's sharp `q^(-5)`: recording `d` at the uniform precision `M + 2`
(rather than at its natural mixed precision `(M, M+1, M+2)`) throws away three digits. Drainage
needs only a constant `< 1`; the sharp count lives in `N3Tie.lean`, where an exact value needs it.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial Filter Topology

/-! ## 0. Divisibility transfer along a congruence

Every case certificate below is a `π`-divisibility statement about the recentred vector `B`, and
must be transported to an arbitrary lift `b ≡ B (mod π ^ 3)`. Both directions of that transport
are the same one-line identity `x = (x - y) + y`. -/

section Transfer

/-- If `x ≡ y` modulo a multiple `c` of `p`, then `p ∣ y` transfers to `p ∣ x`. -/
private theorem dvd_of_dvd_sub_left {R : Type*} [CommRing R] {p c x y : R} (hpc : p ∣ c)
    (hs : c ∣ (x - y)) (hy : p ∣ y) : p ∣ x := by
  have h1 : p ∣ x - y := hpc.trans hs
  have h2 : p ∣ (x - y) + y := dvd_add h1 hy
  have h3 : (x - y) + y = x := by ring
  rwa [h3] at h2

/-- The contrapositive transfer: `¬ p ∣ y` transfers to `¬ p ∣ x`. -/
private theorem not_dvd_of_dvd_sub_left {R : Type*} [CommRing R] {p c x y : R} (hpc : p ∣ c)
    (hs : c ∣ (x - y)) (hy : ¬ p ∣ y) : ¬ p ∣ x := fun hx =>
  hy (dvd_of_dvd_sub_left hpc (dvd_sub_comm.1 hs) hx)

end Transfer

/-! ## 1. `undecidedSeq` is antitone -/

section Antitone

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Refining an undecided class keeps it undecided — contrapositive of
`preimage_decidedSet_subset`. -/
theorem undecidedSet_subset_preimage {n : ℕ} {N M : ℕ} (h : N ≤ M) :
    undecidedSet O n M ⊆ (coeffFactor (O := O) n h) ⁻¹' (undecidedSet O n N) := by
  intro c hc σ hσ
  exact hc σ (preimage_decidedSet_subset (O := O) h hσ)

/-- **The undecided proportion is antitone in the level.** (The `n = 2` file proves the antitone
statement only for `gapSeq`; this is the `undecidedSeq` form, at every `n`.) -/
theorem undecidedSeq_antitone (n : ℕ) : Antitone (undecidedSeq O n) := by
  intro N M h
  have hcount := card_preimage_coeffFactor (O := O) n h (undecidedSet O n N)
  have hsub : undecidedCount O n M
      ≤ Nat.card ((coeffFactor (O := O) n h) ⁻¹' (undecidedSet O n N)) :=
    Nat.card_le_card_of_injective (Set.inclusion (undecidedSet_subset_preimage (O := O) h))
      (Set.inclusion_injective _)
  rw [card_coeff, card_coeff] at hcount
  have hkey : undecidedCount O n M * residueCard O ^ (n * N)
      ≤ undecidedCount O n N * residueCard O ^ (n * M) := by
    calc undecidedCount O n M * residueCard O ^ (n * N)
        ≤ Nat.card ((coeffFactor (O := O) n h) ⁻¹' (undecidedSet O n N))
            * residueCard O ^ (n * N) := Nat.mul_le_mul_right _ hsub
      _ = undecidedCount O n N * residueCard O ^ (n * M) := hcount
  simp only [undecidedSeq]
  rw [div_le_div_iff₀ (qpow_pos (O := O) (n * M)) (qpow_pos (O := O) (n * N))]
  have h2 : ((undecidedCount O n M * residueCard O ^ (n * N) : ℕ) : ℝ)
      ≤ ((undecidedCount O n N * residueCard O ^ (n * M) : ℕ) : ℝ) := Nat.cast_le.2 hkey
  push_cast at h2
  linarith

end Antitone

/-! ## 2. A section of the residue map -/

section Sect

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A chosen lift `O/𝔪 → O` of the residue map: the recursion must recentre at a lift of the
residual triple root that depends only on its residue, so that the level-`(M+3)` class can be
reconstructed from `(γ̄, extraction)`. -/
noncomputable def resSect : ResidueField O → O :=
  Function.surjInv IsLocalRing.residue_surjective

theorem residue_resSect (x : ResidueField O) : residue O (resSect O x) = x :=
  Function.surjInv_eq _ x

end Sect

/-! ## 3. The step: cases E/L/R decide, case S descends -/

section Step

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The certificate wrapper.** A type verdict that only reads the recentred vector mod `π ^ 3`
decides the level-`(M+3)` class: every lift `a'` recentres to `b' ≡ b (mod π^(M+3))`, hence mod
`π³`, and `typeOf (monicPoly a') = typeOf (monicPoly b')` by shift invariance. -/
theorem decidedAt_of_shift_cert {π : O} (hπ : Irreducible π) {M : ℕ} {a : Fin 3 → O} {γ : O}
    {σ : FactorizationType}
    (hcert : ∀ b : Fin 3 → O, (∀ i, π ^ 3 ∣ (b i - shiftVec a γ i)) →
      typeOf (monicPoly b) = σ) :
    DecidedAt O 3 σ (M + 3) (proj O 3 (M + 3) a) := by
  refine decidedAt_of_congr hπ (fun a' ha' => ?_)
  have hb : ∀ i, π ^ (M + 3) ∣ (shiftVec a' γ i - shiftVec a γ i) := dvd_shiftVec_sub γ ha'
  have hb3 : ∀ i, π ^ 3 ∣ (shiftVec a' γ i - shiftVec a γ i) := fun i =>
    (pow_dvd_pow π (by omega)).trans (hb i)
  rw [← typeOf_shiftVec a' γ]
  exact hcert _ hb3

/-- **CASE S is forced.** An undecided level-`(M+3)` class that is residually a perfect cube has a
legal `X = πY` extraction: cases E, L and R would each have decided it. -/
theorem legal_of_undecided_triple {π : O} (hπ : Irreducible π) {M : ℕ} {a : Fin 3 → O} {γ : O}
    (hγ : ∀ i, shiftVec a γ i ∈ maximalIdeal O)
    (hu : UndecidedAt O 3 (M + 3) (proj O 3 (M + 3) a)) :
    π ^ 3 ∣ shiftVec a γ 0 ∧ π ^ 2 ∣ shiftVec a γ 1 ∧ π ∣ shiftVec a γ 2 := by
  -- every recentred coefficient is divisible by `π` (that is the triple-root hypothesis)
  have hd : ∀ i, π ∣ shiftVec a γ i := by
    intro i
    have h1 : shiftVec a γ i ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hγ i
    have h2 := (mem_maximalIdeal_pow_iff_dvd hπ 1 (shiftVec a γ i)).1 h1
    rwa [pow_one] at h2
  have hπ1 : π ∣ π ^ 3 := dvd_pow_self π (by omega)
  have hπ2 : π ^ 2 ∣ π ^ 3 := pow_dvd_pow π (by omega)
  have hπ3 : π ^ 3 ∣ π ^ 3 := dvd_rfl
  by_cases hE : π ^ 2 ∣ shiftVec a γ 0
  · by_cases hL : π ^ 2 ∣ shiftVec a γ 1
    · by_cases hR : π ^ 3 ∣ shiftVec a γ 0
      · -- CASE S: the extraction is legal
        exact ⟨hR, hL, hd 2⟩
      · -- CASE R: `v(B₀) = 2`, `v(B₁) ≥ 2` decides `c3ram`
        exact absurd (decidedAt_of_shift_cert (M := M) hπ (fun b hb =>
          typeOf_ram3_of_val_two hπ (dvd_of_dvd_sub_left hπ1 (hb 2) (hd 2))
            (dvd_of_dvd_sub_left hπ2 (hb 1) hL) (dvd_of_dvd_sub_left hπ2 (hb 0) hE)
            (not_dvd_of_dvd_sub_left hπ3 (hb 0) hR))) (hu _)
    · -- CASE L: `v(B₁) = 1`, `v(B₀) ≥ 2` decides `c3linRam`
      exact absurd (decidedAt_of_shift_cert (M := M) hπ (fun b hb =>
        typeOf_linRam_of_val_one hπ (dvd_of_dvd_sub_left hπ1 (hb 2) (hd 2))
          (dvd_of_dvd_sub_left hπ1 (hb 1) (hd 1))
          (not_dvd_of_dvd_sub_left hπ2 (hb 1) hL)
          (dvd_of_dvd_sub_left hπ2 (hb 0) hE))) (hu _)
  · -- CASE E: `v(B₀) = 1` is Eisenstein, deciding `c3ram`
    exact absurd (decidedAt_of_shift_cert (M := M) hπ (fun b hb =>
      typeOf_ram3_of_val_one hπ (dvd_of_dvd_sub_left hπ1 (hb 0) (hd 0))
        (not_dvd_of_dvd_sub_left hπ2 (hb 0) hE)
        (dvd_of_dvd_sub_left hπ1 (hb 1) (hd 1))
        (dvd_of_dvd_sub_left hπ1 (hb 2) (hd 2)))) (hu _)

/-- **The extraction preserves the type** (`typeOf_scale` at `m = 1`): the coefficient identity is
`(monicPoly b)(πX) = π³·(monicPoly d)(X)`. -/
theorem typeOf_extract {π : O} (hπ : Irreducible π) {b d : Fin 3 → O}
    (e0 : b 0 = π ^ 3 * d 0) (e1 : b 1 = π ^ 2 * d 1) (e2 : b 2 = π * d 2) :
    typeOf (monicPoly b) = typeOf (monicPoly d) := by
  refine typeOf_cubic_scale hπ 1 ?_
  rw [cubic_expand b, cubic_expand d, e0, e1, e2]
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_mul, map_pow, pow_one]
  ring

/-- **The descent.** With the extraction legal, undecidedness at level `M + 3` forces
undecidedness of the extracted class at level `M`. This is the level bookkeeping HYP.08: the
extraction determines `d` to precisions `(M, M+1, M+2)`, and the WEAKEST of the three is the level
that must be quoted. -/
theorem undecided_of_extract {π : O} (hπ : Irreducible π) {M : ℕ} {a : Fin 3 → O} {γ : O}
    {d : Fin 3 → O}
    (e0 : shiftVec a γ 0 = π ^ 3 * d 0) (e1 : shiftVec a γ 1 = π ^ 2 * d 1)
    (e2 : shiftVec a γ 2 = π * d 2)
    (hu : UndecidedAt O 3 (M + 3) (proj O 3 (M + 3) a)) :
    UndecidedAt O 3 M (proj O 3 M d) := by
  intro σ hdec
  refine hu σ ?_
  refine decidedAt_of_congr hπ (fun a' ha' => ?_)
  have hb : ∀ i, π ^ (M + 3) ∣ (shiftVec a' γ i - shiftVec a γ i) := dvd_shiftVec_sub γ ha'
  -- the recentred lift is divisible to the same three depths, so it too has an extraction
  have k0 : π ^ 3 ∣ shiftVec a' γ 0 :=
    dvd_of_dvd_sub_left (pow_dvd_pow π (by omega)) (hb 0) ⟨d 0, e0⟩
  have k1 : π ^ 2 ∣ shiftVec a' γ 1 :=
    dvd_of_dvd_sub_left (pow_dvd_pow π (by omega)) (hb 1) ⟨d 1, e1⟩
  have k2 : π ∣ shiftVec a' γ 2 := dvd_of_dvd_sub_left (dvd_pow_self π (by omega)) (hb 2) ⟨d 2, e2⟩
  obtain ⟨x, hx⟩ := k0
  obtain ⟨y, hy⟩ := k1
  obtain ⟨z, hz⟩ := k2
  -- cancel the extracted powers of `π` from the congruence: precisions `M`, `M+1`, `M+2`
  have c0 : π ^ M ∣ (x - d 0) := by
    obtain ⟨c, hc⟩ := hb 0
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 3 hπ.ne_zero) ?_⟩
    calc π ^ 3 * (x - d 0) = shiftVec a' γ 0 - shiftVec a γ 0 := by rw [hx, e0]; ring
      _ = π ^ (M + 3) * c := hc
      _ = π ^ 3 * (π ^ M * c) := by ring
  have c1 : π ^ (M + 1) ∣ (y - d 1) := by
    obtain ⟨c, hc⟩ := hb 1
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) ?_⟩
    calc π ^ 2 * (y - d 1) = shiftVec a' γ 1 - shiftVec a γ 1 := by rw [hy, e1]; ring
      _ = π ^ (M + 3) * c := hc
      _ = π ^ 2 * (π ^ (M + 1) * c) := by ring
  have c2 : π ^ (M + 2) ∣ (z - d 2) := by
    obtain ⟨c, hc⟩ := hb 2
    refine ⟨c, mul_left_cancel₀ hπ.ne_zero ?_⟩
    calc π * (z - d 2) = shiftVec a' γ 2 - shiftVec a γ 2 := by rw [hz, e2]; ring
      _ = π ^ (M + 3) * c := hc
      _ = π * (π ^ (M + 2) * c) := by ring
  -- so the extraction of `a'` sits in the same level-`M` class as `d`
  have hall : ∀ i, π ^ M ∣ ((![x, y, z] : Fin 3 → O) i - d i) := by
    intro i
    fin_cases i
    · exact c0
    · exact (pow_dvd_pow π (by omega)).trans c1
    · exact (pow_dvd_pow π (by omega)).trans c2
  have hproj : proj O 3 M (![x, y, z] : Fin 3 → O) = proj O 3 M d :=
    ((proj_eq_iff_dvd hπ d (![x, y, z] : Fin 3 → O)).2 hall).symm
  rw [← typeOf_shiftVec a' γ, typeOf_extract hπ (d := (![x, y, z] : Fin 3 → O)) hx hy hz]
  exact hdec _ hproj

/-- **THE STEP (§13.3).** Every undecided triple-root class at level `M + 3` is a legal
extraction of an undecided class at level `M`. -/
theorem undecided_triple_step {π : O} (hπ : Irreducible π) {M : ℕ} {a : Fin 3 → O} {γ : O}
    (hγ : ∀ i, shiftVec a γ i ∈ maximalIdeal O)
    (hu : UndecidedAt O 3 (M + 3) (proj O 3 (M + 3) a)) :
    ∃ d : Fin 3 → O, shiftVec a γ 0 = π ^ 3 * d 0 ∧ shiftVec a γ 1 = π ^ 2 * d 1 ∧
      shiftVec a γ 2 = π * d 2 ∧ UndecidedAt O 3 M (proj O 3 M d) := by
  obtain ⟨⟨d0, h0⟩, ⟨d1, h1⟩, ⟨d2, h2⟩⟩ := legal_of_undecided_triple hπ hγ hu
  refine ⟨![d0, d1, d2], h0, h1, h2, ?_⟩
  exact undecided_of_extract hπ h0 h1 h2 hu

end Step

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.undecidedSet_subset_preimage
#print axioms UniformityCheck.undecidedSeq_antitone
#print axioms UniformityCheck.residue_resSect
#print axioms UniformityCheck.decidedAt_of_shift_cert
#print axioms UniformityCheck.legal_of_undecided_triple
#print axioms UniformityCheck.typeOf_extract
#print axioms UniformityCheck.undecided_of_extract
#print axioms UniformityCheck.undecided_triple_step

end AxCheck

end UniformityCheck
