/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Recur

/-!
# UniformityCheck.N3MBox — the mixed-precision box of the triple-root extraction

Unit `UNIFORMITY-CHECK-N3C`, layer 6 (`notes/N3_CHECK_2026-08-13.md` §13.5). `N3Drain3.lean` gets
drainage from the CRUDE count (record the extraction `d` at the uniform precision `M + 2`, constant
`q^(-2)`). An EXACT density needs the SHARP count, and for that the asymmetry of the extraction has
to be respected: `B₀ = π³d₀`, `B₁ = π²d₁`, `B₂ = πd₂` determines

    d₀ mod π^M ,   d₁ mod π^(M+1) ,   d₂ mod π^(M+2)

from `B mod π^(M+3)` — and nothing more. This file introduces that mixed box,

    MBox O M = Res O M × Res O (M+1) × Res O (M+2) ,

its truncation `mtrunc M : MBox O M →+ Coeff O 3 M` (`d ↦ d mod π^M`, a surjective additive
homomorphism, so its fibres all have the same size and `card_preimage_mtrunc` transports
proportions), and the reconstruction map

    boxClass π M : ResidueField O × MBox O M → Coeff O 3 (M+3) ,

which is INJECTIVE (`boxClass_injective`) with image exactly the case-S triple-root classes. The
sharp fibre size is `#(MBox O M) / #(Coeff O 3 M) = q³`, versus `q⁶` for the uniform-precision
record: those three digits are the difference between `q^(-2)` and §9.4's `q^(-5)`.

`decidedAt_of_extract` is the positive form of `N3Recur.undecided_of_extract`: decidedness
descends ALONG the extraction, which is what the density lower bound consumes.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section MBox

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The mixed-precision box.** The three coordinates of a triple-root extraction are pinned to
precisions `M`, `M+1`, `M+2` respectively. -/
abbrev MBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (M : ℕ) : Type _ :=
  Res O M × Res O (M + 1) × Res O (M + 2)

/-- Truncation of the mixed box to the uniform level-`M` coefficient box. -/
def mtrunc (M : ℕ) : MBox O M →+ Coeff O 3 M :=
  Pi.addMonoidHom fun i =>
    ![(AddMonoidHom.fst (Res O M) (Res O (M + 1) × Res O (M + 2))),
      ((resFactor (O := O) (by omega : M ≤ M + 1)).toAddMonoidHom.comp
        ((AddMonoidHom.fst (Res O (M + 1)) (Res O (M + 2))).comp
          (AddMonoidHom.snd (Res O M) (Res O (M + 1) × Res O (M + 2))))),
      ((resFactor (O := O) (by omega : M ≤ M + 2)).toAddMonoidHom.comp
        ((AddMonoidHom.snd (Res O (M + 1)) (Res O (M + 2))).comp
          (AddMonoidHom.snd (Res O M) (Res O (M + 1) × Res O (M + 2)))))] i

theorem mtrunc_surjective (M : ℕ) : Function.Surjective (mtrunc (O := O) M) := by
  intro c
  obtain ⟨y, hy⟩ := resFactor_surjective (O := O) (by omega : M ≤ M + 1) (c 1)
  obtain ⟨z, hz⟩ := resFactor_surjective (O := O) (by omega : M ≤ M + 2) (c 2)
  refine ⟨(c 0, y, z), ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact hy
  · exact hz

theorem card_mbox (M : ℕ) : Nat.card (MBox O M) = residueCard O ^ (3 * M + 3) := by
  rw [Nat.card_prod, Nat.card_prod, card_res, card_res, card_res, ← pow_add, ← pow_add]
  congr 1
  omega

/-- **The proportion is preserved by the mixed-precision refinement.** Same statement as
`card_preimage_coeffFactor`, for `mtrunc`: the fibre size is
`#(MBox O M)/#(Coeff O 3 M) = q³`. -/
theorem card_preimage_mtrunc (M : ℕ) (S : Set (Coeff O 3 M)) :
    Nat.card ((mtrunc (O := O) M) ⁻¹' S) * Nat.card (Coeff O 3 M)
      = Nat.card S * Nat.card (MBox O M) := by
  have hs := mtrunc_surjective (O := O) M
  have h1 := card_preimage_of_surjective (mtrunc (O := O) M) hs S
  have h2 := card_preimage_of_surjective (mtrunc (O := O) M) hs Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
    Set.ncard_univ] at h2
  rw [h1, h2]
  ring

/-! ## Lifting -/

/-- A chosen lift `Res O k → O` (the level-`k` analogue of `AniCount.resLift`, which lifts the
residue field only). -/
noncomputable def resQLift (k : ℕ) : Res O k → O :=
  Function.surjInv Ideal.Quotient.mk_surjective

theorem mk_resQLift (k : ℕ) (x : Res O k) :
    Ideal.Quotient.mk ((maximalIdeal O) ^ k) (resQLift (O := O) k x) = x :=
  Function.surjInv_eq _ x

/-- The recentred coefficient vector reconstructed from a mixed-box element: `(π³d₀, π²d₁, πd₂)`
for the chosen lifts `d`. -/
noncomputable def boxVec (π : O) (M : ℕ) (x : MBox O M) : Fin 3 → O :=
  ![π ^ 3 * resQLift M x.1, π ^ 2 * resQLift (M + 1) x.2.1, π * resQLift (M + 2) x.2.2]

/-- **The reconstruction map.** From a residual centre `γ̄` and a mixed-precision extraction, the
level-`(M+3)` class of the cubic that extracts to it: recentre back by `−resSect γ̄`. -/
noncomputable def boxClass (π : O) (M : ℕ) (p : ResidueField O × MBox O M) : Coeff O 3 (M + 3) :=
  proj O 3 (M + 3) (shiftVec (boxVec π M p.2) (-(resSect O p.1)))

/-! ### Divisibility bookkeeping for the mixed precisions

The three coordinates carry the extracted factors `π³, π², π`, so a congruence at the *uniform*
level `M + 3` on the reconstructed vector is equivalent to congruences at the *mixed* levels
`M, M+1, M+2` on the extraction. Both directions are one cancellation in the domain `O`. -/

/-- Multiplying up: a level-`k` congruence becomes a level-`N` congruence after scaling by a
cofactor `m` with `π ^ N = m * π ^ k`. -/
private theorem dvd_mul_sub_mul {R : Type*} [CommRing R] {π m : R} {k N : ℕ}
    (hm : π ^ N = m * π ^ k) {u v : R} (h : π ^ k ∣ (u - v)) : π ^ N ∣ (m * u - m * v) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [hm]; linear_combination m * hc⟩

/-- Cancelling down: a level-`N` congruence between `m`-multiples, with `π ^ N = m * π ^ k`, is a
level-`k` congruence (`O` is a domain, so `m ≠ 0` cancels). -/
private theorem dvd_of_dvd_mul_sub_mul {R : Type*} [CommRing R] [IsDomain R] {π m : R}
    (hm0 : m ≠ 0) {k N : ℕ} (hm : π ^ N = m * π ^ k) {u v : R}
    (h : π ^ N ∣ (m * u - m * v)) : π ^ k ∣ (u - v) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, mul_left_cancel₀ hm0 ?_⟩
  calc m * (u - v) = m * u - m * v := by ring
    _ = π ^ N * c := hc
    _ = m * (π ^ k * c) := by rw [hm]; ring

/-- The chosen lift of a level-`k` class is congruent mod `π ^ k` to every representative. -/
private theorem dvd_resQLift_sub {π : O} (hπ : Irreducible π) {k : ℕ} {y : Res O k} {w : O}
    (hw : Ideal.Quotient.mk ((maximalIdeal O) ^ k) w = y) :
    π ^ k ∣ (resQLift (O := O) k y - w) := by
  refine (mem_maximalIdeal_pow_iff_dvd hπ k _).1 (Ideal.Quotient.eq.1 ?_)
  rw [mk_resQLift, hw]

/-- Two level-`k` classes whose chosen lifts are congruent mod `π ^ k` are equal. -/
private theorem res_eq_of_dvd_resQLift {π : O} (hπ : Irreducible π) {k : ℕ} {y y' : Res O k}
    (h : π ^ k ∣ (resQLift (O := O) k y' - resQLift (O := O) k y)) : y' = y := by
  have h2 : Ideal.Quotient.mk ((maximalIdeal O) ^ k) (resQLift (O := O) k y')
      = Ideal.Quotient.mk ((maximalIdeal O) ^ k) (resQLift (O := O) k y) :=
    Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd hπ k _).2 h)
  rwa [mk_resQLift, mk_resQLift] at h2

/-- **The level-`(M+3)` class reads only the MIXED class of the extraction.** Precisions
`(M, M+1, M+2)`: this is the sharp form of the level bookkeeping of §13.3. -/
theorem proj_shiftVec_eq_boxClass {π : O} (hπ : Irreducible π) (M : ℕ) (g : ResidueField O)
    {d : Fin 3 → O} {x : MBox O M}
    (h0 : Ideal.Quotient.mk ((maximalIdeal O) ^ M) (d 0) = x.1)
    (h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 1)) (d 1) = x.2.1)
    (h2 : Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) (d 2) = x.2.2) :
    proj O 3 (M + 3)
        (shiftVec ![π ^ 3 * d 0, π ^ 2 * d 1, π * d 2] (-(resSect O g)))
      = boxClass π M (g, x) := by
  have d0 := dvd_resQLift_sub hπ h0
  have d1 := dvd_resQLift_sub hπ h1
  have d2 := dvd_resQLift_sub hπ h2
  have hsub : ∀ i, π ^ (M + 3) ∣
      (boxVec π M x i - (![π ^ 3 * d 0, π ^ 2 * d 1, π * d 2] : Fin 3 → O) i) := by
    intro i
    fin_cases i
    · show π ^ (M + 3) ∣ (π ^ 3 * resQLift M x.1 - π ^ 3 * d 0)
      exact dvd_mul_sub_mul (m := π ^ 3) (k := M) (by ring) d0
    · show π ^ (M + 3) ∣ (π ^ 2 * resQLift (M + 1) x.2.1 - π ^ 2 * d 1)
      exact dvd_mul_sub_mul (m := π ^ 2) (k := M + 1) (by ring) d1
    · show π ^ (M + 3) ∣ (π * resQLift (M + 2) x.2.2 - π * d 2)
      exact dvd_mul_sub_mul (m := π) (k := M + 2) (by ring) d2
  exact (proj_eq_iff_dvd hπ _ _).2 (dvd_shiftVec_sub (-(resSect O g)) hsub)

/-- **The reconstruction is injective.** The residual centre is recovered from the residue of the
class (`cubeCoeff_injective`), and then the mixed class of the extraction is recovered digit for
digit. -/
theorem boxClass_injective {π : O} (hπ : Irreducible π) (M : ℕ) :
    Function.Injective (boxClass (O := O) π M) := by
  -- every reconstructed coordinate carries at least one factor `π`
  have hmemB : ∀ (x : MBox O M) (i : Fin 3), boxVec π M x i ∈ maximalIdeal O := by
    intro x i
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    fin_cases i
    · exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
    · exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
    · exact dvd_mul_right π _
  -- recentring back by `+γ` undoes the recentring by `−γ`
  have hback : ∀ (g : ResidueField O) (x : MBox O M),
      shiftVec (shiftVec (boxVec π M x) (-(resSect O g))) (resSect O g) = boxVec π M x := by
    intro g x
    have h := shiftVec_shiftVec_neg (boxVec π M x) (-(resSect O g))
    rwa [neg_neg] at h
  -- STEP A: the residue vector of the recentred class is `cubeCoeff` of the centre
  have hcentre : ∀ (g : ResidueField O) (x : MBox O M),
      resVec (shiftVec (boxVec π M x) (-(resSect O g))) = cubeCoeff g := by
    intro g x
    have h1 : ∀ i, shiftVec (shiftVec (boxVec π M x) (-(resSect O g))) (resSect O g) i
        ∈ maximalIdeal O := by
      intro i; rw [hback g x]; exact hmemB x i
    have h2 := (shiftVec_mem_iff (shiftVec (boxVec π M x) (-(resSect O g))) (resSect O g)).1 h1
    rwa [residue_resSect] at h2
  rintro ⟨g, x⟩ ⟨g', x'⟩ heq
  -- STEP B: the class equality is a coordinatewise congruence mod `π ^ (M+3)`
  have hd : ∀ i, π ^ (M + 3) ∣ (shiftVec (boxVec π M x') (-(resSect O g')) i
      - shiftVec (boxVec π M x) (-(resSect O g)) i) := (proj_eq_iff_dvd hπ _ _).1 heq
  have hres : resVec (shiftVec (boxVec π M x) (-(resSect O g)))
      = resVec (shiftVec (boxVec π M x') (-(resSect O g'))) := by
    funext i
    have hm : (shiftVec (boxVec π M x') (-(resSect O g')) i
        - shiftVec (boxVec π M x) (-(resSect O g)) i) ∈ maximalIdeal O := by
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
      exact (dvd_pow_self π (by omega : M + 3 ≠ 0)).trans (hd i)
    have h0 := (residue_eq_zero_iff _).2 hm
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm
  have hgg : g = g' := by
    refine cubeCoeff_injective ?_
    rw [← hcentre g x, ← hcentre g' x']
    exact hres
  subst hgg
  -- STEP C: with the centres equal, recentring back transports the congruence to `boxVec`
  have hB : ∀ i, π ^ (M + 3) ∣ (boxVec π M x' i - boxVec π M x i) := by
    intro i
    have h1 := dvd_shiftVec_sub (π := π) (N := M + 3) (resSect O g) hd i
    rwa [hback g x, hback g x'] at h1
  -- STEP D: cancel the extracted powers of `π`, digit by digit
  have hx1 : x.1 = x'.1 := by
    refine (res_eq_of_dvd_resQLift hπ ?_).symm
    exact dvd_of_dvd_mul_sub_mul (m := π ^ 3) (pow_ne_zero 3 hπ.ne_zero) (k := M) (by ring) (hB 0)
  have hx2 : x.2.1 = x'.2.1 := by
    refine (res_eq_of_dvd_resQLift hπ ?_).symm
    exact dvd_of_dvd_mul_sub_mul (m := π ^ 2) (pow_ne_zero 2 hπ.ne_zero) (k := M + 1) (by ring)
      (hB 1)
  have hx3 : x.2.2 = x'.2.2 := by
    refine (res_eq_of_dvd_resQLift hπ ?_).symm
    exact dvd_of_dvd_mul_sub_mul (m := π) hπ.ne_zero (k := M + 2) (by ring) (hB 2)
  -- STEP E
  exact Prod.ext rfl (Prod.ext hx1 (Prod.ext hx2 hx3))

end MBox

/-! ## Decidedness descends along the extraction -/

/-- If `x ≡ y` modulo a multiple `c` of `p`, then `p ∣ y` transfers to `p ∣ x`. (Local copy of
`N3Recur`'s private helper of the same shape.) -/
private theorem dvd_of_dvd_sub_left {R : Type*} [CommRing R] {p c x y : R} (hpc : p ∣ c)
    (hs : c ∣ (x - y)) (hy : p ∣ y) : p ∣ x := by
  have h1 : p ∣ x - y := hpc.trans hs
  have h2 : p ∣ (x - y) + y := dvd_add h1 hy
  have h3 : (x - y) + y = x := by ring
  rwa [h3] at h2

section Descend

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The positive form of `N3Recur.undecided_of_extract`.** If `σ` is decided on the level-`M`
class of the extraction, it is decided on the level-`(M+3)` class of the cubic. -/
theorem decidedAt_of_extract {π : O} (hπ : Irreducible π) {M : ℕ} {a : Fin 3 → O} {γ : O}
    {d : Fin 3 → O} {σ : FactorizationType}
    (e0 : shiftVec a γ 0 = π ^ 3 * d 0) (e1 : shiftVec a γ 1 = π ^ 2 * d 1)
    (e2 : shiftVec a γ 2 = π * d 2)
    (hdec : DecidedAt O 3 σ M (proj O 3 M d)) :
    DecidedAt O 3 σ (M + 3) (proj O 3 (M + 3) a) := by
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

end Descend

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.mtrunc_surjective
#print axioms UniformityCheck.card_mbox
#print axioms UniformityCheck.card_preimage_mtrunc
#print axioms UniformityCheck.proj_shiftVec_eq_boxClass
#print axioms UniformityCheck.boxClass_injective
#print axioms UniformityCheck.decidedAt_of_extract

end AxCheck

end UniformityCheck
