/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H97r2
import Uniformity.Density.GenuineDensity
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapH.H97r3 — the triple-root step lemma and the sharp `q⁻⁵` count

**Chapter H, node-support file `H97r3`** (unit OM-1, `docs/openmath-campaign/
OM-1_n3-rate_2026-08-16.md`, steps S3 + S4).

**The step (S3, HYP.08's bookkeeping).** For a class UNDECIDED at level `M + 3` and residually
a perfect cube, recentre at a lift `γ` of the residual centre: cases **E**, **L**, **R**
(H97r2) each read off `B mod π³` and so would DECIDE the class — hence case **S** is forced,
the extraction `d` with `B = (π³d₀, π²d₁, πd₂)` exists, and its level-`M` class is undecided
again. The bookkeeping is asymmetric — the extraction determines `d` to precisions
`(M, M+1, M+2)` — and taking the WEAKEST of the three is what lands the step in the level-`M`
undecided set.

**The sharp count (S4, NEW in `leanfinal`).** Recording the extraction at its NATURAL mixed
precisions rather than uniformly,

    #(undecidedSet O 3 (M+3) ∩ tripleSet (M+3)) ≤ q⁴ · undecidedCount O 3 M ,

via the injection `c ↦ (γ̄, (d₀ mod π^M, d₁ mod π^(M+1), d₂ mod π^(M+2)))` into
`ResidueField O × mtrunc⁻¹(undecidedSet O 3 M)` — the constant `q⁴` (rate `q⁻⁵` after
normalizing) instead of the crude `q⁷` (rate `q⁻²`) of the uniform-precision record. This is
`N3_CHECK` §13.5's sharp constant applied to the UNDECIDED set; certification: the bound is an
EQUALITY at every measured cell (`verification/om1_n3_rate_check.py`, V-T1).

**PROVENANCE (quarry discipline).** Backport from the `leancheck` sidecar, verified building
green at leancheck commit `b00b0505` (2026-08-16): `UniformityCheck/N3Recur.lean` (`resSect`,
`residue_resSect`, the transfer helpers, `decidedAt_of_shift_cert`,
`legal_of_undecided_triple`, `typeOf_extract`, `undecided_of_extract`,
`undecided_triple_step`), `UniformityCheck/P5Consume.lean` (`typeOf_cubic_scale`),
`UniformityCheck/N3Drain.lean` (`tripleSet`), `UniformityCheck/N3MBox.lean` (`MBox`,
`mtrunc`, `mtrunc_surjective`, `card_mbox`, `card_preimage_mtrunc`, the mixed-precision
divisibility helpers). **Dedup-audit — verbatim moves except:**

1. namespace `UniformityCheck` → `Uniformity.Density`.
2. `N3Recur`'s `undecidedSet_subset_preimage`/`undecidedSeq_antitone` are NOT ported — landed
   at H.70 (`undecidedSet_preimage_subset`, `undecidedSeq_antitone`).
3. `N3MBox`'s `resQLift`/`boxVec`/`boxClass`/`boxClass_injective` are NOT ported (they serve
   the reconstruction/lower-bound direction, which the rate does not need); in their place the
   NEW `mtrunc_mkBox` and `card_undecidedTriple_sharp` implement the upper-count direction,
   adapting `N3Drain3.card_undecidedTriple_le`'s proof to the mixed precisions.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 0. Divisibility transfer along a congruence (port: `N3Recur` §0) -/

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

/-! ## 1. A section of the residue map (port: `N3Recur` §2) -/

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

/-! ## 2. The triple-root stratum (port: `N3Drain` §1) -/

section Stratum

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The triple-root stratum.** For `N ≥ 1`: a level-`N` class whose residue cubic is
`(X − γ̄)³` (at `N ≥ 1` the residue cubic is a property of the class, so the existential over
lifts is harmless). ⚠ At `N = 0` the coefficient box is a single class with lifts of every
residue, so `tripleSet 0` is everything; every quantitative statement below assumes `N ≥ 3`. -/
def tripleSet (N : ℕ) : Set (Coeff O 3 N) :=
  {c | ∃ (a : Fin 3 → O) (γ : O), proj O 3 N a = c ∧ resVec a = cubeCoeff (residue O γ)}

end Stratum

/-! ## 3. The step: cases E/L/R decide, case S descends (port: `N3Recur` §3,
`P5Consume.typeOf_cubic_scale`) -/

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

/-- **CASE S is forced.** An undecided level-`(M+3)` class that is residually a perfect cube has
a legal `X = πY` extraction: cases E, L and R would each have decided it. -/
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

/-- **The depth-reduction step** (`P5Consume.typeOf_cubic_scale`). If the cubic `monicPoly a`
becomes `monicPoly b` after the integral-slope extraction `X = π^m Y` — i.e.
`(monicPoly a)(π^m Y) = π^(3m)·(monicPoly b)(Y)` — then the two have the same splitting type. -/
theorem typeOf_cubic_scale {π : O} (hπ : Irreducible π) {a b : Fin 3 → O} (m : ℕ)
    (hcomp : (monicPoly a).comp (C (π ^ m) * X) = C (π ^ (m * 3)) * monicPoly b) :
    typeOf (monicPoly a) = typeOf (monicPoly b) := by
  refine typeOf_scale hπ (monicPoly_monic b) ?_ m ?_
  · rw [monicPoly_natDegree, monicPoly_natDegree]
  · rw [monicPoly_natDegree]; exact hcomp

/-- **The extraction preserves the type** (`typeOf_scale` at `m = 1`): the coefficient identity
is `(monicPoly b)(πX) = π³·(monicPoly d)(X)`. -/
theorem typeOf_extract {π : O} (hπ : Irreducible π) {b d : Fin 3 → O}
    (e0 : b 0 = π ^ 3 * d 0) (e1 : b 1 = π ^ 2 * d 1) (e2 : b 2 = π * d 2) :
    typeOf (monicPoly b) = typeOf (monicPoly d) := by
  refine typeOf_cubic_scale hπ 1 ?_
  rw [cubic_expand b, cubic_expand d, e0, e1, e2]
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_mul, map_pow, pow_one]
  ring

/-- **The descent.** With the extraction legal, undecidedness at level `M + 3` forces
undecidedness of the extracted class at level `M`. This is the level bookkeeping HYP.08: the
extraction determines `d` to precisions `(M, M+1, M+2)`, and the WEAKEST of the three is the
level that must be quoted. -/
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

/-- **THE STEP (S3, HYP.08).** Every undecided triple-root class at level `M + 3` is a legal
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

/-! ## 4. The mixed-precision box (port: `N3MBox`) -/

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

/-- The mixed-box record of a lift vector. -/
noncomputable def mkBox (M : ℕ) (d : Fin 3 → O) : MBox O M :=
  (Ideal.Quotient.mk ((maximalIdeal O) ^ M) (d 0),
   Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 1)) (d 1),
   Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) (d 2))

/-- Truncating the record recovers the level-`M` class. (NEW; the membership leg of the sharp
count.) -/
theorem mtrunc_mkBox (M : ℕ) (d : Fin 3 → O) :
    mtrunc (O := O) M (mkBox M d) = proj O 3 M d := by
  funext i
  fin_cases i
  · rfl
  · exact resFactor_mk (by omega : M ≤ M + 1) (d 1)
  · exact resFactor_mk (by omega : M ≤ M + 2) (d 2)

/-- Equal mixed-box records give the three mixed-precision congruences. (NEW; the injectivity
leg of the sharp count.) -/
theorem dvd_of_mkBox_eq {π : O} (hπ : Irreducible π) {M : ℕ} {d d' : Fin 3 → O}
    (h : mkBox (O := O) M d = mkBox M d') :
    π ^ M ∣ (d' 0 - d 0) ∧ π ^ (M + 1) ∣ (d' 1 - d 1) ∧ π ^ (M + 2) ∣ (d' 2 - d 2) := by
  have h0 : Ideal.Quotient.mk ((maximalIdeal O) ^ M) (d 0)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ M) (d' 0) := congrArg Prod.fst h
  have h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 1)) (d 1)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 1)) (d' 1) := congrArg (fun p => p.2.1) h
  have h2 : Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) (d 2)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) (d' 2) := congrArg (fun p => p.2.2) h
  exact ⟨dvd_sub_comm.1 ((mem_maximalIdeal_pow_iff_dvd hπ M _).1 (Ideal.Quotient.eq.1 h0)),
    dvd_sub_comm.1 ((mem_maximalIdeal_pow_iff_dvd hπ (M + 1) _).1 (Ideal.Quotient.eq.1 h1)),
    dvd_sub_comm.1 ((mem_maximalIdeal_pow_iff_dvd hπ (M + 2) _).1 (Ideal.Quotient.eq.1 h2))⟩

end MBox

/-! ## 5. The sharp count (S4, NEW) -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **THE SHARP COUNT (S4).** `#(undecided ∩ triple at level M+3) ≤ q⁴ · undecidedCount M`. The
map `c ↦ (γ̄, mixed-precision record of the extraction)` is injective: `γ̄` fixes the recentring
point through `resSect`, and the mixed congruences `(M, M+1, M+2)` multiply back up to
`π^(M+3) ∣ B' i - B i` with NO loss — the asymmetry of the extraction is exactly matched by the
extracted powers `π³, π², π`. Adapts `N3Drain3.card_undecidedTriple_le` (leancheck), whose
uniform-precision record loses three digits (`q⁷`). -/
theorem card_undecidedTriple_sharp {π : O} (hπ : Irreducible π) (M : ℕ) :
    Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
        Set (Coeff O 3 (M + 3)))
      ≤ residueCard O ^ 4 * undecidedCount O 3 M := by
  classical
  simp only [undecidedCount]
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
  -- (b) the record lands in the mixed boxes over the undecided level-`M` classes
  have hmemS : ∀ c, mkBox (O := O) M ((f c).2.2)
      ∈ (mtrunc (O := O) M) ⁻¹' (undecidedSet O 3 M) := by
    intro c
    show mtrunc (O := O) M (mkBox M ((f c).2.2)) ∈ undecidedSet O 3 M
    rw [mtrunc_mkBox]
    exact hf5 c
  -- (c) the injection `c ↦ (γ̄, mixed record of the extraction)`
  have hinj : Function.Injective
      (fun c : (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
          Set (Coeff O 3 (M + 3))) =>
        (((f c).1, (⟨mkBox M ((f c).2.2), hmemS c⟩ :
            ((mtrunc (O := O) M) ⁻¹' (undecidedSet O 3 M) : Set (MBox O M)))) :
          ResidueField O × ((mtrunc (O := O) M) ⁻¹' (undecidedSet O 3 M) : Set (MBox O M)))) := by
    intro c c' hcc
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcc
    obtain ⟨e1, e2⟩ := hcc
    have hγ' : resSect O (f c').1 = resSect O (f c).1 := by rw [e1]
    obtain ⟨hd0, hd1, hd2⟩ := dvd_of_mkBox_eq hπ e2
    -- multiply the three coordinates back up: `3 + M = 2 + (M+1) = 1 + (M+2) = M + 3`
    have k0 : shiftVec (f c').2.1 (resSect O (f c).1) 0 = π ^ 3 * (f c').2.2 0 := by
      rw [← hγ']; exact hf2 c'
    have k1 : shiftVec (f c').2.1 (resSect O (f c).1) 1 = π ^ 2 * (f c').2.2 1 := by
      rw [← hγ']; exact hf3 c'
    have k2 : shiftVec (f c').2.1 (resSect O (f c).1) 2 = π * (f c').2.2 2 := by
      rw [← hγ']; exact hf4 c'
    have hB0 : π ^ (M + 3) ∣ (shiftVec (f c').2.1 (resSect O (f c).1) 0
        - shiftVec (f c).2.1 (resSect O (f c).1) 0) := by
      rw [k0, hf2 c]
      obtain ⟨t, ht⟩ := hd0
      exact ⟨t, by rw [← mul_sub, ht]; ring⟩
    have hB1 : π ^ (M + 3) ∣ (shiftVec (f c').2.1 (resSect O (f c).1) 1
        - shiftVec (f c).2.1 (resSect O (f c).1) 1) := by
      rw [k1, hf3 c]
      obtain ⟨t, ht⟩ := hd1
      exact ⟨t, by rw [← mul_sub, ht]; ring⟩
    have hB2 : π ^ (M + 3) ∣ (shiftVec (f c').2.1 (resSect O (f c).1) 2
        - shiftVec (f c).2.1 (resSect O (f c).1) 2) := by
      rw [k2, hf4 c]
      obtain ⟨t, ht⟩ := hd2
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
  -- (d) the count
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hle
  have hcp := card_preimage_mtrunc (O := O) M (undecidedSet O 3 M)
  rw [card_coeff, card_mbox] at hcp
  have hScard : Nat.card ((mtrunc (O := O) M) ⁻¹' (undecidedSet O 3 M) : Set (MBox O M))
      = Nat.card (undecidedSet O 3 M) * residueCard O ^ 3 := by
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) (3 * M)) ?_
    rw [hcp, show 3 * M + 3 = 3 + 3 * M from by ring, pow_add]
    ring
  rw [hScard] at hle
  have hres : Nat.card (ResidueField O) = residueCard O := rfl
  rw [hres] at hle
  calc Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
        Set (Coeff O 3 (M + 3)))
      ≤ residueCard O * (Nat.card (undecidedSet O 3 M) * residueCard O ^ 3) := hle
    _ = residueCard O ^ 4 * Nat.card (undecidedSet O 3 M) := by ring

end Count

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.residue_resSect
#print axioms Uniformity.Density.decidedAt_of_shift_cert
#print axioms Uniformity.Density.legal_of_undecided_triple
#print axioms Uniformity.Density.typeOf_cubic_scale
#print axioms Uniformity.Density.typeOf_extract
#print axioms Uniformity.Density.undecided_of_extract
#print axioms Uniformity.Density.undecided_triple_step
#print axioms Uniformity.Density.mtrunc_surjective
#print axioms Uniformity.Density.card_mbox
#print axioms Uniformity.Density.card_preimage_mtrunc
#print axioms Uniformity.Density.mtrunc_mkBox
#print axioms Uniformity.Density.card_undecidedTriple_sharp

end AxCheck
