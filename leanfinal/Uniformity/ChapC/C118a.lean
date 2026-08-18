/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B10
import Uniformity.ChapC.C11
import Uniformity.ChapC.C38a
import Uniformity.ChapC.C117

/-!
# Uniformity.ChapC.C118a — the A-C.7 repair: level-2 reads are WINDOW functions

**Amendment A-C.7's repair unit for NODE C.118** (the frozen clause 1 is machine-refuted —
`C118_REFUTATION.lean.txt`; the blueprint amendment records the defect and drafts the
re-signs).  Two public theorems:

* `dv2_read_congr_min` — the UNCONDITIONAL capped law: two members of the same level-`N`
  window class have equal level-2 pins AS SEEN THROUGH THE WINDOW
  (`min · W` with `W = (F.e₁ * L.ℓ) * N`).  No visibility hypothesis: this is the honest
  content of the node's title "visible reads are window functions".
* `dv2_read_congr_vis` — the guarded raw form: under `Visible₂` and a non-`⊤` pin of the
  visible member, the raw pins agree (the caps become invisible).  This is the consumer
  form; the refuted frozen statement is exactly this WITHOUT the `hT` guard.

## Route (A-C.7)

Every dv2 pin bottoms out in per-coefficient valuations of double developments: the digit
at ANY consulted position only reads the class mod `π^N`, so each capped read agrees, and
the caps ride up the two `inf`-layers because a term at or above the cap on one side is at
or above it on the other (the B.77 capped-min dichotomy, rebuilt at the dv-carrier).
`suppVal_congr` is NOT consumed (its `hdeg` binder fails for blocks — block degrees are
not window-stable); B.10's `dev_congr` propagates the congruence through both `dev`
layers, with the non-monic-`Ψ` junk branch (`%ₘ`/`/ₘ` junk conventions) handled by cases.

## Status

Sorry-free, axiom-free (Lean core only) at landing; the leanspec A-C.7 re-sign is the
orchestrator's separate step, gated on this module per the certify-BEFORE-sign standard.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C118a

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. ℕ∞ cap plumbing -/

/-- `min` commutes with a `Finset.inf` over a nonempty range. -/
theorem min_inf_eq {s : Finset ℕ} (hs : s.Nonempty) (f : ℕ → ℕ∞) (c : ℕ∞) :
    min (s.inf f) c = s.inf (fun i => min (f i) c) := by
  apply le_antisymm
  · refine Finset.le_inf fun i hi => ?_
    exact min_le_min (Finset.inf_le hi) le_rfl
  · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_mem_eq_inf s hs f
    rw [hmin]
    exact Finset.inf_le hi₀


/-- an `inf` over a range is unchanged by extending the range across `⊤` terms. -/
theorem inf_range_ext {m M : ℕ} (hmM : m ≤ M) (f : ℕ → ℕ∞)
    (htop : ∀ i, m < i → i ≤ M → f i = ⊤) :
    (Finset.range (m + 1)).inf f = (Finset.range (M + 1)).inf f := by
  apply le_antisymm
  · refine Finset.le_inf fun i hi => ?_
    rw [Finset.mem_range] at hi
    rcases le_or_gt i m with him | him
    · exact Finset.inf_le (Finset.mem_range.2 (by omega))
    · rw [htop i him (by omega)]
      exact le_top
  · refine Finset.le_inf fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact Finset.inf_le (Finset.mem_range.2 (by omega))

/-- smul-⊤ under a positive scalar. -/
theorem smul_top_pos {k : ℕ} (hk : 0 < k) : k • (⊤ : ℕ∞) = ⊤ := by
  rw [nsmul_eq_mul]
  exact WithTop.mul_top (Nat.cast_ne_zero.mpr hk.ne')

/-- capped valuations only read the class mod `π ^ N`. -/
theorem addVal_min_congr (hπ : Irreducible π) {N : ℕ} {x x' : O}
    (hdvd : π ^ N ∣ (x - x')) :
    min (addVal O x) (N : ℕ∞) = min (addVal O x') (N : ℕ∞) := by
  have key : ∀ y z : O, π ^ N ∣ (z - y) →
      min (addVal O y) (N : ℕ∞) ≤ min (addVal O z) (N : ℕ∞) := by
    intro y z hyz
    have hNzy : (N : ℕ∞) ≤ addVal O (z - y) := by
      have h1 : addVal O (π ^ N) ≤ addVal O (z - y) := addVal_le_iff_dvd.mpr hyz
      rwa [hπ.addVal_pow] at h1
    have hzsum : addVal O y ⊓ addVal O (z - y) ≤ addVal O z := by
      have h2 := addVal_add (a := y) (b := z - y)
      rwa [add_sub_cancel] at h2
    rcases le_or_gt (N : ℕ∞) (addVal O y) with hy | hy
    · have hz : (N : ℕ∞) ≤ addVal O z :=
        le_trans (le_min hy hNzy) hzsum
      rw [min_eq_right hy, min_eq_right hz]
    · have hz : addVal O y ≤ addVal O z :=
        le_trans (le_min le_rfl (le_trans hy.le hNzy)) hzsum
      rw [min_eq_left hy.le]
      exact le_min hz hy.le
  exact le_antisymm (key x x' (dvd_sub_comm.mp hdvd)) (key x' x hdvd)

/-! ### 2. the capped stage-height congruence -/

/-- the stage height of `0` is `⊤`. -/
theorem stageHeight_zero (F : KeyFrame O π) : F.stageHeight 0 = ⊤ := by
  rw [KeyFrame.stageHeight, suppVal]
  simp only [Polynomial.natDegree_zero, zero_add, Finset.range_one, Finset.inf_singleton]
  have h2 : npHgt X (0 : Polynomial O) 0 = ⊤ := by
    rw [npHgt]
    have hz : dev X (0 : Polynomial O) 0 = 0 := by
      rw [show dev X (0 : Polynomial O) 0 = (0 : Polynomial O) %ₘ X from rfl]
      simp
    rw [hz]
    exact gaussVal_eq_top_iff.2 rfl
  rw [h2, smul_top_pos F.he₁]
  simp

/-- the extended-range normal form of the stage height. -/
theorem stageHeight_eq_inf_ext (F : KeyFrame O π) (A : Polynomial O) {M : ℕ}
    (hM : A.natDegree ≤ M) :
    F.stageHeight A
      = (Finset.range (M + 1)).inf
          (fun i => F.e₁ • gaussVal (Polynomial.C (A.coeff i)) + (F.h * i : ℕ∞)) := by
  rw [KeyFrame.stageHeight_eq_inf]
  refine inf_range_ext hM _ fun i hi1 _ => ?_
  rw [A.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.C_0,
    gaussVal_eq_top_iff.2 rfl, smul_top_pos F.he₁, top_add]

/-- **the capped stage-height congruence**: coefficientwise-congruent polynomials have the
same stage height through the `e₁N` window. -/
theorem stageHeight_min_congr (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (h : ∀ i, π ^ N ∣ (A - A').coeff i) :
    min (F.stageHeight A) ((F.e₁ * N : ℕ) : ℕ∞)
      = min (F.stageHeight A') ((F.e₁ * N : ℕ) : ℕ∞) := by
  have hgC : ∀ x : O, gaussVal (Polynomial.C x) = addVal O x := by
    intro x
    rw [gaussVal]
    simp only [Polynomial.natDegree_C, zero_add, Finset.range_one, Finset.inf_singleton,
      Polynomial.coeff_C_zero]
  have hsmulN : F.e₁ • ((N : ℕ) : ℕ∞) = ((F.e₁ * N : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]
    exact_mod_cast rfl
  set M := max A.natDegree A'.natDegree with hM
  rw [stageHeight_eq_inf_ext F A (le_max_left _ _),
    stageHeight_eq_inf_ext F A' (le_max_right _ _),
    min_inf_eq ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩,
    min_inf_eq ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩]
  refine Finset.inf_congr rfl fun i _ => ?_
  have hcoef : π ^ N ∣ (A.coeff i - A'.coeff i) := by
    have := h i
    rwa [Polynomial.coeff_sub] at this
  have hcap := addVal_min_congr hπ (N := N) hcoef
  rcases le_or_gt (N : ℕ∞) (addVal O (A.coeff i)) with hbig | hsmall
  · have hbig' : (N : ℕ∞) ≤ addVal O (A'.coeff i) := by
      rw [min_eq_right hbig] at hcap
      by_contra hc
      push_neg at hc
      rw [min_eq_left hc.le] at hcap
      exact absurd (hcap ▸ hc) (lt_irrefl _)
    have ht1 : ((F.e₁ * N : ℕ) : ℕ∞) ≤ F.e₁ • gaussVal (Polynomial.C (A.coeff i)) + (F.h * i : ℕ∞) := by
      refine le_trans ?_ (le_add_of_nonneg_right zero_le)
      rw [hgC, ← hsmulN, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_left' hbig _
    have ht2 : ((F.e₁ * N : ℕ) : ℕ∞) ≤ F.e₁ • gaussVal (Polynomial.C (A'.coeff i)) + (F.h * i : ℕ∞) := by
      refine le_trans ?_ (le_add_of_nonneg_right zero_le)
      rw [hgC, ← hsmulN, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_left' hbig' _
    rw [min_eq_right ht1, min_eq_right ht2]
  · have heq : addVal O (A.coeff i) = addVal O (A'.coeff i) := by
      rw [min_eq_left hsmall.le] at hcap
      rcases min_cases (addVal O (A'.coeff i)) ((N : ℕ) : ℕ∞) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1] at hcap
        exact hcap
      · rw [h1] at hcap
        exact absurd (hcap ▸ hsmall) (lt_irrefl _)
    rw [hgC, hgC, heq]

/-! ### 3. the capped dv-support congruence -/

/-- `dvHgt` of congruent polynomials agrees through the `e₁N` window (B.10 through the
key layer + the capped stage height). -/
theorem dvHgt_min_congr (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (h : ∀ i, π ^ N ∣ (A - A').coeff i) (j : ℕ) :
    min (dvHgt F A j) ((F.e₁ * N : ℕ) : ℕ∞)
      = min (dvHgt F A' j) ((F.e₁ * N : ℕ) : ℕ∞) := by
  rw [dvHgt, dvHgt]
  exact stageHeight_min_congr hπ F (dev_congr hπ F.hmonic h j)

/-- `dvHgt` vanishes to `⊤` above the degree. -/
theorem dvHgt_top_of_gt (F : KeyFrame O π) (A : Polynomial O) {j : ℕ}
    (hj : A.natDegree < j) : dvHgt F A j = ⊤ := by
  have hdpos : 0 < F.key.natDegree := by
    rw [F.hdeg]
    exact Nat.mul_pos F.he₁ F.hf₁
  have hjd : j ≤ j * F.key.natDegree := Nat.le_mul_of_pos_right _ hdpos
  rw [dvHgt, dev_eq_zero_of_lt F.hmonic hdpos A j (by omega)]
  exact stageHeight_zero F

/-- **the capped dv-support congruence**: `dvSupp` of congruent polynomials agrees through
the `(e₁ℓ)N` window. -/
theorem dvSupp_min_congr (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (h : ∀ i, π ^ N ∣ (A - A').coeff i) (u ℓ : ℕ) (hℓ : 0 < ℓ) :
    min (dvSupp F A u ℓ) (((F.e₁ * ℓ) * N : ℕ) : ℕ∞)
      = min (dvSupp F A' u ℓ) (((F.e₁ * ℓ) * N : ℕ) : ℕ∞) := by
  set M := max A.natDegree A'.natDegree with hM
  have hext : ∀ B : Polynomial O, B.natDegree ≤ M →
      dvSupp F B u ℓ
        = (Finset.range (M + 1)).inf (fun i => ℓ • dvHgt F B i + (u * i : ℕ∞)) := by
    intro B hB
    rw [dvSupp]
    refine inf_range_ext hB _ fun i hi1 _ => ?_
    rw [dvHgt_top_of_gt F B (by omega), smul_top_pos hℓ, top_add]
  rw [hext A (le_max_left _ _), hext A' (le_max_right _ _),
    min_inf_eq ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩,
    min_inf_eq ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩]
  refine Finset.inf_congr rfl fun i _ => ?_
  have hcap := dvHgt_min_congr hπ F h i
  have hsmulW : ℓ • ((F.e₁ * N : ℕ) : ℕ∞) = (((F.e₁ * ℓ) * N : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]
    push_cast
    ring
  rcases le_or_gt ((F.e₁ * N : ℕ) : ℕ∞) (dvHgt F A i) with hbig | hsmall
  · have hbig' : ((F.e₁ * N : ℕ) : ℕ∞) ≤ dvHgt F A' i := by
      rw [min_eq_right hbig] at hcap
      by_contra hc
      push_neg at hc
      rw [min_eq_left hc.le] at hcap
      exact absurd (hcap ▸ hc) (lt_irrefl _)
    have ht1 : (((F.e₁ * ℓ) * N : ℕ) : ℕ∞) ≤ ℓ • dvHgt F A i + (u * i : ℕ∞) := by
      refine le_trans ?_ (le_add_of_nonneg_right zero_le)
      rw [← hsmulW, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_left' hbig _
    have ht2 : (((F.e₁ * ℓ) * N : ℕ) : ℕ∞) ≤ ℓ • dvHgt F A' i + (u * i : ℕ∞) := by
      refine le_trans ?_ (le_add_of_nonneg_right zero_le)
      rw [← hsmulW, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_left' hbig' _
    rw [min_eq_right ht1, min_eq_right ht2]
  · have heq : dvHgt F A i = dvHgt F A' i := by
      rw [min_eq_left hsmall.le] at hcap
      rcases min_cases (dvHgt F A' i) ((F.e₁ * N : ℕ) : ℕ∞) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1] at hcap
        exact hcap
      · rw [h1] at hcap
        exact absurd (hcap ▸ hsmall) (lt_irrefl _)
    rw [heq]

/-! ### 4. through the level-2 development -/

/-- `dev` of `0` is `0` for ANY divisor (both `%ₘ`/`/ₘ` branches). -/
theorem dev_zero_any (Ψ : Polynomial O) : ∀ j, dev Ψ (0 : Polynomial O) j = 0 := by
  intro j
  induction j with
  | zero =>
    rw [show dev Ψ (0 : Polynomial O) 0 = (0 : Polynomial O) %ₘ Ψ from rfl]
    exact Polynomial.zero_modByMonic Ψ
  | succ j ih =>
    rw [show dev Ψ (0 : Polynomial O) (j + 1)
      = dev Ψ ((0 : Polynomial O) /ₘ Ψ) j from rfl, Polynomial.zero_divByMonic]
    exact ih

/-- the level-2 blocks of window-congruent members are congruent (monic and junk `Ψ`
branches alike). -/
theorem dev_blocks_congr (hπ : Irreducible π) {N : ℕ} {f f' : Polynomial O}
    (h : ∀ i, π ^ N ∣ (f - f').coeff i) (Ψ : Polynomial O) (j : ℕ) :
    ∀ i, π ^ N ∣ (dev Ψ f j - dev Ψ f' j).coeff i := by
  by_cases hΨ : Ψ.Monic
  · exact dev_congr hπ hΨ h j
  · cases j with
    | zero =>
      intro i
      rw [show dev Ψ f 0 = f %ₘ Ψ from rfl, show dev Ψ f' 0 = f' %ₘ Ψ from rfl,
        Polynomial.modByMonic_eq_of_not_monic f hΨ, Polynomial.modByMonic_eq_of_not_monic f' hΨ]
      exact h i
    | succ j =>
      intro i
      rw [show dev Ψ f (j + 1) = dev Ψ (f /ₘ Ψ) j from rfl,
        show dev Ψ f' (j + 1) = dev Ψ (f' /ₘ Ψ) j from rfl,
        Polynomial.divByMonic_eq_of_not_monic f hΨ, Polynomial.divByMonic_eq_of_not_monic f' hΨ,
        dev_zero_any, sub_self]
      exact dvd_zero _

/-- window congruence of the coefficient vectors, read off `proj`. -/
theorem monicPoly_coeff_congr (hπ : Irreducible π) {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') :
    ∀ i, π ^ N ∣ (monicPoly a - monicPoly a').coeff i := by
  classical
  have htail : ∀ (b : Fin n → O) (t : ℕ),
      (∑ i : Fin n, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)).coeff t
        = if ht : t < n then b ⟨t, ht⟩ else 0 := by
    intro b t
    rw [finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases ht : t < n
    · rw [dif_pos ht, Finset.sum_eq_single (⟨t, ht⟩ : Fin n)]
      · simp
      · intro c _ hc
        exact if_neg fun hct => hc (Fin.ext hct.symm)
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · rw [dif_neg ht]
      refine Finset.sum_eq_zero fun c _ => if_neg fun hct => ht ?_
      exact hct ▸ c.isLt
  intro i
  have hmp : (monicPoly a - monicPoly a').coeff i
      = (if hi : i < n then a ⟨i, hi⟩ - a' ⟨i, hi⟩ else 0) := by
    rw [Polynomial.coeff_sub, monicPoly, monicPoly, Polynomial.coeff_add,
      Polynomial.coeff_add, htail a i, htail a' i]
    by_cases hi : i < n
    · rw [dif_pos hi, dif_pos hi, dif_pos hi]
      ring
    · rw [dif_neg hi, dif_neg hi, dif_neg hi]
      ring
  rw [hmp]
  by_cases hi : i < n
  · rw [dif_pos hi]
    have hmk := congrFun hc ⟨i, hi⟩
    have hmem : a ⟨i, hi⟩ - a' ⟨i, hi⟩ ∈ (IsLocalRing.maximalIdeal O) ^ N :=
      Ideal.Quotient.eq.mp hmk
    rwa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  · rw [dif_neg hi]
    exact dvd_zero _

end Uniformity.Density.Tower.C118a

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **A-C.7, clause 1′ — the unconditional capped window law.**  Two members of the same
level-`N` window class have equal level-2 pins through the window
`W = (F.e₁ * L.ℓ) * N`. -/
theorem dv2_read_congr_min {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') (j : ℕ) :
    min (dv2Pin L Ψ (monicPoly a) j) (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)
      = min (dv2Pin L Ψ (monicPoly a') j) (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) := by
  have hblocks := C118a.dev_blocks_congr hπ (C118a.monicPoly_coeff_congr hπ hc) Ψ j
  exact C118a.dvSupp_min_congr hπ F hblocks L.u L.ℓ L.hℓ

/-- **A-C.7, clause 1″ — the guarded raw form** (the frozen clause 1 with the missing
non-`⊤` guard).  Under visibility, a non-`⊤` pin of the visible member sits strictly below
the window, so the caps are invisible and the raw pins agree. -/
theorem dv2_read_congr_vis {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N) {j : ℕ} (hj : j ≤ n / L.keyDeg₂)
    (hT : dv2Pin L Ψ (monicPoly a) j ≠ ⊤) :
    dv2Pin L Ψ (monicPoly a) j = dv2Pin L Ψ (monicPoly a') j := by
  have hjbound : j ≤ (monicPoly a).natDegree / L.keyDeg₂ := by
    rw [monicPoly_natDegree]
    exact hj
  have hlt : dv2Pin L Ψ (monicPoly a) j < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) :=
    hvis j hjbound hT
  have hmin := dv2_read_congr_min L hπ (Ψ := Ψ) hc j
  rw [min_eq_left hlt.le] at hmin
  rcases min_cases (dv2Pin L Ψ (monicPoly a') j) (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)
    with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at hmin
    exact hmin
  · rw [h1] at hmin
    exact absurd (hmin ▸ hlt) (lt_irrefl _)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dv2_read_congr_min
#print axioms Uniformity.Density.Tower.dv2_read_congr_vis

end AxCheck
