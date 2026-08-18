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
  sorry

/-! ### 2. the capped stage-height congruence -/

/-- the stage height of `0` is `⊤`. -/
theorem stageHeight_zero (F : KeyFrame O π) : F.stageHeight 0 = ⊤ := by
  sorry

/-- the extended-range normal form of the stage height. -/
theorem stageHeight_eq_inf_ext (F : KeyFrame O π) (A : Polynomial O) {M : ℕ}
    (hM : A.natDegree ≤ M) :
    F.stageHeight A
      = (Finset.range (M + 1)).inf
          (fun i => F.e₁ • gaussVal (Polynomial.C (A.coeff i)) + (F.h * i : ℕ∞)) := by
  sorry

/-- **the capped stage-height congruence**: coefficientwise-congruent polynomials have the
same stage height through the `e₁N` window. -/
theorem stageHeight_min_congr (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (h : ∀ i, π ^ N ∣ (A - A').coeff i) :
    min (F.stageHeight A) ((F.e₁ * N : ℕ) : ℕ∞)
      = min (F.stageHeight A') ((F.e₁ * N : ℕ) : ℕ∞) := by
  sorry

/-! ### 3. the capped dv-support congruence -/

/-- `dvHgt` of congruent polynomials agrees through the `e₁N` window (B.10 through the
key layer + the capped stage height). -/
theorem dvHgt_min_congr (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (h : ∀ i, π ^ N ∣ (A - A').coeff i) (j : ℕ) :
    min (dvHgt F A j) ((F.e₁ * N : ℕ) : ℕ∞)
      = min (dvHgt F A' j) ((F.e₁ * N : ℕ) : ℕ∞) := by
  sorry

/-- `dvHgt` vanishes to `⊤` above the degree. -/
theorem dvHgt_top_of_gt (F : KeyFrame O π) (A : Polynomial O) {j : ℕ}
    (hj : A.natDegree < j) : dvHgt F A j = ⊤ := by
  sorry

/-- **the capped dv-support congruence**: `dvSupp` of congruent polynomials agrees through
the `(e₁ℓ)N` window. -/
theorem dvSupp_min_congr (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (h : ∀ i, π ^ N ∣ (A - A').coeff i) (u ℓ : ℕ) (hℓ : 0 < ℓ) :
    min (dvSupp F A u ℓ) (((F.e₁ * ℓ) * N : ℕ) : ℕ∞)
      = min (dvSupp F A' u ℓ) (((F.e₁ * ℓ) * N : ℕ) : ℕ∞) := by
  sorry

/-! ### 4. through the level-2 development -/

/-- `dev` of `0` is `0` for ANY divisor (both `%ₘ`/`/ₘ` branches). -/
theorem dev_zero_any (Ψ : Polynomial O) : ∀ j, dev Ψ (0 : Polynomial O) j = 0 := by
  sorry

/-- the level-2 blocks of window-congruent members are congruent (monic and junk `Ψ`
branches alike). -/
theorem dev_blocks_congr (hπ : Irreducible π) {N : ℕ} {f f' : Polynomial O}
    (h : ∀ i, π ^ N ∣ (f - f').coeff i) (Ψ : Polynomial O) (j : ℕ) :
    ∀ i, π ^ N ∣ (dev Ψ f j - dev Ψ f' j).coeff i := by
  sorry

/-- window congruence of the coefficient vectors, read off `proj`. -/
theorem monicPoly_coeff_congr (hπ : Irreducible π) {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') :
    ∀ i, π ^ N ∣ (monicPoly a - monicPoly a').coeff i := by
  sorry

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
  sorry

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
  sorry

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dv2_read_congr_min
#print axioms Uniformity.Density.Tower.dv2_read_congr_vis

end AxCheck
