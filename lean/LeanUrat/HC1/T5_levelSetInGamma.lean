/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.T4_slotMinHt

/-!
# HC1.T5_levelSetInγ — LST(i-c): in_γ is a function of exactly the level set

moves_ref: MOVES 3739–3742 "the weight-γ initial form in_γ(B) is a function of
exactly the LEVEL SET L_γ(B)". deps: T4, T6. difficulty: medium. hyp: none.

Proof strategy (blueprint sketch: "difference has weight > γ (T4 on x − y); inγ_kills"):
the two slot coefficients `slotCoeff b x`, `slotCoeff b y` differ only by the OFF-LEVEL
residuals `Rx := slotCoeff b xOff`, `Ry := slotCoeff b yOff`, where `xOff`/`yOff` zero out
the block-`b` coordinates AT height `γ`.  On the level set the two agree, so those digit
terms cancel PAIRWISE and `Bx - By = Rx - Ry`.  Every nonzero off-level digit sits at
height `> γ` (below `γ` both are zero by hypothesis; at `γ` it is on the level set), so T4
puts `wQ Rx, wQ Ry > γ`, hence the side weight of `Bx - By` exceeds `⌊strTop·γ⌋`.  The
class map `inGr γ` then sends `Bx` and `By` to the same graded piece (`inγ_kills` on the
difference — realised directly from the quotient definition of `inGr`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The accumulated stretch is a product of ramification indices, each `≥ 1`. -/
private lemma strAux_pos (T : Tower p F) : ∀ n, 1 ≤ T.strAux n := by
  intro n
  induction n with
  | zero => simp [Tower.strAux]
  | succ k ih =>
    have hfac : 1 ≤ (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1) := by
      split
      · exact (T.stg _).he
      · exact le_refl 1
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ T.strAux k * (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1) :=
          Nat.mul_le_mul ih hfac
      _ = T.strAux (k + 1) := by rw [Tower.strAux]

/-- The frame stretch `strTop = STR_K·e_K` is positive (product of `e ≥ 1` factors). -/
private lemma strTop_pos (T : Tower p F) : 0 < T.strTop := by
  rw [Tower.strTop]
  exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (strAux_pos T _))
    (lt_of_lt_of_le Nat.zero_lt_one (T.stg _).he)

/-- The Teichmüller-style digit lift of the ZERO digit is `0` (no nonzero coefficient has
zero residual — `hRne`). -/
private lemma digLift_zero (T : Tower p F) : T.digLift 0 = 0 := by
  unfold Tower.digLift
  rw [dif_neg]
  rintro ⟨B, hB0, _hinC, _hwp, hR⟩
  refine (T.stg 0).hRne B hB0 ?_
  rw [hR]
  have : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ : ↥(T.stg 0).K)
      = 0 := by
    apply Subtype.ext
    simp
  rw [this]
  simp

/-- `digLift (z c) · m_c` is supported inside `z`'s support (zero digits lift to `0`). -/
private lemma digLift_mono_support_subset (T : Tower p F) (z : T.Coord → ↥(T.stg 0).FQ) :
    Function.support (fun c => T.digLift (z c) * T.mono c) ⊆ Function.support z := by
  intro c hc
  rw [Function.mem_support] at hc ⊢
  intro hz
  exact hc (by rw [hz, digLift_zero T, zero_mul])

/-- Conversion: strict weight `> γ` on the absolute scale `wQ` becomes strict side weight
`> ⌊strTop·γ⌋`. -/
private lemma wQ_gt_imp_side_gt (T : Tower p F) (γ : ℚ) (f : Polynomial ℤ_[p])
    (hpos : 0 < T.strTop) (hgt : (γ : WithTop ℚ) < T.wQ f) :
    (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) < T.side.w f := by
  rcases eq_or_ne (T.side.w f) ⊤ with hw | hw
  · rw [hw]; exact WithTop.coe_lt_top _
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hw
    have hsp : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast hpos
    unfold Tower.wQ at hgt
    rw [← hm] at hgt ⊢
    rw [WithTop.map_coe, WithTop.coe_lt_coe, lt_div_iff₀ hsp] at hgt
    rw [WithTop.coe_lt_coe]
    have hfloor : (⌊(T.strTop : ℚ) * γ⌋ : ℚ) ≤ (T.strTop : ℚ) * γ := Int.floor_le _
    have hlt : (⌊(T.strTop : ℚ) * γ⌋ : ℚ) < (m : ℚ) := by
      calc (⌊(T.strTop : ℚ) * γ⌋ : ℚ) ≤ (T.strTop : ℚ) * γ := hfloor
        _ = γ * (T.strTop : ℚ) := by ring
        _ < (m : ℚ) := hgt
    exact_mod_cast hlt

/-- The class map `inGr γ` identifies polynomials whose difference has side weight strictly
above `⌊strTop·γ⌋` (`inγ_kills`, realised from the quotient definition). -/
private lemma inGr_eq_of_sub_gt (T : Tower p F) (γ : ℚ) (f g : Polynomial ℤ_[p])
    (h : (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) < T.side.w (f - g)) :
    T.inGr γ f = T.inGr γ g := by
  unfold Tower.inGr
  by_cases hlat : T.onLattice γ
  · by_cases hf : (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) ≤ T.side.w f
    · have hg : (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) ≤ T.side.w g := by
        have hw := T.side.w_add g (f - g)
        rw [show g + (f - g) = f by ring] at hw
        -- hw : min (w g) (w (f-g)) ≤ w f  -- not directly useful; use the other order
        have hw2 := T.side.w_add f (-(f - g))
        rw [T.side.w_neg (f - g), show f + -(f - g) = g by ring] at hw2
        exact le_trans (le_min hf (le_of_lt h)) hw2
      rw [dif_pos ⟨hlat, hf⟩, dif_pos ⟨hlat, hg⟩]
      refine (Submodule.Quotient.eq (T.side.gtIn ⌊(T.strTop : ℚ) * γ⌋)).mpr ?_
      exact h
    · have hg : ¬ (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) ≤ T.side.w g := by
        intro hgle
        apply hf
        have hw := T.side.w_add g (f - g)
        rw [show g + (f - g) = f by ring] at hw
        exact le_trans (le_min hgle (le_of_lt h)) hw
      rw [dif_neg (fun hc => hf hc.2), dif_neg (fun hc => hg hc.2)]
  · rw [dif_neg (fun hc => hlat hc.1), dif_neg (fun hc => hlat hc.1)]

/-- Unit T5: two assignments agreeing on the level set, with all block-b digits of
height below γ zero, have equal weight-γ initial forms. -/
theorem T5_levelSetInGamma {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (x y : T.Coord → ↥(T.stg 0).FQ)
    (hxfin : (Function.support x).Finite) (hyfin : (Function.support y).Finite)
    (hagree : ∀ c ∈ T.levelSet b γ, x c = y c)
    (hxlow : ∀ c, T.blk c = b → T.ht c < γ → x c = 0)
    (hylow : ∀ c, T.blk c = b → T.ht c < γ → y c = 0) :
    T.inGr γ (T.slotCoeff b x) = T.inGr γ (T.slotCoeff b y) := by
  classical
  -- off-level restrictions: keep only block-b coordinates strictly away from height γ
  set xOff : T.Coord → ↥(T.stg 0).FQ :=
    fun c => if T.blk c = b ∧ T.ht c ≠ γ then x c else 0 with hxOff
  set yOff : T.Coord → ↥(T.stg 0).FQ :=
    fun c => if T.blk c = b ∧ T.ht c ≠ γ then y c else 0 with hyOff
  -- supports of the restrictions sit inside the originals
  have hxOff_sub : Function.support xOff ⊆ Function.support x := by
    intro c hc; rw [Function.mem_support] at hc ⊢; intro hx0; apply hc
    rw [hxOff]; simp [hx0]
  have hyOff_sub : Function.support yOff ⊆ Function.support y := by
    intro c hc; rw [Function.mem_support] at hc ⊢; intro hy0; apply hc
    rw [hyOff]; simp [hy0]
  have hxOff_supp : ∀ c, xOff c ≠ 0 → T.blk c = b := by
    intro c hc; by_contra hb; apply hc; rw [hxOff]; simp [hb]
  have hyOff_supp : ∀ c, yOff c ≠ 0 → T.blk c = b := by
    intro c hc; by_contra hb; apply hc; rw [hyOff]; simp [hb]
  -- the key polynomial identity: Bx - By = Rx - Ry (level-set terms cancel pairwise)
  have hkey : T.slotCoeff b x + T.slotCoeff b yOff
      = T.slotCoeff b y + T.slotCoeff b xOff := by
    unfold Tower.slotCoeff
    have hfx : ({c : T.Coord | T.blk c = b} ∩
        Function.support (fun c => T.digLift (x c) * T.mono c)).Finite :=
      hxfin.subset (Set.inter_subset_right.trans (digLift_mono_support_subset T x))
    have hfy : ({c : T.Coord | T.blk c = b} ∩
        Function.support (fun c => T.digLift (y c) * T.mono c)).Finite :=
      hyfin.subset (Set.inter_subset_right.trans (digLift_mono_support_subset T y))
    have hfxOff : ({c : T.Coord | T.blk c = b} ∩
        Function.support (fun c => T.digLift (xOff c) * T.mono c)).Finite :=
      hxfin.subset (Set.inter_subset_right.trans
        ((digLift_mono_support_subset T xOff).trans hxOff_sub))
    have hfyOff : ({c : T.Coord | T.blk c = b} ∩
        Function.support (fun c => T.digLift (yOff c) * T.mono c)).Finite :=
      hyfin.subset (Set.inter_subset_right.trans
        ((digLift_mono_support_subset T yOff).trans hyOff_sub))
    rw [← finsum_mem_add_distrib' hfx hfyOff, ← finsum_mem_add_distrib' hfy hfxOff]
    apply finsum_mem_congr rfl
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    by_cases hht : T.ht c = γ
    · -- c is on the level set: x c = y c, both restrictions are 0
      have hxeq : x c = y c := hagree c ⟨hc, hht⟩
      have hxo : xOff c = 0 := by rw [hxOff]; simp [hht]
      have hyo : yOff c = 0 := by rw [hyOff]; simp [hht]
      rw [hxo, hyo, hxeq]
    · -- off the level set: restrictions equal the originals
      have hxo : xOff c = x c := by rw [hxOff]; simp [hc, hht]
      have hyo : yOff c = y c := by rw [hyOff]; simp [hc, hht]
      rw [hxo, hyo]; ring
  -- Bx - By = Rx - Ry
  have hdiff : T.slotCoeff b x - T.slotCoeff b y
      = T.slotCoeff b xOff - T.slotCoeff b yOff := by
    linear_combination hkey
  -- each off-level residual has side weight above ⌊strTop·γ⌋
  have hres : ∀ (z : T.Coord → ↥(T.stg 0).FQ),
      (Function.support z ⊆ Function.support x ∨ Function.support z ⊆ Function.support y) →
      (∀ c, z c ≠ 0 → T.blk c = b) →
      (∀ c, z c ≠ 0 → T.ht c ≠ γ) →
      (∀ c, T.blk c = b → T.ht c < γ → z c = 0) →
      (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) < T.side.w (T.slotCoeff b z) := by
    intro z hzsub hzblk hzht hzlow
    by_cases hz0 : T.slotCoeff b z = 0
    · rw [hz0, T.side.w_zero]; exact WithTop.coe_lt_top _
    · have hzfin : (Function.support z).Finite := by
        rcases hzsub with h | h
        · exact hxfin.subset h
        · exact hyfin.subset h
      obtain ⟨c₀, hc0ne, hweq, _hmin⟩ := T4_slotMinHt T b z hzfin hzblk hz0
      have hgt : γ < T.ht c₀ := by
        have hge : γ ≤ T.ht c₀ := by
          by_contra hlt
          exact hc0ne (hzlow c₀ (hzblk c₀ hc0ne) (not_le.mp hlt))
        exact lt_of_le_of_ne hge (Ne.symm (hzht c₀ hc0ne))
      have hwQ : (γ : WithTop ℚ) < T.wQ (T.slotCoeff b z) := by
        rw [hweq]; exact WithTop.coe_lt_coe.mpr hgt
      exact wQ_gt_imp_side_gt T γ _ (strTop_pos T) hwQ
  have hRx : (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) < T.side.w (T.slotCoeff b xOff) := by
    refine hres xOff (Or.inl hxOff_sub) hxOff_supp ?_ ?_
    · intro c hc; by_contra hht; apply hc; rw [hxOff]; simp [hht]
    · intro c hcb hlt
      rw [hxOff]; simp only [ite_eq_right_iff]
      intro ⟨_, _⟩; exact hxlow c hcb hlt
  have hRy : (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) < T.side.w (T.slotCoeff b yOff) := by
    refine hres yOff (Or.inr hyOff_sub) hyOff_supp ?_ ?_
    · intro c hc; by_contra hht; apply hc; rw [hyOff]; simp [hht]
    · intro c hcb hlt
      rw [hyOff]; simp only [ite_eq_right_iff]
      intro ⟨_, _⟩; exact hylow c hcb hlt
  -- side weight of the difference exceeds the threshold, so the classes coincide
  have hwdiff : (⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ)
      < T.side.w (T.slotCoeff b x - T.slotCoeff b y) := by
    rw [hdiff]
    have hw := T.side.w_add (T.slotCoeff b xOff) (-(T.slotCoeff b yOff))
    rw [T.side.w_neg (T.slotCoeff b yOff),
      show T.slotCoeff b xOff + -(T.slotCoeff b yOff)
        = T.slotCoeff b xOff - T.slotCoeff b yOff by ring] at hw
    exact lt_of_lt_of_le (lt_min hRx hRy) hw
  exact inGr_eq_of_sub_gt T γ _ _ hwdiff

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T5_levelSetInGamma
