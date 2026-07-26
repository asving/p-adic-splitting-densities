import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

namespace LeanUrat.MovesGr

/-- (L0_pmul_mk, inlined) the piece product on classes: `pmul [a] [b] = [a·b]`. -/
private lemma pmul_mk_aux (S : SideVal p) (γ δ : ℤ) (a : S.ge γ) (b : S.ge δ) :
    S.pmul γ δ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
      = Submodule.Quotient.mk (S.mulToGe γ δ a b) := rfl

/-- (L0_deg_add, inlined) degree is additive when `w` is additive on the product. -/
private lemma deg_add_aux (S : SideVal p) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f * g ≠ 0) (hval : S.w (f * g) = S.w f + S.w g) :
    S.deg (f * g) = S.deg f + S.deg g := by
  have := S.deg_eq hfg
  rw [hval, ← S.deg_eq hf, ← S.deg_eq hg] at this
  exact_mod_cast this

/-- transport of `DirectSum.of` across an index equality, given HEq of the components. -/
private lemma of_congr (S : SideVal p) {γ γ' : ℤ} (h : γ = γ')
    (x : S.grPiece γ) (y : S.grPiece γ') (hxy : HEq x y) :
    DirectSum.of (fun δ => S.grPiece δ) γ x = DirectSum.of _ γ' y := by
  subst h; rw [eq_of_heq hxy]

/-- transport across an index equality where the two representatives differ by a `gt`-element. -/
private lemma of_quot_congr (S : SideVal p) {γ γ' : ℤ} (h : γ = γ')
    (a a' : Polynomial ℤ_[p]) (ha : ((γ : ℤ) : WithTop ℤ) ≤ S.w a)
    (ha' : ((γ' : ℤ) : WithTop ℤ) ≤ S.w a') (hd : a - a' ∈ S.gt γ) :
    DirectSum.of (fun δ => S.grPiece δ) γ (Submodule.Quotient.mk (⟨a, ha⟩ : S.ge γ))
      = DirectSum.of (fun δ => S.grPiece δ) γ' (Submodule.Quotient.mk (⟨a', ha'⟩ : S.ge γ')) := by
  subst h
  congr 1
  rw [Submodule.Quotient.eq]
  show a - a' ∈ S.gt γ
  exact hd

/-- two classes with the SAME representative but at (equal) different indices are HEq. -/
private lemma mk_heq (S : SideVal p) {γ γ' : ℤ} (h : γ = γ') (a : Polynomial ℤ_[p])
    (ha : ((γ : ℤ) : WithTop ℤ) ≤ S.w a) (ha' : ((γ' : ℤ) : WithTop ℤ) ≤ S.w a) :
    HEq (Submodule.Quotient.mk (⟨a, ha⟩ : S.ge γ) : S.grPiece γ)
        (Submodule.Quotient.mk (⟨a, ha'⟩ : S.ge γ') : S.grPiece γ') := by
  subst h; rfl

/-- classes at (equal) indices with EQUAL representatives are HEq. -/
private lemma mk_heq' (S : SideVal p) {γ γ' : ℤ} (h : γ = γ') (a a' : Polynomial ℤ_[p])
    (ha : ((γ : ℤ) : WithTop ℤ) ≤ S.w a) (ha' : ((γ' : ℤ) : WithTop ℤ) ≤ S.w a') (hv : a = a') :
    HEq (Submodule.Quotient.mk (⟨a, ha⟩ : S.ge γ) : S.grPiece γ)
        (Submodule.Quotient.mk (⟨a', ha'⟩ : S.ge γ') : S.grPiece γ') := by
  subst h; subst hv; rfl

/-- HEq of two piece products with equal outer index and equal representative product. -/
private lemma pmul_heq (S : SideVal p) {γ δ γ' δ' : ℤ} (h : γ + δ = γ' + δ')
    (a : S.ge γ) (b : S.ge δ) (a' : S.ge γ') (b' : S.ge δ')
    (hv : (a : Polynomial ℤ_[p]) * b = (a' : Polynomial ℤ_[p]) * b') :
    HEq (S.pmul γ δ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b))
        (S.pmul γ' δ' (Submodule.Quotient.mk a') (Submodule.Quotient.mk b')) := by
  rw [pmul_mk_aux, pmul_mk_aux]
  exact mk_heq' S h _ _ _ _ hv

section Build
variable (S : SideVal p)

/-- the degree-0 unit `[1]`. -/
private noncomputable def oneEl : S.grPiece 0 :=
  Submodule.Quotient.mk ⟨(1 : Polynomial ℤ_[p]), by
    show ((0 : ℤ) : WithTop ℤ) ≤ S.w 1
    rw [S.w_one]; simp⟩

private noncomputable instance gmulI : GradedMonoid.GMul (fun γ => S.grPiece γ) where
  mul {i j} x y := S.pmul i j x y

private noncomputable instance goneI : GradedMonoid.GOne (fun γ => S.grPiece γ) where
  one := oneEl S

private noncomputable instance gnnI :
    DirectSum.GNonUnitalNonAssocSemiring (fun γ => S.grPiece γ) where
  mul_zero {i j} a := map_zero (S.pmul i j a)
  zero_mul {i j} b := by
    show S.pmul i j 0 b = 0
    rw [map_zero (S.pmul i j), LinearMap.zero_apply]
  mul_add {i j} a b c := map_add (S.pmul i j a) b c
  add_mul {i j} a b c := by
    show S.pmul i j (a + b) c = S.pmul i j a c + S.pmul i j b c
    rw [map_add (S.pmul i j), LinearMap.add_apply]

private noncomputable instance gmonI : GradedMonoid.GMonoid (fun γ => S.grPiece γ) where
  one_mul := by
    rintro ⟨j, y⟩
    refine Sigma.ext (zero_add j) ?_
    induction y using Submodule.Quotient.induction_on with | _ y =>
    change HEq (S.pmul 0 j (oneEl S) (Submodule.Quotient.mk y)) (Submodule.Quotient.mk y)
    unfold oneEl
    rw [pmul_mk_aux]
    exact mk_heq' S (zero_add j) _ _ _ _ (one_mul _)
  mul_one := by
    rintro ⟨i, x⟩
    refine Sigma.ext (add_zero i) ?_
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change HEq (S.pmul i 0 (Submodule.Quotient.mk x) (oneEl S)) (Submodule.Quotient.mk x)
    unfold oneEl
    rw [pmul_mk_aux]
    exact mk_heq' S (add_zero i) _ _ _ _ (mul_one _)
  mul_assoc a b c := by sorry

private noncomputable instance gcmonI : GradedMonoid.GCommMonoid (fun γ => S.grPiece γ) where
  mul_comm := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    refine Sigma.ext (add_comm i j) ?_
    induction x using Submodule.Quotient.induction_on with | _ x =>
    induction y using Submodule.Quotient.induction_on with | _ y =>
    exact pmul_heq S (add_comm i j) x y y x (mul_comm _ _)

private noncomputable instance gsrI : DirectSum.GSemiring (fun γ => S.grPiece γ) where
  natCast n := n • (GradedMonoid.GOne.one : S.grPiece 0)
  natCast_zero := by simp
  natCast_succ n := succ_nsmul _ n

private noncomputable instance gcsrI : DirectSum.GCommSemiring (fun γ => S.grPiece γ) where

private noncomputable instance gringI : DirectSum.GRing (fun γ => S.grPiece γ) where
  intCast z := z • (GradedMonoid.GOne.one : S.grPiece 0)
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

private noncomputable instance gcrI : DirectSum.GCommRing (fun γ => S.grPiece γ) where

end Build

theorem L1_gradedRingStr_exists (S : SideVal p)
    (hval : ∀ f g, f ≠ 0 → g ≠ 0 → S.w (f * g) = S.w f + S.w g) :
    Nonempty (GradedRingStr S) := by
  letI cr : CommRing S.Gr := DirectSum.commRing (fun γ => S.grPiece γ)
  refine ⟨{ ring := cr, mul_of := ?_, one_def := ?_, if_mul := ?_, if_add_lt := ?_ }⟩
  · intro γ δ x y; exact DirectSum.of_mul_of x y
  · -- one_def : (1 : S.Gr) = S.initialForm 1
    have hdeg : S.deg 1 = 0 := by unfold SideVal.deg; rw [S.w_one]; rfl
    show DirectSum.of (fun γ => S.grPiece γ) 0 (oneEl S) = S.initialForm 1
    unfold SideVal.initialForm SideVal.mkPiece oneEl
    exact (of_congr S hdeg _ _ (mk_heq S hdeg 1 _ _)).symm
  · -- if_mul : [f*g] = [f]*[g]
    intro f g hf hg
    have hfg := mul_ne_zero hf hg
    have hd := deg_add_aux S f g hf hg hfg (hval f g hf hg)
    show S.initialForm (f * g) = S.initialForm f * S.initialForm g
    unfold SideVal.initialForm
    rw [DirectSum.of_mul_of]
    show S.initialForm (f * g) = DirectSum.of _ (S.deg f + S.deg g)
      (S.pmul (S.deg f) (S.deg g) (S.mkPiece f) (S.mkPiece g))
    unfold SideVal.initialForm SideVal.mkPiece
    rw [pmul_mk_aux]
    exact of_congr S hd _ _ (mk_heq S hd (f * g) _ _)
  · -- if_add_lt : [f+g] = [f] when deg f < deg g
    intro f g hf hg hfg hlt
    have hlt' : S.w f < S.w g := by
      rw [← S.deg_eq hf, ← S.deg_eq hg]; exact_mod_cast hlt
    have hge : S.w f ≤ S.w (f + g) :=
      le_of_eq_of_le (min_eq_left (le_of_lt hlt')).symm (S.w_add f g)
    have h2 : min (S.w (f + g)) (S.w g) ≤ S.w f := by
      have h3 := S.w_add (f + g) (-g)
      rw [S.w_neg, show (f + g) + (-g) = f by ring] at h3; exact h3
    have hle : S.w (f + g) ≤ S.w f := by
      rcases min_cases (S.w (f + g)) (S.w g) with ⟨hmin, _⟩ | ⟨hmin, _⟩
      · rw [hmin] at h2; exact h2
      · rw [hmin] at h2; exact absurd (lt_of_lt_of_le hlt' h2) (lt_irrefl _)
    have hadd : S.w (f + g) = S.w f := le_antisymm hle hge
    have hdfg : S.deg (f + g) = S.deg f := by unfold SideVal.deg; rw [hadd]
    show S.initialForm (f + g) = S.initialForm f
    unfold SideVal.initialForm SideVal.mkPiece
    refine of_quot_congr S hdfg (f + g) f _ _ ?_
    rw [show (f + g) - f = g by ring]
    show ((S.deg (f + g) : ℤ) : WithTop ℤ) < S.w g
    rw [hdfg, S.deg_eq hf]; exact hlt'

end LeanUrat.MovesGr
