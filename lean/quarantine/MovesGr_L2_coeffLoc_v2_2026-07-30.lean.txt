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
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! Auxiliary units-of-Laurent arithmetic: `tUnit R a` (value `T a`) is a group hom in `a`. -/

private lemma tUnit_val (R : Type*) [CommRing R] (a : ℤ) :
    ((tUnit R a : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T a := rfl

private lemma tUnit_mul (R : Type*) [CommRing R] (a b : ℤ) :
    tUnit R a * tUnit R b = tUnit R (a + b) :=
  Units.ext (LaurentPolynomial.T_add _ _).symm

private lemma tUnit_zero (R : Type*) [CommRing R] : tUnit R 0 = 1 :=
  Units.ext LaurentPolynomial.T_zero

private lemma tUnit_inv (R : Type*) [CommRing R] (a : ℤ) :
    (tUnit R a)⁻¹ = tUnit R (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tUnit_mul, add_neg_cancel, tUnit_zero]

private lemma tUnit_zpow (R : Type*) [CommRing R] (n : ℤ) : ∀ m : ℤ,
    (tUnit R n) ^ m = tUnit R (n * m) := by
  intro m
  induction m using Int.induction_on with
  | zero => rw [mul_zero, zpow_zero, tUnit_zero]
  | succ k ih => rw [zpow_add_one, ih, tUnit_mul]; congr 1; ring
  | pred k ih => rw [zpow_sub_one, ih, tUnit_inv, tUnit_mul]; congr 1; ring

/-! The weight-detecting evaluation: `Ein : z ↦ z^e` on the inner ring, `Eout : T ↦ z^t`
over `Ein` on `LTwo = L₀[T^{±1}]`.  Every `coeffLocSR` generator is a monomial
`C(c·z^{−t·ν})·T^{e·ν}` (hS5 + hStretch), whose image is `C c` — an inner CONSTANT —
because `e·(−t·ν) + t·(e·ν) = 0`.  So `Eout(coeffLocSR) ⊆ range C`, while on outer-constants
`C ℓ` the map is `mapDomain (e·)` on `ℓ`, injective since `1 ≤ e`: (S4 ⊆) follows. -/

private noncomputable def Ein (σ : Stage p F) :
    LaurentPolynomial ↥σ.K →+* LaurentPolynomial ↥σ.K :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C (tUnit ↥σ.K (σ.e : ℤ))

private noncomputable def Eout (σ : Stage p F) :
    LTwo ↥σ.K →+* LaurentPolynomial ↥σ.K :=
  LaurentPolynomial.eval₂ (Ein σ) (tUnit ↥σ.K σ.t)

private lemma Ein_apply (σ : Stage p F) (y : LaurentPolynomial ↥σ.K) :
    Ein σ y = LaurentPolynomial.eval₂ LaurentPolynomial.C (tUnit ↥σ.K (σ.e : ℤ)) y := rfl

private lemma Eout_apply (σ : Stage p F) (y : LTwo ↥σ.K) :
    Eout σ y = LaurentPolynomial.eval₂ (Ein σ) (tUnit ↥σ.K σ.t) y := rfl

/-- Image of the initial form of any coefficient: an inner constant (the digit scalar). -/
private lemma Eout_grRes (σ : Stage p F) {B : Polynomial ℤ_[p]} (hB0 : B ≠ 0)
    (hBC : inC σ.Φ B) :
    ∃ c : (↥σ.K)ˣ, Eout σ (σ.grRes B) = LaurentPolynomial.C (c : ↥σ.K) ∧
      σ.R B = LaurentPolynomial.C (c : ↥σ.K) * LaurentPolynomial.T (- σ.t * σ.wPrev B) := by
  obtain ⟨c, hc⟩ := σ.hS5 B hB0 hBC
  refine ⟨c, ?_, hc⟩
  have hgr : σ.grRes B = LaurentPolynomial.C (σ.R B) * LaurentPolynomial.T (σ.w B) := rfl
  rw [hgr, hc, Eout_apply, LaurentPolynomial.eval₂_C_mul_T, Ein_apply,
    LaurentPolynomial.eval₂_C_mul_T]
  simp only [tUnit_zpow, tUnit_val]
  rw [σ.hStretch B hB0 hBC, mul_assoc, ← LaurentPolynomial.T_add]
  have h0 : (σ.e : ℤ) * (- σ.t * σ.wPrev B) + σ.t * ((σ.e : ℤ) * σ.wPrev B) = 0 := by ring
  rw [h0, LaurentPolynomial.T_zero, mul_one]

/-- The coefficient localization maps into the inner constants under `Eout`. -/
private lemma coeffLoc_le (σ : Stage p F) :
    σ.coeffLocSR ≤ Subring.comap (Eout σ)
      (LaurentPolynomial.C : ↥σ.K →+* LaurentPolynomial ↥σ.K).range := by
  refine Subring.closure_le.mpr (Set.union_subset ?_ ?_)
  · rintro x ⟨B, hB0, hBC, rfl⟩
    obtain ⟨c, hc, -⟩ := Eout_grRes σ hB0 hBC
    exact Subring.mem_comap.mpr (RingHom.mem_range.mpr ⟨_, hc.symm⟩)
  · rintro x ⟨i, u, hu, rfl⟩
    obtain ⟨hr0, hrC⟩ := σ.hreps (σ.reps.get i) (List.get_mem _ _)
    obtain ⟨c, hc, -⟩ := Eout_grRes σ hr0 hrC
    have hu' : (u : LTwo ↥σ.K) = σ.grRes (σ.reps.get i) := hu
    have hval : Eout σ (u : LTwo ↥σ.K)
        = LaurentPolynomial.C (c : ↥σ.K) := by rw [hu']; exact hc
    refine Subring.mem_comap.mpr (RingHom.mem_range.mpr
      ⟨((c⁻¹ : (↥σ.K)ˣ) : ↥σ.K), ?_⟩)
    have h2 : LaurentPolynomial.C ((c⁻¹ : (↥σ.K)ˣ) : ↥σ.K)
        * LaurentPolynomial.C (c : ↥σ.K) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h1 : LaurentPolynomial.C (c : ↥σ.K)
        * Eout σ ((u⁻¹ : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) = 1 := by
      rw [← hval, ← map_mul, Units.mul_inv, map_one]
    exact left_inv_eq_right_inv h2 h1

/-- `Ein` IS `mapDomain (e·)` as a ring hom — the inner variable is only rescaled. -/
private lemma Ein_eq_mapDomainRingHom (σ : Stage p F) :
    Ein σ = AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    have hb : (AddMonoidAlgebra.single (0 : ℤ) r : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.C r := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
    have h00 : (AddMonoidHom.mulLeft (σ.e : ℤ)) 0 = (0 : ℤ) := mul_zero _
    rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, h00,
      hb, Ein_apply, LaurentPolynomial.eval₂_C]
  · intro m
    have hb1 : (AddMonoidAlgebra.single m (1 : ↥σ.K) : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.T m := by
      rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
    have h0m : (AddMonoidHom.mulLeft (σ.e : ℤ)) m = (σ.e : ℤ) * m := rfl
    have hb2 : (AddMonoidAlgebra.single ((σ.e : ℤ) * m) (1 : ↥σ.K) : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.T ((σ.e : ℤ) * m) := by
      rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
    rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, h0m,
      hb1, hb2, Ein_apply, LaurentPolynomial.eval₂_T, tUnit_zpow, tUnit_val]

theorem L2_coeffLoc (σ : Stage p F) (M : GenuineStageModel σ) : CoeffLocLaw σ := by
  refine ⟨?_, ?_, ?_⟩
  · -- (L^coeff)₀ ⊆ K, PROVED: transport along `Eout` (z ↦ z^e, T ↦ z^t).  Generators land in
    -- the inner constants (positions −t·ν against outer degrees e·ν cancel exactly); on an
    -- outer constant `C ℓ` the map is `mapDomain (e·)` of `ℓ`, injective by `he : 1 ≤ e`,
    -- so `ℓ` is itself a constant.  Stage laws only (hS5, hStretch, hreps, he); `M` unused.
    intro ℓ hℓ
    have hmem := coeffLoc_le σ hℓ
    rw [Subring.mem_comap, RingHom.mem_range] at hmem
    obtain ⟨d0, hd0⟩ := hmem
    have hEC : Eout σ (LaurentPolynomial.C ℓ) = Ein σ ℓ := by
      rw [Eout_apply, LaurentPolynomial.eval₂_C]
    have hd : Ein σ ℓ = LaurentPolynomial.C d0 := by rw [← hEC, ← hd0]
    -- rewrite the constant as a single at 0 and cancel the injective `mapDomain (e·)`
    have hs0 : (AddMonoidAlgebra.single (0 : ℤ) d0 : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.C d0 := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
    have hinj : Function.Injective (⇑(AddMonoidHom.mulLeft (σ.e : ℤ))) := by
      intro a b hab
      have he : (σ.e : ℤ) ≠ 0 :=
        Int.natCast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp σ.he)
      exact mul_left_cancel₀ he hab
    have hinj2 : Function.Injective
        (⇑(AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ)))) := by
      intro x y hxy
      refine AddMonoidAlgebra.mapDomain_injective hinj ?_
      simpa [AddMonoidAlgebra.mapDomainRingHom_apply] using hxy
    have h4 : (AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ))) ℓ
        = (AddMonoidAlgebra.mapDomainRingHom ↥σ.K (AddMonoidHom.mulLeft (σ.e : ℤ)))
            (AddMonoidAlgebra.single (0 : ℤ) d0) := by
      rw [← Ein_eq_mapDomainRingHom, hd, hs0, Ein_apply, LaurentPolynomial.eval₂_C]
    exact ⟨d0, by rw [hinj2 h4, hs0]⟩
  · -- (L^coeff)₀ ⊇ K: OPEN.  For `d ∈ Kˣ` one must realize `C (C d)` in the closure: an hS6b
    -- realizer at weight ν > wPrev Φ gives `C(C a·z^{−tν})·T^{eν}` with `a` free, and the
    -- rep-unit group cancels it iff `−ν ∈ ⟨wPrev(rep_i)⟩`.  That the rep weights reach some
    -- `−ν` with ν > wPrev Φ (informally: reps generate the parent value group, DEF-3/StageWF
    -- content) is NOT a `Stage` field, and `GenuineStageModel` (Θ, discharge, hT) does not
    -- force it: Θ-surjectivity produces preimages `grRes f · Θ(ιm)⁻¹` with `f` an ARBITRARY
    -- polynomial, not a rep-monomial.  Needs base/TRANS construction data.
    sorry
  · -- (P1) z-pinning: OPEN.  The unit equation for `zv = (v, v₂)` collapses (via hbez,
    -- gcd(e,h)=1, h ≥ 1) to: Σ v_i·wPrev(rep_i) = −h AND Π c_i^{v_i} = 1 (c_i the hS5 scalars
    -- of the reps), with v₂ = e forced.  Same gap as conjunct 2: a parent-weight-(−h)-reaching
    -- exponent vector with trivial scalar product is StageWF-type data (`reps_pinned` gives
    -- scalar 1; `p_is_rep` + Gauss weight give the weight), absent from `Stage`, and not
    -- recoverable from Θ: units of `Lo` are `ι[f]·ιm⁻¹` with `f` homogeneous but otherwise
    -- unconstrained, so `z = grRes f·Θ(ιm)⁻¹` never lands in the rep-generated lattice.
    sorry
