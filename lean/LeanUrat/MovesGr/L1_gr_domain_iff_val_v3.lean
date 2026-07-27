/-
MovesGr unit `L1_gr_domain_iff_val` (v3 — the option-(a) re-key; supersedes v2).
Statement byte-identical to `LeanUrat/MovesGr/MANIFEST.json`.

HISTORY: v2 PROVED the forward direction unconditionally and diagnosed the backward
direction as FALSE against the original 4-field `GradedRingStr` (nothing tied `Rg.ring`'s
addition/zero to the DirectSum's; transport counterexample in the v2 header). The §8.1
blueprint proposal, OPTION (a) SIGNED OFF by Asvin 2026-07-28, added the `add_def` field
(ring `+` componentwise = the DirectSum's). Under it the statement text is UNCHANGED and
the backward direction becomes the honest graded leading-term argument — this file.

PROOF SHAPE (backward): `add_def` pins the ring's `0`/`+` to the DirectSum's, so the
ring product is determined by biadditivity + `mul_of` on ALL of `Gr`: writing a bounded
element as an `AddSubmonoid.closure` of `of`-classes (support decomposition), the
`(top a + top b)`-component of `a * b` is exactly `pmul (a top) (b top)`
(`mul_component_top`). Nonzero top classes have representatives of weight EXACTLY their
degree, and `hval` makes their product's weight exact again, so the top component of a
product of nonzero elements is nonzero (`initialForm`-style class nonvanishing).

STATUS: FULLY PROVED, no sorry. Forward direction verbatim from v2.
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

namespace LeanUrat.MovesGr

/-- Inlined dep content (`L0_initialForm_ne_zero`): the initial form of a nonzero
element is nonzero. Stated OUTSIDE any `Rg.ring` scope: the `0` is the DirectSum zero. -/
private theorem if_ne_zero (S : SideVal p) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    S.initialForm f ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : S.Gr => x (S.deg f)) h
  simp only [SideVal.initialForm, DirectSum.of_eq_same, DirectSum.zero_apply] at h2
  simp only [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at h2
  have hlt : (S.deg f : WithTop ℤ) < S.w f := h2
  rw [S.deg_eq hf] at hlt
  exact lt_irrefl _ hlt

/-! ### The `add_def` bridges (§8.1 option (a), signed off 2026-07-28) -/

/-- ring `+` = DirectSum `+` (elementwise, from the componentwise `add_def`). -/
private lemma ring_add_eq (S : SideVal p) (Rg : GradedRingStr S) (x y : S.Gr) :
    (letI := Rg.ring; x + y) = x + y := by
  refine DFinsupp.ext fun γ => ?_
  rw [Rg.add_def]
  rfl

/-- degree-γ `of`-classes add through the ring's `+`. -/
private lemma of_add_of (S : SideVal p) (Rg : GradedRingStr S) (γ : ℤ) (a b : S.grPiece γ) :
    (letI := Rg.ring;
      DirectSum.of (fun δ => S.grPiece δ) γ a + DirectSum.of (fun δ => S.grPiece δ) γ b)
      = DirectSum.of (fun δ => S.grPiece δ) γ (a + b) :=
  (ring_add_eq S Rg _ _).trans ((DirectSum.of (fun δ => S.grPiece δ) γ).map_add a b).symm

/-- `of γ 0` is the RING zero (uniqueness of the additive identity, via `add_def`). -/
private lemma of_zero_ring (S : SideVal p) (Rg : GradedRingStr S) (γ : ℤ) :
    DirectSum.of (fun δ => S.grPiece δ) γ (0 : S.grPiece γ)
      = (letI := Rg.ring; (0 : S.Gr)) := by
  letI := Rg.ring
  have h1 := of_add_of S Rg γ 0 0
  rw [add_zero] at h1
  exact add_right_cancel (h1.trans (zero_add _).symm)

/-- the ring zero IS the DirectSum zero. -/
private lemma ring_zero_eq (S : SideVal p) (Rg : GradedRingStr S) :
    (letI := Rg.ring; (0 : S.Gr)) = 0 :=
  (of_zero_ring S Rg 0).symm.trans ((DirectSum.of (fun δ => S.grPiece δ) 0).map_zero)

/-- γ-bounded generators: homogeneous classes in degrees `≤ γ`. -/
private def genSet (S : SideVal p) (γ : ℤ) : Set S.Gr :=
  {z | ∃ i : ℤ, i ≤ γ ∧ ∃ c : S.grPiece i, z = DirectSum.of (fun δ => S.grPiece δ) i c}

/-- every γ-bounded element lies in the additive closure of the γ-bounded generators
(support decomposition — pure DirectSum, no ring). -/
private lemma mem_closure_of_bdd (S : SideVal p) (γ : ℤ) (x : S.Gr)
    (hx : ∀ i, γ < i → x i = 0) : x ∈ AddSubmonoid.closure (genSet S γ) := by
  classical
  rw [← DirectSum.sum_support_of x]
  refine sum_mem fun i hi => AddSubmonoid.subset_closure ?_
  exact ⟨i, not_lt.mp fun h => (DFinsupp.mem_support_iff.mp hi) (hx i h), x i, rfl⟩

/-- left distributivity of the ring product over a DirectSum-flavored sum. -/
private lemma mulr_addDS_left (S : SideVal p) (Rg : GradedRingStr S) {w x y : S.Gr}
    (h : w = x + y) (z : S.Gr) :
    (letI := Rg.ring; w * z) = (letI := Rg.ring; x * z + y * z) := by
  letI := Rg.ring
  rw [h.trans (ring_add_eq S Rg x y).symm, add_mul]

/-- right distributivity of the ring product over a DirectSum-flavored sum. -/
private lemma mulr_addDS_right (S : SideVal p) (Rg : GradedRingStr S) {w x y : S.Gr}
    (h : w = x + y) (z : S.Gr) :
    (letI := Rg.ring; z * w) = (letI := Rg.ring; z * x + z * y) := by
  letI := Rg.ring
  rw [h.trans (ring_add_eq S Rg x y).symm, mul_add]

/-- **single-left component formula**: for `i ≤ γ` and δ-bounded `y`,
`(of i c * y) (γ+δ) = pmul γ δ ((of i c) γ) (y δ)`. -/
private lemma mul_of_component (S : SideVal p) (Rg : GradedRingStr S)
    (γ δ i : ℤ) (hi : i ≤ γ) (c : S.grPiece i) (y : S.Gr)
    (hy : y ∈ AddSubmonoid.closure (genSet S δ)) :
    (letI := Rg.ring; DirectSum.of (fun ε => S.grPiece ε) i c * y) (γ + δ)
      = S.pmul γ δ ((DirectSum.of (fun ε => S.grPiece ε) i c) γ) (y δ) := by
  letI := Rg.ring
  induction hy using AddSubmonoid.closure_induction with
  | mem z hz =>
      obtain ⟨j, hj, d, rfl⟩ := hz
      rw [Rg.mul_of i j c d]
      by_cases hii : i = γ
      · subst hii
        by_cases hjj : j = δ
        · subst hjj
          rw [DirectSum.of_eq_same, DirectSum.of_eq_same, DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne _ _ _ (by omega : i + δ ≠ i + j),
            DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjj), map_zero]
      · rw [DirectSum.of_eq_of_ne _ _ _ (by omega : γ + δ ≠ i + j),
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm hii), map_zero, LinearMap.zero_apply]
  | zero =>
      rw [DirectSum.zero_apply, map_zero, ← ring_zero_eq S Rg, mul_zero, ring_zero_eq S Rg,
        DirectSum.zero_apply]
  | add x1 x2 hx1c hx2c ih1 ih2 =>
      rw [mulr_addDS_right S Rg rfl _, Rg.add_def, ih1, ih2, DirectSum.add_apply,
        map_add]

/-- **top-component formula**: for γ-bounded `x` and δ-bounded `y`,
`(x * y) (γ+δ) = pmul γ δ (x γ) (y δ)` — the ring product is the biadditive extension of
`pmul`, pinned by `add_def` + `mul_of`. -/
private lemma mul_component_top (S : SideVal p) (Rg : GradedRingStr S) (γ δ : ℤ) (x y : S.Gr)
    (hxb : ∀ i, γ < i → x i = 0) (hyb : ∀ j, δ < j → y j = 0) :
    (letI := Rg.ring; x * y) (γ + δ) = S.pmul γ δ (x γ) (y δ) := by
  letI := Rg.ring
  have hyc := mem_closure_of_bdd S δ y hyb
  have hxc := mem_closure_of_bdd S γ x hxb
  clear hxb hyb
  induction hxc using AddSubmonoid.closure_induction with
  | mem z hz =>
      obtain ⟨i, hi, c, rfl⟩ := hz
      exact mul_of_component S Rg γ δ i hi c y hyc
  | zero =>
      rw [DirectSum.zero_apply, map_zero, LinearMap.zero_apply, ← ring_zero_eq S Rg, zero_mul,
        ring_zero_eq S Rg, DirectSum.zero_apply]
  | add x1 x2 hx1c hx2c ih1 ih2 =>
      rw [mulr_addDS_left S Rg rfl y, Rg.add_def, ih1, ih2, DirectSum.add_apply,
        map_add (S.pmul γ δ), LinearMap.add_apply]

theorem L1_gr_domain_iff_val (S : SideVal p) (Rg : GradedRingStr S) : (letI := Rg.ring; IsDomain S.Gr) ↔ (∀ f g, f ≠ 0 → g ≠ 0 → S.w (f * g) = S.w f + S.w g) := by
  letI := Rg.ring
  constructor
  · -- (⟹). In fact unconditional: `if_mul` + `mul_of` + degree-injectivity of `of`
    -- (verbatim from v2, where it was already machine-checked).
    intro _hdom f g hf hg
    have hfg : f * g ≠ 0 := mul_ne_zero hf hg
    have heq : DirectSum.of (fun γ => S.grPiece γ) (S.deg (f * g)) (S.mkPiece (f * g))
        = DirectSum.of (fun γ => S.grPiece γ) (S.deg f + S.deg g)
            (S.pmul (S.deg f) (S.deg g) (S.mkPiece f) (S.mkPiece g)) :=
      (Rg.if_mul f g hf hg).trans (Rg.mul_of _ _ _ _)
    have hdeg : S.deg (f * g) = S.deg f + S.deg g := by
      by_contra hne
      have hcomp := congrArg (fun x : S.Gr => x (S.deg (f * g))) heq
      simp only [DirectSum.of_eq_same] at hcomp
      rw [DirectSum.of_eq_of_ne (S.deg f + S.deg g) (S.deg (f * g)) _ hne] at hcomp
      simp only [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at hcomp
      have hlt : (S.deg (f * g) : WithTop ℤ) < S.w (f * g) := hcomp
      rw [S.deg_eq hfg] at hlt
      exact lt_irrefl _ hlt
    have hcast : (↑(S.deg (f * g)) : WithTop ℤ) = ↑(S.deg f) + ↑(S.deg g) := by
      rw [hdeg, WithTop.coe_add]
    rw [S.deg_eq hfg, S.deg_eq hf, S.deg_eq hg] at hcast
    exact hcast
  · -- (⟸). The graded leading-term argument, honest under `add_def` (option (a)).
    intro hval
    haveI hnt : Nontrivial S.Gr := nontrivial_of_ne _ _ (if_ne_zero S one_ne_zero)
    haveI hnzd : NoZeroDivisors S.Gr :=
      { eq_zero_or_eq_zero_of_mul_eq_zero := by
          intro a b hab
          by_contra hcon
          push Not at hcon
          obtain ⟨ha, hb⟩ := hcon
          classical
          have hzz := ring_zero_eq S Rg
          have hsa : (DFinsupp.support a).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            exact ha ((DFinsupp.support_eq_empty.mp hemp).trans hzz.symm)
          have hsb : (DFinsupp.support b).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            exact hb ((DFinsupp.support_eq_empty.mp hemp).trans hzz.symm)
          set γa := (DFinsupp.support a).max' hsa with hγa
          set γb := (DFinsupp.support b).max' hsb with hγb
          have hbnd_a : ∀ i, γa < i → a i = 0 := by
            intro i hi
            by_contra hne
            exact absurd (Finset.le_max' _ i (DFinsupp.mem_support_iff.mpr hne)) (not_le.mpr hi)
          have hbnd_b : ∀ j, γb < j → b j = 0 := by
            intro j hj
            by_contra hne
            exact absurd (Finset.le_max' _ j (DFinsupp.mem_support_iff.mpr hne)) (not_le.mpr hj)
          have htop_a : a γa ≠ 0 :=
            DFinsupp.mem_support_iff.mp ((DFinsupp.support a).max'_mem hsa)
          have htop_b : b γb ≠ 0 :=
            DFinsupp.mem_support_iff.mp ((DFinsupp.support b).max'_mem hsb)
          have hcomp := mul_component_top S Rg γa γb a b hbnd_a hbnd_b
          obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective (S.gtIn γa) (a γa)
          obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective (S.gtIn γb) (b γb)
          have hwu_le : S.w (u : Polynomial ℤ_[p]) ≤ (γa : WithTop ℤ) := by
            by_contra hlt
            exact htop_a (by rw [← hu, Submodule.Quotient.mk_eq_zero]; exact not_le.mp hlt)
          have hwv_le : S.w (v : Polynomial ℤ_[p]) ≤ (γb : WithTop ℤ) := by
            by_contra hlt
            exact htop_b (by rw [← hv, Submodule.Quotient.mk_eq_zero]; exact not_le.mp hlt)
          have hwu : S.w (u : Polynomial ℤ_[p]) = (γa : WithTop ℤ) := le_antisymm hwu_le u.2
          have hwv : S.w (v : Polynomial ℤ_[p]) = (γb : WithTop ℤ) := le_antisymm hwv_le v.2
          have hu0 : (u : Polynomial ℤ_[p]) ≠ 0 := by
            intro h0
            rw [h0, S.w_zero] at hwu
            exact WithTop.top_ne_coe hwu
          have hv0 : (v : Polynomial ℤ_[p]) ≠ 0 := by
            intro h0
            rw [h0, S.w_zero] at hwv
            exact WithTop.top_ne_coe hwv
          have hne2 : S.pmul γa γb (a γa) (b γb) ≠ 0 := by
            rw [← hu, ← hv]
            intro h0
            rw [show S.pmul γa γb (Submodule.Quotient.mk u) (Submodule.Quotient.mk v)
                = Submodule.Quotient.mk (S.mulToGe γa γb u v) from rfl,
              Submodule.Quotient.mk_eq_zero] at h0
            have hlt : ((γa + γb : ℤ) : WithTop ℤ)
                < S.w ((u : Polynomial ℤ_[p]) * (v : Polynomial ℤ_[p])) := h0
            rw [hval _ _ hu0 hv0, hwu, hwv, ← WithTop.coe_add] at hlt
            exact lt_irrefl _ hlt
          have hcz : (letI := Rg.ring; a * b) (γa + γb) = 0 := by
            have h1 : (letI := Rg.ring; a * b) = (letI := Rg.ring; (0 : S.Gr)) := hab
            rw [h1, hzz]
            simp
          exact hne2 (hcomp.symm.trans hcz) }
    exact NoZeroDivisors.to_isDomain _

end LeanUrat.MovesGr

#print axioms LeanUrat.MovesGr.L1_gr_domain_iff_val
