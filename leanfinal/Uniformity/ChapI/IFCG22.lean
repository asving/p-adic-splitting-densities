/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG21
import Uniformity.ChapH.H107

/-!
# Uniformity.ChapI.IFCG22 — [CN01 2026-08-30] cone census stages CN0 + CN1:
translation symmetry and the class-level Newton polygon

ECONE (`IFCG21.lean`) reduced the census front to the two cone laws and charged the
follow-up fleet stage by stage (`runs/wave-c/verdict_ECONE.md` §BLUEPRINT).  This file is
the mechanical prefix — stages CN0 and CN1:

* **§1 CN0 (translation symmetry), PROVED.**  `coneCellCount_translation`: the centred
  cone count is the SAME at every centre.  The mechanism: recentring by the canonical
  shift `w := resSect O γ' − resSect O γ` (H.123a's `recentreClass`) transports all three
  constituents of the cone cell — decidedness (`decidedAt_recentreClass`), the stratum
  (`(X+Cγ)^m ∘ (X+C w̄) = (X+Cγ')^m`), and the full recentering range EXACTLY and
  box-preservingly (`recentreClass_fullLoopClassN`: the blueprint's anticipated
  "triangular unit-diagonal action on mixed boxes" collapses to the identity on boxes,
  because the canonical lifts compose on the nose: `resSect γ + w = resSect γ'`).
  Payoff: `ZeroConeLaw` — the centred cone law at the SINGLE centre `0` — with
  `centeredConeLaw_iff_zeroCone : CenteredConeLaw ↔ ZeroConeLaw`; centre-uniformity is
  now DERIVED, not assumed.
* **§2 CN1 (class-level Newton data), PROVED in its class-stable region.**
  `classCoeffVal c i := resOrd (c i)` — H.107's LANDED windowed valuation, coordinatewise;
  its lift semantics (`le_classCoeffVal_iff_dvd`, `classCoeffVal_exact`) say: below the
  window the valuation of EVERY lift is pinned, at the window (`= N`) it is only
  "≥ N, invisible".  The class Newton polygon is encoded by its integer support function
  `classNPSupport c h e'` = min over the `m+1` marked points `(i, v_i)` (monic point
  `(m, 0)` included) of `e'·v_i + h·i` — the standard Legendre/support encoding of the
  lower hull, convexity-free and faithful (faces of slope `−h/e'` = the min attained
  twice, `ClassNPFace`).  THE WELL-DEFINEDNESS THEOREM (`classNP_lift_eq`,
  `classNPFace_lift_iff`): in the region **strictly below the frame floor**
  (`NPVisibleAt`: `classNPSupport c h e' < e'·N`), the support value, the attainment set,
  and the faces of EVERY lift — read at ANY window `K ≥ N` — equal those of the class.
  Engine: the refinement min-law `resOrd_resFactor : resOrd (resFactor h x) = min N (resOrd x)`.

## ⚠ What is NOT class-stable (the honest fence — CN2's subject, not leaked into)

At or above the floor (`classNPSupport c h e' ≥ e'·N`) the polygon is NOT class-stable:
`npSupport_not_stable_at_floor` PROVES the boundary sharp — over every DVR, the zero
class at `m = 2, N = 1` (support `= e'·N` exactly) has two lifts `(π,π)` and `(π³,π³)`
whose window-3 supports differ (`1 ≠ 2`).  The at-or-above-floor part of the polygon —
equivalently the classes whose visible polygon still touches the precision ceiling — is
exactly the deep/undecided boundary that stage CN2's decidedness criterion must dissect;
NOTHING here decides a type or counts a stratum.  Both cone laws stay OPEN.

## Signature deltas vs the ECONE blueprint (recorded per charge)

* CN0's `coneCellCount_translation (γ γ')` gained the forced hypotheses
  `(hπ : Irreducible π)` (the class machinery is π-pinned) and `(hm : 1 ≤ m)`
  (the stratum iff needs level `≥ 1`); all consumption sites have `4 ≤ m`.
* CN1's `classNP` is realized as the support-function encoding `classNPSupport`
  (+ `NPAttains`/`ClassNPFace`); `classNP_lift_eq`'s "when visible" is made precise as
  the strict floor criterion `NPVisibleAt` — provably sharp (see the fence above).
  `classCoeffVal` needs no `π` argument (H.107's `resOrd` is ideal-theoretic).

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG22

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG1 (MBoxN shiftVecN shiftVecN_add shiftVecN_zero
  monicPoly_shiftVecN)
open Uniformity.Density.IFCG3 (loopMapN loopVecN)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG20 (fullLoopClassN DeepFractionalCellLaw)
open Uniformity.Density.IFCG21 (coneCellCount CenteredConeLaw)

attribute [local instance] Classical.propDecidable

/-! ## §1 — CN0: the translation symmetry of the cone counts -/

section CN0

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The canonical centre shift `resSect O γ' − resSect O γ` lifts `γ' − γ`. -/
theorem residue_resSect_sub (γ γ' : ResidueField O) :
    residue O (resSect O γ' - resSect O γ) = γ' - γ := by
  rw [map_sub, residue_resSect, residue_resSect]

/-- **CN0, stratum leg**: recentring at the canonical centre shift carries the stratum of
`(X + Cγ)^m` into the stratum of `(X + Cγ')^m` — the reduction of the recentred lift is
`((X + Cγ)^m)(X + C(γ' − γ)) = (X + Cγ')^m`. -/
theorem recentreClass_mem_stratum {π : O} (hπ : Irreducible π) {m N : ℕ} (hN : 1 ≤ N)
    {γ γ' : ResidueField O} {c : Coeff O m N}
    (hc : c ∈ levelZeroStratum O m N ((X + C γ) ^ m)) :
    recentreClass O m N (resSect O γ' - resSect O γ) c
      ∈ levelZeroStratum O m N ((X + C γ') ^ m) := by
  obtain ⟨a, ha, hres⟩ := (mem_levelZeroStratum_iff hN _ c).1 hc
  refine (mem_levelZeroStratum_iff hN _ _).2
    ⟨recentreVec a (resSect O γ' - resSect O γ), proj_recentreVec hπ ha _, ?_⟩
  have hkey : ((X : Polynomial (ResidueField O)) + C (γ' - γ) + C γ) = X + C γ' := by
    rw [add_assoc, ← C_add, sub_add_cancel]
  rw [monicPoly_recentreVec, Polynomial.map_comp, hres, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, residue_resSect_sub, pow_comp, add_comp,
    X_comp, C_comp, hkey]

/-- **CN0, range leg (the key exact commutation)**: recentring at the canonical centre
shift carries the centre-`γ` full recentering range to the centre-`γ'` one WITH THE SAME
BOX — the blueprint's anticipated box action is the identity, because
`resSect γ + (resSect γ' − resSect γ) = resSect γ'` on the nose. -/
theorem recentreClass_fullLoopClassN {π : O} (hπ : Irreducible π) {m M : ℕ}
    (γ γ' : ResidueField O) (d : MBoxN O m M) :
    recentreClass O m (M + m) (resSect O γ' - resSect O γ) (fullLoopClassN π (γ, d))
      = fullLoopClassN π (γ', d) := by
  have h1 : proj O m (M + m) (recentreVec (loopMapN γ π d) (resSect O γ' - resSect O γ))
      = recentreClass O m (M + m) (resSect O γ' - resSect O γ) (fullLoopClassN π (γ, d)) :=
    proj_recentreVec hπ rfl _
  rw [← h1]
  have h2 : recentreVec (loopMapN γ π d) (resSect O γ' - resSect O γ) = loopMapN γ' π d := by
    show shiftVecN (shiftVecN (loopVecN π d) (resSect O γ)) (resSect O γ' - resSect O γ)
      = shiftVecN (loopVecN π d) (resSect O γ')
    rw [shiftVecN_add]
    have h3 : resSect O γ + (resSect O γ' - resSect O γ) = resSect O γ' := by ring
    rw [h3]
  rw [h2]
  rfl

/-- **CN0, the set transport**: recentring at the canonical centre shift maps the
centre-`γ` cone cell into the centre-`γ'` cone cell. -/
theorem recentreClass_mem_coneSet {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 1 ≤ m)
    {σ : FactorizationType} {M : ℕ} {γ γ' : ResidueField O} {c : Coeff O m (M + m)}
    (hc : c ∈ (decidedSet O m σ (M + m)
        ∩ levelZeroStratum O m (M + m) ((X + C γ) ^ m))
      \ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d))) :
    recentreClass O m (M + m) (resSect O γ' - resSect O γ) c
      ∈ (decidedSet O m σ (M + m)
          ∩ levelZeroStratum O m (M + m) ((X + C γ') ^ m))
        \ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ', d)) := by
  obtain ⟨⟨hdec, hstrat⟩, hrange⟩ := hc
  refine ⟨⟨decidedAt_recentreClass hπ _ hdec,
    recentreClass_mem_stratum hπ (by omega) hstrat⟩, ?_⟩
  rintro ⟨d, hd⟩
  refine hrange ⟨d, ?_⟩
  have h2 := congrArg (recentreClass O m (M + m) (-(resSect O γ' - resSect O γ))) hd
  rw [recentreClass_recentreClass hπ, neg_sub,
    recentreClass_fullLoopClassN hπ γ' γ d] at h2
  exact h2

/-- ★ **CN0 — THE TRANSLATION SYMMETRY** (blueprint signature, hypotheses recorded as
deltas): the centred cone count is centre-independent.  Injection both ways by the class
recentring at the canonical centre shifts. -/
theorem coneCellCount_translation {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 1 ≤ m)
    (σ : FactorizationType) (M : ℕ) (γ γ' : ResidueField O) :
    coneCellCount O π m σ M γ = coneCellCount O π m σ M γ' := by
  have key : ∀ δ δ' : ResidueField O,
      coneCellCount O π m σ M δ ≤ coneCellCount O π m σ M δ' := fun δ δ' =>
    Nat.card_le_card_of_injective
      (fun c => ⟨recentreClass O m (M + m) (resSect O δ' - resSect O δ) c.1,
        recentreClass_mem_coneSet hπ hm c.2⟩)
      (fun c c' h =>
        Subtype.ext (recentreClass_injective hπ _ (congrArg Subtype.val h)))
  exact le_antisymm (key γ γ') (key γ' γ)

/-- ★ **THE SINGLE-CENTRE CONE LAW** — `CenteredConeLaw` with the centre pinned to `0`:
the ONE remaining fractional-cell obligation after CN0.  Verbatim the kernel's
conditional shape. -/
def ZeroConeLaw : Prop :=
  ∀ m : ℕ, 4 ≤ m →
    (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
    ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
      ∃ n d : Polynomial ℚ, d ≠ 0 ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
          [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
          d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
            ∀ π : O, Irreducible π →
              Filter.Tendsto
                (fun M => (coneCellCount O π m σ M 0 : ℝ)
                  / (residueCard O : ℝ) ^ (m * (M + m)))
                Filter.atTop
                (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
                  / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

theorem zeroConeLaw_of_centered (h : CenteredConeLaw) : ZeroConeLaw := by
  intro m hm hsm σ hσ hwit
  obtain ⟨n, d, hd, hval⟩ := h m hm hsm σ hσ hwit
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  exact ⟨hne, fun π hπ => hlim π hπ 0⟩

/-- ★★ **CN0's PAYOFF**: the single-centre law fires the centre-uniform law — the count
at every centre IS the count at `0` (`coneCellCount_translation`), so one pair serves all
centres.  Centre-uniformity is derived, never assumed. -/
theorem centeredConeLaw_of_zeroCone (h : ZeroConeLaw) : CenteredConeLaw := by
  intro m hm hsm σ hσ hwit
  obtain ⟨n, d, hd, hval⟩ := h m hm hsm σ hσ hwit
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  refine ⟨hne, ?_⟩
  intro π hπ γ
  refine (hlim π hπ).congr fun M => ?_
  rw [coneCellCount_translation hπ (by omega) σ M 0 γ]

/-- ★★ The census front's fractional-cell obligation, CN0-reduced: centre-uniform ↔
single-centre. -/
theorem centeredConeLaw_iff_zeroCone : CenteredConeLaw ↔ ZeroConeLaw :=
  ⟨zeroConeLaw_of_centered, centeredConeLaw_of_zeroCone⟩

end CN0

/-! ## §2 — CN1: the class-level Newton polygon -/

section CN1

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **CN1 (blueprint signature)**: the class coefficient valuation — H.107's windowed
(conservative) valuation, coordinatewise.  `classCoeffVal c i = N` means INVISIBLE
(`c i = 0` in the window), never "valuation exactly `N`". -/
def classCoeffVal {m N : ℕ} (c : Coeff O m N) (i : Fin m) : ℕ := resOrd (c i)

theorem classCoeffVal_le {m N : ℕ} (c : Coeff O m N) (i : Fin m) :
    classCoeffVal c i ≤ N := resOrd_le _

/-- **The lift semantics** (the class invariance of the visible valuations): for `k ≤ N`,
`k ≤ classCoeffVal c i` iff `π^k` divides the `i`-th coefficient of EVERY (equivalently,
any) lift. -/
theorem le_classCoeffVal_iff_dvd {π : O} (hπ : Irreducible π) {m N k : ℕ} (hk : k ≤ N)
    {a : Fin m → O} {c : Coeff O m N} (ha : proj O m N a = c) (i : Fin m) :
    k ≤ classCoeffVal c i ↔ π ^ k ∣ a i := by
  subst ha
  exact resOrd_ge_iff hπ hk (a i)

/-- **Visibility is exactness**: a class valuation `< N` is the exact `π`-valuation of
every lift's coefficient. -/
theorem classCoeffVal_exact {π : O} (hπ : Irreducible π) {m N : ℕ}
    {a : Fin m → O} {c : Coeff O m N} (ha : proj O m N a = c) {i : Fin m}
    (hvis : classCoeffVal c i < N) :
    π ^ classCoeffVal c i ∣ a i ∧ ¬ π ^ (classCoeffVal c i + 1) ∣ a i := by
  refine ⟨(le_classCoeffVal_iff_dvd hπ (classCoeffVal_le c i) ha i).1 le_rfl,
    fun hdvd => ?_⟩
  have h2 := (le_classCoeffVal_iff_dvd hπ (by omega) ha i).2 hdvd
  omega

/-- **Invisibility** (H.107 clause ii, coordinatewise): the top value means the
coordinate vanishes in the window. -/
theorem classCoeffVal_eq_iff {m N : ℕ} (c : Coeff O m N) (i : Fin m) :
    classCoeffVal c i = N ↔ c i = 0 := resOrd_eq_iff _

/-- **The refinement min-law** — CN1's engine: truncating a finer class caps the windowed
valuation at the coarser window. -/
theorem resOrd_resFactor {N K : ℕ} (hNK : N ≤ K) (x : Res O K) :
    resOrd (resFactor (O := O) hNK x) = min N (resOrd x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [resFactor_mk]
  refine le_antisymm (le_min (resOrd_le _) ?_) ?_
  · exact (resOrd_ge_iff hπ (le_trans (resOrd_le _) hNK) y).2
      ((resOrd_ge_iff hπ (resOrd_le _) y).1 le_rfl)
  · refine (resOrd_ge_iff hπ (min_le_left _ _) y).2 ?_
    exact (resOrd_ge_iff hπ (le_trans (min_le_left _ _) hNK) y).1 (min_le_right _ _)

/-- Computation rule for the windowed valuation: exact divisibility data pins `resOrd`
(the `v = K` alternative is the at-window case, where no exactness is required). -/
theorem resOrd_mk_eq {π : O} (hπ : Irreducible π) {K v : ℕ} (hvK : v ≤ K) {x : O}
    (hd : π ^ v ∣ x) (hnd : v = K ∨ ¬ π ^ (v + 1) ∣ x) :
    resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ K) x) = v := by
  refine le_antisymm ?_ ((resOrd_ge_iff hπ hvK x).2 hd)
  by_contra hlt
  rw [not_le] at hlt
  have hle := resOrd_le (Ideal.Quotient.mk ((maximalIdeal O) ^ K) x)
  rcases hnd with rfl | hnd
  · omega
  · exact hnd ((resOrd_ge_iff (N := K) hπ (by omega) x).1 (by omega))

/-- The NP height function of a class: the windowed valuations, with the monic marked
point `(m, 0)` appended (and junk `0` beyond `m` — never consumed: all reads are on
`Finset.range (m+1)`). -/
def npHeight {m N : ℕ} (c : Coeff O m N) (i : ℕ) : ℕ :=
  if h : i < m then classCoeffVal c ⟨i, h⟩ else 0

/-- **CN1 (blueprint's `classNP`)** — the class Newton polygon, support-function
encoding: at integer slope data `(h, e')` (representing the rational slope `h/e'`), the
minimum over the `m+1` marked points `(i, v_i)` of `e'·v_i + h·i`.  The lower convex hull
is the Legendre transform of this function, so the polygon IS this data; a FACE of slope
`−h/e'` is the min attained at two abscissae (`ClassNPFace`). -/
def classNPSupport {m N : ℕ} (c : Coeff O m N) (h e' : ℕ) : ℕ :=
  (Finset.range (m + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun i => e' * npHeight c i + h * i)

/-- The support is a lower bound on every marked point's value. -/
theorem classNPSupport_le_apply {m N : ℕ} (c : Coeff O m N) (h e' : ℕ) {i : ℕ}
    (hi : i ≤ m) : classNPSupport c h e' ≤ e' * npHeight c i + h * i :=
  Finset.inf'_le _ (Finset.mem_range_succ_iff.mpr hi)

/-- Uniform lower bounds pass to the support. -/
theorem le_classNPSupport {m N : ℕ} {c : Coeff O m N} {h e' a : ℕ}
    (hb : ∀ i, i ≤ m → a ≤ e' * npHeight c i + h * i) : a ≤ classNPSupport c h e' :=
  Finset.le_inf' _ _ fun i hi => hb i (Finset.mem_range_succ_iff.mp hi)

/-- The monic point caps the support: `classNPSupport ≤ h·m`. -/
theorem classNPSupport_le {m N : ℕ} (c : Coeff O m N) (h e' : ℕ) :
    classNPSupport c h e' ≤ h * m := by
  refine le_trans (classNPSupport_le_apply c h e' (le_refl m)) ?_
  simp [npHeight]

/-- The abscissa `i` attains the support minimum. -/
def NPAttains {m N : ℕ} (c : Coeff O m N) (h e' : ℕ) (i : ℕ) : Prop :=
  i ≤ m ∧ e' * npHeight c i + h * i = classNPSupport c h e'

/-- **The class NP has a face of slope `−h/e'`**: the support minimum is attained at two
distinct abscissae (their segment lies on the lower hull with exactly that slope). -/
def ClassNPFace {m N : ℕ} (c : Coeff O m N) (h e' : ℕ) : Prop :=
  ∃ i j : ℕ, i < j ∧ NPAttains c h e' i ∧ NPAttains c h e' j

/-- The support minimum is attained. -/
theorem exists_npAttains {m N : ℕ} (c : Coeff O m N) (h e' : ℕ) :
    ∃ i, NPAttains c h e' i := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun i => e' * npHeight c i + h * i)
  exact ⟨j, Finset.mem_range_succ_iff.mp hj, hjeq.symm⟩

/-- **The frame-floor visibility criterion**: the support value sits STRICTLY below the
precision ceiling `e'·N`.  This is the class-stable region (`classNP_lift_eq`); it is
sharp (`npSupport_not_stable_at_floor`). -/
def NPVisibleAt {m N : ℕ} (c : Coeff O m N) (h e' : ℕ) : Prop :=
  classNPSupport c h e' < e' * N

/-- Heights refine by the min-law: for a level-`K` refinement `c'` of `c` (`K ≥ N`),
every height of `c` is the `N`-capped height of `c'` — uniformly in `i` (the monic point
gives `min N 0 = 0`). -/
theorem npHeight_refine {m N K : ℕ} (hNK : N ≤ K) {c : Coeff O m N} {c' : Coeff O m K}
    (href : ∀ i, resFactor (O := O) hNK (c' i) = c i) (i : ℕ) :
    npHeight c i = min N (npHeight c' i) := by
  unfold npHeight
  by_cases hi : i < m
  · rw [dif_pos hi, dif_pos hi]
    show classCoeffVal c ⟨i, hi⟩ = min N (classCoeffVal c' ⟨i, hi⟩)
    rw [classCoeffVal, classCoeffVal, ← href ⟨i, hi⟩, resOrd_resFactor hNK]
  · rw [dif_neg hi, dif_neg hi, Nat.min_zero]

/-- Refinement can only raise the support. -/
theorem classNPSupport_le_refine {m N K : ℕ} (hNK : N ≤ K) {c : Coeff O m N}
    {c' : Coeff O m K} (href : ∀ i, resFactor (O := O) hNK (c' i) = c i) (h e' : ℕ) :
    classNPSupport c h e' ≤ classNPSupport c' h e' := by
  obtain ⟨j, hjm, hjeq⟩ := exists_npAttains c' h e'
  rw [← hjeq]
  refine le_trans (classNPSupport_le_apply c h e' hjm) ?_
  have hmin := npHeight_refine hNK href j
  have hle : npHeight c j ≤ npHeight c' j := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left e' hle) _

/-- ★ **CN1, support stability below the floor**: a refinement's support EQUALS the class
support whenever the class support is strictly below the floor. -/
theorem classNPSupport_refine_eq {m N K : ℕ} (hNK : N ≤ K) {c : Coeff O m N}
    {c' : Coeff O m K} (href : ∀ i, resFactor (O := O) hNK (c' i) = c i) {h e' : ℕ}
    (hfloor : NPVisibleAt c h e') :
    classNPSupport c' h e' = classNPSupport c h e' := by
  have hfl : classNPSupport c h e' < e' * N := hfloor
  refine le_antisymm ?_ (classNPSupport_le_refine hNK href h e')
  obtain ⟨j, hjm, hjeq⟩ := exists_npAttains c h e'
  have hjvis : npHeight c j < N := by
    have h2 : e' * npHeight c j < e' * N := by omega
    exact Nat.lt_of_mul_lt_mul_left h2
  have hmin := npHeight_refine hNK href j
  have heq : npHeight c' j = npHeight c j := by omega
  refine le_trans (classNPSupport_le_apply c' h e' hjm) ?_
  rw [heq, hjeq]

/-- ★ **CN1, attainment stability below the floor**: the attainment set of every
refinement equals that of the class. -/
theorem npAttains_refine_iff {m N K : ℕ} (hNK : N ≤ K) {c : Coeff O m N}
    {c' : Coeff O m K} (href : ∀ i, resFactor (O := O) hNK (c' i) = c i) {h e' : ℕ}
    (hfloor : NPVisibleAt c h e') (i : ℕ) :
    NPAttains c' h e' i ↔ NPAttains c h e' i := by
  have hfl : classNPSupport c h e' < e' * N := hfloor
  have hsup := classNPSupport_refine_eq hNK href hfloor
  have hmin := npHeight_refine hNK href i
  constructor
  · rintro ⟨him, heq⟩
    refine ⟨him, ?_⟩
    have hvis' : npHeight c' i < N := by
      refine Nat.lt_of_mul_lt_mul_left (a := e') ?_
      omega
    have heqh : npHeight c i = npHeight c' i := by omega
    rw [heqh]
    omega
  · rintro ⟨him, heq⟩
    refine ⟨him, ?_⟩
    have hvis : npHeight c i < N := by
      refine Nat.lt_of_mul_lt_mul_left (a := e') ?_
      omega
    have heqh : npHeight c' i = npHeight c i := by omega
    rw [heqh]
    omega

/-- ★ **CN1, face stability below the floor**. -/
theorem classNPFace_refine_iff {m N K : ℕ} (hNK : N ≤ K) {c : Coeff O m N}
    {c' : Coeff O m K} (href : ∀ i, resFactor (O := O) hNK (c' i) = c i) {h e' : ℕ}
    (hfloor : NPVisibleAt c h e') :
    ClassNPFace c' h e' ↔ ClassNPFace c h e' := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨i, j, hij, (npAttains_refine_iff hNK href hfloor i).1 hi,
      (npAttains_refine_iff hNK href hfloor j).1 hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨i, j, hij, (npAttains_refine_iff hNK href hfloor i).2 hi,
      (npAttains_refine_iff hNK href hfloor j).2 hj⟩

/-- ★★ **CN1 (blueprint signature `classNP_lift_eq`)**: below the floor, EVERY lift's
Newton polygon — read at ANY window `K ≥ N` — has the class's support value.  (The lift's
window-`K` polygon is the class polygon of its level-`K` class; as `K` grows past every
coefficient valuation this IS the lift's true polygon.) -/
theorem classNP_lift_eq {m N K : ℕ} (hNK : N ≤ K) {a : Fin m → O} {c : Coeff O m N}
    (ha : proj O m N a = c) {h e' : ℕ} (hfloor : NPVisibleAt c h e') :
    classNPSupport (proj O m K a) h e' = classNPSupport c h e' := by
  refine classNPSupport_refine_eq hNK (fun i => ?_) hfloor
  rw [← ha]
  exact resFactor_mk hNK (a i)

/-- ★★ **CN1, the face form**: below the floor, every lift's faces at every window are
the class faces. -/
theorem classNPFace_lift_iff {m N K : ℕ} (hNK : N ≤ K) {a : Fin m → O} {c : Coeff O m N}
    (ha : proj O m N a = c) {h e' : ℕ} (hfloor : NPVisibleAt c h e') :
    ClassNPFace (proj O m K a) h e' ↔ ClassNPFace c h e' := by
  refine classNPFace_refine_iff hNK (fun i => ?_) hfloor
  rw [← ha]
  exact resFactor_mk hNK (a i)

/-- **The cone glue**: every class of the level-`N` stratum of `X^m` has all visible
valuations `≥ 1` — the marked points of the CN1 polygon start above the axis, exactly
the cone-dissection shape CN2 consumes (centres `≠ 0` reduce to this via CN0). -/
theorem one_le_classCoeffVal_of_mem_stratum {m N : ℕ} (hN : 1 ≤ N) {c : Coeff O m N}
    (hc : c ∈ levelZeroStratum O m N (X ^ m)) (i : Fin m) :
    1 ≤ classCoeffVal c i := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a, ha, hres⟩ := (mem_levelZeroStratum_iff hN _ c).1 hc
  refine (le_classCoeffVal_iff_dvd hπ hN ha i).2 ?_
  rw [pow_one]
  have h0 : residue O (a i) = 0 := by
    have hcoeff := congrArg (fun p => Polynomial.coeff p (i : ℕ)) hres
    simp only [Polynomial.coeff_map] at hcoeff
    rw [monicPoly_coeff_lt a i.isLt, Polynomial.coeff_X_pow,
      if_neg (Nat.ne_of_lt i.isLt)] at hcoeff
    simpa using hcoeff
  have hmem : a i ∈ (maximalIdeal O) ^ 1 := by
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hdvd := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 (a i)).1 hmem
  rwa [pow_one] at hdvd

/-- ⚠ **THE FLOOR IS SHARP** (the honest fence; the at-or-above-floor polygon is CN2's
subject): over EVERY DVR, the zero class at `m = 2, N = 1` has support exactly `e'·N`
at slope data `(1,1)`, and two of its lifts — `(π, π)` and `(π³, π³)` — have DIFFERENT
window-`3` supports (`1 ≠ 2`).  Nothing at or above the floor is class-stable. -/
theorem npSupport_not_stable_at_floor {π : O} (hπ : Irreducible π) :
    ∃ a a' : Fin 2 → O, proj O 2 1 a = proj O 2 1 a' ∧
      classNPSupport (proj O 2 1 a) 1 1 = 1 * 1 ∧
      classNPSupport (proj O 2 3 a) 1 1 ≠ classNPSupport (proj O 2 3 a') 1 1 := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  -- exactness of the valuation of π itself
  have hnd2 : ¬ π ^ 2 ∣ π := by
    rintro ⟨t, ht⟩
    have h1 : π * 1 = π * (π * t) := by
      calc π * 1 = π := mul_one π
        _ = π ^ 2 * t := ht
        _ = π * (π * t) := by ring
    have h2 : π * t = 1 := (mul_left_cancel₀ hπ0 h1).symm
    exact hπ.not_isUnit ⟨⟨π, t, h2, by rwa [mul_comm]⟩, rfl⟩
  -- the three windowed valuations
  have hv1K : ∀ K : ℕ, 1 ≤ K →
      resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ K) π) = 1 := by
    intro K hK
    rcases eq_or_lt_of_le hK with rfl | hK1
    · exact resOrd_mk_eq hπ le_rfl (by simp) (Or.inl rfl)
    · exact resOrd_mk_eq hπ hK (by simp) (Or.inr hnd2)
  have hv11 : resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ 1) π) = 1 := hv1K 1 le_rfl
  have hv13 : resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ 3) π) = 1 :=
    hv1K 3 (by norm_num)
  have hv33 : resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ 3) (π ^ 3)) = 3 :=
    resOrd_mk_eq hπ le_rfl dvd_rfl (Or.inl rfl)
  -- height reads on constant vectors
  have hh : ∀ (K : ℕ) (x : O) (i : ℕ) (hi : i < 2),
      npHeight (proj O 2 K (fun _ : Fin 2 => x)) i
        = resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ K) x) := by
    intro K x i hi
    unfold npHeight
    rw [dif_pos hi]
    rfl
  -- the m = 2 support formula
  have hsupcalc : ∀ {N : ℕ} (c : Coeff O 2 N) (v0 v1 : ℕ),
      npHeight c 0 = v0 → npHeight c 1 = v1 →
      classNPSupport c 1 1 = min v0 (min (v1 + 1) 2) := by
    intro N c v0 v1 h0 h1
    have h2 : npHeight c 2 = 0 := by
      unfold npHeight
      rw [dif_neg (by norm_num)]
    refine le_antisymm (le_min ?_ (le_min ?_ ?_)) ?_
    · have := classNPSupport_le_apply c 1 1 (show (0 : ℕ) ≤ 2 by norm_num)
      rw [h0] at this; omega
    · have := classNPSupport_le_apply c 1 1 (show (1 : ℕ) ≤ 2 by norm_num)
      rw [h1] at this; omega
    · have := classNPSupport_le_apply c 1 1 (le_refl 2)
      rw [h2] at this; omega
    · refine le_classNPSupport fun i hi => ?_
      interval_cases i
      · rw [h0]; omega
      · rw [h1]; omega
      · rw [h2]; omega
  -- the two lifts of one class
  have hproj : proj O 2 1 (fun _ : Fin 2 => π) = proj O 2 1 (fun _ : Fin 2 => π ^ 3) := by
    funext i
    show Ideal.Quotient.mk ((maximalIdeal O) ^ 1) π
      = Ideal.Quotient.mk ((maximalIdeal O) ^ 1) (π ^ 3)
    rw [Ideal.Quotient.eq]
    refine (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 _).2 ?_
    rw [pow_one]
    exact dvd_sub dvd_rfl (dvd_pow_self π (by norm_num))
  refine ⟨fun _ => π, fun _ => π ^ 3, hproj, ?_, ?_⟩
  · rw [hsupcalc _ 1 1 ((hh 1 π 0 (by norm_num)).trans hv11)
      ((hh 1 π 1 (by norm_num)).trans hv11)]
    decide
  · rw [hsupcalc _ 1 1 ((hh 3 π 0 (by norm_num)).trans hv13)
        ((hh 3 π 1 (by norm_num)).trans hv13),
      hsupcalc _ 3 3 ((hh 3 (π ^ 3) 0 (by norm_num)).trans hv33)
        ((hh 3 (π ^ 3) 1 (by norm_num)).trans hv33)]
    decide

end CN1

end Uniformity.Density.IFCG22

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG22.recentreClass_fullLoopClassN
#print axioms Uniformity.Density.IFCG22.recentreClass_mem_stratum
#print axioms Uniformity.Density.IFCG22.coneCellCount_translation
#print axioms Uniformity.Density.IFCG22.centeredConeLaw_iff_zeroCone
#print axioms Uniformity.Density.IFCG22.le_classCoeffVal_iff_dvd
#print axioms Uniformity.Density.IFCG22.classCoeffVal_exact
#print axioms Uniformity.Density.IFCG22.resOrd_resFactor
#print axioms Uniformity.Density.IFCG22.classNPSupport_refine_eq
#print axioms Uniformity.Density.IFCG22.npAttains_refine_iff
#print axioms Uniformity.Density.IFCG22.classNP_lift_eq
#print axioms Uniformity.Density.IFCG22.classNPFace_lift_iff
#print axioms Uniformity.Density.IFCG22.one_le_classCoeffVal_of_mem_stratum
#print axioms Uniformity.Density.IFCG22.npSupport_not_stable_at_floor
