/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType
import LeanUrat.OM.QpTypeH3
import LeanUrat.OM.RealInstanceW4Gates

/-!
# QpTypeMixed — the axiom-free mixed-gate anchor for the W4c axiom re-scope
(Wild Wave 4c, `notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md` §W4c; 2026-07-22)

The W4c re-scope extends `om_leaf_faithful` (`OM/OmLeafFaithful.lean`) from the K-windowed menu
`WildMenuW3.omMenuW3` to the mixed-e menu `MultiSlopeMenu.omMenu4`, with the per-family fiber
dispatch `fiberOf4` (mixed literals carry `classify1`/`InCell` fibers, NOT `B.classify`
fibers). The NEW menu content at `n = 5`, `σ₅ = {(2,1),(3,1)}` is the ONE canonical mixed
stratum `multiSideLit 5 [(0,2),(2,1),(5,0)] [[(1,1)],[(1,1)]]` — the two-slope path
`(0,2) → (2,1) → (5,0)` (slopes `−1/2` then `−1/3`), both residuals `[(1,1)]`. THIS module is
the axiom-free machine anchor pinning the re-scoped axiom's payload at that new stratum — the
mixed-gate mirror of `QpType.wildGateFiber_eisenstein` (W2) and the `QpTypeH3` anchors (W3c):

* `mixedGateFiber_valuation` — the fiber link: membership of a genuine monic quintic in the
  level-`N` (`N ≥ 3`) `classify1` fiber of the mixed-gate cell forces the EXACT valuation
  pins of the two-slope polygon: `v(a₀) = 2` (left vertex, exact), `a₁ ∈ (p)²` (strictly
  above the slope-`−1/2` side: the line value at abscissa 1 is `3/2`, so the integer
  valuation is `≥ 2`), `v(a₂) = 1` (interior vertex `(2,1)`, exact), `a₃ ∈ (p)` and
  `a₄ ∈ (p)` (on-or-above the slope-`−1/3` side: line values `2/3` and `1/3`). Route:
  `classify1_eq_some_iff` → `inCell_mkCell_iff` → `Matches` digit conditions → the decode
  bridge (`QpType.valuation_eq_of_zmodValuation_lt`,
  `QpTypeH3.mem_maximalIdeal_pow_of_le_zmodValuation`). Mirrors
  `QpType.wildGateFiber_valuation` / `QpTypeH3.wildH3Fiber_valuation`.
* `mixedGate_no_root'` / `mixedGate_no_root` / `mixedGate_no_linear_factor'` — **the
  cheap-strongest semantic anchor, FULL strength** (blueprint §W4c: "f has no ℚ_p-root"): a
  monic quintic with the five pinned coefficient conditions has NO root in ℚ_p, hence NO
  degree-1 factor over ℚ_p. The elementary two-case ledger (NO Newton-polygon machinery; the
  blueprint's three cases `v(r) ∈ {0}, {1}, [2,∞)` collapse to two):
  - a ℚ_p-root of a monic `ℤ_[p]`-polynomial is integral, hence lies in `ℤ_[p]`
    (`IsIntegralClosure.isIntegral_iff` at the integrally closed `ℤ_[p]`); call it `y`;
  - if `p ∣ y`: every non-constant term of `a₀ = −(a₁y + a₂y² + a₃y³ + a₄y⁴ + y⁵)` is
    divisible by `p³` (`a₁y`: `p²·p`; `a₂y²`: `p·p²`; the rest: `y³ ∣`), so `p³ ∣ a₀` —
    contradicting the EXACT `v(a₀) = 2`;
  - if `p ∤ y`: every term of `y⁵ = −(a₀ + a₁y + a₂y² + a₃y³ + a₄y⁴)` is divisible by `p`,
    so `p ∣ y⁵`, so `p ∣ y` (primality) — contradiction.
  (Genuinely both polygon slopes enter: the root valuations of the true factorization are
  `1/2` and `1/3`, so NO integer valuation is available — this two-case ledger is the
  elementary shadow of that fact.)
* `mixedGateFiber_no_root` / `mixedGateFiber_no_linear_factor` — the fiber-scoped anchors:
  the level-`N` mixed-gate fiber forces "no ℚ_p-root / no degree-1 factor over ℚ_p" —
  unconditionally, no axiom. Any mutation of the re-scoped axiom asserting a type with a
  `(1,1)` (or any `(e,1)·f=1`-degree-1) part on this fiber is machine-refutable (probe (i)
  evidence block below).
* `mixedGateFiber_nonempty` — the concrete mixed-gate fiber witness:
  `f0 = X⁵ + 2X² + 4` over `ℤ_[2]` at level `N = 4` (`v(a₀) = 2, v(a₂) = 1`, all other
  middle coefficients `0`; `InCell` proved directly from the digit conditions, mirroring
  `QpTypeH3.h3box_inCell` — the two residuals both read `X + 1`, shape `{(1,1)}`). The
  re-scoped axiom's mixed instance quantifies over a genuinely NONEMPTY fiber: the mutation
  probes below have real force.
* `ef_mul_eq_natDegree` / `natDegree_pos_of_irreducible_map` — probe plumbing: for ANY
  local-factor bundle on `g`, the fundamental identity `eOf · fOf = [L:ℚ_p] = deg g`
  (`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` through the bundle's instance stack,
  as in `QpTypeEisenstein.ef_of_eisenstein`), and monic factors irreducible over ℚ_p have
  positive degree. These are what turn a mutated `(e,f)`-multiset into a machine-checkable
  DEGREE LEDGER: a `(1,1)` part forces a degree-1 factor (probe (i), refuted by the
  no-linear-factor anchor); a wrong-e singleton `{(2,1)}` forces `2·1 = 5` (probe (ii),
  refuted by arithmetic).
* the σ₅ bookkeeping (`mixedGateLit_mem_omMenu4`, `decodePath_mixedGateLit`,
  `decodeShapes_mixedGateLit`, `headOrd_mixedGateLit`) — the probes' `hT`/`hfib` legs,
  consuming the banked `RealInstanceW4Gates.sigma5` computations.
* **Mutation probes (§W4c)**: both the ALL-UNRAMIFIED mutation `{(1,1)}⁵` and the WRONG-E
  SINGLETON mutation `{(2,1)}` of the RE-SCOPED axiom derive machine-checked `False` at the
  mixed-gate stratum — scratches NOT committed; verbatim text + output recorded in the two
  `Mutation probe evidence` comment blocks below. Positive coherence note: the REAL
  conclusion `σ₅ = {(2,1),(3,1)}` passes both guards — it has no `(e,f)` part of degree
  `e·f = 1` (no forced linear factor) and its degree ledger reads `2·1 + 3·1 = 5` exactly.

Leaf module: no existing file is modified (the census append to `AxChk_baseline.lean` is Part D
of the wave). **No axiom, no sorry** — every declaration here must be core-only (AxCheck at
bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.QpTypeMixed

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Block 1 — the mixed-gate stratum literals (n = 5, σ₅ = {(2,1),(3,1)}) -/

/-- The mixed-gate menu path `[(0,2),(2,1),(5,0)]` (two sides, slopes `−1/2` then `−1/3`,
`H_total = fSum σ₅ = 2`). -/
def mixedGatePath : List (ℕ × ℕ) := [(0, 2), (2, 1), (5, 0)]

/-- The `e = 2` side `((0,2),(2,1))` (slope `−1/2`, `sideDeg = gcd(1,2) = 1`). -/
def mixedGateSide1 : (ℕ × ℕ) × (ℕ × ℕ) := ((0, 2), (2, 1))

/-- The `e = 3` side `((2,1),(5,0))` (slope `−1/3`, `sideDeg = gcd(1,3) = 1`). -/
def mixedGateSide2 : (ℕ × ℕ) × (ℕ × ℕ) := ((2, 1), (5, 0))

/-- The per-side residual shapes: one linear μ=1 factor per side. -/
def mixedGateSh : List (List (ℕ × ℕ)) := [[(1, 1)], [(1, 1)]]

theorem sidePairs_mixedGatePath :
    sidePairs mixedGatePath = [mixedGateSide1, mixedGateSide2] := rfl

/-- The mixed-gate path is a menu path at every level `N ≥ 3` (= its threshold `H_total + 1`);
F4 holds: `−1/2 < −1/3`. -/
theorem menuPath_mixedGate {N : ℕ} (hN : 3 ≤ N) : MenuPath 5 N mixedGatePath :=
  ⟨2, (2, 1), [(5, 0)], rfl, by omega, by omega, by norm_num, by norm_num,
    ChainOK.cons (by norm_num) (by norm_num) (by norm_num [SlopeLt]) (ChainOK.nil rfl rfl)⟩

theorem shapesFor_mixedGate : ShapesFor mixedGatePath mixedGateSh := by
  unfold ShapesFor
  rw [sidePairs_mixedGatePath]
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil) <;>
  · rw [mem_shapesOfDegree_iff]
    refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
    · intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨le_refl 1, le_refl 1⟩
    · rfl

/-! ### σ₅ bookkeeping: the canonical mixed literal IS this stratum (the probes' `hT` leg) -/

/-- The mixed-gate multi-slope literal — the ONE `omMenu4` entry at σ₅ beyond the (empty)
Wave-3 legs. -/
noncomputable def mixedGateLit : ClusterShape :=
  MultiSlopeMenu.multiSideLit 5 mixedGatePath mixedGateSh

/-- The mixed-gate literal is the canonical W4a literal of σ₅ (the banked
`RealInstanceW4Gates` computations of `mixedPath`/`mixedSh`). -/
theorem mixedGateLit_eq_canonical :
    mixedGateLit
      = MultiSlopeMenu.multiSideLit 5
          (MultiSlopeMenu.mixedPath RealInstanceW4Gates.sigma5)
          (MultiSlopeMenu.mixedSh RealInstanceW4Gates.sigma5) := by
  rw [RealInstanceW4Gates.mixedPath_sigma5, RealInstanceW4Gates.mixedSh_sigma5]
  rfl

/-- **The mixed-gate literal is a member of the Wave-4 menu at σ₅, for EVERY window bound K**
(the mixed branch is K-independent) — the `hT` leg of the re-scoped axiom's mixed instance. -/
theorem mixedGateLit_mem_omMenu4 (K : ℕ) :
    mixedGateLit ∈ MultiSlopeMenu.omMenu4 5 K RealInstanceW4Gates.sigma5 := by
  rw [MultiSlopeMenu.omMenu4_of_mixed RealInstanceW4Gates.mixedOK_sigma5,
    mixedGateLit_eq_canonical]
  exact Finset.mem_singleton_self _

theorem headOrd_mixedGateLit : MultiSlopeMenu.headOrd mixedGateLit = 1 :=
  MultiSlopeMenu.headOrd_multiSideLit 5 mixedGatePath mixedGateSh

theorem decodePath_mixedGateLit :
    MultiSlopeMenu.decodePath mixedGateLit = mixedGatePath :=
  MultiSlopeMenu.decodePath_multiSideLit 5 mixedGatePath mixedGateSh

theorem allMuOne_mixedGateSh : PathShapeMultiSideTree.AllMuOne mixedGateSh := by
  intro shape hs q hq
  fin_cases hs <;> · rw [List.mem_singleton] at hq; subst hq; rfl

theorem decodeShapes_mixedGateLit :
    MultiSlopeMenu.decodeShapes mixedGateLit = mixedGateSh :=
  MultiSlopeMenu.decodeShapes_multiSideLit (n := 5) rfl allMuOne_mixedGateSh

/-! ## Block 2 — the fiber link: the mixed-gate `classify1` fiber forces the valuation pins -/

/-- **The mixed-gate fiber link.** If `toBox f` lies in the level-`N` `classify1` fiber of the
mixed-gate cell (`N ≥ 3` — the stratum's threshold), then the five coefficient pins of the
two-slope polygon hold: `v(a₀) = 2` (exact), `a₁ ∈ (p)²`, `v(a₂) = 1` (exact), `a₃ ∈ (p)`,
`a₄ ∈ (p)`. (This is the mixed-branch fiber hypothesis of the re-scoped
`om_leaf_faithful` — `fiberOf4_mixed` — at `T = mixedGateLit`, after the decode lemmas.) -/
theorem mixedGateFiber_valuation {N : ℕ} (hN0 : 0 < N) (hN3 : 3 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 5)
    (hfib : classify1 p (PadicLift.toBox p 5 N hN0 f hf hdeg)
      = some (mkCell 5 mixedGatePath mixedGateSh)) :
    (f.coeff 0).valuation = 2 ∧ f.coeff 1 ∈ (maximalIdeal ℤ_[p]) ^ 2
      ∧ (f.coeff 2).valuation = 1
      ∧ f.coeff 3 ∈ maximalIdeal ℤ_[p] ∧ f.coeff 4 ∈ maximalIdeal ℤ_[p] := by
  set fbox := PadicLift.toBox p 5 N hN0 f hf hdeg with hfbox
  -- fiber → InCell → Matches
  have hIn : InCell p fbox (mkCell 5 mixedGatePath mixedGateSh) :=
    (classify1_eq_some_iff p).mp hfib
  have hM : Matches p fbox mixedGatePath mixedGateSh :=
    (inCell_mkCell_iff p (menuPath_mixedGate hN3) shapesFor_mixedGate).mp hIn
  -- vertex exactness
  have hv0 : vOf p fbox 0 = 2 := hM.1 (0, 2) (by simp [mixedGatePath])
  have hv2 : vOf p fbox 2 = 1 := hM.1 (2, 1) (by simp [mixedGatePath])
  -- the two side matches
  have h2 := hM.2
  rw [sidePairs_mixedGatePath] at h2
  have hSM1 : SideMatch p fbox [(1, 1)] mixedGateSide1 := by
    cases h2 with | cons h _ => exact h
  have hSM2 : SideMatch p fbox [(1, 1)] mixedGateSide2 := by
    cases h2 with | cons _ t => cases t with | cons h _ => exact h
  -- the strictly-above condition on the e=2 side at abscissa 1: line value 3/2
  have hv1 : 2 ≤ vOf p fbox 1 := by
    have hline := hSM1.1 1 (by norm_num [mixedGateSide1]) (by norm_num [mixedGateSide1])
    have hval : lineAt mixedGateSide1 ((1 : ℕ) : ℚ) = 3 / 2 := by
      norm_num [lineAt, slopeQ, mixedGateSide1]
    rw [hval] at hline
    by_contra hlt
    rw [not_le] at hlt
    have h01 : vOf p fbox 1 = 0 ∨ vOf p fbox 1 = 1 := by omega
    rcases h01 with h01 | h01 <;> rw [h01] at hline <;> norm_num at hline
  -- the on-or-above conditions on the e=3 side at abscissae 3 and 4: line values 2/3, 1/3
  have hv3 : 1 ≤ vOf p fbox 3 := by
    have hline := hSM2.1 3 (by norm_num [mixedGateSide2]) (by norm_num [mixedGateSide2])
    have hval : lineAt mixedGateSide2 ((3 : ℕ) : ℚ) = 2 / 3 := by
      norm_num [lineAt, slopeQ, mixedGateSide2]
    rw [hval] at hline
    by_contra hlt
    rw [not_le] at hlt
    have h00 : vOf p fbox 3 = 0 := by omega
    rw [h00] at hline
    norm_num at hline
  have hv4 : 1 ≤ vOf p fbox 4 := by
    have hline := hSM2.1 4 (by norm_num [mixedGateSide2]) (by norm_num [mixedGateSide2])
    have hval : lineAt mixedGateSide2 ((4 : ℕ) : ℚ) = 1 / 3 := by
      norm_num [lineAt, slopeQ, mixedGateSide2]
    rw [hval] at hline
    by_contra hlt
    rw [not_le] at hlt
    have h00 : vOf p fbox 4 = 0 := by omega
    rw [h00] at hline
    norm_num at hline
  -- decode through toBox
  have hvOf : ∀ i, vOf p fbox i
      = PadicLift.zmodValuation p N (PadicInt.toZModPow N (f.coeff i)) := by
    intro i
    simp only [vOf, hfbox, PadicLift.toBox_val, Polynomial.coeff_map]
  rw [hvOf 0] at hv0
  rw [hvOf 1] at hv1
  rw [hvOf 2] at hv2
  rw [hvOf 3] at hv3
  rw [hvOf 4] at hv4
  obtain ⟨-, hval0⟩ := QpType.valuation_eq_of_zmodValuation_lt p (by omega : 2 < N) hv0
  obtain ⟨-, hval2⟩ := QpType.valuation_eq_of_zmodValuation_lt p (by omega : 1 < N) hv2
  exact ⟨hval0,
    QpTypeH3.mem_maximalIdeal_pow_of_le_zmodValuation p (by omega : 2 ≤ N) hv1,
    hval2,
    QpType.mem_maximalIdeal_of_one_le_zmodValuation p hN0 hv3,
    QpType.mem_maximalIdeal_of_one_le_zmodValuation p hN0 hv4⟩

/-! ## Block 3 — the axiom-free no-root / no-linear-factor anchor (FULL strength) -/

/-- **The abstract mixed-gate no-root theorem (`ℤ_[p]` form — the ledger core).** A monic
quintic with `v(a₀) = 2` (exact), `a₁ ∈ (p)²`, `a₂, a₃, a₄ ∈ (p)` has no root in `ℤ_[p]`.
Two-case ledger (module docstring): `p ∣ y` forces `p³ ∣ a₀` (against exactness);
`p ∤ y` forces `p ∣ y⁵` (against primality). -/
theorem mixedGate_no_root' {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 5)
    (h0 : (f.coeff 0).valuation = 2) (h1 : f.coeff 1 ∈ (maximalIdeal ℤ_[p]) ^ 2)
    (h2 : f.coeff 2 ∈ maximalIdeal ℤ_[p]) (h3 : f.coeff 3 ∈ maximalIdeal ℤ_[p])
    (h4 : f.coeff 4 ∈ maximalIdeal ℤ_[p]) (y : ℤ_[p]) : f.eval y ≠ 0 := by
  intro hy
  have ha0 : f.coeff 0 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at h0
    omega
  -- the divisibility ledger
  have hd0 : (p : ℤ_[p]) ^ 2 ∣ f.coeff 0 := by
    have hm := (PadicInt.mem_span_pow_iff_le_valuation _ ha0 2).mpr (by omega)
    rwa [Ideal.mem_span_singleton] at hm
  have hnd0 : ¬ (p : ℤ_[p]) ^ 3 ∣ f.coeff 0 := by
    intro hdvd
    have hm := (PadicInt.mem_span_pow_iff_le_valuation _ ha0 3).mp
      (Ideal.mem_span_singleton.mpr hdvd)
    omega
  have hd1 : (p : ℤ_[p]) ^ 2 ∣ f.coeff 1 := by
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at h1
  have hd2 : (p : ℤ_[p]) ∣ f.coeff 2 := by
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2
  have hd3 : (p : ℤ_[p]) ∣ f.coeff 3 := by
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h3
  have hd4 : (p : ℤ_[p]) ∣ f.coeff 4 := by
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h4
  -- the root equation, expanded
  have hexp : ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * y ^ i = 0 := by
    rw [← Polynomial.eval_eq_sum_range]
    exact hy
  rw [hdeg] at hexp
  have h5 : f.coeff 5 = 1 := by
    have hc := hf.coeff_natDegree
    rwa [hdeg] at hc
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h5, one_mul,
    pow_zero, mul_one, pow_one] at hexp
  -- hexp : a₀ + a₁·y + a₂·y² + a₃·y³ + a₄·y⁴ + y⁵ = 0
  by_cases hpy : (p : ℤ_[p]) ∣ y
  · -- CASE p ∣ y: p³ divides every non-constant term, so p³ ∣ a₀ — against v(a₀) = 2
    refine hnd0 ?_
    have hkey : f.coeff 0
        = -(f.coeff 1 * y + f.coeff 2 * y ^ 2 + f.coeff 3 * y ^ 3
            + f.coeff 4 * y ^ 4 + y ^ 5) := by linear_combination hexp
    rw [hkey]
    refine dvd_neg.mpr (dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_)
    · -- p³ = p²·p ∣ a₁·y
      rw [show ((p : ℤ_[p]) ^ 3) = p ^ 2 * p from by ring]
      exact mul_dvd_mul hd1 hpy
    · -- p³ = p·p² ∣ a₂·y²
      rw [show ((p : ℤ_[p]) ^ 3) = p * p ^ 2 from by ring]
      exact mul_dvd_mul hd2 (pow_dvd_pow_of_dvd hpy 2)
    · exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpy 3) _
    · exact Dvd.dvd.mul_left
        ((pow_dvd_pow_of_dvd hpy 3).trans (pow_dvd_pow y (by omega))) _
    · exact (pow_dvd_pow_of_dvd hpy 3).trans (pow_dvd_pow y (by omega))
  · -- CASE p ∤ y: p divides every term of the complement, so p ∣ y⁵ — against primality
    have hkey : y ^ 5
        = -(f.coeff 0 + f.coeff 1 * y + f.coeff 2 * y ^ 2 + f.coeff 3 * y ^ 3
            + f.coeff 4 * y ^ 4) := by linear_combination hexp
    have hdvd : (p : ℤ_[p]) ∣ y ^ 5 := by
      rw [hkey]
      refine dvd_neg.mpr (dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_)
      · exact (dvd_pow_self (p : ℤ_[p]) two_ne_zero).trans hd0
      · exact ((dvd_pow_self (p : ℤ_[p]) two_ne_zero).trans hd1).mul_right y
      · exact hd2.mul_right _
      · exact hd3.mul_right _
      · exact hd4.mul_right _
    exact hpy ((PadicInt.prime_p).dvd_of_dvd_pow hdvd)

/-- **The abstract mixed-gate no-root theorem (ℚ_p form).** Same hypotheses; no root in ℚ_p:
a ℚ_p-root of the monic integral `f` is integral over the integrally closed `ℤ_[p]`, hence
descends to `ℤ_[p]`, where `mixedGate_no_root'` refutes it. -/
theorem mixedGate_no_root {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 5)
    (h0 : (f.coeff 0).valuation = 2) (h1 : f.coeff 1 ∈ (maximalIdeal ℤ_[p]) ^ 2)
    (h2 : f.coeff 2 ∈ maximalIdeal ℤ_[p]) (h3 : f.coeff 3 ∈ maximalIdeal ℤ_[p])
    (h4 : f.coeff 4 ∈ maximalIdeal ℤ_[p]) (r : ℚ_[p]) :
    (f.map (algebraMap ℤ_[p] ℚ_[p])).eval r ≠ 0 := by
  intro hr
  have hint : IsIntegral ℤ_[p] r := ⟨f, hf, by rwa [Polynomial.eval_map] at hr⟩
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff
    (A := ℤ_[p]) (R := ℤ_[p]) (B := ℚ_[p])).mp hint
  have hyval : f.eval y = 0 := by
    have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) :=
      IsFractionRing.injective ℤ_[p] ℚ_[p]
    apply hinj
    rw [map_zero]
    calc algebraMap ℤ_[p] ℚ_[p] (f.eval y)
        = (f.map (algebraMap ℤ_[p] ℚ_[p])).eval (algebraMap ℤ_[p] ℚ_[p] y) := by
          rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      _ = (f.map (algebraMap ℤ_[p] ℚ_[p])).eval r := by rw [hy]
      _ = 0 := hr
  exact mixedGate_no_root' p hf hdeg h0 h1 h2 h3 h4 y hyval

/-- **The abstract no-linear-factor theorem**: under the mixed-gate coefficient pins, `f` has
NO degree-1 factor over ℚ_p (a monic-scaled linear factor would exhibit a ℚ_p-root). -/
theorem mixedGate_no_linear_factor' {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 5)
    (h0 : (f.coeff 0).valuation = 2) (h1 : f.coeff 1 ∈ (maximalIdeal ℤ_[p]) ^ 2)
    (h2 : f.coeff 2 ∈ maximalIdeal ℤ_[p]) (h3 : f.coeff 3 ∈ maximalIdeal ℤ_[p])
    (h4 : f.coeff 4 ∈ maximalIdeal ℤ_[p]) :
    ¬ ∃ g : Polynomial ℚ_[p], g.natDegree = 1 ∧ g ∣ f.map (algebraMap ℤ_[p] ℚ_[p]) := by
  rintro ⟨g, hg1, hgdvd⟩
  obtain ⟨a, ha, b, hab⟩ := Polynomial.natDegree_eq_one.mp hg1
  have hroot : g.eval (-b / a) = 0 := by
    rw [← hab]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    field_simp
    ring
  obtain ⟨h, hfac⟩ := hgdvd
  have heval : (f.map (algebraMap ℤ_[p] ℚ_[p])).eval (-b / a) = 0 := by
    rw [hfac, Polynomial.eval_mul, hroot, zero_mul]
  exact mixedGate_no_root p hf hdeg h0 h1 h2 h3 h4 _ heval

/-! ## Block 4 — the fiber-scoped anchors -/

/-- **The axiom-free mixed-gate no-root anchor.** Membership in the level-`N` `classify1`
fiber of the mixed-gate cell forces "no root in ℚ_p" — unconditionally, no axiom. -/
theorem mixedGateFiber_no_root {N : ℕ} (hN0 : 0 < N) (hN3 : 3 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 5)
    (hfib : classify1 p (PadicLift.toBox p 5 N hN0 f hf hdeg)
      = some (mkCell 5 mixedGatePath mixedGateSh)) (r : ℚ_[p]) :
    (f.map (algebraMap ℤ_[p] ℚ_[p])).eval r ≠ 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := mixedGateFiber_valuation p hN0 hN3 hf hdeg hfib
  have h2' : f.coeff 2 ∈ maximalIdeal ℤ_[p] := by
    have ha2 : f.coeff 2 ≠ 0 := by
      intro h
      rw [h, PadicInt.valuation_zero] at h2
      omega
    rw [PadicInt.maximalIdeal_eq_span_p]
    have hm := (PadicInt.mem_span_pow_iff_le_valuation _ ha2 1).mpr (by omega)
    simpa [pow_one] using hm
  exact mixedGate_no_root p hf hdeg h0 h1 h2' h3 h4 r

/-- **The axiom-free mixed-gate anchor (blueprint §W4c: `mixedGate_no_linear_factor`).**
Membership in the level-`N` `classify1` fiber of the mixed-gate cell forces "NO degree-1
factor over ℚ_p" — unconditionally, no axiom. Any mutation of the re-scoped
`om_leaf_faithful` asserting a type with a degree-1 part (in particular the all-unramified
`{(1,1)}⁵`) on this fiber is machine-refutable (probe evidence below). -/
theorem mixedGateFiber_no_linear_factor {N : ℕ} (hN0 : 0 < N) (hN3 : 3 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 5)
    (hfib : classify1 p (PadicLift.toBox p 5 N hN0 f hf hdeg)
      = some (mkCell 5 mixedGatePath mixedGateSh)) :
    ¬ ∃ g : Polynomial ℚ_[p], g.natDegree = 1 ∧ g ∣ f.map (algebraMap ℤ_[p] ℚ_[p]) := by
  rintro ⟨g, hg1, hgdvd⟩
  obtain ⟨a, ha, b, hab⟩ := Polynomial.natDegree_eq_one.mp hg1
  have hroot : g.eval (-b / a) = 0 := by
    rw [← hab]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    field_simp
    ring
  obtain ⟨h, hfac⟩ := hgdvd
  have heval : (f.map (algebraMap ℤ_[p] ℚ_[p])).eval (-b / a) = 0 := by
    rw [hfac, Polynomial.eval_mul, hroot, zero_mul]
  exact mixedGateFiber_no_root p hN0 hN3 hf hdeg hfib _ heval

/-! ## Block 5 — the concrete mixed-gate fiber witness (p = 2, N = 4)

No banked `CellMenu` gate exists at the mixed cell (the W0 numeric gates are all at `n = 2`),
so the box element of `f0 = X⁵ + 2X² + 2²` is constructed and its `InCell` proved directly
from the digit conditions, mirroring `QpTypeH3.h3box_inCell` side by side. -/

/-- The concrete mixed-gate fiber witness: `X⁵ + 2X² + 4` over `ℤ_[2]`
(`v(a₀) = 2`, `v(a₂) = 1`, `a₁ = a₃ = a₄ = 0`). -/
noncomputable def mixedGatePoly : Polynomial ℤ_[2] := X ^ 5 + C 2 * X ^ 2 + C 4

theorem mixedGatePoly_monic : mixedGatePoly.Monic := by unfold mixedGatePoly; monicity!

theorem mixedGatePoly_natDegree : mixedGatePoly.natDegree = 5 := by
  unfold mixedGatePoly; compute_degree!

/-- The level-4 box of the witness. -/
noncomputable def mixedGateBox : QuotientBox.monicBox 2 4 5 :=
  ⟨X ^ 5 + C 2 * X ^ 2 + C 4, ⟨by monicity!, by compute_degree!⟩⟩

/-- `toBox` sends the genuine witness to the level-4 box. -/
theorem toBox_mixedGatePoly :
    PadicLift.toBox 2 5 4 (by norm_num) mixedGatePoly mixedGatePoly_monic
      mixedGatePoly_natDegree = mixedGateBox := by
  apply Subtype.ext
  rw [PadicLift.toBox_val]
  show mixedGatePoly.map (PadicInt.toZModPow 4)
    = (X ^ 5 + C 2 * X ^ 2 + C 4 : (ZMod (2 ^ 4))[X])
  unfold mixedGatePoly
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, map_ofNat]

/-! ### Level-4 valuation and unit-residue facts (`p = 2`, `ZMod 16`) -/

theorem mgv1 : PadicLift.zmodValuation 2 4 (1 : ZMod (2 ^ 4)) = 0 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem mgv2 : PadicLift.zmodValuation 2 4 (2 : ZMod (2 ^ 4)) = 1 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem mgv4 : PadicLift.zmodValuation 2 4 (4 : ZMod (2 ^ 4)) = 2 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem mgu1 : PadicLift.zmodUnitResidue 2 4 (1 : ZMod (2 ^ 4)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (1 : ZMod (2 ^ 4))) (u := 1) (by decide) mgv1 (by decide)
  simpa using h

theorem mgu2 : PadicLift.zmodUnitResidue 2 4 (2 : ZMod (2 ^ 4)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (2 : ZMod (2 ^ 4))) (u := 1) (by decide) mgv2 (by decide)
  simpa using h

theorem mgu4 : PadicLift.zmodUnitResidue 2 4 (4 : ZMod (2 ^ 4)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (4 : ZMod (2 ^ 4))) (u := 1) (by decide) mgv4 (by decide)
  simpa using h

/-- The witness box lies in the mixed-gate cell (digit conditions checked directly on BOTH
sides). -/
theorem mixedGateBox_inCell : InCell 2 mixedGateBox (mkCell 5 mixedGatePath mixedGateSh) := by
  have hc0 : (mixedGateBox.1).coeff 0 = 4 := by simp [mixedGateBox]
  have hc1 : (mixedGateBox.1).coeff 1 = 0 := by simp [mixedGateBox]
  have hc2 : (mixedGateBox.1).coeff 2 = 2 := by simp [mixedGateBox]
  have hc3 : (mixedGateBox.1).coeff 3 = 0 := by simp [mixedGateBox]
  have hc4 : (mixedGateBox.1).coeff 4 = 0 := by simp [mixedGateBox]
  have hc5 : (mixedGateBox.1).coeff 5 = 1 := by simp [mixedGateBox]
  have hv0 : vOf 2 mixedGateBox 0 = 2 := by unfold vOf; rw [hc0]; exact mgv4
  have hv1 : vOf 2 mixedGateBox 1 = 4 := by
    unfold vOf; rw [hc1]; exact PadicLift.zmodValuation_zero 2 4
  have hv2 : vOf 2 mixedGateBox 2 = 1 := by unfold vOf; rw [hc2]; exact mgv2
  have hv3 : vOf 2 mixedGateBox 3 = 4 := by
    unfold vOf; rw [hc3]; exact PadicLift.zmodValuation_zero 2 4
  have hv4 : vOf 2 mixedGateBox 4 = 4 := by
    unfold vOf; rw [hc4]; exact PadicLift.zmodValuation_zero 2 4
  have hv5 : vOf 2 mixedGateBox 5 = 0 := by unfold vOf; rw [hc5]; exact mgv1
  -- side 1 = ((0,2),(2,1)): e = 2, h = −1, d = 1, v₀ = 2
  have hsd1 := side_data (pr := ((0, 2), (2, 1))) (by decide) (by decide)
  have hE1 : (mkSide ((0, 2), (2, 1))).e = 2 := by rw [hsd1.1]; decide
  have hH1 : (mkSide ((0, 2), (2, 1))).h = -1 := by rw [hsd1.2.1]; decide
  have hD1 : M4.residualDeg (mkSide ((0, 2), (2, 1))) = 1 := by rw [hsd1.2.2.1]; decide
  have hg10 : (PadicLift.zmodValuation 2 4 ((mixedGateBox.1).coeff 0) : ℤ)
      = ((mkSide ((0, 2), (2, 1))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 2), (2, 1))).h := by
    rw [hc0, mgv4]; simp [mkSide]
  have hg11 : (PadicLift.zmodValuation 2 4 ((mixedGateBox.1).coeff 2) : ℤ)
      = ((mkSide ((0, 2), (2, 1))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 2), (2, 1))).h := by
    rw [hc2, mgv2, hH1]; norm_num [mkSide]
  have hb10 : B.boxCoeffData 2 4 (mkSide ((0, 2), (2, 1))) mixedGateBox 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg10, hc0, mgu4]
  have hb11 : B.boxCoeffData 2 4 (mkSide ((0, 2), (2, 1))) mixedGateBox 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 2) (by rw [hE1]; decide) hg11, hc2, mgu2]
  have hR1 : residualOf 2 mixedGateBox ((0, 2), (2, 1)) = X + 1 := by
    rw [residual_deg_one 2 mixedGateBox _ hD1, hb10, hb11, map_one, one_mul]
    ring
  -- side 2 = ((2,1),(5,0)): e = 3, h = −1, d = 1, v₀ = 1
  have hsd2 := side_data (pr := ((2, 1), (5, 0))) (by decide) (by decide)
  have hE2 : (mkSide ((2, 1), (5, 0))).e = 3 := by rw [hsd2.1]; decide
  have hH2 : (mkSide ((2, 1), (5, 0))).h = -1 := by rw [hsd2.2.1]; decide
  have hD2 : M4.residualDeg (mkSide ((2, 1), (5, 0))) = 1 := by rw [hsd2.2.2.1]; decide
  have hg20 : (PadicLift.zmodValuation 2 4 ((mixedGateBox.1).coeff 2) : ℤ)
      = ((mkSide ((2, 1), (5, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((2, 1), (5, 0))).h := by
    rw [hc2, mgv2]; simp [mkSide]
  have hg21 : (PadicLift.zmodValuation 2 4 ((mixedGateBox.1).coeff 5) : ℤ)
      = ((mkSide ((2, 1), (5, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((2, 1), (5, 0))).h := by
    rw [hc5, mgv1, hH2]; norm_num [mkSide]
  have hb20 : B.boxCoeffData 2 4 (mkSide ((2, 1), (5, 0))) mixedGateBox 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 2) (by simp [mkSide]) hg20, hc2, mgu2]
  have hb21 : B.boxCoeffData 2 4 (mkSide ((2, 1), (5, 0))) mixedGateBox 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 5) (by rw [hE2]; decide) hg21, hc5, mgu1]
  have hR2 : residualOf 2 mixedGateBox ((2, 1), (5, 0)) = X + 1 := by
    rw [residual_deg_one 2 mixedGateBox _ hD2, hb20, hb21, map_one, one_mul]
    ring
  -- assemble the match
  have hmenu : MenuPath 5 4 mixedGatePath := menuPath_mixedGate (by norm_num)
  have hexact : ∀ q ∈ mixedGatePath, vOf 2 mixedGateBox q.1 = q.2 := by
    intro q hq
    fin_cases hq <;> assumption
  have habove1 : SideAbove 2 mixedGateBox ((0, 2), (2, 1)) := by
    intro i hi0 hi2
    interval_cases i
    · rw [hv0]; norm_num [lineAt, slopeQ]
    · rw [hv1]; norm_num [lineAt, slopeQ]
    · rw [hv2]; norm_num [lineAt, slopeQ]
  have habove2 : SideAbove 2 mixedGateBox ((2, 1), (5, 0)) := by
    intro i hi0 hi2
    interval_cases i
    · rw [hv2]; norm_num [lineAt, slopeQ]
    · rw [hv3]; norm_num [lineAt, slopeQ]
    · rw [hv4]; norm_num [lineAt, slopeQ]
    · rw [hv5]; norm_num [lineAt, slopeQ]
  have hmatch : Matches 2 mixedGateBox mixedGatePath mixedGateSh :=
    ⟨hexact,
      List.Forall₂.cons ⟨habove1, by rw [hR1, polyShape_X_add_one 2]; simp⟩
        (List.Forall₂.cons ⟨habove2, by rw [hR2, polyShape_X_add_one 2]; simp⟩
          List.Forall₂.nil)⟩
  exact ⟨_, _, hmenu, shapesFor_mixedGate, rfl, hmatch⟩

/-- **The mixed-gate fiber is INHABITED** by the concrete `mixedGatePoly = X⁵ + 2X² + 4` at
`p = 2`, `N = 4`: the re-scoped axiom's mixed instance quantifies over a genuinely nonempty
fiber, so the mutation probes (evidence blocks below) have real force. Route: direct `InCell`
(`mixedGateBox_inCell`) + `classify1_eq_some_iff` (mpr). -/
theorem mixedGateFiber_nonempty :
    ∃ (f0 : Polynomial ℤ_[2]) (hf : f0.Monic) (hdeg : f0.natDegree = 5),
      classify1 2 (PadicLift.toBox 2 5 4 (by norm_num) f0 hf hdeg)
        = some (mkCell 5 mixedGatePath mixedGateSh) := by
  refine ⟨mixedGatePoly, mixedGatePoly_monic, mixedGatePoly_natDegree, ?_⟩
  rw [toBox_mixedGatePoly]
  exact (classify1_eq_some_iff 2).mpr mixedGateBox_inCell

/-! ## Block 6 — probe plumbing: the degree ledger of a local-factor bundle -/

/-- A monic factor irreducible over ℚ_p has positive degree (degree 0 + monic = the unit 1). -/
theorem natDegree_pos_of_irreducible_map {g : ℤ_[p][X]} (hg : g.Monic)
    (hirr : Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p]))) : 0 < g.natDegree := by
  by_contra hle
  have h0 : g.natDegree = 0 := by omega
  have hg1 : g = 1 := (Polynomial.Monic.natDegree_eq_zero hg).mp h0
  rw [hg1, Polynomial.map_one] at hirr
  exact hirr.not_isUnit isUnit_one

/-- **The fundamental degree ledger, axiom-free**: EVERY local-factor bundle on `g` of positive
degree has `eOf · fOf = [L : ℚ_p] = deg g` (`ramificationIdx_mul_inertiaDeg_of_isLocalRing`
through the bundle's instance stack, exactly as inlined in `QpTypeEisenstein.ef_of_eisenstein`
and `QpTypeH3.ef_of_wildH3`; here exposed standalone as the probes' degree guard). -/
theorem ef_mul_eq_natDegree {g : ℤ_[p][X]} (hdeg : 0 < g.natDegree)
    (D : QpType.LocalFactorData p g) :
    QpType.eOf p D * QpType.fOf p D = g.natDegree := by
  letI := D.fieldL
  letI := D.algQL
  letI := D.algZL
  letI := D.towerZQL
  letI := D.crO
  letI := D.domO
  letI := D.dvrO
  letI := D.algZO
  letI := D.algOL
  letI := D.towerZOL
  letI := D.intClosure
  letI := D.liesOver
  haveI hFD : FiniteDimensional ℚ_[p] D.L :=
    FiniteDimensional.of_finrank_pos (by rw [D.finrank_eq]; omega)
  haveI : IsFractionRing D.O D.L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] D.L D.O
  haveI : Module.Finite ℤ_[p] D.O := IsIntegralClosure.finite ℤ_[p] ℚ_[p] D.L D.O
  have hbot : maximalIdeal ℤ_[p] ≠ ⊥ := by
    intro hb
    have hpmem : (p : ℤ_[p]) ∈ (⊥ : Ideal ℤ_[p]) := by
      rw [← hb, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    exact (PadicInt.prime_p (p := p)).ne_zero (Ideal.mem_bot.mp hpmem)
  show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O)
      * Ideal.inertiaDeg (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = g.natDegree
  rw [Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (S := D.O) (K := ℚ_[p]) (L := D.L)
    hbot, D.finrank_eq]

/-! ## Block 7 — mutation probe evidence (blueprint §W4c, both probes at the NEW mixed stratum)

**Probe (i) — the ALL-UNRAMIFIED mutation of the RE-SCOPED axiom is refuted at the mixed-gate
stratum (machine-checked 2026-07-22, scratch NOT committed).** The scratch below — the
re-scoped axiom's hypotheses VERBATIM (including the W4c `hT : T ∈ MultiSlopeMenu.omMenu4
n K σ` and `hfib : OmLeafFaithful.fiberOf4 …`), conclusion mutated to the ALL-UNRAMIFIED type
`{(1,1),(1,1),(1,1),(1,1),(1,1)}` — compiled with zero errors against this module: `False`
derives from the mutated axiom + `mixedGateFiber_nonempty` + `mixedGateLit_mem_omMenu4` +
the decode lemmas (which convert the witness's `classify1` fiber equation into the axiom's
`fiberOf4` hypothesis) + the degree ledger (`ef_mul_eq_natDegree`: a `(1,1)` bundle is a
degree-1 factor) + the AXIOM-FREE `mixedGateFiber_no_linear_factor`. This is the W4c probe
at the NEW menu content the re-scope adds (the mixed multi-slope stratum), against a purely
axiom-free anchor.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeEisenstein
import LeanUrat.OM.QpTypeMixed

namespace LeanUrat.OM.QpTypeMixedScratchUnram

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of the RE-SCOPED `om_leaf_faithful` verbatim
(omMenu4 menu + fiberOf4 dispatch), conclusion replaced by the ALL-UNRAMIFIED type
`{(1,1),(1,1),(1,1),(1,1),(1,1)}`. -/
axiom om_leaf_faithful_MUTATED_unram (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ)
    (hT : T ∈ MultiSlopeMenu.omMenu4 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf4 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ)),
        ((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

/-- The all-unramified mutation is REFUTED at the mixed-gate stratum: the inhabited fiber
(`QpTypeMixed.mixedGateFiber_nonempty`) would carry a factorization with a `(1,1)` bundle,
whose degree ledger (`ef_mul_eq_natDegree`) forces a degree-1 factor of `f0` over ℚ_2 —
against the AXIOM-FREE `QpTypeMixed.mixedGateFiber_no_linear_factor`. -/
theorem mutation_unram_refuted : False := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := QpTypeMixed.mixedGateFiber_nonempty
  have hfib4 : OmLeafFaithful.fiberOf4 2 5 4 (by norm_num) QpTypeMixed.mixedGateLit
      f0 hf hdeg := by
    rw [OmLeafFaithful.fiberOf4_mixed 2 5 4 (by norm_num) QpTypeMixed.headOrd_mixedGateLit
        f0 hf hdeg,
      QpTypeMixed.decodePath_mixedGateLit, QpTypeMixed.decodeShapes_mixedGateLit]
    exact hfib
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_unram 2 5 4 (by norm_num)
    RealInstanceW4Gates.sigma5 QpTypeMixed.mixedGateLit 1
    (QpTypeMixed.mixedGateLit_mem_omMenu4 1) f0 hf hdeg hfib4
  -- the factor list is nonempty (the mutated type has five parts)
  have hlen : F.factors.length = 5 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  have hne : F.factors ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hne
  -- its bundle pair is (1,1)
  have hin := QpTypeEisenstein.efOf_mem_qpType 2 F hg
  rw [hF] at hin
  have hef : QpType.efOf 2 (F.data g hg) = (1, 1) := by
    simpa using hin
  -- the degree ledger: natDegree g = 1
  have hdegpos : 0 < g.natDegree :=
    QpTypeMixed.natDegree_pos_of_irreducible_map 2 (F.monic g hg) (F.irred g hg)
  have hdg : g.natDegree = 1 := by
    have hml := QpTypeMixed.ef_mul_eq_natDegree 2 hdegpos (F.data g hg)
    have he : QpType.eOf 2 (F.data g hg) = 1 := congrArg Prod.fst hef
    have hfd : QpType.fOf 2 (F.data g hg) = 1 := congrArg Prod.snd hef
    rw [he, hfd] at hml
    omega
  -- a degree-1 factor of f0 over ℚ_2 — against the axiom-free anchor
  have hdvd : g ∣ f0 := F.prod_eq ▸ List.dvd_prod hg
  have hmapdvd : g.map (algebraMap ℤ_[2] ℚ_[2]) ∣ f0.map (algebraMap ℤ_[2] ℚ_[2]) :=
    Polynomial.map_dvd _ hdvd
  have hmapdeg : (g.map (algebraMap ℤ_[2] ℚ_[2])).natDegree = 1 := by
    rw [(F.monic g hg).natDegree_map]
    exact hdg
  exact QpTypeMixed.mixedGateFiber_no_linear_factor 2 (by norm_num) (by norm_num)
    hf hdeg hfib ⟨g.map (algebraMap ℤ_[2] ℚ_[2]), hmapdeg, hmapdvd⟩

end LeanUrat.OM.QpTypeMixedScratchUnram

#print axioms LeanUrat.OM.QpTypeMixedScratchUnram.mutation_unram_refuted
```

`lake env lean` output on the scratch (2026-07-22): NO errors; the single info line

```
'LeanUrat.OM.QpTypeMixedScratchUnram.mutation_unram_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeMixedScratchUnram.om_leaf_faithful_MUTATED_unram]
```

i.e. `False` follows from the MUTATED axiom + Lean core + PROVED theorems alone — the real
(re-scoped) `om_leaf_faithful` does NOT appear in the refutation's cone.

**Probe (ii) — the WRONG-E SINGLETON mutation of the RE-SCOPED axiom is refuted at the
mixed-gate stratum (machine-checked 2026-07-22, scratch NOT committed; enabled by the degree
ledger `ef_mul_eq_natDegree` landing).** The scratch below — same re-scoped hypotheses,
conclusion mutated to the SINGLETON type `{(2,1)}` (the W1 gate type; invisible to any
no-linear-factor guard, since it asserts no degree-1 part) — compiled with zero errors:
`False` derives from the mutated axiom + `mixedGateFiber_nonempty` +
`QpTypeEisenstein.qpType_singleton_forces` + the AXIOM-FREE `ef_mul_eq_natDegree`
(`2·1 = 5` is refuted by arithmetic).

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeEisenstein
import LeanUrat.OM.QpTypeMixed

namespace LeanUrat.OM.QpTypeMixedScratchESing

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of the RE-SCOPED `om_leaf_faithful` verbatim
(omMenu4 menu + fiberOf4 dispatch), conclusion replaced by the WRONG-E SINGLETON type
`{(2,1)}` (the W1 gate type — a plausible copy-paste payload error). -/
axiom om_leaf_faithful_MUTATED_esingleton (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ)
    (hT : T ∈ MultiSlopeMenu.omMenu4 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf4 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

/-- The wrong-e singleton mutation is REFUTED at the mixed-gate stratum: the inhabited fiber
would carry a SINGLETON factorization whose unique factor is `f0` itself with bundle payload
`efOf = (2,1)` (`QpTypeEisenstein.qpType_singleton_forces`), but the AXIOM-FREE degree ledger
(`QpTypeMixed.ef_mul_eq_natDegree`) forces `eOf · fOf = deg f0 = 5 ≠ 2·1`. -/
theorem mutation_esingleton_refuted : False := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := QpTypeMixed.mixedGateFiber_nonempty
  have hfib4 : OmLeafFaithful.fiberOf4 2 5 4 (by norm_num) QpTypeMixed.mixedGateLit
      f0 hf hdeg := by
    rw [OmLeafFaithful.fiberOf4_mixed 2 5 4 (by norm_num) QpTypeMixed.headOrd_mixedGateLit
        f0 hf hdeg,
      QpTypeMixed.decodePath_mixedGateLit, QpTypeMixed.decodeShapes_mixedGateLit]
    exact hfib
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_esingleton 2 5 4 (by norm_num)
    RealInstanceW4Gates.sigma5 QpTypeMixed.mixedGateLit 1
    (QpTypeMixed.mixedGateLit_mem_omMenu4 1) f0 hf hdeg hfib4
  obtain ⟨hmem, hef⟩ := QpTypeEisenstein.qpType_singleton_forces 2 F ((2 : ℕ), (1 : ℕ)) hF
  have hdegpos : 0 < f0.natDegree := by rw [hdeg]; norm_num
  have hml := QpTypeMixed.ef_mul_eq_natDegree 2 hdegpos (F.data f0 hmem)
  have he : QpType.eOf 2 (F.data f0 hmem) = 2 := congrArg Prod.fst hef
  have hfd : QpType.fOf 2 (F.data f0 hmem) = 1 := congrArg Prod.snd hef
  rw [he, hfd, hdeg] at hml
  omega

end LeanUrat.OM.QpTypeMixedScratchESing

#print axioms LeanUrat.OM.QpTypeMixedScratchESing.mutation_esingleton_refuted
```

`lake env lean` output on the scratch (2026-07-22): NO errors; the single info line

```
'LeanUrat.OM.QpTypeMixedScratchESing.mutation_esingleton_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeMixedScratchESing.om_leaf_faithful_MUTATED_esingleton]
```

Together the two probes pin the re-scoped axiom's payload at its NEW menu content (the mixed
multi-slope stratum) in BOTH coordinates — factorization SHAPE (no degree-1 part may be
asserted: probe (i)) and the DEGREE LEDGER `Σ e·f = n` (probe (ii)) — against purely
axiom-free anchors, exactly as the W2/W3c probes pinned the constant-e gates. Positive
coherence: the REAL conclusion `σ₅ = {(2,1),(3,1)}` passes both guards (`2·1 + 3·1 = 5`,
no `e·f = 1` part). -/

/-! ## Block 8 — axiom census (this module declares NO axiom; everything must be core-only) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeMixed.mixedGatePath
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateSide1
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateSide2
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateSh
#print axioms LeanUrat.OM.QpTypeMixed.sidePairs_mixedGatePath
#print axioms LeanUrat.OM.QpTypeMixed.menuPath_mixedGate
#print axioms LeanUrat.OM.QpTypeMixed.shapesFor_mixedGate
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateLit_eq_canonical
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateLit_mem_omMenu4
#print axioms LeanUrat.OM.QpTypeMixed.headOrd_mixedGateLit
#print axioms LeanUrat.OM.QpTypeMixed.decodePath_mixedGateLit
#print axioms LeanUrat.OM.QpTypeMixed.decodeShapes_mixedGateLit
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_valuation
#print axioms LeanUrat.OM.QpTypeMixed.mixedGate_no_root'
#print axioms LeanUrat.OM.QpTypeMixed.mixedGate_no_root
#print axioms LeanUrat.OM.QpTypeMixed.mixedGate_no_linear_factor'
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_no_root
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_no_linear_factor
#print axioms LeanUrat.OM.QpTypeMixed.mixedGatePoly_monic
#print axioms LeanUrat.OM.QpTypeMixed.mixedGatePoly_natDegree
#print axioms LeanUrat.OM.QpTypeMixed.toBox_mixedGatePoly
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateBox_inCell
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_nonempty
#print axioms LeanUrat.OM.QpTypeMixed.natDegree_pos_of_irreducible_map
#print axioms LeanUrat.OM.QpTypeMixed.ef_mul_eq_natDegree

end AxCheck

end LeanUrat.OM.QpTypeMixed
