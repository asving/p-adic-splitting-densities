/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType
import LeanUrat.OM.WildMenuW3

/-!
# QpTypeH3 — the axiom-free H = 3 anchor for the W3c axiom re-scope
(Wild Wave 3c, `notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md` §2 item 4; 2026-07-21)

The W3c re-scope extends `om_leaf_faithful` (`OM/OmLeafFaithful.lean`) from the Wave-1 menu
`WildMenu.omMenuW` to the K-windowed `WildMenuW3.omMenuW3`. The NEW menu content at `n = 2`,
`σ = {(2,1)}` is the height-3 window leg `ramShapeAt 2 σ 3 = Tselfloop 2 ((0,3),(2,0)) [(1,1)]`
(the `k = 3` admissible multiplier). THIS module is the axiom-free machine anchor pinning the
re-scoped axiom's payload at that new leg — the H = 3 mirror of the Wave-2 anchors
`QpType.wildGateFiber_eisenstein` (H = 1 irreducibility) and `QpTypeEisenstein.gate_ef_forced`
(H = 1 fine-(e,f)):

* `wildH3_irreducible'` / `wildH3_irreducible` — **the elementary two-root valuation
  contradiction** (blueprint §2 item 4; NO Newton polygon): monic quadratic `f` over `ℤ_[p]`
  with `v(a₀) = 3` and `a₁ ∈ (p)²` is irreducible over ℚ_p. If `f` were reducible, monic
  quadratic reducibility over the integrally closed `ℤ_[p]` gives roots `a₀ = c₁·c₂`,
  `a₁ = c₁ + c₂` IN `ℤ_[p]` (`Monic.not_irreducible_iff_exists_add_mul_eq_coeff` + Gauss
  transfer `Monic.irreducible_iff_irreducible_map_fraction_map`); then
  `v(c₁) + v(c₂) = 3`, WLOG `v(c₁) ≤ v(c₂)` forces `v(c₁) ≤ 1 < 2 ≤ v(c₂)`, so
  `v(a₁) = v(c₁ + c₂) = v(c₁) ≤ 1`, contradicting `v(a₁) ≥ 2`. The primary form is the
  MEMBERSHIP form `a₁ ∈ (maximalIdeal ℤ_[p])²` (faithful under mathlib's `v(0) = 0`
  convention); the blueprint-literal disjunct form (`2 ≤ v(a₁) ∨ a₁ = 0`) is derived.
* `wildH3Fiber_valuation` / `wildH3Fiber_irreducible` — the fiber link: membership of a genuine
  monic quadratic in the LEVEL-N CLASSIFIER FIBER of the H = 3 window shape (`N ≥ 4`) forces
  `v(a₀) = 3 ∧ a₁ ∈ (p)²` (via `classify_eq_selfloop_iff` + the decode bridge — the digit
  conditions of the side `(0,3)–(2,0)` read `vOf 0 = 3`, `vOf 1 ≥ ⌈3/2⌉ = 2`), hence
  irreducibility over ℚ_p. Mirrors `QpType.wildGateFiber_valuation`/`_eisenstein` verbatim.
* `h3Fiber_nonempty` — the concrete H = 3 fiber witness: `f0 = X² + 4X + 8` over `ℤ_[2]` at
  level `N = 5` (`v(a₀) = 3`, `v(a₁) = 2`; `InCell` proved directly from the digit conditions —
  the banked `CellMenu` gates are all at `N = 3`, below the H = 3 threshold `N₀ = 4`, so no
  banked cell exists for this stratum). The re-scoped axiom's H = 3 instance quantifies over a
  genuinely NONEMPTY fiber: the mutation probes below have real force.
* `ef_of_wildH3` / `gate_h3_ef_forced` — **route (a), the parity argument (blueprint §2
  item 4)**: for ANY `LocalFactorData` bundle on an H = 3 fiber member, `(e, f) = (2, 1)`.
  H = 3 members are NOT Eisenstein (`v(a₀) = 3 ≠ 1`), so `QpTypeEisenstein.ef_of_eisenstein`
  does not apply; instead: the fundamental identity `e·f = [L:ℚ_p] = 2` leaves `e ∈ {1, 2}`,
  and `e = 1` is refuted by parity — with `algebraMap p = u·ϖ` (`e = 1`), the root equation
  `y² = −(a₀ + a₁y)` in the DVR `O` has ϖ-order exactly 3 on `a₀`, `≥ 2 + k` on `a₁y`, and
  exactly `2k` on `y²` (`y = u_y·ϖᵏ`): `k ≤ 1` makes the RHS divisible by `ϖ^{2k+1}` but not
  the LHS; `k ≥ 2` makes `ϖ⁴ ∣ a₀` — both machine-refuted by pure divisibility in the DVR
  (no valuation function needed). **Honest scope**: the bundle slot `D` is exactly the
  existence content the axiom carries (mathlib at the pin cannot CONSTRUCT a bundle for a wild
  quadratic); like `QpTypeEisenstein.gate_ef_forced`, this theorem is the machine GUARD that
  any carried bundle's `(e,f)` payload is forced — consumed contrapositively by the fine-swap
  mutation probe.
* `ramShapeAt_h3` / `h3_mem_omMenuW3` — the W3-menu bookkeeping: the H = 3 literal IS
  `WildMenuW3.ramShapeAt 2 ⟨{(2,1)}⟩ 3`, and it is a member of the window-3 menu
  `omMenuW3 2 3 ⟨{(2,1)}⟩` (the probe's `hT` leg).
* **Mutation probes (§2 item 4 last bullet)**: both the SPLIT-TYPE mutation `{(1,1),(1,1)}`
  and the FINE-(e,f)-SWAP mutation `{(1,2)}` of the RE-SCOPED axiom derive machine-checked
  `False` at the H = 3 stratum — scratches NOT committed; verbatim text + output recorded in
  the two `Mutation probe evidence` comment blocks below.

Leaf module: no existing file is modified (the census append to `AxChk_baseline.lean` is Part C
of the wave). **No axiom, no sorry** — every declaration here must be core-only (AxCheck at
bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.QpTypeH3

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Block 1 — the H = 3 stratum literals (the k = 3 window leg at n = 2, σ = {(2,1)}) -/

/-- The H = 3 menu path `[(0,3),(2,0)]` (the height-3 self-loop, `H = fSum σ · 3 = 3`). -/
def h3Path : List (ℕ × ℕ) := [(0, 3), (2, 0)]

/-- The H = 3 side `((0,3),(2,0))` (slope `−3/2`). -/
def h3Side : (ℕ × ℕ) × (ℕ × ℕ) := ((0, 3), (2, 0))

/-- The H = 3 residual shape `[(1,1)]` (one linear residual factor, μ = 1 — the SAME `wShape σ`
as the Wave-1 gate: the side degree is `gcd(3,2) = 1 = fSum σ`, the keystone
`WildMenuW3.gcd_admissible`). -/
def h3Shape : List (ℕ × ℕ) := [(1, 1)]

theorem sidePairs_h3Path : sidePairs h3Path = [h3Side] := rfl

/-- The H = 3 path is a menu path at every level `N ≥ 4` (= the leg's threshold `H + 1`). -/
theorem menuPath_h3 {N : ℕ} (hN : 4 ≤ N) : MenuPath 2 N h3Path :=
  ⟨3, (2, 0), [], rfl, by omega, by omega, by norm_num, by norm_num, ChainOK.nil rfl rfl⟩

theorem shapesFor_h3 : ShapesFor h3Path [h3Shape] := by
  unfold ShapesFor
  rw [sidePairs_h3Path]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rw [mem_shapesOfDegree_iff]
  refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
  · intro q hq
    rw [h3Shape, List.mem_singleton] at hq
    subst hq
    exact ⟨le_refl 1, le_refl 1⟩
  · rfl

/-- **The H = 3 literal is the k = 3 window leg** of the totally ramified quadratic type:
`WildMenuW3.ramShapeAt 2 {(2,1)} 3 = Tselfloop 2 ((0,3),(2,0)) [(1,1)]`
(`fSum = 1`, `wShape = [(1,1)]`, height `1·3 = 3`). -/
theorem ramShapeAt_h3 :
    WildMenuW3.ramShapeAt 2 (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) 3
      = ClassifierBridgeFiber.Tselfloop 2 h3Side h3Shape := by
  have hf1 : WildMenu.fSum (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) = 1 := by
    simp [WildMenu.fSum]
  have hws : WildMenu.wShape (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) = [(1, 1)] := by
    simp [WildMenu.wShape, Multiset.sort_singleton]
  rw [WildMenuW3.ramShapeAt_def, hf1, hws]
  rfl

/-- **The H = 3 literal is a member of the window-3 menu** `omMenuW3 2 3 {(2,1)}` — the `hT` leg
of the re-scoped axiom's H = 3 instance (`k = 3 ∈ admissibleK 2 3`: `gcd(3, 2) = 1`). -/
theorem h3_mem_omMenuW3 :
    ClassifierBridgeFiber.Tselfloop 2 h3Side h3Shape
      ∈ WildMenuW3.omMenuW3 2 3 (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) := by
  have hc : WildMenu.constERam 2 (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) := by
    refine ⟨2, le_refl 2, by simp, ?_, by simp [WildMenu.fSum]⟩
    intro pr hpr
    simp only [Multiset.mem_singleton] at hpr
    subst hpr
    exact ⟨rfl, le_refl 1⟩
  rw [WildMenuW3.omMenuW3, Finset.mem_union]
  right
  rw [WildMenuW3.mem_ramShapes3]
  refine ⟨hc, 3, ?_, ramShapeAt_h3⟩
  rw [WildMenuW3.mem_admissibleK]
  have hf1 : WildMenu.fSum (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) = 1 := by
    simp [WildMenu.fSum]
  rw [hf1]
  exact ⟨⟨by omega, by omega⟩, by decide⟩

/-! ## Block 2 — the decode bridge, power form

`QpType.mem_maximalIdeal_of_one_le_zmodValuation` decodes a box valuation `≥ 1` to membership in
`(p)`; the H = 3 side needs the `≥ 2 → (p)²` form (same route, `k`-generic). -/

/-- **Decoder (power lower bound).** A box-native valuation `≥ k` (with `k ≤ N`) decodes to
membership in `(maximalIdeal ℤ_[p])^k` (correctly absorbing the `x = 0` / vanished-residue
cases: a vanished level-`N` residue puts `x ∈ (p^N) ⊆ (p^k)`). -/
theorem mem_maximalIdeal_pow_of_le_zmodValuation {N k : ℕ} (hkN : k ≤ N) {x : ℤ_[p]}
    (h : k ≤ PadicLift.zmodValuation p N (PadicInt.toZModPow N x)) :
    x ∈ (maximalIdeal ℤ_[p]) ^ k := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  by_cases hy : PadicInt.toZModPow N x = 0
  · -- vanished residue: x ∈ (p^N) ≤ (p^k)
    have hker : x ∈ Ideal.span {(p : ℤ_[p]) ^ N} := by
      rw [← PadicInt.ker_toZModPow]; exact RingHom.mem_ker.mpr hy
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hkN) hker
  · obtain ⟨hx0, heq, -⟩ := QpType.valuation_eq_of_toZModPow_ne_zero p hy
    exact (PadicInt.mem_span_pow_iff_le_valuation x hx0 k).mpr (by omega)

/-! ## Block 3 — the axiom-free H = 3 irreducibility (the elementary two-root argument) -/

/-- **The abstract H = 3 irreducibility theorem (membership form — the primary one).** Monic
degree-2 `f` over `ℤ_[p]` with `v(a₀) = 3` and `a₁ ∈ (p)²` is irreducible over ℚ_p.

Route (blueprint §2 item 4, NO Newton polygon): reducibility of the monic quadratic over the
fraction field transfers to `ℤ_[p]` (Gauss, `irreducible_iff_irreducible_map_fraction_map`),
where it means `a₀ = c₁·c₂`, `a₁ = c₁ + c₂` (`not_irreducible_iff_exists_add_mul_eq_coeff`).
Then `v(c₁) + v(c₂) = 3`; WLOG `v(c₁) ≤ v(c₂)`, so `2·v(c₁) ≤ 3` gives `v(c₁) ≤ 1` and
`v(c₂) = 3 − v(c₁) ≥ 2 > v(c₁)`; the ultrametric then pins `v(a₁) = v(c₁) ≤ 1 < 2`,
contradicting `a₁ ∈ (p)²`. (`a₁ = 0` is impossible: `c₂ = −c₁` would force `2·v(c₁) = 3`.) -/
theorem wildH3_irreducible' {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (h0 : (f.coeff 0).valuation = 3) (h1 : f.coeff 1 ∈ (maximalIdeal ℤ_[p]) ^ 2) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  have ha0 : f.coeff 0 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at h0
    omega
  have hirr : Irreducible f := by
    by_contra hred
    obtain ⟨c₁, c₂, hmul, hadd⟩ :=
      (hf.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp hred
    -- both roots are nonzero and their valuations sum to 3
    have hc1 : c₁ ≠ 0 := by rintro rfl; rw [zero_mul] at hmul; exact ha0 hmul
    have hc2 : c₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hmul; exact ha0 hmul
    have hsum : c₁.valuation + c₂.valuation = 3 := by
      rw [← PadicInt.valuation_mul hc1 hc2, ← hmul, h0]
    -- a₁ = c₁ + c₂ ≠ 0 (else 2·v(c₁) = 3 — parity)
    have hne : c₁ + c₂ ≠ 0 := by
      intro hz
      have h2 : c₂ = -c₁ := eq_neg_of_add_eq_zero_right hz
      rw [h2, QpType.valuation_neg] at hsum
      omega
    -- v(a₁) ≥ 2 from the (p)² membership
    have hv1 : 2 ≤ (c₁ + c₂).valuation := by
      have hna : f.coeff 1 ≠ 0 := by rw [hadd]; exact hne
      have hm := (PadicInt.mem_span_pow_iff_le_valuation _ hna 2).mp (by
        rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] at h1)
      rwa [hadd] at hm
    -- the symmetric core: the smaller-valuation root pins v(c₁ + c₂) ≤ 1
    have key : ∀ a b : ℤ_[p], a ≠ 0 → a + b ≠ 0 →
        a.valuation + b.valuation = 3 → a.valuation ≤ b.valuation →
        2 ≤ (a + b).valuation → False := by
      intro a b ha hab hs hle hv
      -- a = (a + b) + (−b): min(v(a+b), v(b)) ≤ v(a) ≤ 1, but both arms are ≥ 2
      have h' : a = (a + b) + (-b) := by ring
      have hmin : min (a + b).valuation (-b).valuation ≤ a.valuation := by
        have hh := PadicInt.le_valuation_add (x := a + b) (y := -b) (by rw [← h']; exact ha)
        rwa [← h'] at hh
      rw [QpType.valuation_neg] at hmin
      omega
    rcases le_total c₁.valuation c₂.valuation with hle | hle
    · exact key c₁ c₂ hc1 hne hsum hle hv1
    · exact key c₂ c₁ hc2 (by rwa [add_comm]) (by omega) hle (by rwa [add_comm])
  exact (hf.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirr

/-- **The H = 3 irreducibility theorem (valuation form, blueprint literal).** The `∨ a₁ = 0`
disjunct absorbs mathlib's `v(0) = 0` convention; the membership form `wildH3_irreducible'` is
the faithful primary and is what the fiber link uses. -/
theorem wildH3_irreducible {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (h0 : (f.coeff 0).valuation = 3) (h1 : 2 ≤ (f.coeff 1).valuation ∨ f.coeff 1 = 0) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  refine wildH3_irreducible' p hf hdeg h0 ?_
  rcases h1 with h1 | h1
  · by_cases hc : f.coeff 1 = 0
    · rw [hc]; exact Ideal.zero_mem _
    · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
      exact (PadicInt.mem_span_pow_iff_le_valuation _ hc 2).mpr h1
  · rw [h1]; exact Ideal.zero_mem _

/-! ## Block 4 — the fiber link: the H = 3 classifier fiber forces the valuation conditions -/

/-- **The H = 3 fiber link.** If `toBox f` lies in the level-`N` classifier fiber of the H = 3
window shape (`N ≥ 4` — the leg's threshold), then `v(a₀) = 3` and `a₁ ∈ (p)²`. Mirrors
`QpType.wildGateFiber_valuation` through `classify_eq_selfloop_iff` + `inCell_mkCell_iff` +
the decode bridge; the digit conditions of the side `(0,3)–(2,0)` read `vOf 0 = 3` (vertex
exactness) and `vOf 1 ≥ 3/2`, i.e. `≥ 2` (SideAbove at the midpoint). -/
theorem wildH3Fiber_valuation {N : ℕ} (hN0 : 0 < N) (hN4 : 4 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : B.classify p 2 N (PadicLift.toBox p 2 N hN0 f hf hdeg)
      = ClassifierBridgeFiber.Tselfloop 2 h3Side h3Shape) :
    (f.coeff 0).valuation = 3 ∧ f.coeff 1 ∈ (maximalIdeal ℤ_[p]) ^ 2 := by
  set fbox := PadicLift.toBox p 2 N hN0 f hf hdeg with hfbox
  -- fiber → InCell → Matches
  have hIn : InCell p fbox (mkCell 2 h3Path [h3Shape]) :=
    (ClassifierBridgeFiber2.classify_eq_selfloop_iff 2 N hN0 (by norm_num) h3Path
      (menuPath_h3 hN4) h3Side sidePairs_h3Path h3Shape shapesFor_h3
      (by intro q hq; rw [h3Shape, List.mem_singleton] at hq; subst hq; rfl)
      (by simp [h3Shape]) fbox).mp hfib
  have hM : Matches p fbox h3Path [h3Shape] :=
    (inCell_mkCell_iff p (menuPath_h3 hN4) shapesFor_h3).mp hIn
  -- the box digit conditions
  have hv0 : vOf p fbox 0 = 3 := hM.1 (0, 3) (by simp [h3Path])
  have hSM : SideMatch p fbox h3Shape h3Side := by
    have h2 := hM.2
    rw [sidePairs_h3Path] at h2
    cases h2 with
    | cons h _ => exact h
  have hv1 : 2 ≤ vOf p fbox 1 := by
    have hline := hSM.1 1 (by norm_num [h3Side]) (by norm_num [h3Side])
    have hhalf : lineAt h3Side ((1 : ℕ) : ℚ) = 3 / 2 := by
      norm_num [lineAt, slopeQ, h3Side]
    rw [hhalf] at hline
    by_contra hlt
    rw [not_le] at hlt
    have h01 : vOf p fbox 1 = 0 ∨ vOf p fbox 1 = 1 := by omega
    rcases h01 with h01 | h01 <;> rw [h01] at hline <;> norm_num at hline
  -- decode through toBox
  have hvOf : ∀ i, vOf p fbox i
      = PadicLift.zmodValuation p N (PadicInt.toZModPow N (f.coeff i)) := fun i => by
    simp only [vOf, hfbox, PadicLift.toBox_val, Polynomial.coeff_map]
  rw [hvOf 0] at hv0
  rw [hvOf 1] at hv1
  obtain ⟨-, hval0⟩ := QpType.valuation_eq_of_zmodValuation_lt p (by omega : 3 < N) hv0
  exact ⟨hval0, mem_maximalIdeal_pow_of_le_zmodValuation p (by omega : 2 ≤ N) hv1⟩

/-- **The axiom-free H = 3 anchor.** Membership in the level-`N` classifier fiber of the H = 3
window shape forces IRREDUCIBILITY over ℚ_p — unconditionally, no axiom. Any mutation of the
re-scoped `om_leaf_faithful` asserting a SPLIT type on this fiber contradicts this theorem
(probe evidence below). The H = 3 mirror of `QpType.wildGateFiber_eisenstein`. -/
theorem wildH3Fiber_irreducible {N : ℕ} (hN0 : 0 < N) (hN4 : 4 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : B.classify p 2 N (PadicLift.toBox p 2 N hN0 f hf hdeg)
      = ClassifierBridgeFiber.Tselfloop 2 h3Side h3Shape) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  obtain ⟨h0, h1⟩ := wildH3Fiber_valuation p hN0 hN4 hf hdeg hfib
  exact wildH3_irreducible' p hf hdeg h0 h1

/-! ## Block 5 — the concrete H = 3 fiber witness (p = 2, N = 5)

No banked `CellMenu` gate exists at the H = 3 cell (`[(0,3),(2,0)]` needs `N ≥ 4`; the W0
numeric gates are all at `N = 3`), so the box element of `f0 = X² + 2²X + 2³` is constructed
and its `InCell` proved directly from the digit conditions, mirroring `CellMenu.gate_S2C1`. -/

/-- The concrete H = 3 fiber witness: `X² + 4X + 8` over `ℤ_[2]` (`v(a₀) = 3`, `v(a₁) = 2`). -/
noncomputable def h3Poly : Polynomial ℤ_[2] := X ^ 2 + C 4 * X + C 8

theorem h3Poly_monic : h3Poly.Monic := by unfold h3Poly; monicity!

theorem h3Poly_natDegree : h3Poly.natDegree = 2 := by unfold h3Poly; compute_degree!

/-- The level-5 box of the witness. -/
noncomputable def h3box : QuotientBox.monicBox 2 5 2 :=
  ⟨X ^ 2 + C 4 * X + C 8, ⟨by monicity!, by compute_degree!⟩⟩

/-- `toBox` sends the genuine witness to the level-5 box. -/
theorem toBox_h3Poly :
    PadicLift.toBox 2 2 5 (by norm_num) h3Poly h3Poly_monic h3Poly_natDegree = h3box := by
  apply Subtype.ext
  rw [PadicLift.toBox_val]
  show h3Poly.map (PadicInt.toZModPow 5) = (X ^ 2 + C 4 * X + C 8 : (ZMod (2 ^ 5))[X])
  unfold h3Poly
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, map_ofNat]

/-! ### Level-5 valuation and unit-residue facts (`p = 2`, `ZMod 32`) -/

theorem h3v1 : PadicLift.zmodValuation 2 5 (1 : ZMod (2 ^ 5)) = 0 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem h3v4 : PadicLift.zmodValuation 2 5 (4 : ZMod (2 ^ 5)) = 2 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem h3v8 : PadicLift.zmodValuation 2 5 (8 : ZMod (2 ^ 5)) = 3 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

theorem h3u1 : PadicLift.zmodUnitResidue 2 5 (1 : ZMod (2 ^ 5)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (1 : ZMod (2 ^ 5))) (u := 1) (by decide) h3v1 (by decide)
  simpa using h

theorem h3u8 : PadicLift.zmodUnitResidue 2 5 (8 : ZMod (2 ^ 5)) = 1 := by
  have h := zmodUnitResidue_eq 2 (x := (8 : ZMod (2 ^ 5))) (u := 1) (by decide) h3v8 (by decide)
  simpa using h

/-- The witness box lies in the H = 3 cell (digit conditions checked directly). -/
theorem h3box_inCell : InCell 2 h3box (mkCell 2 h3Path [h3Shape]) := by
  have hc0 : (h3box.1).coeff 0 = 8 := by simp [h3box]
  have hc1 : (h3box.1).coeff 1 = 4 := by simp [h3box]
  have hc2 : (h3box.1).coeff 2 = 1 := by simp [h3box]
  have hv0 : vOf 2 h3box 0 = 3 := by unfold vOf; rw [hc0]; exact h3v8
  have hv1 : vOf 2 h3box 1 = 2 := by unfold vOf; rw [hc1]; exact h3v4
  have hv2 : vOf 2 h3box 2 = 0 := by unfold vOf; rw [hc2]; exact h3v1
  have hsd := side_data (pr := ((0, 3), (2, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 3), (2, 0))).e = 2 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 3), (2, 0))).h = -3 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 3), (2, 0))) = 1 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 5 ((h3box.1).coeff 0) : ℤ)
      = ((mkSide ((0, 3), (2, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 3), (2, 0))).h := by
    rw [hc0, h3v8]; simp [mkSide]
  have hg1 : (PadicLift.zmodValuation 2 5 ((h3box.1).coeff 2) : ℤ)
      = ((mkSide ((0, 3), (2, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 3), (2, 0))).h := by
    rw [hc2, h3v1, hH]; norm_num [mkSide]
  have hb0 : B.boxCoeffData 2 5 (mkSide ((0, 3), (2, 0))) h3box 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0, h3u8]
  have hb1 : B.boxCoeffData 2 5 (mkSide ((0, 3), (2, 0))) h3box 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 2) (by rw [hE]; decide) hg1, hc2, h3u1]
  have hR : residualOf 2 h3box ((0, 3), (2, 0)) = X + 1 := by
    rw [residual_deg_one 2 h3box _ hD, hb0, hb1, map_one, one_mul]
    ring
  have hmenu : MenuPath 2 5 h3Path := menuPath_h3 (by norm_num)
  have hexact : ∀ q ∈ h3Path, vOf 2 h3box q.1 = q.2 := by
    intro q hq
    fin_cases hq <;> assumption
  have habove : SideAbove 2 h3box ((0, 3), (2, 0)) := by
    intro i hi0 hi2
    interval_cases i
    · rw [hv0]; norm_num [lineAt, slopeQ]
    · rw [hv1]; norm_num [lineAt, slopeQ]
    · rw [hv2]; norm_num [lineAt, slopeQ]
  have hmatch : Matches 2 h3box h3Path [h3Shape] :=
    ⟨hexact, List.Forall₂.cons ⟨habove, by rw [hR, polyShape_X_add_one 2]; simp [h3Shape]⟩
      List.Forall₂.nil⟩
  exact ⟨_, _, hmenu, shapesFor_h3, rfl, hmatch⟩

/-- **The H = 3 fiber is INHABITED** by the concrete `h3Poly = X² + 4X + 8` at `p = 2`,
`N = 5`: the re-scoped axiom's H = 3 window instance quantifies over a genuinely nonempty
fiber, so the mutation probes (evidence blocks below) have real force. Route: direct `InCell`
(`h3box_inCell`) + `ClassifierBridgeFiber2.classify_eq_selfloop_iff` (mpr). -/
theorem h3Fiber_nonempty :
    ∃ (f0 : Polynomial ℤ_[2]) (hf : f0.Monic) (hdeg : f0.natDegree = 2),
      B.classify 2 2 5 (PadicLift.toBox 2 2 5 (by norm_num) f0 hf hdeg)
        = ClassifierBridgeFiber.Tselfloop 2 h3Side h3Shape := by
  refine ⟨h3Poly, h3Poly_monic, h3Poly_natDegree, ?_⟩
  rw [toBox_h3Poly]
  exact (ClassifierBridgeFiber2.classify_eq_selfloop_iff 2 5 (by norm_num) (by norm_num)
    h3Path (menuPath_h3 (by norm_num)) h3Side sidePairs_h3Path h3Shape shapesFor_h3
    (by intro q hq; rw [h3Shape, List.mem_singleton] at hq; subst hq; rfl)
    (by simp [h3Shape]) h3box).mpr h3box_inCell

/-! ## Block 6 — route (a): the parity argument forces `(e, f) = (2, 1)` on the H = 3 fiber -/

/-- DVR divisibility helper: `ϖ^(m+1)` never divides `c·ϖ^m` for a unit `c` and irreducible
`ϖ` (cancel `ϖ^m` in the domain; `ϖ ∣ c` would make `ϖ` a unit). -/
theorem not_pow_succ_dvd_unit_mul_pow {O : Type*} [CommRing O] [IsDomain O] {ϖ c : O}
    (hϖ : Irreducible ϖ) (hc : IsUnit c) (m : ℕ) : ¬ (ϖ ^ (m + 1) ∣ c * ϖ ^ m) := by
  rintro ⟨d, hd⟩
  have hcan : c = ϖ * d := by
    have h1 : ϖ ^ m * c = ϖ ^ m * (ϖ * d) := by
      rw [mul_comm (ϖ ^ m) c, hd, pow_succ]
      ring
    exact mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (hcan ▸ hc))

/-- **The H = 3 `(e, f)` theorem (master form, axiom-free — route (a), the parity argument).**
For monic degree-2 `f` over `ℤ_[p]` with `v(a₀) = 3` and `a₁ ∈ (p)²`, EVERY local-factor
bundle `D : LocalFactorData p f` has `eOf p D = 2` and `fOf p D = 1`.

Route: the fundamental identity `e·f = [L:ℚ_p] = 2` (instance stack as in
`QpTypeEisenstein.ef_of_eisenstein`) leaves `e ∈ {1, 2}`; `e = 1` is refuted by PARITY. With
`algebraMap p = u_p·ϖ` (that is `e = 1`), the descended root `y = u_y·ϖᵏ` of
`y² = −(a₀ + a₁·y)` gives ϖ-order exactly `3` on `a₀ = w·p³` (`w` the unit coefficient of
`v(a₀) = 3`), `≥ 2 + k` on `a₁·y` (`a₁ = p²·b`), and exactly `2k` on `y²`: for `k ≤ 1` the RHS
is divisible by `ϖ^{2k+1}` but the LHS is not (`not_pow_succ_dvd_unit_mul_pow`); for `k ≥ 2`
the RHS forces `ϖ⁴ ∣ w·p³` — a unit times `ϖ³` — likewise impossible. Pure divisibility in the
DVR; no valuation function.

**Honest scope**: the bundle slot `D` is exactly the existence content `om_leaf_faithful`
carries (mathlib at the pin cannot construct a bundle for a wild quadratic; same status as
`QpTypeEisenstein.gate_ef_forced`) — this theorem GUARDS the payload of any carried bundle. -/
theorem ef_of_wildH3 {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (h0 : (f.coeff 0).valuation = 3) (h1 : f.coeff 1 ∈ (maximalIdeal ℤ_[p]) ^ 2)
    (D : QpType.LocalFactorData p f) :
    QpType.eOf p D = 2 ∧ QpType.fOf p D = 1 := by
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
  -- the instance stack for the fundamental identity
  haveI hFD : FiniteDimensional ℚ_[p] D.L :=
    FiniteDimensional.of_finrank_pos (by rw [D.finrank_eq]; omega)
  haveI : IsFractionRing D.O D.L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] D.L D.O
  haveI : Module.Finite ℤ_[p] D.O := IsIntegralClosure.finite ℤ_[p] ℚ_[p] D.L D.O
  -- the root of f in L descends to O
  obtain ⟨x, hxroot, -⟩ := D.hasRoot
  rw [Polynomial.aeval_map_algebraMap] at hxroot
  have hxint : IsIntegral ℤ_[p] x := ⟨f, hf, by rwa [Polynomial.aeval_def] at hxroot⟩
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := D.O) (R := ℤ_[p]) (B := D.L)).mp hxint
  have hyroot : Polynomial.aeval y f = 0 := by
    apply IsIntegralClosure.algebraMap_injective D.O ℤ_[p] D.L
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, hy]
    exact hxroot
  -- injectivity of ℤ_[p] → O
  have hinjL : Function.Injective (algebraMap ℤ_[p] D.L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] D.L]
    exact (algebraMap ℚ_[p] D.L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have hinj : Function.Injective (algebraMap ℤ_[p] D.O) := by
    intro a b hab
    apply hinjL
    rw [IsScalarTower.algebraMap_eq ℤ_[p] D.O D.L, RingHom.comp_apply, RingHom.comp_apply, hab]
  have hfp0 : algebraMap ℤ_[p] D.O (p : ℤ_[p]) ≠ 0 := by
    intro h
    exact (PadicInt.prime_p (p := p)).ne_zero (hinj (by rw [h, map_zero]))
  -- coefficient data: a₀ = w·p³ (w a unit), a₁ = p²·b
  have ha0ne : f.coeff 0 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at h0
    omega
  set w : ℤ_[p]ˣ := PadicInt.unitCoeff ha0ne with hwdef
  have hw : f.coeff 0 = (w : ℤ_[p]) * (p : ℤ_[p]) ^ 3 := by
    conv_lhs => rw [PadicInt.unitCoeff_spec ha0ne]
    rw [h0]
  obtain ⟨b, hb⟩ : (p : ℤ_[p]) ^ 2 ∣ f.coeff 1 := by
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at h1
  -- the root equation in O: aM(a₀) + aM(a₁)·y + y² = 0
  have hexp : ∑ i ∈ Finset.range (f.natDegree + 1),
      algebraMap ℤ_[p] D.O (f.coeff i) * y ^ i = 0 := by
    calc ∑ i ∈ Finset.range (f.natDegree + 1), algebraMap ℤ_[p] D.O (f.coeff i) * y ^ i
        = ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i • y ^ i :=
          Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm
      _ = Polynomial.aeval y f := (Polynomial.aeval_eq_sum_range y).symm
      _ = 0 := hyroot
  rw [Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul, hdeg,
    Finset.sum_range_succ, Finset.sum_range_one, pow_zero, mul_one, pow_one] at hexp
  -- hexp : aM(a₀) + aM(a₁)·y + y² = 0
  -- the DVR uniformizer and the decomposition of p
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.O
  obtain ⟨E, up, hpE⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfp0 hϖ
  -- e = E: map(p·ℤ_p) = m_O^E by the decomposition, ramificationIdx = E by spec
  have hassoc : Associated (algebraMap ℤ_[p] D.O (p : ℤ_[p])) (ϖ ^ E) :=
    Associated.symm ⟨up, by rw [mul_comm]; exact hpE.symm⟩
  have hspan : Ideal.map (algebraMap ℤ_[p] D.O) (maximalIdeal ℤ_[p])
      = maximalIdeal D.O ^ E := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hgt : ¬ Ideal.map (algebraMap ℤ_[p] D.O) (maximalIdeal ℤ_[p])
      ≤ maximalIdeal D.O ^ (E + 1) := by
    rw [hspan, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton]
    intro hdvd
    have hle := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hdvd
    rw [hϖ.addVal_pow, hϖ.addVal_pow] at hle
    have : E + 1 ≤ E := by exact_mod_cast hle
    omega
  have he_val : QpType.eOf p D = E := by
    show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = E
    exact Ideal.ramificationIdx_spec (le_of_eq hspan) hgt
  -- the fundamental identity e·f = [L:ℚ_p] = 2
  have hbot : maximalIdeal ℤ_[p] ≠ ⊥ := by
    intro hbb
    have hpmem : (p : ℤ_[p]) ∈ (⊥ : Ideal ℤ_[p]) := by
      rw [← hbb, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    exact (PadicInt.prime_p (p := p)).ne_zero (Ideal.mem_bot.mp hpmem)
  have hef : QpType.eOf p D * QpType.fOf p D = 2 := by
    show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O) *
      Ideal.inertiaDeg (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = 2
    rw [Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (S := D.O) (K := ℚ_[p]) (L := D.L)
      hbot, D.finrank_eq, hdeg]
  -- y ≠ 0, decomposed as u_y·ϖᵏ
  have hy0 : y ≠ 0 := by
    intro h0y
    rw [h0y] at hexp
    have hz : algebraMap ℤ_[p] D.O (f.coeff 0) = 0 := by simpa using hexp
    exact ha0ne (hinj (by rw [hz, map_zero]))
  obtain ⟨k, uy, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  -- THE PARITY REFUTATION of E = 1
  have hEne1 : E ≠ 1 := by
    intro hE1
    rw [hE1, pow_one] at hpE
    -- A₀ = c₀·ϖ³ with c₀ a unit
    set c₀ : D.O := algebraMap ℤ_[p] D.O ((w : ℤ_[p])) * (up : D.O) ^ 3 with hc₀def
    have hc₀ : IsUnit c₀ := (w.isUnit.map (algebraMap ℤ_[p] D.O)).mul (up.isUnit.pow 3)
    have hA0 : algebraMap ℤ_[p] D.O (f.coeff 0) = c₀ * ϖ ^ 3 := by
      rw [hw, map_mul, map_pow, hpE, hc₀def]
      ring
    have hA1y : algebraMap ℤ_[p] D.O (f.coeff 1) * y
        = (algebraMap ℤ_[p] D.O b * (up : D.O) ^ 2 * (uy : D.O)) * ϖ ^ (2 + k) := by
      rw [hb, map_mul, map_pow, hpE, hyk, pow_add]
      ring
    have hy2 : y ^ 2 = ((uy : D.O)) ^ 2 * ϖ ^ (2 * k) := by
      rw [hyk, mul_pow, ← pow_mul, mul_comm k 2]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · -- k ≤ 1: ϖ^{2k+1} divides A₀ (order 3) and A₁y (order ≥ 2+k), hence y² (order 2k)
      have hdA0 : ϖ ^ (2 * k + 1) ∣ algebraMap ℤ_[p] D.O (f.coeff 0) := by
        rw [hA0]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hdA1 : ϖ ^ (2 * k + 1) ∣ algebraMap ℤ_[p] D.O (f.coeff 1) * y := by
        rw [hA1y]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hkey : y ^ 2 = -(algebraMap ℤ_[p] D.O (f.coeff 0)
          + algebraMap ℤ_[p] D.O (f.coeff 1) * y) := by
        linear_combination hexp
      have hdy2 : ϖ ^ (2 * k + 1) ∣ ((uy : D.O)) ^ 2 * ϖ ^ (2 * k) := by
        rw [← hy2, hkey]
        exact dvd_neg.mpr (dvd_add hdA0 hdA1)
      exact not_pow_succ_dvd_unit_mul_pow hϖ (uy.isUnit.pow 2) (2 * k) hdy2
    · -- k ≥ 2: ϖ⁴ divides y² (order 2k ≥ 4) and A₁y (order ≥ 2+k ≥ 4), hence A₀ = c₀·ϖ³
      have hdy2 : ϖ ^ (3 + 1) ∣ y ^ 2 := by
        rw [hy2]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hdA1 : ϖ ^ (3 + 1) ∣ algebraMap ℤ_[p] D.O (f.coeff 1) * y := by
        rw [hA1y]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
      have hkey : algebraMap ℤ_[p] D.O (f.coeff 0)
          = -(algebraMap ℤ_[p] D.O (f.coeff 1) * y + y ^ 2) := by
        linear_combination hexp
      have hdA0 : ϖ ^ (3 + 1) ∣ c₀ * ϖ ^ 3 := by
        rw [← hA0, hkey]
        exact dvd_neg.mpr (dvd_add hdA1 hdy2)
      exact not_pow_succ_dvd_unit_mul_pow hϖ hc₀ 3 hdA0
  -- conclude: E ∣ 2 and E ≠ 1 force E = 2, then f = 1
  have hE2 : E = 2 := by
    have hdvd : E ∣ 2 := ⟨QpType.fOf p D, by rw [← he_val]; exact hef.symm⟩
    exact (Nat.prime_two.eq_one_or_self_of_dvd E hdvd).resolve_left hEne1
  have hff : 2 * QpType.fOf p D = 2 := by
    calc 2 * QpType.fOf p D = QpType.eOf p D * QpType.fOf p D := by rw [he_val, hE2]
      _ = 2 := hef
  exact ⟨he_val.trans hE2, by omega⟩

/-- **The H = 3 fiber forces `(e, f) = (2, 1)`.** For a genuine monic quadratic in the level-`N`
classifier fiber of the H = 3 window shape, EVERY local-factor bundle carries `efOf = (2, 1)` —
machine-checked, no axiom. The H = 3 mirror of `QpTypeEisenstein.gate_ef_forced` (route (a);
the fine-(e,f) swap `{(1,2)}` is machine-refutable at the H = 3 stratum — probe evidence
below). -/
theorem gate_h3_ef_forced {N : ℕ} (hN0 : 0 < N) (hN4 : 4 ≤ N) {f : ℤ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : B.classify p 2 N (PadicLift.toBox p 2 N hN0 f hf hdeg)
      = ClassifierBridgeFiber.Tselfloop 2 h3Side h3Shape)
    (D : QpType.LocalFactorData p f) :
    QpType.efOf p D = (2, 1) := by
  obtain ⟨h0, h1⟩ := wildH3Fiber_valuation p hN0 hN4 hf hdeg hfib
  have h := ef_of_wildH3 p hf hdeg h0 h1 D
  unfold QpType.efOf
  rw [h.1, h.2]

/-! ## Block 7 — mutation probe evidence (blueprint §2 item 4, both probes re-run at H = 3)

**Probe (i) — the SPLIT-TYPE mutation of the RE-SCOPED axiom is refuted at the H = 3 stratum
(machine-checked 2026-07-21, scratch NOT committed).** The scratch below — the re-scoped
axiom's hypotheses VERBATIM (including the new `(K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ)`),
conclusion mutated to the SPLIT type `{(1,1),(1,1)}` — compiled with zero errors against this
module: `False` derives from the mutated axiom + `h3Fiber_nonempty` + `h3_mem_omMenuW3` +
`wildH3Fiber_irreducible`. This is the W2 split-type probe re-run at the NEW menu content the
re-scope adds (the H = 3 window leg, `K = 3`), against a PURELY AXIOM-FREE anchor.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeH3

namespace LeanUrat.OM.QpTypeH3ScratchSplit

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of the RE-SCOPED `om_leaf_faithful` verbatim
(K-windowed menu), conclusion replaced by the SPLIT type `{(1,1),(1,1)}`. -/
axiom om_leaf_faithful_MUTATED_split_w3 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

/-- The mutated axiom is REFUTED at the H = 3 window stratum: the inhabited fiber
(`QpTypeH3.h3Fiber_nonempty`) would carry a 2-factor ℚ_2-factorization of a polynomial that is
PROVEN irreducible (`QpTypeH3.wildH3Fiber_irreducible`). -/
theorem mutation_split_w3_refuted : False := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := QpTypeH3.h3Fiber_nonempty
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_split_w3 2 2 5 (by norm_num)
    (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) _ 3 QpTypeH3.h3_mem_omMenuW3
    f0 hf hdeg hfib
  have hirr : Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2])) :=
    QpTypeH3.wildH3Fiber_irreducible 2 (by norm_num) (by norm_num) hf hdeg hfib
  -- the mutated conclusion forces EXACTLY TWO factors
  have hlen : F.factors.length = 2 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  obtain ⟨g₁, g₂, hfac⟩ := List.length_eq_two.mp hlen
  have h1 : ¬ IsUnit (g₁.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₁ (by rw [hfac]; exact List.mem_cons_self ..)).not_isUnit
  have h2 : ¬ IsUnit (g₂.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₂ (by rw [hfac]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).not_isUnit
  have hmap : f0.map (algebraMap ℤ_[2] ℚ_[2])
      = g₁.map (algebraMap ℤ_[2] ℚ_[2]) * g₂.map (algebraMap ℤ_[2] ℚ_[2]) := by
    rw [← F.prod_eq, hfac]
    simp [Polynomial.map_mul]
  rcases hirr.isUnit_or_isUnit hmap with h | h
  · exact h1 h
  · exact h2 h

end LeanUrat.OM.QpTypeH3ScratchSplit

#print axioms LeanUrat.OM.QpTypeH3ScratchSplit.mutation_split_w3_refuted
```

`lake env lean` output on the scratch (2026-07-21): NO errors; the single info line

```
'LeanUrat.OM.QpTypeH3ScratchSplit.mutation_split_w3_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeH3ScratchSplit.om_leaf_faithful_MUTATED_split_w3]
```

i.e. `False` follows from the MUTATED axiom + Lean core + PROVED theorems alone — the real
(re-scoped) `om_leaf_faithful` does NOT appear in the refutation's cone.

**Probe (ii) — the FINE-(e,f)-SWAP mutation of the RE-SCOPED axiom is refuted at the H = 3
stratum (machine-checked 2026-07-21, scratch NOT committed; enabled by route (a) landing).**
The scratch below — same re-scoped hypotheses, conclusion mutated to the SINGLETON swapped
type `{(1,2)}` (invisible to the factor-count probe) — compiled with zero errors: `False`
derives from the mutated axiom + `h3Fiber_nonempty` + `h3_mem_omMenuW3` + the AXIOM-FREE
`gate_h3_ef_forced` + `QpTypeEisenstein.qpType_singleton_forces`.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeEisenstein
import LeanUrat.OM.QpTypeH3

namespace LeanUrat.OM.QpTypeH3ScratchSwap

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of the RE-SCOPED `om_leaf_faithful` verbatim
(K-windowed menu), conclusion replaced by the fine-(e,f)-SWAPPED SINGLETON type `{(1,2)}`. -/
axiom om_leaf_faithful_MUTATED_efswap_w3 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (2 : ℕ))}⟩ : FactorizationType)

/-- The ef-swap mutation is REFUTED at the H = 3 window stratum: the inhabited fiber forces a
singleton factorization whose unique factor is `f0` itself with bundle payload `efOf = (1,2)`
(`QpTypeEisenstein.qpType_singleton_forces`), but the AXIOM-FREE parity theorem forces
`efOf = (2,1)` for EVERY bundle on the H = 3 fiber (`QpTypeH3.gate_h3_ef_forced`). -/
theorem mutation_efswap_w3_refuted : False := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := QpTypeH3.h3Fiber_nonempty
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_efswap_w3 2 2 5 (by norm_num)
    (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) _ 3 QpTypeH3.h3_mem_omMenuW3
    f0 hf hdeg hfib
  obtain ⟨hmem, hef⟩ := QpTypeEisenstein.qpType_singleton_forces 2 F ((1 : ℕ), (2 : ℕ)) hF
  have hef2 : QpType.efOf 2 (F.data f0 hmem) = (2, 1) :=
    QpTypeH3.gate_h3_ef_forced 2 (by norm_num) (by norm_num) hf hdeg hfib (F.data f0 hmem)
  rw [hef] at hef2
  exact absurd hef2 (by decide)

end LeanUrat.OM.QpTypeH3ScratchSwap

#print axioms LeanUrat.OM.QpTypeH3ScratchSwap.mutation_efswap_w3_refuted
```

`lake env lean` output on the scratch (2026-07-21): NO errors; the single info line

```
'LeanUrat.OM.QpTypeH3ScratchSwap.mutation_efswap_w3_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeH3ScratchSwap.om_leaf_faithful_MUTATED_efswap_w3]
```

Together the two probes pin the re-scoped axiom's payload at its NEW menu content (the H = 3
window leg) in BOTH coordinates — factor count AND `(e,f)` — against purely axiom-free
anchors, exactly as the W2 probes pinned the H = 1 gate. -/

/-! ## Block 8 — axiom census (this module declares NO axiom; everything must be core-only) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeH3.h3Path
#print axioms LeanUrat.OM.QpTypeH3.h3Side
#print axioms LeanUrat.OM.QpTypeH3.h3Shape
#print axioms LeanUrat.OM.QpTypeH3.sidePairs_h3Path
#print axioms LeanUrat.OM.QpTypeH3.menuPath_h3
#print axioms LeanUrat.OM.QpTypeH3.shapesFor_h3
#print axioms LeanUrat.OM.QpTypeH3.ramShapeAt_h3
#print axioms LeanUrat.OM.QpTypeH3.h3_mem_omMenuW3
#print axioms LeanUrat.OM.QpTypeH3.mem_maximalIdeal_pow_of_le_zmodValuation
#print axioms LeanUrat.OM.QpTypeH3.wildH3_irreducible'
#print axioms LeanUrat.OM.QpTypeH3.wildH3_irreducible
#print axioms LeanUrat.OM.QpTypeH3.wildH3Fiber_valuation
#print axioms LeanUrat.OM.QpTypeH3.wildH3Fiber_irreducible
#print axioms LeanUrat.OM.QpTypeH3.h3Poly
#print axioms LeanUrat.OM.QpTypeH3.h3Poly_monic
#print axioms LeanUrat.OM.QpTypeH3.h3Poly_natDegree
#print axioms LeanUrat.OM.QpTypeH3.toBox_h3Poly
#print axioms LeanUrat.OM.QpTypeH3.h3box_inCell
#print axioms LeanUrat.OM.QpTypeH3.h3Fiber_nonempty
#print axioms LeanUrat.OM.QpTypeH3.not_pow_succ_dvd_unit_mul_pow
#print axioms LeanUrat.OM.QpTypeH3.ef_of_wildH3
#print axioms LeanUrat.OM.QpTypeH3.gate_h3_ef_forced

end AxCheck

end LeanUrat.OM.QpTypeH3
