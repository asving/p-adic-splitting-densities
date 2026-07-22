/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpTypeLeafMasters
import LeanUrat.OM.QpTypeChainAll
import LeanUrat.OM.ChainMenuU

/-!
# QpTypeSplitU — the axiom-free splitU faithfulness masters, all depths, all translates,
general `p` (Wild Wave 6q task D, `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md` §1.5, §3)

The W6q splitU family (`OM/ChainMenuU.lean`: even-height rescale frame with separable
residual having two DISTINCT roots) is split-keyed (`{(1,1),(1,1)}`), so by the blueprint §3
REQUIREMENT its faithfulness must be PROVED outright — axiom-free — and every split-keyed
consumer must fire these masters, never the axiom. This module supplies the full ladder:

* `hensel_lift_at_simple_root` / `splitRes_two_roots` — **the root-generic two-simple-roots
  Hensel engine**. The banked `QpTypeChainLeaves.split_two_roots` is HARD-CODED to the
  residual root pair `{0, −w̄₁}` (hypotheses `w₀ ∈ (p)`, `w̄₁ ≠ 0`), so it is generalized
  here (FLAGGED, not reused): for ANY residual pair in the order-0 split pool
  `ChainMenuU.splitResPairs p` (two distinct roots `r̄ ≠ s̄`, zero allowed), lift each root by
  mathlib `hensels_lemma` at its canonical `ℕ`-cast lift — the derivative read
  `h̄'(r̄) = 2r̄ + w̄₁ = r̄ − s̄ ≠ 0` (Vieta `w̄₁ = −(r̄ + s̄)`) is char-2-safe, exactly the
  blueprint §1.5 remark — then Vieta pins `h = (z − r₁)(z − r₂)` with `r₁ ≠ r₂`.
* `splitSep_master_hasType` — **the (SU) master core** at the order-0 split pool, all
  `m ≥ 0`: `g = y² + b₁y + b₀` with `b₀ = p^{2m}·w₀`, `b₁ = p^m·w₁`,
  `(w̄₀, w̄₁) ∈ splitResPairs p` has a genuine certificate of type `{(1,1),(1,1)}` — the
  general-`m` rescale `g(p^m·z) = p^{2m}·h(z)` (`leafInert_rescale`), the Hensel
  factorization of `h`, the proved degree-1 bundles (`pairFactorization`), and the proved
  transport (`translateFactorization` at `a = p^m`, `c = 0`).
* `leafSplitU_master_hasType` — the splitU-pool instance (blueprint §1.5 splitU master:
  `rootedPairs ⊆ splitResPairs`, drop the both-nonzero condition the proof never needs);
  `ord0Split_master_hasType` — the `m = 0` boundary instance (the general-`p` order-0
  split-cell master, roots NOT restricted to `{0, 1}` — generalizing the `p = 2` (S0) read).
* `leafFiberU_split_hasType` / `ord0SplitCell_hasType` — the box-decode wrappers: `LeafPairU`
  fibers (frame `leafNeedU ≤ L₀ ≤ L₁`) resp. `Ord0SplitCell` fibers (`1 ≤ N`) of a genuine
  monic quadratic decode (`dvd_of_box_dvd` + the digit bridge `box_digit_toZMod`) to the
  master hypotheses.
* `stepDecodeU_general` / `chainUnwindU` — the splitU chain unwind. `QpTypeChainAll`'s
  `chainUnwind` and `QpTypeLeafMasters.stepDecode_general` are stated for
  `ChainMenu.ChainPair` at a `ChainMenu.ChainLeaf` — the fiber predicate is baked into the
  hypothesis type, so neither is instantiable at `ChainMenuU.ChainPairU`; both inductions
  are TRANSCRIBED here (FLAGGED) with the leaf clause swapped, consuming the same banked
  engine pieces (`dvd_of_box_dvd`, `box_shift_cast`, `monic_quadratic_eq`,
  `comp_affine_comp`) — only the wrapper inductions are re-run.
* `chainFiberU_split_hasType` — all-depth splitU fiber ⟹ genuine certificate (unwind + the
  master at the final frame + certificate transport UP the composed relation).
* `transBoxP_comp` / `transChainFiberU_split_hasType` — the GENERAL-`p` translate reduction:
  the box pair of the genuine translate `f(x + ĉ)` IS `RecenterBox.affineEquiv p N N _ ĉ` of
  the box pair of `f` (the `QpTypeChainAll.transBox_comp` commutation, re-proved against
  `affineEquiv` directly since the banked version is pinned to `M9.realP` through
  `SeriesAssembly.transMap`), then the Section-above conclusion on `f(x + ĉ)` transported
  back at `a = 1` (`translate_rel`). No translation form enters any axiom ((P4d) discipline).
* **The `p = 3` witness** (`w6qSplitUPoly = y² + 9y + 18 = (y + 3)(y + 6)`, residual pair
  `(2, 0) ∈ rootedPairs 3` at height `2`): its `LeafPairU` fiber membership at `N = 3`
  (digit checks by `decide`), the axiom-free master's verdict at the witness
  (`gate_w6q_splitU_hasType_axfree` — the blueprint §3 guard, CORE-ONLY footprint), and the
  irreducibility REFUTER `w6qSplitU_not_irreducible` (the direct two-factor certificate;
  the wrong-keying mutation probes of `OM/OmLeafFaithful.lean` Block 5c fire against it).

Leaf module discipline: **no axiom, no `sorry`** — every declaration core-only (AxCheck at
bottom); any `om_leaf_faithful` appearance in a footprint is a FAILURE (blueprint §3: a
census line showing the axiom inside a split-keyed payload is a stop-the-line defect).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.QpTypeSplitU

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu LeanUrat.OM.CellCard
open LeanUrat.OM.QpTypeChain LeanUrat.OM.QpTypeChainLeaves LeanUrat.OM.QpTypeLeafMasters
open LeanUrat.OM.QpTypeChainAll

/-! ## Block 1 — residue/norm toolkit -/

section Toolkit

variable (p : ℕ) [hp : Fact p.Prime]

/-- A nonzero mod-`p` residue pins the norm to `1`. -/
theorem norm_eq_one_of_toZMod_ne {u : ℤ_[p]} (hu : PadicInt.toZMod u ≠ 0) : ‖u‖ = 1 :=
  PadicInt.isUnit_iff.mp (isUnit_of_toZMod_ne p hu)

/-- A vanishing mod-`p` residue pins the norm below `1`. -/
theorem norm_lt_one_of_toZMod_eq_zero {u : ℤ_[p]} (hu : PadicInt.toZMod u = 0) : ‖u‖ < 1 :=
  (PadicInt.norm_lt_one_iff_dvd u).mpr ((toZMod_eq_zero_iff p u).mp hu)

/-- Two elements at distance `< 1` share their mod-`p` residue. -/
theorem toZMod_eq_of_norm_sub_lt_one {x a : ℤ_[p]} (h : ‖x - a‖ < 1) :
    PadicInt.toZMod x = PadicInt.toZMod a := by
  have hd : PadicInt.toZMod (x - a) = 0 :=
    (toZMod_eq_zero_iff p _).mpr ((PadicInt.norm_lt_one_iff_dvd _).mp h)
  rw [map_sub] at hd
  exact sub_eq_zero.mp hd

/-- The canonical `ℕ`-cast lift of a residue reduces back to it. -/
theorem toZMod_natCast_val (ρ : ZMod p) : PadicInt.toZMod ((ρ.val : ℕ) : ℤ_[p]) = ρ := by
  rw [map_natCast]
  exact ZMod.natCast_rightInverse ρ

end Toolkit

/-! ## Block 2 — the root-generic two-simple-roots Hensel engine

**FLAG (generalization, not reuse):** the banked `QpTypeChainLeaves.split_two_roots` is
hard-coded to the residual roots `{0, −w̄₁}` (hypotheses `w₀ ∈ (p)`, `w̄₁ ≠ 0`); the engine
below re-runs its proof shape at an ARBITRARY simple residual root (Hensel at the `ℕ`-cast
lift) and derives the distinct-root factorization from the order-0 split pool membership. -/

section Hensel

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Hensel at one simple residual root**: if `ρ` is a root of the residual quadratic
`z² + w̄₁z + w̄₀` with nonvanishing derivative read `2ρ + w̄₁ ≠ 0`, then `z² + w₁z + w₀` has a
genuine root `r ∈ ℤ_[p]` with residue `ρ` (mathlib `hensels_lemma` at the lift
`a = (ρ.val : ℤ_[p])`: `‖h(a)‖ < 1 = ‖h'(a)‖²`, and `‖r − a‖ < 1` pins the residue). -/
theorem hensel_lift_at_simple_root {w₀ w₁ : ℤ_[p]} {ρ : ZMod p}
    (hroot : ρ ^ 2 + PadicInt.toZMod w₁ * ρ + PadicInt.toZMod w₀ = 0)
    (hder : 2 * ρ + PadicInt.toZMod w₁ ≠ 0) :
    ∃ r : ℤ_[p], r ^ 2 + w₁ * r + w₀ = 0 ∧ PadicInt.toZMod r = ρ := by
  set F : ℤ_[p][X] := X ^ 2 + C w₁ * X + C w₀ with hF
  set a : ℤ_[p] := ((ρ.val : ℕ) : ℤ_[p]) with ha
  have haρ : PadicInt.toZMod a = ρ := toZMod_natCast_val p ρ
  have hFd : Polynomial.derivative F = C 2 * X + C w₁ := by
    rw [hF]
    rw [Polynomial.derivative_add, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.derivative_X_pow]
    norm_num
  have hFa : Polynomial.aeval a F = a ^ 2 + w₁ * a + w₀ := by
    rw [hF]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply]
  have hFda : Polynomial.aeval a (Polynomial.derivative F) = 2 * a + w₁ := by
    rw [hFd]
    simp only [map_add, map_mul, map_ofNat, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply]
  have hnum : ‖a ^ 2 + w₁ * a + w₀‖ < 1 := by
    refine norm_lt_one_of_toZMod_eq_zero p ?_
    rw [map_add, map_add, map_mul, map_pow, haρ]
    exact hroot
  have hden : ‖2 * a + w₁‖ = 1 := by
    refine norm_eq_one_of_toZMod_ne p ?_
    rw [map_add, map_mul, map_ofNat, haρ]
    exact hder
  obtain ⟨r, hroot', hclose, -, -⟩ := hensels_lemma (F := F) (a := a)
    (by rw [hFa, hFda, hden, one_pow]; exact hnum)
  have he : r ^ 2 + w₁ * r + w₀ = 0 := by
    have h := hroot'
    rw [hF] at h
    simpa [map_add, map_mul, map_pow] using h
  have hres : PadicInt.toZMod r = ρ := by
    have hc := hclose
    rw [hFda, hden] at hc
    exact (toZMod_eq_of_norm_sub_lt_one p hc).trans haρ
  exact ⟨r, he, hres⟩

/-- **The root-generic two-roots Hensel factorization** (the `split_two_roots`
generalization): a residual pair in the order-0 split pool (two DISTINCT roots `ρ ≠ τ`,
zero allowed) lifts to `z² + w₁z + w₀ = (z − r₁)(z − r₂)` with `r₁ ≠ r₂` in `ℤ_[p]` — the
derivative reads `2ρ + w̄₁ = ρ − τ ≠ 0` and `2τ + w̄₁ = τ − ρ ≠ 0` (Vieta), valid at `p = 2`
as well; only DISTINCTNESS of the roots enters, never nonvanishing. -/
theorem splitRes_two_roots {w₀ w₁ : ℤ_[p]}
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenuU.splitResPairs p) :
    ∃ r₁ r₂ : ℤ_[p], r₁ ≠ r₂ ∧
      (X - C r₁) * (X - C r₂) = (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) := by
  obtain ⟨ρ, τ, hρτ, hρ, hτ⟩ := (ChainMenuU.mem_splitResPairs p).mp hmem
  have hρ' : ρ ^ 2 + PadicInt.toZMod w₁ * ρ + PadicInt.toZMod w₀ = 0 := hρ
  have hτ' : τ ^ 2 + PadicInt.toZMod w₁ * τ + PadicInt.toZMod w₀ = 0 := hτ
  have hvieta := ChainMenuU.root_pair_vieta p hρτ hρ' hτ'
  have hderρ : 2 * ρ + PadicInt.toZMod w₁ ≠ 0 := by
    rw [hvieta.2]
    intro h0
    exact hρτ (by linear_combination h0)
  have hderτ : 2 * τ + PadicInt.toZMod w₁ ≠ 0 := by
    rw [hvieta.2]
    intro h0
    exact hρτ (by linear_combination -h0)
  obtain ⟨r₁, he₁, hres₁⟩ := hensel_lift_at_simple_root p hρ' hderρ
  obtain ⟨r₂, he₂, hres₂⟩ := hensel_lift_at_simple_root p hτ' hderτ
  have hne : r₁ ≠ r₂ := by
    intro h
    exact hρτ (by rw [← hres₁, h, hres₂])
  have hsum : w₁ = -(r₁ + r₂) := by
    have hfac : (r₁ - r₂) * (r₁ + r₂ + w₁) = 0 := by
      linear_combination he₁ - he₂
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact absurd (sub_eq_zero.mp hc) hne
    · linear_combination hc
  have hprod : w₀ = r₁ * r₂ := by
    linear_combination he₁ - r₁ * hsum
  refine ⟨r₁, r₂, hne, ?_⟩
  rw [hsum, hprod]
  simp only [map_neg, map_add, map_mul]
  ring

end Hensel

/-! ## Block 3 — the (SU) masters (blueprint §1.5): all `m ≥ 0`, both pools -/

section Masters

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The (SU) master core, order-0 split pool, all `m ≥ 0`** — the axiom-free splitU
faithfulness certificate. `g = y² + b₁y + b₀` with `b₀ = p^{2m}·w₀`, `b₁ = p^m·w₁` and
residual pair `(w̄₀, w̄₁) ∈ splitResPairs p` (two DISTINCT roots, zero allowed) HAS a genuine
ℚ_p-factorization certificate of type `{(1,1),(1,1)}`: the rescaled `h = z² + w₁z + w₀`
(`leafInert_rescale` at `a = p^m`, `c = 0`) Hensel-factors at the two distinct simple
residual roots (`splitRes_two_roots`), each linear factor carries the proved degree-1
bundle (`pairFactorization`), and the PROVED transport `translateFactorization` carries the
certificate to `g` with the same `qpType` (`ChainMenu.splitType2`). At `m = 0` the rescale
is trivial — the order-0 boundary instance `ord0Split_master_hasType` below. -/
theorem splitSep_master_hasType (m : ℕ) {b₀ b₁ w₀ w₁ : ℤ_[p]}
    (hb₀ : b₀ = (p : ℤ_[p]) ^ (2 * m) * w₀) (hb₁ : b₁ = (p : ℤ_[p]) ^ m * w₁)
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenuU.splitResPairs p) :
    ∃ F : QpType.QpFactorization p (X ^ 2 + C b₁ * X + C b₀),
      QpType.qpType p F = ChainMenu.splitType2 := by
  obtain ⟨r₁, r₂, hne, hfac⟩ := splitRes_two_roots p hmem
  have hrel := leafInert_rescale p m hb₀ hb₁
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  have hpne : ((p : ℤ_[p]) ^ m) ≠ 0 := pow_ne_zero _ hpz
  have hhdeg : (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hrel' : (X ^ 2 + C b₁ * X + C b₀ : ℤ_[p][X]).comp (C ((p : ℤ_[p]) ^ m) * X + C 0)
      = C (((p : ℤ_[p]) ^ m) ^ (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]).natDegree)
        * (X ^ 2 + C w₁ * X + C w₀ : ℤ_[p][X]) := by
    rw [hhdeg]
    exact hrel
  refine ⟨translateFactorization p ((p : ℤ_[p]) ^ m) 0 hpne hrel'
    (pairFactorization p r₁ r₂ hfac), ?_⟩
  rw [qpType_translateFactorization p ((p : ℤ_[p]) ^ m) 0 hpne hrel'
    (pairFactorization p r₁ r₂ hfac)]
  exact qpType_pairFactorization p r₁ r₂ hfac

/-- **The splitU master** (blueprint §1.5, the splitU-pool instance): residual pair in the
splitU pool `rootedPairs p` (two distinct NONZERO roots) — the both-nonzero condition is
dropped through `rootedPairs_subset_splitResPairs` (the proof needs only DISTINCTNESS,
exactly the blueprint remark "both ≠ 0 irrelevant to the proof"). -/
theorem leafSplitU_master_hasType (m : ℕ) {b₀ b₁ w₀ w₁ : ℤ_[p]}
    (hb₀ : b₀ = (p : ℤ_[p]) ^ (2 * m) * w₀) (hb₁ : b₁ = (p : ℤ_[p]) ^ m * w₁)
    (hmem : (PadicInt.toZMod w₀, PadicInt.toZMod w₁) ∈ ChainMenuU.rootedPairs p) :
    ∃ F : QpType.QpFactorization p (X ^ 2 + C b₁ * X + C b₀),
      QpType.qpType p F = ChainMenu.splitType2 :=
  splitSep_master_hasType p m hb₀ hb₁ (ChainMenuU.rootedPairs_subset_splitResPairs p hmem)

/-- **The general-`p` order-0 split-cell master** — the `m = 0` boundary instance of the
(SU) core: a monic quadratic whose residual pair has two distinct roots (any, `0` allowed —
the `Ord0SplitCell` pool shape, generalizing the `p = 2` root pair `{0, 1}` of the W6c (S0)
read) has a genuine certificate of type `{(1,1),(1,1)}`. -/
theorem ord0Split_master_hasType {b₀ b₁ : ℤ_[p]}
    (hmem : (PadicInt.toZMod b₀, PadicInt.toZMod b₁) ∈ ChainMenuU.splitResPairs p) :
    ∃ F : QpType.QpFactorization p (X ^ 2 + C b₁ * X + C b₀),
      QpType.qpType p F = ChainMenu.splitType2 :=
  splitSep_master_hasType p 0 (by rw [mul_zero, pow_zero, one_mul])
    (by rw [pow_zero, one_mul]) hmem

end Masters

/-! ## Block 4 — the box-decode wrappers (`LeafPairU` / `Ord0SplitCell` fibers → masters) -/

section Wrappers

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The splitU-leaf fiber wrapper — axiom-free existence**: a genuine monic quadratic whose
box pair at frame `(L₀, L₁)` (`leafNeedU m = 2m + 1 ≤ L₀ ≤ L₁`) lies in the `LeafPairU m`
digit fiber HAS a genuine ℚ_p-factorization certificate of type `{(1,1),(1,1)}` — decode by
`dvd_of_box_dvd` at heights `2m ≤ L₀`, `m ≤ L₁` and the digit→residue bridge
`box_digit_toZMod` for the `rootedPairs` membership, then the splitU master. This is the
`om_leaf_faithful` conclusion ITSELF at the splitU leaf, no axiom. -/
theorem leafFiberU_split_hasType {m L₀ L₁ : ℕ}
    (hL₀ : ChainMenuU.leafNeedU m ≤ L₀) (hL01 : L₀ ≤ L₁)
    {g : ℤ_[p][X]} (hg : g.Monic) (hdeg : g.natDegree = 2)
    (hfib : ChainMenuU.LeafPairU p m L₀ L₁
      (PadicInt.toZModPow L₀ (g.coeff 0), PadicInt.toZModPow L₁ (g.coeff 1))) :
    ∃ F : QpType.QpFactorization p g, QpType.qpType p F = ChainMenu.splitType2 := by
  have hneed : 2 * m + 1 ≤ L₀ := hL₀
  obtain ⟨hd0, hd1, hmem⟩ := hfib
  obtain ⟨w₀, hw₀⟩ := dvd_of_box_dvd p (show 2 * m ≤ L₀ by omega) hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p (show m ≤ L₁ by omega) hd1
  have hdig0 : digit p L₀ (2 * m) (PadicInt.toZModPow L₀ (g.coeff 0))
      = PadicInt.toZMod w₀ := by
    rw [hw₀]
    exact box_digit_toZMod p (show 2 * m + 1 ≤ L₀ by omega) w₀
  have hdig1 : digit p L₁ m (PadicInt.toZModPow L₁ (g.coeff 1)) = PadicInt.toZMod w₁ := by
    rw [hw₁]
    exact box_digit_toZMod p (show m + 1 ≤ L₁ by omega) w₁
  rw [hdig0, hdig1] at hmem
  have hgeq : g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := monic_quadratic_eq p hg hdeg
  rw [hgeq]
  exact leafSplitU_master_hasType p m hw₀ hw₁ hmem

/-- **The order-0 split-cell wrapper — axiom-free existence** (general `p`): a genuine monic
quadratic whose box pair at level `N ≥ 1` lies in the `Ord0SplitCell` residual-shape fiber
has a genuine certificate of type `{(1,1),(1,1)}` — the height-0 digits ARE the mod-`p`
residues (`box_digit_toZMod` at `k = 0`), then the `m = 0` master. -/
theorem ord0SplitCell_hasType {N : ℕ} (hN : 1 ≤ N)
    {g : ℤ_[p][X]} (hg : g.Monic) (hdeg : g.natDegree = 2)
    (hfib : ChainMenuU.Ord0SplitCell p N
      (PadicInt.toZModPow N (g.coeff 0), PadicInt.toZModPow N (g.coeff 1))) :
    ∃ F : QpType.QpFactorization p g, QpType.qpType p F = ChainMenu.splitType2 := by
  have hdig : ∀ x : ℤ_[p], digit p N 0 (PadicInt.toZModPow N x) = PadicInt.toZMod x := by
    intro x
    have h := box_digit_toZMod p (show 0 + 1 ≤ N by omega) x
    rwa [pow_zero, one_mul] at h
  have h : (digit p N 0 (PadicInt.toZModPow N (g.coeff 0)),
      digit p N 0 (PadicInt.toZModPow N (g.coeff 1))) ∈ ChainMenuU.splitResPairs p := hfib
  rw [hdig (g.coeff 0), hdig (g.coeff 1)] at h
  have hgeq : g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := monic_quadratic_eq p hg hdeg
  rw [hgeq]
  exact ord0Split_master_hasType p h

end Wrappers

/-! ## Block 5 — the splitU chain unwind

**FLAG (transcription, not reuse):** `QpTypeLeafMasters.stepDecode_general` and
`QpTypeChainAll.chainUnwind` are stated for `ChainMenu.ChainPair _ (leaf : ChainLeaf)` —
the fiber predicate is baked into the hypothesis type, so they cannot be instantiated at
`ChainMenuU.ChainPairU` (the blueprint §1.6 design note: the `ChainLeaf` inductive was
deliberately NOT extended). Both inductions are transcribed below with the leaf clause
swapped; every leaf-independent engine piece (`dvd_of_box_dvd`, `box_shift_cast`,
`monic_quadratic_eq`, `comp_affine_comp`) is CONSUMED from the bank, not copied. -/

section UnwindU

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The tail-generic splitU step decode at head slope `mstep`** (the `stepDecode_general`
transcription at `ChainPairU`): a genuine monic quadratic whose box pair at staircase frame
`(L₀, L₁)` (`2·mstep ≤ L₀`, `mstep ≤ L₁`, `L₀ ≤ L₁`) satisfies
`ChainPairU (mstep :: ms') m` yields the genuine recentered monic quadratic `g` with
`f(p^mstep·y + ĉp^mstep) = p^{2·mstep}·g(y)` whose box pair at the child frame satisfies
`ChainPairU ms' m` — the tail rides through the `descendPair` box match definitionally. -/
theorem stepDecodeU_general {m mstep L₀ L₁ : ℕ} (_hm : 1 ≤ mstep) (h2m : 2 * mstep ≤ L₀)
    (hm1 : mstep ≤ L₁) (hL01 : L₀ ≤ L₁) (ms' : List ℕ)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenuU.ChainPairU p (mstep :: ms') m L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    ∃ (ĉ : ℕ) (g : ℤ_[p][X]) (_ : g.Monic), g.natDegree = 2 ∧
      f.comp (C ((p : ℤ_[p]) ^ mstep) * X + C ((ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ mstep))
        = C ((p : ℤ_[p]) ^ (2 * mstep)) * g ∧
      ChainMenuU.ChainPairU p ms' m (L₀ - 2 * mstep) (L₁ - mstep)
        (PadicInt.toZModPow (L₀ - 2 * mstep) (g.coeff 0),
          PadicInt.toZModPow (L₁ - mstep) (g.coeff 1)) := by
  simp only [ChainMenuU.ChainPairU] at hfib
  obtain ⟨c, hstep, htail⟩ := hfib
  simp only [RecenterBox.StratumPair, RecenterBox.CoordCond] at hstep
  obtain ⟨⟨hd0, -⟩, ⟨hd1, -⟩⟩ := hstep
  obtain ⟨w₀, hw₀⟩ := dvd_of_box_dvd p h2m hd0
  obtain ⟨w₁, hw₁⟩ := dvd_of_box_dvd p hm1 hd1
  set ĉ : ℕ := ((c : ZMod p)).val with hĉ
  set b₁ : ℤ_[p] := w₁ + 2 * (ĉ : ℤ_[p]) with hb₁
  set b₀ : ℤ_[p] := w₀ + (ĉ : ℤ_[p]) * w₁ + (ĉ : ℤ_[p]) ^ 2 with hb₀
  set g : ℤ_[p][X] := X ^ 2 + C b₁ * X + C b₀ with hgdef
  have hg : g.Monic := by
    rw [hgdef]
    monicity!
  have hgdeg : g.natDegree = 2 := by
    rw [hgdef]
    compute_degree!
  have hg0 : g.coeff 0 = b₀ := by
    rw [hgdef]
    simp
  have hg1 : g.coeff 1 = b₁ := by
    rw [hgdef]
    simp
  have hrel : f.comp (C ((p : ℤ_[p]) ^ mstep) * X + C ((ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ mstep))
      = C ((p : ℤ_[p]) ^ (2 * mstep)) * g := by
    conv_lhs => rw [monic_quadratic_eq p hf hdeg]
    rw [hw₀, hw₁, hgdef, hb₀, hb₁]
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_add, map_mul, map_pow, map_ofNat]
    ring
  have hdesc : ChainMenu.descendPair p mstep ĉ
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))
      = (PadicInt.toZModPow (L₀ - 2 * mstep) b₀, PadicInt.toZModPow (L₁ - mstep) b₁) := by
    unfold ChainMenu.descendPair
    refine Prod.ext ?_ ?_
    · show ((((PadicInt.toZModPow L₀ (f.coeff 0)).val / p ^ (2 * mstep) : ℕ))
          : ZMod (p ^ (L₀ - 2 * mstep)))
        + (ĉ : ZMod (p ^ (L₀ - 2 * mstep)))
            * (((PadicInt.toZModPow L₁ (f.coeff 1)).val / p ^ mstep : ℕ)
                : ZMod (p ^ (L₀ - 2 * mstep)))
        + (ĉ : ZMod (p ^ (L₀ - 2 * mstep))) ^ 2 = PadicInt.toZModPow (L₀ - 2 * mstep) b₀
      rw [hw₀, hw₁, box_shift_cast p h2m (le_refl _),
        box_shift_cast p hm1 (show L₀ - 2 * mstep ≤ L₁ - mstep by omega),
        hb₀, map_add, map_add, map_mul, map_pow, map_natCast]
    · show (((PadicInt.toZModPow L₁ (f.coeff 1)).val / p ^ mstep : ℕ)
          : ZMod (p ^ (L₁ - mstep)))
        + 2 * (ĉ : ZMod (p ^ (L₁ - mstep))) = PadicInt.toZModPow (L₁ - mstep) b₁
      rw [hw₁, box_shift_cast p hm1 (le_refl _),
        hb₁, map_add, map_mul, map_natCast, map_ofNat]
  rw [hdesc] at htail
  rw [← hg0, ← hg1] at htail
  exact ⟨ĉ, g, hg, hgdeg, hrel, htail⟩

/-- **The splitU chain unwind** (the `chainUnwind` transcription at `ChainPairU`): by
induction on the slope list (entries `≥ 1`, additive budget `2·Σms + leafNeedU m ≤ L₀`,
staircase invariant `L₀ ≤ L₁`), a genuine monic quadratic whose box pair satisfies
`ChainPairU ms m` decodes to a genuine monic quadratic `g` at the final frame in the
`LeafPairU m` fiber, connected to `f` by the SINGLE composed affine relation
`f.comp (C p^Σms·X + C c) = C p^{2Σms}·g` (steps composed by `comp_affine_comp`). -/
theorem chainUnwindU (m : ℕ) (ms : List ℕ) (hms : ∀ x ∈ ms, 1 ≤ x)
    {L₀ L₁ : ℕ} (hbud : 2 * ms.sum + ChainMenuU.leafNeedU m ≤ L₀) (hL01 : L₀ ≤ L₁)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenuU.ChainPairU p ms m L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    ∃ (c : ℤ_[p]) (g : ℤ_[p][X]) (_ : g.Monic), g.natDegree = 2 ∧
      f.comp (C ((p : ℤ_[p]) ^ ms.sum) * X + C c)
        = C ((p : ℤ_[p]) ^ (2 * ms.sum)) * g ∧
      ChainMenuU.LeafPairU p m (L₀ - 2 * ms.sum) (L₁ - ms.sum)
        (PadicInt.toZModPow (L₀ - 2 * ms.sum) (g.coeff 0),
          PadicInt.toZModPow (L₁ - ms.sum) (g.coeff 1)) := by
  induction ms generalizing L₀ L₁ f with
  | nil =>
      refine ⟨0, f, hf, hdeg, ?_, ?_⟩
      · simp only [List.sum_nil, mul_zero, pow_zero, Polynomial.C_1, Polynomial.C_0,
          one_mul, add_zero, Polynomial.comp_X]
      · exact hfib
  | cons mstep ms' ih =>
      rw [List.sum_cons] at hbud
      have hm : 1 ≤ mstep := hms mstep List.mem_cons_self
      have hneed : 1 ≤ ChainMenuU.leafNeedU m := ChainMenuU.one_le_leafNeedU m
      obtain ⟨ĉ, g, hg, hgdeg, hrel₁, htail⟩ :=
        stepDecodeU_general p hm (by omega) (by omega) hL01 ms' hf hdeg hfib
      have hms' : ∀ x ∈ ms', 1 ≤ x := fun x hx => hms x (List.mem_cons_of_mem mstep hx)
      obtain ⟨c', gl, hgl, hgldeg, hrel₂, hleaf⟩ :=
        ih hms' (L₀ := L₀ - 2 * mstep) (L₁ := L₁ - mstep) (by omega) (by omega) hg hgdeg htail
      rw [List.sum_cons,
        show L₀ - 2 * (mstep + ms'.sum) = L₀ - 2 * mstep - 2 * ms'.sum from by omega,
        show L₁ - (mstep + ms'.sum) = L₁ - mstep - ms'.sum from by omega]
      refine ⟨(p : ℤ_[p]) ^ mstep * c' + (ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ mstep, gl, hgl, hgldeg,
        ?_, hleaf⟩
      calc f.comp (C ((p : ℤ_[p]) ^ (mstep + ms'.sum)) * X
              + C ((p : ℤ_[p]) ^ mstep * c' + (ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ mstep))
          = (f.comp (C ((p : ℤ_[p]) ^ mstep) * X
              + C ((ĉ : ℤ_[p]) * (p : ℤ_[p]) ^ mstep))).comp
              (C ((p : ℤ_[p]) ^ ms'.sum) * X + C c') := by
            rw [comp_affine_comp, pow_add]
        _ = (C ((p : ℤ_[p]) ^ (2 * mstep)) * g).comp
              (C ((p : ℤ_[p]) ^ ms'.sum) * X + C c') := by
            rw [hrel₁]
        _ = C ((p : ℤ_[p]) ^ (2 * mstep))
              * (g.comp (C ((p : ℤ_[p]) ^ ms'.sum) * X + C c')) := by
            rw [Polynomial.mul_comp, Polynomial.C_comp]
        _ = C ((p : ℤ_[p]) ^ (2 * mstep)) * (C ((p : ℤ_[p]) ^ (2 * ms'.sum)) * gl) := by
            rw [hrel₂]
        _ = C ((p : ℤ_[p]) ^ (2 * (mstep + ms'.sum))) * gl := by
            rw [← mul_assoc, ← Polynomial.C_mul, ← pow_add,
              show 2 * mstep + 2 * ms'.sum = 2 * (mstep + ms'.sum) from by omega]

/-- **All-depth splitU fiber ⟹ genuine certificate, AXIOM-FREE**: unwind, fire the splitU
leaf wrapper at the final frame, transport the certificate UP through the single composed
relation (`qpType_translate_rescale`). -/
theorem chainFiberU_split_hasType {ms : List ℕ} (hms : ∀ x ∈ ms, 1 ≤ x) {m L₀ L₁ : ℕ}
    (hbud : 2 * ms.sum + ChainMenuU.leafNeedU m ≤ L₀) (hL01 : L₀ ≤ L₁)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenuU.ChainPairU p ms m L₀ L₁
      (PadicInt.toZModPow L₀ (f.coeff 0), PadicInt.toZModPow L₁ (f.coeff 1))) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = ChainMenu.splitType2 := by
  obtain ⟨c, g, hg, hgdeg, hrel, hleaf⟩ := chainUnwindU p m ms hms hbud hL01 hf hdeg hfib
  have hneed : ChainMenuU.leafNeedU m ≤ L₀ - 2 * ms.sum := by
    have := ChainMenuU.one_le_leafNeedU m
    omega
  have hL01' : L₀ - 2 * ms.sum ≤ L₁ - ms.sum := by omega
  obtain ⟨Fg, hFg⟩ := leafFiberU_split_hasType p hneed hL01' hg hgdeg hleaf
  have hpz : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (PadicInt.prime_p (p := p)).ne_zero
  have hrel' : f.comp (C ((p : ℤ_[p]) ^ ms.sum) * X + C c)
      = C (((p : ℤ_[p]) ^ ms.sum) ^ g.natDegree) * g := by
    rw [hgdeg, ← pow_mul, Nat.mul_comm ms.sum 2]
    exact hrel
  obtain ⟨F, hF⟩ := qpType_translate_rescale p ((p : ℤ_[p]) ^ ms.sum) c
    (pow_ne_zero _ hpz) hrel' Fg
  exact ⟨F, hF.trans hFg⟩

end UnwindU

/-! ## Block 6 — the GENERAL-`p` translate reduction

`QpTypeChainAll` §2's `transBox_comp` is pinned to `p = M9.realP` through
`SeriesAssembly.transMap`; the commutation is re-derived here at general `p` directly
against `RecenterBox.affineEquiv` (whose definition is already general-`p`), mirroring the
realP proof. The transport back is the banked `translate_rel` at `a = 1` ((P4d): the
translate is DERIVED, no translation form enters any axiom). -/

section TranslateP

variable (p : ℕ) [hp : Fact p.Prime]

/-- Equal-level `castHom` is the identity (general-`p` form of
`SeriesAssembly.castHom_pow_self_apply`; the divisibility proof slot is arbitrary). -/
theorem castHom_pow_self_eq {N : ℕ} (h : p ^ N ∣ p ^ N) (x : ZMod (p ^ N)) :
    ZMod.castHom h (ZMod (p ^ N)) x = x :=
  RingHom.congr_fun (ZMod.castHom_self) x

/-- **The general-`p` translate commutation** (the `transBox_comp` analogue at any prime):
the box pair of the genuine translate `f(x + ĉ)` IS `RecenterBox.affineEquiv p N N _ ĉ` of
the box pair of `f` — coefficient-wise through the ring hom `toZModPow N`
(`comp_translate_coeff_zero`/`_one`). -/
theorem transBoxP_comp {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2) (ĉ N : ℕ) :
    (PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[p]))).coeff 0),
      PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[p]))).coeff 1))
      = RecenterBox.affineEquiv p N N le_rfl ĉ
          (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1)) := by
  refine Prod.ext ?_ ?_
  · show PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[p]))).coeff 0)
        = PadicInt.toZModPow N (f.coeff 0)
          + (ĉ : ZMod (p ^ N)) * (ZMod.castHom (pow_dvd_pow p le_rfl) (ZMod (p ^ N))
              (PadicInt.toZModPow N (f.coeff 1)))
          + (ĉ : ZMod (p ^ N)) ^ 2
    rw [comp_translate_coeff_zero p hf hdeg, castHom_pow_self_eq p _ _,
      map_add, map_add, map_mul, map_pow, map_natCast]
  · show PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[p]))).coeff 1)
        = PadicInt.toZModPow N (f.coeff 1) + 2 * (ĉ : ZMod (p ^ N))
    rw [comp_translate_coeff_one p hf hdeg, map_add, map_mul, map_natCast, map_ofNat]

/-- **All-translate all-depth splitU fiber ⟹ genuine certificate, AXIOM-FREE, general
`p`**: the `affineEquiv`-translated `ChainPairU` fiber of `f` is the `c = 0` fiber of the
genuine translate `g = f(x + ĉ)` (`transBoxP_comp`); fire the all-depth conclusion on `g`,
transport the certificate back to `f` along the pure translation (`qpType_translate_rescale`
at `a = 1`, relation `translate_rel`). -/
theorem transChainFiberU_split_hasType {ms : List ℕ} (hms : ∀ x ∈ ms, 1 ≤ x) {m ĉ N : ℕ}
    (hbud : 2 * ms.sum + ChainMenuU.leafNeedU m ≤ N)
    {f : ℤ_[p][X]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : ChainMenuU.ChainPairU p ms m N N
      (RecenterBox.affineEquiv p N N le_rfl ĉ
        (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1)))) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = ChainMenu.splitType2 := by
  have hg : (f.comp (X + C (ĉ : ℤ_[p]))).Monic := comp_translate_monic p hf hdeg _
  have hgdeg : (f.comp (X + C (ĉ : ℤ_[p]))).natDegree = 2 :=
    comp_translate_natDegree p hf hdeg _
  have hfib' : ChainMenuU.ChainPairU p ms m N N
      (PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[p]))).coeff 0),
        PadicInt.toZModPow N ((f.comp (X + C (ĉ : ℤ_[p]))).coeff 1)) := by
    rw [transBoxP_comp p hf hdeg ĉ N]
    exact hfib
  obtain ⟨Fg, hFg⟩ := chainFiberU_split_hasType p hms hbud le_rfl hg hgdeg hfib'
  obtain ⟨F, hF⟩ := qpType_translate_rescale p 1 (ĉ : ℤ_[p]) one_ne_zero
    (translate_rel p f (ĉ : ℤ_[p])) Fg
  exact ⟨F, hF.trans hFg⟩

end TranslateP

/-! ## Block 7 — the `p = 3` witness and the axiom-free gate (blueprint §3 non-vacuity;
the coherence/mutation-probe consumers live in `OM/OmLeafFaithful.lean` Block 5c) -/

section GateWitness

/-- The W6q splitU witness: `y² + 9y + 18 = (y + 3)(y + 6)` over `ℤ_[3]` — the `m = 1`
splitU frame `b₀ = 3²·2`, `b₁ = 3·3`, residual pair `(w̄₀, w̄₁) = (2, 0)`, i.e. the
hand-enumerated splitU pool member `z² + 2 = (z − 1)(z − 2)` over `F₃`
(`ChainMenuU.rootedPairs_three`). -/
noncomputable def w6qSplitUPoly : Polynomial ℤ_[3] := X ^ 2 + C 9 * X + C 18

theorem w6qSplitUPoly_monic : w6qSplitUPoly.Monic := by
  unfold w6qSplitUPoly
  monicity!

theorem w6qSplitUPoly_natDegree : w6qSplitUPoly.natDegree = 2 := by
  unfold w6qSplitUPoly
  compute_degree!

theorem w6qSplitUPoly_coeff_zero : w6qSplitUPoly.coeff 0 = 18 := by
  unfold w6qSplitUPoly
  simp

theorem w6qSplitUPoly_coeff_one : w6qSplitUPoly.coeff 1 = 9 := by
  unfold w6qSplitUPoly
  simp

/-- **The witness inhabits the splitU leaf fiber** at `m = 1`, frame `(3, 3)`
(`leafNeedU 1 = 3 = N`, the minimal readable frame): `v(b₀) = 2` with digit `2`,
`v(b₁) ≥ 1` with digit `0`, pair `(2, 0) ∈ rootedPairs 3` — digit checks by `decide`. -/
theorem w6qSplitUPair_mem :
    ChainMenuU.LeafPairU 3 1 3 3
      (PadicInt.toZModPow 3 (w6qSplitUPoly.coeff 0),
        PadicInt.toZModPow 3 (w6qSplitUPoly.coeff 1)) := by
  rw [w6qSplitUPoly_coeff_zero, w6qSplitUPoly_coeff_one]
  have h18 : PadicInt.toZModPow 3 (18 : ℤ_[3]) = (18 : ZMod (3 ^ 3)) := map_ofNat _ 18
  have h9 : PadicInt.toZModPow 3 (9 : ℤ_[3]) = (9 : ZMod (3 ^ 3)) := map_ofNat _ 9
  rw [h18, h9]
  exact ⟨by decide, by decide, by decide⟩

/-- The witness factors LITERALLY: `(y − (−3))(y − (−6)) = y² + 9y + 18`. -/
theorem w6qSplitUPoly_factors :
    (X - C (-3 : ℤ_[3])) * (X - C (-6 : ℤ_[3])) = w6qSplitUPoly := by
  unfold w6qSplitUPoly
  rw [show (9 : ℤ_[3]) = -(-3 + -6) from by norm_num,
    show (18 : ℤ_[3]) = (-3 : ℤ_[3]) * (-6) from by norm_num]
  simp only [map_neg, map_add, map_mul]
  ring

/-- **The irreducibility REFUTER at the witness**: the direct two-factor certificate makes
`w6qSplitUPoly` reducible over ℚ₃ — any singleton-type keying (`{(2,1)}` or `{(1,2)}`) at
the splitU witness machine-derives `False` against this (the Block 5c mutation probe of
`OM/OmLeafFaithful.lean` consumes it). -/
theorem w6qSplitU_not_irreducible :
    ¬ Irreducible (w6qSplitUPoly.map (algebraMap ℤ_[3] ℚ_[3])) :=
  not_irreducible_of_two_factors 3
    (pairFactorization 3 (-3) (-6) w6qSplitUPoly_factors) rfl

/-- **Gate (splitU witness, AXIOM-FREE certificate)**: the splitU master's verdict at the
witness — a genuine certificate of type `{(1,1),(1,1)}`, CORE-ONLY footprint (the blueprint
§3 guard: the split-keyed payload is PROVED outright; the axiom instance at this literal is
redundant-in-consumers by REQUIREMENT). -/
theorem gate_w6q_splitU_hasType_axfree :
    ∃ F : QpType.QpFactorization 3 w6qSplitUPoly,
      QpType.qpType 3 F = ChainMenu.splitType2 :=
  leafFiberU_split_hasType 3 (by decide) le_rfl
    w6qSplitUPoly_monic w6qSplitUPoly_natDegree w6qSplitUPair_mem

end GateWitness

/-! ## Block 8 — axiom census (this module declares NO axiom; everything must be core-only:
`[propext, Classical.choice, Quot.sound]`. Any `om_leaf_faithful` appearance is a FAILURE —
blueprint §3: the split-keyed payloads must be axiom-free.) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeSplitU.norm_eq_one_of_toZMod_ne
#print axioms LeanUrat.OM.QpTypeSplitU.norm_lt_one_of_toZMod_eq_zero
#print axioms LeanUrat.OM.QpTypeSplitU.toZMod_eq_of_norm_sub_lt_one
#print axioms LeanUrat.OM.QpTypeSplitU.toZMod_natCast_val
#print axioms LeanUrat.OM.QpTypeSplitU.hensel_lift_at_simple_root
#print axioms LeanUrat.OM.QpTypeSplitU.splitRes_two_roots
#print axioms LeanUrat.OM.QpTypeSplitU.splitSep_master_hasType
#print axioms LeanUrat.OM.QpTypeSplitU.leafSplitU_master_hasType
#print axioms LeanUrat.OM.QpTypeSplitU.ord0Split_master_hasType
#print axioms LeanUrat.OM.QpTypeSplitU.leafFiberU_split_hasType
#print axioms LeanUrat.OM.QpTypeSplitU.ord0SplitCell_hasType
#print axioms LeanUrat.OM.QpTypeSplitU.stepDecodeU_general
#print axioms LeanUrat.OM.QpTypeSplitU.chainUnwindU
#print axioms LeanUrat.OM.QpTypeSplitU.chainFiberU_split_hasType
#print axioms LeanUrat.OM.QpTypeSplitU.castHom_pow_self_eq
#print axioms LeanUrat.OM.QpTypeSplitU.transBoxP_comp
#print axioms LeanUrat.OM.QpTypeSplitU.transChainFiberU_split_hasType
#print axioms LeanUrat.OM.QpTypeSplitU.w6qSplitUPoly
#print axioms LeanUrat.OM.QpTypeSplitU.w6qSplitUPoly_monic
#print axioms LeanUrat.OM.QpTypeSplitU.w6qSplitUPoly_natDegree
#print axioms LeanUrat.OM.QpTypeSplitU.w6qSplitUPair_mem
#print axioms LeanUrat.OM.QpTypeSplitU.w6qSplitUPoly_factors
#print axioms LeanUrat.OM.QpTypeSplitU.w6qSplitU_not_irreducible
#print axioms LeanUrat.OM.QpTypeSplitU.gate_w6q_splitU_hasType_axfree

end AxCheck

end LeanUrat.OM.QpTypeSplitU
