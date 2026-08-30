/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapH.H98
import Uniformity.ChapH.H97b
import Uniformity.Density.CoveringMenus
import Uniformity.Density.Gates

/-!
# Uniformity.ChapI.IFCG45 — [DRN 2026-08-30] the capstone's `a2` field dissected:
`DrainageAt n ↔ UndecidedDrainAt n` (the σ-free reduction), the degree instances
`n = 0, 1` (with `2, 3` re-pinned), and the per-degree package bridge

**Unit DRN** (verdict `runs/wave-c/verdict_DRN.md`).  The capstone structure
`CapstoneHypotheses n` (`ChapI/I10_I15_I18.lean` §2) carries the field `a2 : DrainageAt n`;
PROJECT_STATE §4 (2026-08-30) flags it as a coverage gap ("only `drainageAt_two` exists; NO
general-n discharger").  This file pins the field exactly and lands everything the machinery
reaches today, uniformly in `n`.

## §0 THE PIN — what `a2` demands

`DrainageAt n` (`Density/Statement.lean:118`) quantifies over EVERY complete DVR `O` with
finite residue field and EVERY splitting type `σ`, and demands
`UndecidedVanishes O n σ : Tendsto (gapSeq O n σ) atTop (𝓝 0)` — the level-`N` **ambiguity
gap** (`possibleSeq − decidedSeq`: the proportion of coefficient classes with a `σ`-lift that
are not yet forced) drains to `0`.  Equivalently (landed both directions,
`genuineDensity_eq_of_drainage` / `drainage_of_genuineDensity_eq`): THE density equals the
certified density at `(n, σ)`.  It is an *exhaustiveness-in-the-limit* statement about the
decided strata, NOT a per-class "eventually decided" claim and NOT itself a sum-to-1 claim
(`TotalMassOne` follows from it via `totalMassOne_of_drainage`).

## What is landed where (the instances, before this file)

* `n = 1`: `drainage_one` (`Density/Gates.lean:125`) — the gap is identically `0`.
* `n = 2`: `drainage_two` (`Density/Drainage.lean:838`), wrapped `drainageAt_two`
  (`ChapI/I03_I04w.lean:46`) — the tangency counting bound at level `2M`.
* `n = 3`: **already landed, missed by the PROJECT_STATE flag** — `drainageAt_three`
  (`ChapH/H97b.lean:236`), unconditional Lean-core, from the H97r4 counting recursion.
* General `n`: `drainage_of_package` (`ChapH/H98.lean:148`) fires `∀ n, DrainageAt n` from
  `∀ n, InductionPackage n` — but the package's induction step (`ChapH/H124c.lean`) CARRIES
  `FullClusterRateBound n` (gates HYP.36/30/32/33, HYP.81 at μ ≥ 3, HYP.82 at n ≥ 8;
  `d ≥ 2` leaf reads B-BOX-1-gated), so `∀ n, InductionPackage n` is OPEN and
  `drainageAt_all` is NOT provable from landed machinery.  Nothing here pretends otherwise.

## What THIS file adds

* **§1 the missing cheap instances**: `drainageAt_zero`, `drainageAt_one` (both trivial —
  the gap is levelwise `0`), plus `example` regression pins re-exporting `n = 2, 3`.
* **§2 ★ the σ-free reduction, uniform in `n`** — the file's content.  The named Prop

      UndecidedDrainAt n := ∀ O, Tendsto (undecidedSeq O n) atTop (𝓝 0)

  (no `σ` anywhere) and the EQUIVALENCE `drainageAt_iff_undecidedDrain n`.  The `←`
  direction is CN-11's landed plumbing (`drainage_of_undecided_comp`, φ = id).  The `→`
  direction is NEW counting: over a covering menu `S` (CN-22: one exists at every degree)
  the undecided classes and the per-type decided classes pack disjointly into the level-`N`
  box, `undecidedCount + Σ_{σ∈S} decidedCount ≤ q^(nN)`, while the possible sets cover it,
  `q^(nN) ≤ Σ_{σ∈S} possibleCount` (landed `card_le_sum_possibleCount`); subtracting,
  `undecidedSeq ≤ Σ_{σ∈S} gapSeq σ`, and a finite sum of draining gaps drains.
  **Consequence**: the capstone's `a2` field at EVERY degree is exactly the scalar rate
  statement on `undecidedSeq` — the σ-quantifier is never the frontier, and the exact open
  remainder at `n ≥ 4` is `UndecidedDrainAt n` (equivalently, by §3, any per-`O`-uniform
  rate species — which is where the H.124 census machinery operates).
* **§3 the per-degree package bridge**: `drainageAt_of_package : InductionPackage n →
  DrainageAt n` — H.98's `∀ n` conditional holds degree-by-degree (extraction, no new
  mathematics), so any FUTURE `package_n` lands `a2` at that `n` alone.
* **§4 the exact remainder, sharpened**: `drainageAt_all_iff_undecidedDrain_from_four` —
  the capstone's full `a2` supply `∀ n, DrainageAt n` is EQUIVALENT to
  `∀ n ≥ 4, UndecidedDrainAt n`.  Degrees `0–3` are closed; the remainder is named, σ-free,
  and exactly where the H.124 rate machinery operates.

## Honesty

`DrainageAt` is untouched (`Density/Statement.lean`); no statement is weakened; every
theorem here is uniform in `n` or an explicit instance.  The general-`n` field REMAINS OPEN;
its minimal named remainder is `UndecidedDrainAt n` (n ≥ 4).  Axioms: Lean core only.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.IFCG45

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density

/-! ## §1 The cheap instances: `n = 0` and `n = 1` -/

section Instances

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- At `n = 0` there is exactly one monic polynomial (the empty product), so every class is
decided outright: the possible and decided sets coincide for every type and level. -/
theorem possibleSet_zero_eq (σ : FactorizationType) (N : ℕ) :
    possibleSet O 0 σ N = decidedSet O 0 σ N := by
  ext c
  refine ⟨?_, fun hc => decided_imp_possible hc⟩
  rintro ⟨a, -, hta⟩
  intro b _
  have hba : b = a := funext fun i => i.elim0
  rwa [hba]

/-- **`DrainageAt 0`** — degenerate but a genuine field of `∀ n, CapstoneHypotheses n`:
the ambiguity gap at degree `0` is identically zero. -/
theorem drainageAt_zero : DrainageAt 0 := by
  intro O _ _ _ _ _ σ
  have hz : gapSeq O 0 σ = fun _ => (0 : ℝ) := by
    funext N
    rw [gapSeq, possibleSeq, decidedSeq, possibleCount, decidedCount, possibleSet_zero_eq,
      sub_self]
  rw [UndecidedVanishes, hz]
  exact tendsto_const_nhds

/-- **`DrainageAt 1`** — the landed `drainage_one` (`Density/Gates.lean:125`), packaged at the
`DrainageAt` carrier. -/
theorem drainageAt_one : DrainageAt 1 := by
  intro O _ _ _ _ _ σ
  exact drainage_one σ

-- Regression pins: the landed `n = 2` and `n = 3` instances, re-exported facts (no new proof;
-- the `n = 2` production wrapper `drainageAt_two` lives in `I03_I04w.lean`, whose import is
-- not taken here — the pin goes to its own source `drainage_two` instead).
example : DrainageAt 2 := fun _ _ _ _ _ _ σ => drainage_two σ
example : DrainageAt 3 := drainageAt_three

end Instances

/-! ## §2 ★ The σ-free reduction: the counting core

An undecided class is decided for NO type (`UndecidedAt`), and distinct types have disjoint
decided sets (`decidedSet_disjoint`), so the undecided classes and the per-type decided
classes pack DISJOINTLY into the level-`N` box; meanwhile over a covering menu the possible
sets COVER the box (landed `card_le_sum_possibleCount`).  Subtracting the two counts:
`undecidedSeq ≤ Σ_{σ∈S} gapSeq σ`.  A finite sum of draining gaps drains, so per-type
drainage implies the σ-free scalar rate — the converse of CN-11. -/

section Reduction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The disjoint packing.**  Undecided classes plus per-type decided classes (any finite set
of types) fit into the level-`N` box without collision.  Sigma-injection pattern of the landed
`sum_decidedCount_le`, extended by the undecided summand. -/
theorem undecidedCount_add_sum_decidedCount_le (n : ℕ) (S : Finset FactorizationType) (N : ℕ) :
    undecidedCount O n N + ∑ σ ∈ S, decidedCount O n σ N ≤ residueCard O ^ (n * N) := by
  classical
  have hinj : Function.Injective
      (Sum.elim (fun c : undecidedSet O n N => (c : Coeff O n N))
        (fun x : (Σ σ : {σ // σ ∈ S}, decidedSet O n σ.1 N) => (x.2 : Coeff O n N))) := by
    rintro (c | ⟨σ, c⟩) (d | ⟨τ, d⟩) hcd
    · simp only [Sum.elim_inl] at hcd
      exact congrArg Sum.inl (Subtype.ext hcd)
    · -- an undecided class cannot equal a `τ`-decided one
      exfalso
      simp only [Sum.elim_inl, Sum.elim_inr] at hcd
      have hund : UndecidedAt O n N (c : Coeff O n N) := c.2
      have hdec : DecidedAt O n τ.1 N (d : Coeff O n N) := d.2
      rw [← hcd] at hdec
      exact hund τ.1 hdec
    · exfalso
      simp only [Sum.elim_inl, Sum.elim_inr] at hcd
      have hdec : DecidedAt O n σ.1 N (c : Coeff O n N) := c.2
      have hund : UndecidedAt O n N (d : Coeff O n N) := d.2
      rw [hcd] at hdec
      exact hund σ.1 hdec
    · simp only [Sum.elim_inr] at hcd
      have hστ : (σ : FactorizationType) = (τ : FactorizationType) := by
        by_contra hne
        exact (Set.disjoint_left.1 (decidedSet_disjoint (O := O) (n := n) hne N)) c.2
          (by rw [hcd]; exact d.2)
      obtain rfl : σ = τ := Subtype.ext hστ
      exact congrArg Sum.inr (by simpa using Subtype.ext hcd)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_sum, Nat.card_sigma, card_coeff] at hle
  rw [← Finset.sum_attach S (fun σ => decidedCount O n σ N)]
  exact hle

/-- **The σ-free majorant.**  Over a covering menu the undecided proportion is at most the sum
of the per-type ambiguity gaps — the packing above against the landed cover
`card_le_sum_possibleCount`. -/
theorem undecidedSeq_le_sum_gapSeq {n : ℕ} {S : Finset FactorizationType}
    (h : CoveringMenu O n S) (N : ℕ) :
    undecidedSeq O n N ≤ ∑ σ ∈ S, gapSeq O n σ N := by
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos _
  have hnat : undecidedCount O n N + ∑ σ ∈ S, decidedCount O n σ N
      ≤ ∑ σ ∈ S, possibleCount O n σ N :=
    (undecidedCount_add_sum_decidedCount_le (O := O) n S N).trans (card_le_sum_possibleCount h N)
  have hcast : (undecidedCount O n N : ℝ) + ∑ σ ∈ S, (decidedCount O n σ N : ℝ)
      ≤ ∑ σ ∈ S, (possibleCount O n σ N : ℝ) := by exact_mod_cast hnat
  have hsum : ∑ σ ∈ S, gapSeq O n σ N
      = (∑ σ ∈ S, ((possibleCount O n σ N : ℝ) - (decidedCount O n σ N : ℝ)))
          / (residueCard O : ℝ) ^ (n * N) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [gapSeq, possibleSeq, decidedSeq, div_sub_div_same]
  have hsub : (undecidedCount O n N : ℝ)
      ≤ ∑ σ ∈ S, ((possibleCount O n σ N : ℝ) - (decidedCount O n σ N : ℝ)) := by
    rw [Finset.sum_sub_distrib]
    linarith
  rw [undecidedSeq, hsum, div_le_div_iff₀ hq hq]
  exact mul_le_mul_of_nonneg_right hsub hq.le

/-- **Per-type drainage implies the scalar rate** (the converse of CN-11): if every type's gap
drains, the undecided proportion itself drains — the menu is CN-22's. -/
theorem undecided_tendsto_zero_of_vanishes {n : ℕ}
    (hd : ∀ σ : FactorizationType, UndecidedVanishes O n σ) :
    Tendsto (undecidedSeq O n) atTop (𝓝 0) := by
  obtain ⟨S, hS⟩ := exists_coveringMenu (O := O) n
  have hsum : Tendsto (fun N => ∑ σ ∈ S, gapSeq O n σ N) atTop (𝓝 0) := by
    have h := tendsto_finsetSum S (fun σ _ => hd σ)
    simpa using h
  exact squeeze_zero
    (fun N => div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le)
    (fun N => undecidedSeq_le_sum_gapSeq hS N) hsum

end Reduction

/-! ## §3 The named σ-free carrier, the equivalence, and the per-degree package bridge -/

/-- **The σ-free drainage carrier at degree `n`** — the `a2` field's minimal named remainder:
the undecided PROPORTION drains (no splitting type mentioned anywhere), over every complete
DVR with finite residue field.  Same interface bundle as `DrainageAt`. -/
def UndecidedDrainAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    Tendsto (undecidedSeq O n) atTop (𝓝 0)

/-- ★ **The `a2` field, dissected — the equivalence.**  `DrainageAt n` is EXACTLY the σ-free
scalar rate statement: the per-type σ-quantifier is never the frontier.  `←` is CN-11's landed
plumbing (`drainage_of_undecided_comp`, `φ = id`); `→` is §2's packing/cover subtraction. -/
theorem drainageAt_iff_undecidedDrain (n : ℕ) : DrainageAt n ↔ UndecidedDrainAt n := by
  constructor
  · intro hd O _ _ _ _ _
    exact undecided_tendsto_zero_of_vanishes (hd O)
  · intro hu O _ _ _ _ _ σ
    exact drainage_of_undecided_comp (φ := fun M => M) tendsto_id (hu O) σ

/-- The analytic step of the package bridge, replicated from H.98 (where it is `private`):
a polynomial coefficient against an exponential deficit with `q ≥ 2` tends to `0`.  The
truncated subtraction `M − c` needs no side condition: `(q^(M−c))⁻¹ ≤ q^c·(q⁻¹)^M` at every
`M`. -/
private theorem tendsto_rateBound_zero' {q : ℕ} (hq : 2 ≤ q) {K : ℝ} (hK : 0 ≤ K) (B c : ℕ) :
    Tendsto (fun M : ℕ => K * (M : ℝ) ^ B * ((q : ℝ) ^ (M - c))⁻¹) atTop (𝓝 0) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have h : (0 : ℕ) < q := by omega
    exact_mod_cast h
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h : (1 : ℕ) ≤ q := by omega
    exact_mod_cast h
  have hlt1 : (q : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    have h : (1 : ℕ) < q := by omega
    exact_mod_cast h
  have hgeom : Tendsto (fun M : ℕ => (K * (q : ℝ) ^ c) * ((M : ℝ) ^ B * ((q : ℝ)⁻¹) ^ M))
      atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_const_mul_const_pow_of_lt_one B (inv_nonneg.2 hq0.le) hlt1).const_mul
        (K * (q : ℝ) ^ c)
  have hbound : ∀ M : ℕ, ((q : ℝ) ^ (M - c))⁻¹ ≤ (q : ℝ) ^ c * ((q : ℝ)⁻¹) ^ M := by
    intro M
    rw [inv_pow, ← one_div, ← div_eq_mul_inv,
      div_le_div_iff₀ (pow_pos hq0 _) (pow_pos hq0 _), one_mul, ← pow_add]
    exact pow_le_pow_right₀ hq1 (by omega)
  refine squeeze_zero (fun M => ?_) (fun M => ?_) hgeom
  · exact mul_nonneg (mul_nonneg hK (pow_nonneg (Nat.cast_nonneg M) B))
      (inv_nonneg.2 (pow_nonneg hq0.le _))
  · calc K * (M : ℝ) ^ B * ((q : ℝ) ^ (M - c))⁻¹
        ≤ K * (M : ℝ) ^ B * ((q : ℝ) ^ c * ((q : ℝ)⁻¹) ^ M) :=
          mul_le_mul_of_nonneg_left (hbound M)
            (mul_nonneg hK (pow_nonneg (Nat.cast_nonneg M) B))
      _ = (K * (q : ℝ) ^ c) * ((M : ℝ) ^ B * ((q : ℝ)⁻¹) ^ M) := by ring

/-- **The per-degree package bridge.**  H.98's `drainage_of_package` consumes
`∀ n, InductionPackage n`; the implication in fact holds DEGREE-BY-DEGREE, so any future
`package_n` theorem lands the capstone's `a2` at that `n` alone.  Extraction of H.98's body at
fixed `n`; no new mathematics. -/
theorem drainageAt_of_package {n : ℕ} (hp : InductionPackage n) : DrainageAt n := by
  obtain ⟨K, B, c, hK, h⟩ := hp
  intro O _ _ _ _ _ σ
  obtain ⟨-, hrate⟩ := h O
  have hlim : Tendsto (fun M : ℕ => undecidedSeq O n M) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_rateBound_zero' (two_le_residueCard O) hK B c)
    · filter_upwards with M
      exact div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le
    · filter_upwards [eventually_ge_atTop 1] with M hM
      exact hrate M hM
  exact drainage_of_undecided_comp (φ := fun M => M) tendsto_id hlim σ

/-! ## §4 The exact remainder of the capstone's `a2` supply -/

/-- ★ **The `a2` coverage ledger, sharpened.**  The full drainage supply
`∀ n, DrainageAt n` (what `drainage_of_capstoneHypotheses` extracts, and what
`UniformityStatement.ofDecided` / `totalMassOne_of_drainage` consume) is EQUIVALENT to the
σ-free scalar rate at the degrees `n ≥ 4` alone: degrees `0, 1, 2, 3` are closed
unconditionally (§1 + the landed `drainage_two`/`drainageAt_three`).  This is the field's
exact named remainder. -/
theorem drainageAt_all_iff_undecidedDrain_from_four :
    (∀ n, DrainageAt n) ↔ (∀ n, 4 ≤ n → UndecidedDrainAt n) := by
  constructor
  · intro h n _
    exact (drainageAt_iff_undecidedDrain n).1 (h n)
  · intro h n
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · exact drainageAt_zero
      · exact drainageAt_one
      · exact fun _ _ _ _ _ _ σ => drainage_two σ
      · exact drainageAt_three
    · exact (drainageAt_iff_undecidedDrain n).2 (h n h4)

end Uniformity.Density.IFCG45

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG45.drainageAt_zero
#print axioms Uniformity.Density.IFCG45.drainageAt_one
#print axioms Uniformity.Density.IFCG45.undecidedCount_add_sum_decidedCount_le
#print axioms Uniformity.Density.IFCG45.undecidedSeq_le_sum_gapSeq
#print axioms Uniformity.Density.IFCG45.undecided_tendsto_zero_of_vanishes
#print axioms Uniformity.Density.IFCG45.drainageAt_iff_undecidedDrain
#print axioms Uniformity.Density.IFCG45.drainageAt_of_package
#print axioms Uniformity.Density.IFCG45.drainageAt_all_iff_undecidedDrain_from_four
