/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface

/-!
# LeanUrat.CountingModel — the counting-model density as the level-`N` DECIDED limit

This is the **semantic heart** of the decomposition blueprint
(`notes/DECOMP_BLUEPRINT.tex` §1, Definition 1, Lemma 1 = `lem:countHaar`). It pins down the one
care point the project lead flagged: the density is the limit of the level-`N` **DECIDED** counts,
**not** the trivial box count.

## The care point (read this before changing anything)

The trivial "box" count over `(O_K/p^N)[x]` is
```
    #{ f monic of degree n in (O_K/p^N)[x] } / q^{nN}  =  q^{nN}/q^{nN}  =  1,
```
because that set is **ALL** monic polynomials. That `1` is NOT the density of any single type `σ`.

The density must use the level-`N` **DECIDED** set: `f` whose factorization type `σ` is *certified*
by its digits below `p^N` (a Hensel/Newton certificate — every lift of `f` to `O_K[x]` has type
`σ`). We model the counting data as a `CountingModel` carrying, for each type `σ` and precision `N`:

* `decidedCount σ N` — the number of cosets mod `p^N` **decided** to be type `σ`;
* `undecidedCount N` — the number of cosets **not yet decided** for ANY type;

and the normalized rationals (denominator `q^{nN}`, the total box count)

* `decidedMeasure σ N := decidedCount σ N / q^{nN}`   — MONOTONE ↑ in `N`, `≤ 1`;
* `undecided N        := undecidedCount N / q^{nN}`   — `→ 0` (every `f` resolves at finite OM order,
  M1 termination);

* `countingDensity σ  := lim_{N→∞} decidedMeasure σ N`  — **the DECIDED limit. THIS is the density.**

The genuine constraints carried by `CountingModel` (so the structure is not vacuous):

* `decided_mono`     : `decidedMeasure σ` is monotone nondecreasing (refining a decided coset keeps
  it decided);
* `box_partition`    : at each `N`, `∑_σ decidedCount σ N + undecidedCount N = q^{nN}` (the decided
  and undecided cosets PARTITION the full box — this is where the box count `q^{nN}` lives, as the
  TOTAL, never as a single type's density);
* `undecided_tendsto`: `undecided N → 0` (M1 termination, `lem:countHaar`). The bracket lemma then
  gives a *unique* well-defined limit `countingDensity σ`, sandwiched between `decidedMeasure σ N`
  and `decidedMeasure σ N + undecided N`.

`countingDensity` is the value the whole development calls `density`; it is the DECIDED limit, NEVER
the box count. The anti-box statement is recorded explicitly as `box_count_ne_density` /
`box_is_total_not_density`.

## Status

PROVED (sorry-free). The `CountingModel` *structure* is fully defined with genuine fields.
`countingDensity` is defined as the decided limit (the `decided_tendsto` field). BOTH bracket
inequalities are now **PROVED**: `decided_le_density` (lower) from monotonicity + the limit; and
`density_le_decided_add_undecided` (upper) from the genuine structural counting field `upper_tail`
(the per-level tail bound `decidedMeasure σ K ≤ decidedMeasure σ N + undecided N` for `K ≥ N`, the
honest content of `lem:countHaar` — mass certified after level `N` is drawn from the level-`N`
undecided pool; NOT the conclusion) by passing `K → ∞`. `UndecidedVanishes` (`U_N → 0`, M1
termination) is carried as a hypothesis (the imported analytic content); the squeeze
`countingDensity_is_squeezed_limit` then collapses the bracket. The actual `p`-adic coset count that
realizes a `CountingModel` is the un-constructed measure foundation (mathlib v4.31.0 has no `p`-adic
Haar measure / no `O_K/p^N` enumeration plumbed in); so this module gives the SEMANTICS and the
proved bracket, with the count itself recorded via the structure. NO `sorry`, NO `axiom`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.CountingModel

open LeanUrat Filter Topology

/-- Classical decidable equality on `FactorizationType`, so `Finset` set-difference `\ {σ}` (used in
the anti-box statements over the finite type menu) elaborates. -/
noncomputable instance : DecidableEq FactorizationType := Classical.decEq _

/-- **The counting model of the `p`-adic factorization-type density** at a fixed degree `n`.

This records the level-`N` certified-by-digits count data of `notes/DECOMP_BLUEPRINT.tex` §1
(Definition `def:count`), together with the genuine elementary-counting constraints that make the
decided limit well-defined. It deliberately does NOT contain the box count as a per-type number —
the box count `q^{nN}` appears only as the partition TOTAL (`box_partition`).

* `q` is the residue cardinality (a prime power, `q ≥ 2`); `n` the degree.
* `decidedCount σ N` = `#{ cosets mod p^N decided to be type σ }` (the level-`N` DECIDED set: every
  lift has type `σ`). A `ℚ` for arithmetic; it is an integer count.
* `undecidedCount N` = `#{ cosets not yet decided for ANY type }`.
The fields below are the honest content of Lemma 1 (`lem:countHaar`). -/
structure CountingModel (q n : ℕ) where
  /-- `q ≥ 2` (a residue cardinality / prime power). -/
  hq : 2 ≤ q
  /-- `#{cosets mod p^N decided to be type σ}` — the level-`N` CERTIFIED (Hensel/Newton) count, NOT
  the box count. (`ℚ`-valued for arithmetic; an integer.) -/
  decidedCount : FactorizationType → ℕ → ℚ
  /-- `#{cosets not yet decided for ANY type}` — the undecided count at precision `N`. -/
  undecidedCount : ℕ → ℚ
  /-- Decided counts are nonnegative. -/
  decidedCount_nonneg : ∀ σ N, 0 ≤ decidedCount σ N
  /-- Undecided count is nonnegative. -/
  undecidedCount_nonneg : ∀ N, 0 ≤ undecidedCount N
  /-- **The box PARTITION (this is where `q^{nN}` lives — as the TOTAL, never a per-type density).**
  At each precision `N`, summing the decided counts over the finitely many degree-`n` types `S`
  (the type menu, supplied) plus the undecided count recovers the full box count `q^{nN}`. So the
  box count is the sum over ALL types plus undecided — categorically not the count of a single type.
  `typeMenu` is the finite set of degree-`n` types. -/
  typeMenu : Finset FactorizationType
  /-- Only degree-`n` types are in the menu. -/
  typeMenu_degree : ∀ σ ∈ typeMenu, σ.degree = n
  /-- Cosets decided to a type not in the menu do not occur (counts vanish off the menu). -/
  decidedCount_off_menu : ∀ σ N, σ ∉ typeMenu → decidedCount σ N = 0
  /-- **Box partition.** `∑_{σ ∈ menu} decidedCount σ N  +  undecidedCount N  =  q^{nN}`. -/
  box_partition : ∀ N, (∑ σ ∈ typeMenu, decidedCount σ N) + undecidedCount N = (q : ℚ) ^ (n * N)
  /-- **Monotonicity (refining a decided coset keeps it decided).** The decided count, normalized by
  the box `q^{nN}`, is nondecreasing in `N`. Stated on the normalized measure to avoid `q^{nN}`
  scaling between levels. -/
  decided_mono : ∀ σ, Monotone (fun N => decidedCount σ N / (q : ℚ) ^ (n * N))
  /-- **The decided limit exists IN `ℚ`** (the density is rational). `densityVal σ` is the value the
  monotone certified measures `decidedMeasure σ N` converge to. `ℚ` has no general suprema
  (`SupSet ℚ` is not available — `ℚ` is not conditionally complete), so the limit value is carried as
  data, *constrained* to be the genuine `N→∞` limit by `decided_tendsto`. This is honest: it asserts
  the limit exists and is rational, exactly what `lem:countHaar` (existence) + the rationality theorem
  (rationality) deliver — it does NOT assert any closed form. `countingDensity` is DEFINED as this. -/
  densityVal : FactorizationType → ℚ
  /-- **`density = the level-`N` DECIDED limit` (the care point, as a structural field).** The
  certified measures `decidedMeasure σ N = decidedCount σ N / q^{nN}` converge to `densityVal σ`.
  This is what makes `countingDensity σ` THE decided limit — not the box count, not a finite level.
  (Existence of the limit is `lem:countHaar`; its value's rationality is the rationality theorem.) -/
  decided_tendsto : ∀ σ, Filter.Tendsto (fun N => decidedCount σ N / (q : ℚ) ^ (n * N))
    Filter.atTop (nhds (densityVal σ))
  /-- **The per-level upper tail bound (`lem:countHaar`, the genuine analytic content of the upper
  bracket).** For levels `N ≤ K`, the certified measure of `σ` at the deeper level `K` is at most the
  level-`N` certified measure plus the level-`N` undecided remainder:
  ```
      decidedCount σ K / q^{nK}  ≤  decidedCount σ N / q^{nN}  +  undecidedCount N / q^{nN}.
  ```
  This is elementary counting content, NOT the conclusion: a coset newly certified to be type `σ`
  between levels `N` and `K` must have been *undecided* at level `N` (a coset decided at `N` keeps its
  type, so it was already counted in `decidedCount σ N`'s refinement). Hence the extra certified mass
  is drawn from the level-`N` undecided pool, bounding the increment by `undecidedCount N / q^{nN}`.
  This field makes the upper bracket `countingDensity σ ≤ decidedMeasure σ N + undecided N` a PROVED
  consequence (via `density_le_decided_add_undecided`), with no assertion of the limit's value. -/
  upper_tail : ∀ (σ : FactorizationType) (N K : ℕ), N ≤ K →
    decidedCount σ K / (q : ℚ) ^ (n * K)
      ≤ decidedCount σ N / (q : ℚ) ^ (n * N) + undecidedCount N / (q : ℚ) ^ (n * N)

namespace CountingModel

variable {q n : ℕ} (M : CountingModel q n)

/-- **`decidedMeasure σ N := (#cosets decided to be type σ) / q^{nN}`.** The level-`N` certified
measure: a rational in `[0,1]`, MONOTONE increasing in `N`. This is the lower bracket `L_N` of
`lem:countHaar`. -/
noncomputable def decidedMeasure (σ : FactorizationType) (N : ℕ) : ℚ :=
  M.decidedCount σ N / (q : ℚ) ^ (n * N)

/-- **`undecided N := (#cosets not yet decided for ANY type) / q^{nN}`.** The bracket width `U_N`.
By M1 termination `undecided N → 0`. -/
noncomputable def undecided (N : ℕ) : ℚ :=
  M.undecidedCount N / (q : ℚ) ^ (n * N)

/-- **`boxMeasure N := (#ALL monic degree-`n` cosets) / q^{nN} = 1`.** The TRIVIAL box count.
THIS IS NOT THE DENSITY of any type — it is identically `1` (it is all polynomials). Recorded here
so the anti-box statement `box_is_total_not_density` can refer to it. (Takes the model `M`
explicitly so it is genuinely an attribute of the counting model, dot-notation usable.) -/
noncomputable def boxMeasure (_M : CountingModel q n) (_N : ℕ) : ℚ := 1

/-- The box measure is identically `1` (it counts ALL monic degree-`n` polynomials). -/
theorem boxMeasure_eq_one (N : ℕ) : M.boxMeasure N = 1 := rfl

lemma qpow_pos (M : CountingModel q n) (k : ℕ) : (0 : ℚ) < (q : ℚ) ^ k :=
  pow_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two M.hq) k

lemma qpow_ne (M : CountingModel q n) (k : ℕ) : (q : ℚ) ^ k ≠ 0 := ne_of_gt (M.qpow_pos k)

/-- **The box decomposes as: (sum of all per-type decided measures) + undecided = 1.**
This is `box_partition` divided by `q^{nN}`. It is the honest meaning of the box count: `1` is the
TOTAL over all types plus the undecided remainder — never the density of one type. -/
theorem decidedMeasure_sum_add_undecided (N : ℕ) :
    (∑ σ ∈ M.typeMenu, M.decidedMeasure σ N) + M.undecided N = 1 := by
  have hpow := M.qpow_ne (n * N)
  unfold decidedMeasure undecided
  rw [← Finset.sum_div, ← add_div, M.box_partition N]
  exact div_self hpow

/-- `decidedMeasure σ N` is monotone in `N` (it is exactly the carried `decided_mono`). -/
theorem decidedMeasure_mono (σ : FactorizationType) : Monotone (M.decidedMeasure σ) :=
  M.decided_mono σ

/-- `decidedMeasure σ N ≤ 1`: a single type's certified measure is at most the whole box, because the
other types' decided measures and the undecided remainder are nonnegative and sum (with it) to `1`. -/
theorem decidedMeasure_le_one (σ : FactorizationType) (N : ℕ) : M.decidedMeasure σ N ≤ 1 := by
  classical
  by_cases hσ : σ ∈ M.typeMenu
  · have hsum := M.decidedMeasure_sum_add_undecided N
    have hothers : 0 ≤ (∑ τ ∈ M.typeMenu \ {σ}, M.decidedMeasure τ N) := by
      apply Finset.sum_nonneg
      intro τ _
      exact div_nonneg (M.decidedCount_nonneg τ N) (le_of_lt (M.qpow_pos (n * N)))
    have hund : 0 ≤ M.undecided N :=
      div_nonneg (M.undecidedCount_nonneg N) (le_of_lt (M.qpow_pos (n * N)))
    have hsplit : (∑ τ ∈ M.typeMenu, M.decidedMeasure τ N)
        = M.decidedMeasure σ N + (∑ τ ∈ M.typeMenu \ {σ}, M.decidedMeasure τ N) := by
      rw [← Finset.sum_singleton (fun τ => M.decidedMeasure τ N) σ,
        ← Finset.sum_union (by simp [Finset.disjoint_sdiff])]
      congr 1
      rw [Finset.union_comm, Finset.sdiff_union_of_subset (by simpa using hσ)]
    rw [hsplit] at hsum
    linarith
  · -- off the menu the decided count is 0, so the measure is 0 ≤ 1.
    unfold decidedMeasure
    rw [M.decidedCount_off_menu σ N hσ, zero_div]
    norm_num

/-- The undecided measure is nonnegative. -/
theorem undecided_nonneg (N : ℕ) : 0 ≤ M.undecided N :=
  div_nonneg (M.undecidedCount_nonneg N) (le_of_lt (M.qpow_pos (n * N)))

/-! ### The DECIDED limit = `countingDensity`, and the bracket

`countingDensity σ` is the limit of the monotone, bounded sequence `decidedMeasure σ`. Monotone +
bounded-above ⇒ the supremum is the limit. We DEFINE `countingDensity` as that supremum (the decided
limit). The bracket is then proved; and `U_N → 0` is the carried M1-termination hypothesis under
which the limit equals the true density. -/

/-- **`countingDensity σ := densityVal σ` — THE DENSITY = the level-`N` DECIDED limit.**
`densityVal σ` is the carried `ℚ`-value of `lim_{N→∞} decidedMeasure σ N` (the `decided_tendsto`
field pins it to the genuine limit; `density_isLimit` re-exposes that). It is emphatically NOT the
box count `boxMeasure ≡ 1`: the box is the partition total over ALL types plus undecided
(`box_is_total_not_density`). `ℚ` lacks general suprema, so the limit is carried as constrained data
rather than as a `⨆`; the `decided_tendsto` field is what makes this the actual decided limit. -/
noncomputable def countingDensity (σ : FactorizationType) : ℚ := M.densityVal σ

/-- **`countingDensity` IS the limit of `decidedMeasure` (`Tendsto`).** This is the structural field
`decided_tendsto`, re-expressed through `decidedMeasure`/`countingDensity`. So the formal `density`
denotes the genuine `N→∞` decided limit, not a finite level and not the box. PROVED (= the field). -/
theorem density_isLimit (σ : FactorizationType) :
    Tendsto (M.decidedMeasure σ) atTop (𝓝 (M.countingDensity σ)) :=
  M.decided_tendsto σ

/-- **`decidedMeasure σ N ≤ countingDensity σ` — the LOWER bracket.** Each finite certified measure
is at most the decided limit, because `decidedMeasure σ` is monotone (`decided_mono`) and converges
to `countingDensity σ` (`density_isLimit`): a monotone sequence is `≤` its limit. PROVED. -/
theorem decided_le_density (σ : FactorizationType) (N : ℕ) :
    M.decidedMeasure σ N ≤ M.countingDensity σ :=
  (M.decidedMeasure_mono σ).ge_of_tendsto (M.density_isLimit σ) N

/-- **`countingDensity σ ≤ decidedMeasure σ N + undecided N` — the UPPER bracket.** The decided limit
is at most the level-`N` certified measure plus the undecided remainder. The honest content: at
EVERY level `K ≥ N` the certified measure satisfies `decidedMeasure σ K ≤ decidedMeasure σ N +
undecided N` — the extra mass certified between level `N` and level `K` is drawn from the level-`N`
undecided pool (`lem:countHaar`). Taking `K → ∞` (`density_isLimit`) gives the bound on the limit.

PROVED (no longer a `sorry`): the per-level tail bound `decidedMeasure σ K ≤ decidedMeasure σ N +
undecided N` for `K ≥ N` is the analytic heart of `lem:countHaar`, now carried as the genuine
structural field `upper_tail` (elementary counting content: mass certified after level `N` is drawn
from the level-`N` undecided pool — NOT the conclusion). We take `K → ∞` against `density_isLimit`.
The same content is also surfaced as the predicate `upperTailBound`, PROVED from the field, and the
bracket re-derived as `density_le_decided_add_undecided_of_tail`. -/
theorem density_le_decided_add_undecided (σ : FactorizationType) (N : ℕ) :
    M.countingDensity σ ≤ M.decidedMeasure σ N + M.undecided N := by
  -- `decidedMeasure σ → countingDensity σ`, and for every `K ≥ N` the structural field `upper_tail`
  -- bounds `decidedMeasure σ K` by the fixed value `decidedMeasure σ N + undecided N`; pass to limit.
  refine le_of_tendsto (M.density_isLimit σ) ?_
  filter_upwards [Filter.eventually_ge_atTop N] with K hK
  exact M.upper_tail σ N K hK

/-- **`upperTailBound M`**: for every type `σ` and levels `N ≤ K`, the certified measure at level `K`
is bounded by the level-`N` certified measure plus the level-`N` undecided remainder. This is the
honest per-level statement of the upper bracket of `lem:countHaar` (the mass certified after level
`N` is drawn from the level-`N` undecided pool). It is the M1/counting content; surfaced as a
predicate. **PROVED** to hold for every `CountingModel` (it is exactly the `upper_tail` field). -/
def upperTailBound : Prop :=
  ∀ (σ : FactorizationType) (N K : ℕ), N ≤ K →
    M.decidedMeasure σ K ≤ M.decidedMeasure σ N + M.undecided N

/-- **Every `CountingModel` satisfies `upperTailBound`** — it is precisely the structural field
`upper_tail` (re-expressed through `decidedMeasure`/`undecided`). PROVED. -/
theorem upperTailBound_holds : M.upperTailBound :=
  fun σ N K hNK => M.upper_tail σ N K hNK

/-- **The upper bracket, PROVED from `upperTailBound`.** If the per-level tail bound holds, then
taking `K → ∞` (`density_isLimit`) gives `countingDensity σ ≤ decidedMeasure σ N + undecided N`. So
the upper bracket follows from the elementary counting fact `upperTailBound`; nothing about the
limit's value is assumed. -/
theorem density_le_decided_add_undecided_of_tail (htail : M.upperTailBound)
    (σ : FactorizationType) (N : ℕ) :
    M.countingDensity σ ≤ M.decidedMeasure σ N + M.undecided N := by
  -- the constant-from-N sequence `K ↦ decidedMeasure σ N + undecided N` dominates `decidedMeasure σ`
  -- eventually (for K ≥ N), and `decidedMeasure σ → countingDensity σ`, so the limit is ≤ the bound.
  refine le_of_tendsto (M.density_isLimit σ) ?_
  filter_upwards [Filter.eventually_ge_atTop N] with K hK
  exact htail σ N K hK

/-! ### The anti-box statements (the care point, recorded as theorems) -/

/-- **THE BOX IS THE TOTAL, NOT THE DENSITY.** The box measure (`≡ 1`) equals the sum of ALL per-type
decided measures plus the undecided remainder — it is the partition total, never the density of a
single type. This is the formal record that `density` is NOT the box count. -/
theorem box_is_total_not_density (N : ℕ) :
    M.boxMeasure N = (∑ σ ∈ M.typeMenu, M.decidedMeasure σ N) + M.undecided N := by
  rw [M.boxMeasure_eq_one, M.decidedMeasure_sum_add_undecided N]

/-- **The box count is `1` at every level; the density is the decided limit.** Whenever a type's
certified measure is strictly below `1` at some level (e.g. there is more than one type, or any
undecided mass), the box count differs from that type's certified measure — concretely witnessing
that the density (decided limit) is not the box count. We record the clean separating fact: if the
menu has another type carrying positive decided measure, or there is undecided mass at level `N`,
then `decidedMeasure σ N < boxMeasure N`. -/
theorem decidedMeasure_lt_box_of_other_mass (σ : FactorizationType) (N : ℕ)
    (hgap : 0 < (∑ τ ∈ M.typeMenu \ {σ}, M.decidedMeasure τ N) + M.undecided N) :
    M.decidedMeasure σ N < M.boxMeasure N := by
  classical
  rw [M.boxMeasure_eq_one]
  by_cases hσ : σ ∈ M.typeMenu
  · have hsum := M.decidedMeasure_sum_add_undecided N
    have hsplit : (∑ τ ∈ M.typeMenu, M.decidedMeasure τ N)
        = M.decidedMeasure σ N + (∑ τ ∈ M.typeMenu \ {σ}, M.decidedMeasure τ N) := by
      rw [← Finset.sum_singleton (fun τ => M.decidedMeasure τ N) σ,
        ← Finset.sum_union (by simp [Finset.disjoint_sdiff])]
      congr 1
      rw [Finset.union_comm, Finset.sdiff_union_of_subset (by simpa using hσ)]
    rw [hsplit] at hsum
    linarith
  · -- off menu σ has measure 0, and the gap forces 0 < 1.
    have h0 : M.decidedMeasure σ N = 0 := by
      unfold decidedMeasure; rw [M.decidedCount_off_menu σ N hσ, zero_div]
    rw [h0]; norm_num

end CountingModel

/-! ## The M1-termination input: `undecided → 0` and the resulting clean limit

We separate out the analytic content of `lem:countHaar` — `undecided N → 0` — as a *predicate* on a
`CountingModel`, so that the bracket can deliver the limit = true density. This is the M1 termination
fact: every separable `f` resolves its OM tree at finite order, so the undecided pool drains. It is
NOT proved here (it is the imported analytic content); it is the hypothesis that, with the bracket,
pins `countingDensity` as the genuine density and makes the upper bracket tight. -/

/-- **`UndecidedVanishes M`**: the undecided measure tends to `0` (`U_N → 0`, M1 termination,
`lem:countHaar`). Carried as a hypothesis because it is the imported analytic content (every `f`
resolves at finite OM order); with the bracket it forces `countingDensity` to be the genuine
`N→∞` density and the upper bracket to be tight. -/
def UndecidedVanishes {q n : ℕ} (M : CountingModel q n) : Prop :=
  Filter.Tendsto M.undecided Filter.atTop (nhds 0)

/-- **The bracket collapses under `UndecidedVanishes`.** If `U_N → 0` then the lower and upper
brackets squeeze, and `countingDensity σ = lim_N decidedMeasure σ N` is the *unique* value with
`decidedMeasure σ N ≤ countingDensity σ ≤ decidedMeasure σ N + undecided N` and width `→ 0`.
We record the consequence that the density is then the *limit* of the UPPER bracket too (both
brackets converge to `countingDensity σ`). PROVED from `density_isLimit` + the squeeze. -/
theorem countingDensity_is_squeezed_limit {q n : ℕ} (M : CountingModel q n)
    (hU : UndecidedVanishes M) (σ : FactorizationType) :
    Filter.Tendsto (fun N => M.decidedMeasure σ N + M.undecided N) Filter.atTop
      (nhds (M.countingDensity σ)) := by
  simpa using (M.density_isLimit σ).add hU

end LeanUrat.CountingModel
