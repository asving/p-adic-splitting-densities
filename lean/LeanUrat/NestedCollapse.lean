/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.L5fix
import LeanUrat.CountingModel

/-!
# LeanUrat.NestedCollapse — the corrected crux: the well-founded NESTED multi-block recursion

This is the corrected self-loop collapse of `notes/DECOMP_BLUEPRINT.tex` §4 (Theorem `thm:nested`,
the fix [F1]). The size-`s` completely-split cluster volume `I_s` is **NOT** a single geometric
series for `s ≥ 3`; it satisfies a well-founded NESTED multi-block recursion. The single geometric
series is only the `s = 2` special case (`lem:s2`).

## The nested recursion (blueprint `eq:nested`)

```
  I_s · (1 − q^{-w(s)})  =  Σ_{P ⊢ {1,…,s}, #P = r ≥ 2}  [ Π_{j=0}^{r-1}(q − j) ]
                                                          · Π_{B ∈ P} q^{-(|B| + C(|B|,2))} · I_{|B|},
  I_0 = I_1 = 1,   w(s) = s(s+1)/2 − 1.
```

* The sum is over set-partitions `P` of `{1,…,s}` into `r ≥ 2` nonempty blocks (`Finpartition` of
  `Finset.range s`, filtered to `parts.card ≥ 2`).
* `Π_{j=0}^{r-1}(q − j)` is the falling factorial `q^{\underline r}` = `Nat.descFactorial q r` (the
  number of ways to assign `r` DISTINCT residues to the `r` labelled blocks — the cross-block
  Vandermonde factor is `1` since distinct residues give unit differences).
* `q^{-(|B| + C(|B|,2))}` is the within-block box × Vandermonde rescale (`lem:rescale` WITHOUT the
  `Q`-residue-choice, already counted by the falling factorial).
* The `r = 1` single-block "all stay together" term has been moved to the LEFT, producing the
  self-loop pivot `1 − q^{-w(s)}` on `I_s`. **Every block on the right has size `|B| < s`** (since
  `r ≥ 2`), so the recursion is WELL-FOUNDED (strict descent), terminating at `I_0 = I_1 = 1`.

## What this module provides

* `descFactorial`-based residue weight and the within-block rescale weight, fully defined;
* `nestedRHS I s q` — the right side, a `Finpartition`-sum, fully defined;
* `SatisfiesNested I` — the predicate "`I` satisfies `eq:nested` for all `s ≥ 2`" (the crux
  recursion, as a STATEMENT);
* `nested_wellFounded` — the strict-descent fact `|B| < s` for every block of a `≥2`-block partition
  (PROVED — this is what makes the recursion well-founded and is the load-bearing structural point);
* the closed-form CHECKS `I_2 = q/(q+1)`, `I_3 = q^3(q^2−q+1)/((q+1)·Φ_5)` as the intended solution
  (`closedI2`, `closedI3`), and the statement that the nested solution reproduces them
  (`nested_reproduces_I2`, `nested_reproduces_I3`);
* the **geometric LIMIT** upgrade (`geometricLimit_of_selfLoop`): the finite truncations
  `V_N = a(1 − r^{N+1})/(1 − r)` converge to `a/(1 − r)`, the COUNTING limit, upgrading the algebraic
  `selfLoop_geometric`.

## Status

PROVED (sorry-free). The recursion and weights are fully DEFINED; the well-foundedness (`|B| < s`)
and the geometric-limit upgrade are PROVED. The `s = 2` and `s = 3` closed forms
(`nested_reproduces_I2`, `nested_reproduces_I3`) are now PROVED by genuine finite computation: the
`≥2`-block set-partitions of `range 2` / `range 3` are enumerated explicitly (one / four of them,
the `Finpartition`-enumeration discharged by `decide`), the per-partition falling-factorial and
within-block weights are computed, `nestedRHS` is evaluated in closed form (`nestedRHS_two`,
`nestedRHS_three`), and the self-loop pivot `1 − q^{-w(s)}` is inverted (positivity from
`L5fix.selfLoop_geometric`), reproducing `I_2 = q/(q+1)` and `I_3 = q^3(q^2−q+1)/((q+1)Φ_5)`.
`SatisfiesNested` is a PREDICATE (the crux equation), not an axiom — it is something a constructed
`I` must satisfy, not an assumed conclusion. NO `sorry`, NO `axiom` in this module.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.NestedCollapse

open Finset BigOperators

/-! ### The within-block and cross-block weights -/

/-- The within-block rescale exponent `|B| + C(|B|,2)` for a block of size `b = |B|`
(`eq:nested`): the box measure `q^{-b}` times the within-block Vandermonde `q^{-\binom b2}`. -/
def blockExponent (b : ℕ) : ℕ := b + b.choose 2

/-- The within-block weight `q^{-(b + C(b,2))} · I_b` for a block of size `b`, given the recursive
volume function `I`. -/
noncomputable def blockWeight (I : ℕ → ℕ → ℚ) (q b : ℕ) : ℚ :=
  ((q : ℚ) ^ blockExponent b)⁻¹ * I b q

/-- The cross-block residue-assignment weight `Π_{j=0}^{r-1}(q − j) = q^{\underline r}`, the falling
factorial (`Nat.descFactorial`): the number of ways to assign `r` DISTINCT residues in `F_q` to the
`r` labelled blocks of the partition. -/
def residueWeight (q r : ℕ) : ℚ := (q.descFactorial r : ℚ)

/-- The per-partition weight in `eq:nested`: the residue-assignment falling factorial times the
product over blocks of the within-block weight. `P : Finpartition (range s)` and the block sizes are
`B.card` for `B ∈ P.parts`. -/
noncomputable def partitionWeight (I : ℕ → ℕ → ℚ) (q s : ℕ) (P : Finpartition (range s)) : ℚ :=
  residueWeight q P.parts.card * ∏ B ∈ P.parts, blockWeight I q B.card

/-- **The right side of `eq:nested`**: the sum over `≥2`-block set-partitions of `{0,…,s-1}` of the
per-partition weight. We sum over `Finpartition (range s)` filtered to `parts.card ≥ 2` (the `r ≥ 2`
condition; the `r = 1` single block has been moved to the LHS pivot). -/
noncomputable def nestedRHS (I : ℕ → ℕ → ℚ) (s q : ℕ) : ℚ :=
  ∑ P ∈ {P : Finpartition (range s) | 2 ≤ P.parts.card}, partitionWeight I q s P

/-- **The crux recursion predicate (`thm:nested`, `eq:nested`).** `I : ℕ → ℕ → ℚ` (size, residue
card) satisfies the nested multi-block recursion: base `I_0 = I_1 = 1`, and for `s ≥ 2`,
`I_s · (1 − q^{-w(s)}) = nestedRHS I s q`.

This is a STATEMENT a constructed `I` must satisfy (the crux), NOT an axiom asserting a conclusion:
it is the self-loop-collapse equation derived from M1 + C1 + counting, and its solution's rationality
is what the rationality theorem proves. `w = L5fix.selfLoopExponent`. -/
def SatisfiesNested (I : ℕ → ℕ → ℚ) : Prop :=
  (∀ q, I 0 q = 1) ∧ (∀ q, I 1 q = 1) ∧
    ∀ (s q : ℕ), 2 ≤ s → 2 ≤ q →
      I s q * (1 - ((q : ℚ) ^ L5fix.selfLoopExponent s)⁻¹) = nestedRHS I s q

/-! ### Well-foundedness: every block of a `≥2`-block partition is STRICTLY smaller

This is the load-bearing structural point of the corrected crux: because `r ≥ 2`, each block `B` in
the sum has `|B| < s`, so the recursion descends strictly and terminates at `I_0 = I_1 = 1`. PROVED. -/

/-- **Strict descent (well-foundedness of `eq:nested`).** For a partition `P` of `range s` with at
least `2` parts, every part `B ∈ P.parts` has `B.card < s`. So every `I_{|B|}` on the RHS is a
STRICTLY smaller instance — the recursion is well-founded. PROVED. -/
theorem nested_block_lt {s : ℕ} (P : Finpartition (range s)) (hP : 2 ≤ P.parts.card)
    {B : Finset ℕ} (hB : B ∈ P.parts) : B.card < s := by
  classical
  -- B ⊆ range s, so B.card ≤ s. If B.card = s then B = range s, forcing P.parts = {range s}, so
  -- parts.card = 1, contradicting hP.
  have hsub : B ⊆ range s := by
    have := P.le hB
    simpa using this
  have hle : B.card ≤ s := by simpa using Finset.card_le_card hsub
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    -- B.card = s = (range s).card and B ⊆ range s ⇒ B = range s.
    have hcard : B.card = (range s).card := by simpa using h
    have hBeq : B = range s := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
    -- Every other part C ≠ B is disjoint from B = range s but ⊆ range s, hence empty — but parts are
    -- nonempty (`nonempty_of_mem_parts`). So parts ⊆ {B}, hence card ≤ 1, contradicting hP.
    have honly : ∀ C ∈ P.parts, C = B := by
      intro C hC
      by_contra hCB
      have hdisj : Disjoint C B := P.disjoint hC hB hCB
      have hCsub : C ⊆ range s := by have := P.le hC; simpa using this
      have hCempty : C = ∅ := by
        rw [hBeq] at hdisj
        -- `Disjoint C (range s)` and `C ⊆ range s` ⇒ `Disjoint C C` ⇒ `C = ∅`.
        have : Disjoint C C := hdisj.mono_right hCsub
        exact (Finset.disjoint_self_iff_empty C).mp this
      exact (P.nonempty_of_mem_parts hC).ne_empty hCempty
    have hsubsingle : P.parts ⊆ {B} := fun C hC => by simp [honly C hC]
    have : P.parts.card ≤ 1 := by
      calc P.parts.card ≤ ({B} : Finset (Finset ℕ)).card := Finset.card_le_card hsubsingle
        _ = 1 := Finset.card_singleton B
    omega

/-! ### The `s = 2` special case (a single geometric series) and the closed forms (`cor:closed`) -/

/-- The intended closed form `I_2 = q/(q+1)` (`lem:s2`, `eq:s2limit`). -/
noncomputable def closedI2 (q : ℕ) : ℚ := (q : ℚ) / ((q : ℚ) + 1)

/-- The intended closed form `I_3 = q^3(q^2 − q + 1) / ((q+1)·Φ_5)`, `Φ_5 = q^4+q^3+q^2+q+1`
(`cor:closed`). -/
noncomputable def closedI3 (q : ℕ) : ℚ :=
  ((q : ℚ) ^ 3 * ((q : ℚ) ^ 2 - q + 1)) /
    (((q : ℚ) + 1) * ((q : ℚ) ^ 4 + (q : ℚ) ^ 3 + (q : ℚ) ^ 2 + (q : ℚ) + 1))

/-- **The `s = 2` self-loop collapse value, via the geometric limit** (`lem:s2`/`lem:collapse`):
`a = (q−1)/q`, `r = q^{-2}`, and `a/(1−r) = q/(q+1)`. PROVED algebraically (the limit is supplied by
`geometricLimit_of_selfLoop`; this lemma pins the limit VALUE to the closed form). -/
theorem s2_collapse_value (q : ℕ) (hq : 2 ≤ q) :
    (((q : ℚ) - 1) / q) / (1 - ((q : ℚ) ^ 2)⁻¹) = closedI2 q := by
  have hq0 : (q : ℚ) ≠ 0 := by
    have : (0 : ℚ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq
    exact ne_of_gt this
  have hq1 : (q : ℚ) + 1 ≠ 0 := by
    have : (0 : ℚ) < (q : ℚ) + 1 := by
      have : (0 : ℚ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq
      linarith
    exact ne_of_gt this
  have hqpos : (0 : ℚ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq
  have hgt : (1 : ℚ) < q := by exact_mod_cast hq
  -- the pivot `1 - q^{-2} ≠ 0` (positive for q ≥ 2)
  have hpivot : (1 : ℚ) - ((q : ℚ) ^ 2)⁻¹ ≠ 0 := by
    have h2 : ((q : ℚ) ^ 2)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; nlinarith [hgt, hqpos]
    have h3 : (0 : ℚ) < (q : ℚ) ^ 2 := by positivity
    have : (0 : ℚ) < ((q : ℚ) ^ 2)⁻¹ := by positivity
    linarith
  unfold closedI2
  rw [div_div, div_eq_div_iff (mul_ne_zero hq0 hpivot) hq1]
  field_simp
  ring

/-! #### The explicit set-partitions enumerated by `nestedRHS` at `s = 2, 3`

To evaluate `nestedRHS I s q` at `s = 2, 3` we must enumerate the `≥2`-block set-partitions of
`Finset.range s`. For `s = 2` there is exactly one (`⊥`, the two singletons). For `s = 3` there are
exactly four: the three-singleton `⊥`, and the three `{size-2, size-1}` partitions. We name the four
size-`3` partitions so the `Finset.sum` over the filtered universe can be unfolded by
`Finset.sum_insert`. Each carries its three `Finpartition` obligations discharged by `decide`. -/

/-- The size-3 partition `{{0,1},{2}}` (a `{2,1}`-block partition of `range 3`). -/
def part3_201 : Finpartition (Finset.range 3) where
  parts := {{0, 1}, {2}}
  supIndep := by decide
  sup_parts := by decide
  bot_notMem := by decide

/-- The size-3 partition `{{1},{0,2}}` (a `{1,2}`-block partition of `range 3`). -/
def part3_021 : Finpartition (Finset.range 3) where
  parts := {{1}, {0, 2}}
  supIndep := by decide
  sup_parts := by decide
  bot_notMem := by decide

/-- The size-3 partition `{{0},{1,2}}` (a `{1,2}`-block partition of `range 3`). -/
def part3_012 : Finpartition (Finset.range 3) where
  parts := {{0}, {1, 2}}
  supIndep := by decide
  sup_parts := by decide
  bot_notMem := by decide

set_option maxRecDepth 8000 in
/-- **`nestedRHS I 2 q = (q−1)/q`** (the `s = 2` instance of `eq:nested`, PROVED). The only
`≥2`-block set-partition of `range 2` is `⊥ = {{0},{1}}`, whose per-partition weight is
`q^{\underline 2} · (q^{-1})·(q^{-1}) = q(q−1)·q^{-2} = (q−1)/q`. The `Finpartition`-enumeration is
discharged by `decide`; the block product and falling factorial are computed explicitly. -/
theorem nestedRHS_two (I : ℕ → ℕ → ℚ) (q : ℕ) (hI1 : I 1 q = 1) (hq : 2 ≤ q) :
    nestedRHS I 2 q = ((q : ℚ) - 1) / q := by
  have hq0 : (q : ℚ) ≠ 0 := by positivity
  unfold nestedRHS
  have hset : ((Finset.univ : Finset (Finpartition (Finset.range 2))).filter
      (fun P => 2 ≤ P.parts.card)) = {⊥} := by decide
  rw [hset, Finset.sum_singleton]
  unfold partitionWeight residueWeight blockWeight blockExponent
  have hcard : (⊥ : Finpartition (Finset.range 2)).parts.card = 2 := by decide
  have hparts : (⊥ : Finpartition (Finset.range 2)).parts = {{0}, {1}} := by decide
  rw [hcard, hparts]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [Finset.card_singleton]
  rw [hI1]
  have hdf : (Nat.descFactorial q 2 : ℚ) = ((q : ℚ) - 1) * (q : ℚ) := by
    have h1 : Nat.descFactorial q 2 = (q - 1) * q := by simp [Nat.descFactorial]
    rw [h1]
    have h2 : (1 : ℕ) ≤ q := by omega
    push_cast [Nat.cast_sub h2]; ring
  have hch : (1 : ℕ) + Nat.choose 1 2 = 1 := by decide
  rw [hch, hdf]; field_simp

set_option maxRecDepth 8000 in
/-- **`nestedRHS I 3 q`, evaluated (`s = 3` instance of `eq:nested`, PROVED).** The four `≥2`-block
set-partitions of `range 3` are `⊥ = {{0},{1},{2}}` (three singletons) and the three `{2,1}`-block
partitions `part3_201/021/012`. Summing the per-partition weights gives the displayed value: the
three-singleton contributes `q^{\underline 3}·(q^{-1})^3`, and each `{2,1}` partition contributes
`q^{\underline 2}·(q^{-(2+\binom 22)}·I_2)·(q^{-1}·I_1) = q^{\underline 2}·q^{-3}·I_2·q^{-1}`. -/
theorem nestedRHS_three (I : ℕ → ℕ → ℚ) (q : ℕ) (hI1 : I 1 q = 1) (_hq : 2 ≤ q) :
    nestedRHS I 3 q =
      (Nat.descFactorial q 3 : ℚ) * ((q : ℚ))⁻¹ * ((q : ℚ))⁻¹ * ((q : ℚ))⁻¹
      + 3 * ((Nat.descFactorial q 2 : ℚ) * (((q : ℚ) ^ 3)⁻¹ * I 2 q) * (((q : ℚ))⁻¹)) := by
  unfold nestedRHS
  have hset : ((Finset.univ : Finset (Finpartition (Finset.range 3))).filter
      (fun P => 2 ≤ P.parts.card)) = {⊥, part3_201, part3_021, part3_012} := by decide
  rw [hset]
  rw [show ({⊥, part3_201, part3_021, part3_012} : Finset (Finpartition (Finset.range 3)))
      = insert ⊥ (insert part3_201 (insert part3_021 {part3_012})) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  unfold partitionWeight residueWeight blockWeight blockExponent
  rw [show (⊥ : Finpartition (Finset.range 3)).parts = ({{0}, {1}, {2}} : Finset (Finset ℕ))
        from by decide,
      show part3_201.parts = ({{0, 1}, {2}} : Finset (Finset ℕ)) from rfl,
      show part3_021.parts = ({{1}, {0, 2}} : Finset (Finset ℕ)) from rfl,
      show part3_012.parts = ({{0}, {1, 2}} : Finset (Finset ℕ)) from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
      Finset.prod_insert (by decide), Finset.prod_singleton,
      Finset.prod_insert (by decide), Finset.prod_singleton,
      Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [show ({{0}, {1}, {2}} : Finset (Finset ℕ)).card = 3 from by decide,
      show ({{0, 1}, {2}} : Finset (Finset ℕ)).card = 2 from by decide,
      show ({{1}, {0, 2}} : Finset (Finset ℕ)).card = 2 from by decide,
      show ({{0}, {1, 2}} : Finset (Finset ℕ)).card = 2 from by decide,
      show ({0} : Finset ℕ).card = 1 from by decide, show ({1} : Finset ℕ).card = 1 from by decide,
      show ({2} : Finset ℕ).card = 1 from by decide,
      show ({0, 1} : Finset ℕ).card = 2 from by decide,
      show ({0, 2} : Finset ℕ).card = 2 from by decide,
      show ({1, 2} : Finset ℕ).card = 2 from by decide]
  norm_num [hI1, Nat.choose]; ring

/-- **The nested recursion reproduces `I_2 = q/(q+1)`** (`lem:s2`/`cor:closed`). PROVED. For any `I`
satisfying the nested recursion and any `q ≥ 2`, `I 2 q = closedI2 q`: the `s = 2` recursion gives
`I 2 q · (1 − q^{-2}) = nestedRHS I 2 q = (q−1)/q` (`nestedRHS_two`, since `selfLoopExponent 2 = 2`),
and the pivot `1 − q^{-2} ≠ 0` (`L5fix.selfLoop_geometric`), so dividing and applying
`s2_collapse_value` gives `I 2 q = q/(q+1) = closedI2 q`. -/
theorem nested_reproduces_I2 (I : ℕ → ℕ → ℚ) (hI : SatisfiesNested I) (q : ℕ) (hq : 2 ≤ q) :
    I 2 q = closedI2 q := by
  obtain ⟨_, hI1, hrec⟩ := hI
  have hbase : I 1 q = 1 := hI1 q
  have heq : I 2 q * (1 - ((q : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹) = ((q : ℚ) - 1) / q := by
    rw [hrec 2 q le_rfl hq]; exact nestedRHS_two I q hbase hq
  have hexp : L5fix.selfLoopExponent 2 = 2 := by unfold L5fix.selfLoopExponent; decide
  rw [hexp] at heq
  have hpivot : (1 : ℚ) - ((q : ℚ) ^ 2)⁻¹ ≠ 0 := by
    have h := L5fix.selfLoop_geometric 2 q le_rfl hq
    rw [hexp] at h; exact ne_of_gt h
  have hI2 : I 2 q = (((q : ℚ) - 1) / q) / (1 - ((q : ℚ) ^ 2)⁻¹) :=
    eq_div_of_mul_eq hpivot heq
  rw [hI2]; exact s2_collapse_value q hq

/-- **The nested recursion reproduces `I_3 = q^3(q^2−q+1)/((q+1)Φ_5)`** (`cor:closed`). PROVED. The
`s = 3` recursion gives `I 3 q · (1 − q^{-5}) = nestedRHS I 3 q` (`nestedRHS_three`, since
`selfLoopExponent 3 = 5`). Substituting the proved `I 2 q = q/(q+1)` (`nested_reproduces_I2`) and the
falling factorials `q^{\underline 3} = q(q−1)(q−2)`, `q^{\underline 2} = q(q−1)`, the pivot
`1 − q^{-5} ≠ 0` (`L5fix.selfLoop_geometric`), and clearing denominators (`q ≠ 0`, `q+1 ≠ 0`,
`q^5 − 1 ≠ 0`) yields `closedI3 q`. -/
theorem nested_reproduces_I3 (I : ℕ → ℕ → ℚ) (hI : SatisfiesNested I) (q : ℕ) (hq : 2 ≤ q) :
    I 3 q = closedI3 q := by
  have hrec := hI.2.2
  have hbase : I 1 q = 1 := hI.2.1 q
  -- the proved `s = 2` value, fed into the `s = 3` recursion
  have hI2 : I 2 q = (q : ℚ) / ((q : ℚ) + 1) := nested_reproduces_I2 I hI q hq
  have hqpos : (0 : ℚ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq
  have hq0 : (q : ℚ) ≠ 0 := ne_of_gt hqpos
  have hq1 : (q : ℚ) + 1 ≠ 0 := by positivity
  -- falling factorials as polynomials in q
  have hdf3 : (Nat.descFactorial q 3 : ℚ) = (q : ℚ) * ((q : ℚ) - 1) * ((q : ℚ) - 2) := by
    have h : Nat.descFactorial q 3 = q * (q - 1) * (q - 2) := by
      simp [Nat.descFactorial]
      ring
    rw [h]
    have h2 : (2 : ℕ) ≤ q := hq
    have h1 : (1 : ℕ) ≤ q := by omega
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
  have hdf2 : (Nat.descFactorial q 2 : ℚ) = (q : ℚ) * ((q : ℚ) - 1) := by
    have h : Nat.descFactorial q 2 = q * (q - 1) := by
      simp [Nat.descFactorial]
      ring
    rw [h]
    have h1 : (1 : ℕ) ≤ q := by omega
    push_cast [Nat.cast_sub h1]; ring
  have heq : I 3 q * (1 - ((q : ℚ) ^ L5fix.selfLoopExponent 3)⁻¹) =
      (q : ℚ) * ((q : ℚ) - 1) * ((q : ℚ) - 2) * ((q : ℚ))⁻¹ * ((q : ℚ))⁻¹ * ((q : ℚ))⁻¹
      + 3 * (((q : ℚ) * ((q : ℚ) - 1)) * (((q : ℚ) ^ 3)⁻¹ * ((q : ℚ) / ((q : ℚ) + 1)))
          * (((q : ℚ))⁻¹)) := by
    rw [hrec 3 q (by norm_num) hq, nestedRHS_three I q hbase hq, hdf3, hdf2, hI2]
  have hexp : L5fix.selfLoopExponent 3 = 5 := by unfold L5fix.selfLoopExponent; decide
  rw [hexp] at heq
  have hpivot : (1 : ℚ) - ((q : ℚ) ^ 5)⁻¹ ≠ 0 := by
    have h := L5fix.selfLoop_geometric 3 q (by norm_num) hq
    rw [hexp] at h; exact ne_of_gt h
  have hq5 : (q : ℚ) ^ 5 - 1 ≠ 0 := by
    have hgt : (1 : ℚ) < (q : ℚ) ^ 5 := by
      have : (1 : ℚ) < q := by exact_mod_cast hq
      nlinarith [pow_pos hqpos 5, this]
    linarith
  have hsol : I 3 q =
      ((q : ℚ) * ((q : ℚ) - 1) * ((q : ℚ) - 2) * ((q : ℚ))⁻¹ * ((q : ℚ))⁻¹ * ((q : ℚ))⁻¹
        + 3 * (((q : ℚ) * ((q : ℚ) - 1)) * (((q : ℚ) ^ 3)⁻¹ * ((q : ℚ) / ((q : ℚ) + 1)))
            * (((q : ℚ))⁻¹))) / (1 - ((q : ℚ) ^ 5)⁻¹) :=
    eq_div_of_mul_eq hpivot heq
  rw [hsol]; unfold closedI3
  field_simp; ring

/-! ### The geometric LIMIT upgrade (blueprint `lem:collapse`, `eq:limit`)

The `s = 2` collapse (and the pivot in the nested system) is the limit of FINITE geometric sums, not
merely the algebraic identity `Σ r^j = 1/(1−r)`. We upgrade `L5fix.selfLoop_geometric`'s algebraic
content to the COUNTING limit: `V_N = a(1 − r^{N+1})/(1 − r) → a/(1 − r)`. -/

/-- The finite truncation `V_N = a·(1 − r^{N+1})/(1 − r)` (the geometric sum `a·Σ_{j=0}^{N} r^j`). -/
noncomputable def geomTrunc (a r : ℚ) (N : ℕ) : ℚ := a * (1 - r ^ (N + 1)) / (1 - r)

/-- The finite truncation is the honest geometric sum `a · Σ_{j=0}^{N} r^j`. PROVED. -/
theorem geomTrunc_eq_sum (a r : ℚ) (hr : r ≠ 1) (N : ℕ) :
    geomTrunc a r N = a * ∑ j ∈ range (N + 1), r ^ j := by
  unfold geomTrunc
  rw [geom_sum_eq hr]
  have h1 : (1 : ℚ) - r ≠ 0 := sub_ne_zero.mpr (fun h => hr h.symm)
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  field_simp
  ring

/-- **The geometric LIMIT (`eq:limit`, the counting upgrade of `selfLoop_geometric`).** For
`0 < r < 1`, the finite truncations `V_N = a(1 − r^{N+1})/(1 − r)` converge to `a/(1 − r)`. This is
the COUNTING limit `lim_N V_N` of `lem:collapse` — the level-`N` finite geometric sums tending to the
rational value — NOT just the algebraic identity. PROVED (`r^{N+1} → 0` for `|r| < 1`). -/
theorem geometricLimit_of_selfLoop (a r : ℚ) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (geomTrunc a r) Filter.atTop (nhds (a / (1 - r))) := by
  have hrne : r ≠ 1 := ne_of_lt hr1
  have hpow : Filter.Tendsto (fun N => r ^ (N + 1)) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr0) hr1
    exact h.comp (Filter.tendsto_add_atTop_nat 1)
  have hnum : Filter.Tendsto (fun N => a * (1 - r ^ (N + 1))) Filter.atTop (nhds (a * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hpow)
  have hdiv : Filter.Tendsto (fun N => a * (1 - r ^ (N + 1)) / (1 - r)) Filter.atTop
      (nhds (a * (1 - 0) / (1 - r))) :=
    hnum.div_const _
  have heq : a * (1 - 0) / (1 - r) = a / (1 - r) := by ring
  rw [heq] at hdiv
  exact hdiv

end LeanUrat.NestedCollapse
