/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H116
import Uniformity.ChapH.H117

/-!
# Uniformity.ChapH.H118 — the conservative verdict (S-1's CONSERVATIVE object)

**Chapter H, NODE H.118** [def] (`blueprint/CHAP-H_general_induction.md` §17.3 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §3.2's reader `read_cluster`
(`'U'` at DRAIN/CS, recurse at α, some-child at β, decided at DEC) and §4 sketch N3.1, sources
`EFF.GENIND.08` (the event grammar) and `EFF.GENIND.202` (the lexicographic repair measure).
First node of **N-3**, the conservative verdict / `RecursionLegs` layer.

`ClusterUndecided O π m N c` is the LEAST predicate on cluster states closed under the
conservative reader's four propagation rules:

* **DRAIN** — the constant coefficient is invisible in the window (H.108); the reader has no
  visible digit at the polygon's left endpoint and exits UNDECIDED at depth 0;
* **CS** — a composite-stage opening (H.110); DECISION D-H17.1 makes the reader PESSIMISTIC
  here and it exits UNDECIDED at depth 0 as well;
* **α** — a full-multiplicity child (H.111 (a)); the whole cluster recentres, and the state is
  undecided exactly when its sheared child at window `N − m k` is (H.115's `alphaChild`);
* **β** — fracture (H.111 (b)); the state is undecided when ANY of its children, read at its
  capped window `N − betaContent c k`, is (H.116's `betaChild`).

DEC states (H.111 (c)) are reached by no rule, so they are decided — that direction is the
inductive's INVERSION and lands at H.119 (`clusterUndecided_iff`), not here.

## ⚠ The S-1 fence (this repo's central discipline, at this node)

**This is the corpus's conservative complement `u_{m,d}`, NOT the semantic `undecidedSet`.**
The two are DIFFERENT objects and identifying them is REFUTED on F-2's witnesses: the reader
above quits at CS and at DRAIN without looking further, so it over-counts undecidedness by
construction.  Every consumer of `ClusterUndecided` inherits the fence; the one-way bridge to
the semantic object is H.123's, and it is an INEQUALITY.  No lemma in this file, and no lemma
downstream of it, may be read as a statement about `undecidedSet`.

## Why the definition needs no termination argument

`EFF.GENIND.202`'s lexicographic measure `(degree, window)` is what makes the *reader* — a
recursive FUNCTION — total, and it is the measure H.71's closure runs on.  The object defined
here is not that function but its undecided set, presented as an inductive family: Lean's
least-fixed-point semantics discharges the well-foundedness for free, and the four constructors
carry no recursion bookkeeping at all.  What the measure still buys us is stated and proved
below as two honest lemmas, both consumed downstream (H.120's truncation induction, H.121's
per-leg aggregation):

* `alphaChild_window_lt` — the α rule strictly descends the WINDOW (`N − m k < N`, since
  `1 ≤ k` is part of `HasChildAt` and a non-drain state has `1 ≤ N`, `1 ≤ m`);
* `betaChild_mult_lt` — the β rule strictly descends the DEGREE (`μ < m`: `μ ≤ m` is H.112's
  `mult_le_of_hasChildAt`, and `μ = m` is exactly what H.111 (b)'s fourth conjunct denies —
  a full-multiplicity child is the α case, not the β case).

Neither lemma is a side condition of the inductive; both are theorems about its constructors.

DEPENDS: H.108 (`IsDrainState`, `betaContent`), H.110 (`IsCSState`), H.111 (`IsAlphaState`,
`IsBetaState`), H.115 (`alphaChild`), H.116 (`betaChild`) · H.109 (`HasChildAt`) · H.112
(`mult_le_of_hasChildAt`, `one_le_window_of_not_drain`) for the two measure lemmas.

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `[IsAdicComplete (maximalIdeal O) O]` (β's
description-defined child needs it) + `π` explicit, every binder INLINE.  No
`[Finite (ResidueField O)]`: this node counts nothing — counting starts at H.119.

## TEETH (GC-8)

Battery `P1(e) recursion identity` of `verification/openmath/OM2_genindb_battery.py` (the
verdict recursion replayed exhaustively at every cell, both rings) is teeth for the
DEFINITION this node fixes; its EQUATIONS are H.119's teeth and are proved there.  The gate at
the end of this file runs the cheap, fully closed-form leg of that identity that this node's
constructor list already determines: at `m = 2` the CS bucket is empty (H.117) and the β bucket
is empty (a child has `μ ≥ 2` and `μ ≤ m = 2`, so every child is full-multiplicity, i.e. α), so
the reader's rule list collapses to DRAIN + α and the recursion must read
`u(W) = Q^(W−1) + Σ_k (Q−1) Q^(k·c(2)) u(W − 2k)`.  The gate checks that ChapG's landed closed
form `hex3R` satisfies exactly that equation, at both battery characteristics and every window
in range — a decorrelated check of the constructor list itself.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The conservative verdict -/

/-- **H.118.** The conservative reader's UNDECIDED set, as the least predicate closed under
the four propagation rules — DRAIN and CS exit undecided at depth 0 (DECISION D-H17.1,
pessimistic on stage data), α recurses at the sheared child (same degree, window `−mk`),
β propagates from ANY undecided child at its capped window.  Well-founded by the lexicographic
measure (degree, window) — `EFF.GENIND.202`'s repair, the same measure H.71's closure runs
on.  `DecidedAt`-side inversion: a state outside this predicate is DEC-resolved along its
whole recursion tree (H.119's iff).  **This is the conservative complement `u_{m,d}`, NOT the
semantic `undecidedSet` — identifying them is REFUTED on F-2's witnesses (the S-1 fence).** -/
inductive ClusterUndecided (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) :
    ∀ (m N : ℕ), ClusterState O m N → Prop
  | drain {m N : ℕ} (c : ClusterState O m N) :
      IsDrainState c → ClusterUndecided O π m N c
  | cs {m N : ℕ} (c : ClusterState O m N) :
      IsCSState π c → ClusterUndecided O π m N c
  | alpha {m N k : ℕ} {z : ResidueField O} (c : ClusterState O m N)
      (h : IsAlphaState π c k z) :
      ClusterUndecided O π m (N - m * k) (alphaChild π c h) → ClusterUndecided O π m N c
  | beta {m N μ k : ℕ} {z : ResidueField O} (c : ClusterState O m N)
      (hβ : IsBetaState π c) (h : HasChildAt π c μ k z) :
      ClusterUndecided O π μ (N - betaContent c k)
          (betaChild π c h (N - betaContent c k)) →
      ClusterUndecided O π m N c

/-! ## 2. The lexicographic measure, on the two recursive constructors

Not side conditions of the inductive (Lean needs none) — theorems about where its two
recursive rules can point.  They are what makes the H.120/H.121 inductions on a
`ClusterUndecided` derivation terminate in the ARITHMETIC, after `induction` has already
consumed the derivation itself. -/

/-- **The α rule strictly descends the window.**  `1 ≤ k` is a conjunct of `HasChildAt`
(H.109) and hence of `IsAlphaState`; `1 ≤ m` and `1 ≤ N` come from non-drainness (at `m = 0`
every state is a drain, H.108's `isDrainState_of_eq_zero`; at `N = 0` the truncation ring is
trivial, H.112's `one_le_window_of_not_drain`).  So `m * k ≥ 1` and the child window
`N − m k` is strictly below `N`. -/
theorem alphaChild_window_lt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N k : ℕ} {z : ResidueField O} {c : ClusterState O m N}
    (h : IsAlphaState π c k z) : N - m * k < N := by
  obtain ⟨h0, -, hchild⟩ := h
  obtain ⟨-, hk, -, -⟩ := hchild
  have hm : 1 ≤ m := by
    by_contra hm0
    exact h0 (isDrainState_of_eq_zero (by omega) c)
  have hN : 1 ≤ N := one_le_window_of_not_drain c h0
  have : 1 ≤ m * k := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

/-- **The β rule strictly descends the degree.**  `μ ≤ m` is H.112's `mult_le_of_hasChildAt`
(the event's non-divisible coefficient is nonzero, hence within the recentring's degree), and
`μ = m` is precisely what H.111 (b)'s fourth conjunct `¬ ∃ k z, HasChildAt π c m k z` denies:
a full-multiplicity child would make the state α, not β. -/
theorem betaChild_mult_lt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N μ k : ℕ} {z : ResidueField O} {c : ClusterState O m N}
    (hβ : IsBetaState π c) (h : HasChildAt π c μ k z) : μ < m := by
  have hle : μ ≤ m := mult_le_of_hasChildAt h
  rcases Nat.lt_or_ge μ m with hlt | hge
  · exact hlt
  · exact absurd ⟨k, z, (by rwa [le_antisymm hle hge] at h : HasChildAt π c m k z)⟩ hβ.2.2.2

/-- **The β child's window never grows.**  `betaContent` is a `ℕ`-valued infimum, so the capped
child window `N − betaContent c k` is at most `N`; on a non-drain state H.108's
`betaContent_le` makes it strictly smaller as soon as the content is positive, but the plain
bound is all the downstream inductions consult alongside `betaChild_mult_lt`. -/
theorem betaChild_window_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (c : ClusterState O m N) (k : ℕ) : N - betaContent c k ≤ N :=
  Nat.sub_le _ _

/-! ## 3. The two depth-0 exits, as named lemmas

The constructors, re-exported under the names the N-3 legs use.  `IsDecState` gets no such
lemma: it is NOT an entry point, and the statement that DEC states are decided is the
inversion, which needs `cases` on a derivation and therefore lands at H.119. -/

/-- Every DRAIN state is conservatively undecided (`ClusterUndecided.drain`). -/
theorem clusterUndecided_of_isDrainState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (π : O) {m N : ℕ}
    (c : ClusterState O m N) (h : IsDrainState c) : ClusterUndecided O π m N c :=
  ClusterUndecided.drain c h

/-- Every CS state is conservatively undecided — DECISION D-H17.1's pessimistic exit
(`ClusterUndecided.cs`).  At `2 ≤ m ≤ 3` this rule is VACUOUS: H.117's `isCSState_four_le`
empties the CS bucket below `m = 4`, which is why H.121/H.122 are stated there. -/
theorem clusterUndecided_of_isCSState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (π : O) {m N : ℕ}
    (c : ClusterState O m N) (h : IsCSState π c) : ClusterUndecided O π m N c :=
  ClusterUndecided.cs c h

/-- **The CS rule is vacuous at `2 ≤ m ≤ 3`** — H.117 (clause i) read at this node's
constructor list, in the form the H.121 split consumes: below `m = 4` no state enters the
verdict through `ClusterUndecided.cs`. -/
theorem not_isCSState_of_le_three {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 1 ≤ m)
    (hN : 1 ≤ N) (hm3 : m ≤ 3) (c : ClusterState O m N) : ¬ IsCSState π c :=
  not_isCSState_of_lt_four hπ hm hN (by omega) c

end Uniformity.Density.Induction

/-! ## 4. TEETH — the `m = 2` collapse of the constructor list

At `m = 2` the reader's four rules collapse to two.  CS is empty by H.117 (`4 ≤ m` on every CS
event).  β is empty for a reason internal to this node's own measure lemmas: `HasChildAt` forces
`2 ≤ μ` and `betaChild_mult_lt` would force `μ < 2`, so no β state has a child and H.111 (b)'s
third conjunct fails — every child at `m = 2` is full-multiplicity, i.e. α.  Hence the battery's
`P1(e) recursion identity` must read, at `m = 2`,

  `u(W) = Q ^ (W − 1) + Σ_{k ≥ 1, 2k ≤ W − 1} (Q − 1) · Q ^ (k · c(2)) · u(W − 2k)`,

with `c(2) = 1` and the drain count `Q ^ ((m−1)(W−1)) = Q ^ (W−1)` (battery `P1(b)`).  The gate
below checks that ChapG's landed closed form `hex3R` — the `m = 2` conservative complement,
reproduced here as `hexTwo` verbatim from `OM2_genindb_battery.py`'s `hex3R_ref` — satisfies
that equation at both battery characteristics and every window in range.  It is a decorrelated
check of THIS node's constructor list: a missing or spurious rule at `m = 2` breaks it.

⚠ S-1: `hex3R` is a CONSERVATIVE-family closed form.  Nothing here ties `ClusterUndecided` to
the semantic `undecidedCount`, and the tie must never be stated (finding F-2). -/

section NumericGate

/-- ChapG `hex3R` / the battery's `hex3R_ref`, verbatim: the `m = 2` conservative complement. -/
private def hexTwo (q M : ℕ) : ℕ :=
  if M = 0 then 0 else if M = 1 then 1
  else q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

/-- The realized α slopes at cluster size `m` and window `N` — the battery's own range
condition `1 ≤ k ∧ m * k ≤ N − 1` (H.112's `alpha_content`). -/
private def slopes (m N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ m * k ≤ N - 1)

/-- The right-hand side of the `m = 2` recursion this node's constructor list forces:
drain + the α sum (CS and β both empty). -/
private def rhsTwo (q W : ℕ) : ℕ :=
  q ^ (W - 1) + ((slopes 2 W).map fun k => (q - 1) * q ^ k * hexTwo q (W - 2 * k)).sum

-- the recursion identity at `m = 2`, both battery characteristics, every window `1 ≤ W ≤ 9`
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 10).filter fun W => decide (1 ≤ W)).all fun W => hexTwo q W == rhsTwo q W

-- the two largest `m = 2` cells of the battery's `part1` plan, on the nose
#guard (hexTwo 2 6, rhsTwo 2 6) == (64, 64)
#guard (hexTwo 3 4, rhsTwo 3 4) == (45, 45)

-- the boundary the α rule bottoms out on (`u(1) = 1`, H.119 (i)); no slope is realized there,
-- so the α sum is empty and the drain count `Q ^ 0` carries the whole value
#guard ([2, 3] : List ℕ).all fun q => (slopes 2 1 == []) && (hexTwo q 1 == 1)

-- `betaChild_mult_lt` in numerals: no `μ` is simultaneously `≥ 2` (a child) and `< 2` (a β
-- child at `m = 2`), so the β bucket is empty exactly where the gate assumes it
#guard (List.range 6).all fun μ => !(decide (2 ≤ μ) && decide (μ < 2))

end NumericGate

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.ClusterUndecided
#print axioms Uniformity.Density.Induction.alphaChild_window_lt
#print axioms Uniformity.Density.Induction.betaChild_mult_lt
#print axioms Uniformity.Density.Induction.betaChild_window_le
#print axioms Uniformity.Density.Induction.clusterUndecided_of_isDrainState
#print axioms Uniformity.Density.Induction.clusterUndecided_of_isCSState
#print axioms Uniformity.Density.Induction.not_isCSState_of_le_three

end AxCheck
