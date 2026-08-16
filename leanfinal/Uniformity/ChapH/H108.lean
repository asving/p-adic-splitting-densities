/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H106
import Uniformity.ChapH.H107

/-!
# Uniformity.ChapH.H108 — the drain predicate and the capped slope content

**Chapter H, NODE H.108** (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1 completion
layer, dated extension 2026-08-16; provenance OM-2 §3.2 `N-2c`'s window display, source
`EFF.GENIND.24`).  Third node of **N-2**, the cluster event grammar over `O`.

Two definitions and one lemma, all about a single cluster state `c : ClusterState O m N`
(H.106) read through the windowed valuation `resOrd` (H.107):

* **(a) `IsDrainState c`** — the constant coefficient is INVISIBLE in the window
  (`c.1 ⟨0, _⟩ = 0`, equivalently `resOrd (c.1 ⟨0, _⟩) = N` by H.107 clause (ii)).  On such a
  state the conservative S-1 reader exits UNDECIDED at depth `0`: it refuses to consult digits
  below the window, so it cannot see the Newton polygon at all.
* **(b) `betaContent c k`** — the **CAPPED** slope-`k` content
  `D = min_{j ≤ m} (min (v (a j)) N + j * k)`, with the monic top `j = m` contributing `m * k`.
  This is `GENIND-3`'s terminal `[r3]`-capped display, computed on the CLASS: `resOrd` is
  already the capped valuation, so no lift is consulted anywhere.
* **lemma half `betaContent_le`** — on a NON-drain state `D ≤ N − 1`.  Equivalently (corollary
  `one_le_window_of_not_isDrainState`) every extracted child window `N − D` is `≥ 1`: the
  window-positivity rider that the three-layer correction history recorded at `EFF.GENIND.24`
  earned (sealed uncapped → capped → regime inventory).

The mechanism is a one-term `Finset.inf'_le`: the `j = 0` term of the infimum is
`resOrd (c.1 ⟨0, _⟩) + 0 * k = resOrd (c.1 ⟨0, _⟩)`, and non-drain forces that to be `< N`.

**The `m = 0` convention.**  `IsDrainState` is stated in `∀ h : 0 < m` form, so the degenerate
`m = 0` state is VACUOUSLY a drain (`isDrainState_of_eq_zero`) and `betaContent_le` never fires
there — which is why the lemma half also carries `1 ≤ m`.  Every consumer in §17 has `m ≥ 2`
(the cluster grammar's own scope), so the convention costs nothing; it is recorded here because
the ∀-form is what makes `IsDrainState` a hypothesis-free predicate on `ClusterState O m N`.

DEPENDS: H.106 (`ClusterState`), H.107 (`resOrd`, `resOrd_le`, `resOrd_eq_iff`) · mathlib
`Finset.inf'_le`, `Finset.nonempty_range_iff`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0), binders INLINE (the B.42 completeness-binder
rule): `[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]` and nothing else.  No `Finite`
(no counting happens at this node), no `IsAdicComplete` (no Hensel), no irreducible `π` (the
content is read off the class, never off a uniformizer).

## TEETH (GC-8)

`verification/openmath/OM2_genindb_battery.py` computes exactly this content, at every child
extraction of every PART-1 cell, both rings:

```python
    D = min(RB.val(x) for x in c)
    # the capped-window content identity (GENIND-3 [r3] display):
    Dpred = min(min(RB.val(a[j]), W) + j * k if j < m else j * k for j in range(m + 1))
```

The reader `_read_cluster_work` then asserts three things about it, on every state it visits, so
the blueprint's named PART-1 checks (**`P1(e)` recursion identity**, **`P1(f)` beta genre
composition**) all consume them: `assert D == Dpred` on the BETA branch (the content identity —
the reader's uncapped `min` over the recentred coefficients agrees with the class-computable
`Dpred`), `assert M >= 1` for `M = W - D` (the child window is non-degenerate — this IS
`betaContent_le`), and on the ALPHA branch `assert D == m * k and Dpred == m * k`.

`Dpred`'s displayed formula is `betaContent`'s body verbatim under `resOrd = min ∘ (val, W)`
(H.107's `resOrd_ge_iff` is that identification).  GC-8 disposition: **Lean theorems** for the
two class-level assertions — `betaContent_le` (the `M ≥ 1` guarantee) and the ALPHA identity's
`Dpred == m * k` half, recorded as the `example` of §4; the remaining `D == Dpred` half is a
statement about the recentred expansion, i.e. H.109's business, not this node's.  Plus a kernel
`#guard` block in §5 that re-runs both proved assertions exhaustively over the
capped-valuation grids of the battery's own `part1` shapes (`m ∈ {2, 3, 4}`) — a genuine
re-execution of the lemma's content, `q` playing no role in this pure-valuation arithmetic.
The ring-level enumeration stays the executable regression.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The drain predicate -/

/-- **H.108 (def half, a). DRAIN.** The constant coefficient of the cluster state is invisible
in the window.  The conservative S-1 reader exits UNDECIDED here: it decides on visible digits
only, and a drain state shows it none at the polygon's left endpoint.

Stated in `∀ h : 0 < m` form so that it is a predicate on `ClusterState O m N` with no side
hypothesis; `m = 0` is vacuously a drain (`isDrainState_of_eq_zero`). -/
def IsDrainState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ∀ h : 0 < m, c.1 ⟨0, h⟩ = 0

/-- At `0 < m` the ∀-form collapses to the single equation it is about (proof irrelevance in
the `Fin` index). -/
theorem isDrainState_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (hm : 0 < m) (c : ClusterState O m N) :
    IsDrainState c ↔ c.1 ⟨0, hm⟩ = 0 :=
  ⟨fun h => h hm, fun h _ => h⟩

/-- The degenerate convention, recorded: at `m = 0` every state is vacuously a drain. -/
theorem isDrainState_of_eq_zero {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m N : ℕ} (hm : m = 0) (c : ClusterState O m N) :
    IsDrainState c := by
  intro h
  omega

/-- The battery's own drain test, in Lean: `vals[0] >= W` is `resOrd (c 0) = N`, and by H.107
clause (ii) that is exactly invisibility of the constant coefficient. -/
theorem isDrainState_iff_resOrd_eq {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m N : ℕ} (hm : 0 < m) (c : ClusterState O m N) :
    IsDrainState c ↔ resOrd (c.1 ⟨0, hm⟩) = N := by
  rw [isDrainState_iff hm, resOrd_eq_iff]

/-- **Non-drain makes the constant coefficient VISIBLE.** Its windowed valuation is at most
`N − 1`: it is `≤ N` always (`resOrd_le`) and `≠ N` because the coefficient is nonzero
(H.107 clause (ii)). -/
theorem resOrd_zero_le_of_not_isDrainState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m N : ℕ} (hm : 0 < m) (c : ClusterState O m N)
    (h0 : ¬ IsDrainState c) : resOrd (c.1 ⟨0, hm⟩) ≤ N - 1 := by
  have hne : c.1 ⟨0, hm⟩ ≠ 0 := fun hq => h0 ((isDrainState_iff hm c).2 hq)
  have h1 : resOrd (c.1 ⟨0, hm⟩) ≤ N := resOrd_le _
  have h2 : resOrd (c.1 ⟨0, hm⟩) ≠ N := fun h => hne ((resOrd_eq_iff _).1 h)
  omega

/-! ## 2. The capped slope content -/

/-- **H.108 (def half, b). The CAPPED slope-`k` content.**
`D = min_{j ≤ m} (min (v (a j)) N + j * k)`, the monic top `j = m` contributing `m * k`
(`GENIND-3`'s terminal `[r3]`-capped display, `EFF.GENIND.24`).  Computed on the CLASS: the
capping is already inside `resOrd` (H.107), so no lift is consulted. -/
noncomputable def betaContent {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m N : ℕ} (c : ClusterState O m N) (k : ℕ) : ℕ :=
  Finset.inf' (Finset.range (m + 1)) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun j => if h : j < m then resOrd (c.1 ⟨j, h⟩) + j * k else m * k)

/-- The content is below each visible term of its infimum. -/
theorem betaContent_le_of_lt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (c : ClusterState O m N) (k : ℕ) {j : ℕ} (hj : j < m) :
    betaContent c k ≤ resOrd (c.1 ⟨j, hj⟩) + j * k := by
  have hmem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have h := Finset.inf'_le (s := Finset.range (m + 1))
    (fun i => if h : i < m then resOrd (c.1 ⟨i, h⟩) + i * k else m * k) hmem
  simpa only [betaContent, dif_pos hj] using h

/-- The content is below the monic top term `m * k` — the `j = m` term of the infimum. -/
theorem betaContent_le_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (c : ClusterState O m N) (k : ℕ) : betaContent c k ≤ m * k := by
  have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have h := Finset.inf'_le (s := Finset.range (m + 1))
    (fun i => if h : i < m then resOrd (c.1 ⟨i, h⟩) + i * k else m * k) hmem
  simpa only [betaContent, dif_neg (lt_irrefl m)] using h

/-! ## 3. The lemma half: the content sits below the window -/

set_option linter.unusedVariables false in
/-- **H.108 (lemma half).** On a NON-drain state the capped content sits strictly inside the
window: `D ≤ N − 1`.  Proof: the `j = 0` term of the infimum is `resOrd (c 0) + 0 * k`, and
non-drain makes `resOrd (c 0) ≤ N − 1`.

The `1 ≤ N` binder is part of the FROZEN blueprint signature and is not consumed by the proof
(non-drain already forces `N ≥ 1`, since `resOrd (c 0) ≠ N` is impossible at `N = 0`); the
linter is silenced rather than the binder dropped. -/
theorem betaContent_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (c : ClusterState O m N)
    (h0 : ¬ IsDrainState c) (k : ℕ) : betaContent c k ≤ N - 1 := by
  have hm' : 0 < m := hm
  have h := betaContent_le_of_lt c k hm'
  have hz := resOrd_zero_le_of_not_isDrainState hm' c h0
  omega

/-- **The window-positivity rider** (`EFF.GENIND.24`'s three-layer correction, in one line):
on a non-drain state the extracted child window `N − D` is at least `1`, so the recursion never
hands a child a degenerate window. -/
theorem one_le_window_of_not_isDrainState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (c : ClusterState O m N)
    (h0 : ¬ IsDrainState c) (k : ℕ) : 1 ≤ N - betaContent c k := by
  have h := betaContent_le hm hN c h0 k
  omega

end Uniformity.Density.Induction

/-! ## 4. TEETH, Lean half — the ALPHA content identity

Battery, ALPHA branch: `assert D == m * k and Dpred == m * k`.  The `Dpred` half is a statement
about the capped content alone, so it is provable here: when every visible term of the infimum
already dominates the monic top term, the infimum IS the monic top term.  (The `D == Dpred`
half — the reader's uncapped `min` over the recentred coefficients agreeing with the class-level
`Dpred` — is the expansion statement of H.109, not of this node.) -/

section Teeth

open Uniformity.Density.Induction

/-- TEETH — the ALPHA branch's content value: if no visible coefficient beats the monic top,
`betaContent c k = m * k`. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {m N : ℕ}
    (c : ClusterState O m N) (k : ℕ)
    (hdom : ∀ (j : ℕ) (h : j < m), m * k ≤ resOrd (c.1 ⟨j, h⟩) + j * k) :
    betaContent c k = m * k := by
  refine le_antisymm (betaContent_le_mul c k) ?_
  refine Finset.le_inf' _ _ ?_
  intro j _
  by_cases hj : j < m
  · simpa only [dif_pos hj] using hdom j hj
  · rw [dif_neg hj]

end Teeth

/-! ## 5. TEETH, numeric half — the bound, re-run on the battery's grids

`Dpred` depends on the state only through the vector of CAPPED valuations
`(min (v (a j)) W)_{j < m} ∈ {0, …, W} ^ m`, so the lemma half is a finite arithmetic
statement once `(m, W, k)` are fixed — and `q` never enters.  `contentModel` is `Dpred`
transcribed from the battery source; `boundHolds m W k` asserts `betaContent_le` over the whole
non-drain grid at that shape, and the guards run it on the `m` values of the battery's `part1`
plan (`m ∈ {2, 3, 4}`) at every window `W ≤ 4` and every slope `k ≤ 3`.

**Non-vacuity is pinned, not assumed.**  Both `all`-quantifiers run over FILTERED grids, so an
over-tight filter would make them vacuously true; the two cardinality guards below fix the
exercised populations at `3856` non-drain states and `1333` alpha-dominating states (of which
`77` at slope `k ≥ 1`).  The drain spot check `contentModel [3, 3] 2 5 = 3 > 3 − 1` shows the
non-drain filter is load-bearing: the bound is FALSE on drain states, which is exactly why the
node's lemma half carries `¬ IsDrainState c`. -/

section NumericGate

/-- The battery's `Dpred`, transcribed: `v` lists the capped valuations of `a 0, …, a (m−1)`. -/
private def contentModel (v : List ℕ) (m k : ℕ) : ℕ :=
  ((List.range (m + 1)).map
    (fun j => if j < m then v.getD j 0 + j * k else m * k)).foldr min (m * k)

/-- All capped-valuation vectors of length `n` with entries in `{0, …, W}`. -/
private def cappedVecs : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | (n + 1), W => (cappedVecs n W).flatMap fun t => (List.range (W + 1)).map fun x => x :: t

/-- The NON-DRAIN grid of shape `(m, W)`: the battery's drain test is `vals[0] >= W`. -/
private def nonDrainGrid (m W : ℕ) : List (List ℕ) :=
  (cappedVecs m W).filter fun v => decide (v.getD 0 0 < W)

/-- The ALPHA grid: every visible term already dominates the monic top term `m * k`. -/
private def alphaGrid (m W k : ℕ) : List (List ℕ) :=
  (cappedVecs m W).filter fun v => decide (∀ j ∈ List.range m, m * k ≤ v.getD j 0 + j * k)

/-- `betaContent_le` on the whole non-drain grid of shape `(m, W)` at slope `k`. -/
private def boundHolds (m W k : ℕ) : Bool :=
  (nonDrainGrid m W).all fun v => decide (contentModel v m k ≤ W - 1)

/-- The ALPHA identity of §4, on the same shapes: domination by the monic top pins the value. -/
private def alphaHolds (m W k : ℕ) : Bool :=
  (alphaGrid m W k).all fun v => decide (contentModel v m k = m * k)

/-- The battery's `part1` shapes, folded: `m ∈ {2, 3, 4}`, `W ∈ {1, …, 4}`, `k ∈ {0, …, 3}`. -/
private def overPlan (P : ℕ → ℕ → ℕ → Bool) : Bool :=
  (List.range 3).all fun mi =>
    (List.range 4).all fun Wi => (List.range 4).all fun k => P (mi + 2) (Wi + 1) k

/-- The same fold, summing a population instead of conjoining a test. -/
private def countOverPlan (F : ℕ → ℕ → ℕ → ℕ) : ℕ :=
  ((List.range 3).flatMap fun mi =>
    (List.range 4).flatMap fun Wi =>
      (List.range 4).map fun k => F (mi + 2) (Wi + 1) k).sum

-- THE LEMMA HALF, re-run: `D ≤ W − 1` at every non-drain state of every planned shape
#guard overPlan boundHolds

-- THE ALPHA IDENTITY of §4, re-run: `D = m * k` wherever the monic top dominates
#guard overPlan alphaHolds

-- non-vacuity: the exercised populations, pinned
#guard countOverPlan (fun m W _ => (nonDrainGrid m W).length) == 3856
#guard countOverPlan (fun m W k => (alphaGrid m W k).length) == 1333
#guard ((List.range 3).flatMap fun mi => (List.range 4).flatMap fun Wi =>
  (List.range 3).map fun k => (alphaGrid (mi + 2) (Wi + 1) (k + 1)).length).sum == 77

-- the non-drain filter is load-bearing: on a DRAIN state the bound FAILS
-- (`m = 2`, `W = 3`, `k = 5`, capped valuations `(3, 3)`: `D = 3 > 2 = W − 1`)
#guard contentModel [3, 3] 2 5 == 3
#guard !(decide (contentModel [3, 3] 2 5 ≤ 3 - 1))

-- spot values: `m = 3`, `k = 1`, capped valuations `(1, 2, 3)` gives `min(1, 3, 5, 3) = 1`
#guard contentModel [1, 2, 3] 3 1 == 1
-- the ALPHA shape at `m = 2`, `k = 2`: `(4, 3)` gives `min(4, 5, 4) = 4 = m * k`
#guard contentModel [4, 3] 2 2 == 4

end NumericGate

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.IsDrainState
#print axioms Uniformity.Density.Induction.isDrainState_iff
#print axioms Uniformity.Density.Induction.isDrainState_of_eq_zero
#print axioms Uniformity.Density.Induction.isDrainState_iff_resOrd_eq
#print axioms Uniformity.Density.Induction.resOrd_zero_le_of_not_isDrainState
#print axioms Uniformity.Density.Induction.betaContent
#print axioms Uniformity.Density.Induction.betaContent_le_of_lt
#print axioms Uniformity.Density.Induction.betaContent_le_mul
#print axioms Uniformity.Density.Induction.betaContent_le
#print axioms Uniformity.Density.Induction.one_le_window_of_not_isDrainState

end AxCheck
