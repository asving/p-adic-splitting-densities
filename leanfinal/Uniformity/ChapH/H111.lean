/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H109
import Uniformity.ChapH.H110

/-!
# Uniformity.ChapH.H111 — the five-case partition (N-2a's shell)

**Chapter H, NODE H.111** [def+lemma] (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §3.2 N-2a's displayed five-case
classification, source `EFF.GENIND.08`).  Sixth node of **N-2**, the cluster event grammar
over `O`, and the one that closes the grammar's shell.

Every cluster state falls in exactly one of five buckets:

| bucket | reading | carrier |
|---|---|---|
| DRAIN | the constant coefficient is invisible; the reader exits UNDECIDED (S-1) | H.108 |
| CS | a side carries a repeated residual block of size `≥ 2`; UNDECIDED (D-H17.1) | H.110 |
| α | a FULL-multiplicity child (`μ = m`): the cluster recentres entire | H.109 |
| β | a child exists, but none of full multiplicity: fracture | H.109 |
| DEC | no drain, no CS, no child — every residual factor is simple, and the reader DECIDES | — |

* `IsAlphaState`, `IsBetaState`, `IsDecState` (def halves) — the three buckets not already
  carried by H.108/H.110;
* `cluster_partition` (lemma half, **totality**) — every state is drain ∨ CS ∨ α ∨ β ∨ DEC;
* `alpha_not_beta` (lemma half, the ONE non-definitional disjointness) — plus `alpha_not_dec`
  and `beta_not_dec` as riders.  The remaining pairs are disjoint by the leading `¬`-conjuncts
  of the definitions and need no lemma (DRAIN vs everything: the `¬ IsDrainState` conjunct;
  CS vs α/β/DEC: the `¬ IsCSState` conjunct).

The DEC bucket's `(e, f)`-read of the pieces is chapter B's leaf layer (TRACK V) and is not
touched here: `IsDecState` is the *reader's* exit condition, nothing more.

## The α SHAPE is a consequence, not a conjunct

`IsAlphaState` says only `HasChildAt π c m k z` on top of the two negations.  That a
full-multiplicity child forces the α shape — the slope-`k` residual has a degree-`m` root block,
so the `(k, 1)`-side spans abscissae `0 .. m`, a single side with no cofactor pieces, and the
residual IS `unit * (y − z) ^ m` — is a CONSEQUENCE, recorded in the blueprint as the reading
consumed at H.112/H.115.  It is deliberately NOT proved here and NOT added as a conjunct: the
definition stays minimal so that `cluster_partition` is a pure case split.

DEPENDS: H.108 (`IsDrainState`), H.109 (`HasChildAt`), H.110 (`IsCSState`).

## TEETH (GC-8)

Battery `P1(a) partition total` and the **CC-2(i) partition-defeat scan** (EMPTY at every cell:
no state lands in two buckets, and none in zero) of
`verification/openmath/OM2_genindb_battery.py` (RESULTS 2026-08-16, 612/612).  What is
reproducible cheaply is the *combinatorial* content of that scan, and it is reproduced exactly:
`bucketFires` evaluates the five bucket conditions from the four defining booleans (drain, CS,
"a child exists", "a full-multiplicity child exists"), and the `#guard` below checks that
across all 16 assignments satisfying `full → child`, EXACTLY ONE bucket fires.

`full → child` is the one consistency constraint, and it is load-bearing: the defeat guard below
shows that the two assignments violating it fire TWO buckets (α and DEC).  On the Lean side the
constraint is automatic — `IsAlphaState`'s witness `HasChildAt π c m k z` is itself a child, so
`alpha_not_dec` holds — which is why the scan comes back empty.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The three remaining buckets -/

/-- **H.111 (def a).** α: a FULL-multiplicity child (`μ = m`) at integer slope `k` — the
whole cluster recenters. -/
def IsAlphaState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) (k : ℕ) (z : ResidueField O) : Prop :=
  ¬ IsDrainState c ∧ ¬ IsCSState π c ∧ HasChildAt π c m k z

/-- **H.111 (def b).** β: fracture — a child exists but no full-multiplicity child. -/
def IsBetaState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ¬ IsDrainState c ∧ ¬ IsCSState π c ∧
    (∃ μ k z, HasChildAt π c μ k z) ∧ ¬ ∃ k z, HasChildAt π c m k z

/-- **H.111 (def c).** DEC: no drain, no CS, no child — every residual factor is simple and
the conservative reader DECIDES (the pieces' `(e,f)` read is chapter B's leaf layer). -/
def IsDecState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ¬ IsDrainState c ∧ ¬ IsCSState π c ∧ ¬ ∃ μ k z, HasChildAt π c μ k z

/-! ## 2. Totality -/

/-- **H.111 (lemma half, totality).** Every state is drain, CS, α, β or DEC.  The proof is the
classical case split on the four defining data, in the order the reader tests them: drain first
(S-1), then CS (D-H17.1's pessimistic exit), then a full-multiplicity child, then any child. -/
theorem cluster_partition {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) :
    IsDrainState c ∨ IsCSState π c ∨ (∃ k z, IsAlphaState π c k z) ∨
      IsBetaState π c ∨ IsDecState π c := by
  classical
  by_cases hd : IsDrainState c
  · exact Or.inl hd
  by_cases hcs : IsCSState π c
  · exact Or.inr (Or.inl hcs)
  by_cases hfull : ∃ k z, HasChildAt π c m k z
  · obtain ⟨k, z, hkz⟩ := hfull
    exact Or.inr (Or.inr (Or.inl ⟨k, z, hd, hcs, hkz⟩))
  by_cases hchild : ∃ μ k z, HasChildAt π c μ k z
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, hcs, hchild, hfull⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hd, hcs, hchild⟩)))

/-! ## 3. Disjointness -/

/-- **H.111 (lemma half, the one non-definitional disjointness).**  The α witness IS a
full-multiplicity child, which is exactly what β's fourth conjunct denies. -/
theorem alpha_not_beta {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N : ℕ} {c : ClusterState O m N} {k : ℕ} {z : ResidueField O} :
    IsAlphaState π c k z → ¬ IsBetaState π c := by
  intro hα hβ
  exact hβ.2.2.2 ⟨k, z, hα.2.2⟩

/-- **Rider.**  α excludes DEC: the α witness is a child (at multiplicity `m`), and DEC denies
every child.  This is the constraint `full → child` of the CC-2(i) defeat scan below. -/
theorem alpha_not_dec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N : ℕ} {c : ClusterState O m N} {k : ℕ} {z : ResidueField O} :
    IsAlphaState π c k z → ¬ IsDecState π c := by
  intro hα hdec
  exact hdec.2.2 ⟨m, k, z, hα.2.2⟩

/-- **Rider.**  β excludes DEC: β asserts a child, DEC denies every child. -/
theorem beta_not_dec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N : ℕ} {c : ClusterState O m N} :
    IsBetaState π c → ¬ IsDecState π c := by
  intro hβ hdec
  exact hdec.2.2 hβ.2.2.1

/-- The three buckets of this node are all non-drain — the leading conjunct, exported so that
consumers can feed H.108/H.109/H.110's non-drain hypotheses without destructuring. -/
theorem not_isDrainState_of_isAlphaState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {m N : ℕ} {c : ClusterState O m N} {k : ℕ}
    {z : ResidueField O} (h : IsAlphaState π c k z) : ¬ IsDrainState c := h.1

theorem not_isDrainState_of_isBetaState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {m N : ℕ} {c : ClusterState O m N}
    (h : IsBetaState π c) : ¬ IsDrainState c := h.1

theorem not_isDrainState_of_isDecState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {m N : ℕ} {c : ClusterState O m N}
    (h : IsDecState π c) : ¬ IsDrainState c := h.1

end Uniformity.Density.Induction

/-! ## 4. TEETH — the CC-2(i) partition-defeat scan, reproduced

`bucketFires drain cs child full` lists the five bucket conditions, transcribed from the
definitions of §1 (and from H.108/H.110) with the four defining data as booleans:

```
DRAIN = drain
CS    = ¬drain ∧ cs
α     = ¬drain ∧ ¬cs ∧ full
β     = ¬drain ∧ ¬cs ∧ child ∧ ¬full
DEC   = ¬drain ∧ ¬cs ∧ ¬child
```

The battery's CC-2(i) scan reports EMPTY — no state in two buckets, none in zero — at every
cell of every ring.  Its combinatorial content is the `#guard` below. -/

section NumericGate

/-- The five bucket conditions, from the four defining booleans. -/
def bucketFires (drain cs child full : Bool) : List Bool :=
  [drain,
   !drain && cs,
   !drain && !cs && full,
   !drain && !cs && child && !full,
   !drain && !cs && !child]

/-- Exactly one entry of the list is `true`. -/
def exactlyOne (l : List Bool) : Bool := (l.filter id).length == 1

/-- All 16 assignments of the four defining booleans. -/
def allAssignments : List (Bool × Bool × Bool × Bool) :=
  [false, true].flatMap fun d =>
    [false, true].flatMap fun cs =>
      [false, true].flatMap fun ch =>
        [false, true].map fun f => (d, cs, ch, f)

-- CC-2(i): on every consistent assignment (`full → child`, automatic in Lean by
-- `alpha_not_dec`) exactly one bucket fires — the scan is EMPTY.
#guard (allAssignments.filter fun t => !t.2.2.2 || t.2.2.1).all
  fun t => exactlyOne (bucketFires t.1 t.2.1 t.2.2.1 t.2.2.2)

-- DEFEAT: drop `full → child` and the scan is no longer empty.  The rogue assignment
-- (drain = F, cs = F, child = F, full = T) fires TWO buckets, α and DEC.
#guard bucketFires false false false true == [false, false, true, false, true]
#guard ((bucketFires false false false true).filter id).length == 2

-- and it is the ONLY one of the 16 assignments that fails the scan (the other three
-- `full ∧ ¬child` assignments are shielded by their own DRAIN/CS conjunct).
#guard (allAssignments.filter fun t => !(exactlyOne (bucketFires t.1 t.2.1 t.2.2.1 t.2.2.2)))
  == [(false, false, false, true)]

end NumericGate

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.IsAlphaState
#print axioms Uniformity.Density.Induction.IsBetaState
#print axioms Uniformity.Density.Induction.IsDecState
#print axioms Uniformity.Density.Induction.cluster_partition
#print axioms Uniformity.Density.Induction.alpha_not_beta
#print axioms Uniformity.Density.Induction.alpha_not_dec
#print axioms Uniformity.Density.Induction.beta_not_dec

end AxCheck
