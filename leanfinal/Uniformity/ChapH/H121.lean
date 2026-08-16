/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H119
import Uniformity.ChapH.H114

/-!
# Uniformity.ChapH.H121 — the split leg (H.121 clause i)

**Chapter H, NODE H.121 clause (i)** [theorem] (`blueprint/CHAP-H_general_induction.md` §17.3 —
the T-1 completion layer, dated extension 2026-08-16; provenance OM-2 §3.3 N-3, *"hsplit and
hhead hold as EQUALITIES"*, sources `EFF.GENIND.45` (the `S5.2` recursion) and
`EFF.GENIND.152`).  Split-mandated part **a** of H.121 (parts b/c are `H121b`/`H121c`).

* `clusterUndecided_setOf_split` — the set-level partition of the conservative verdict;
* `uCluster_split` (clause i) — `u(N) = #drain + #(α ∧ undec) + #(β ∧ undec)`, an EQUALITY.

## Why the equality holds, and where the `m ≤ 3` guard enters

H.111's totality says every cluster state is DRAIN, CS, α, β or DEC, and the buckets are
pairwise disjoint.  Restricting that partition to the conservatively undecided set kills two of
the five cells:

* **CS is EMPTY at `2 ≤ m ≤ 3`** — H.117 (clause i) caps every CS event at `4 ≤ m`, re-exported
  as H.118's `not_isCSState_of_le_three`.  This is the ONLY place the `m ≤ 3` guard is used, and
  it is load-bearing: DECISION D-H17.1 sends CS states into the verdict unconditionally
  (`ClusterUndecided.cs`), so above `m = 3` the display acquires a fourth, HYP-gated term.  The
  defeat gate of §3 exhibits the failure on a toy carrying one CS state.
* **DEC is DECIDED** — H.119's `not_clusterUndecided_of_isDecState`: no rule of H.118 reaches a
  DEC state, because α's witness is a full-multiplicity child and β's witness is a child, and
  H.111 (c)'s third conjunct denies every child.

What survives is DRAIN ⊎ (α ∧ undecided) ⊎ (β ∧ undecided).  The drain cell needs no
`∧ undecided` qualifier: H.118's first constructor makes every drain state undecided
(`clusterUndecided_of_isDrainState`), which is exactly the asymmetry in the blueprint display —
the head term is a plain census (H.113's `Q ^ ((m−1)(N−1))`) while the α and β terms are not.

Disjointness is three one-liners: α and β are non-drain by their leading conjunct
(H.111's `not_isDrainState_of_isAlphaState`/`_isBetaState`) and α excludes β because the α
witness IS a full-multiplicity child (H.111's `alpha_not_beta`), which β's fourth conjunct
denies.

**Counting.**  `Nat.card` of a subtype is `Set.ncard` of the corresponding set (definitionally),
and `Set.ncard` is additive over a disjoint union of finite sets.  Finiteness is H.114's
`instFiniteClusterState` (the carrier is a finite product of finite quotients once
`[Finite (ResidueField O)]` is in scope) — which is why this clause, unlike H.119's, carries
that instance.

## ⚠ The S-1 fence

`uCluster` is the CONSERVATIVE complement `u_{m,1}`, never the semantic `undecidedCount`; the
bridge is H.123's and it is an INEQUALITY in one direction only (finding F-2).  Nothing in this
file may be read as a statement about the semantic undecided locus.

DEPENDS: H.111 (`cluster_partition`, `alpha_not_beta`, the non-drain riders), H.113 (the head
census, consumed downstream not here), H.114 (`instFiniteClusterState`), H.117 → H.118
(`not_isCSState_of_le_three`, `clusterUndecided_of_isDrainState`), H.119 (`uCluster`,
`not_clusterUndecided_of_isDecState`).

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `[Finite (ResidueField O)]` +
`[IsAdicComplete (maximalIdeal O) O]` + `π` explicit, every binder INLINE.  `(O : Type)` (not
`Type*`) in the signed statement: the frozen stub pins the universe.

## TEETH (GC-8)

Battery `P3 hsplit as EQUALITY` of `verification/openmath/OM2_genindb_battery.py`.  §3 runs
three gates.  (1) The split as an exact count on a ten-state toy reader carrying all five bucket
labels' behaviour, with the least fixed point of H.118's rule list computed by closure
iteration; plus the DEFEAT: relabelling one state CS breaks the identity, which is the `m ≤ 3`
guard's numeric shadow.  (2) The `m = 2` closed form: `hexR = drain + αleg` on the nose at both
battery characteristics — at `m = 2` the β bucket is EMPTY (H.118's `betaChild_mult_lt` needs
`2 ≤ μ < 2`), so the residual must vanish identically, and it does.  (3) The `m = 3` closed
form: `hexU − drain − αleg ≥ 0` at both characteristics, the β cell of the very same split
(its envelope is clause (iii)'s business, not this file's).

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The partition of the verdict set -/

/-- **The conservative verdict, partitioned.**  At `2 ≤ m ≤ 3` the undecided set is exactly
DRAIN ∪ (α ∧ undecided) ∪ (β ∧ undecided): CS is empty (H.117 via H.118) and DEC is decided
(H.119).  The `⊇` inclusion needs only H.118's drain constructor. -/
theorem clusterUndecided_setOf_split {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3) {N : ℕ} (hN : 1 ≤ N) :
    {c : ClusterState O m N | ClusterUndecided O π m N c}
      = ({c : ClusterState O m N | IsDrainState c}
            ∪ {c : ClusterState O m N |
              (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c})
          ∪ {c : ClusterState O m N | IsBetaState π c ∧ ClusterUndecided O π m N c} := by
  ext c
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro hc
    rcases cluster_partition π c with hd | hcs | ⟨k, z, hα⟩ | hβ | hdec
    · exact Or.inl (Or.inl hd)
    · exact absurd hcs (not_isCSState_of_le_three hπ (by omega) hN hm3 c)
    · exact Or.inl (Or.inr ⟨⟨k, z, hα⟩, hc⟩)
    · exact Or.inr ⟨hβ, hc⟩
    · exact absurd hc (not_clusterUndecided_of_isDecState hdec)
  · rintro ((hd | ⟨-, hu⟩) | ⟨-, hu⟩)
    · exact clusterUndecided_of_isDrainState π c hd
    · exact hu
    · exact hu

/-! ## 2. Disjointness, and the count -/

/-- DRAIN meets no α state: `IsAlphaState`'s leading conjunct. -/
theorem disjoint_drain_alphaUndecided {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {π : O} {m N : ℕ} :
    Disjoint {c : ClusterState O m N | IsDrainState c}
      {c : ClusterState O m N | (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c} := by
  rw [Set.disjoint_left]
  rintro c hd ⟨⟨k, z, hα⟩, -⟩
  exact not_isDrainState_of_isAlphaState hα hd

/-- DRAIN and α both miss β: the first by `IsBetaState`'s leading conjunct, the second because
the α witness IS a full-multiplicity child (H.111's `alpha_not_beta`). -/
theorem disjoint_drainAlpha_betaUndecided {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {π : O} {m N : ℕ} :
    Disjoint ({c : ClusterState O m N | IsDrainState c}
        ∪ {c : ClusterState O m N |
          (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c})
      {c : ClusterState O m N | IsBetaState π c ∧ ClusterUndecided O π m N c} := by
  rw [Set.disjoint_left]
  rintro c (hd | ⟨⟨k, z, hα⟩, -⟩) ⟨hβ, -⟩
  · exact not_isDrainState_of_isBetaState hβ hd
  · exact alpha_not_beta hα hβ

/-- **H.121 (clause i) — the split, as an EQUALITY.**  At `2 ≤ m ≤ 3` the conservative
complement is the head census plus the two live buckets:
`u(N) = #DRAIN + #(α ∧ undecided) + #(β ∧ undecided)`.

The CS cell is empty (H.117 (i) read through H.118) and the DEC cell is decided (H.119's
inversion corollary), so H.111's five-way partition collapses to three cells; the drain cell
carries no `∧ undecided` because H.118's first constructor makes every drain state
undecided. -/
theorem uCluster_split {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3) (N : ℕ) (hN : 1 ≤ N) :
    uCluster O π m N
      = Nat.card {c : ClusterState O m N // IsDrainState c}
        + Nat.card {c : ClusterState O m N //
            (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c}
        + Nat.card {c : ClusterState O m N //
            IsBetaState π c ∧ ClusterUndecided O π m N c} := by
  classical
  have h1 : uCluster O π m N = {c : ClusterState O m N | ClusterUndecided O π m N c}.ncard := rfl
  rw [h1, clusterUndecided_setOf_split hπ hm hm3 hN,
    Set.ncard_union_eq disjoint_drainAlpha_betaUndecided (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq disjoint_drain_alphaUndecided (Set.toFinite _) (Set.toFinite _)]
  rfl

end Uniformity.Density.Induction

/-! ## 3. TEETH

### 3.1 The split on a toy reader, and the CS defeat

`splitLbl` labels ten toy states (`0 = DRAIN`, `1 = CS`, `2 = α`, `3 = β`, `4 = DEC`) and
`splitKids` gives each state's children at strictly smaller indices (the lexicographic measure).
`splitLfp` iterates H.118's rule list — DRAIN and CS fire unconditionally, α and β fire from an
undecided child — ten times from the empty set, i.e. computes the least fixed point.  The gate
checks the clause exactly:

  `#undecided = #DRAIN + #(α ∧ undecided) + #(β ∧ undecided)`.

The DEFEAT relabels state `2` from DEC to CS.  The identity then FAILS (`9 ≠ 8`), because the CS
state and everything it feeds enter the verdict through a constructor with no bucket on the
right-hand side.  That is the `m ≤ 3` guard's content: above `m = 3` the display needs a fourth
term, and DECISION D-H17.1's pessimistic exit is what puts it there.

### 3.2/3.3 The split against the landed conservative closed forms

`hexR`/`hexU` are `OM2_genindb_battery.py`'s `hex3R_ref`/`hex3U_ref` transcribed verbatim (the
same transcription H.119's gate pins, with the same reference values).  `drainCount q m N`
is H.113's head census `q ^ ((m−1)(N−1))` and `alphaLeg` is clause (ii)'s display.  At `m = 2`
the β bucket is EMPTY, so the split forces `hexR = drain + αleg` with ZERO residual — checked at
both battery characteristics through window 8.  At `m = 3` the β bucket is live and the split
only forces the residual to be a genuine count, i.e. nonnegative — checked the same way, with
the realized values pinned so a silent change is caught.

⚠ S-1: `hexR`/`hexU` are CONSERVATIVE-family closed forms; nothing here ties them to the
semantic `undecidedCount` (finding F-2). -/

section NumericGate

/-- Bucket labels of the toy: `0 = DRAIN`, `1 = CS`, `2 = α`, `3 = β`, `4 = DEC`. -/
private def splitLbl : List ℕ := [0, 0, 4, 2, 3, 2, 3, 4, 3, 2]

/-- Children of each toy state, always at strictly smaller indices. -/
private def splitKids : List (List ℕ) :=
  [[], [], [], [2], [0, 2], [1], [3, 5], [], [3, 7], [4]]

/-- One application of H.118's rule list at a given labelling. -/
private def splitStep (lbl : List ℕ) (S : List Bool) : List Bool :=
  (List.range 10).map fun i =>
    decide (lbl.getD i 4 ≤ 1) ||
      (decide (lbl.getD i 4 = 2) || decide (lbl.getD i 4 = 3)) &&
        (splitKids.getD i []).any fun j => S.getD j false

/-- The least fixed point of the rule list: ten closure iterations from the empty set. -/
private def splitLfp (lbl : List ℕ) : List Bool :=
  (List.range 10).foldl (fun S _ => splitStep lbl S) (List.replicate 10 false)

/-- `#{i | lbl i = b ∧ undecided i}`, the bucket cell of the split. -/
private def cellCount (lbl : List ℕ) (S : List Bool) (b : ℕ) : ℕ :=
  ((List.range 10).filter fun i => decide (lbl.getD i 4 = b) && S.getD i false).length

/-- `#undecided`. -/
private def undecCount (S : List Bool) : ℕ := (S.filter id).length

-- the pinned verdict, so a silent change to either computation is caught
#guard splitLfp splitLbl == [true, true, false, false, true, true, true, false, false, true]

-- clause (i): `#undec = #DRAIN + #(α ∧ undec) + #(β ∧ undec)` (the drain cell is all of DRAIN)
#guard undecCount (splitLfp splitLbl)
  == cellCount splitLbl (splitLfp splitLbl) 0 + cellCount splitLbl (splitLfp splitLbl) 2
      + cellCount splitLbl (splitLfp splitLbl) 3

-- every DRAIN state is undecided (H.118's first constructor), so the head cell is a census
#guard cellCount splitLbl (splitLfp splitLbl) 0
  == ((List.range 10).filter fun i => decide (splitLbl.getD i 4 = 0)).length

-- no DEC state is undecided (H.119's inversion corollary)
#guard cellCount splitLbl (splitLfp splitLbl) 4 == 0

/-- The DEFEAT labelling: state `2` becomes CS instead of DEC. -/
private def csLbl : List ℕ := [0, 0, 1, 2, 3, 2, 3, 4, 3, 2]

-- with ONE CS state the three-term split FAILS — the `m ≤ 3` guard is load-bearing
#guard !(undecCount (splitLfp csLbl)
  == cellCount csLbl (splitLfp csLbl) 0 + cellCount csLbl (splitLfp csLbl) 2
      + cellCount csLbl (splitLfp csLbl) 3)
#guard (undecCount (splitLfp csLbl),
    cellCount csLbl (splitLfp csLbl) 0 + cellCount csLbl (splitLfp csLbl) 2
      + cellCount csLbl (splitLfp csLbl) 3) == (9, 8)

/-- The battery's `hex3R_ref` — ChapG `hex3R`, the `m = 2` conservative complement. -/
private def hexR (q M : ℕ) : ℕ :=
  if M = 0 then 0 else if M = 1 then 1
  else q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

/-- The battery's `hex3U_ref` — ChapG `hex3U`, the cubic per-centre conservative complement. -/
private def hexU (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ 3 * k ≤ N - 1)).map fun k =>
        (q - 1) * q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hexR q (N - 3 * k))).sum

/-- H.113's head census `q ^ ((m − 1)(N − 1))`. -/
private def drainCount (q m N : ℕ) : ℕ := q ^ ((m - 1) * (N - 1))

/-- Clause (ii)'s α leg, `Σ_{1 ≤ k, mk ≤ N−1} (q − 1) q ^ (k · c(m)) u(N − mk)`,
`c(2) = 1`, `c(3) = 3`. -/
private def alphaLeg (q m N : ℕ) (u : ℕ → ℕ) (c : ℕ) : ℕ :=
  (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ m * k ≤ N - 1)).map fun k =>
    (q - 1) * q ^ (k * c) * u (N - m * k)).sum

-- 3.2: at `m = 2` the β bucket is EMPTY, so the split is `hexR = drain + αleg` EXACTLY
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 9).drop 1).all fun N =>
    hexR q N == drainCount q 2 N + alphaLeg q 2 N (hexR q) 1

-- 3.3: at `m = 3` the β cell is live; the split makes it a genuine (nonnegative) count
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 8).drop 1).all fun N =>
    decide (drainCount q 3 N + alphaLeg q 3 N (hexU q) 3 ≤ hexU q N)

-- the realized β cells, pinned (`hexU − drain − αleg`)
#guard ((List.range 8).drop 1).map
    (fun N => hexU 2 N - drainCount 2 3 N - alphaLeg 2 3 N (hexU 2) 3)
  == [0, 0, 0, 0, 16, 208, 928]
#guard ((List.range 8).drop 1).map
    (fun N => hexU 3 N - drainCount 3 3 N - alphaLeg 3 3 N (hexU 3) 3)
  == [0, 0, 0, 54, 810, 16686, 156492]

end NumericGate

/-! ## 4. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.clusterUndecided_setOf_split
#print axioms Uniformity.Density.Induction.disjoint_drain_alphaUndecided
#print axioms Uniformity.Density.Induction.disjoint_drainAlpha_betaUndecided
#print axioms Uniformity.Density.Induction.uCluster_split

end AxCheck
