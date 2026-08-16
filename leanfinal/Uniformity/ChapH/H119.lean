/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H118

/-!
# Uniformity.ChapH.H119 — the conservative complement and its boundary

**Chapter H, NODE H.119** [def+lemma] (`blueprint/CHAP-H_general_induction.md` §17.3 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §4 sketch N3.1 and row 0d
(*"`u(1) = 1`, certified again on true data"*), sources `EFF.GENIND.45` (the `S5.2` recursion)
and `EFF.GENIND.160` (`ANNEX R R3`).  Second node of **N-3**.

* `uCluster O π m N` (def a) — the conservative undecided COUNT, `Nat.card` of the subtype
  H.118's inductive cuts out of the cluster-state space;
* `uClusterNorm O π m N` (def b) — its normalization by the H.106 census `Q ^ (m (N − 1))`;
* `uCluster_one` (clause i) — the window-1 boundary `u(1) = 1`;
* `clusterUndecided_iff` (clause ii) — the RECURSION IDENTITY / INVERSION: H.118's inductive is
  EXACTLY the reader's verdict equations.

## ⚠ The S-1 fence, restated (it is sharpest at this node)

`uCluster` counts the CONSERVATIVE complement `u_{m,1}`.  It is NOT `undecidedCount`, and no
result in this file or downstream of it may be read as one about the semantic object; the
bridge is H.123's, and it is an INEQUALITY in one direction only.  The battery's `P1(i)` ties —
`u_2 = ChapG hex3R`/`uTwo`, `u_3 = ChapG hex3U` — are ties to the CONSERVATIVE family
(`hex3R`/`hex3U`/`uTwo`) and must never be cited as ties to `undecidedCount` (finding F-2).

## The two clauses, and where their content actually sits

**Clause (i), `u(1) = 1`, is a statement about the CARRIER, not about the reader.**  At window
`1` the coefficient ring is `O ⧸ 𝔪 ^ 1` and the image ideal `𝔪 · (O ⧸ 𝔪)` is `⊥`, so a cluster
state — every coordinate residually zero — has every coordinate `0`.  The state space is a
singleton, its one element has constant coefficient `0`, i.e. is a DRAIN (H.108), and DRAIN is
H.118's first constructor.  So the undecided subtype is a singleton and its `Nat.card` is `1`.
Note what is NOT used: no `[Finite (ResidueField O)]` (nothing is enumerated — the carrier is a
singleton for structural reasons), and neither `hπ` nor `hm`, both of which are carried because
the blueprint signature is frozen.

**Clause (ii) is the inductive's inversion.**  `⟸` is the four constructors verbatim; `⟹` is
`cases` on the derivation, each constructor landing in its own disjunct.  There is no
arithmetic and no measure argument: H.118 already presented the reader's verdict as a least
fixed point, and the equations are what a least fixed point of THOSE rules satisfies.  The
content of the node is therefore the CLAIM that these four disjuncts are the reader's complete
rule list — which is a definitional-faithfulness claim, and is exactly what the battery's
`P1(e) recursion identity` tests exhaustively (both rings, every cell).

The corollary the N-3 legs actually consume is `not_clusterUndecided_of_isDecState`: no rule
reaches a DEC state, so DEC states are DECIDED.  It is proved by the same `cases`, and needs no
hypotheses at all — the α case is excluded because its witness IS a full-multiplicity child and
the β case because its witness IS a child, both of which H.111 (c)'s third conjunct denies.

DEPENDS: H.106 (`ClusterState`, the census normalization `Q ^ (m (N − 1))`), H.118
(`ClusterUndecided`) · H.108 (`IsDrainState`, `betaContent`), H.111 (`IsAlphaState`,
`IsBetaState`, `IsDecState`), H.115 (`alphaChild`), H.116 (`betaChild`) as statement carriers ·
`Uniformity.Density.LocalData` (`Res`, `Coeff`, `residueCard`).

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `[IsAdicComplete (maximalIdeal O) O]`, plus
`[Finite (ResidueField O)]` on def (b) ONLY, + `π` explicit, every binder INLINE.  `(O : Type)`
(not `Type*`) in every signature of this node: the frozen stub pins the universe, because
`uClusterNorm` lands in `ℝ`.

## TEETH (GC-8)

Battery `P1(e) recursion identity` + `P1(i) tie u_2 = ChapG hex3R/uTwo closed form` +
`P1(i) tie u_3 = ChapG hex3U` of `verification/openmath/OM2_genindb_battery.py`.  §4 below runs
two gates.  The first is clause (ii)'s structural content on a TOY reader: a ten-state acyclic
system carrying all five bucket labels, where the least fixed point of H.118's rule list
(computed by iterating the closure from the empty set) is checked to equal the reader's
recursive verdict (computed by one upward pass), and DEC states are checked decided in both.
The second is clause (i) at the two landed conservative closed forms — the battery's own
`hex3R_ref` and `hex3U_ref`, transcribed verbatim — at both battery characteristics, together
with four reference values at the plan's largest cells.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The conservative complement and its normalization -/

/-- **H.119 (def a).** `u_{m,1}(N)`: the conservative undecided count. -/
noncomputable def uCluster (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) (m N : ℕ) : ℕ :=
  Nat.card {c : ClusterState O m N // ClusterUndecided O π m N c}

/-- **H.119 (def b).** The normalized conservative complement `û(N) = u(N)/Q^{m(N−1)}`. -/
noncomputable def uClusterNorm (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] (π : O) (m N : ℕ) : ℝ :=
  (uCluster O π m N : ℝ) / (residueCard O : ℝ) ^ (m * (N - 1))

/-! ## 2. Clause (i) — the window-1 boundary -/

/-- **The window-1 image ideal is trivial.**  `𝔪 · (O ⧸ 𝔪 ^ 1) = ⊥`: the ideal being mapped is
the kernel of the map.  This is why the whole window-1 cluster-state space is a point, and it is
the only ring-theoretic input clause (i) has. -/
theorem eq_zero_of_mem_map_maximalIdeal_one {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (x : Res O 1)
    (hx : x ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ 1))) : x = 0 := by
  have hle : (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ 1)) ≤ ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hy
  simpa using hle hx

/-- **The window-1 cluster state is unique, and it is the zero state.** -/
theorem clusterState_one_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m : ℕ} (c : ClusterState O m 1) : c.1 = (fun _ => 0 : Coeff O m 1) :=
  funext fun i => eq_zero_of_mem_map_maximalIdeal_one (c.1 i) (c.2 i)

set_option linter.unusedVariables false in
/-- **H.119 (lemma a) [clause i].** The window-1 boundary `u(1) = 1` (`ANNEX R R3`,
`EFF.GENIND.160`; OM-2 row 0d): at window 1 the unique state is drain.

`hπ` and `hm` are carried by the frozen blueprint signature and are not consumed: the argument
is that `𝔪` maps to `⊥` in `O ⧸ 𝔪 ^ 1`, which needs neither irreducibility of `π` nor
positivity of `m` (at `m = 0` the state space is the empty function, still a singleton, and
still vacuously a drain by H.108's `isDrainState_of_eq_zero`). -/
theorem uCluster_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) (hπ : Irreducible π) (m : ℕ)
    (hm : 1 ≤ m) : uCluster O π m 1 = 1 := by
  classical
  -- the zero state, and the fact that it is the ONLY one
  let c0 : ClusterState O m 1 := ⟨fun _ => 0, fun _ => Ideal.zero_mem _⟩
  have huniq : ∀ c : ClusterState O m 1, c = c0 := fun c =>
    Subtype.ext (clusterState_one_eq c)
  have hdrain : IsDrainState c0 := fun _ => rfl
  haveI : Unique {c : ClusterState O m 1 // ClusterUndecided O π m 1 c} :=
    { default := ⟨c0, ClusterUndecided.drain c0 hdrain⟩
      uniq := fun a => Subtype.ext (huniq a.1) }
  exact Nat.card_unique

/-- **The normalized boundary.**  `û(1) = 1`: the census denominator at window `1` is
`Q ^ (m · 0) = 1`, so clause (i) transports verbatim.  This is the base case of H.122's strong
induction and of H.120's antitonicity. -/
theorem uClusterNorm_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] (π : O) (hπ : Irreducible π)
    (m : ℕ) (hm : 1 ≤ m) : uClusterNorm O π m 1 = 1 := by
  rw [uClusterNorm, uCluster_one π hπ m hm]
  norm_num

/-! ## 3. Clause (ii) — the recursion identity / inversion -/

set_option linter.unusedVariables false in
/-- **H.119 (lemma b) [clause ii].** The recursion identity / inversion (battery `P1(e)`): the
inductive predicate is EXACTLY the reader's verdict equations — undecided iff drain, or CS, or
α with an undecided sheared child, or β with SOME undecided capped-window child.

`⟸` is H.118's four constructors; `⟹` is the inductive's inversion.  `hπ`, `hm`, `hN` are
carried by the frozen blueprint signature and are not consumed: the equivalence is structural,
and holds at every `(m, N)` including the degenerate ones. -/
theorem clusterUndecided_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π) {m N : ℕ}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (c : ClusterState O m N) :
    ClusterUndecided O π m N c ↔
      IsDrainState c ∨ IsCSState π c ∨
      (∃ (k : ℕ) (z : ResidueField O) (h : IsAlphaState π c k z),
        ClusterUndecided O π m (N - m * k) (alphaChild π c h)) ∨
      (IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O) (h : HasChildAt π c μ k z),
        ClusterUndecided O π μ (N - betaContent c k)
          (betaChild π c h (N - betaContent c k))) := by
  constructor
  · intro h
    cases h with
    | drain c hd => exact Or.inl hd
    | cs c hcs => exact Or.inr (Or.inl hcs)
    | alpha c ha hrec => exact Or.inr (Or.inr (Or.inl ⟨_, _, ha, hrec⟩))
    | beta c hβ hch hrec => exact Or.inr (Or.inr (Or.inr ⟨hβ, _, _, _, hch, hrec⟩))
  · rintro (hd | hcs | ⟨k, z, ha, hrec⟩ | ⟨hβ, μ, k, z, hch, hrec⟩)
    · exact ClusterUndecided.drain c hd
    · exact ClusterUndecided.cs c hcs
    · exact ClusterUndecided.alpha c ha hrec
    · exact ClusterUndecided.beta c hβ hch hrec

/-- **DEC states are DECIDED** — the corollary of the inversion that the N-3 legs consume.  No
rule of H.118 reaches a DEC state: drain and CS are denied by H.111 (c)'s first two conjuncts,
the α witness IS a full-multiplicity child and the β witness IS a child, both denied by its
third.  No hypotheses are needed. -/
theorem not_clusterUndecided_of_isDecState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {π : O} {m N : ℕ}
    {c : ClusterState O m N} (hdec : IsDecState π c) : ¬ ClusterUndecided O π m N c := by
  intro h
  cases h with
  | drain c hd => exact hdec.1 hd
  | cs c hcs => exact hdec.2.1 hcs
  | alpha c ha _ => exact hdec.2.2 ⟨_, _, _, ha.2.2⟩
  | beta c hβ hch _ => exact hdec.2.2 ⟨_, _, _, hch⟩

/-- **The verdict is DRAIN-closed and DEC-free**, in the form H.121's split consumes: on a state
that is neither drain nor CS, being conservatively undecided forces an α or a β witness. -/
theorem exists_witness_of_clusterUndecided {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {π : O} {m N : ℕ}
    {c : ClusterState O m N} (h : ClusterUndecided O π m N c) (h0 : ¬ IsDrainState c)
    (hcs : ¬ IsCSState π c) :
    (∃ (k : ℕ) (z : ResidueField O) (hα : IsAlphaState π c k z),
        ClusterUndecided O π m (N - m * k) (alphaChild π c hα)) ∨
      (IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O) (hch : HasChildAt π c μ k z),
        ClusterUndecided O π μ (N - betaContent c k)
          (betaChild π c hch (N - betaContent c k))) := by
  cases h with
  | drain c hd => exact absurd hd h0
  | cs c hc => exact absurd hc hcs
  | alpha c ha hrec => exact Or.inl ⟨_, _, ha, hrec⟩
  | beta c hβ hch hrec => exact Or.inr ⟨hβ, _, _, _, hch, hrec⟩

end Uniformity.Density.Induction

/-! ## 4. TEETH

### 4.1 Clause (ii) on a toy reader — least fixed point = recursive verdict

`ClusterUndecided` is a LEAST fixed point; `read_cluster` (OM-2 §3.2, the battery's reader) is a
RECURSIVE FUNCTION on the lexicographic measure.  Clause (ii) says the first satisfies the
second's equations; the sharper fact that makes the identification legitimate is that on a
system whose rule graph is well-founded the two objects COINCIDE.  The gate exhibits that on a
ten-state acyclic toy carrying all five bucket labels (`0 = DRAIN`, `1 = CS`, `2 = α`,
`3 = β`, `4 = DEC`; every child has a strictly smaller index, mirroring the measure):

* `toyLfp` iterates H.118's closure ten times from the empty set — the least fixed point;
* `toyRead` is one upward pass — the reader's recursive verdict;
* they are checked EQUAL, `toyLfp` is checked CLOSED (the `⟸` direction), and every `DEC`
  state is checked FALSE in both (`not_clusterUndecided_of_isDecState`).

### 4.2 Clause (i) at the landed conservative closed forms

`hexR`/`hexU` are `OM2_genindb_battery.py`'s `hex3R_ref`/`hex3U_ref` transcribed verbatim — the
battery's `P1(i)` reference implementations of ChapG's landed `hex3R` (`m = 2`) and `hex3U`
(`m = 3`).  The boundary `u(1) = 1` is checked at both battery characteristics, and four
reference values at the plan's largest cells pin the transcription.

⚠ S-1: `hex3R`/`hex3U` are CONSERVATIVE-family closed forms.  Nothing here ties `uCluster` to
the semantic `undecidedCount` (finding F-2). -/

section NumericGate

/-- Bucket labels of the toy: `0 = DRAIN`, `1 = CS`, `2 = α`, `3 = β`, `4 = DEC`. -/
private def toyLbl : List ℕ := [0, 4, 1, 2, 2, 3, 3, 2, 3, 2]

/-- Children of each toy state — always at strictly smaller indices (the measure). -/
private def toyKids : List (List ℕ) :=
  [[], [], [], [1], [0], [1, 3], [1, 4], [5], [3, 5, 7], [8]]

/-- One application of H.118's rule list: DRAIN/CS fire unconditionally, α and β fire from an
undecided child (α's child list is a singleton, so `any` covers both). -/
private def toyStep (S : List Bool) : List Bool :=
  (List.range 10).map fun i =>
    decide (toyLbl.getD i 4 ≤ 1) || (toyKids.getD i []).any fun j => S.getD j false

/-- The least fixed point: ten closure iterations from the empty set. -/
private def toyLfp : List Bool :=
  (List.range 10).foldl (fun S _ => toyStep S) (List.replicate 10 false)

/-- The reader's recursive verdict, by one upward pass (children have smaller indices). -/
private def toyRead : List Bool :=
  (List.range 10).foldl (fun acc i =>
    acc ++ [decide (toyLbl.getD i 4 ≤ 1) ||
      (toyKids.getD i []).any fun j => acc.getD j false]) []

-- clause (ii): the least fixed point IS the reader's verdict
#guard toyLfp == toyRead

-- the pinned verdict, so a silent change to either computation is caught
#guard toyRead == [true, false, true, false, true, false, true, false, false, false]

-- the `⟸` direction: the verdict set is closed under the four rules
#guard toyStep toyLfp == toyLfp

-- `not_clusterUndecided_of_isDecState`: no DEC state is undecided
#guard (List.range 10).all fun i =>
  !(decide (toyLbl.getD i 4 == 4) && toyLfp.getD i false)

-- leastness has bite here: the empty set is NOT closed, so the fixed point is reached by
-- genuine propagation and not by starting at the top
#guard !(toyStep (List.replicate 10 false) == List.replicate 10 false)

/-- The battery's `hex3R_ref` — ChapG `hex3R`, the `m = 2` conservative complement. -/
private def hexR (q M : ℕ) : ℕ :=
  if M = 0 then 0 else if M = 1 then 1
  else q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

/-- The battery's `hex3U_ref` — ChapG `hex3U`, the cubic per-centre conservative complement. -/
private def hexU (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ 3 * k ≤ N - 1)).map fun k =>
        (q - 1) * q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hexR q (N - 3 * k))).sum

-- clause (i), `u(1) = 1`, at both conservative families and both battery characteristics
#guard ([2, 3] : List ℕ).all fun q => (hexR q 1 == 1) && (hexU q 1 == 1)

-- the plan's largest cells, as reference values (`P1(i)`)
#guard (hexR 2 6, hexR 3 5) == (64, 189)
#guard (hexU 2 4, hexU 3 4) == (72, 837)
#guard (hexU 2 6, hexU 3 3) == (1360, 81)

end NumericGate

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uCluster
#print axioms Uniformity.Density.Induction.uClusterNorm
#print axioms Uniformity.Density.Induction.eq_zero_of_mem_map_maximalIdeal_one
#print axioms Uniformity.Density.Induction.clusterState_one_eq
#print axioms Uniformity.Density.Induction.uCluster_one
#print axioms Uniformity.Density.Induction.uClusterNorm_one
#print axioms Uniformity.Density.Induction.clusterUndecided_iff
#print axioms Uniformity.Density.Induction.not_clusterUndecided_of_isDecState
#print axioms Uniformity.Density.Induction.exists_witness_of_clusterUndecided

end AxCheck
