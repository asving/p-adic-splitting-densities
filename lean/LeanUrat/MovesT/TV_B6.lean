/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_B2

/-! # TV-B6 — `treeN_stable_of_inputs`: the six-clause fiberAt transfer assembled

BRIDGE CAMPAIGN unit **TV-B6** (area BP3, cluster B; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.B + §4). E-PHASE SKELETON —
statement pinned, body `sorry`.

INFORMAL STATEMENT: the TV-B2 stability-input bundle implies TREE-N cross-level
stability — for every N ≥ Tr.thr n and working level N' ≥ N, two boxes agreeing
on the level-<N block (the first n·N coordinates) have equal `fiberAt` truth
values. This is the note's stability theorem (MOVES 7559–7574) REDUCED to the
typed owner inputs; TV-B7 executes the ratified Q2 restatement from it.

PROOF SKETCH (clause-by-clause, template = E5's six-clause reconstruction
`hconv`, E5_rootSplit.lean:453-510; both directions by the symmetry of the
agreement hypothesis):
* fix N ≥ Tr.thr n, N' ≥ N (with N₀ ≤ N'), boxes x =_{<n·N} x'; specialize
  `SI.child_cyl N hN N' h' hNN'` pointwise at (x, x') to get the TV-B3/B5 core
  hypothesis `hchild`; get `hmem` from TV-B3's core lemma;
* clause (i): `tv_b5_clause_i_transfer` under the ↔ (backward direction uses
  arbitrary-H determinacy — quantifier option α, TV-B2's R8 flag);
* clause (ii): per maximal chain, the leaf dichotomy transfers — the (τ-irr)
  disjunct is x-free except `¬ Tr.nsLeaf H`/leafV ties (x-free), the (τ-ns)
  disjunct via `tv_b5_nsHalts_transfer` (+ x-free leafV/nsVerdict values);
* clause (iii): `Tr.henV = henPayload (χat N') ·` via `tv_b4_henPayload_cyl`
  at `SI.chart_pin N' h'` and 1 ≤ N (`VTree.thr` is `… ⊔ 1`, Defs.lean:734);
* clause (iv): `tv_b5_duty_transfer` per non-maximal chain;
* clause (v): x-free (typemult only);
* clause (vi): the head/track-degree roster identity via `tv_b4_factors_cyl`
  (the filter and counts are functions of the factor multiset).

E-PHASE FINDING carried from TV-B1/TV-B2 (recorded): the statement binds the
unguarded tower chart χat, so it is VACUOUSLY derivable at n ≥ 1 until the
Q2/B7 guard repair — the honest content of this unit lives in the
clause-by-clause assembly over TV-B3/B4/B5's guard-free cores, which survives
the guard repair verbatim. Do NOT close this sorry by the vacuity (the TV-B1
soundness note; honest-sorries discipline).

deps: B3, B4, B5 (+ B2 for the bundle type). Consumed by: TV-B7. difficulty:
hard-fable, ~80 lines. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

/-- **TV-B6 `treeN_stable_of_inputs`** — the typed stability-input bundle
(TV-B2, owner HC-2/D4R0K) implies TREE-N cross-level stability
(`TreeNStable`, Defs.lean:1624). The six-clause transfer assembled from
TV-B3 (mem), TV-B4 (redPoly/henPayload/factor roster), TV-B5
(NsHalts/PrunedMem/duties); clause (v) x-free. -/
theorem treeN_stable_of_inputs {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N')) (Tr : VTree p F)
    (SI : StableInputs Tat χat Tr) :
    TreeNStable Tat χat Tr := by
  sorry

end LeanUrat.MovesT
