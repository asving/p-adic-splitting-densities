/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.Defs

/-! # TV-B2 — the TREE-N stability-input bundle `StableInputs`, TYPED

BRIDGE CAMPAIGN unit **TV-B2** (area BP3, cluster B; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.B + §4). E-PHASE STATEMENT MODULE
(carrier only — no sorries; the E-DEV-9 pattern "carrier typed in the consuming
unit", landed in a NEW file per the E-phase rules; B7's ratified Q2 execution
[named-hypothesis option 2] threads it into `treeN_stable`/`TreeNStableStmt`/
`RS1GivenPackage.tree_n` at prover time).

OWNER: **HC-2/D4R0K**, quoting MOVES 7566–7570 — the note's declared proof
inputs for TREE-N stability: "per site: the joint cell's literal system at its
B(iii) level; per branch: D4R.4's exact level-N realization; per leaf: TB-CAP's
level-N_V cylinders". The bundle types exactly the three level-determinacy
inputs of blueprint §3.B: (S-chart) = `chart_pin`, (S-child) = `child_cyl`;
(S-mem) is DERIVED from (S-child) by TV-B3 via the TV-B8 snoc eliminator.

FIELD (iii) `ns_cyl` — DROPPED, RECORDED (per the blueprint's own typing
instruction "if NsHalts is mem/child-composed, this field is DERIVED and
dropped"): verified at Defs.lean:223-225, `NsHalts T o x` IS mem/child-composed
— `T.mem o x ∧ ∀ ν, ¬ T.child o ν x` — so its transfer is the And-congruence of
the B3 mem transfer (from `child_cyl`) with `child_cyl` itself at `o := some H`.
No separate field.

STATEMENT RESOLUTIONS (recorded):
* the blueprint sketch writes `chart_pin : ∀ N' h b, ((χat N' h) b : ℕ) < n`,
  but the corpus chart carrier `χat : ∀ N', Fin n → Fin (n * N')`
  (Defs.lean:1638, E11:92) takes NO tower-bound argument; the `h` binder is
  kept as a GUARD on the quantifier (`N₀ ≤ N'`) — the minimal resolution that
  preserves the sketch's binder roster and demands nothing below the tower base;
* `child_cyl`'s threshold row mirrors `TreeNStable`'s own quantifier shape
  (Defs.lean:1624-1631): ∀ N ≥ Tr.thr n, ∀ N' ≥ N (with N₀ ≤ N'), agreement on
  the first n·N coordinates.

QUANTIFIER-STRENGTH FLAG (risk R8 — BOTH options presented, per the blueprint's
instruction that this docstring return the choice to the orchestrator):
* AS TYPED (option α): `child_cyl` quantifies over ALL (o, ν) — every history
  state and node — at every threshold-passing level. This is what the B6
  assembly needs verbatim (clause (i) of `fiberAt` is an ↔ whose BACKWARD
  direction needs mem determinacy for ARBITRARY H, not just Tr.chains members).
* Option β (weaker, if the HC-2 owner cannot discharge α): realizable-H-only
  transfer + a separate no-stray-history law; B6 would then need the extra step
  recovering arbitrary-H determinacy from no-stray. The bundle is typed at α;
  re-scoping is a B7-time decision.

E-PHASE FINDING (inherited from TV-B1, recorded here because it hits this
carrier too): the unguarded `χat` type is uninhabited at n ≥ 1 (N' = 0 forces
`Fin n → Fin 0`; `tv_b1_chart_carrier_uninhabited`, TV_B1.lean) — so ANY
consumer binding this bundle's `χat` at n ≥ 1 is vacuous until the Q2/B7 repair
also guards χat. `StableInputs` itself stays well-typed either way and its
field shapes survive the guard repair verbatim.

deps: none. Consumed by: TV-B3/B4/B5/B6 (the transfer chain), TV-B7 (the
ratified restatement). difficulty: routine-opus, ~30 lines. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

/-- **TV-B2 `StableInputs`** — the typed stability-input bundle for TREE-N
cross-level stability (owner HC-2/D4R0K, MOVES 7566–7570; blueprint §3.B):

* `chart_pin` = (S-chart): above the tower base the chart lands in the LEVEL-1
  block — `(χat N' b : ℕ) < n` — so `redPoly`/`henPayload`/the factor roster
  read only level-<N digits for every N ≥ 1 (TV-B4's input);
* `child_cyl` = (S-child): at every threshold-passing pair N ≤ N', the child
  relation is a level-<n·N cylinder event, uniformly in the site (o, ν) —
  (S-mem) follows by TV-B3 (snoc induction via TV-B8), and the NsHalts
  transfer is derived (NsHalts is mem/child-composed; field dropped, recorded
  in the module docstring).

Carried as the NAMED warranted hypothesis of `treeN_stable` per the ratified
Q2 ruling (option 2) — B7 executes; NEVER proved in this corpus. -/
structure StableInputs {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N')) (Tr : VTree p F) : Prop where
  chart_pin : ∀ (N' : ℕ), N₀ ≤ N' → ∀ b : Fin n, ((χat N' b : ℕ)) < n
  child_cyl : ∀ (N : ℕ), Tr.thr n ≤ N →
    ∀ (N' : ℕ) (h' : N₀ ≤ N'), N ≤ N' →
    ∀ (o : Option (History p F)) (ν : Node p F) (x x' : Box p (n * N')),
      (∀ c : Fin (n * N'), (c : ℕ) < n * N → x c = x' c) →
      ((Tat N' h').child o ν x ↔ (Tat N' h').child o ν x')

end LeanUrat.MovesT
