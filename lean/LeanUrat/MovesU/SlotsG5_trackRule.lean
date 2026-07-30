/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-G5 — Slot_trackRule FORMULATION SKELETON (bridge BP1, §3.8)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (the
trackRule row) + §4 group G (IB-G5: "Slot_trackRule (MovesX vocabulary; must be
CONSISTENT with K7.track_restarts's (t3) — same Pop counters). ADJ→H") and
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (BP1 Q5).

THE RESERVED PARAMETER (U10_theoremU.lean:71–73, verbatim): "`trackRule` —
CL-7a's (t1)/(t2) key/branch recognitions + the (c1) assignment map (owner [4];
the (t3) restart face and the L(n) bound are typed at `K7.track_restarts`)" —
one of the thirteen wave-4-boundary bare-Prop parameters (UNPINNED pending this
carrier).  DefsLedger's `Cl7Kernel.track_restarts` docstring records the exact
residue: "The (t1)/(t2) key/branch recognitions and the (c1) assignment MAP have
no X carrier — they ride `theoremU`'s bare `trackRule` parameter."

FORMULATION TARGET (H-phase; deps: the built MovesX corpus via `KernelCarriers`
+ `Cl7Kernel`; owner [4]; note display CL-7a (t1)/(t2)+(c1)): over
`MovesX.XHistory n` (MovesX/Defs.lean:57) —
* (t1)/(t2): the KEY and BRANCH recognition predicates on history nodes — which
  continuing nodes are key-track (genuine T1/T2 increments) vs branch-track,
  recognized from the node data (`rowOf`/`isIncrement`/`popOf?` vocabulary,
  MovesX/Defs.lean:69–116);
* (c1): a `trackOf` ASSIGNMENT MAP sending each continuing node of each stratum
  history to its track, TOTAL on continuing nodes and CONSISTENT WITH
  `K7.track_restarts`'s (t3) face — the SAME `MovesX.Pop` counters
  (`countPop H .recT1`, `countPop H .t4`, `countPop H .incT12`,
  MovesX/Defs.lean:109–119): the recognitions must aggregate to the populations
  (t3) bounds by `K7.L` and `zero_gain`/`genuine_bound` budget by
  `K7.Dden`/`K7.wstar` (DefsLedger.lean:199–217) — no private re-count.
The track carrier itself (the track index type + `trackOf`) has NO built
vocabulary — the H-phase designs it as bound data INSIDE the Prop (per §3.8's
"stated over built or newly-designed carrier vocabulary").

E-PHASE DIVISION OF LABOR (as in IB-G2, per §3.8/R9): body `sorry`; the
displayed Prop is the ADJ→H deliverable behind the Q5 Codex-audit gate.
NON-VACUITY DUTY (IB-G11b): `example : ¬ Slot_trackRule degenerate…` — e.g.
FALSE for an assignment that re-counts populations inconsistently with (t3).
CLOSURE MANIFEST DUTY (IB-G12): every identifier → built decl path.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
H-PHASE RESOLUTIONS (2026-07-30, cluster BP1-P10-slots; against the (TRK-RULE)
display, MOVES_2026-07-24.md 12988–13004, and SQ.0(c1) 12943–12947; FLAGGED for
the Q5 Codex audit):
* (h1) THE THREE RECOGNITIONS, per (TRK-RULE) "recognized per node from
  move-species cell data alone":
  - (t3) LADDER RESTART is PINNED to the SAME `MovesX.Pop` counters as
    `K7.track_restarts` (`popOf? = some .recT1 ∨ popOf? = some .t4`) — the charge's
    "no private re-count" clause, satisfied by definition;
  - (t2) BRANCH OPENING is PINNED to the carried tree (`KC.XF.ctx p`): one opening
    per (ancestor c of b, member d ∈ children c NOT an ancestor of b) — the
    display's "each member beyond the designated continuing one opens its own
    track", the designated member being the one on b's own path.  An explicit
    `Set.Finite` conjunct keeps an infinite sibling family from slipping under the
    budget via `Set.ncard`'s junk value 0;
  - (t1) KEY CREATION has NO carrier (the §B2-DEF carry-algebra key vocabulary is
    unbuilt) — it is the ONE ∃-bound recognition, a per-node predicate
    (`XNode n → Prop`, so it reads node data alone); declaring openings is priced
    against the SAME `K7.L` budget, so the freedom cannot inflate the track count.
* (h2) (c1) THE ASSIGNMENT MAP: every zero-gain move (continuing, not a genuine
  T1/T2 increment — SQ.0(c)'s d_zero population) is assigned an opening event of
  its own history AT OR BEFORE it ("the open ladder its D.10 increment extends";
  openings on this branch's history are the (t1)/(t3) events — (t2) events open
  the OTHER members' tracks).  The monotone-climb duty of the assigned ladder is
  (c2) = `Slot_dnLattice`'s conjunct, not restated here (CL-7a/CL-7b split).
* (h3) BUDGET: #(t1) + #(t2) + #(t3) ≤ K7.L per stratum history — (TRK-RULE)'s
  probe count against TRACK-COUNT's L(n), the SAME constant `track_restarts`
  bounds its (t3) face by.
NON-VACUITY (IB-G11b's duty): FALSE at a degenerate instance whose carried tree
is too bushy — a stratum branch with more than `K7.L` non-designated siblings
(the PINNED (t2) count alone breaks the budget, while `track_restarts` stays
satisfiable: it bounds only the (t3) counters).
-/

namespace LeanUrat.MovesU

/-- IB-G5 — **`Slot_trackRule`** (CL-7a (t1)/(t2)+(c1), owner [4]): the key/branch
recognition predicates on `MovesX.XHistory` + the (c1) `trackOf` assignment map,
CONSISTENT with `K7.track_restarts`'s (t3) face — same `MovesX.Pop` counters (see
the file header for the formulation target).  H-phase fills the displayed Prop;
Codex audit before any consumer (Q5). -/
def Slot_trackRule (n : ℕ) {C : UCarriers n} (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (b : (KC.XF.ctx p).Branch f),
    f ∉ MovesX.discZero n p →
    (KC.XF.gmn p).inStratum f ((KC.XF.ctx p).hist b) →
    -- (h1)(t2): the branch-opening events are the carried tree's own data —
    -- finitely many non-designated members over the ancestors of b:
    {cd : (KC.XF.ctx p).Branch f × (KC.XF.ctx p).Branch f |
        MovesX.isPrefixB (KC.XF.ctx p) cd.1 b ∧
        cd.2 ∈ (KC.XF.ctx p).children cd.1 ∧
        ¬ MovesX.isPrefixB (KC.XF.ctx p) cd.2 b}.Finite ∧
    -- (h1)(t1): the ONE designed recognition — a per-node key-creation predicate:
    ∃ (keyRec : MovesX.XNode n → Prop)
    -- (h2)(c1): the assignment map on this history's positions:
      (trackOf : Fin ((KC.XF.ctx p).hist b).length →
        Fin ((KC.XF.ctx p).hist b).length),
      -- (h3) the (TRK-RULE) probe count within TRACK-COUNT's budget:
      {i : Fin ((KC.XF.ctx p).hist b).length |
          keyRec (((KC.XF.ctx p).hist b).get i)}.ncard
        + {cd : (KC.XF.ctx p).Branch f × (KC.XF.ctx p).Branch f |
            MovesX.isPrefixB (KC.XF.ctx p) cd.1 b ∧
            cd.2 ∈ (KC.XF.ctx p).children cd.1 ∧
            ¬ MovesX.isPrefixB (KC.XF.ctx p) cd.2 b}.ncard
        + {i : Fin ((KC.XF.ctx p).hist b).length |
            MovesX.popOf? (((KC.XF.ctx p).hist b).get i) = some MovesX.Pop.recT1 ∨
            MovesX.popOf? (((KC.XF.ctx p).hist b).get i) = some MovesX.Pop.t4}.ncard
        ≤ K7.L ∧
      -- (h2) totality of (c1) on the zero-gain moves, charged to an OPEN ladder:
      ∀ i : Fin ((KC.XF.ctx p).hist b).length,
        (((KC.XF.ctx p).hist b).get i).continuing = true →
        MovesX.popOf? (((KC.XF.ctx p).hist b).get i) ≠ some MovesX.Pop.incT12 →
        (trackOf i : ℕ) ≤ (i : ℕ) ∧
        (keyRec (((KC.XF.ctx p).hist b).get (trackOf i)) ∨
          MovesX.popOf? (((KC.XF.ctx p).hist b).get (trackOf i))
            = some MovesX.Pop.recT1 ∨
          MovesX.popOf? (((KC.XF.ctx p).hist b).get (trackOf i))
            = some MovesX.Pop.t4)

end LeanUrat.MovesU
