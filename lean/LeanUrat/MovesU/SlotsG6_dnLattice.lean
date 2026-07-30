/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-G6 — Slot_dnLattice FORMULATION SKELETON (bridge BP1, §3.8)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (the
dnLattice row) + §4 group G (IB-G6: "Slot_dnLattice (K7.Dden-keyed). ADJ→H") and
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (BP1 Q5).

THE RESERVED PARAMETER (U10_theoremU.lean:74–77, verbatim): "`dnLattice` —
CL-7b's key-weight lattice duty (all key weights in (1/D(n))·ℤ, candidate
D(n) | n!) + the per-node strict-increment sub-claim (owner [4]; the D(n)
constant and the budget/genuine bounds are typed at `K7`)" — one of the thirteen
wave-4-boundary bare-Prop parameters (UNPINNED pending this carrier).
DefsLedger's `Cl7Kernel.zero_gain` docstring records the exact residue: "the
weight-lattice duty (all key weights in (1/D(n))·ℤ, candidate D(n) | n!) has no
key-weight carrier — bare `dnLattice` parameter"; `genuine_bound`'s docstring
adds "the per-node strict-ledger-increment sub-claim itself is part of
`dnLattice`'s owner residue, disclosed at U10."

FORMULATION TARGET (H-phase; deps: `Cl7Kernel` + the MovesX Pop/dTotal
vocabulary; owner [4]; note display CL-7b lattice + strict increment), the
three-conjunct shape keyed to `K7`'s p-UNIFORM constants:
* (lattice) every KEY WEIGHT of every stratum history lies in `(1 / K7.Dden)·ℤ`
  — the key-weight ledger has NO built carrier (MovesX histories carry
  `XNode`/`Pop`/`dTotal` populations, MovesX/Defs.lean:104–119, but no per-node
  weight): the H-phase designs the weight carrier as bound data INSIDE the Prop
  (per §3.8's "newly-designed carrier vocabulary"), keyed so that `K7.wstar`'s
  budget (`zero_gain`, DefsLedger.lean:210) prices the SAME weights;
* (denominator) `K7.Dden ∣ n.factorial` — the note's candidate D(n) | n!;
* (strict increment) per-node STRICT ledger increment at every genuine
  (T1/T2-increment, `MovesX.Pop.incT12`) continuing node — the sub-claim whose
  aggregate face is `K7.genuine_bound` (`countPop … .incT12 ≤ n·N`,
  DefsLedger.lean:215): the per-node strictness must IMPLY the typed aggregate,
  never contradict it.

E-PHASE DIVISION OF LABOR (as in IB-G2, per §3.8/R9): body `sorry`; the
displayed Prop is the ADJ→H deliverable behind the Q5 Codex-audit gate.
NON-VACUITY DUTY (IB-G11b): `example : ¬ Slot_dnLattice degenerate…` — e.g.
FALSE at a weight assignment off the (1/Dden)-lattice or a non-strict increment.
CLOSURE MANIFEST DUTY (IB-G12): every identifier → built decl path.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
H-PHASE RESOLUTIONS (2026-07-30, cluster BP1-P10-slots; against SQ.0(c2)/(d),
MOVES_2026-07-24.md 12947–12961, and the D(n) duty 12962–12964; FLAGGED for the
Q5 Codex audit):
* (h1) THE KEY-WEIGHT CARRIER is ∃-bound per stratum branch (`w : positions → ℚ`)
  with the note's three displayed duties as its LAWS: (lattice) `w·Dden ∈ ℤ`;
  (budget keying) `0 ≤ w ≤ w*(N)` on threshold-≤-N branches — the SAME weights
  `K7.zero_gain`'s budget `L·D(n)·w*(N)` prices; (climb, = SQ.0(c2)) each
  zero-gain move strictly increases ITS OWN track's weight by ≥ 1/D(n) (D.10's
  strict climb).  The climb needs a track handle, so a track labelling rides in
  the ∃ with the zero-gain moves confined to ≤ K7.L tracks — the (c1)-count face
  duplicated BY NECESSITY ((c1)/(c2) are one display; the opening-recognition
  side lives at `Slot_trackRule`, the CL-7a/CL-7b split).  Jointly these force
  d_zero ≤ L·(D(n)·w*(N) + 1) — the zero_gain aggregate's mechanism, per track.
* (h2) (denominator) `K7.Dden ∣ n!` — the note's "candidate D(n) | n!, underived"
  duty, stated at K7's own p-uniform constant.
* (h3) (strict increment) THE PREFIX LEDGER: SQ.0(d)'s A(η) is ∃-bound as
  `A : Fin (len+1) → ℕ` with A(root) = 0, monotone along the history, STRICTLY
  increasing at every genuine (T1/T2-increment, `Pop.incT12`) node, and
  A(full history) ≤ n·N — the FLAGGED-OPEN sub-claim "every genuine node strictly
  increments the ledger" plus Theorem C's forcing A ≤ nN.  This ∃ IMPLIES the
  typed aggregate `K7.genuine_bound` (#genuine ≤ A(end) ≤ n·N), never
  contradicts it — the header's consistency duty.
NON-VACUITY (IB-G11b's duty): FALSE at any degenerate K7 with `Dden ∤ n!`
(conjunct (h2); such K7 exist — the aggregate proof fields are vacuously
dischargeable at an empty-strata instance with junk constants).
-/

namespace LeanUrat.MovesU

/-- IB-G6 — **`Slot_dnLattice`** (CL-7b lattice + strict increment, owner [4]):
all key weights in `(1/K7.Dden)·ℤ`, `K7.Dden ∣ n!`, and the per-node
strict-ledger-increment sub-claim — over the MovesX Pop/dTotal vocabulary with a
newly-designed key-weight carrier bound inside the Prop (see the file header).
H-phase fills the displayed Prop; Codex audit before any consumer (Q5). -/
def Slot_dnLattice (n : ℕ) {C : UCarriers n} (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) : Prop :=
  -- (h2) the D(n) denominator duty:
  K7.Dden ∣ Nat.factorial n ∧
  -- per stratum branch at decision threshold ≤ N:
  ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (b : (KC.XF.ctx p).Branch f) (N : ℕ),
    f ∉ MovesX.discZero n p → (KC.XF.ctx p).threshold b ≤ N →
    ∃ (w : Fin ((KC.XF.ctx p).hist b).length → ℚ)       -- key weights (h1)
      (trk : Fin ((KC.XF.ctx p).hist b).length → ℕ)     -- track labels (h1)
      (A : Fin ((KC.XF.ctx p).hist b).length.succ → ℕ), -- prefix ledger (h3)
      -- (h1)(lattice) every key weight in (1/Dden)·ℤ:
      (∀ i, ∃ z : ℤ, w i * (K7.Dden : ℚ) = (z : ℚ)) ∧
      -- (h1)(budget keying) the SAME weights w*(N) prices:
      (∀ i, 0 ≤ w i ∧ w i ≤ (K7.wstar N : ℚ)) ∧
      -- (h1)(climb, SQ.0(c2)) zero-gain moves strictly climb their own track
      -- by ≥ 1/D(n):
      (∀ i j : Fin ((KC.XF.ctx p).hist b).length, i < j → trk i = trk j →
        ((((KC.XF.ctx p).hist b).get i).continuing = true ∧
          MovesX.popOf? (((KC.XF.ctx p).hist b).get i)
            ≠ some MovesX.Pop.incT12) →
        ((((KC.XF.ctx p).hist b).get j).continuing = true ∧
          MovesX.popOf? (((KC.XF.ctx p).hist b).get j)
            ≠ some MovesX.Pop.incT12) →
        w i + 1 / (K7.Dden : ℚ) ≤ w j) ∧
      -- (h1)(c1-count face) the zero-gain moves ride ≤ L(n) tracks:
      {t : ℕ | ∃ i : Fin ((KC.XF.ctx p).hist b).length,
          ((((KC.XF.ctx p).hist b).get i).continuing = true ∧
            MovesX.popOf? (((KC.XF.ctx p).hist b).get i)
              ≠ some MovesX.Pop.incT12) ∧ trk i = t}.ncard ≤ K7.L ∧
      -- (h3)(strict increment) the prefix ledger: root 0, monotone, strict at
      -- every genuine node, and bounded by SQ.0(d)'s n·N:
      A 0 = 0 ∧
      (∀ i : Fin ((KC.XF.ctx p).hist b).length, A i.castSucc ≤ A i.succ) ∧
      (∀ i : Fin ((KC.XF.ctx p).hist b).length,
        MovesX.popOf? (((KC.XF.ctx p).hist b).get i)
          = some MovesX.Pop.incT12 → A i.castSucc < A i.succ) ∧
      A (Fin.last _) ≤ n * N

end LeanUrat.MovesU
