/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R5_EQ2Pass

/-!
# HC1.CL20_rel1Vacuity — the R5 antecedent-vacuity certificate (BP5 CL-20)

**Unit CL-20** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.2 "R5
vacuity (A17's second half)"; Q-4 ADJUDICATED 2026-07-30: keep `EQ2lawIfREL1'`
typed-only-with-record). **FLAGGED NEW PUBLIC THEOREM** (campaign precedent: every
added public name is flagged for orchestrator ratification).

**Informal statement.** `EQ2lawIfREL1' p EQ2law := (∀ K : CarrierPackR p,
REL1Pack p K) → EQ2law` quantifies its antecedent over ALL carrier packs — including
junk packs — so ONE junk pack refutes the antecedent and the def is (vacuously) True
for EVERY consequent. This unit compiles that refutation:
`rel1_forall_refuted : ¬ ∀ K : CarrierPackR p, REL1Pack p K`.

**Proof sketch (~30-line witness).** Build a junk pack violating `DOMStmt'`:
`Hist := Unit`, `Coord := Unit`, `Digit := ℤ`, any trivial `GradedCarrierR` (e.g.
`Coeff := ℤ`, `Gr _ := ℤ`, `w _ := ⊤`-free variant: `w B := ⊤` fails `inγ_detects`
vacuously? — no: pick `w B := if B = 0 then ⊤ else 0`, `inγ γ B := if γ = 0 then B
else 0`-style; the four laws are elementary), TWO CONSTANT LINES with
`(lines () 0).at 0 > (lines () 1).at 0` (MovesC.Line with slope 0 and intercepts
1 > 0), `interiorEnd () i := 1`. Then `DOMStmt'` at H = (), i = 1, m = 0, b = 0
demands `(line 0).at 0 ≤ (line 1).at 0` — false by construction. `REL1Pack` includes
`DOMStmt'` (third conjunct), so `∀ K, REL1Pack p K` fails at the junk pack.

**HEADER RECORD on `EQ2lawIfREL1'` (the A17 DEFECT-2-adjacent scoping, per Q-4).**
* `EQ2lawIfREL1'` is TYPED-ONLY: it is a statement def, never asserted, and — grep
  verified at HEAD 2026-07-30 by this unit's E-phase writer — has ZERO consumers
  outside its own file `R5_EQ2Pass.lean` (likewise `REL1Pack`; the only other mention
  is the HC1/MANIFEST.json record). This theorem documents that its antecedent is
  REFUTABLE, hence any future consumer instantiating it as stated obtains only a
  vacuous truth.
* Whether to re-scope the antecedent (e.g. to Gr-pinned packs, or an ∃-form over the
  real instance of R6) is a MovesR-UNPARKING design question, explicitly NOT decided
  here (adjudication Q-4: defer; keeping this area self-contained).
* `R5_EQ2Pass.lean` itself is UNTOUCHED (statement fence; new-files-only discipline);
  this file carries the record instead.

**Deps.** R1-R5 statement defs as-is. Independent of CL-06's LSTStmt' (i-b) edit —
the junk pack breaks the DOM conjunct, which CL-06 does not touch — but RE-VERIFY
after CL-06 lands (the R1 rebuild ripples through R5's imports). difficulty:
routine-opus. Size: ~40. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- The junk graded carrier: weight `⊤` everywhere, class map `≡ 0`. The four
`GradedCarrierR` laws hold trivially (`inγ_detects` is VACUOUS — `w B = ↑γ` is never
`⊤ = ↑γ`). -/
private def junkGR (p : ℕ) [Fact p.Prime] : GradedCarrierR p where
  Coeff := ℤ
  Gr := fun _ => ℤ
  w := fun _ => ⊤
  inγ := fun _ _ => 0
  w_add := fun _ _ => le_top
  inγ_add := fun _ _ _ _ _ => (add_zero 0).symm
  inγ_kills := fun _ _ _ => rfl
  inγ_detects := fun _ _ h => absurd h (by simp)

/-- The junk carrier pack: two constant lines `line 0 ≡ 1`, `line k ≡ 0` (k ≠ 0),
`interiorEnd ≡ 1`. Refutes `DOMStmt'` at `H = ()`, `i = 1`, `m = 0`, `b = 0`:
`(line 0).at 0 = 1 > 0 = (line 1).at 0` while `m < i` and `b < interiorEnd`. -/
private def junkPackR (p : ℕ) [Fact p.Prime] : CarrierPackR p where
  G := junkGR p
  Hist := Unit
  Coord := Unit
  Digit := ℤ
  kIdx := fun _ => 0
  ht := fun _ _ => 0
  blk := fun _ _ => 0
  lvl := fun _ _ _ => ∅
  slotCoeff := fun _ _ _ => 0
  aDim := fun _ _ _ => 0
  lines := fun _ k => if k = 0 then ⟨1, 0⟩ else ⟨0, 0⟩
  blockEdge := fun _ _ => 0
  interiorEnd := fun _ _ => 1
  window := fun _ _ => True
  mono := fun _ _ => 0
  floorB := fun _ _ => 0

/-- **CL-20 (FLAGGED new public theorem)**: the ∀-instances antecedent of
`EQ2lawIfREL1'` is REFUTED — a junk carrier pack (two constant lines with the wrong
order at the interior, `interiorEnd = 1`) violates `DOMStmt'`, hence `REL1Pack`.
Consequently `EQ2lawIfREL1' p EQ2law` holds vacuously for every `EQ2law`: the def is
typed-only and any consumer must re-scope its antecedent first (Q-4, deferred to the
MovesR unparking). -/
theorem rel1_forall_refuted (p : ℕ) [Fact p.Prime] :
    ¬ ∀ K : CarrierPackR p, REL1Pack p K := by
  intro h
  have hdom := (h (junkPackR p)).2.2.1
  have hbad := hdom () 1 0 0 (by norm_num) (by simp [junkPackR])
  simp only [junkPackR, MovesC.Line.at] at hbad
  norm_num at hbad

end LeanUrat.HC1

#print axioms LeanUrat.HC1.rel1_forall_refuted
