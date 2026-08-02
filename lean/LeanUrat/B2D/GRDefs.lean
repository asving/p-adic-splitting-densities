/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesC.Defs
import LeanUrat.MovesGr.Defs
import LeanUrat.HC2.Defs

/-!
# B2D/GRDefs — the GRADED-READ definitional layer  [B2DEF_LEAN unit E1; wave E]

Blueprint: `lean/blueprints/B2DEF_LEAN_2026-08-08.md` §4 + §5 (unit E1).
moves_ref: §B2-DEF D.0 (P1)–(P4), D.5 (MOVES :2266–2277). deps: none (wave E).
difficulty: easy (definitions + compile probe).

**E-PHASE NOTE (the sanctioned exception to the no-sorry rule).** This module and
its `GR1..GR4`/`TD*` fan-out are the B2DEF_LEAN campaign's E-phase skeleton: the
definitional layer plus theorem statements whose `sorry` bodies are the campaign's
OPEN-GOALS LEDGER, tracked unit-by-unit by the blueprint (each `sorry` carries its
unit ID). No consumer may cite a sorry-bodied statement as evidence.

## What this file carries

* `ReadHyps ν` — the displayed wiring pack of blueprint §4: the hypotheses the D.5
  EQUAL WEIGHTS / RESIDUAL computation consumes that `IsNodeLift`'s fields do NOT
  carry. §4 displays four groups (`hscale`, `hbez`, `hψ`, `hRlaws`); per the §4
  instruction ("this signature is a design display, not frozen — E-PHASE PROBE
  REQUIRED") the groups are FLATTENED to per-fact fields so GR-0's supplier map is
  per-field. FLAGGED deviations from the §4 display, all sanctioned-respelling
  class:
  - `hbez`/`hbezCanon` render "the Stage T-vector/Bézout pins" at the NODE's own
    recorded read pair (`Node.hbez`/`Node.hbezCanon` — the F10 adjudication: D.8's
    normalization consumes the READ's `(s, t)`, never the frame's `(σ.s, σ.t)`).
  - `hψ*` renders the ψ conditions (monic, irreducible, degree = g, `coeff 0 ≠ 0`).
  - `hR*` renders "the parent σ.R product/tie laws the computation consumes"
    explicitly (probe result: they are `Stage` FIELDS at the parent — see GR-0).
  - E1's "(S6b)/(I-aug) range fields" — PROBE RESULT, FLAGGED: the (S6b) clause is
    already a `Stage` field at the parent (`ν.σ.hS6b`), and no GR-1..GR-4 statement
    of this decomposition consumes an (I-aug) range fact (GR reads a GIVEN lift; it
    builds nothing). No field is added; if a wave-2a prover finds a range fact
    load-bearing, it is added here with a supplier-map row, never smuggled.
* `readPos` — the slot position functional pos(κ) of GR-2's (SL-dev) display, in
  the parent normalization forced by the corpus laws (`Stage.hS5` positions +
  `Stage.hRΦ`): pos(κ) = −σ.t·wPrev(t_κ) + (e·κ)·σ.s.
* the D.8 normalization exponent m̂ = −t·h·g is NOT rebuilt: it is the existing
  `MovesC.Node.mhat` (reuse census §1 discipline — cite, don't rebuild).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesGr

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **The displayed wiring pack of blueprint §4** — what the D.5 EQUAL WEIGHTS +
RESIDUAL displays consume at the parent stage `ν.σ` BEYOND `IsNodeLift`'s own
fields. Supplier-or-hypothesis per field: see `GR0_readHyps.lean` (the E-gate) for
the supplier map. [R1-C2 fold: `IsReadLift` alone does NOT imply equal weights —
the slot total `ν.h·(g−k) + e·k·σ.w(σ.Φ)` is k-free iff `hscale` holds; that law
is not an `IsNodeLift` field and rides HERE, displayed.] -/
structure ReadHyps (ν : Node p F) : Prop where
  /-- THE equal-weights scale law (D.5's own bookkeeping h′ = e·h, h = w(Φ)):
      the read's slope numerator is the stride times the parent key weight.
      GR-0 probe verdict: DISPLAYED-HYPOTHESIS (no single-node wiring decl
      supplies it; the history-level slope law of `HistoryCoherent` is the
      wave-2 supplier candidate — see GR-0's docstring). WAVE-2a (2026-08-02):
      supplier PROVED at interior coherent reads (`GR0b.readHyps_of_history`,
      via `child_e`/`child_h`); moreover with `Node.hcop` this field FORCES
      `ν.e = 1` (`GR0b.readHyps_e_eq_one`) — it is the compiled e = 1/[NR]
      recording perimeter, false at steep recorded reads by design. -/
  hscale : (ν.h : ℤ) = (ν.e : ℤ) * ν.σ.w ν.σ.Φ
  /-- the read's own Bézout pin `e·s + h·t = 1` (behind m̂ = −t·h·g, D.8).
      SUPPLIED-BY `Node.hbez`. -/
  hbez : (ν.e : ℤ) * ν.s + (ν.h : ℤ) * ν.t = 1
  /-- the canonical Bézout window `0 ≤ t < e`. SUPPLIED-BY `Node.hbezCanon`. -/
  hbezCanon : 0 ≤ ν.t ∧ ν.t < (ν.e : ℤ)
  /-- ψ monic. SUPPLIED-BY `Node.hψmonic`. -/
  hψmonic : ν.ψ.Monic
  /-- ψ irreducible. SUPPLIED-BY `Node.hψirr`. -/
  hψirr : Irreducible ν.ψ
  /-- ν.g = deg ψ. SUPPLIED-BY `Node.hψdeg`. -/
  hψdeg : ν.ψ.natDegree = ν.g
  /-- `ψ.coeff 0 ≠ 0`. GR-0 probe verdict: DISPLAYED-HYPOTHESIS (recentering
      nodes have ψ = z − c̃ with no corpus pin `c̃ ≠ 0`). WAVE-2a CORRECTION
      (2026-08-02): SUPPLIED at every node — `GR0b.node_hψ0` derives it from
      `hOrd` + `hμ` + `hpat0` + `hRanch` (the anchored-residual provenance);
      the field stays displayed for interface stability (§4 frozen), with the
      supplier discharging it at every use site. -/
  hψ0 : ν.ψ.coeff 0 ≠ 0
  /-- parent residual multiplicativity. SUPPLIED-BY `Stage.hRmul` at `ν.σ`. -/
  hRmul : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → ν.σ.R (f * g) = ν.σ.R f * ν.σ.R g
  /-- parent lower-weight-wins tie. SUPPLIED-BY `Stage.hRlt` at `ν.σ`. -/
  hRlt : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
    ν.σ.w f < ν.σ.w g → ν.σ.R (f + g) = ν.σ.R f
  /-- parent equal-weight additivity. SUPPLIED-BY `Stage.hRadd` at `ν.σ`. -/
  hRadd : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
    ν.σ.w f = ν.σ.w g → ν.σ.w (f + g) = ν.σ.w f → ν.σ.R (f + g) = ν.σ.R f + ν.σ.R g
  /-- the pinned parent key residual `R Φ = T^{σ.s}`. SUPPLIED-BY `Stage.hRΦ` at `ν.σ`. -/
  hRΦ : ν.σ.R ν.σ.Φ = LaurentPolynomial.T ν.σ.s

/-- **The slot position functional pos(κ) of GR-2's per-κ (SL-dev) display**, in
the parent-stage normalization the corpus laws force: `σ.R (t_κ)` sits at position
`−σ.t·wPrev(t_κ)` (the `IsNodeLift`/(S5) field) and `σ.R (Φ^{e·κ}) = T^{e·κ·σ.s}`
(`Stage.hRΦ` + multiplicativity), so
`pos(κ) = −σ.t·wPrev(t_κ) + (e·κ)·σ.s`.
The blueprint's affine/unit-step prediction for pos (D.3(c) stride at the read) is
GR-2's `GR2_posStep` STATEMENT, gated by the §7 N-GR1 falsifier family — never
assumed here. -/
def readPos (ν : Node p F) (tt : ℕ → Polynomial ℤ_[p]) (κ : ℕ) : ℤ :=
  - ν.σ.t * ν.σ.wPrev (tt κ) + ((ν.e * κ : ℕ) : ℤ) * ν.σ.s

/-- REUSE POINTER (cite-don't-rebuild): the D.8 normalization exponent
m̂ = −t·h·g is the EXISTING `LeanUrat.MovesC.Node.mhat` — this campaign declares
NO new m̂. This `abbrev` is a namespace convenience only. -/
abbrev mhat (ν : Node p F) : ℤ := ν.mhat

end LeanUrat.B2D
