/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H2.FreshLaws
import LeanUrat.Scaffold.HDischarge.H2.FreshReduction
import LeanUrat.Scaffold.HDischarge.H2.CenJWiring

/-!
# Scaffold/HDischarge/H2/TransDeep — the (TRANS-DEEP) hypothesis row + the
  (FRESH-RED) assembly [HDISCHARGE_H2 unit U9; wave 3, GATE SATISFIED]

**Gate record (supersession).** Unit H2-U9 was GATED on acceptance of the GD
order-≥ 2 carry-algebra write-up, named **B2-FINAL** in blueprint §6 H2-U9;
per blueprint §1 (~line 47) the B2-FINAL campaign tie is "organizational, not
logical", so the gate condition transfers to that campaign's definitive
successor. That successor **§B2-DEF** (`lean/notes/MOVES_2026-07-24.md`) is
**ACCEPTED** (2026-07-26, passes 20 + 21 consecutive CLEAN on identical text;
MOVES :3231) and **DUAL-ACCEPTED** (Codex CLEAN + fresh-Fable CLEAN on the
identical rev-D¹¹d text; MOVES :5606) — the gate is satisfied and this unit
transcribes FROM THE ACCEPTED DOCUMENT ONLY.

**Dual statement gate on THIS unit's text (2026-08-02) — PASSED.** Codex leg:
three rounds on the proposed statements — R1 REJECT (2 CRIT: an invented
cross-realization (L) form; `huni` mis-attributed as bare (GR-B)-side), R2
REJECT (1 CRIT/1 GAP: no faithful (slotCount, slotDigits)-law can carry (L) —
mass-preserving digit-exclusion counterexample), folds applied after each;
R3 confirmation **ACCEPT, 0 CRITICAL / 0 GAP** on this text. Fable leg
(fresh context, sources re-read on disk): **PASS** — all six open questions
ratified (bare-Prop (L) via the `RootHyps` E-phase device; the
counting-shadow (FRESH-RED) reading with the blueprint's own name kept;
`huni`'s (ADM) attribution; the (J) value drop; the U8 binder form; `hscope`
absence per U5's law-to-law convention). Codex transcripts archived:
`lean/notes/openmath/H2U9_codex_statement_gate_2026-08-02.md`.

**What this file is.** The (TRANS-DEEP) row of blueprint §5 — the open kernel
(H2)'s trade target — as a DISPLAYED HYPOTHESIS ([M]-row discipline: stated
and consumed, NOT proved here; its supplier is the §B2-DEF campaign's future
Lean formalization), MINIMIZED to §5's consumer-side counting shadows per the
blueprint's own instruction (§4: "INTERFACE-MINIMIZABLE at transcription
time: transcribe the consumer-side minimal form, never the campaign's
strongest form"). The whole tower induction (stage axioms (S1)–(S6), the move
species D.5–D.10, the ledger D.11) is NOT transcribed — only the interface
the (FRESH-RED) assembly and its census consumers cite.

**What the row does NOT carry (pricing fences).** (i) `SlotUniformLaw` — the
full-alphabet per-digit uniformity — is (ADM)-FULL + (GR-B)-line ENGINE
content (U2's docstring records the suppliers) and blueprint §4 displays
(ADM) as CEN-J's own (H3) row, NOT part of this row; it enters
`fresh_of_transDeep` as the separate hypothesis `huni`. This split is forced
by the accepted §B2-DEF itself: at shallow heights the attainable alphabet
𝔸(γ) is a proper F_p-subspace (D.3(e)(ii), rev D¹¹c — "the uniform
field-alphabet display is FALSE at shallow heights"), so full-alphabet
uniformity is exactly the full-attainment ((ADM)) regime, never (TRANS-DEEP)
content. (ii) The junction VALUE identification ((c-GR)'s cofactor constant
under the anchored-march normalizers) is dropped: CEN-J §6.4 step 4 (O-9
Lemmas C + D) consumes only the pin's NONVANISHING and FIXEDNESS, never its
value.
-/

namespace LeanUrat.Scaffold.HDischarge.H2

open LeanUrat.Scaffold

variable {D : CensusData}

/-- **The (TRANS-DEEP) hypothesis row** (blueprint §5, three displayed
    clauses (F)/(L)/(J)) at one census-keyed joint stratum — an [M]-row:
    DISPLAYED, consumed by `fresh_of_transDeep`, NOT proved in this corpus.

    SUPPLIER OF RECORD: the ACCEPTED §B2-DEF (`lean/notes/MOVES_2026-07-24.md`;
    accepted 2026-07-26, passes 20+21 consecutive CLEAN; dual-accepted Codex +
    Fable on rev D¹¹d) — the GD order-≥ 2 graded/carry-algebra tower
    induction. Clause ↔ display map:

    * **(F) [floors/product]** = `floorsCharge` + `digitsProd` + `fiberSum`:
      the ρ-fiber's conditions are EXACTLY a product box of shape-only
      per-slot floors plus the (J) pin. §B2-DEF PIN — D.8 (BOX)/(VERTEX)
      (the landing box), D.3(e)(ii) (strata are digit CYLINDERS cut by
      unitriangular digit systems, one fresh coordinate per equation), D.11
      (the per-move ledger: stratum count = p^{nN}·vol(cylinder), vol = the
      attainable product — measure-exact). `FloorsChargeLaw`'s COUNT VALUE
      composes (F)'s shape-only floors with the PROVED A1/TRI/LED ledger
      count (O-9 §4); the two are inseparable at the skeletal carrier.
    * **(L) [leak]** = `leakFree`, a BARE `Prop` FIELD — an UNPINNED named
      assumption per the corpus's documented E-phase transcription device
      (`Scaffold/Hypotheses.lean` `RootHyps`: "all fields are bare Prop,
      True-instantiable — the conditionality claim of record MUST list
      consumed fields as UNPINNED named assumptions until their typed
      carriers land"). STATEMENT-GATE FOLD OF RECORD (rounds 1–2): clause
      (L) has NO faithful typed counting shadow at this skeletal carrier —
      the round-1 cross-realization form was a source-free consequence
      (Codex R1-C1), and the round-2 per-realization digit-sum form admits
      mass-preserving digit exclusions (Codex R2-C1's counterexample:
      slotDigits 0 = 2, slotDigits 1 = 0 under slotCount = 2), while
      pinning per-digit VALUES would bake in the LED/(ADM) baseline the
      row must not carry. The typed (L) carrier lands with the engine
      instantiation / the gated classifier-face unit (H2-U10), keyed to
      §B2-DEF D.3(e)(ii.3)/(ii.4) (parent equations pin blocks DISJOINT
      from interior window blocks; each pinned leaf's value is forced
      given predecessors) — until then no consumer may read `leakFree` as
      discharged or as content-bearing.
    * **(J) [junction]** = `junctionPin`: the k_s-read is a ρ-determined
      NONZERO constant. §B2-DEF PIN — D.8 (VERTEX): dig′(B_μ) =
      z̄^{−μm̂}·((R(f)/ψ^μ) mod ψ) ≠ 0, deterministic in the parent's
      residual data, nonzero in the FIELD F′ (D.6: dig′ lands in F′ˣ); at
      recentered stages D.10 (R(Φ′) = z − c̃; the (z′+c̃)^a anchored
      display). MINIMIZED: only nonvanishing + ρ-fixedness are transcribed
      (`JunctionPinLaw`'s ∃ c ≠ 0); the value identification is (c-GR)'s,
      never consumed by the census (module docstring, fence (ii)).

    The row deliberately does NOT include `SlotUniformLaw` (fence (i)) and
    does NOT restate the tower induction — it is the CONSUMER-SIDE interface
    of §5, per §4's minimization instruction. TYPE NOTE: the bare-`Prop`
    (L) field puts this structure in `Type` (the `RootHyps` precedent),
    not `Prop`. -/
structure TransDeep (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) where
  /-- (F), floors face: per-slot height counts at the joint condition
      max(β_k, g_k), shape-only (§B2-DEF D.8 (BOX) + D.11 through the proved
      A1/TRI ledger). -/
  floorsCharge : FloorsChargeLaw W P J
  /-- (F), product-box face: fiberwise per-slot factorization of the
      prescribed-digit counts (§B2-DEF D.3(e)(ii) digit cylinders + D.11
      attainable product). -/
  digitsProd : DigitsProdLaw W P J
  /-- (F), aggregation seam: digit-level counts aggregate to the height-only
      fiber count (§B2-DEF D.3(e)(ii) bottom-up display: w ≥ γ ⟺ all lower
      digits vanish). -/
  fiberSum : FiberSumLaw W P J
  /-- (L) [leak], §5 verbatim referent: "at every interior on-line slot
      k ≠ k_s, the parent's realized conditions impose NO constraint on the
      height-β_k digit of a_k beyond (F)'s floor." UNPINNED bare-`Prop`
      field (RootHyps E-phase convention) — see the structure docstring's
      fold record; True-instantiable; not consumed by `fresh_of_transDeep`. -/
  leakFree : Prop
  /-- (J): the junction read is a ρ-determined nonzero constant (§B2-DEF
      D.8 (VERTEX) + D.6 + D.10). -/
  junctionPin : JunctionPinLaw W P J

/-- **The (FRESH-RED) assembly AT THE CENSUS COUNTING SHADOW** (blueprint
    §4's discharge shape, projected to the carrier where (FRESH) lives as
    `FreshClauses`): LED-uniformity + (TRANS-DEEP) ⟹ the (FRESH) counting
    shadow, at one census-keyed (W, P, J).

    HYPOTHESIS ATTRIBUTION, exact (round-1 gate fold, Codex C2): `huni :
    SlotUniformLaw` is the LED §5.1 engine layer at this carrier, whose
    SUPPLIERS ARE (ADM)-FULL + THE (GR-B) LINE CLAUSE (U2's docstring of
    record) — it is NOT the bare (GR-B)-side hypothesis of the
    displayed-clause (FRESH-RED). The (ADM) dependence is DISPLAYED, not
    smuggled, and is the blueprint's own accounting: the conclusion here
    includes clause (b)'s COUNTING face (`FreshReadsLaw`), and §3.2's
    (b-RED) display reads "Given (a′) at (D, ρ), (ADM)-FULL at D, and
    (GR-B)'s line clause (the §5.1 layer), clause (b) follows"; §4 then
    scopes (ADM) OUT of the ROW and OUT of displayed-clause (FRESH-RED)
    ("CEN-J carries (ADM) as its own displayed §3.1 row (H3)") — so (ADM)
    content appears exactly here, as a hypothesis of the CONSUMING theorem,
    never as a field of `TransDeep`. The displayed-clause (FRESH-RED)
    (concluding (b)'s STRUCTURAL clause without (ADM)) has no carrier at
    this counting skeleton and is NOT claimed by this theorem.

    PROOF (real, not deferred): (F)- and (J)-fields pass through; clause
    (b)'s counting face fires the landed U5 reduction
    `freshReads_of_digitsProd` (§3.2's retirement: residue NONE beyond
    (a′) + (ADM) + (GR-B)-line). `leakFree` is NOT consumed here — its
    consumers are the Step-10/K1 classifier face and the H2-N2 leak gates;
    it rides the row because §5 displays three clauses and the row is the
    row. -/
theorem fresh_of_transDeep (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) (hTD : TransDeep W P J)
    (huni : SlotUniformLaw W P J) : FreshClauses W P J :=
  { floorsCharge := hTD.floorsCharge
    digitsProd := hTD.digitsProd
    fiberSum := hTD.fiberSum
    freshReads := freshReads_of_digitsProd W P J hTD.digitsProd huni
    junctionPin := hTD.junctionPin }

/-- The D-keyed corollary at the U8 packaging: (TRANS-DEEP) + the engine
    uniformity over a designated strata family deliver BP_IV C5′'s
    `FreshRowOn` binder — the "at every D, N, ρ" quantification of
    (FRESH-RED) (blueprint §4), keyed exactly as U8 declared it. -/
theorem freshRowOn_of_transDeep (D : CensusData)
    (Strata : ∀ (W : WindowDatum D) (P : ParentShape D W),
      Set (JointStratum D W P))
    (hTD : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ Strata W P, TransDeep W P J)
    (huni : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ Strata W P, SlotUniformLaw W P J) :
    FreshRowOn D Strata :=
  fun W P J hJ => fresh_of_transDeep W P J (hTD W P J hJ) (huni W P J hJ)

end LeanUrat.Scaffold.HDischarge.H2
