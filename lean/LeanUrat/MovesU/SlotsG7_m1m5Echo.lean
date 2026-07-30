/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers
import LeanUrat.MovesSp.Defs

/-!
# IB-G7 — Slot_m1m5Echo FORMULATION SKELETON (bridge BP1, §3.8)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (the
m1m5Echo row) + §4 group G (IB-G7: "Slot_m1m5Echo (M1_bridge.md raw material).
ADJ→H") and `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (BP1 Q5).

THE RESERVED PARAMETER (U10_theoremU.lean:78–79, verbatim): "`m1m5Echo` — CL-14,
the [2a] M1+M5 catalogue echo row (closed upstream; the instance tie to this seam
is unbuilt)" — one of the thirteen wave-4-boundary bare-Prop parameters
(UNPINNED pending this carrier).  The mathematics is CLOSED UPSTREAM; what this
slot types is the INSTANCE TIE — that the built instance's catalogue/menu is the
one the closed M1+M5 seam speaks about.

RAW MATERIAL (blueprint §3.8, verified present 2026-07-30):
* `lean/notes/M1_bridge.md` — the monic → projective density bridge (PROJ)/
  (MONIC): both densities are the same Sym^n stratification driven by the same
  intrinsic cluster laws L_e^{(δ)} = β(e,·;q^δ) = α(e,·;q^{-δ}), differing only
  in the base-point set (A¹ vs P¹) — the recorded M1 statement + proof skeleton;
* `LeanUrat.M1` (M1.lean:28ff) — the built Lean-side M1 vocabulary
  (`projPointCount`, `clusterLaw`, `clusterLaw_baseChange`,
  `clusterLaw_reciprocal`);
* the MovesSp CATALOGUE — `LeanUrat.MovesSp.InCatalogue`/`SnRaw`
  (MovesSp/Defs.lean:124/128) with the closed catalogue equalities
  (SP6_catalogueEq's `SnRaw3_eq` pattern) and the SP8 instantiation seam
  (`SpeciesReadout`, SP8_instantiation.lean) — the [2a] species-word side;
* the M5 echo face: the catalogue's realized menu vs the M1 cluster-law index —
  the note's CL-14 display (the catalogue letters realized by the engine echo
  the M1/M5 seam's species inventory, so the per-letter cluster-law reads and
  the catalogue words price the SAME objects).

FORMULATION TARGET (H-phase; deps: `UCarriers` + the raw material above; owner
[2a]; note display CL-14): the INSTANCE TIE — the carried §S corpus's verdict/
species inventory (through `C.T`'s roster and `C.chain`'s σ-index `Sigmas`) is
tied to the MovesSp catalogue and, through it, to the M1+M5 seam's cluster-law
keying: each realized species letter of the instance is in the catalogue, and
its M1-side cluster-law key (the (e, δ)-read that `clusterLaw` consumes) is the
letter's own stage tuple — no private menu, no re-keyed echo.  The tie carrier
(instance letters → catalogue species) has NO built vocabulary — the H-phase
designs it as bound data INSIDE the Prop (per §3.8's "newly-designed carrier
vocabulary"), consuming the raw-material modules by explicit import at fill
time (imports here are minimal per the E-phase rule).

E-PHASE DIVISION OF LABOR (as in IB-G2, per §3.8/R9): body `sorry`; the
displayed Prop is the ADJ→H deliverable behind the Q5 Codex-audit gate.
NON-VACUITY DUTY (IB-G11c): `example : ¬ Slot_m1m5Echo degenerate…` — e.g.
FALSE for an instance whose letters miss the catalogue or re-key the seam.
CLOSURE MANIFEST DUTY (IB-G12): every identifier → built decl path.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
H-PHASE RESOLUTIONS (2026-07-30, cluster BP1-P10-slots; FLAGGED for the Q5 Codex
audit):
* (h1) THE TIE CARRIER is an ∃-bound letter assignment on the carried roster:
  `letterOf e τ o : MovesSp.Species` per outcome of `C.T` — the instance's
  realized species letters, with `MovesSp.InCatalogue n` as the "no private menu"
  clause (the [2a] catalogue is the inductive closure `SnRaw`, built).
* (h2) "THE (e, δ)-READ THAT `clusterLaw` CONSUMES IS THE LETTER'S OWN STAGE
  TUPLE — no re-keyed echo": the M1 cluster-law key at a branch member is the
  member's own base-change factor `Member.δ` (CONVENTION DELTA-ABS, the same
  convention `M1.clusterLaw`'s base-change identity `L_e^{(δ)}(q) = L_e^{(1)}(q^δ)`
  reads).  The pin is stated as TWO-SIDED agreement of the letter's residual
  partition first components (`Species.lam.map Prod.fst` — the residual (g)-reads)
  with the outcome's own member δ-reads, plus the selection pin (h3).  The
  MULTIPLICITY components of `lam` are deliberately NOT pinned (no built member
  datum prices them; pinning them would invent content — the round-1 sin).
  `M1.clusterLaw` itself is cited, not restated: its base-change/reciprocal
  identities are definitional theorems (M1.lean:59/65), so restating them here
  would add a vacuous conjunct; the slot pins the KEYS the seam consumes.
* (h3) SELECTION = the designated continuing member's own read: the letter's
  `sel` is populated exactly when the outcome continues, and any selected `(g, m)`
  has `g` = a continuing member's own δ — never a re-keyed value.
NON-VACUITY (IB-G11c's duty, follow-up file): FALSE at a degenerate instance
whose roster carries a member with a base-change factor no degree-n catalogue
letter realizes (e.g. δ beyond the catalogue's budget) — the letters miss the
catalogue, exactly the file-header example.
-/

namespace LeanUrat.MovesU

/-- IB-G7 — **`Slot_m1m5Echo`** (CL-14, the [2a] M1+M5 catalogue echo row; closed
upstream, the INSTANCE TIE typed here): the carried instance's species inventory
is tied to the MovesSp catalogue and through it to the M1+M5 seam's cluster-law
keying (see the file header for the formulation target and raw material:
notes/M1_bridge.md, `LeanUrat.M1`, `LeanUrat.MovesSp.InCatalogue`/SP8).  H-phase
fills the displayed Prop; Codex audit before any consumer (Q5). -/
def Slot_m1m5Echo (n : ℕ) (C : UCarriers n) : Prop :=
  ∃ letterOf : ∀ (e : ℕ) (τ : C.T.State e), C.T.Out e τ → MovesSp.Species,
    ∀ e, e ∈ Finset.Icc 1 n → ∀ (τ : C.T.State e) (o : C.T.Out e τ),
      -- (h1) no private menu — the realized letter is in the [2a] catalogue:
      MovesSp.InCatalogue n (letterOf e τ o) ∧
      -- (h2) the letter's residual (g)-reads are the roster's own base-change
      -- factors (two-sided agreement — the (e, δ)-keys the M1 seam consumes):
      (∀ μ ∈ (C.T.odata e τ o).mem,
        (μ.δ : ℕ) ∈ (letterOf e τ o).lam.map Prod.fst) ∧
      (∀ g ∈ (letterOf e τ o).lam.map Prod.fst,
        ∃ μ ∈ (C.T.odata e τ o).mem, (μ.δ : ℕ) = g) ∧
      -- (h3) selection ↔ continuation, at a continuing member's own read:
      ((letterOf e τ o).sel.isSome = true ↔ (C.T.odata e τ o).c ≠ 0) ∧
      (∀ g m : ℕ, (letterOf e τ o).sel = some (g, m) →
        ∃ μ ∈ (C.T.odata e τ o).mem,
          μ.status.isRight = true ∧ (μ.δ : ℕ) = g)

end LeanUrat.MovesU
