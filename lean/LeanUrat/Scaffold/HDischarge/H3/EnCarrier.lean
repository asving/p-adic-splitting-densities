/-
HDISCHARGE_H3 §3.4 — unit EN-U4 (wave 1): the (E-N) redundancy carrier at the
presented model layer.  Def `ENRedundancyAt` transcribed VERBATIM from the
blueprint (compile-probed there; `LeanUrat.MovesT` vocabulary), plus the
MANDATORY decidedness derivation `fiberAt_nsFree_decided` (Codex pass-1
finding 14) and the display lemmas tying the carrier to the seam contract's
`Tr.thr n ≤ N'` rows (MovesT/Defs `TreeNStmt` / `TreeNStable`).
NO PROOF of `ENRedundancyAt` is scheduled (blueprint §3.4 note).
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-!
# (E-N) redundancy carrier [HDISCHARGE_H3 unit EN-U4]

**PROVENANCE.**

* Blueprint: `lean/blueprints/HDISCHARGE_H3.md` §3.4 (EN-U4: the def verbatim,
  compile-probed; the decidedness-encoding adjudication of Codex pass-1
  finding 14; the degeneracy fence of finding 16's genre).
* Vocabulary: `LeanUrat.MovesT` (`VTree.thr` = the Defs §2.5 threshold join;
  `VTree.fiberAt`, `NsFree` as built) over `LeanUrat.MovesD` model carriers
  (`TreeModel`, `CanonPolicy`, `Box`).
* Seam contract consumers: the `Tr.thr n ≤ N'` hypothesis rows of
  `LeanUrat.MovesT.TreeNStmt` (Defs ~1669) and the `Tr.thr n ≤ N` gate of
  `LeanUrat.MovesT.TreeNStable` — the threshold gate is the SEAM's declared
  contract shape; this carrier makes the (E-N) question a first-class `Prop`
  the seam can consume or discharge.

**STATUS.** `ENRedundancyAt` is UNPROVED and UNSCHEDULED (blueprint §3.4):
it is the TYPED HOME for route (a) if the G-EN-1 falsifier scan supports it,
and the typed FALSIFIER TARGET if G-EN-1 hits (a compiled counterexample
lands as `¬ ENRedundancyAt …` at the instance).  Nothing in this file claims
it; the lemmas below only route it to its consumption sites.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.Scaffold.HD3

open LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- unit EN-U4 (blueprint-verbatim) — the (E-N) redundancy carrier at the
presented model layer: every ns-free complete finite tree fibering a level-`N`
box has threshold `thr(T) ≤ N` (the redundancy of the (E-N) caveat, route (a)
of HDISCHARGE_H3 §3.3).

DECIDEDNESS ENCODING (Codex pass-1 finding 14, adjudicated MIXED): a
`Decided` premise is DERIVABLE, not missing — see `fiberAt_nsFree_decided`
below (`VTree.fiberAt` clause 2 + `NsFree` force every maximal chain to be a
(τ-irr) leaf, i.e. the fibered tree IS decided ns-free); consumers must cite
that lemma before reading this def as the (E-N) carrier.

DEGENERACY FENCE / GLOBAL ∀-CLOSURE (finding 14/16's genre): this def is
PER-MODEL — the parameters `p, F, n, N, m, pol, T, χ` are FIXED.  The GLOBAL
(E-N) carrier is the ∀-closure over presented models at the standing
perimeter (`n ≥ 1`, `m` per the model's chart; the degenerate `m = 0` /
empty-`χ` corner is excluded by the presented-model constructors, which never
present an empty chart).  Consumers must quantify explicitly — NEVER cite
this fixed-parameter `Prop` as the global claim. -/
def ENRedundancyAt (n N m : ℕ) (pol : CanonPolicy p F)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) : Prop :=
  ∀ (Tr : VTree p F) (x : Box p m),
    NsFree Tr → Tr.fiberAt T χ x → Tr.thr n ≤ N

/-- **MANDATORY auxiliary (Codex pass-1 finding 14)** — decidedness is
DERIVABLE from `fiberAt` clause 2 + `NsFree`: `VTree.fiberAt` clause 2 forces
every maximal chain to be halted (`IrrHalts … ∨ NsHalts …`, with the ns
disjunct requiring `Tr.nsLeaf H`), and `NsFree Tr` kills the ns disjunct — so
under `ENRedundancyAt`'s hypotheses every maximal chain is a (τ-irr) leaf,
i.e. the fibered tree IS decided ns-free.  This lemma must be on record
BEFORE any consumer cites `ENRedundancyAt` as the (E-N) carrier. -/
theorem fiberAt_nsFree_decided {n N m : ℕ} {pol : CanonPolicy p F}
    {T : TreeModel p F n N m pol} {χ : Fin n → Fin m}
    {Tr : VTree p F} {x : Box p m}
    (hns : NsFree Tr) (hfib : Tr.fiberAt T χ x) :
    ∀ H ∈ Tr.chains, IsMaximalIn Tr.chains H → IrrHalts H := by
  intro H hH hmax
  rcases hfib.2.1 H hH hmax with ⟨hirr, _, _⟩ | ⟨_, _, hnsl, _⟩
  · exact hirr
  · exact absurd hnsl (hns H hH)

/-- Companion read-off of the same clause: on an ns-free fibered tree every
maximal chain carries the (τ-irr) verdict (`leafV = some (irrVerdictOf ·)`). -/
theorem fiberAt_nsFree_leafV {n N m : ℕ} {pol : CanonPolicy p F}
    {T : TreeModel p F n N m pol} {χ : Fin n → Fin m}
    {Tr : VTree p F} {x : Box p m}
    (hns : NsFree Tr) (hfib : Tr.fiberAt T χ x) :
    ∀ H ∈ Tr.chains, IsMaximalIn Tr.chains H →
      Tr.leafV H = some (irrVerdictOf H) := by
  intro H hH hmax
  rcases hfib.2.1 H hH hmax with ⟨_, _, hleaf⟩ | ⟨_, _, hnsl, _⟩
  · exact hleaf
  · exact absurd hnsl (hns H hH)

/-- Route lemma (unfolding shape): the carrier discharges the threshold bound
for any ns-free tree fibering any box of the model. -/
theorem ENRedundancyAt.thr_le {n N m : ℕ} {pol : CanonPolicy p F}
    {T : TreeModel p F n N m pol} {χ : Fin n → Fin m}
    (hEN : ENRedundancyAt n N m pol T χ) {Tr : VTree p F} {x : Box p m}
    (hns : NsFree Tr) (hfib : Tr.fiberAt T χ x) : Tr.thr n ≤ N :=
  hEN Tr x hns hfib

/-- **Display lemma (the seam tie)** — the carrier discharges EXACTLY the seam
contract's threshold-gate rows: `LeanUrat.MovesT.TreeNStmt`'s hypothesis row
`Tr.thr n ≤ N'` (stated there at the standard layout `m = n·N'`, under the
rows `Realizes T χ Tr` and `∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H` — the literal
ns-free row shape), and likewise `TreeNStable`'s gate `Tr.thr n ≤ N`.  Given
the carrier at the seam's parameters, the gate row is supplied verbatim. -/
theorem ENRedundancyAt.seam_thr_row {n N' : ℕ} {pol : CanonPolicy p F}
    {T : TreeModel p F n N' (n * N') pol} {χ : Fin n → Fin (n * N')}
    (hEN : ENRedundancyAt n N' (n * N') pol T χ) {Tr : VTree p F}
    (hns : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hreal : Realizes T χ Tr) :
    Tr.thr n ≤ N' := by
  obtain ⟨x, hfib⟩ := hreal
  exact hEN Tr x hns hfib

end LeanUrat.Scaffold.HD3
