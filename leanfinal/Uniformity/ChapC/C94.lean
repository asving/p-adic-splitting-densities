/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C09
import Uniformity.ChapC.C13
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C29

/-!
# Uniformity.ChapC.C94 — the [AGNPRW] termination axiom (gate-(b) cite)

**Chapter C, NODE C.94 `[cite:AGNPRW]`** — the THIRD landed literature-cite axiom, at the
**A-C.6 REDRAFTED statement** (the A-C.1 draft was machine-refuted pre-landing — it admitted
the self-loop `s' = s` and both its side clauses were vacuous, making the drafted Prop imply
`False`; record: `C94_REFUTATION.lean.txt`; redraft certification: `C94_REDRAFT_CERT.lean.txt`).
The grammar `DescentStepR` and the Prop `NS7TerminationStatementR` are transcribed verbatim
from `leanspec/Leanspec/ChapC.lean` (A-C.6 block).

## Faithfulness entry

* **Publication.** M. Alberich-Carramiñana, J. Guàrdia, E. Nart, A. Poteaux, J. Roé,
  M. Weimann, *Polynomial Factorization Over Henselian Fields*, **Found. Comput. Math. 25
  (2025), no. 2, 631–681**, DOI 10.1007/s10208-024-09646-x. Cited: **Theorem 5.6** verbatim —
  *"If `v` is discrete of rank-one, then the OM-algorithm terminates."* — together with §5.5's
  reduction (*"the OM-algorithm does not terminate if and only if there is an infinite sequence
  of refinement steps"*) and **Definition 5.5**'s characterization of a refinement step.
  Numbering per the A-3 audit (the repo's older "Thm 5.2" was the arXiv-v1 number and collided
  with a different published theorem).
* **Provenance CLOSED.** The owner supplied the published PDF
  (`docs/references/s10208-024-09646-x.pdf`, 2026-08-17) and the orchestrator executed the
  print-read: Thm 5.6 verbatim-match; every Def 5.5 source-reading clause of the redraft is
  consistent with the published text (the uniqueness/newness grounding the self-loop
  exclusion, the one-sidedness with `e_rel(µ_λ) = 1`, the `(y − ζ)^ℓ` residual with
  `ζ ∈ κ(µ_λ)^*`, and the finite-jump clause); the adjudicated-out `ℓ = 1` row is confirmed
  against the published Thm 2.18 display. Dated closure note: blueprint A-C.6 §II.
* **Containment honesty (disclosed, from the amendment).** `DescentStepR`'s clauses are
  polygon-level shadows of Def 5.5's type-level conditions; containment of the repo relation
  in the source relation is argued clause-by-clause in A-C.6 §II.3's two-column table (each
  clause justified once by the published text and once by a corpus-side argument), not proved
  in Lean. The cheapest hardening (carrying the type datum in `DescentState`) is identified
  there and deliberately not taken.
* **Signature.** Owner-signed 2026-08-17 under the ratification-by-compile ruling
  (PROJECT_STATE append #84).

## Non-vacuity / consistency

* **Satisfiability**: `C94_REDRAFT_CERT.lean.txt` constructs a GENUINE two-step refine descent
  over `ℤ₂` (block `f = (x−6)² − 32`, keys `x → x−2 → x−6`, slopes `1 → 2`) inhabiting every
  clause — the relation has real steps, so termination is not true-for-lack-of-steps.
* **Non-refutability**: the refutation program dies mechanically against this statement, and
  after a best-effort revival its goals are the FALSE `s.key ≠ s.key` and `0 < 0`; the general
  `redraft_no_self_loop : ∀ π s, ¬ DescentStepR π s s` is PROVED for both constructors.
* **Numeric leg**: `verification/ac6_cite_redraft_check.py` PART 2 (index bookkeeping + a
  Lean-vs-Python model cross-check agreeing digit-for-digit), green.
-/

namespace Uniformity.Density.Tower

open Polynomial Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The §5 descent state: the current key and the current block. (A-C.6 carrier,
transcribed from leanspec.) -/
structure DescentState (O : Type*) [CommRing O] where
  key : Polynomial O
  block : Polynomial O

set_option linter.unusedVariables false in
/-- **The A-C.6 REDRAFTED descent grammar** — the relation contained in the one [AGNPRW]
§5.5 proves terminates. `jump` is the A-C.1 form (no self-loop is possible there: `IsTestKey`
pins the key degree strictly up); `refine` carries the Def 5.5 clauses — the self-loop
exclusion `s'.key ≠ s.key`, genuine two-point sides, purity, `0 < u` with coprimality, the
`(X − C ζ)^sideDeg` residual with `ζ ≠ 0` and the LOAD-BEARING `2 ≤ sideDeg`, and the strict
slope increase. Transcribed verbatim from the signed leanspec block. -/
inductive DescentStepR (π : O) : DescentState O → DescentState O → Prop
  | jump : ∀ {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (L : LevelDatum F H₀ hpin)
      (s s' : DescentState O),
      s.key = F.key → 2 ≤ L.ℓ * L.r.natDegree →
      HasLabel L s'.block → s'.block ∣ s.block →
      IsTestKey L s'.key → L.keyDeg₂ * 2 ≤ s'.block.natDegree →
      DescentStepR π s s'
  | refine : ∀ (s s' : DescentState O) (u ℓ u' ℓ' : ℕ)
      (hne : (sideSet s.key s.block u ℓ).Nonempty)
      (hne' : (sideSet s'.key s.block u' ℓ').Nonempty),
      s.key.Monic → s'.key.Monic → 0 < s.key.natDegree →
      s'.block = s.block →
      s'.key.natDegree = s.key.natDegree →
      s'.key ≠ s.key →
      (s.key - s'.key).natDegree < s.key.natDegree →
      0 < u → 0 < ℓ → Nat.Coprime u ℓ →
      0 < u' → 0 < ℓ' → Nat.Coprime u' ℓ' →
      1 < (sideSet s.key s.block u ℓ).card →
      1 < (sideSet s'.key s.block u' ℓ').card →
      IsPure s.key s.block u ℓ →
      IsPure s'.key s.block u' ℓ' →
      2 ≤ sideDeg s.key s.block u ℓ hne →
      (∀ H₀ : ℕ, npHgt s.key s.block (sideMin s.key s.block u ℓ hne) = (H₀ : ℕ∞) →
        ∃ ζ : resField s.key, ζ ≠ 0 ∧
          resPoly π s.key s.block u ℓ hne H₀
            = (Polynomial.X - Polynomial.C ζ) ^ sideDeg s.key s.block u ℓ hne) →
      u * ℓ' < u' * ℓ →
      DescentStepR π s s'

/-- NODE C.94's exact Lean statement over the redrafted grammar: no infinite descent history
on a fixed monic squarefree `f`. Transcribed verbatim from the signed leanspec block. -/
def NS7TerminationStatementR : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (π : O), Irreducible π →
    ∀ f : Polynomial O, f.Monic → Squarefree f →
    ∀ hist : ℕ → DescentState O,
      (∀ n, (hist n).block ∣ f) →
      (∀ n, DescentStepR π (hist n) (hist (n + 1))) → False

/-- **NODE C.94 `[cite:AGNPRW]` (gate (b)).** OM descent terminates — [AGNPRW] Thm 5.6 via
§5.5's refinement reduction. The full faithfulness entry (incl. the executed print-read and
the disclosed containment honesty) is the module docstring. -/
axiom agnprw_termination : NS7TerminationStatementR

end Uniformity.Density.Tower

/-! ## Axiom footprint (the axiom prints itself; consumers inherit it) -/

section AxCheck
#print axioms Uniformity.Density.Tower.agnprw_termination
end AxCheck
