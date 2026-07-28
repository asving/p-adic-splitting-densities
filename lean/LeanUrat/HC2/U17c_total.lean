/-
Unit U17c.presentNorm_total  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD `PresentNorm` clause (i) — TOTALITY.
deps: U17a + U17b + membership bookkeeping (H' ∈ PrefSet → its class is a PrefIdx
member); the assembled `presentNorm_polOM` additionally consumes U18.
difficulty: medium.  hypothesis_fields: inherits U17a's stage supplier (`StageTransHyp`).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U17a_liftSwap
import LeanUrat.HC2.U17b_galois
import LeanUrat.HC2.U18_unique

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The TOTALITY clause of `PresentNorm n (polOM p F) P`: every policy-free realizable
prefix has a normalized class-mate up to Galois. -/
theorem presentNorm_total {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} (hst : StageTransHyp p F) :
    ∀ H : History p F, H ∈ PrefSetAny n P →
      ∃ i : PrefIdx n (polOM p F) P,
        EtaGalEq (etaData (P : ShapePrefix) H) i.1 := by
  intro H hH
  -- U17a `lift_swap`: canonical-lift (`IsCanon`), same-η class-mate.
  obtain ⟨H', hMatch', hEta', hCanon', hcoh', hreal', hbox'⟩ := lift_swap hst H hH
  -- U17b `galois_normalize`: root-normalize (`canonRoot`) up to a Galois automorphism —
  -- with the N-3 `IsCanon`-transport clause (the escalation record's route (A), landed).
  obtain ⟨φ, H'', hMatch'', hRoot'', hTrans'', hGal'', hcoh'', hreal'', hbox'', hCanTrans⟩ :=
    galois_normalize (P := P) H' hMatch' hcoh' hreal' hbox'
  -- Membership bookkeeping: `H'' ∈ PrefSet` ⟹ its η-class is a `PrefIdx` member.
  -- [N-3 CLOSURE RECORD, 2026-07-28: the former sorry here was the escalation-diagnosed
  -- MISSING OUTPUT CLAUSE — both composition orders verified blocked, route (A)
  -- (`IsCanon`-transport on U17b) ratified as the design; the full obstruction record
  -- lives in the U17b header and the git history of this file. Consumption = one line.]
  have hmem : H'' ∈ PrefSet n (polOM p F) P :=
    ⟨hMatch'', hcoh'', hreal'', hbox'', hCanTrans hCanon', hRoot''⟩
  refine ⟨⟨etaData (P : ShapePrefix) H'', ⟨H'', hmem, rfl⟩⟩, ?_⟩
  -- η(H') = η(H) and EtaGalEq (η H') (η H'') ⟹ EtaGalEq (η H) (η H'').
  rw [← hEta']
  exact hGal''

/-- ASSEMBLED: the full typed dictionary pin `PresentNorm` at `polOM` — U15/U16's `hnorm`
discharger. K3 RE-KEY (2026-07-28): U18's `presentNorm_unique` now carries the ADJACENCY
hypotheses the conditional refutation dictates (`AdjacentReads`, Defs K3 addendum;
`scratch_U18_unique_false.lean`), so it no longer discharges `PresentNorm`'s clause (ii)
as typed. Per the blueprint's P-3 disposition the consumer carries the NAMED HYPOTHESIS
`OmUniqHyp` (never an axiom) — NOTE the standing caveat: `OmUniqHyp` as typed is itself
CONDITIONALLY REFUTED by the same scratch witness (`omUniqHyp_refuted_by_witness`); at
witness-admitting shapes this hypothesis is unsatisfiable, and the wave-4 negotiation
(MovesD dictionary vs. the adjacency-restated U18) decides the final uniqueness form. -/
theorem presentNorm_polOM {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} (hst : StageTransHyp p F)
    (huniq : OmUniqHyp n (polOM p F) P) :
    PresentNorm n (polOM p F) P :=
  ⟨presentNorm_total hst, huniq⟩

end LeanUrat.MovesJ
