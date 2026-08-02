/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TD1_floorsCharge
import LeanUrat.B2D.TD2_fiberSum
import LeanUrat.B2D.TD3_digitsProd
import LeanUrat.B2D.TD4_junctionPin
import LeanUrat.B2D.TD5_leakCarrier

/-!
# B2D/TD6_assembly — `transDeep_of_ledger`, the row supplier
  [B2DEF_LEAN unit TD-6; wave 3]

Blueprint §3 + §5 TD-6. moves_ref: §B2-DEF D.3(e)(ii) + D.8 + D.11 assembled.
deps: TD-1..TD-5. difficulty: easy (glue). E-phase file: statements only.

`leakFree` is instantiated by TD-5's `LeakFreeCarrier` — the charter-demanded
typed carrier, NOT the `True` fallback [R2-G1 fold]. Pricing fences carried
verbatim (§3): `SlotUniformLaw` is NOT supplied (it is (ADM) + (GR-B)-line
content — it enters the demonstration corollary as the displayed `huni`
hypothesis, never proved here); the junction VALUE is not identified.
The H2 row's [M]-status update on acceptance is a ROOT-owner move, never this
campaign's (§8).

STATEMENT ROUND 2 (v2, 2026-08-02): the designated family is now
`LedgerStrataV2` (TDDefsV2's finite-box lawfulness) — v1's `LedgerStrata`
carried only refuted-law members (`TD3_countermodel.not_digitsProd_of_lawful`),
so THIS supplier was unfillable as stated. The v1 family stays on file in
TDDefs as the refutation record.

STATEMENT ROUND 3 (v3, 2026-08-08 wallclock 2026-08-02): the designated
family is now `LedgerStrataV3` (TDDefsV3's pack: v2 + member existence +
full parent/box-slot disjointness). The round-2 family was AGAIN unfillable
for this supplier — the TD-3 round-2 Seam-A witness `cmL4` is v2-lawful and
in the scope/clean regime, yet its carrier violates `DigitsProdLaw`, so no
`TransDeep` row datum exists over it; `transDeep_of_ledger_v2_unfillable`
below is the compiled adjudication of the re-key (the v1-round precedent,
one level up). On v3 the `digitsProd` field is SUPPLIED by the proved TD-3
(`ledger_digitsProd`, round 3). -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **The round-2 (v2) family was UNFILLABLE for this supplier** — the
compiled adjudication of the v2 → v3 re-key: the TD-3 Seam-A witness `cmL4`
is v2-lawful (`cmL4_lawfulV2`) and in the scope/clean regime, but its
q-generic carrier violates `DigitsProdLaw` (`cm4_not_digitsProd`), which is
the `digitsProd` FIELD of any `TransDeep` row over it. -/
theorem transDeep_of_ledger_v2_unfillable :
    ¬ ∀ (D : CensusData) (W : WindowDatum D) (P : ParentShape D W)
        (J : JointStratum D W P), J ∈ LedgerStrataV2 D W P → LedgerScope W P →
        LedgerClean D W P J.N → Nonempty (TransDeep W P J) := by
  intro h
  obtain ⟨td⟩ := h cmD cmW cmP cmL4.ledgerJoint ⟨cmL4, cmL4_lawfulV2, rfl⟩
    cm_scope cm_clean
  exact cm4_not_digitsProd td.digitsProd

/-- **TD-6, the row supplier** (blueprint §3's `transDeep_of_ledger`): every
member of the designated family, in the scope/clean regime, satisfies the
(TRANS-DEEP) row — with `leakFree := LeakFreeCarrier` of the presenting datum
(the typed (L) carrier, never `True`).

RESPELLING FLAG (E-phase, sanctioned): the §3 display says `theorem`, but the
landed `TransDeep` lives in `Type` (its bare-`Prop` `leakFree` FIELD — the
carrier's own docstring's TYPE NOTE), so the supplier is a `def` producing the
row datum — the direct consumable for `fresh_of_transDeep`'s `hTD` binder (the
`kp_step`/`Nonempty` precedent considered and rejected: a `Nonempty` wrapper
would erase WHICH carrier fills `leakFree`, defeating the [R2-G1] requirement
that TD-5's `LeakFreeCarrier` is the plugged value). Statement content
unchanged. -/
noncomputable def transDeep_of_ledger (J : JointStratum D W P)
    (hJ : J ∈ LedgerStrataV3 D W P) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P J.N) :
    TransDeep W P J := by
  sorry -- B2DEF_LEAN E-phase sorry [unit TD-6, statement round 3 (v3)]

/-- **TD-6 demonstration corollary** at the designated family: the ledger strata
deliver BP_IV C5′'s `FreshRowOn` binder, with `huni` as the DISPLAYED (ADM) +
(GR-B)-line hypothesis (never supplied — §3 fence (i)). -/
theorem ledger_freshRowOn (D : CensusData)
    (hscope : ∀ (W : WindowDatum D) (P : ParentShape D W),
      LedgerScope W P)
    (hclean : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ LedgerStrataV3 D W P, LedgerClean D W P J.N)
    (huni : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ LedgerStrataV3 D W P, SlotUniformLaw W P J) :
    FreshRowOn D (fun W P => LedgerStrataV3 D W P) := by
  sorry -- B2DEF_LEAN E-phase sorry [unit TD-6, statement round 3 (v3)]

end LeanUrat.B2D

#print axioms LeanUrat.B2D.transDeep_of_ledger_v2_unfillable
