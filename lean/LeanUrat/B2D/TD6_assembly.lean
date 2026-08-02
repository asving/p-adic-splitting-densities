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
(`ledger_digitsProd`, round 3).

PROVED (TD mop-up wave, 2026-08-08 wallclock 2026-08-02), statements
byte-unchanged from the round-3 re-key: with TD-1..TD-5 all proved
(TD-1/TD-2/TD-4/TD-5 at v2, consumed through the v3 pack's `extends`; TD-3
at v3) the assembly is the glue the blueprint priced. The helper
`transDeep_of_lawful` builds the row AT the presenting datum — making the
plugged `leakFree := LeakFreeCarrier L` value inspectable per [R2-G1] — and
`transDeep_of_ledger` transports it along the family membership's
`J = L.ledgerJoint` equation (`Exists.choose`, the `noncomputable` warrant).
`ledger_freshRowOn` = `freshRowOn_of_transDeep` at this supplier, `huni`
passed through as the displayed hypothesis, exactly the H2 §3 interface
(`fresh_of_transDeep`'s `hTD` binder is fed by this def). -/

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

/-- **The row at the presenting datum** (TD-6's builder): a v3-lawful ledger
datum's own q-generic carrier satisfies the (TRANS-DEEP) row, with
`leakFree := LeakFreeCarrier L` — the TD-5 typed carrier OF THIS DATUM, the
[R2-G1]-demanded plugged value, inspectable here by `rfl`. Field suppliers:
TD-1 (`ledger_floorsCharge`, v2) + TD-3 (`ledger_digitsProd`, v3) + TD-2
(`ledger_fiberSum`, v2) + TD-4 (`ledger_junctionPin`, v2); the v2-statement
units consume the v3 pack through `extends`. -/
noncomputable def transDeep_of_lawful (L : LedgerStratumData D W P)
    (hL : L.LedgerLawfulV3) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    TransDeep W P L.ledgerJoint where
  floorsCharge := ledger_floorsCharge L hL.toLedgerLawfulV2 hscope hclean
  digitsProd := ledger_digitsProd L hL hscope hclean
  fiberSum := ledger_fiberSum L hL.toLedgerLawfulV2 hscope hclean
  leakFree := LeakFreeCarrier L
  junctionPin := ledger_junctionPin L hL.toLedgerLawfulV2 hscope hclean

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
  have hJ' : ∃ L : LedgerStratumData D W P, L.LedgerLawfulV3 ∧ J = L.ledgerJoint := hJ
  have hclean' : LedgerClean D W P hJ'.choose.N := by
    have h := hJ'.choose_spec.2
    rw [h] at hclean
    exact hclean
  have key : TransDeep W P hJ'.choose.ledgerJoint :=
    transDeep_of_lawful hJ'.choose hJ'.choose_spec.1 hscope hclean'
  rw [hJ'.choose_spec.2]
  exact key

/-- **TD-6 demonstration corollary** at the designated family: the ledger strata
deliver BP_IV C5′'s `FreshRowOn` binder, with `huni` as the DISPLAYED (ADM) +
(GR-B)-line hypothesis (never supplied — §3 fence (i)). PROVED:
`freshRowOn_of_transDeep` (the landed H2 §3 interface) fed by
`transDeep_of_ledger`. -/
theorem ledger_freshRowOn (D : CensusData)
    (hscope : ∀ (W : WindowDatum D) (P : ParentShape D W),
      LedgerScope W P)
    (hclean : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ LedgerStrataV3 D W P, LedgerClean D W P J.N)
    (huni : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ LedgerStrataV3 D W P, SlotUniformLaw W P J) :
    FreshRowOn D (fun W P => LedgerStrataV3 D W P) :=
  freshRowOn_of_transDeep D (fun W P => LedgerStrataV3 D W P)
    (fun W P J hJ => transDeep_of_ledger J hJ (hscope W P) (hclean W P J hJ))
    huni

/-! ## Non-vacuity gates: the supplier FIRES at the designated r = 1 instance,
and the [R2-G1] plug is definitional -/

/-- **The supplier fired**: the (TRANS-DEEP) row datum at TD-0's designated
r = 1 instance (in the v3 family by `td_mem_ledgerStrataV3`; scope/clean by
`td_scope`/`td_clean`) — the supplier is non-vacuous, the same instance whose
fiber counts are positive (`td_devacuify`). -/
noncomputable def td_transDeep : TransDeep tdW tdP tdL.ledgerJoint :=
  transDeep_of_ledger tdL.ledgerJoint td_mem_ledgerStrataV3 td_scope td_clean

/-- **The [R2-G1] plug, verified definitionally**: at the presenting datum the
row's `leakFree` field IS TD-5's typed carrier — `rfl`, never `True`. -/
theorem transDeep_of_lawful_leakFree (L : LedgerStratumData D W P)
    (hL : L.LedgerLawfulV3) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    (transDeep_of_lawful L hL hscope hclean).leakFree = LeakFreeCarrier L := rfl

end LeanUrat.B2D

#print axioms LeanUrat.B2D.transDeep_of_ledger_v2_unfillable
#print axioms LeanUrat.B2D.transDeep_of_lawful
#print axioms LeanUrat.B2D.transDeep_of_ledger
#print axioms LeanUrat.B2D.ledger_freshRowOn
#print axioms LeanUrat.B2D.td_transDeep
#print axioms LeanUrat.B2D.transDeep_of_lawful_leakFree
