# Verdict — unit CIFACE (capstone interface nodes L0 / DT0 / W0 / WIN0)

**Charge** (brief `runs/wave-b/brief_CIFACE.md`): author the four interface nodes named
by CHFD's supply map — the precise Lean carriers a supplier campaign proves and the
capstone field consumes — elaborating against the landed corpus today, fence-audited,
with BLOCKED-BECAUSE over invention.

**Deliverables landed** (no commits, per brief):

* `docs/in-progress/CAPSTONE_IFACE_2026-08-26.md` — per-node design, supplier sketch,
  consumer derivation, anti-swallow audit (297 lines).
* `leanfinal/Uniformity/ChapI/IFC0.lean` (452 lines, namespace
  `Uniformity.Density.IFC0`) — `lake env lean` exit 0, ZERO sorry, ZERO new axiom; all
  23 AxChk-footer declarations print Lean-core-or-less footprints.
* This verdict.

## Per-node result

**L0 — PROVED-EXACT decomposition.** Four supplier `Prop`s at the capstone `ladder`
field's byte-exact binder block and guard, one per E.24 `LadderSupply` field:
`LadderPackageSupplier` (HE7A/`Nonempty RungInterface`), `LadderLB1Supplier`,
`LadderMP1Supplier`, `LadderVarthetaSupplier` (sitewise ϑ at `i ≥ 3`).  Exit gate
`ladderField_iff_suppliers`: the four are JOINTLY EQUIVALENT to the field (both
directions proved; `LadderField` pinned definitionally to `CapstoneHypotheses.ladder`
by an `example` that fails the build on drift).  E-D6 universe discipline kept
(`uW` bound explicitly; `O, K` at `Type 0` as the field pins them).

**DT0 — PROVED-EXACT decomposition, two suppliers not four.** The cumulative `WFrame`
legs over all live levels flatten to the per-level family `∀ j, 3 ≤ j → j < r →
GentowW (A j) (q j) (R j) (w j)` — so `DeepVarthetaSupplier` + `DeepGentowSupplier`
are jointly equivalent to the `deepTwist` field (`deepTwistField_iff_suppliers`, both
directions).  The `GentowW` supplier is stated at D.44's raw identity, so per-level
campaign endpoints (μ₃'s depth-2 tooth, when OPEN-RP1-TRANSPORT clears) plug in
directly.  Per-live projections on the conjunct itself also landed
(`deepTwistConjunctLive_vartheta_at` / `_gentowW_at`).

**W0 — INTERFACE LANDED, canonical guard BLOCKED-BECAUSE.**  `ArisingWeldSiteSupply`
binds the three weld legs together (A-I.1's I-D7/I-D8 trigger: `JD0Box2`, `GenhnBox2`,
and the owed `w1`, the last restricted to the arising line subtype), each guarded by an
arising predicate.  Machine teeth: at TOTAL guards the socket is exactly F.28's refuted
all-sites `WeldObligations` (`arisingWeldSiteSupply_total_iff`) and is REFUTED at the
F12w `Fin 1`/`ZMod 3` instance (guard load-bearing); at EMPTY guards it is trivially
inhabited (fabricability disclosure — D-D12 genre).  Fold half
`ArisingWeldSiteSupply.of_strikes` composes F04w strikes into the jd0 leg.
BLOCKED-BECAUSE: no landed declaration exports weld sites from arising chapter-C/H
data (`rg`: `ValueDictSite`/`CarrySite` occur only in ChapF) — the missing mechanism is
a SITE EXPORT, the weld analogue of CC-12's views; until it lands the guards stay
parameters and the socket is a campaign target, NOT a capstone-field candidate.

**WIN0 — INTERFACE LANDED, canonical guard BLOCKED-BECAUSE.**  `StageWindowData` (the
pre-`hwin` window/loss datum), `StageWindowData.Pinned` (= the `hwin` clause, `Iff.rfl`
pin + projection `stageWindowDataOf_pinned := st.hwin` + extension
`stageInterfaceOfPinned` — the byte-tie in both directions, hwin asserted nowhere), and
`WindowPinningBody Arises n` demanding `Pinned` at guarded data only.  Teeth: unguarded
reading REFUTED at a concrete legal genre with the zero datum (I-D13 genre); empty
guard trivially inhabited (disclosure).  The canonical guard = the GENHN-CAP-GEN
reader rule, not formalized (H.89w is `e₁ = 2` lemmas only) — supplier campaign's
first target.  The signed `WindowPinningAt` `True` placeholder is untouched.

## Trust boundary / review flags

NEW statements (all flagged, none signed): the 4 L0 suppliers, the 2 DT0 suppliers,
`LadderField`/`DeepTwistField` (pinned name-carriers), `ArisingWeldSiteSupply`,
`StageWindowData` + `.Pinned`, `WindowPinningBody`.  No leanspec edit; every eventual
re-sign is noted in the doc as a later recorded owner amendment.  Honest-vacuity note
carried in the doc: at `n = 2` no landed witness inhabits either socket guard (S2 teeth
are degree 4), so supplier campaigns need a non-vacuity tooth at their exit gates.

## Verification record

`cd leanfinal && lake env lean Uniformity/ChapI/IFC0.lean` → exit 0, no diagnostics;
the 23 `#print axioms` lines show `{propext, Classical.choice, Quot.sound}` subsets
only.  Probed incrementally (§1, §§1-2, §§1-3, full).  The doc's Lean snippets match
the landed signatures (name drift reconciled post-landing).
