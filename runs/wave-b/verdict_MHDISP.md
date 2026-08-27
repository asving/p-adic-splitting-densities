# Verdict — MHDISP disposition of VHENS

**Date:** 2026-08-27

**Unit:** MHDISP

**Input:** `runs/wave-b/verdict_VHENS.md` (read in full)
**Overall:** **VHENS rejection sustained as to engine certification, but findings 1–2 are
STALE-VS-AMND.  Current pinned C.34/C.35 are not refuted.  The proposed engine is NOT proved,
and the MH transcription fleet MAY NOT FIRE.**

The chronology matters.  `HENSEL_ENGINE_2026-08-26.md` predates commit `b59e2dd5`, which
landed A-C.20 from MHENS's own degree-leak finding.  A-C.20 pinned every load-bearing C.34/C.35
label by `HasLabel ∧ D′ ∣ natDegree`, retained the old selector as `blockFactorLeaky`, and
retained its old multiplicity as `mult₂Leaky`.  The historical counterexample remains useful,
but it is not a refutation of the post-amendment signatures.

## Per-finding disposition

| # | classification | disposition and repair |
|---:|---|---|
| 1 | **(a) STALE-VS-AMND** | Correct against the pre-addendum prose, but not a current statement defect.  Current C.34 pins both witnesses and all `hsep` competitors by `HasLabel L fS ∧ (F.e₁*F.f₁) ∣ fS.natDegree`; the degree-3 candidate fails the pin.  The document now dates the chronology and retargets §7.2(1) to the historical pre-A-C.20 shape.  Current pinned C.34 is **not refuted**. |
| 2 | **(a) STALE-VS-AMND** | Correct chronology correction.  Current `blockFactor` and `BlockFrontier` are pinned; the unpinned selector/multiplicity survive only as `blockFactorLeaky`/`mult₂Leaky`.  The proposed `BlockFrontier′` is now the substance of landed `BlockFrontier`.  §7.2(2–3), §7.3, §8, MH.15, and MH.16 were corrected.  Current `blockFactor_spec` clause 3 is **not refuted**. |
| 3 | **(c) GENUINE CRITICAL** | Sustained.  M1(2)'s bare `slotRes` equality is false: slot multiplication carries a stage-letter factor.  The zero-`sorry` probe's executable `(2,2,3)`/`F₉` mirror proves `bareSlotRead 6 X² ≠ bareSlotRead 3 X * bareSlotRead 3 X`, while the inverse-twisted reads multiply.  The document withdraws M1(2), invalidates §3.1(d), and marks MH.1 **BLOCKED-CRITICAL**.  A generic carry formula/direct `twistRead` product theorem is required; the gate row is evidence, not that generic proof. |
| 4 | **(b) GENUINE JUSTIFICATION GAP** | Sustained.  The original Theorem M used weak `ℓ*(D′*h) ≤ u`, but `C130nv3.stageHeight_dev_endpoint_le_of_surv` and `lt_line_dev_term` need strict `<`.  The statement is corrected to the strict floor already carried by intended consumers.  The inventory now exposes the generic theorem's `hsurv` premise.  The newly landed `C132nv3.s2_dvSupp_mul_modByComposedKey_le` supplies survival only at the S2 composed-key frame (degree `< 4`); it does not close arbitrary-frame MH.1/M. |
| 5 | **(b) GENUINE JUSTIFICATION GAP** | Sustained.  OPEN-1/M1a, OPEN-3, MH.8, and OPEN-4/X1 are load-bearing for the engine or `BlockFrontier_of_context`.  The headline, section grades, node gate, and OPEN inventory now say so.  The already-landed conditional C.35 `_of_frontier` wrappers remain valid, but that does not prove their frontier premise. |
| 6 | **(b) GENUINE JUSTIFICATION GAP (current API partially patches availability)** | The cited C.46/C.47 declarations are private, so the original inventory/formula was not consumable as written.  Current C131f publicly exports the degree/`slotRes`/height pins, and C.14 publicly exports `exists_twistRead_preimage`.  The document now uses those APIs and corrects the lift target from bare `κ` to `η^twistExp(M)*κ`.  The probe proves an explicit exact-`twistRead` `stageLiftO` construction without a finiteness instance; the C.14 existential remains an alternative requiring `[Finite (ResidueField O)]`.  MH.5 is still blocked downstream of M and its five clauses remain to be proved. |
| 7 | **(b) GENUINE JUSTIFICATION GAP** | Sustained and load-bearing.  The original implication used an inequality in the wrong direction, and B.40's `inf_npHgt_le_gaussVal` is private.  MH.8 now explicitly requires a new public bounded-window upper comparison controlling the finite `F.h*j` loss, plus the reverse transport.  This looks repairable with a fixed window loss, but it is not proved here; Theorem A remains blocked. |
| 8 | **(b) GENUINE JUSTIFICATION GAP (repair mechanism verified)** | Sustained as a citation/API error.  C.04's `fieldStageField` is private and no global `Field (stageField …)` instance is exported.  The inventory now requires local reconstruction.  `MHDISP_probe.lean` constructs it from `instFieldResField`, `F.hresirr`, and `AdjoinRoot.instField` with a Lean-core footprint. |
| 9 | **(b) GENUINE JUSTIFICATION GAP / AUDIT SUMMARY** | Accepted as the aggregate audit, with findings 1–2 reclassified by chronology and finding 6 updated for the public C131f promotion.  The five positive spot-checks do not establish the global “proved” verdict.  The document's global status is corrected to **ENGINE NOT PROVED**. |

## Honest engine and node status

There is a genuine critical break in the proof artifact: M1(2) is mathematically false as
stated.  This does **not** establish that the intended twist-normalized mixed product theorem
M is false; the gate computation supports the corrected normalization.  It does establish
that the present document does not prove M and that its downstream arguments cannot be
transcribed as written.

Node gate:

* **BLOCKED-CRITICAL:** MH.1.
* **BLOCKED by the critical root and/or their own load-bearing gaps:** MH.0b, MH.0c,
  MH.2–MH.9, MH.11–MH.15.  MH.8 independently needs the corrected limit comparisons; MH.14
  independently needs X1.
* **HISTORICAL-ONLY:** MH.16, and only against `blockFactorLeaky`/`mult₂Leaky` (or an
  explicitly named pre-A-C.20 C.34 record), never against current pinned declarations.
* **Not refuted but insufficient to un-fence the fleet:** MH.0a and independent algebraic
  MH.10.

Current pinned C.34/C.35 are therefore **statement-consistent under this audit but still
proof-blocked**.  No claim of their construction, uniqueness, or maximality has landed from
this engine.

## Lean verification

Created `leanfinal/scratch/MHDISP_probe.lean` and ran:

```text
cd leanfinal
lake env lean scratch/MHDISP_probe.lean
```

Result: **exit 0**, zero `sorry`, zero declared `axiom`.  The probe checks:

* current C.34/C.35 pins and historical `*Leaky` names;
* C130nv3's strict floor and explicit `hsurv` premise;
* C132nv3's S2-only survival theorem;
* public C131f lift pins and both exact-twist lift routes;
* local construction of the stage-field `Field` structure; and
* the nontrivial `F₉` bare-slot carry and its cancellation by inverse twist.

Printed footprints are exactly `[propext, Classical.choice, Quot.sound]`; there is no
`sorryAx`.

## Fleet ruling

**NO — the MH transcription fleet may not fire.**  Before rescheduling it, land and review:

1. a correctly stated generic carry/`twistRead` product theorem replacing M1(2), together
   with M1a and generic survival under the strict floor;
2. the public bounded-window `W`/Gauss conversion lemmas for MH.8; and
3. X1 for the §8 residual-transport step.

Only after those gates are green may MH.2–MH.9 and MH.11–MH.15 be repriced and fired.
Isolated work on MH.0a or MH.10 is logically separable, but is not authorization for the
engine fleet.

## Deliverables touched

* `docs/in-progress/HENSEL_ENGINE_2026-08-26.md`
* `leanfinal/scratch/MHDISP_probe.lean`
* `runs/wave-b/verdict_MHDISP.md`

No commit was made.
