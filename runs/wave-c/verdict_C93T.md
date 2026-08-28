# Verdict — UNIT C93T: transcribe leanspec's `C93Census` block into landed Lean (2026-08-28)

## Re-grounding

`runs/wave-c/verdict_CHA.md`'s `genhnTow1` row named the next node: C.93's census block
(`leanspec/Leanspec/ChapC.lean`, `section C93Census`) — a `#check` manifest over seven
already-signed names, one per HYP.82 census item — "lives ONLY in signed leanspec ChapC" and
must be transcribed before `GenhnTow1At`'s `Tow1CensusAt` (I.07,
`docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` §I.07) can even elaborate: its
seven conjuncts bind, in order, exactly these seven names, and at that freeze note's writing
none were leanfinal declarations.

## What landed

`leanfinal/Uniformity/ChapC/C135c93.lean` — NEW file, namespace `Uniformity.Density.Tower`.
Verified: `timeout 580 lake env lean Uniformity/ChapC/C135c93.lean`, exit 0, zero
errors/warnings/`sorry`. Nothing imported by any landed file; no leanspec or other landed file
touched (read-only on leanspec, per charge).

**Verdict: PARTIAL — 4 of 7 census items land (one under a corrected name), 1 item half-lands
(new theorem this unit), 2 remain genuinely open.**

## Per-item table

| item | name | leanspec node | status |
|---|---|---|---|
| (1) | `towerLocus_iff_budget` | C.52 | **LANDED** verbatim — `Uniformity.Density.Tower.towerLocus_iff_budget` (`C131ag.lean:147`). Byte-verified against leanspec `:2059`. |
| (2) | `refine_invariants` | C.56 | **BLOCKED, unchanged.** `C150rb3.lean`'s own dispatch note: real content is a one-step Newton–Hensel refinement of `composedKey T`; no landed transport/step lemma. Sized at ~200–900 new lines. Cited, not re-derived. |
| (3) | `shadow_floor` | C.72 | **LANDED** verbatim — `Uniformity.Density.Tower.C131w.shadow_floor` (`C131w.lean:851`). Byte-verified against leanspec `:3507`. |
| (4) | `partial_floor_and_datum` | C.76 | **HALF-LANDED (new this unit).** Conclusion splits into clause (a) (open frame-opening floor) and clause (b) (residual datum). Clause (b) = C.26's already-landed `natDegree_dvResPoly` exactly (same `dvResPoly` term, swapped-order conjuncts, `F.Pin` definitionally `natDegree_dvResPoly`'s `hpin` type). Landed as `partial_floor_and_datum_of_floor`: signed binder list + one new explicit hypothesis `hfloor` carrying clause (a). |
| (5) | `window_band1` | C.58 | **LANDED** verbatim — `Uniformity.Density.Tower.window_band1` (`C150rb3.lean:93`). Byte-verified against leanspec `:2232`. |
| (6)(β) | `towerLocus_depth3_floor` | C.55 | **BLOCKED, census annotation corrected.** Census comment reads "DISCHARGED into (1)"; FALSE as a literal reduction — the signed axiom carries neither `hh` nor `[Finite (ResidueField O)]`, but every landed C.54-family floor (`towerLocus_dev_strict_floor` = `towerLocus_node_floor` up to unfolding `dv2Pin`) needs both. Whatever "pin-lattice arithmetic" the source uses must be independent of the budget floor; not landed anywhere. |
| (6)(α) | `gentow5_key_certificate` | C.90 | **LANDED, under a corrected name.** The bare-name match `C107ac14.gentow5_key_certificate` is the **superseded pre-A-C.21 carrier** (retained only for the do-not-edit refutation record `C132sg2.lean`; machine-refuted at the honest μ₃ instance, `C132sg3.s2Mu3_gentow5w_old_refuted`). The true current twin is `Uniformity.Density.Tower.C132sg3.gentow5_key_certificate_cleared` (byte-verified against leanspec `:3945`'s A-C.21-cleared `hres`/`Wle`). |

## Findings worth flagging (review queue)

1. **Item (6)(α) naming trap.** A name-only match (`gentow5_key_certificate` exists in both
   `C107ac14.lean` and, differently bodied, nowhere else) would have silently cited the
   *refuted* pre-A-C.21 carrier. Caught by byte-diffing leanspec's current `hres`/`Wle`
   against both candidates before writing the `#check`; the file deliberately checks the
   fully-qualified `C132sg3.gentow5_key_certificate_cleared` rather than opening `C107ac14`,
   so the correction stays visible at the call site.
2. **Item (6)(β) annotation correction.** The census's own "DISCHARGED into (1)" note for
   `towerLocus_depth3_floor` does not hold under the signed hypothesis list — a precise,
   citable reason (missing `hh`/`[Finite (ResidueField O)]`) rather than a bare "still
   blocked." Recorded in the file's docstring for whoever next touches C.54/C.55.
3. **Item (4) partial discharge.** `partial_floor_and_datum` was filed as "BLOCKED
   (unattempted)" in `runs/wave-b/verdict_CCUR.md`; re-examination found its second conjunct
   is a free corollary of already-landed C.26 machinery. Only the frame-opening floor (clause
   a) is real open content — narrows the remaining gap for whoever attacks it next.

## Amendment drafts

NONE. No signed statement was touched; `partial_floor_and_datum_of_floor` is a new,
distinctly-named conditional form (the `gentow5w_one_shape_of_letter_tie` genre), not a
substitute for the signed name.

## Verification record

* `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C135c93.lean` — exit
  0, output is exactly the four `#check` type-dumps plus one `#print axioms` line:
  `Uniformity.Density.Tower.partial_floor_and_datum_of_floor` depends on
  `[propext, Classical.choice, Quot.sound]` (Lean core).
* `git status` confirms only `C135c93.lean` was created; no leanspec or other leanfinal file
  touched.
* Byte-diffs performed by direct read-comparison (not `diff` — namespaces differ): items (1),
  (3), (5) confirmed identical binder lists/conclusions to their leanspec twins modulo
  `axiom → theorem`; item (6)(α)'s discrepancy is the headline finding above.

## GenhnTow1At status after this unit

`Tow1CensusAt`'s seven conjuncts can now bind 4 of 7 names directly (items 1/3/5/6α, the last
under the corrected name) plus a conditional form for item 4; items 2 and 6β remain
undeclared in leanfinal, so `Tow1CensusAt` is still not fully typeable end-to-end — the next
node is either closing items 2/6β (both genuinely open research, not transcription) or wiring
I.07's definition against the four-plus-one names now available and carrying items 2/6β as
explicit hypotheses at the `GenhnTow1At` definition site (a design choice, not this unit's
call).
