# CU-1 — no-missing + interior adequacy + state binding — Phase-B attempt REV 3 (Fable, 2026-07-31)

LIGHT repair of the V29 hostile verification (`V29_cu1r2.jsonl`, verdict
**SOUND-WITH-GAPS**) of the rev-2 brief (`CU1_phaseB_verifybrief_rev2.md`).
V29 CONFIRMED the whole rev-2 structure: the interior/terminal split
("neither a gap nor overlap"; the μ = 1 leaf half's O5triple conditionality
explicitly admitted), the dressing construction ("creation-versus-recovery
confusion is repaired"), the global read-back quantification, the N-free
induction ("no box, decode, D-14, REAL≡, or N\* leaks into §3"), the width
route OL-2(b) → FR≡ → WGEO(c), the record-only non-saturation step, and the
top-site D-14 application. EVERY remaining finding was consumption
accounting: the §5 map "fails its own exact-exhaustiveness claim" at five
named points, and §4's SURJ dependency sentence ("exactly ∀-instances of
CU-1 + ADEQ") understates the walk clause's inputs.

Rev 3 repairs exactly those, per the orchestrator's charge (consumption-
accounting repairs only; induction byte-stable). The repaired brief is
`CU1_phaseB_verifybrief_rev3.md`, produced by COPYING rev 2 and editing
only: the preamble, the new §0-R3 disposition table, one bracketed
annotation in §0's trailing paragraph, §4's one dependency sentence, §5
(rows 2/3/5 rebuilt; rows 24–29 added; the exhaustiveness paragraph
rewritten), §8 item 9, and the closing line. **§§2–3 (the theorem, the
corollary CU-1-LVL, and the whole induction) are byte-identical to rev 2**
— verified by diff; §4's constructions/split and §§6–7 likewise (§4's sole
edit is the SURJ dependency sentence).

## 1. V29 findings → dispositions (full table = brief §0-R3)

| V29 finding | disposition |
|---|---|
| 1. split — PASS (scope caveat already displayed) | no change owed |
| 2. dressing — PASS | no change owed |
| 3. SURJ dependency sentence FALSE AS WRITTEN (walk clause needs CU-1-LVL, hence D-14/REAL≡/decode/(M6) bundle) | §4 sentence split by clause: construction + realization on f = ∀-instances of CU-1 + ADEQ; walk clause = ∀-instance of CU-1-LVL with its displayed bundle (rows 7–11, 15, 16, 18, 22). Statement unchanged; §8 item 9 matched |
| 4a. row 2 lists OL-2 (a)–(d); (a) unconsumed | row 2 narrowed to clauses (b)/(c)/(d); (a) displayed as consumed NOWHERE (strict weakening of CU-1's listed conditionality) |
| 4b. ADEQ's W4 cite of (L3)/the OL-3 note unlocated in row 3 | row 3 gains the ADEQ W4 site, classified: the consumed fact is (L3)'s y ∤ R_λ(f) (new row 25); the OL-3 note is only its home display site — no OPEN OL-3 content enters §4 |
| 4c. (L2)/(L3)/Def 2.21/(C1)/W-laws invoked in ADEQ but carried by no row | NEW rows 24–28, one per input, each with sites + home status ((L2)/(L3)/Def 2.21 = GMN literature transcriptions, byte-stable at O-2a rev 5 through V10–V25; (C1)/W-laws = O-2a §2 definitional); exhaustiveness paragraph re-assigned honestly (rows 7/17/18 = O-1thr vocabulary ONLY) |
| 4d. [F.2] cited independently, no standalone entry | NEW row 29: [F.2] standalone (stage-side tower / emitted-field-list display; sites §0′/step 2/step 3(d)); machine-side instantiation still rides (FR≡)/(D3) |
| 4e. O-2a Thm 2(A) listed with no displayed use | DROPPED (the charge's "drop" option): no sentence of §§2–4 uses (A); row 5 is now Thm 2(B) at the §4 split only; §0's trailing paragraph annotated |

Churn direction: NOTHING added to the dependence set — two listed
consumptions dropped as unconsumed (4a/4e, strict weakenings), one location
recorded (4b), six ALREADY-CONSUMED definitional/literature inputs made
explicit rows (4c/4d), one dependency sentence made truthful (3). Hence no
new gate is owed: rev 2's falsifier accounting (§7.4) carries verbatim, and
the depth-3 gate record (§7, SURVIVED) is untouched.

## 2. Files

* `lean/notes/openmath/CU1_phaseB_verifybrief_rev3.md` — the self-contained
  rev-3 brief (hand THIS to the next hostile pass; the map audit — §8
  item 5 plus the rebuilt §5 — is where V29's residue lived).
* `lean/notes/openmath/CU1_phaseB_attempt_rev3.md` — this record.
* Rev-1/rev-2 files, the falsifier suite, and all numerics UNCHANGED.

**Grade: PROVED-UNVERIFIED conditional composition (rev 3; first hostile
verdict SOUND-WITH-GAPS at rev 2, gaps all accounting, repaired here).**
Open residue unchanged from rev 2 §6: OL-1 + OL-2(b)/(c)/(d) + full OL-3
(GD-1..3) + O-1thr's interface residue ((M6b)(ii−)/(iii), (V1)/(V2)) + the
pending home passes + (N\*-MAJ)'s cluster discharge + the R-6 pins — every
item named with owner in brief §6 (note: the OL-2 conditionality is now
NARROWER than rev 2 listed, by the 4a drop).
