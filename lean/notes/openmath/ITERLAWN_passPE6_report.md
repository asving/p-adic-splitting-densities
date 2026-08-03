# ITERLAWN-PE6 — Fable round-6 pass on the 362d118 text: NOT-CLEAN 0C/1G — the census gap PC5 found concurrently, CONFIRMED AND CLOSED BY MACHINE; zero mathematical defects; the machine census (194/194 hits mapped) installed as the enumeration of record

## VERDICT BLOCK

* **Grade: 0 critical / 1 gap (+2 nits).** The single gap is the SAME defect
  the concurrent Codex pass found (PC5 @ c2992a0, GAPS-ONLY 0C/1G): the r5
  closed-census sentence — "the 23 sites enumerated by the stated grep
  patterns over the note text AS OF commit 0672082" — is still not a correct
  census of the pinned text. My machine census (§3, the whole point of this
  pass) proves it mechanically and in BOTH directions: (a) the 8 stated
  patterns hit **7 additional in-genre claim-site families (F1–F7, ≈15
  textual sites)** beyond rows 1–23 — every one content-TRUE, none false —
  including both PC5 sites (F2 = the S4.6 "WEIGHT clauses only" pair; F1 =
  the "INSTANCE EVIDENCE ONLY, never proof steps" family, which is 5 sites,
  not 1); and (b) rows 13 and 18 match NO stated pattern (21 of 23 rows are
  pattern-derived; two were judgment-added). Content consequence: none —
  **zero false dependency claims exist anywhere in the note** (the r4
  substantive result, now confirmed by a fourth independent sweep and for
  the first time by machine).
* **Errata-r5 fidelity: VERIFIED in full** (§2) — insertion-only (20+20
  lines, reconstruction byte-exact), row 23's content independently
  re-verified TRUE on three legs, census arithmetic right, ledger append
  faithful to PE5.
* **The leak question (charge item 1), adjudicated:** the REGRESS-PROOFING
  **works for its stated purpose** — dating the claim to 0672082 makes
  forward leakage impossible by construction, and the r5 bracket itself obeys
  its own no-new-first-order-claims constraint (its only dependency content
  is the adjudication of the quoted gloss). What the dating does NOT do is
  cure under-enumeration already inside the pinned text — PC5's finding,
  which §3 completes. (PC5, independently: "Dating the assertion successfully
  prevents future brackets from expanding its scope; it does not cure
  under-enumeration already present in the pinned text." Concur exactly.)
* **Execution re-runs: both exit 0, zero violations** (§4). diag
  byte-identical (md5 `7c72c4c6c0a953ebd41a56eab1e266e1`); reimpl
  semantically identical, sole diff = two wall-clock digits (0.1s→0.2s on
  I4A/I4B) — the PE4-classified benign species.
* **Round-6 consequence:** the 2-clean bar is NOT met (PC5 0C/1G + PE6
  0C/1G — one shared defect, dual-confirmed from decorrelated contexts).
  The cure is pre-designated by the orchestrator's PC5 adjudication:
  **errata round 6 = THIS report's §3 machine census** as the enumeration of
  record (complete by construction; subsumes PC5's two sites). A future
  closed restatement should cite this census, not a hand count. Trajectory:
  2C/3G → 0C/2G → 0C/1G → 0C/1G → 0C/1G → 0C/1G → 0C/1G — still zero
  mathematical findings since composition; the residue has been census
  meta-sentences for three straight rounds, and hand-census is the proven
  failure mode.

## §1 Charge, identity, pins

ITERLAWN-PE6, Fable round-6 fresh verifier on the general-n note
`lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` as amended at 362d118
(errata round 5). Duties per charge: (1) errata-r5 fidelity incl. the
independent S₀ verification and the leak adjudication; (2) THE COMPLETENESS
CHECK by machine over the pinned 0672082 text; (3) execution re-runs;
(4) fresh content sweep; (5) this report + ledger + scoped commit.

Pins: note @362d118 md5 `3e83feae4d95020c8239c6e41154e1f4` (= HEAD text at
pass start); pinned base @0672082 md5 `5811db126d1ed0824e4870b20e0fd774`
(matches the PE5 pin); scripts `iterlawn_pe_reimpl.py` md5
`cae45db2318b89520dd5484466ef3604`, `iterlawn_diag.py` md5
`cd7581b7fd9df555e517b69556199ef3` (both = the standing pins). Mid-pass
event: PC5 landed at c2992a0 (report read AFTER my own census classification
was already drafted; the F1/F2 adjudications below were made before reading
it, then checked against it — F1/F2 ⊇ PC5's two sites).

## §2 Errata-r5 fidelity (VERIFIED, six legs)

1. **Additive/insertion-only.** `git diff e4a8e8a..362d118` numstat: 20+0 on
   the note, 20+0 on the bridge ledger; note untouched between 0672082 and
   e4a8e8a (0-line diff). Deleting the 20 inserted note lines (1148–1167 of
   the r5 text) reproduces the 0672082 file **byte-exactly** (`diff -q`
   clean). Single hunk, no context drift.
2. **Row 23's content, independently re-verified TRUE (three legs).**
   (i) Token census: S₀ occurs in the pinned text at exactly lines 201
   (`[composed shift; S₀ unused]`, the recursion display's tag) and 207–208
   (the convention gloss itself); line 121's `[IL S0]` is a section label of
   the cited note, not the quantity. PE5 defined the claim-site as
   {display tag L201 + gloss L207–208}, so "no other S₀ occurrence" is
   correct under the cited record (see nit N2). (ii) Consumer instantiation:
   every consumer of composed shifts instantiates j ≥ 1 — SHIFT (j = n..1),
   D_j-INT (j ≥ 1), (★)-POS (statement range j = n..1; the j = 1 step needs
   no descent to 0), WINDOW (S₁), the descent lemma (states "all S_j" incl.
   S₀ but nothing downstream consumes the S₀ instance), EXP-KIT(c) kernels
   (shift T = S_j at levels j = n..1). (iii) A leg the prior passes did not
   display: **COR-3's own bullet split corroborates non-consumption** — the
   "Interior e_{j−1} = 1" passthrough bullet (L1059, asserts S_{j−1} = S_j)
   is scoped INTERIOR, while the j = 1 case gets its own bullet ("e₀ = 1:
   D₁ = 0, the letter z₁ leaves the law") with no S₀ clause. The note's only
   near-S₀ display deliberately avoids S₀. Referee side confirmed: the
   reimpl computes S[0] and reads it only in K13/K12c/K15 as strengthenings
   (PE5's classification re-checked at source, lines 511–517, 649, 901–913).
3. **Census arithmetic.** The pinned table has rows 1–22 (verified by
   direct read); 22 + 1 = 23. The row-23 line in the bracket is well-formed
   against the table schema.
4. **Ledger append faithful.** The r5 bridge block's trajectory line
   matches the pass-report grades (2C/3G, 0C/2G, then 0C/1G ×4); the
   "POSITIVELY CONFIRMED" clause is a fair quote of PE5 §Classification.
5. **Quote fidelity.** The r5 bracket's gloss quote is a byte-exact
   substring of L207–208 (modulo the leading "so " and closing paren); the
   row-23 ellipsis quote is fair.
6. **Regress-proofing honesty.** Adjudicated in the verdict block: works
   against forward leaks by construction; the r5 bracket makes no
   first-order dependency assertion beyond its quoted content; does not (and
   textually does not claim to) re-derive the pinned text's enumeration —
   but its "23 sites" count inherits the hand census, which is where the gap
   (§3) lives.

## §3 THE MACHINE CENSUS (charge item 2 — the enumeration of record)

**Method.** The 8 stated patterns run programmatically over all 1,417 lines
of the pinned 0672082 text, case-insensitive, with nets WIDENED where the
stated form is narrower (recorded here as part of the census definition):
`\bonly\b`, `\balone\b`, `not\s+affected`, `self-contained`, `free`
(substring — catches engine-free etc.), `independen` (catches
independent/-ly/-ce), `consum` (catches consume/-s/-d/consumption — the
PE5-F1 lesson), `\bnever\b`. **Result: 194 raw hits on 147 distinct lines.**
Per-pattern: consume 84, only 51, never 18, alone 15, self-contained 9,
independent 8, free 6, not-affected 3. Every hit is classified below;
**zero hits are unadjudicated**. Full line-by-line map in Appendix A.

**Disposition summary (all 194 hits):**

| class | hits | meaning |
|---|---|---|
| R-rows | 88 | at a tabulated row's site, duplicate site, or dated cure bracket (rows 1–12, 14–17, 19–23) |
| F-families | 21 | in-genre claim sites BEYOND the 23 rows — the gap's content; all adjudicated below, all TRUE |
| A apparatus | 53 | the r4 sweep bracket + table + close (L1096–1147) and the S10 hostile-charge display (L1391): quotations/adjudications, not new claims |
| B quoted record | 8 | rule-8 pastes / the [IL3] acceptance capsule / r38-bracket quoted scope text (L29, 99, 528, 1170–71, 1188) |
| C non-genre | 18 | math content ("E₁ ≠ 0 only in…"), status labels ("MEASURED GREEN only"), empirical ("never TIGHT"), narrative, grammatical "alone" |
| D positive displays | 6 | visible positive-consumption statements with no exclusivity content (e.g. "Weights consumed below (IH (P-DS))") |

Rows with pattern hits: 1–12, 14–17, 19–23 (21 rows). **Rows 13 and 18 have
zero pattern hits** (row 13's "[No DCX exclusion needed…]" and row 18's "no
cross-level denominator EVER forms" match no stated pattern) — they were
enumerated by editorial judgment, which falsifies the r5 sentence's
attribution of all 23 to the patterns (nit N1; harmless direction:
over-coverage of the table cannot hide a site).

**The F-families (the sites the hand census missed; each adjudicated):**

* **F1 — evidence-only universal, FIVE sites** (L50 header, L319 S1
  manifest, L789 S4.6 box, L1207 S7 row 11, L1327 S8 close): sealed/measured
  artifacts are instance evidence, never proof steps. **TRUE** — verified
  this pass: no proof body in S2–S5 cites sealed data as a step; the S6.3
  DCX witnesses are concrete instances (legitimate existence witnesses, not
  statistical evidence); row 2's adjudication column already carries the
  clause ("sealed artifacts evidence-only"). ⊇ **PC5 site 2** (PC5 cited
  L319 alone).
* **F2 — engine "WEIGHT clauses only", TWO sites** (L865 Case II-2, L890–91
  Case II-3): the (RM-(n−1)) call on E₁ᴵᴴĈ consumes only the weight/line
  clauses of the engine output, never its read clause. **TRUE — re-derived
  this pass**: in II-2 the downstream argument uses only line bounds on
  R¹/Q¹ (slot k+1 line ≥ B_n + h_{n−1}, slot k+2 ≥ B_n + 2h_{n−1}); the only
  read entering C₀ is R⁰'s (the E₀ᴵᴴĈ call, whose read IS consumed, as the
  display says); in II-3 the attained read is E₀ᴵᴴ's at slot e_{n−1}−1.
  ⊇ **PC5 site 1** (PC5 cited the II-3 instance).
* **F3 — the no-equivocation universal** (L623: "NO site consumes one
  reading while asserting the other"): adjudicated at r1 (E1 verdict NO
  EQUIVOCATION; execution referee ssum-vs-S separation 22,369/0 +
  orchestrator site-by-site re-check, commit ac03cb1). Standing.
* **F4 — paste-site exclusivity** (L73: "the full paste recurs ONLY at
  operative consumption sites"): document-structure claim, audited at r1/r2
  (E6 byte-match of pastes; the r2 bracket-count corrigendum). Standing.
* **F5 — honest-grade-at-every-consumption** (L26): citation-hygiene
  universal; the rule-8 apparatus has been audited coherent by PC3/PC4/PC5;
  stale grade wording is governed by the r38 supersession clause. Standing.
* **F6 — the r38 ALONE-clauses** (L1160, L1176 ×2, L1193): grading-census
  claims inside the dated r38 ledger bracket ("upgrades to conditional on
  (RM-m) alone"; "rung 3 = conditional on (RM-2) ALONE…"; "the remaining
  distance… the two displayed families alone"). **TRUE in the ledger's
  grading semantics** (off-DCX opens at rungs ≥ 3 = exactly the RM family
  given the two acceptances; the L1193 distance correctly adds
  (W-MULT-DCX-m) for the DCX part, matching S7 row 7). Adjudications on
  record: PC3/PE4 full-S7 row-by-row audits, PC4 adversarial re-derivation,
  PE5 §adjacent explicit disposal; genre note — these are conditionality
  arithmetic over the ledger, not consumption claims adjudicable against
  proof bodies (the r4 bracket's own verification-target definition), which
  is why no prior pass tabulated them. The machine census lists them anyway:
  under the strict reading they are pattern-enumerated claim sites.
* **F7 — read-only execution hygiene** (L1287–88 S8, L1337 S9): the
  diagnostic consumed sealed artifacts read-only, imports byte-untouched.
  Verified operationally across passes (PE3's byte check; this pass's
  byte-identical re-runs).

**The gap, stated exactly (shared with PC5):** the r5 closed sentence
asserts the pattern census of the pinned text = the 23 tabulated sites. The
machine census shows the pattern census = 21 of the 23 rows PLUS the
F1–F7 families (≈15 sites). Every extra site is content-true, so — for the
third consecutive round — the defect is a census meta-sentence, with zero
grade or mathematical impact. The cure of record (per the orchestrator's
PC5 adjudication): restate exhaustiveness as THIS machine census — "194
hits, 147 lines, over the 8 stated widened patterns on the 0672082 text,
each hit mapped per ITERLAWN_passPE6_report.md §3/Appendix A; zero
unadjudicated hits; zero false dependency claims."

## §4 Execution re-runs (charge item 3)

* **iterlawn_pe_reimpl.py:** exit 0; `== BASELINE VIOLATIONS: 0 ==`; 940
  pairs; per-family totals match PE5 exactly (K1_shift 3444, K3_star 3444,
  K7_law 940, K10_sharp2 940, …); mutations `7/7 caught+visible`; elapsed
  7.0s. Fresh md5 `f3669123e29208ae750434123b47a5b7` vs committed
  `cfad79439821551f9c6a572f5d627d0b`: sole diff = two per-instance
  wall-clock digits (I4A and I4B lines, `0.1s` → `0.2s`) — the identical
  benign species PE4 classified; zero count/violation diffs.
* **iterlawn_diag.py:** exit 0; **byte-identical** (fresh md5
  `7c72c4c6c0a953ebd41a56eab1e266e1` = committed); `== VIOLATIONS: 0 ==`,
  `DIAG VERDICT: CLEAN`; count block independently re-summed this pass:
  18 families, **total 5,311** (matches the S8/PE5 figure).

## §5 Fresh content sweep (charge item 4)

* Recursion display ↔ reimpl transcription re-checked at source: D_j and
  S_{j−1} lines match `constants()` (lines 511–517) exactly (baseline
  sgn = −1); the j = 1 convention algebra checks (w₀Φ₀ := 0, γ₁ = h₀ ⟹
  S₀ = D₁h₀ + S₁ℓ₀′).
* (★)-POS active-case identity re-derived: e_{j−1}S_{j−1} = S_j +
  (s_j-defect)γ_j follows from the recursion given D_j-INT's
  s_j-defect = e_{j−1}D_j − ℓ_{j−1}S_j and 1 − ℓ_{j−1}γ_j =
  e_{j−1}(ℓ_{j−1}′ − ℓ_{j−1}w_{j−1}Φ_{j−1}) — consistent.
* S4.6 II-2/II-3 weight-bound arithmetic spot-checked while adjudicating F2
  (slot k+1 and R¹ line computations re-done; agree with the display).
* No new mathematical finding. The standing surface (architecture, integer
  layer, EXP-KIT, T-notation separation, both S7 branches, corollaries, S8
  claims) is coherent — concurring with PC5's independent content pass.

## §6 Nits (recorded, no cure owed on their own)

* **N1.** The r5 sentence "the 23 sites enumerated by the stated grep
  patterns" over-attributes: 21 of 23 rows are pattern-derived; rows 13/18
  are judgment-added (no pattern token at either site). Direction harmless
  (table ⊇ pattern census); subsumed by the §3 cure.
* **N2.** The r5 bracket's compression "S₀ appears nowhere else in the
  note" is exact only under PE5's site definition (site = display tag L201
  + gloss L207–208, which the bracket cites as its authority); read cold,
  L201's `S₀ unused` is another token. Display precision only — L201
  asserts the same non-consumption.

## §7 Provenance appendix — see Appendix A (line-by-line census map) below.

## Appendix A — the machine-census line map (pinned 0672082 text; 194 hits, 147 lines; every line's disposition)

Row-site / duplicate / cure-bracket lines (88 hits):

```
R1 : 139                    R2 : 69,308,313,316
R3 : 54,58,59,64            R4 : 248
R5 : 219,944,947,954        R6 : 274
R7 : 345                    R8 : 420
R9 : 244,422,444,445,1198,1358
R10: 458                    R11: 518,520,529,531
R12: 567,569,572,573,575,581,583,586
R14: 607,608,616            R15: 710,711
R16: 774,775                R17: 952
R19: 1200
R20: 1212,1216,1218,1223,1226,1229,1230,1234,1235,1237,1240,1247
R21: 162,328,1265,1266,1267,1271,1272,1274,1276
R22: 305,405,415,1006,1353,1355,1365,1373,1375
R23: 208
(rows 13 and 18: zero pattern hits — judgment-added rows; see nit N1)
```

Site-families beyond the rows (21 hits; §3 adjudications):

```
F1: 50,319,789,1207,1327    (evidence-only universal — TRUE; ⊇ PC5 site 2)
F2: 865,891                 (engine WEIGHT-clauses-only — TRUE; ⊇ PC5 site 1)
F3: 623                     (no-equivocation universal — r1 E1, 22,369/0)
F4: 73                      (paste-site exclusivity — r1 E6 / r2 corrigendum)
F5: 26                      (honest-grade-at-every-consumption — rule-8 audits)
F6: 1160,1176,1193          (r38 ALONE-clauses — TRUE in grading semantics;
                             PE5 §adjacent + PC3/PE4 full-S7 + PC4)
F7: 1287,1288,1337          (read-only execution hygiene — re-run verified)
```

Apparatus / quoted-record / non-genre / positive-display lines:

```
A (53): 1102,1103,1104,1113–1124,1126–1129,1131–1134,1144 (the r4 sweep
        bracket, its pattern list, the 22 quoted rows, the close) + 1391
        (the S10 hostile-charge display — a charge, not a claim)
B (8) : 29,99,528,1170,1171 (the [IL3] acceptance capsule / rule-8 paste
        quotes; L528 sits inside row 11's site), 1188 (status label in the
        r38 quote)
C (18): 36 (grading-policy truism), 49 (status label), 389,396 (the
        never-tight EMPIRICAL observation, labeled as such), 466
        (provenance cross-ref), 643,693,705,884,963,1057,1067 (math
        content "only"), 803 (grammatical "alone"), 1069 (math term
        "representative independence"), 1302 (diag provenance), 1329
        (temporal "never"), 1399,1401 (forward-consumers narrative)
D (6) : 266,267 (the ITER-PKG package description; the consumes-more-than-
        package risk is the displayed S10 hostile charge (i), not an
        asserted exemption), 715,736,737 (positive IH-consumption notes,
        no exclusivity), 932 (grade propagation, ledger-displayed)
```

Sum check: 88 + 21 + 53 + 8 + 18 + 6 = 194. Zero unmapped hits.

## Appendix B — provenance

* Commit chain verified: 0672082 (r4 text) → 4d0eeb1/… → b71f170 (PC4) →
  e4a8e8a (PE5; note file untouched since 0672082, 0-line diff) → 362d118
  (r5, insertion-only 20+20) → c2992a0 (PC5 report, mid-pass).
* Note md5s: 0672082 text `5811db126d1ed0824e4870b20e0fd774`; 362d118 text
  `3e83feae4d95020c8239c6e41154e1f4` (= HEAD at pass start). Reconstruction:
  deleting lines 1148–1167 from the r5 text reproduces the pinned file
  byte-exactly.
* Script md5s: reimpl `cae45db2318b89520dd5484466ef3604`; diag
  `cd7581b7fd9df555e517b69556199ef3`. Output md5s: §4.
* Key quoted slices (verbatim, with line numbers in the PINNED text):
  L201 `[composed shift; S₀ unused]` · L207–208 `(Convention at j = 1:
  w₀Φ₀ := 0 and γ₁ = h₀, so S₀ = D₁h₀ + S₁ℓ₀′ — computed by the recursion
  but consumed by nothing.)` · L121 `res and lift as in [IL S0]` (citation
  label, not the quantity) · L865 `(read clause consumed), E₁ᴵᴴĈ = R¹+Q¹Φ
  (WEIGHT clauses only)` · L888–891 `E₀ⁿᵉʷ = E₀ᴵᴴΦ^{e_{n−1}−1} − R¹ − Q¹Φ
  (engine on E₁ᴵᴴĈ, weight clauses only)` · L319 `INSTANCE EVIDENCE ONLY,
  never proof steps` · L1059–60 `**Interior e_{j−1} = 1:** … D_j = 0 and
  S_{j−1} = S_j (passthrough)` vs L1061 `**e₀ = 1:** D₁ = 0, the letter z₁
  leaves the law` (no S₀ clause) · L1033–34 `no cross-level denominator
  ever forms` (row 18 — "ever", not "never": no pattern hit) · L632 `[No
  DCX exclusion needed for this clause — L6-(n), S4.2.]` (row 13: no
  pattern hit).
* PC5 cross-check: `ITERLAWN_passPC5_report.md` @ c2992a0 read AFTER my
  classification draft; its two sites map to my F1 (L319 member) and F2
  (L891 member); its hygiene-execution NOTE (no sandbox) is covered by this
  pass's §2 leg 1.
