# STATEMENT LEDGER — 2026-08-10 (unit S-0)

**Unit:** S-0, the simplification campaign's byte-tracking instrument
(SIMPLIFICATION_BLUEPRINT_2026-08-10.md S5.1). One row per NAMED
STATEMENT (THEOREM/LEMMA/COROLLARY/PROPOSITION/DEFINITION block with its
label) in the 26-text accepted corpus (blueprint S1 corpus map).
**Instrument:** `verification/openmath/statement_ledger.py --check`
re-extracts and compares md5s against the sealed baseline
(`statement_ledger_baseline.json`); exit 1 with a diff on ANY changed or
deleted statement; additions allowed. This is blueprint S5.3 item 3's
tripwire: "a simplification never weakens a statement" — consumption
checks must display absorbed statements md5-identical to this ledger.

**Baseline:** repo HEAD `788bba26932c`, generated
2026-08-12T18:08:30+00:00, extractor S0-v1.
**Totals:** 178 statements over 26 notes; 5 unlabeled
(numbered deterministically); 4 truncated at the 120-line cap.

**Normalization (declared):** blockquote markers stripped as block
syntax at extraction; then whitespace-collapse ONLY. A single-token
change to any statement changes its md5 and fires the tripwire.
**Grade provenance:** the blueprint S1 corpus map (25 texts ACCEPTED 2/2;
JD0 PROVED grade, machine 68,523/0, sub-bar) — the notes' own status
headers are heterogeneous free text and are NOT parsed for grades.
**Flags:** T = span truncated at cap; S = span contains struck (~~)
text; U = unlabeled (label assigned by deterministic numbering).

## S1. The ledger (one row per statement)

### LIFTCORNER_2026-08-08.md — commit `33225dd9`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM (unlabeled) | 962–992 | `b652f278` | U |
| 2 | COR 1 | 994–998 | `8bcb7d3e` | — |
| 3 | COR 2 | 1000–1004 | `650d435a` | — |
| 4 | PROP (unlabeled) | 1034–1069 | `3859bfb8` | TU |

### GRTW2_PROOF_2026-08-08.md — commit `8584db40`, grade: ACCEPTED 2/2, 5 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA W2-C1a | 474–503 | `be975688` | S |
| 2 | THEOREM W2-C1 | 507–526 | `ee27f7cd` | — |
| 3 | LEMMA W2-ID1 | 707–779 | `cd5037b9` | TS |
| 4 | LEMMA W2-T3E | 910–936 | `6bde997e` | — |
| 5 | THEOREM W2-C1-CORR | 1486–1529 | `a8ea19b6` | — |

### GRTJA_PROOF_2026-08-08.md — commit `76fa9d51`, grade: ACCEPTED 2/2, 7 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM JA-PIN | 110–169 | `663c87cc` | S |
| 2 | THEOREM JA-RES | 307–315 | `8a1345fc` | — |
| 3 | COROLLARY JA-VDIND | 326–335 | `fd8c3357` | — |
| 4 | COROLLARY JA-MIN | 388–411 | `68a50d4b` | — |
| 5 | THEOREM JA-EPS-CORR | 975–997 | `cbea05ad` | — |
| 6 | COROLLARY JA-MIN-CORR | 1033–1035 | `10ce0f52` | — |
| 7 | THEOREM JA-GRID-CORR | 1079–1100 | `e24b7823` | — |

### GRTJB_PROOF_2026-08-08.md — commit `68a993fa`, grade: ACCEPTED 2/2, 7 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM JB-DEV | 1402–1495 | `51c79ed1` | TS |
| 2 | LEMMA JB-AFF | 1615–1621 | `8f37bc75` | — |
| 3 | THEOREM JB-VTX | 1623–1694 | `6b2498e5` | S |
| 4 | THEOREM JB-TREE | 1790–1903 | `123aa097` | S |
| 5 | COROLLARY (unlabeled) | 2064–2169 | `8149211c` | SU |
| 6 | LEMMA JB-EPS | 2171–2177 | `83fbac6b` | — |
| 7 | THEOREM JB-CREAD | 2186–2221 | `af2ebcbb` | S |

### GRTJC_PROOF_2026-08-08.md — commit `e2403a2b`, grade: ACCEPTED 2/2, 13 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM W-6 | 664–684 | `4cddd908` | S |
| 2 | LEMMA JC-LOC | 1037–1045 | `571c13dc` | — |
| 3 | LEMMA JC-PIINV | 1106–1115 | `0a80a843` | — |
| 4 | LEMMA JC-BSURJ | 1145–1153 | `dec2acb5` | — |
| 5 | COROLLARY JC-COB | 1335–1413 | `478e5ada` | S |
| 6 | THEOREM W-7 | 1419–1438 | `15ddb376` | S |
| 7 | THEOREM JC-CARRY-m | 1479–1485 | `dbd49a4c` | — |
| 8 | THEOREM JC-INNER | 1512–1516 | `f59557de` | — |
| 9 | THEOREM JC-IND | 1552–1553 | `72f6a958` | — |
| 10 | THEOREM W-8 | 1658–1664 | `a400bc0a` | — |
| 11 | COROLLARY W-9 | 1777–1787 | `222be4a8` | — |
| 12 | LEMMA JC-RANKMULT | 2919–2932 | `60da5ac7` | — |
| 13 | COROLLARY (unlabeled) | 2955–3000 | `ac4006e7` | U |

### WELDMASTER_2026-08-08.md — commit `35cc703f`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM WELD-M | 284–311 | `30b82e4d` | — |
| 2 | THEOREM WM-COB | 344–369 | `4813269b` | — |
| 3 | THEOREM WM-FENCE | 483–599 | `f023af52` | S |
| 4 | THEOREM WELD-M-PKG | 1123–1152 | `c2cde3b4` | — |

### JD0_PROOF_2026-08-08.md — commit `438afac2`, grade: PROVED (machine 68,523/0; sub-bar), 2 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA J-D0 | 49–57 | `68254d43` | — |
| 2 | LEMMA J-D0 #2 | 513–529 | `c2367145` | — |

### SIGMALAW_PROOF_2026-08-08.md — commit `25ce1e65`, grade: ACCEPTED 2/2, 5 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA SL-L1 | 122–133 | `69c5cb7c` | — |
| 2 | THEOREM SL-1 | 168–177 | `2ffdbb04` | — |
| 3 | LEMMA SL-L2 | 197–311 | `1868220f` | T |
| 4 | COROLLARY SL-C1 | 332–335 | `0f4d08f8` | — |
| 5 | COROLLARY SL-C2 | 361–372 | `738e49e8` | — |

### W11_PROOF_2026-08-08.md — commit `87d8923b`, grade: ACCEPTED 2/2, 1 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM W-11 | 109–148 | `58d463fc` | S |

### W12_PROOF_2026-08-08.md — commit `06958241`, grade: ACCEPTED 2/2, 8 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM W-12.A | 197–231 | `06b4e5d3` | — |
| 2 | THEOREM W-12.C | 250–266 | `afe5b2c0` | — |
| 3 | THEOREM W-12.D | 267–315 | `70bc878f` | — |
| 4 | LEMMA W12-S2.1 | 469–473 | `a9794cfa` | — |
| 5 | LEMMA W12-L0 | 694–706 | `239c0ffe` | — |
| 6 | LEMMA W12-L1 | 742–753 | `3690f7d5` | — |
| 7 | LEMMA W12-S3.2 | 837–839 | `3ee0843d` | — |
| 8 | LEMMA W12-HT | 2237–2274 | `bc1c91b9` | — |

### HMENU3_PROOF_2026-08-08.md — commit `d665620b`, grade: ACCEPTED 2/2, 5 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM HM3.A | 113–144 | `bb779df1` | — |
| 2 | THEOREM HM3.B | 145–210 | `f07e9cb8` | S |
| 3 | THEOREM HM3.C | 211–225 | `288959f7` | — |
| 4 | COROLLARY HM3.D | 231–267 | `3ba094ba` | — |
| 5 | LEMMA HM3-4 | 383–385 | `4c9dd40d` | — |

### HEX3_PROOF_2026-08-08.md — commit `fb83ff16`, grade: ACCEPTED 2/2, 3 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM HEX3.A | 123–143 | `30756ab1` | — |
| 2 | THEOREM HEX3.B | 144–157 | `01183b2d` | — |
| 3 | COROLLARY HEX3.C | 158–166 | `9b3f15cf` | — |

### GENIND_PROOF_2026-08-08.md — commit `5e33b01f`, grade: ACCEPTED 2/2, 8 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENIND.A | 127–178 | `52f2b4a4` | — |
| 2 | THEOREM GENIND.B | 186–224 | `02dc45ce` | — |
| 3 | LEMMA GENIND-1 | 231–243 | `6d20c11a` | — |
| 4 | LEMMA GENIND-2 | 290–306 | `792e554d` | — |
| 5 | LEMMA GENIND-3 | 346–378 | `49982180` | — |
| 6 | LEMMA GENIND-0 | 525–534 | `5232e76c` | — |
| 7 | LEMMA GENIND-6 | 604–660 | `dd96cd1b` | — |
| 8 | LEMMA GENIND-4 | 1213–1233 | `afa8214b` | — |

### GENH4_PROOF_2026-08-08.md — commit `65681144`, grade: ACCEPTED 2/2, 10 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENH4.A | 86–116 | `1b90bda3` | — |
| 2 | LEMMA GENH4-4 | 138–147 | `5b8d5ba8` | — |
| 3 | THEOREM GENH4.B | 149–169 | `d5545164` | — |
| 4 | THEOREM GENH4.C | 171–181 | `4ed66333` | — |
| 5 | COROLLARY GENH4.D | 183–199 | `c244247c` | — |
| 6 | LEMMA GENH4-1F | 240–251 | `d5605398` | — |
| 7 | LEMMA GENH4-CAP | 294–333 | `8fcbb9de` | — |
| 8 | LEMMA GENH4-2 | 337–354 | `50d638e9` | — |
| 9 | LEMMA GENH4-3 | 376–403 | `6067ad94` | — |
| 10 | LEMMA GENH4-6 | 607–617 | `b1c4f078` | — |

### GENHN_PROOF_2026-08-08.md — commit `06958241`, grade: ACCEPTED 2/2, 12 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENHN.CLASS | 127–154 | `1b6bdada` | — |
| 2 | THEOREM GENHN.A | 156–211 | `eb606039` | — |
| 3 | THEOREM GENHN.C | 259–273 | `c8c98e43` | — |
| 4 | LEMMA GENHN-T | 275–301 | `d81fbc66` | — |
| 5 | THEOREM GENHN.B | 303–373 | `4ef55318` | — |
| 6 | LEMMA GENHN-1 | 531–548 | `1b516265` | — |
| 7 | LEMMA GENHN-2 | 699–717 | `73a1d718` | — |
| 8 | LEMMA GENHN-3 | 741–763 | `1d6aa5f6` | — |
| 9 | LEMMA GENHN-T #2 | 1127–1210 | `c932ac30` | — |
| 10 | LEMMA GENHN-CAP-GEN | 2061–2087 | `cece40d7` | — |
| 11 | LEMMA GENHN-LIFT | 2103–2189 | `3b70a20f` | — |
| 12 | LEMMA GENHN-COUNT-RERUN | 2352–2426 | `a95e85a8` | — |

### HE3_PROOF_2026-08-08.md — commit `62400944`, grade: ACCEPTED 2/2, 16 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | DEFINITION 1 | 242–251 | `14e5992f` | — |
| 2 | DEFINITION 2 | 288–310 | `2d144eb4` | — |
| 3 | THEOREM HE3.A | 312–331 | `ef48e8d3` | — |
| 4 | COROLLARY HE3.B | 333–367 | `6c44365c` | — |
| 5 | COROLLARY HE3.C | 369–378 | `b5efc2d1` | — |
| 6 | LEMMA HE3-1 | 450–478 | `022b3a55` | S |
| 7 | LEMMA HE3-1L | 498–514 | `d910b382` | — |
| 8 | LEMMA HE3-1′ | 548–559 | `93410450` | S |
| 9 | LEMMA HE3-0 | 648–671 | `db0aeb83` | — |
| 10 | COROLLARY HE3-0′ | 684–687 | `8dcbef7f` | — |
| 11 | LEMMA HE3-2 | 702–747 | `2bba660b` | S |
| 12 | COROLLARY HE3-2′ | 811–815 | `eeafb977` | — |
| 13 | LEMMA HE3-3 | 830–833 | `bf91e937` | — |
| 14 | LEMMA HE3-4 | 983–989 | `8e344d4f` | — |
| 15 | LEMMA HE3-6 | 1118–1121 | `531b7d3b` | — |
| 16 | LEMMA HE3-5 | 1238–1258 | `b8d77bc3` | — |

### HE6_PROOF_2026-08-08.md — commit `a5d8eb01`, grade: ACCEPTED 2/2, 13 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA HE6-1L | 130–199 | `0d03d1da` | — |
| 2 | DEFINITION HE6-1 | 201–213 | `187ff3a9` | — |
| 3 | LEMMA HE6-0″ | 215–238 | `376a2177` | — |
| 4 | LEMMA HE6-0 | 240–242 | `01ae336b` | — |
| 5 | LEMMA HE6-0′ | 244–248 | `887f79b7` | — |
| 6 | LEMMA HE6-1 | 250–253 | `85d23d67` | — |
| 7 | LEMMA HE6-2 | 255–264 | `b2ee5808` | — |
| 8 | LEMMA HE6-2′ | 266–269 | `779f1a73` | — |
| 9 | LEMMA HE6-3 | 271–278 | `c6644fa6` | — |
| 10 | LEMMA HE6-4 | 280–282 | `7dcc0367` | — |
| 11 | LEMMA HE6-5 | 284–287 | `5e137498` | — |
| 12 | THEOREM HE6.A | 289–301 | `e31bea9d` | — |
| 13 | COROLLARY HE6.B | 311–331 | `9cb6d5da` | — |

### HE7_PROOF_2026-08-08.md — commit `fe589460`, grade: ACCEPTED 2/2, 24 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | DEFINITION HE7-1 | 93–109 | `8c7fa1b9` | — |
| 2 | THEOREM HE7.A | 197–251 | `0a90b21f` | — |
| 3 | THEOREM HE7.C | 253–277 | `821982b0` | — |
| 4 | COROLLARY HE7.B | 279–293 | `a4f763be` | — |
| 5 | LEMMA HE6R1-2 | 294–305 | `94c22908` | — |
| 6 | THEOREM HE7.D | 307–314 | `79ed380f` | — |
| 7 | LEMMA HE7-L1 | 379–402 | `e3efbb57` | — |
| 8 | DEFINITION HE7-3 | 519–535 | `1a71e1c8` | — |
| 9 | LEMMA HE7-4 | 539–542 | `d29eed83` | — |
| 10 | LEMMA HE7-5 | 552–554 | `261ee4fb` | — |
| 11 | LEMMA HE7-7 | 567–569 | `cb7abb1e` | — |
| 12 | LEMMA HE7-7′ | 659–664 | `69027ae6` | — |
| 13 | COROLLARY HE7-7″ | 673–683 | `d3d888bd` | — |
| 14 | LEMMA HE7-6 | 688–689 | `881d4167` | — |
| 15 | LEMMA HE7-9 | 736–739 | `6b592d5e` | — |
| 16 | LEMMA HE7-10 | 740–741 | `8a86d600` | — |
| 17 | LEMMA HE7-11 | 776–777 | `dba01731` | — |
| 18 | LEMMA HE7-12 | 812–857 | `60bd963c` | — |
| 19 | LEMMA HE7-13 | 918–934 | `0caa3639` | — |
| 20 | DEFINITION HE7-2 | 976–992 | `16f71144` | — |
| 21 | THEOREM HE7.D #2 | 994–1002 | `1e0199f3` | — |
| 22 | LEMMA HE7-8 | 1087–1115 | `36fc0fc6` | — |
| 23 | THEOREM HE7.A′ | 1224–1231 | `c934a492` | — |
| 24 | LEMMA HE6R1-2 #2 | 1337–1346 | `53daa436` | — |

### HE6R1_RECON_2026-08-08.md — commit `d810e100`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | COROLLARY HE6.B | 90–98 | `54da07e3` | — |
| 2 | LEMMA HE6R1-1 | 270–282 | `1c64ae1c` | — |
| 3 | LEMMA HE6R1-2 | 316–347 | `58329fbc` | — |
| 4 | LEMMA HE6R1-3 | 469–477 | `593ab005` | — |

### HETOW_RECON_2026-08-09.md — commit `7fb88236`, grade: ACCEPTED 2/2, 5 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA HETOW-1 | 152–169 | `a3424ec7` | — |
| 2 | LEMMA HETOW-2 | 198–211 | `1bffd7bf` | — |
| 3 | LEMMA HETOW-3 | 264–270 | `b245e335` | — |
| 4 | THEOREM HETOW.A | 286–327 | `6b4a7dc4` | — |
| 5 | LEMMA HETOW-4 | 689–746 | `2500c2f4` | — |

### GENTOW1_PROOF_2026-08-09.md — commit `4caf0fb8`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA GENTOW-1 | 150–172 | `4b4d9f21` | — |
| 2 | COROLLARY GENTOW-1.1 | 273–277 | `84643df8` | — |
| 3 | LEMMA GENTOW-2 | 319–345 | `cd64f476` | — |
| 4 | LEMMA GENTOW-5 | 411–452 | `75f4b14f` | — |

### GENTOW2_PROOF_2026-08-09.md — commit `33f86204`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENTOW2-A | 187–219 | `5d1ae5f0` | — |
| 2 | LEMMA GENTOW2-B | 303–340 | `8a00bf44` | — |
| 3 | LEMMA GENTOW2-B′ | 518–538 | `bae471b0` | — |
| 4 | LEMMA GENTOW2-B″ | 729–738 | `d4c8b885` | — |

### GENTOW3_PROOF_2026-08-09.md — commit `3ee83992`, grade: ACCEPTED 2/2, 2 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENTOW-3 | 186–216 | `a6d97dfe` | — |
| 2 | COROLLARY GENTOW-3.C | 320–338 | `f2459aa5` | — |

### GENTOW4_PROOF_2026-08-09.md — commit `73b93fd0`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA GENTOW-4.1 | 170–195 | `d7d1bf2b` | — |
| 2 | THEOREM GENTOW-4.A | 253–324 | `f77a8145` | — |
| 3 | LEMMA GENTOW-4.2 | 378–383 | `73f54036` | — |
| 4 | COROLLARY GENTOW-4.C | 406–416 | `0096e69a` | — |

### GENTOW5_PROOF_2026-08-09.md — commit `cb010522`, grade: ACCEPTED 2/2, 2 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | DEFINITION (unlabeled) | 191–207 | `c9a95972` | U |
| 2 | LEMMA GENTOW5-A1 | 209–223 | `9d473730` | — |

### GENTOW6_PROOF_2026-08-09.md — commit `3d7fc37b`, grade: ACCEPTED 2/2, 6 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA GENTOW-6.1 | 95–109 | `cb50ffdc` | — |
| 2 | COROLLARY GENTOW-6.1C | 210–236 | `1a047b21` | — |
| 3 | LEMMA GENTOW-6.2 | 249–259 | `e1eb6807` | — |
| 4 | COROLLARY GENTOW-6.2C | 270–293 | `1ebcf7f0` | — |
| 5 | THEOREM GENTOW-6.3 | 378–434 | `05fc3881` | — |
| 6 | LEMMA GENTOW-6.4 | 879–950 | `832e21a2` | — |

## S2. Extraction rule (S0-v1, verbatim from the instrument)

Capture starts at column 0 only, three forms: (A) `**KW ...` and
`> **KW ...`; (B) `> * **KW ...` (quote-bullet; sole corpus instance
THEOREM W-12.C); (C) `**(i) [KW ...` / `> **(i) [KW ...` (W12 verdict
items). KW in {THEOREM, LEMMA, COROLLARY, COR, PROPOSITION, PROP,
DEFINITION, DEF}. Span ends at the FIRST of: next statement start; a
line opening `*Proof`/`**Proof` (optionally quoted); [plain] a heading
or `---` rule; [quoted] end of the `>` block, a `> **(ii) ` roman item
marker, or `> **GRADE`; 120-line cap (cut to last blank line, flag T).
Labels: keyword + first token after it (trailing punctuation stripped);
unlabeled and duplicate labels numbered in document order.

## S3. Ambiguity & skip record (honest; enumerative, no universal claims)

1. **Over-capture is possible and accepted.** Spans may include
   trailing non-statement prose (inline `*Proof.*` inside a statement's
   own paragraph, notation brackets, correction brackets) up to the next
   terminator — e.g. LIFTCORNER's unlabeled THEOREM span carries its
   inline proof and the [r4, F4-5] notation bracket. Conservative for a
   tripwire: edits there also fire. Line ranges let a human adjudicate.
2. **Skipped class — plain-bullet keyword recaps** (consumption/
   hypothesis-set lists, not statement displays), enumerated:
   - GRTJB_PROOF_2026-08-08.md:506 `* **LEMMA JB-EPS — UNCONDITIONAL at every m ≥ 1** (row 19), and its`
   - W11_PROOF_2026-08-08.md:594 `* **THEOREM W-10(2,1,1)** — PROVED at the instance, two-commit seal`
   - W11_PROOF_2026-08-08.md:599 `* **LEMMA J-D0** — PROVED on its perimeter, seal 1642275/**9387eb1**;`
   - W12_PROOF_2026-08-08.md:1115 `* **THEOREM W-11(n = 2)** — the complete menu + exact drainage + the`
   - W12_PROOF_2026-08-08.md:1118 `* **THEOREM W-10(2,1,1)** — the digit-calculus template (S2.2 is its`
   - W12_PROOF_2026-08-08.md:1121 `* **LEMMA J-D0** — the shape-keying/count-gauge-blindness FRAME: what`
   - W12_PROOF_2026-08-08.md:1489 `* **THEOREM W-11(n = 2)** — PROVED at attempt grade (arc: seal 7020ceb`
   - W12_PROOF_2026-08-08.md:1496 `* **THEOREM W-10(2,1,1)** — PROVED, seal 2e6fdd8 / verdict 9506a55;`
   - W12_PROOF_2026-08-08.md:1499 `* **LEMMA J-D0** — PROVED on its perimeter, seal 1642275 / verdict`
   - HMENU3_PROOF_2026-08-08.md:682 `* **THEOREM W-12.D** @ w12 seal f669cb0 / verdict c16c717 /`
   - HMENU3_PROOF_2026-08-08.md:699 `* **THEOREM W-12.A (order-1 laws) + S2.4 depth-0 completeness +`
   - HMENU3_PROOF_2026-08-08.md:703 `* **THEOREM W-11(n = 2)** @ seal 7020ceb / verdict cb05127 / r2 HEAD`
   - HMENU3_PROOF_2026-08-08.md:717 `* **LEMMA J-D0** @ 1642275/9387eb1 — the gauge-blindness frame`
   - HEX3_PROOF_2026-08-08.md:710 `* **THEOREM W-11(n = 2)** @ seal 7020ceb / verdict cb05127 / r2 HEAD`
   - HEX3_PROOF_2026-08-08.md:720 `* **LEMMA J-D0** @ 1642275/9387eb1 — the gauge-blindness frame behind`
   - GENIND_PROOF_2026-08-08.md:1466 `* **THEOREM W-12.D + W-12.A + S2.4/S2.5 + W12-L0/L1** @ w12 seal`
   - GENIND_PROOF_2026-08-08.md:1483 `* **THEOREM W-11(n = 2)** @ seal 7020ceb / r2 31506b3 / PE3 CLEAN`
   - GENIND_PROOF_2026-08-08.md:1518 `* **LEMMA J-D0** @ 1642275/9387eb1 — the count-gauge-blindness frame`
3. **Skipped class — bold NAMED displays without a keyword opener**
   (outside S-0's THEOREM/LEMMA/COR/DEF scope by the blueprint's own
   definition): e.g. `> **W-12 (the general-n assembly).**`,
   `> **(J-D1) THE FAITHFULNESS HANDOFF.**`, GRTW2's `> **(CLAUSE 1..3)`
   blocks, SIGMALAW's `**(Σ-DEF)`/`**(U-REC)` definitional displays, and
   per-clause `**(a)**...` markers. Audit count of `**(`-opening bold
   lines not captured, per note (size of this residue class):
   LIFTCORNER 8, GRTW2 6, GRTJA 1, GRTJB 16, GRTJC 18, WELDMASTER 7, JD0 7, SIGMALAW 3, W12 2, GENIND 14, GENH4 1, HE3 1, HE7 19, HE6R1 5.
   These are pinned only when inside a captured span; a statement whose
   ONLY display is such a form has no ledger row.
4. **Headings are not rows.** Section headings that restate labels
   (`## S4. THEOREM GENTOW2-A ...`) are not captured; the bold block
   below them is.
5. **Baseline matching is by (note, label), not line numbers** — dated
   appends that shift line numbers do NOT fire the tripwire; only text
   changes inside a span do. If an append INSERTS a same-labeled
   statement before an existing one, deterministic numbering shifts and
   the tripwire fires — conservative, adjudicate by hand.
6. **Parenthetical name-parts are cut from labels** (the token stops at
   `(`): observed instances at baseline — `THEOREM W-11` (displayed as
   `W-11(n = 2)`), `LEMMA GENHN-T #2` (displayed `GENHN-T(b)′`, GENHN
   L1127), `LEMMA HE6R1-2 #2` (displayed `HE6R1-2(b)(c)`, HE7 L1337).
   The md5 pins the FULL display text either way.
7. **Quoted keyword-opening RECAPS are captured as rows** (conservative
   over-inclusion; they pin cross-note quotes, which S5.3's record rule
   wants stable anyway): observed at baseline — HE7 L294 (`> **LEMMA
   HE6R1-2** when the block is PROPER ...`, a recap of HE6R1's export)
   and HE7 L307 vs L994 (`THEOREM HE7.D` summary display + full
   statement => rows HE7.D and HE7.D #2, both pinned).

## S4. Teeth record (instrument validated before seal, 2026-08-10)

Three momentary working-tree mutations, each restored via git checkout
immediately after the check (notes verified unmodified afterward):

1. Single-token change inside THEOREM W-12.D's span (W12 L267,
   `REDUCTION` -> `REDUCTIONX`): CHANGED reported with diff, **exit 1**.
2. Whitespace-only rewrap inside the same span (W12 L268-269 spacing):
   **exit 0**, GREEN — the declared whitespace-collapse tolerance.
3. Label rename (JD0 L49, `LEMMA J-D0.` -> `LEMMA J-D0X.`): DELETED
   (LEMMA J-D0) + ADDED-as-info (LEMMA J-D0X), **exit 1** — deletions
   fire, additions alone do not.

Verdict-of-record runs are appended below (S5) after the seal commit;
a --force rebuild regenerates S1-S4 only, so S5 appends must be
re-attached if the ledger is ever legitimately re-pinned.

