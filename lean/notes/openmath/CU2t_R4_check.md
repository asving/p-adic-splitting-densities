# CU-2t R4 spot-check (unit CU2tc, 2026-07-31; fresh context)

**Object checked:** `lean/notes/openmath/CU_cluster_phaseB.md`, the CU-2t
sections (§9–§11 plus the new §12 R4 record), at R4 = commit b9f05db
(working tree clean on the file). **Charge (per the CU2tp disposition
recommendation, `CU2t_R3_verify.md` §4):** NOT a full pass — the prior pass
already VERIFIED both R3 logic repairs; verify only the three R4-fixed sites
(G-α, G-β, M-γ) and that no proof body changed. **Method:** full diff
81589e9 (R3) → b9f05db (R4) mapped hunk-by-hunk onto the section
boundaries of both versions; the three repaired sites read in place; every
NEW factual claim the R4 text introduces checked against its source
(O-2a rev 5 verbatim; tree/ROOT files at HEAD; git history of the ROOT).

## VERDICT: PASS — R4 ACCEPTED. 3/3 repairs verified in place; no proof body, statement, or tie logic changed; 0 findings.

---

## 1. No proof body changed — VERIFIED by hunk map

The R3→R4 diff touches exactly (old-file line ranges → section):

| hunk | site | content class |
|---|---|---|
| 1, 19 | header + new R4 parenthetical | record |
| 598–608 | §9.1 carrier note | M-γ display |
| 899–907 | §9.4 (T-READ) row label sentence | G-α label |
| 926–945 | §9.4 pricing note | G-α re-grade |
| 952–959 | §9.5 conditionality line | G-α sync |
| 962–988 | §9.5 pricing correction + fold-state note + touches (1)–(4) | G-α/G-β |
| 1037–1051 | §9.7 item-(5) bracket + grade line | record |
| 1162–1165 | §11 files paragraph (flagged annotation) + appended §12 | record |

NO hunk intersects: §9.0, §9.2 (old 611–638), §9.2a incl. Definition RC +
the (c1) display (639–694), the ENTIRE §9.3 Lemma + proof block + Corollary
(695–862), the §9.4 four-row display's (T-PREFIX)/(T-DEC)/(T-VERD) rows and
the "Given the rows" per-half tie-consumption paragraph (old 908–925,
between hunks — byte-stable), §9.6 (1013–1030), §§0–8, §10 (1061–1103), or
the §11 table. Inside the (T-READ) row, only the grade label changed
("Engine READ bookkeeping:" → "Read-semantics CONFORMANCE — re-graded at R4
(…):"); the row's factual content ("the terminal record's shape fields are
written FROM the level-(k'+1) polygon read … No other row can supply
this…") is byte-identical. §12's byte-stability declaration matches this map
exactly, including its one declared exception (the §11 annotation).

## 2. G-α (the (T-READ) re-grade) — VERIFIED

The repair executes the verifier's prescribed disposition (re-grade as the
scope note's second semantic clause) AND its alternative (the displayed
per-case decomposition) — strictly more than either option alone. Checked:

* §9.4 pricing note now grades (T-READ) in the OL-2-min/OL-5 conformance
  family (GD-2/GD-5), keeps (T-DEC-dec)/(T-DEC-cor)/(T-VERD) +
  (T-READ)'s terminal-binding half at GD-4, displays the k' ≥ 1 / k' = 0
  decomposition, keeps the THREE-row count, and restates "no new open
  FAMILY" in the corrected sense — all exactly per `CU2t_R3_verify.md` G-α.
* Source quotes verified verbatim against `O2a_phaseB_verifybrief_rev5.md`:
  OL-2-min's premise "suppose the engine's stage read at level i + 1 on f
  over c emits the record (e, h, ℓ, s, u, …)" — unrestricted (contrast
  OL-3-min's "emits a continuing record"); OL-5's premise "emits the
  continuing record ν₁" + its scope note "Histories whose first node is
  terminal need no level-1 clause"; OL-6's "Terminal records need no
  binding clause". The "second semantic clause after K-OB-E" claim matches
  the GD-4 charter's "K-OB-E … the one semantic clause" (ROOT §3.3 row).
* Syncs present and consistent: §9.5 conditionality line, family-homes
  sentence, touches (1)/(2)/(4), touch (3)'s grading-sync line, §9.7
  item-(5) bracket (accurate: CU2tp item (5) = "PARTIAL, see G-α"), both
  grade lines (§9.7, §12).

## 3. G-β (the fold-state rewrite) — VERIFIED against the live repo

Every factual claim of the rewritten note checked:

* Tree §D3.5 at HEAD still carries "zero new open inputs; the two
  engine-bookkeeping terminal rows (T-DEC)/(T-VERD)…" (the rev-1
  zero-count sentence) — so touch (1) = rewrite, correct. ✓
* Tree §D2.3's CU-2t bullet at HEAD reads "Status: OPEN (one lemma) over
  the GD residue" — NO row count, so touch (2) = FIRST execution. ✓
* DELTA 4 (unit TREE-GAPS, 46e583e) recorded the R3 event post-audit
  (tree line ~1543) while both sites above kept pre-R2 wording. ✓
* ROOT two-row fold: ea0336f = "ROOT ASSEMBLY REVISION 3 (unit ROOT r4)",
  Step 11 "including the two NEW GD-4 terminal rows (T-DEC)/(T-VERD)",
  recorded there as a wave-14 fold — and R2's §10 F4 owed list indeed
  names no ROOT touch. ✓
* ROOT three-row fold: 5c7abd9 = "ROOT ASSEMBLY REVISION 4 (unit ROOT
  r5)"; ROOT at HEAD, Step 11: "including the THREE NEW GD-4 terminal rows
  (T-DEC)/(T-READ)/(T-VERD)". ✓
* The owed §3.3 grading sync is real: ROOT §3.3 GD-4/GD-6 row at HEAD
  still words (T-READ) among "THREE genuinely NEW unproved mandatory-path
  GD-4 obligations" — pre-R4-grade wording, exactly what touch (3) says
  remains. ✓
* The §11 annotation is present, flagged, and correct (the §11 files
  paragraph's closing parenthetical does repeat the R3 error; the table is
  left byte-stable per the §10/M6 precedent).

## 4. M-γ (the §9.1 a₀ ≥ 2 display) — VERIFIED

W3 quoted correctly ("a₀ ≥ 2 if k ≥ 1" — verbatim at O-2a rev 5 (C1),
line 235); the clause does fire on appending ν to a k' = 0 track (k
becomes 1); the interior-μ clause is vacuous there, so "𝔈-legal in the
(τ-hen) case ONLY at a₀ ≥ 2" is exactly right; the a₀ = 1 sub-case now
matches §9.2's "at a₀ = 1 the seam object is (ρ₀) plus the machine record"
word-for-word in content. §9.1 and §9.2 agree read-alone, as §12 claims.

## 5. Residual observations (NO findings; nothing owed by this unit)

1. **Label collision, reading note only.** §9.5/§12 use "r4" for the ROOT's
   two-row state and "ROOT REVISION 4" for the three-row state. Both are
   correct under the ecosystem's convention (unit ROOT r4 = in-file
   REVISION 3; unit ROOT r5 = REVISION 4) and match the CU2tp brief's own
   usage, but a cold reader could equate "r4" with "REVISION 4". The
   parentheticals disambiguate by content; no edit demanded.
2. **Inherited, for the conformance-family owner (not an R4 defect):** the
   k' ≥ 1 decomposition sentence — transcribed verbatim from CU2tp G-α —
   calls (T-READ)'s mathematical half "an OL-2-min INSTANCE"; OL-2-min's
   conclusion is stated for sides of FINITE slope −h/e, while DEC(τ-irr)'s
   j₀ = 1 sub-case reads a slope-−∞ side (handled in §9.2a via the §9.2
   convention, verified at CU2tp item (11)). The instance claim is exact on
   the finite-slope sub-case; the −∞ sub-case's conformance leg may need
   its own line when the conformance-family owner absorbs the row. Rides
   the already-owed touch (4)/O-3-family routing; no new obligation.

## 6. Disposition

R4 is ACCEPTED as the unit of record. Per the CU2tp recommendation adopted
at §12, no further pass is owed on CU-2t; the grade stands at
PROVED-UNVERIFIED (R4), conditional per §9.5 as corrected (P(O-2a r5) ·
TB-CAP/D-12r · GD residue + the three terminal rows at their R4 grades).
Still owed elsewhere, unchanged: tree touches (1)–(2), the ROOT §3.3
grading sync, the GD-4 owner-brief absorption (4), the O-2a delivery (5).

*Checker: unit CU2tc (fresh context, spot-check charge). Nothing in the
target file or any source was edited by this pass.*
