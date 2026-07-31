# O9 Phase-B rev 5 — hostile verification PASS 5, CONFIRMING (fresh context, 2026-07-31)

**Charge.** Confirming pass on `O9_phaseB_verifybrief_rev5.md` (rev 5 present;
verified rev 5, not rev 4). Pass 4 (`O9_pass4_verify.md`) was **SOUND — 0
critical, 1 justification gap** (Finding 1: the rev-4-withdrawn "per-slot
bijection of F_{r+1}" (GR-B) gloss surviving verbatim at two non-load-bearing
summary sites — the §0 OL-A(iii) row and §1's (P5) pin). Rev 5 claims a
two-site fix and byte-stability elsewhere. Verify the two fixed sites at
confirming depth + the standard census-layer audit. Quote-and-classify; fix
nothing.

**Method.** Full `diff` rev 4 → rev 5 (46 changed lines) audited hunk by hunk
against the rev-5 header's own delta claim; both fixed sites re-read in full
context and checked line-by-line against §5.1 (the section whose content they
must now summarize) and against pass 4's Finding-1 quotes of the offending
rev-4 text; fresh grep for every surviving "biject"/"surjectiv" token with
per-site classification; **re-execution** of the K7 script
(`o9_rev4_fulladm_check.py`) with byte-diff against the committed log;
spot re-confirmation of every pass-4 headline number in the K7 log; carried
K6/K5/K1–K4 log checks; §6.4 source-cite re-check.

**VERDICT: CLEAN — 0 critical errors, 0 justification gaps.**

Pass 4's single gap is repaired at both sites, faithfully to §5.1; nothing
else moved. Two remark-level observations recorded below (§3), neither a
finding.

---

## 1. The two fixed sites — VERIFIED at confirming depth

### 1.1 The §0 OL-A(iii) row (rev-5 line 89)

New statement cell:

> "weight-β initial forms of deg < m elements live on the line ϕ_β·F_{q^d}
> (the LINE clause — all §5.1 consumes of (GR-B) here); the graded digit
> read embeds G_β ↪ F_{q^d}, onto ⟺ FULL attainment dim G_β = d — a proved
> LED(ii)/(iii) lattice fact, not a (GR-B) clause (§5.1; the unqualified
> 'per-slot F_{q^d}-bijections' gloss was withdrawn in rev 4, this row
> synced in rev 5)"

Checked clause-by-clause against §5.1 (rev-5 lines 562–612, verbatim rev 4,
which pass 4 re-derived by hand):

* "live on the line ϕ_β·F_{q^d}" = §5.1's LINE clause (in(a) = ϕ_{w(a)}·c(a),
  c(a) ∈ F_{r+1}^×; F_{r+1} ≅ F_{q^d} by §1's d := [F_{r+1} : F_q]). ✓
* "all §5.1 consumes of (GR-B) here" — matches §5.1's header tag
  "[(GR-B) line clause + LED]" and pass 4's exactness audit (§2.1 there:
  §5.1's chain uses the line clause, LED(ii)/(iii), and dim G_{β_k} = d,
  nothing else of (GR-B)). ✓
* "embeds G_β ↪ F_{q^d}" = §5.1's injectivity bullet (r_β factors through
  G_β and the line clause embeds it: G_β ↪ ϕ_β·F_{r+1} ≅ F_{r+1}). ✓
* "onto ⟺ FULL attainment dim G_β = d — a proved LED(ii)/(iii) lattice
  fact, not a (GR-B) clause" = §5.1's fourth bullet verbatim in content
  ("Onto F_{r+1} ⟺ FULL attainment (a LATTICE fact, not a (GR-B) clause):
  V_β = F_{r+1} ⟺ dim G_β = d"). The LED grounding is honest: given the
  embedding, dim V_β = dim G_β = s(β+1) − s(β) is LED(iii), and the
  fiber/kernel consistency (z = 0 fiber q^{mN−s(β)−dim V_β} =
  q^{mN−s(β+1)} = #{w > β}) is LED(ii) — re-checked by hand here. The
  conditional structure is readable: the LINE clause is named FIRST as the
  (GR-B) consumption, and the row's status cell retains "orders ≥ 2 =
  (GR-B) [OPEN there]" unchanged. ✓
* Pass 4's refutability complaint is dissolved: the new cell asserts
  onto-ness ONLY at fully attained β, which is exactly what LED(ii)/(iii)
  permit — no reading of the row now contradicts the proved lattice counts
  at a partially attained slot. ✓

### 1.2 The §1 (P5) pin (rev-5 lines 151–155)

New parenthetical:

> "(corroboration, at FULLY attained β only, for §5.1's onto-F_{r+1} law —
> no surjectivity clause of (GR-B) is consumed, that gloss being withdrawn
> in rev 4; not load-bearing — see §5.1)"

Matches §5.1's own re-scope sentence exactly ("The pinned (P5) (GMN Prop
2.10) corroboration is re-scoped accordingly: it is cited only at fully
attained β, and was never load-bearing"). The positive attribution
"corroboration for (GR-B)'s surjectivity clause" that pass 4 flagged is
gone; the phrase "surjectivity clause" survives only inside an explicit
negation ("no surjectivity clause of (GR-B) is consumed"), i.e. as
disclosure, not consumption. The §1 byte-stability bracket is honestly
updated ("verbatim, except the (P5) parenthetical — re-scoped in rev 5").

### 1.3 Residual-gloss grep — CLEAN

Fresh grep of rev 5 for "biject"/"surjectiv": every hit is (a) the
§0-pre/header delta narrative and the §0 F1 falsifier row (historical
quotes of the withdrawn gloss, describing the pass-3/pass-4 findings and
repairs), (b) §5.1's withdrawal notice itself, (c) §11's attack-list items
4 (which ASKS the grep question), (d) the two fixed sites' own withdrawal
disclosures, or (e) line 470's unrelated euclidean-division coordinate
bijection f ↔ (a₀, …, a_ℓ) in §4. No unqualified survival anywhere; §§6–8
consume "§5.1 fiber uniformity + FULL attainment" only, as in pass 4.

---

## 2. Census-layer audit — CLEAN

* **K7 re-executed** (`python3 o9_rev4_fulladm_check.py`, exit 0):
  reproduces `logs/o9_rev4_fulladm_20260731_202140.log` **byte-identically**
  (RESULT: ALL PASS). Headline numbers re-confirmed in the log verbatim:
  D1 display 73728 vs truth 49152 at p = 2 (ratio (q+1)/q), 102036672 vs
  76527504 at p = 3; D2 positive control 147456 / 306110016 = q¹⁴(q²−1)²
  with (ADM)FULL = True; CH4's 0/0, 16/16, 0/0, 324/324 under the f₁ = 1
  FULL ⟺ VALUE collapse; CH5's seven (e₁,h₁,f₁,f₀) tuples all PASS
  ("FULL ineq ⟺ count==d; VALUE ineq regression; (CLASS-d); f₁=1
  collapse"); CH5b thresholds FULL 2 > 1 = β₁ ≥ 0 = VALUE. ✓
* **Carried logs unchanged:** K6 (`o9_rev3_adm_20260731_194858.log`) —
  mod-e display 256 / 26244 REFUTED vs truth 0, positive controls
  census = display at 16 and 324 (naive 2¹⁸-pair loop agreeing), RESULT:
  ALL PASS ✓; K1–K4 (`o9_census_20260731_165908.log`) — "K4: cross-p
  cells=18 (singles skipped=5) violations=0 / OVERALL: GATE SURVIVES (0
  violations)" ✓; K5 (`o9_rev2_ledger_predict_20260731_175221.log`) —
  RESULT: ALL PASS with the rev-0 formula REFUTED at the integral
  left-tail cases (e.g. p3-LT: truth 108 = new formula, rev-0 324) ✓.
* **§6.4 source cite:** `o9_order2_census_check.py` lines 121–124 are the
  v(a₀) ≥ M parent drop (`vs = [...]; if vs[0] >= M: return None`), as
  cited. ✓
* **Byte-stability manifest:** the full rev 4 → rev 5 diff is exactly
  seven hunks — the title line; the header's rev-5 self-description; the
  §0-pre rev-5 delta paragraph; the §0 OL-A(iii) row (fix site 1); the §1
  byte-stability bracket; the §1 (P5) parenthetical (fix site 2); and the
  sign-off trailer's first two lines (rev label only, the verdict text
  itself unchanged). §§2–11 (rev-5 lines 171–1103) are verbatim rev 4 —
  the claim "every other byte, §§2–11 included, is verbatim rev 4" holds
  for all mathematical content, with the extra changed bytes being the
  delta's own self-description (see remark R1). ✓
* **Pass-4 characterization:** the rev-5 header and §0-pre quote pass 4's
  verdict (SOUND — 0 critical, 1 gap), its Finding-1 sites, its
  REFUTABLE-as-stated observation, and its grep audit accurately against
  `O9_pass4_verify.md`. The rev-4 text pass 4 quoted is confirmed as what
  the diff removed. ✓

---

## 3. Remarks (verified non-findings, recorded for the file)

* **R1.** The header sentence "Rev 5 touches ONLY the §0 OL-A(iii) row and
  the §1 (P5) parenthetical" is accurate for content sites; strictly, the
  header block, the §0-pre delta paragraph, the §1 bracket annotation, and
  the trailer's rev label also differ from rev 4 — all four being the
  delta's self-description, disclosed in place. No mathematical byte
  outside the two sites changed. Not a finding.
* **R2.** The §0-pre delta says the (P5) fix has "the withdrawn
  surjectivity clause's name removed"; the phrase "surjectivity clause"
  in fact survives in (P5) inside an explicit negation ("no surjectivity
  clause of (GR-B) is consumed"). The ATTRIBUTION is removed, which is
  what the repair required; the surviving mention is disclosure. Not a
  finding.

---

## 4. Verdict

**CLEAN — 0 critical errors, 0 justification gaps.** Pass 4's single gap
(the two unconsumed gloss survivals) is repaired at both sites, each fix
faithful to §5.1's verified content, with the conditionality on (GR-B)'s
line clause preserved in the §0 status cell; everything else is byte-stable
rev 4, whose mathematics pass 4 verified in full; the census layer
re-executes byte-identically. Confirming-pass ledger for this brief:
pass 4 SOUND (1 gap) → pass 5 CLEAN. The honest headline — the order-r
census REDUCED to (GR-B) + (FRESH) under the per-datum decidable
FULL-attainment (ADM), with the disclosed VALUE-gate coverage limits —
stands as displayed.

— Pass-5 hostile verifier (fresh context, confirming pass), 2026-07-31.
