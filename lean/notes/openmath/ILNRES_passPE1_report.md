# ILNRES-PE1 — first hostile pass on ILNRES_2026-08-08.md

**Target:** `lean/notes/openmath/ILNRES_2026-08-08.md` at d05dd02 (confirmed in
`git log`; file byte-identical d05dd02 → HEAD 77c767e). Seal chain verified:
a79f0fe (commit 1: S1–S3+S5 + runner, battery NOT run, "PENDING" placeholders)
→ 7c6f060 (commit 2: verdict + artifacts; only the PENDING placeholders
replaced, nothing sealed deleted) → d05dd02 (S6 composed post-battery; note
file only). Runner `ilnres_checks.py` byte-stable across all three. No
accepted text edited by the unit (commit stats verified).

**Role:** verify only, fix nothing. New artifact (verification only, mine):
`verification/openmath/ilnres_pe1_ext.py`.

---

## 1. Charge (1): completeness of the S1 residual enumeration — FIFTH-RESIDUAL HUNT

Sources re-read in full: ITERLAWN_PROOF head declaration + ACCEPTED bracket
(lines 13–41), S0.3 status + clause table, S4.3–S4.7 incl. the PE-G1 erratum
and the refutation bracket, S7 + the r38 bracket + the dependency-sweep table
(23 rows + machine census bracket), S9 fences, S10 DAG; BRIDGE_ADJUDICATIONS
[ILN] block (line 8518) and [RMG] block + COR-A (line 9328); the [RMG]
honest-residuals paragraph.

**Candidates hunted and adjudicated (none is a missed fifth residual):**

- **(TAIL-STAB)** — listed in the [ILN] acceptance bracket as a separate item
  of "the campaign's remaining mathematical distance ON THE MODEL CLASS".
  Adjudication: it is the single open lemma of the LIFT-corner cure
  (`ITERLAWLIFT_CORNER_2026-08-08.md` Step 2, honesty box: "UNPROVED — the
  entire distance between this sketch and a proof note"). It is the missing
  tool INSIDE NR-1, not an independent conditionality of the accepted law;
  S5.1 threads it correctly. NOT a fifth residual.
- **(INV-n) class / GMN transport / gr(w) wrapper (S9 fence bullet).** The
  gr(w) wrapper = NR-2. GMN transport = an OM-semantic consumption, inside
  NR-2's stated consumer set ("every OM-semantic consumption (Q4)"). (INV-n)
  is an UNCLAIMED companion display (PROJECT_STATE: "confirmed instances
  exactly n = 1 … NOT asserted beyond") — a fence on a statement never made,
  not conditionality of (ITER-LAW-n). NOT residuals.
- **The fenced corners.** Verified perimeter fact (i)'s set algebra: the [RMG]
  fence d₀ ≥ 2 ∧ (e₀ = 1 ∨ ∃ interior flat) IS exactly ¬T-class(n) (index
  ranges match: T-scope(m) needs e_i ≥ 2 for i ≤ m−1, consumed for
  m ≤ n−1 → union over m = 1..n−2 = T-class(n)'s range); the [IL3] DEV-1
  corner {e₀ = 1 ∧ d₀ ≥ 2 ∧ j ≥ g₀} ⊆ that complement. Zero intersection
  with T-class(n). Correctly excluded.
- **RM-1's own fenced corner** (e₀ = 1 ∧ d₀ ≥ 2): off T-class; on T-class
  with d₀ = 1 ∧ e₀ = 1, RM-1's proved scope (e₀ ≥ 2, plus e₀ = 1 ∧ d₀ = 1)
  covers it. Not a residual on T-class.
- **The DITER §S2 E₂ > 1 coincidence restriction** ([IL] package scope
  sentence; d₀ = 1 T-class towers can have E₂ = 1): a scope statement about
  an external identification, not an open member of the package; the law
  itself is unconditional there. Interpretation-side questions are NR-2's
  genre. Not a residual (nearest miss; see finding F2).
- **S7 rows 1–4, 9–11:** unconditional / accepted-package-fed / measured
  evidence — all covered by perimeter facts (ii)–(iv), and the accepted
  packages' open members all map into NR-1/NR-2/NR-3/NR-4 (but see F2 on the
  parenthetical).
- **Top-level e_{n−1}, e_n unconstrained by T-class:** checked — the II-legs
  at rung n consume (RM-(n−1)), needing T-scope(n−1) = e_i ≥ 2 for
  i ≤ n−2 = exactly T-class(n). No hidden constraint escapes the list.

**Verdict on charge (1): the four-member list is COMPLETE relative to the
sources of record. No fifth residual found.**

## 2. Charge (2): (DS-SUB) — the rung induction re-derived; scope exact

- **Sub-package extraction (S3) faithful:** CII chain verbatim = [ILN] S4.3
  (P-DS) under the T-notation erratum; the kept/excluded partition (support +
  deg clauses + E₁⟹CII kept; E₀ ≠ 0, weights, certified read excluded) is
  coherent, and the S6 proof consumes no excluded clause (checked line by
  line; clause (ii)'s proof needs no E₀ ≠ 0 in any leg).
- **Base r = 1:** [IL L7] displays as pasted in [ILN] S4.3; support/E₁⟹CII₁
  read off; at e₀ = 1 the window forces s₁ = 0 (T₁ = 0), so the base is
  Case I there — no hidden corner. Consumes the ACCEPTED [IL] (honest: the
  census lists the accepted bases; "engine-free" ≠ assumption-free, and the
  note says so).
- **Step, case split (1):** S4.4's partition proof is genuinely "direct from
  the slot support" — predicates use only g, E₁ᴵᴴ, δ^pl, T (integer layer) +
  IH support; the S4.4 weight paragraph is a separate display consumed by the
  W-MULT legs only. Overflow at g ≥ 2 impossible: T_r+1 ≤ 2e−1 < eg. ✓
- **Step, construction (3):** hand-verified the identity
  E₀ᶜ + E₁ᶜΦ_r = Σ_{a<e}E_aΦ^a + E₁ᶜ(Φ_r − Ĉ) = BP_r (Ĉ = Φ_r − Φ^e);
  degree chain exact (deg E₁ᶜ ≤ (d−1)+(T_r+1−e)d < ed ⟸ T_r ≤ 2e−2; E₀ᶜ
  threat slots: only Q¹ at k+2 (II-2, fires only at T_r = 2e−2) resp. slot 1
  (II-3, fires only at e = 1) — exactly the DCX_r definition); the II-1/II-2/
  II-3 specializations match the S4.6 displays symbol for symbol (R⁰/Q⁰/R¹/Q¹
  = plain-division refinements). Uniqueness: division-algorithm development,
  Φ_r monic. ✓
- **Where engine-freeness enters (the charge's question):** two places, both
  verified: (a) the engine call sites in S4.6 exist ONLY to certify the
  weight/read clauses of the R/Q pieces — the clauses excluded from (P-DS⁻);
  (b) the DCX_r predicate's "engine Q-part" equals the PLAIN division
  quotient by monic-division uniqueness (deg fĈ ≤ 2d−2 forces the engine's
  (R,Q) split to coincide with divmod), so the off-DCX hypothesis is
  engine-independently meaningful. Consumption census confirmed EXACT:
  division algorithm (S0.2) + S4.1 WELL-DEF existence/degree
  (unconditional-generic per the accepted [ILN] structure; ledger row 11:
  S4.1 "DCX-independent and engine-free", m = 1 base on [IL3]†) + S2 integer
  layer + accepted [IL]/[IL3]† bases. No (RM-m), no weight, no read. ✓
- **Discharge scope (ON and OFF T-class) exact:** the S4.7 outer-bound proof's
  (P-DS) consumptions are precisely (a) support/digit-degrees + T_m ≤ 2e−2
  [clause (i) + integer layer], (b) E₁ᴵᴴ ≠ 0 ⟹ CII_{m−1} [clause (ii)],
  (c) CII_{m−1} ⟹ g_{m−2} = 1 [definitional conjunct of CII]. All ride
  (DS-SUB); given the lemma the outer bound + emptiness leg are
  unconditional-generic at every rung with no T-class hypothesis anywhere in
  the chain. The retirement claims are correctly scoped "AT THE GRADE OF THIS
  NOTE" (attempt, counter 0, arc owed, no upstream cites). ✓

## 3. Charge (3): NR-3 bites-on-T-class; priced specs

- **RM2 witness:** `RM2_PROBE_2026-08-08.md` roster: RM2A = d₀ 1, r0/r1/r2 =
  (2,1,1) — headline tuple (RM2A/Zp3, γ = γ′ = 51, all s-values 1, DCX₃-live,
  Q¹ ≠ 0, cross-ring confirmed). T-class(3) = d₀ = 1 ∨ (e₀ ≥ 2 ∧ e₁ ≥ 2):
  RM2A satisfies BOTH disjuncts. ILNRES S1's claim verified. (Also live at
  RM2C, d₀ = 2, e₀ = e₁ = 2 — T-class via the e-disjunct.)
- **X5 second family:** X5-TCTRL-d1 (d₀ = 1 → T-class by definition) shows
  dcx3 = 48 in the committed census; I re-derived the 48 count INDEPENDENTLY
  with fresh integer-polynomial arithmetic (see §4) — exact match. The S4
  note-of-record is correct.
- **Priced specs:** S5.1 (M; TAIL-STAB priced S/M at r39) ✓ matches
  PROJECT_STATE/ROOT; S5.2 (L) ✓ matches the Q4/GRT-2 pricing and "GRT-1
  rides P1" matches the wave-18 fold verbatim; S5.3 (= standing Q2 program) ✓.
  NR-3's instance figures cross-checked: 132/132 ([IL3] r38 block) ✓, T5B
  5-read ([ILN] S4.7) ✓. Honest.

## 4. Charge (4): machine leg

- **Reproduction:** `ilnres_checks.py` re-run read-only at HEAD: exit 0,
  stdout identical to committed `ilnres_checks_output.txt` modulo the elapsed
  figure; `ilnres_checks_results.json` byte-identical after re-run (md5
  c799769e… unchanged; pre-run md5s recorded: runner 14daf86d…, output
  71bc4f4d…). Counts reproduce exactly: DS-SUPP 3,650 · DS-E1 3,650 ·
  DS-CASE 2,386 · DS-CHAT 17 · OB-OUT 110 · DS-E0 3,650 (0 dev) · ENG-GATE 0.
  Count arithmetic independently confirmed: 1,264 pairs × 3 rungs − 142
  on-DCX skips = 3,650; DS-CHAT 17 = Σ per-tower defined Ĉ_m; OB-OUT
  110 = 101 flagged pairs + 9 double-flagged (X6) — all consistent.
- **Hand re-derivations (fresh arithmetic, `ilnres_pe1_ext.py`):** own
  integer-polynomial layer (no grb primitives), consuming only the committed
  Φ's + split data. THREE instances, all green (33 checks): (A) X3-FLAT-H2/Zp3
  rung 2, Case II via the e₁ = 1 leg — construction == dev, degrees, CII₂;
  (B1) X5 rung 3 off-DCX₃ with E₁ᴵᴴ ≠ 0 — construction == dev, E₁ ≠ 0 ⟹
  CII₃; (B2) X5 rung 3 DCX₃-flagged pair — E₁ᴵᴴ ≠ 0, Q¹ ≠ 0 by my own
  division, track-extreme, outer locus (OB-OUT by hand), on-DCX support
  still ⊆ {0,1}. Plus the full X5 window rescanned with fresh arithmetic:
  dcx3 = 48 reproduced exactly.

---

## FINDINGS

**F1 [GAP — verdict figure fails to reproduce from the artifacts].**
S4 bullet (and the commit-2 message, and the dispatch claims): "**Coverage
that carries the decorrelation weight: 1,344 pairs (of 1,656) on OFF-T-class
towers**". Neither number is derivable from the committed artifacts under any
reading I could construct. From `ilnres_checks_results.json` (re-verified by
re-run): total pairs = **1,264**, OFF-T-class tower (X1/X2/X3/X4) pairs =
**608** (48.1%); per-(pair,rung) sub-package checks = 3,650 total, **1,760**
(48.2%) on OFF-T-class towers; per-rung T-class(r) classification gives 832.
The claimed 81% off-T share overstates the actual ≈48% either way. The
substantive claims survive (all-green everywhere; roughly half the coverage
genuinely off-T, on shapes where (RM-m) is unproven; all four rings present —
verified), and the (DS-SUB) proof does not consume the count — but S4 declares
itself "appended in commit 2 from the artifacts" and this line is not, which
violates the corpus's as-of-machine-quotes discipline. Cure: erratum bracket
correcting to 608/1,264 pairs (or 1,760/3,650 checks); the parent claim
"incl. 1,344 off-T-class pairs" should be corrected wherever repeated.

**F2 [GAP — display-grade under-count in perimeter fact (ii)].**
S1 perimeter fact (ii): "the accepted packages [IL]†/[IL3]†/[RMG]† ride
through at accepted grade (their open members are already listed as
**NR-1/NR-3**)". Under-inclusive parenthetical: the [IL] package's gr(w₂)
wrapper clause maps to **NR-2**, and the [RMG] honest-residuals' "(H2)-class
discharge via (P-DS)" line maps to **NR-4** — both package-carried, both
listed in S1 but not named in this parenthetical. The enumeration itself is
unaffected (all members ARE on the list); the parenthetical alone
mis-describes the mapping. Cure: read "NR-1/NR-2/NR-3/NR-4" (or "the S1
list").

**Remark (no finding):** OB-OUT's non-trivial teeth reduce to the CII_{m−1}
leg — the flag's track-extreme conjunct (T_m = 2e−2, s ≤ e−1 each) already
FORCES s_m = s_m′ = e−1 by integer arithmetic, and g_{m−1} = 1 is shared, so
the family is a consistency mirror of the outer-bound derivation rather than
an independent test. The sealed sheet states it honestly; recorded here so
the family's evidentiary weight is not over-read later.

**Not findings (verified sound):** seal discipline (two-commit, placeholders
only); runner byte-stability; the S6 induction and its consumption census;
the discharge scope; the S3 sub-package extraction fidelity; the NR-3
witnesses; the priced specs; the DCX-flag semantics (plain-division Q¹ =
engine Q¹ by monic uniqueness); the honest-grade box.

---

ILNRES-PE1 FINDINGS: 0 critical, 2 gaps
VERDICT: GAPS-ONLY
