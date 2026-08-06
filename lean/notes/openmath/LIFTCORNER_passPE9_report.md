# LIFTCORNER passPE9 — hostile verification report (fresh context, post-r7; THE ACCEPTANCE PASS)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD** (5f56308;
note byte-identical to r7 = 4898d32, verified `git diff 4898d32 HEAD -- <note>`
= **0 bytes**), i.e. after repair rounds **r1** (b2dc120), **r2** (a3112dc +
e5b3faf), **r3** (feedaab), **r4** (6170b09 + 56997be), **r5** (46e6e88),
**r6** (91f0cde), **r7** (4898d32). The counter stands at **1/2** after PE8's
clean pass (report c6097d7); per the acceptance rule a clean pass here ACCEPTS
the note, any finding resets the count. The bar is the same as every pass.
**Arc read before the note:** all eight prior reports
(`LIFTCORNER_passPE1..PE8_report.md` at 30e570c / 3367f3c / 39ea0db / 8b53efa /
a5212e8 / f2b48e7 / 58f7060 / c6097d7).
**Charge:** (1) TWO proof components re-derived, decorrelated from the eight
reports' choices (complement nearly empty; overlap disclosed with the route
difference); (2) the full note top-to-bottom for statement-level truth at
HEAD; (3) the arc-accounting system; machine legs both mandatory; PE8's four
unnumbered observations adjudicated independently (their non-owed status was
PE8's judgment, not a fence). Quote-and-classify, fix nothing; honesty
defects graded; fences read as part of the statement.

**VERDICT: 0 CRITICAL ERRORS / 0 JUSTIFICATION GAPS — A CLEAN PASS, the
SECOND consecutive. Per the acceptance rule this pass ACCEPTS the note
(2/2); the ledger action recording the close is the orchestrator's, not this
report's.**

Both machine legs reproduce with the seal intact (§1). The full note re-read
top-to-bottom at HEAD: every checkable statement verified — census figures
independently re-executed at all three pinned commits AND at HEAD under
their stated units, all 17 cited source line numbers re-read at source, all
cross-note quotes verified verbatim, all committed-table claims reproduced
(§2). The arc-accounting system is consistent, and true at HEAD under the
protocol's own division of record (the note carries the r7-dated record; the
ledger carries PE8 — adjudicated NOT a defect, §3). My two decorrelated
components — the CONTENT sub-lemma by a route no pass has used (O-linearity
of monic division, charge item (3)), and READ-EQ's case-(b) skeleton by
general ledger arithmetic from the split identity (charge item (4)) — both
re-derive cleanly (§4, §5), and a FRESH-INSTANCE machine leg at p = 7
(outside the battery's p ∈ {2,3,5}, two fresh (e₀,h₀) configs) reproduces
(LEDGER) with 0 violations (§6). PE8's four observations: CONCUR on all four,
each independently re-grounded (§7). Two new unnumbered observations, neither
a defect (§7).

---

## 1. Machine legs (mandatory, two parts) — BOTH RUN, BOTH REPRODUCE

### (a) The SEALED runner — exit 0, seal intact, 0-byte diff, every counted figure matches

```
$ md5sum liftcorner_checks.py
ccb4351c92573f5f962cae4ae952d8dd          <- = the note's claim (header + S3)
$ git show dafc0b5:verification/openmath/liftcorner_checks.py | md5sum
ccb4351c92573f5f962cae4ae952d8dd          <- md5 at the seal == md5 at HEAD
$ git diff dafc0b5 HEAD -- verification/openmath/liftcorner_checks.py | wc -c
0                                         <- 0 bytes
$ python3 liftcorner_checks.py ; echo EXIT=$?
... TOTAL checks 25409  elapsed 4.3s ... VERDICT: ALL GREEN ... EXIT=0
```

Family table: GATE 0/56 · AV 0/656 · TLAW 0/4176 · PV 0/4176 · INT 0/4176 ·
LOC 0/0 · CHI 0/4176 · COV 0/0 · WRONGLET 0/3816 · TRS 0/4176 · ENGGATE 0/1 ·
CERT 0 (internal) · WRONGLET total fires **1,576** · gate-passed **56** ·
coverage min d1-pairs **6** · teeth min **6**. Sum 56 + 656 + 5·4176 + 3816 +
1 = **25,409** ✓. Diff vs the committed `liftcorner_checks_output.txt`:
**6 differing lines per side, all wall-clock stamp fields** (five per-block
`[  N.Ns]` stamps + `elapsed 4.3s` vs the artifact's `4.4s`); **empty under
timing normalisation** (unit + method stated per the note's standing rule;
jitter history PE4 4 / PE5 6 / PE6 7 / PE7 2 / PE8 5 / this pass 6 — counted
quantities identical in every recorded run).

### (b) The children generator — regenerates BYTE-IDENTICALLY; A7 all four legs PASS

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe9_children_regen.txt ; echo EXIT=$?
EXIT=0
$ diff /tmp/pe9_children_regen.txt liftcorner_tailstab_children_table.txt | wc -c
0        -> BYTE-IDENTICAL TO COMMITTED
```

Assertion failures 0; A1–A6 PASS; A7 PASS — 752 nodes / 5,336 children;
(i) sum-identity 0 mismatches; (ii) shape 0 violations; (iii) digit-wise
dev-linearity 0 mismatches; (iv) branching ≤ 2e₀+3 violations 0, observed max
{2:7, 3:9, 4:11, 5:13, 6:15} = 2e₀+3 at every e₀; "ANY CHILD DROPPING NEITHER
COORDINATE: NO"; "OVERALL: ALL GREEN". Matches the [r2, G3] block and the
[r4] machine-leg bracket exactly. Nothing in the repo was edited by this pass
except this report.

---

## 2. Charge (2): the full note top-to-bottom at HEAD — EVERY CHECKABLE STATEMENT TRUE

Read in full, lines 1–1428, fences and brackets as part of the statement.
Beyond the re-derivations of §§4–6, the statement-level checks and their
results:

* **The census, re-executed independently at every pinned commit AND at
  HEAD.** `grep`/`grep -o` of `c′` on the note: at **46e6e88 = 46
  occurrences / 42 lines**; at **91f0cde = 51 / 47**; at **HEAD = 54 / 50** —
  all three exactly as the note (r7 text) and PE8's O-d state. The double
  lines are the SAME four scalar-pair sentences at each commit (46e6e88:
  L301/527/892/930; 91f0cde: L328/554/919/959; HEAD: L363/589/954/1002 — the
  ξ-conjugate letters line, the Φ″ setting line, READ-EQ's b₀-difference
  line, COR 2's preamble), verified by per-line occurrence counting. My own
  one-by-one classification at HEAD: **33 residue-scalar + 4 covered-cocycle
  + 17 mention/quotation = 54**, the covered bucket EXACTLY the correction of
  record's four (S1 CANDIDATE display ×2 at L375/376, Q7 row L400, Q9 row
  L402) — **NO fourth bare-`c′`-as-cocycle site at HEAD**. (My split differs
  from PE7's transcribed 34+13 at the same single use/mention occurrence PE8's
  O-b names; totals and the load-bearing bucket agree under both conventions.)
* **All 17 cited source line numbers re-read at source, all accurate:**
  `liftcorner_checks.py` :35 (make_tower) / :36 (psi1 snapshot) / :52
  (assert (i)) / :144 (T0 same params) / :179 (assert (ii));
  `grb_order2_check.py` :333–334 (mk_field_ext, g = len(psi)−1) / :345
  (reduction loop `range(len(out)-1, g-1, -1)`, empty at g = 1) / :455 (eq12,
  `u*e + s*h = gamma, 0 <= s < e`) / :499–507 (standard lift) / :515 (the
  single `self.psi1` assignment, override-guarded) / :651 (build_Phi2 reads
  psi1); `iterlawlift_corner.py` :145–155 (apply_pert writes only
  Phi1/Phi2, per its docstring) / :224 (closed_form); `strata_probe.py` :389
  (K2 = mk_field_ext) / :400–401 (Gamma0) / :403 (split).
* **Cross-note quotes verified verbatim at source at HEAD:** ITERLAWN S0.1
  Lifts clause (its L163–164, "STANDARD LIFT of ψ₀ (grb_order2_check
  :499–507) … CANONICAL ε_m-CORRECTED LIFT"); ITERLAWN S0.3 L6 row with the
  "errata r4, 2026-08-03; PE4-F1" attribution bracket (its L278); ILNRES S5.1
  spec sentence (L180); ILNRES S7 "NO FIFTH RESIDUAL EXISTS" (L289); ILNRES
  S1's "at any level" clause (L28); wave-18 S0's Φ₁-only display (L36). The
  wave-18 S1 three-step lawful-class derivation re-read as the S1 frame's
  source of record — the note's S1 is its faithful ξ-conjugate transposition.
* **Committed-table claims:** §3 genre summary carries exactly NINE labels
  mapping onto the seven census rows as displayed; `b0-main-r` gain set
  exactly {0}; `mid[TOP=e0-1]-q` = 220 instances, ALL `degA-DROP`, all other
  labels all `m-DROP`; rows A12/B14 present in the roster as `pure` genre and
  ABSENT from the §4 m′ = m stratum (0 hits) — the (B)/[r2, G5] vacuous-rows
  claim ✓.
* **Provenance sites, re-read at their sources:** PE2's "bit-identically"
  unqualified at its L33/54/471 + qualified at L67 (L76/472 are generator
  sites, correctly not counted) ✓; PE2's 896 r/q pairs at its L277 ✓; PE4's
  header L11 "the S9 dependency-sweep table" (the F5-4 origin) ✓; PE6's L221
  "all 42 `c′` occurrences" (the F7-1 origin, unit word and figure) ✓; PE7's
  L194–198 "51 … four lines carry two … all scalar pairs … 34 = the residue
  scalar" (the warrant of record r7 transcribed, with unit and commit) ✓.
* **Ledger entries cited by the round blocks exist:**
  BRIDGE_ADJUDICATIONS_2026-07-30.md "PE1 VERDICTS" (L10467) and "LIFT PE2:
  THE REPAIR HOLDS" (L10571) ✓.
* **Arithmetic spot-sweep** (independent of §§4–6): the base-case degree
  bound (d₀−1)+(e₀−1)d₀ = e₀d₀−1 < e₀d₀ ✓; the m′ column's four inequalities
  at e₀ ≥ 2 ✓; all eight ω-gain entries recomputed from the two displayed
  per-digit inequalities ✓ (row 1 net = γ₂ − e₁e₀h₀ = h₁ ✓); the ρ-drop
  ≤ −1 on every genre and path bound m·d₀+d₀−1 ✓; e₀·amin(k) ≥ (e₀−k)h₀+1
  from gcd(e₀,h₀) = 1 ✓; 2e₀+3 = 1+4+2(e₀−1) ✓; the [r3, F-B] replacement
  witness divisions and the (αδ)² = −8 non-realizability criterion ✓; S2's
  applicability arithmetic (16 → 48 → 56; 3,816 + 360 = 4,176; AV 656) ✓;
  TLAW − WRONGLET = 360 = 4·(72+18) ✓.
* **Fences:** `liftcorner_checks.py` touched ONLY at dafc0b5 (seal);
  generator + table touched ONLY at b2dc120/a3112dc (r1/r2, as disclosed);
  GRTW2_PROOF last touched 2026-08-04 and its header still carries
  "acceptance counter 0/2" — the note's cap language CURRENT at HEAD ✓;
  ILNRES / ITERLAWN / ITERLAWLIFT_CORNER bodies untouched by this arc (last
  touches 2026-08-03/04, before r1) ✓; no Lean file touched by any arc
  commit ✓; the ARCHIVE region untouched since r4 (r5–r7 diffs contain no
  hunk inside the markers; note byte-frozen since r7) ✓.

**No statement found false at HEAD. No un-superseded refuted text. Strike
discipline intact (every strike quotes the superseded wording inside the
superseding bracket).**

---

## 3. Charge (3): the arc-accounting system at HEAD — CONSISTENT; TRUE UNDER THE PROTOCOL'S DIVISION OF RECORD

* **Hashes and verdicts.** All eight report commits and all nine repair/seal
  commits resolve; each round block's cited verdict matches its report's
  verdict line in count and class (PE1 1C+3G / PE2 0C+5G / PE3 0C+5G / PE4
  0C+6G / PE5 0C+5G / PE6 0C+3G / PE7 0C+1G-minor — all seven re-read this
  pass), and PE8 = 0C/0G at c6097d7.
* **Footer wallclocks vs commit dates:** r1–r4 = 2026-08-05 (17:08 / 18:24–
  18:27 / 19:42 / 21:12–21:19) ✓; r5–r7 = 2026-08-06 (08:23 / 09:21 / 10:15)
  ✓. Acceptance-attempt ordinals (FIRST = PE3 … FIFTH = PE7) match the
  reports' own headers ✓.
* **"Items (1), (2), (7): re-derived by three hostile passes"** — still
  accurate at HEAD: the count is PE2+PE3+PE4; PE5–PE8 added complements
  (read-kill close, fresh-eyes sweeps, D₁ transcription, lift-independence),
  none a full re-derivation of (1)/(2)/(7); my §§4–5 touch charge items (3)
  and (4), not (1)/(2)/(7).
* **The post-PE8 record lag — ADJUDICATED, NOT A DEFECT.** At HEAD the
  STATUS BLOCK/ARC line/grade box still read "PE8 = the next acceptance
  attempt; counter 0/2 — no pass has been clean", while PE8 has run CLEAN
  and the counter of record is 1/2. This is the protocol's own geometry, not
  a stale-record defect of the F6-1 genre: a clean pass fixes nothing and
  triggers no repair round, so the note has NO vehicle to record it — the
  counter advance is the orchestrator's ledger action (so recorded, wave-fold
  5f56308; PE8's verdict says exactly this), and every note surface is
  round-dated by its own label ([r7] brackets, the block label "[r4; edited
  r5, r6, r7]", "this round" language). Unlike F6-1 there is no internal
  contradiction: all surfaces consistently carry the r7-dated record, true
  when committed. Judging this a defect would make every clean pass
  self-falsifying and acceptance unreachable — a reductio. The system of
  record (note + ledger) is consistent and true at HEAD.
* **Dated-text discipline:** every stale close carries its date bracket
  ([r4]/[r6] closes in the grade box; r1–r6 round-block terminators); the
  five-line STATUS BLOCK has grown no sixth line ✓.

---

## 4. Charge (1), component 1 — the CONTENT sub-lemma (charge item (3)), re-derived by a route no pass has used: O-LINEARITY OF MONIC DIVISION — HOLDS

**Decorrelation.** CONTENT ("for monic Φ, the digits of dev(F, Φ) satisfy
w₀-content ≥ w₀-content(F)") was verified by PE1 (listed) and PE6 (spot
re-derivation) — both along the note's own step-subtraction induction. My
route is module-theoretic, no step induction, and simultaneously grounds the
no-cascade and row-7b degree facts the census consumes.

**The derivation.** Let Φ ∈ O[x] be monic of degree d, w₀ the Gauss
valuation (min coefficient valuation; a valuation on O[x] by the base facts
of record — [ILN] S0.2's "w₀ a valuation" is Gauss's lemma).
(i) For each n ≥ 0 write x^n = q_nΦ + r_n, deg r_n < d. By induction on n,
q_n, r_n ∈ O[x]: x^{n+1} = (x·q_n)Φ + x·r_n and x·r_n = cΦ + (x·r_n − cΦ)
with c := lc(x·r_n) ∈ O if deg(x·r_n) = d, else c := 0 — monicity keeps every
coefficient in O.
(ii) Division is O-LINEAR: for F = Σ f_nx^n, the unique (q, r) with
F = qΦ + r, deg r < d is (Σ f_nq_n, Σ f_nr_n). Every coefficient of q and of
r is an O-linear combination Σ f_n·(an O-element), so
v(coeff) ≥ min_n v(f_n) = w₀(F): **w₀(q) ≥ w₀(F) and w₀(r) ≥ w₀(F).**
(iii) The digits of dev(F, Φ) are A₀ = r(F), A₁ = r(q(F)), A₂ = r(q²(F)), …;
by (ii) and induction w₀(qᵏ(F)) ≥ w₀(F), hence **every digit has
w₀ ≥ w₀(F)**. ∎
(iv) *No-cascade corollary* (consumed by (A)'s "exactly two digits per
branch"): if deg F ≤ 2d−2 then deg q ≤ d−2 < d, so q is itself a terminal
digit — the dev is F = r + qΦ, exactly two digits, no re-division. With
F = a·b, deg a < d₀, deg b < d₀, Φ = Φ₀: deg(a·b) ≤ 2d₀−2 ✓.
(v) *Row 7b corollary*: deg q = deg(a·b_{e₀−1}) − d₀ ≤ deg a − 1 whenever the
q-digit is nonzero ✓ (and at deg a = 0, deg(a·b) < d₀ kills it ✓).

The note's own proof sentence and the per-digit application at [r2, G4]
("CONTENT applied to EACH digit separately: w₀(r), w₀(q) ≥ w₀(a·b) ≥
w₀(a)+w₀(b)") are exactly (ii) plus Gauss multiplicativity. The base-fact
status charged as item (3) is sound: nothing beyond the division algorithm by
monic keys and w₀ a valuation is consumed. **No finding.**

---

## 5. Charge (1), component 2 — READ-EQ's case-(b) skeleton (charge item (4)) by GENERAL LEDGER ARITHMETIC from the split identity — HOLDS

**Decorrelation.** PE4 re-derived READ-EQ digit by digit on a CONCRETE orbit
member; PE6 spot-checked the b₀-difference bound; PE8 grounded the splits'
Bézout uniqueness at `eq12` for the lift-independence clause (disclosed
partial correlation: I consume the same eq12 range fact 0 ≤ s₁ < e₀, re-read
at source). No pass has displayed the GENERAL symbolic derivation of the
case-(b) paragraph — the ω(P) = Γ identity, the exactly-one-overflow window,
and the four child-ledger computations. That derivation:

* **The split identity, derived** (not transcribed): γ = e₁u₂ + s₂h₁
  (0 ≤ s₂ < e₁), γ₁ = u₂ − s₂·w₁Φ₁, γ₁ = e₀u₁ + s₁h₀ (0 ≤ s₁ < e₀) give
  γ = e₁γ₁ + s₂(e₁·w₁Φ₁ + h₁) = e₁(e₀u₁+s₁h₀) + s₂γ₂, using w₁Φ₁ = e₀h₀
  (part of the S1 orbit definition) and γ₂ = e₁e₀h₀ + h₁ (S4.1) ✓ — the
  note's parenthetical is exact.
* **Exactly one overflow:** s₁, s₁′ ≤ e₀−1 (eq12 range) ⟹ s₁+s₁′ ≤ 2e₀−2;
  δ₁ = 1 ⟹ s₁+s₁′ ≥ e₀; so S₁″ := s₁+s₁′−e₀ ∈ [0, e₀−2] — ONE pass of the
  orbit identity, and every child's Φ₀-exponent S₁″ (key, b₀) sits < e₀:
  single digits, no re-entry ✓.
* **ω(P) = Γ:** ω(π^UΦ₀^{e₀+S₁″}K^{S₂}) = e₁(e₀U + (e₀+S₁″)h₀) + S₂γ₂ with
  U = u₁+u₁′, S₂ = s₂+s₂′; since (e₀+S₁″)h₀ = (s₁+s₁′)h₀ this is
  γ + γ′ = Γ by the split identity ✓.
* **Key child** π^UΦ₀^{S₁″}K^{S₂+1}: ledger Γ − e₁e₀h₀ + γ₂ = **Γ + h₁** ✓,
  bytes identical on both towers, single digit (S₁″ < e₀), strict π-excess at
  its slot on both ✓.
* **b₀-main children:** −π^{U+h₀}ĉ′Φ₀^{S₁″}K^{S₂} has ledger
  e₁(e₀(U+h₀)+S₁″h₀)+S₂γ₂ = **Γ exactly** — the ON-line digit (row 2's
  gain-0 thread) on both towers; the cross-tower difference carries
  ĉ′ − lift(c′) with res = c′−c′ = 0 ⟹ w₀ ≥ 1 ⟹ ledger ≥ **Γ + e₁e₀** ✓ —
  the on-line residue content coincides.
* **Φ′-only children:** t₀-child ledger ≥ Γ + e₁e₀ (w₀(t₀) ≥ h₀+1), and it is
  a base-case single digit (exponent S₁″ < e₀); mid-children
  −π^Ub_kΦ₀^{S₁″+k}K^{S₂} have ledger ≥ Γ + e₁(e₀·amin(k) − (e₀−k)h₀) ≥
  **Γ + e₁ ≥ Γ+1** ✓, and S₁″+k may reach ≥ e₀ — THE consumption point of
  (TAIL-STAB), which then pins every generated digit ≥ ω(child) > Γ ✓.
* **Close:** on-Γ-line content = the b₀-main residue at slot (S₁″, S₂), equal
  on both towers mod strict π-excess; every deviation ≥ Γ+1 dies in res; the
  ultrametric keeps w₂ = Γ and on-line status equal; reads agree slot by
  slot — exactly the note's paragraph, now derived rather than instantiated.
  (The parenthetical "g₀ = 1 ⟹ s₁+s₁′ ≤ 2e₀−2" is true as stated; the bound
  itself only needs the eq12 range — g₀ = 1 is the scope tag.) **No finding.**

---

## 6. The fresh-instance machine leg — (LEDGER) at p = 7, OUTSIDE the committed battery — 0 VIOLATIONS

Independent implementation (no repo imports; exact ℤ[x] arithmetic, monic
division, honest double dev by Φ′ then Φ₀), placed where no committed
evidence exists — the battery spans p ∈ {2,3,5}, e₀ ∈ {2..6}; this leg runs
**p = 7** with two dense fresh configs and PE1's counter-instance corner
re-implemented from scratch:

* Config A: d₀ = 2, Φ₀ = x²+1, e₀ = 3, h₀ = 1, e₁ = 2, h₁ = 3; b₀ =
  7(3x+2)+49x (tail w₀ = 2), mids 7x, 14 at amin. 594 nonzero digits over
  6 a-values × m ≤ 2e₀+1 × j ≤ 2: **0 violations, min slack 0**.
* Config B: d₀ = 2, e₀ = 5, h₀ = 2 (amin = 2,2,1,1), e₁ = 1, h₁ = 2; dense
  b₀-tail + four mids. 1,224 nonzero digits: **0 violations, min slack 0**.
* Config C: PE1's corner (ℤ₂, Φ₀ = x²+x+1, b₀ = 2, b₁ = 2x): 360 nonzero
  digits, **0 violations, min slack 0**; Φ′ = x⁴+4x³+5x²+4x+3 reproduced, and
  the independent tie **xΦ₀² = (x−2)Φ′ + (6x+2)Φ₀ + (−2x+4)** re-multiplied
  EXACT.

Every dev step self-checks by exact reconstruction (Σ digits·powers == input
at both levels). Min slack 0 in all three configs = the row-2 equality thread
realized, as the proof predicts. (Script: /tmp/pe9_fresh_ledger.py, this
pass's working leg — evidence for this report, not a committed instrument.)

---

## 7. PE8's four observations adjudicated + two new observations — none a defect

* **(O-a) ARC-line "0C + 1 minor" compression — CONCUR.** Literally true
  (one finding, graded minor); both adjacent surfaces carry the full class
  wording; this note never uses "minor" as a class below gap. Not a defect.
* **(O-b) the 34/13 vs 33/14 use-mention wobble — CONCUR, independently
  reproduced.** My own HEAD classification (33+4+17 at 54) sits on the same
  side as PE8's at the same single occurrence (the quoted `ξ := c₀/c′`
  display inside the F4-5 bracket). The note transcribes PE7's split with
  attribution, unit and commit per its own standing rule; totals and the
  covered-cocycle bucket are convention-independent. Not a defect.
* **(O-c) the label-bump self-exclusion — CONCUR.** The "[r4; edited r5, r6,
  r7]" label edit is the dating record OF the edits the r7 list names,
  self-evidencing, and the identical structure was adjudicated unnumbered at
  r5/r6 (PE7) and r7 (PE8). Not a defect.
* **(O-d) the 54-vs-51 pin arithmetic — CONCUR, re-executed.** 54/50 at
  HEAD, 51/47 at the pin, all 3 net-new occurrences mention/quotation inside
  r7's own brackets (my classification, §2). The commit-pinned warrant is
  stable under its own growth. Not a defect.
* **(NEW, O-e) The r1 round block's "PE1's machine leg was bit-identical".**
  Post-F-C/F4-3, this is the one remaining unqualified "bit-identical" for
  the sealed runner on a live surface. Adjudicated NOT a defect, unlike the
  PE2 case: it is a faithful attribution of PE1's own record, and PE1's
  report contains NO dropped qualification — its §1 reports `elapsed 4.4s`
  MATCHING the committed artifact's 4.4s and the family table line-for-line,
  so its headline is internally consistent and unfalsifiable at HEAD (a
  0-jitter run is possible; PE7 saw only 2 differing lines). The [r4]
  machine-leg bracket discloses the timing-field caveat for every later run.
  Recorded so a future pass does not mistake it for a fourth F-C site.
* **(NEW, O-f) The post-PE8 record lag** (§3, adjudicated there): the note's
  "PE8 = next / 0/2" surfaces are r7-dated record, the ledger carries the
  1/2 counter; if the arc closes on this pass, the acceptance fold should
  carry the note's final bring-forward so the closed record is HEAD-true in
  one place (an orchestrator action, not an owed repair — nothing is false
  under the protocol's division of record).

---

## 8. Bottom line

**A CLEAN PASS: 0 CRITICAL, 0 JUSTIFICATION GAPS — the second consecutive.
Per the acceptance rule (counter 1/2 going in; a clean pass here accepts),
this pass ACCEPTS the note at 2/2; the ledger/counter action is the
orchestrator's.** The mathematics is now nine readings deep with no defect
ever found below the description layer; both machine legs reproduce
bit-exactly (modulo disclosed wall-clock fields) with the seal intact; the
record system is consistent and true at HEAD under the protocol's division
of record; my two decorrelated components (CONTENT by O-linearity; READ-EQ's
case-(b) skeleton by general ledger arithmetic) re-derive cleanly, and
(LEDGER) reproduces on fresh p = 7 instances outside the battery with 0
violations. The observations above are recorded context, not owed repairs.

— passPE9, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-06).
Machine legs: **(a)** sealed runner exit 0, `VERDICT: ALL GREEN`,
`TOTAL checks 25409`, 0 violations in every counted family, 1,576 WRONGLET
fires, coverage/teeth minima 6/6, md5 `ccb4351c92573f5f962cae4ae952d8dd` =
seal md5, `git diff dafc0b5 HEAD` = 0 bytes; output differs from the
committed artifact at 6 wall-clock-stamp lines only, empty under timing
normalisation. **(b)** children generator exit 0, regenerated table
byte-identical (diff 0 bytes), A1–A6 PASS, A7 all four legs PASS (752 nodes /
5,336 children; 0/0/0/0; observed max branching = 2e₀+3 at every
e₀ ∈ {2,…,6}). **(c)** fresh-instance leg: p = 7 configs (e₀,h₀) = (3,1),
(5,2) + the PE1 corner, 2,178 nonzero digits, 0 violations, min slack 0.
Nothing in the repo was edited by this pass except this report.
