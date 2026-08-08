# W11 passPE4 report — hostile verification of W11_PROOF_2026-08-08.md (THE ACCEPTING ATTEMPT)

**Target:** `lean/notes/openmath/W11_PROOF_2026-08-08.md` at HEAD. **Role:**
hostile verifier, fresh context, fix nothing. All prior arc records read
first: the PE1/PE2/PE3 reports (fbf0a02 / 473a993 / 839b735), the r1/r2
repair diffs (8c87fa3: 114 diff lines; 31506b3: 69 diff lines), and the S10
verdict. This pass mined what the charge named as unmined: the 2SIDED
derivation from scratch in both characteristics (with a per-HISTORY machine
tie no pass had), the S2.5 assembly logic re-derived symbolically, the
S7 roster census, freeze-convention integrity across the whole arc, and a
wild-card vein — a MUTATION AUDIT of the sealed battery (does it actually
go RED under seeded defects? — no prior pass ever tested the teeth beyond
their fire-counts).

**Verdict: CLEAN — 0 CRITICAL + 0 JUSTIFICATION GAPS + 0 MINOR.**
Second consecutive clean pass: the acceptance counter reaches **2/2 —
THEOREM W-11(n = 2) is ACCEPTED**; the fold is owed to the orchestrator.
Two non-finding remarks recorded (§1), one of them instrument-side coverage
information the fold should carry forward.

---

## 1. FINDINGS

None.

**Non-finding remarks (recorded for the arc, no repair owed — and none
possible note-only: the note's own sentences are accurate at both sites):**

* (R-a) **Runner-docstring coverage overstatement (instrument-side, not the
  note).** The frozen runner's docstring (`w11_checks.py` line ~110) says
  the deep rows realize "menu rows through RAM(7), SPLITEQ/INERTDEEP(3),
  2SIDED(2,5)". Censused against the committed JSON: RAM(7) ✓ ((2,8) both
  kinds), INERTDEEP(3) ✓ ((2,8) both kinds), 2SIDED(2,5) ✓ ((2,8) both
  kinds) — but **SPLITEQ is realized at k = 1 ONLY on every one of the 30
  sealed rows** (deep rows are q ∈ {2,3}: at q = 2 SPLITEQ is empty
  ((q−2) = 0); the only q ≥ 3 rows with N ≥ 3 stop at N = 4, so k ≤ 1).
  SPLITEQ(2) and SPLITEQ(3) are realized NOWHERE in the sealed battery; the
  docstring's "SPLITEQ/…(3)" is true only on the INERTDEEP half. The NOTE's
  own S7 sentence claims only "rows through RAM(7)" — accurate — and S7
  incorporates the docstring by reference for the teeth plants only. No
  note sentence, box, or S10 claim is touched; the runner is byte-frozen
  (seal 7020ceb), so remark-grade is the only honest disposition. Fold
  note: the sealed battery's machine evidence for the SPLITEQ k-scaling
  (q^(−2k) in the law) is k = 1 only; the arc's sole ≥ 2 machine instance
  is PE3's fresh route at (Fqt, 4, 5) (SPLITEQ(2), char-2 Artin–Schreier
  split). The mathematics of clause (ii) is carried by S2, not the roster,
  so nothing is overclaimed — but a future W-11 sibling battery could
  cheaply add a (q ≥ 3, N ≥ 6) row.
* (R-b) Roster q-coverage boundaries, censused (§2.3): 2SIDED and
  RAM(h ≥ 3) are machine-realized only at q ∈ {2,3} (both characteristics;
  the N ∈ {2,3} rows carry q up to 9 but see only RAM(1)/SPLITEQ(1)/
  INERTDEEP(1)/TAIL(1)). Disclosed row list; the q-dependence at those
  families is carried by the proof + the PE-passes' fresh routes (this
  pass adds 𝔽₉ at N = 4 via the disc fibration). No claim touched.

---

## 2. CHARGE-BY-CHARGE RECORD

### 2.1 The 2SIDED family re-derived from scratch, BOTH characteristics (charge vein 1)

No prior pass had re-derived this family as its own object (PE1/PE2 checked
it inside the trichotomy + totals; PE3 did two instances). Full derivation:

**Read and decidedness.** At a node C(2s+1, s+1) with u = v(A₀) ≤ N−1
exact, w = v(A₁) = w₁ exact, 2w₁ < u: the lower hull of (0,u),(1,w₁),(2,0)
has two sides of lattice length 1 with slopes w₁ and u−w₁ (both integer,
w₁ < u−w₁). One-point-side factorization is degree-1 Hensel in BOTH
characteristics: substitute x = A₁y, f = A₁²(y² + y + A₀/A₁²) with
v(A₀/A₁²) = u−2w₁ ≥ 1; the residual ȳ(ȳ+1) is separable in every
characteristic (char 2 included — the two roots 0̄, 1̄ stay distinct), so
Hensel splits f into two monic linear factors with root valuations w₁
(from the ȳ = −1 branch) and u−w₁ (from ȳ = 0). σ = split, two roots in O
at distinct valuations; v(disc) = 2·v(r₁−r₂) = 2w₁ (both chars). Since
u, w₁ ≤ N−1, every lift of the window pair has the same (u, w₁), hence the
same hull: DECIDED. Setting w₂ = u−w₁: the leaf datum is exactly the
table-(i) row 2SIDED(w₁,w₂), window-visible iff w₁+w₂ ≤ N−1.

**Count, per instance.** #{A₁ : v = w₁ exact} = (q−1)q^(N−1−w₁) and
#{A₀ : v = u exact} = (q−1)q^(N−1−u), independent constraints, both
s-independent for any node s < w₁ (w₁ ≥ s+1 and u ≥ 2w₁+1 ≥ 2s+3 make the
node constraints vacuous). Per instance: (q−1)²q^(2N−2−u−w₁).

**Bracket over histories.** The read happens at whichever node the
recursion reached; a 2SIDED(w₁,w₂) member can sit over any history
H = (k₁ < ⋯ < k_t) with k_t < w₁ (each refine at depth k requires
v(A₁) ≥ k+1, and the S2.3 isomorphism is count-preserving with q−1
letters per step). instances(s) = Σ_t C(s−1,t−1)(q−1)^t = (q−1)q^(s−1)
(verified symbolically, s = 1..11); Σ_{s<w₁} instances(s) = q^(w₁−1)
(verified symbolically, w₁ = 1..11). Per center: q^(w₁−1) ·
(q−1)²q^(2N−2−u−w₁) = **(q−1)²q^(2N−3−w₁−w₂)** = clause (ii)'s law;
whole space × q centers, limit density (q−1)²/q^(w₁+w₂+2) = table (i) ✓
(both verified symbolically for all visible (w₁,w₂), N = 4..12).

**Where characteristic enters, checked at each door:** (a) the q centers
at level 0 (char ≠ 2: one center −ā₁/2 per double-root f̄; char 2: ā₁ = 0
and center √ā₀ Frobenius — q classes each way); (b) the S2.3 refinement
isomorphism (char-split digit cancellations, re-checked: −2z̄+2z̄ = 0 /
z̄²−2z̄²+z̄² = 0 vs A₁ unchanged / 2z̄² ≡ 0); (c) the Hensel step above
(char-free). The count algebra itself never sees the characteristic.

**Per-HISTORY machine tie (new to the arc):** own classifier with history
tracking (`/tmp/w11pe4/hist_bracket.py`, own arithmetic, no runner
imports), rows (Zp,3,6), (Fqt,3,6), (Fqt,2,6): for EVERY 2SIDED key and
EVERY realized history H, count == q·(q−1)^|H|·(q−1)²q^(2N−2−u−w₁)
EXACTLY, and the history sum == q·q^(w₁−1)·per-instance — e.g. at
(Zp,3,6), 2SIDED(2,3): H = () gives 324 = q·108, H = (1) gives 648 =
q·(q−1)·108, bracket 972 = q·q^(w₁−1)·108. The (q−1)-letter weight and
the bracket structure are visible RAW, in both ring types and both
characteristics — the S2.5 instance-bracket mechanism confirmed at the
per-history grain for the first time in the arc. **ALL MATCH.**

### 2.2 The S2.5 assembly re-derived (charge vein 2: how families + drainage compose into (i)–(iii))

Assembly logic re-derived and checked symbolically in q
(`/tmp/w11pe4/assembly_sym.py`, sympy, exact):

* **Clause (i) skeleton:** the read is a total deterministic function
  (level-0 trichotomy → per-center node recursion → S2.1 trichotomy at
  each node → refine strictly increases depth, bounded by ⌊(N−1)/2⌋ in
  window), so the leaves + the undecided cell PARTITION q^(2N) by
  construction; the menu list is complete iff the trichotomy is (re-read
  against S2.1; the residual censuses re-checked in both characteristics:
  (q−1)(q−2)/2 / q(q−1)/2 / q−1, row sum q(q−1)).
* **Per-center window identity (the finite assembly):** Σ over clause
  (ii)'s per-center laws [RAM(2k−1), k ≤ ⌊N/2⌋; 2SIDED(w₁,w₂),
  w₁+w₂ ≤ N−1; SPLITEQ/INERTDEEP/TAIL(k ≤ ⌊(N−1)/2⌋); undecided q^(N−1)]
  **== q^(2N−2) as a polynomial identity in symbolic q, every N = 2..12**;
  whole space q·(that) + 2·((q²−q)/2)q^(2N−2) == q^(2N). This is the
  finite-N exhaustiveness that clause (iii) asserts; clause (ii)'s laws
  force it, and the machine census re-verifies it per row.
* **σ-symmetry at every window:** Σ(2SIDED + SPLITEQ + TAIL) == Σ INERTDEEP
  per center, symbolic q, N = 2..12; and per (N, w) the r2 telescoping
  identity re-verified symbolically (geometric sum + tail cell == q^(N−1−2w);
  factor (q−1)(1+(q−2)/2) = q(q−1)/2).
* **Drainage:** undecided per instance q^(⌈(N−1)/2⌉), s-uniform on
  reachable s ≤ ⌊(N−1)/2⌋, × bracket q^(⌊(N−1)/2⌋) × q centers = q^N.
* **Limits:** ram-total 1/(q+1); 2SIDED-total 1/(q²(q+1)); SPLITEQ-total
  (q−2)/(2q²(q+1)); deep-split == deep-inert == 1/(2q(q+1)); split == inert
  == q/(2(q+1)); Σ = 1; capstone 1/4 + 1/12 = 1/3 at q = 2 — all exact
  (geometric closed forms, sympy). ALL PASS.

### 2.3 S7 roster census (charge vein 3)

From the committed `w11_checks_results.json` (30 rows == the S7 list;
Σ q^(2N) re-summed = 1,235,872 ✓): rows realizing each family —
SEP-SPLIT/SEP-INERT/RAM/UNDECIDED **30** each (12 Zp + 18 Fqt);
INERTDEEP and SPLIT-TAIL **19** (8 Zp + 11 Fqt); SPLITEQ **11** (4 Zp +
7 Fqt, incl. the char-2 Artin–Schreier-split rows q = 4, 8); 2SIDED **8**
(4 Zp + 4 Fqt). **Every family ≥ 8 rows and both characteristics — the
≥ 2 (q,N) bar is exceeded four-fold.** Depth coverage: RAM through h = 7,
INERTDEEP through k = 3, 2SIDED through (2,5), histories to depth 3 (64
members at (Zp,2,8)) — but SPLITEQ at k = 1 only and 2SIDED/deep-RAM at
q ∈ {2,3} only (remarks R-a/R-b). Teeth arithmetic re-derived from the
closed forms: SIGMA 3,020 = 20+80+1344+27+270+250+1029, TAMEDISC 1,440 =
16+80+1344, dlift 1,070 = Σ(q^(2N)−q^N) over its 4 rows ✓✓✓.

### 2.4 Freeze-convention integrity (charge vein 4)

`git diff 31506b3 HEAD --` on the note: **empty** (byte-frozen since r2).
Arc text-state chain verified pairwise byte-identical: cb05127 == fbf0a02
(PE1 read the sealed+verdict text), 8c87fa3 == e3db535 == 473a993 (PE2
read exactly the post-r1 text), 31506b3 == 839b735 == HEAD (PE3 and this
pass read exactly the post-r2 text). The r1/r2 diffs touch only the
declared sites (six findings + S-STATUS/S10 echo; telescoping bracket +
v(2)=1 pins + S-STATUS/S10 echo). Runner md5
`500aae152bb5b5e9df3712904a6d73a6` == `git show 7020ceb:…` ✓; committed
artifacts `c0b6b10b…`/`72ad1567…` match cb05127's record ✓. Lean anchors
unchanged since PE3 (no commits touch the two files): `gate3_inert_q2` @
`OM/OMCountV2.lean:646`, `omMenu_order0 = rfl` @ :315,
`montes_unconditional_exhaustive` @ `OM/RealInstanceV2.lean:439` with
`hExhaust` at :441–443 — the note's 439–442 cite faithful.

### 2.5 Wild-card vein: MUTATION AUDIT of the sealed battery

No prior pass tested whether the battery actually goes RED under a seeded
defect (all verified only that teeth FIRED on the healthy run). Four
mutants of a /tmp copy (frozen imports byte-identical, smoke mode: 5
census rows + towers C2A/C3E + oracle (2,3)+(3,2) with gp):

| mutant | seeded defect | result |
|---|---|---|
| M0 | none (baseline) | **GREEN, exit 0** |
| M1 | predict(): RAM closed form × spurious q | **RED**, 6 W11-CENSUS violations (obs 16 vs pred 32 …) |
| M2 | classifier: odd-char residual σ swapped (SPLITEQ↔INERTDEEP) | **RED**, W11-CENSUS ×2 + W11-EXHAUST symmetry ×2 |
| M3 | classifier: tail boundary 2w+1 ≤ N → 2w ≤ N (w = N/2 wrongly certified split) | **RED**, 29 violations across THREE independent families (CENSUS 6, EXHAUST drain 11, ORACLE 12 — PARI catches the wrongly-certified members directly) |
| M4 | leaf_expect: inert leaves keyed (2,1,1) | **RED**, 47 W11-ORACLE violations — the PARI leg alone catches it |

The battery's independence claims are real: a wrong closed form, a wrong
σ-assignment, a wrong window boundary, and a wrong oracle expectation are
each caught, M3 redundantly by both the self-census and the independent
engine. (Scratch: `/tmp/w11pe4/mut/`, not committed; repo untouched.)

---

## 3. MACHINE LEG

**Seal:** runner md5 == 7020ceb ✓ (§2.4). **Re-run:** exit **0**, verdict
**GREEN**, elapsed 50.0 s (committed 49.9 s). Every number == §S10: 30/30
census rows; checks **1,250,280**; violations 0 in all six families; teeth
MISSING=SHADOW=DRAIN=**30**, SIGMA=**3,020**, TAMEDISC=**1,440**; towers 12
levels (wild 7, beyond-211 1 = C3E level 2, (2,3,1), p = 2, γ = 13); oracle
(2,3):64/0 (2,4):256/0 (2,6):4096/0 (3,2):81/0 (3,3):729/0 (5,2):625/0
(7,2):2401/0. **Artifact diff vs committed: timing-only** (output.txt
`elapsed:` line; `elapsed_s` fields in results.json — programmatic
strip-compare content-identical); artifacts **restored to committed bytes**
(md5s re-verified: c0b6b10b… / 72ad1567…). S10 spot values re-checked in
the committed JSON ((Zp,2,8) RAM 16384/4096/1024/256, undec 256, depth-3 =
64; (Fqt,8,3) full seven-family table).

## 4. FRESH ROUTE — the DISC-FIBRATION angle (differs from all four prior routes)

Prior fresh routes: PE1 own classifier (~345k polys); PE2 own classifier +
per-member ℚ_p square-class σ-oracle on lifts; PE3 own-forms/own-F₄
classifier on never-checked rows. This pass uses **no classifier and no
recursion at all**: for odd residue characteristic, disc = a₁²−4a₀ is a
UNIFORM map (O/π^N)² → O/π^N (fixed a₁: a₀ ↦ disc is a bijection, 4 a
unit), so #{v(disc) = d} = (q−1)q^(2N−1−d) and #{disc ≡ 0} = q^N — and the
menu's v(disc) laws (S2.2, re-derived from root valuations) turn the whole
clause-(ii)/(iii) table into fiber-count identities:

* v = d odd fiber == RAM(d) whole-space count — EXACTLY the whole fiber;
* v = 0 fiber == SEP-SPLIT + SEP-INERT, halved by the square class;
* v = 2k > 0 fiber: square half == SPLITEQ(k) + Σ_{w₂} 2SIDED(k,w₂) +
  SPLIT-TAIL(k), nonsquare half == INERTDEEP(k) — the r2 telescoping
  identity reappears here as the tail term completing the truncated
  2SIDED geometric sum to exactly half the fiber (a THIRD independent
  derivation of the every-window split = inert law, for odd q);
* **disc ≡ 0 (mod π^N) fiber == the σ-undecided residue exactly** (decided
  leaves all have v(disc) ≤ N−1; both counts q^N) — the drainage law
  derived from disc-uniformity alone.

All eight identity families verified symbolically (N = 2..12, symbolic q;
§2.2's script section H). **Machine leg — measured fiber tallies vs the
note's menu sums, EXACT on five rows:** new territory **(Zp,3,5)**,
**(Zp,5,4)**, **(Fqt,5,4)**, **(Fqt,9,4)** (never measured by any arc
instrument; the 𝔽₉ N = 4 row is 43,046,721 pairs, numpy-vectorized F₉
arithmetic built from F₃[i] with self-checked tables) plus roster row
**(Fqt,9,3)** cross-tied: the committed classifier's family sums per fiber
== my measured fiber tallies key-for-key. Drainage disc≡0 = q^N EXACT on
all five rows (243 / 625 / 625 / 6561 / 729). **FRESH-ROUTE VERDICT: ALL
MATCH** (`/tmp/w11pe4/fresh_discfiber.py`, no imports from
`verification/openmath` except the read-only JSON tie).

---

## 5. SUMMARY FOR THE RECORD

The post-r2 text survives a fourth hostile pass with zero findings, on
veins no prior pass had mined: the 2SIDED family re-derived from scratch in
both characteristics with the arc's first per-HISTORY machine tie (the
(q−1)^t letter weights and the q^(w₁−1) bracket visible raw); the S2.5
assembly re-derived as symbolic polynomial identities (per-center
exhaustiveness, σ-symmetry, drainage, limits, Σ = 1); the 30-row roster
censused (every family ≥ 8 rows, both characteristics; two coverage
remarks recorded for the fold); freeze-convention integrity verified
byte-level across the entire arc (each pass provably read exactly its
era's text); the sealed battery survives a four-mutant audit (baseline
GREEN, every seeded defect RED, the PARI leg independently catching two of
them); the sealed runner re-runs GREEN bit-stable; and a genuinely new
fresh route (disc-fibration counting, classifier-free) reproduces the
entire menu table, the every-window σ-symmetry, and the exact q^N drainage
law on 43M+ never-measured pairs including 𝔽₉ at N = 4.

**Pass verdict: CLEAN (0/0/0). Acceptance counter: 2 of 2 consecutive
clean passes — THEOREM W-11(n = 2) is ACCEPTED. Fold owed to the
orchestrator** (S-STATUS/grade-box update is the composer's, not the
verifier's). Remarks R-a/R-b travel with the fold.

*Verifier: fresh-context hostile pass PE4, 2026-08-08. Scratch artifacts:
`/tmp/w11pe4/` (assembly_sym.py, limits_sym.py, fresh_discfiber.py,
hist_bracket.py, mut/, rerun.log — not committed).*
