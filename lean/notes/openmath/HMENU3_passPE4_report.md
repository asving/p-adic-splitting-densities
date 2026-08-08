# HMENU3 passPE4 report — hostile verification of HMENU3_PROOF_2026-08-08.md (THE ACCEPTING ATTEMPT)

**Pass:** PE4 (fourth hostile pass on the (hMenu-3) discharge note; fresh
context; verifier fixes nothing, quotes and classifies; fences/boxes/annex
drafts are part of the statement; counter enters at 1/2 after PE3 CLEAN — a
second consecutive clean pass ACCEPTS at 2/2). **Target:**
`lean/notes/openmath/HMENU3_PROOF_2026-08-08.md` at HEAD, byte-frozen since r2
(e1280be verified: HEAD md5 943c51e2… == the r2 blob; seal 64d3ff9, verdict
625fa49, PE1 f4f7b03, r1 3235e1b, PE2 af988ee, r2 e1280be, PE3 7e5026a).
**Date:** 2026-08-08.

## VERDICT LINE

**CLEAN — 0 CRITICAL + 0 GAPS + 0 MINOR. Second consecutive clean pass: the
2-clean acceptance counter reaches 2/2 — the note is ACCEPTED; the acceptance
fold is owed to the orchestrator.** Every orchestrator-designated unmined vein
CONFIRMS the note: (1) LEMMA HM3-2 re-derived IN FULL for the first time in
the arc — the shear table is exactly the abscissa grading of H-2(ii)'s map
(height at abscissa j shifts by (3−j)k: u₀-type +3k, the abscissa-1 vertex
height +2k, slopes/depths +k), the ghost zones re-derived to the corrected
N−jk pairing with fiber q^{3k} = 2k+k+0 free digits, and the lemma verified
TWO new ways: key-resolution self-similarity on the COMMITTED tallies (268
checks over 15 (row,α-depth) pairs, both directions, 0 violations — every
committed (('ALPHA',k),…)-key equals (q−1)q^{3k} × its unsheared image on the
window-(N−3k) row, through accumulated depth 2) and CONSTRUCTIVELY (the
transport used as a member factory; see wildcard). (2) The SEP tier
re-derived: the three censuses q(q−1)(q−2)/6, q²(q−1)/2, (q³−q)/3 sum to
q²(q−1) = the squarefree count q³−q², the level-0 partition
SEP + DBL + TRP = q²(q−1)+q(q−1)+q = q³ is exact, and SEP is disjoint from
the DBL boundary by level-0 factorization type (a multiplicity-2 root of a
cubic is forced rational, so DBL level-0 patterns are exactly (y−a)²(y−b),
a ≠ b ∈ F_q — the boundary families live inside that stratum, SEP is
separable). (3) The drainage-complement identity re-derived SYMBOLICALLY in q
(not numerically): the full aggregate menu + u(q,N) == q^{3(N−1)} as
POLYNOMIAL IDENTITIES in ℚ[q] at every window N = 2..14, and the whole-space
identity SEP + DBL + r(N)-boundary + q·TRP + q·u == q^{3N} likewise — the
fresh route below. (4) The S8.1 BOX-2 annex and its applied copy in W12_PROOF
ANNEX 2 are RAW BYTE-EQUAL (808 bytes, not merely normalized-equal); the HEX3
S8.2 pointer annex is verified NOT applied anywhere in HEX3_PROOF, consistent
with the note's own "nothing edited" framing. (5) Freeze integrity across all
four eras verified byte-level and quote-level: the note has exactly four
commits ever (seal → verdict-append → r1 → r2), each PE report's verbatim
quotes exist in exactly its era's text, no era carries anachronistic repair
tags (era-1's only "[r1" hits are references to W-12's own [r1 F3] tag; era-2
has no [r2 m·]), and HEAD == r2 byte-identical. (6) Wildcard: the FIRST
multi-lift (A0) probe in the arc, on wild strata at a never-oracled row —
constructive HM3-2 fibers at (Zp,3,6) (26,244 + 2,916 distinct states built
from reduced-member × letter × ghost data, EXACTLY the committed
(('ALPHA',1),('RAM3',4/5)) counts) with 1,200 deep wild-p=3 PARI σ-reads on 3
random beyond-window lifts per sampled member, plus 960 depth-0 wild-RAM3 and
450 wild-p=2 RAM2LIN multi-lift reads — every single σ the leaf-table value.
Machine leg bit-clean: runner md5 = seal 65326f85…, fresh full run GREEN exit
0, 183,387/0 in 447.9 s, teeth 21/15/10/4, results JSON structurally
identical ex `elapsed_s`, output txt's ONLY diff line is the timing line.
Supplier movement since r2 (HEX3 passPE2 landed at f60348b, NOT CLEAN
0C+1G+1m) checked clause-by-clause: nothing fired here is touched — recorded
as arc-aging REMARK 1, the same genre PE2/PE3 classified as non-findings.

---

## FINDINGS

None.

---

## CHARGE 1 — LEMMA HM3-2 re-derived in full (the never-mined vein)

**What the lemma claims (S3.1, quoted).** "the raw key of X ∈ D_k equals the
raw key of σ_k(X) (a window-(N−3k) state) with every step/leaf parameter
sheared: u₀-type params +3k, slope/depth params +k, the LINRAM2 vertex height
+2k; and every fiber of σ_k (q^{3k} ghost digits) is key-constant."

**Own derivation, three parts.**

*(a) The ghost zones and the fiber count (H-2(i) consumed at the CORRECTED
pairing).* D_k = {v(B₂) ≥ k+1, v(B₁) ≥ 2k+1, v(B₀) ≥ 3k+1} and σ_k divides
coordinate j by π^{(3−j)k}, taken mod π^{N−3k}. A reduced digit of B̃_j at
height v corresponds to the raw digit at height v+(3−j)k < (N−3k)+(3−j)k =
N−jk. So the raw digits DETERMINED by σ_k(X) at abscissa j are exactly
{< N−jk}, and the free (ghost) digits are {≥ N−jk}: 2k at abscissa 2
(heights N−2k..N−1), k at abscissa 1, 0 at abscissa 0 — total q^{3k},
matching H-2(ii)'s displayed fiber and REPRODUCING the corrected pairing
N−jk from scratch (the pairing HEX3's PE1 fixed at HEX3 r1; my derivation
never consults the broken sealed display, and independently confirms the
fixed one). H-2(i) (consulted digits sit strictly below the ghost zones,
recentering updates never pull ghost digits down — carries move up) then
makes the whole CHAIN, not merely the drain verdict, a function of σ_k(X):
this is exactly the leaf-resolution upgrade the note claims, and it needs
nothing beyond H-2(i)+(ii) as pinned.

*(b) The shear table = the abscissa grading.* H-2(ii)'s correspondence
shears heights by (j,v) ↦ (j, v−(3−j)k). Consequences, parameter class by
parameter class: a parameter that is a HEIGHT AT ABSCISSA 0 (v(B₀)-type:
RAM3's h, LINRAM2/RAM2LIN/VERT1/VERT2's u₀) moves by (3−0)k = 3k ✓; a
height at abscissa 1 (LINRAM2's u₁, the vertex-at-1 height) moves by
(3−1)k = 2k ✓; a height at abscissa 2 (VERT2/RAM2LIN's t) moves by k ✓;
a SLOPE (difference of heights at adjacent abscissae: ALPHA/FULL11SQ's d,
FULL's k, 3LIN's m_i, VERT1's slope field) moves by ((v₁−(3−j₁)k) −
(v₂−(3−j₂)k) − (v₁−v₂))/(j₂−j₁) = +k ✓; a recentering DEPTH moves by k
(f(π^k(y+s̃)) = π^{3k}f̃(y+s̃), s = π^k s̃) ✓. That is the note's entire
shear table — "u₀-type +3k, slope/depth +k, LINRAM2 vertex height +2k" is
the (3−j)k grading read off at j = 0, 1 and at slopes. Cross-checked
against HM3.A's displays: ('VERT2', (3t+2j)+3s, t+s) has u₀-type +3s and
abscissa-2/slope +s ✓; ('VERT1', 3k+w+3s, m) with m = s+k the raw slope ✓.

*(c) Key-constancy of fibers + the α-prefix count.* By (a) the chain of X
is a function of σ_k(X); the q^{3k} ghost digits are never consulted, so
every fiber is key-constant ✓. With H-2(iii) (the α z-slice → D_k
bijection, q−1 letters, pinned digits cancelling in every characteristic —
including the char-3 (0,0,−z³) degeneration), the α-prefixed menu =
(q−1)q^{3k} × the window-(N−3k) menu, key-sheared ✓ = THEOREM HM3.A's
α-line.

**Machine leg 1 (new): committed-tally self-similarity at key resolution.**
Own script (`/tmp/hmenu3_pe4/selfsim.py`): for every committed row (kind,q,N)
and every k with (kind,q,N−3k) also committed (15 pairs), every key starting
(('ALPHA',k),…) must equal (q−1)q^{3k} × the count of the UNSHEARED tail key
on the smaller row, and every smaller-row key must appear sheared (both
directions). Result: **268 checks, 0 violations** — including the
accumulated-depth keys ((('ALPHA',1),('ALPHA',2),…) unshearing to
(('ALPHA',1),…) — the depth-accumulation convention verified), all leaf
genres (RAM3 −3k, 3LIN slopes −k each, LINRAM2 (−3k,−2k), RAM2LIN/VERT1/
VERT2 (−3k,−k), FULL −k, λ fields fixed, DRAIN fixed). Max raw α-depth on
the roster confirmed = 2 (at (Zp,2,7) (('ALPHA',1),('ALPHA',2),('DRAIN',)))
— PE3's census reproduced. **Machine leg 2 (constructive): see CHARGE 6.**

## CHARGE 2 — the SEP tier (3 families) and its disjointness from the DBL boundary

**Censuses re-derived.** Level-0 residual f̄ = y³+b̄₂y²+b̄₁y+b̄₀ over F_q.
SEP3 (three distinct F_q-roots): C(q,3) = q(q−1)(q−2)/6. SEPLQ (root ×
irreducible quadratic): q·(q²−q)/2 = q²(q−1)/2. SEPC (irreducible cubic):
(q³−q)/3. Sum = [q³−3q²+2q + 3q³−3q² + 2q³−2q]/6 = q³−q² = q²(q−1) = the
monic squarefree-cubic count q³ − q^{3−1} ✓ (two independent routes agree).
Each family is decided at level 0 with all N−1 higher digits of each
coefficient free: count C₀(q)·q^{3(N−1)}, a point family (d_F = 0), (A1)-
admissible trivially; (A0) = Hensel/Ore at the separable level-0 residual
(every lift splits as the residual does): σ = {(1,1)³}, {(1,1),(1,2)},
{(1,3)} respectively.

**Level-0 partition is exact.** A multiplicity-2 root a of a cubic over F_q
is Galois-stable with multiplicity preserved, and its degree-2 orbit would
force degree ≥ 4 — so a ∈ F_q and the cofactor root b ∈ F_q: the DBL
stratum's level-0 patterns are EXACTLY (y−a)²(y−b), a ≠ b ∈ F_q [q(q−1)
patterns], TRP's are (y−a)³ [q]. SEP + DBL + TRP = q²(q−1) + q(q−1) + q =
q³: a PARTITION of all residuals — no overlaps, no residue. (Symbolic
check: engine leg 7, exact.)

**Disjointness from the DBL boundary.** The complement families in r(N)
(S5.3's transported SPLIT-TAIL aggregate ⌊(N−1)/2⌋(q−1)q^{N−2} per pattern
and the UNDECIDED q^{N−1}) are strata OF THE DBL LOCUS — every member has
level-0 type (2,1). SEP members are separable at level 0. Disjointness is
decided before any window digit is read; no boundary mass can be
double-claimed by a SEP family (nor by TRP: type (1³)). Within the DBL
stratum, boundary-vs-decided disjointness is the deterministic W-11 read
(SPLIT-TAIL = the A₀ = 0-window exit with v(A₁) = w exact; UNDECIDED =
A₀ = 0-window with v(A₁) ≥ M+1; the four decided leaves have A₀ ≠ 0
in-window — mutually exclusive loci by definition). The whole-space
identity (engine leg 3) then confirms no mass is dropped or double-counted
ANYWHERE: SEP + DBL-decided + DBL-boundary + q·(TRP decided) + q·u(q,N) ==
q^{3N} exactly, symbolically in q, at every N ≤ 12.

## CHARGE 3 — the aggregate-level drainage-complement identity, SYMBOLIC (fresh route)

**Route (differs from all three priors: no state enumeration [PE1/PE3], no
numeric convolution [PE2] — pure polynomial identities in ℚ[q] with symbolic
q, laws transcribed from the NOTES, not from runner code).** Own engine
(`/tmp/hmenu3_pe4/sym_engine2.py`; exact Laurent-polynomial dict arithmetic
over ℚ for the finite-window legs, closed-form geometric sums for the
limits): tier I = the seven W12-S2.4 laws with
their visibility ranges (params ≥ 1, u₀ ≤ N−1, S_λ censuses re-derived:
S_{(1)} = q−1, S_{(1,1)} = (q−1)(q−2)/2, S_{(2)} = q(q−1)/2, S_{(1,1,1)} =
(q−1)(q−2)(q−3)/6, S_{(1,2)} = q(q−1)²/2, S_{(3)} = (q³−q)/3 — pinned
against the committed w12 exploratory values FULL(1,'3')/FULL(1,'12') at
(Zp,2,4), which decided the whole-space ×q normalization); tier II =
b(m)·[tier I at window N−3m]; B1/B2/B3 = b(m) × route prefactors × the
A_L/A^{(j)}_L aggregates rebuilt from W12-L0's instance laws × the W-11
bracket q^{s_max} (the bracket-cancellation A_RAM(u) =
(q−1)q^{2M−1−(3u+1)/2}·q^{(u−1)/2} = (q−1)q^{2M−u−2} re-derived — the r2
carry-rescope algebra confirmed a fourth time); u(q,N) and R(M) transcribed
from THEOREM HEX3.A as stated.

**Results (every check a polynomial identity with symbolic q):**

* **L1 (n = 2 exhaustiveness):** Σ_L Σ_x A_L(M) + ⌊(M−1)/2⌋(q−1)q^{M−2} +
  q^{M−1} == q^{2(M−1)} — EXACT for M = 2..14. {ENGINE-L1}
* **L2 (THE identity):** [tier I + tier II + B1/B2/B3](N) + u(q,N) ==
  q^{3(N−1)} — EXACT for N = 2..14. This is "S-menu + drain = whole space"
  at the aggregate level: THEOREM HM3.B's family list is exactly
  density-complementary to THEOREM HEX3.A's residue, as polynomials in q,
  jointly re-deriving HM3.B's exhaustiveness AND (A2)'s exactness with no
  enumeration anywhere. {ENGINE-L2}
* **L3 (whole space / S5.3's r(N)):** q²(q−1)q^{3(N−1)} [SEP] +
  q(q−1)q^{N−1}·ΣA_L(N) [DBL decided] + q(q−1)q^{N−1}(⌊(N−1)/2⌋(q−1)q^{N−2}
  + q^{N−1}) [DBL boundary = r's first leg] + q·TRP-decided + q·u(q,N)
  [r's second leg] == q^{3N} — EXACT for N = 2..12. {ENGINE-L3}
* **L4 (the five R_τ, symbolic limits):** summing the same transcriptions
  over their INFINITE ranges (sympy exact geometric sums; no partial-sum
  approximation): all five displayed closed forms reproduced symbolically,
  Σ_τ R_τ = 1, E[#roots] = q/(q+1), q = 2/3 anchor vectors exact.
  {ENGINE-L4}
* **L5 (S5.5 intermediates):** block densities (1/(q(q+1)), 1/(q³(q+1)),
  (q−2)/(2q³(q+1)), 1/(2q²(q+1))), block total = q^{−2}; amplifier
  Σb(m)q^{−9m} = (q⁶−1)/(q⁶−q); the j-entry ratio Σ_j a^{(j)}_L =
  (q−1)/(q³−1)·a_L for ALL FOUR L; the β_τ collector display β_τ =
  c²_{τ′}(q−1)²q²/((q⁶−1)(q³−1)) verified against my independently summed
  route densities (β1+β2+β3 = (q−1)(q−2)+(q−1)+(q−1)²/(q³−1) over q(q⁶−1)
  in the c² normalization — the note's parenthetical is exactly right);
  Σ_τ T_τ = q^{−3}. {ENGINE-L5}
* **L6 (oracle-count tie):** the closed forms evaluate the deep-decided
  per-center counts at the four oracle rows to EXACTLY 48/624/6,688/2,592
  — the sealed P-7 member counts are now DERIVED from the menu symbolically,
  not merely measured. {ENGINE-L6}

## CHARGE 4 — S8.1 annex byte-ties (vein 4)

The [BOX-2 ANNEX, 2026-08-08, HMENU3] blockquote in this note's S8.1 and the
copy applied in W12_PROOF's ANNEX 2 (line 1378) are **RAW BYTE-EQUAL** — 808
bytes identical including blockquote markers (md5 of normalized text
ce01b262 both sides; equality holds BEFORE normalization). This is stronger
than PE2's normalized-equality check and than the W12-r2 commit's own record.
The HEX3 S8.2 pointer annex: `grep HMENU3 HEX3_PROOF` is EMPTY — the pointer
has NOT been applied to HEX3_PROOF by anyone; the note only PROPOSES it
("proposed annex texts are §S8.1", "This note edits neither W12_PROOF nor
HEX3_PROOF"), so nothing is owed and nothing misdescribes. Verified: the
W12-side application is the ONLY applied copy in the corpus (grep over
lean/notes/openmath).

## CHARGE 5 — freeze integrity across all four eras (vein 5)

* **The note's complete git history is exactly four commits** (seal 64d3ff9
  08:40:17Z → verdict 625fa49 08:49:41Z → r1 3235e1b 09:30:39Z → r2 e1280be
  11:05:02Z); HEAD blob == r2 blob (md5 943c51e2…). Era md5s: seal
  1a1585dd…, verdict f8d449bc…, r1 d6fdf092…, r2 943c51e2….
* **Chronology brackets each pass into one era:** PE1 (09:17:50) between
  verdict and r1 → read the verdict text; PE2 (10:32:56) between r1 and r2
  → read the r1 text; PE3 (11:55:54) after r2 → read the r2 text (= HEAD).
* **Quote-level verification, per era:** PE1's four FINDING-1 quotes ("(arc
  0/2, PE1 adjudicated, PE2 owed)", "(r1 done, PE2 owed)", "(W-12 PE2 owed;
  HEX3 and this note's hostile arcs unbegun)") and its FINDING-2 quote
  ("integer coefficients (m carries 5, k/t carry ≥ 3, w/j/u/k′ carry ≥ 1)")
  all exist VERBATIM in the verdict-era text and only make sense there (the
  r1 text strikes them). PE2's quotes ("carry 3/2 in RAW coordinates — the
  two consulted windows contribute u + (u+1)/2", "counter 0/2, r1 owed
  [r1]") exist verbatim in the r1-era text. PE3's quotes (the [r2 m1]
  rescope bracket, the 16,384 = 2^{27−13} pin, the [r2 m2] fired-clause
  record, the W-11 2/2 bracket) exist verbatim in the r2 text.
* **No anachronisms:** the verdict-era text's only "[r1" occurrences are
  references to W-12's OWN [r1 F3] tag (the S2 taxonomy point), not HMENU3
  repair tags; "[r1, PE1 FINDING" does not occur there. The r1-era text's
  only "[r2" occurrences are references to W-12's [r2 G3] guard; "[r2 m1/m2"
  do not occur there. The seal text contains "VERDICT: PENDING" and no S10;
  all three never-measured-row preregistrations and the teeth counts are in
  the SEAL text (re-confirmed; PE2's charge 5 re-verified at the blob level).
* **Runner/artifacts:** runner touched only at 64d3ff9 (md5 at HEAD ==
  65326f85c218087261f434f8b8cc8dda == seal); artifacts only at 625fa49
  (md5s at HEAD == the S10-displayed 7f754887…/daf077d0…). Both repair
  commits verified single-file diffs on the note alone (r1: 71+/15−;
  r2: 78+/20−) — "note-only" holds at `git show --stat` granularity.

## CHARGE 6 — WILDCARD: constructive HM3-2 + the first multi-lift (A0) probe, wild strata, never-oracled row

**Design.** The sealed ORACLE leg tested one representative per deep member
on four rows ((Zp,2,5/6/7),(Zp,3,5)). (A0) as consumed claims EVERY lift of
every menu member carries the family σ (S5.2: "Ore then assigns the SAME σ
to every O-lift"). Nobody in the arc had (i) oracled a row outside those
four, (ii) tested MULTIPLE lifts per member, or (iii) used LEMMA HM3-2
CONSTRUCTIVELY (as a member factory rather than a read-side correspondence).
This leg does all three at (Zp,3,6) — wild p = 3, deep members behind a
refinement step.

**Leg A (deep, constructive).** Built the DEEP-RAM3(m=1,h) fibers at
(Zp,3,6) from raw material: reduced RAM3(h) members at window 3 (locus
v(A₀) = h exact, v(A₁) ≥ ⌈2h/3⌉, v(A₂) ≥ ⌈h/3⌉ — counts 486 (h=1), 54
(h=2) = (q−1)q^{3M−2h−2} on the nose), × letter z ∈ F₃ˣ, × q³ = 27 ghost
digits, mapped through σ₁^{-1} (B′ = (3A₂+81g₁+243g₂, 9A₁+243g₃, 27A₀))
then un-recentered by c = 3z (B = (B′₂−3c, 3c²−2cB′₂+B′₁,
−c³+c²B′₂−cB′₁+B′₀) mod 3⁶). Results: all constructed states DISTINCT
(injectivity), totals **26,244 (h=1) and 2,916 (h=2) == (q−1)q^{4m−1} ×
reduced counts == the COMMITTED (Zp,3,6) tallies for
(('ALPHA',1),('RAM3',4)) and (('ALPHA',1),('RAM3',5))** — the transport's
fiber structure (letters × ghosts × reduced member) reproduces the
committed key counts exactly on a row whose deep members were never
independently touched. PARI σ-leg: 200 sampled members per h, **3
independent random lifts each** (random digits at heights 6..13):
**1,200/1,200 σ = {(3,1)}** — wild totally-ramified cubics behind a
refinement, every lift. (Verifier-side instrument note: the naive
slope-denominator σ-read is INSUFFICIENT here — the raw deep members have
integer root valuation 1 with residual (u−z)³, so the classifier itself
needs a recentering recursion (a mini-OM); my first classifier draft
flagged all 600 h=1 reads ambiguous until upgraded. No note defect — a
warning to future oracle-leg authors: deep members are exactly the ones
whose σ is invisible to first-slope reads.)
**Leg B (depth-0 wild p = 3).** RAM3(h) members sampled from the S2.4 locus
at (Zp,3,6), h ∈ {1,2,4,5}: 960/960 multi-lift σ-reads = {(3,1)}; committed
depth-0 counts equal the law 2·3^{16−2h} for all four h.
**Leg C (depth-0 wild p = 2).** RAM2LIN(4,1) at (Zp,2,6): ALL 256 members
constructed from the locus (== the committed tally exactly), 150 sampled ×
3 lifts: **450/450 σ = {(2,1),(1,1)}**.

## CHARGE 7 — S10 verdict facts re-audited from the committed artifacts

All never-measured-row spot claims re-extracted from the committed JSON:
(Fqt,2,9) 187 keys / 150 decided / decided total 16,674,048 / deep 523,008 /
drain 103,168, spots 131,072 / 65,536 / 32,768 / 32,768 ✓; (Fqt,3,6) 39 keys
/ 30 decided / deep 95,580 / drain 80,109, spots 26,244 = 26,244 (the
FULL11SQ twin), 17,496, 2,916, 5,832 ✓; (Fqt,27,2) EXACTLY two keys,
('RAM3',1) = 18,954 + drain 729 ✓ (and 18,954 = 26·27² is the RAM3 law at
(27,2) by hand). Roster arithmetic: Σ states = 94,824,902 ✓, 18 ℤ_p + 23
𝔽_q[[t]] ✓, family checks sum to 183,387 ✓, ORACLE 9,956 = 9,952 σ + 4
member-count checks with 48+624+6,688+2,592 = 9,952 ✓.

## MACHINE LEG

* **Runner vs seal:** md5 65326f85c218087261f434f8b8cc8dda == sealed value;
  `git diff 64d3ff9 HEAD -- verification/openmath/hmenu3_checks.py` EMPTY.
  Artifacts at HEAD: output txt 7f754887…, results JSON daf077d0… == S10.
* **Fresh full run** (isolated `git archive` of seal 64d3ff9 into /tmp;
  single run): **GREEN, exit 0, 183,387 checks / 0 violations, 447.9 s**
  (committed 443.8 s; PE1 448.4, PE2 447.8, PE3 445.1) — PIN 7, MENU 1,031,
  DRAIN 82, AGG 707, XREAD 171,444, HEX3TIE 38, W12TIE 69, DBLTIE 23,
  ORACLE 9,956, RTAU 30; teeth 21/15/10/4 all exactly preregistered; 41/41
  rows. Results JSON == committed EX `elapsed_s` (python structural
  compare); output txt diff vs committed = the ONE timing line.

## REMARKS (verified non-findings)

1. **Supplier arc aging (HEX3).** HEX3 passPE2 landed at f60348b AFTER this
   note's r2 (NOT CLEAN — 0C + 1 GAP + 1 minor), so BOX-2/S9's "HEX3 …
   PE2 next" has aged — accurate when written, dated [r2 m2] bracket, the
   same genre PE2's REMARK 1 and PE3's charge 5 classified as non-findings.
   Fired-clause propagation checked by me: HEX3-PE2's gap is HEX3's OWN P-1
   never-measured census bookkeeping ((8,3) omitted from an 11-set that
   should be 12) — an instrument-disclosure item, not H-1..H-4/HEX3.A/u(q,N);
   its minor is the S8.2 ASIDE's N-linear-mass display (k = 1 correction
   term), which this note does not consume (S9's consumed list stops at
   HEX3.A/B/C + H-1..H-4; the aside is outside, and my ENGINE-L2/L3 legs
   re-derive every u(q,N)-adjacent identity symbolically anyway). Bonus:
   HEX3-PE2 itself re-verified "HM3-2 fires post-r1 H-2(i)'s proof-content
   verbatim (compatible; HMENU3 r2 fired-clause record accurate)" — the
   supplier's own hostile pass corroborates this note's fired-clause record.
   W-12: still no PE3 at my read time (last W12_PROOF touch = 99f1813);
   W-11: accepted 2/2, unchanged. The note's W-12/W-11 displays are CURRENT.
2. **The S_λ censuses are nowhere displayed in this note** (they live in
   W12 S2.4's table and are consumed silently through "the depth-0 W-12.A
   laws"). My engine had to re-derive them from the residual-pattern counts
   and pin the normalization against committed w12 values. Not a defect —
   the note consumes tier I by pointer, as its S9 declares — recorded so a
   future reader knows the tier-I laws' λ-split is supplier-side.
3. **Instrument caution for future σ oracles** (from CHARGE 6): deep
   members' σ is invisible to first-slope factor reads; any future
   independent σ leg must recurse (recenter at the repeated residual root)
   or it will flag spurious ambiguities exactly on the deep strata.

## SCORE AGAINST P-10

No falsifier fired on any leg: no MENU/AGG-equivalent discrepancy in the
symbolic route (so LEMMA HM3-4, every A_L/A^{(j)} aggregation, AND their
exhaustiveness against u(q,N) stand as polynomial identities), no
self-similarity violation at any committed (row, depth) pair, no σ anomaly
in 2,610 fresh multi-lift PARI reads (wild p = 2 and p = 3, deep and
depth-0, never-oracled row), no tooth anomaly, engine/series identities
hold symbolically.

## COUNTER

PE4: **0 critical / 0 gaps / 0 minor — CLEAN.** Second consecutive clean
pass: 2-clean acceptance counter = **2/2 — the (hMenu-3) note is ACCEPTED.**
Acceptance fold owed to the orchestrator (arc: composed → PE1 0C+1G+1m →
r1 → PE2 0C+0G+2m → r2 → PE3 CLEAN → PE4 CLEAN THIS).
