# W12 passPE2 report — hostile verification pass 2 (fresh context) of W12_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD = post-r1
(repair ba0d1a4, all six PE1 findings) + the dated HEX3 annex (8e535d2).
Read first: the PE1 report (2b47711) and the full r1 diff. This pass fixes
nothing; it quotes and classifies. Charge-designated veins: (1) the r1
edits themselves (corrected W-12.A display vs S2's proof AND the committed
JSON at ≥ 3 multi-branch mixed-m_i shapes PE1 did not check; the new H-e
member; the F3 e·d degree claim; the F4 warrant swap); (2) the HEX3-annex
interaction, headlined by the (A2)-needs-σ-vs-conv check; (3) one S3/S5
proof detail no pass has re-derived (chosen: S3.3); machine leg + fresh
spot-route.

**VERDICT: NOT CLEAN — 0 CRITICAL + 3 JUSTIFICATION GAPS + 2 minor.
THE HEADLINE CHECK IS CLEAN: W-12.D's (A2) does NOT get stranded on the
σ-vs-conv seam — HEX3.B's stated conclusion itself carries the σ-side
transfer (q^N ≤ U₃^σ ≤ U₃^conv ≤ N·q^{2N−1}, "(A2)'s σ-undecided part
vanishes"), the inequality direction is sound, and no W-12 surface
post-annex claims W-12.D fires at n = 3 (HEX3-BOX-4 says so explicitly;
the annex keeps (hMenu-3) + the σ-law bracket open). The gaps found are:
the r1 F4 warrant is still incomplete (the a ≡ b (mod p) sub-genre of
disc = 0 mixed cubics is TRP-read, outside W12-L1's fence); the
(hExhaust-3) gloss undercounts (A2)'s n = 3 residue by the transported
DBL SPLIT-TAIL boundary leg; and r1 m1's integrality justification
asserts a false implication (true conclusion, wrong lemma). Machine leg:
runner md5-identical to seal f669cb0, re-run exit 0 GREEN 3,232,506/0,
teeth 23/23/8/1273, every count == §S10, artifacts content-identical
ex-timing (committed bytes restored, md5s re-verified). Fresh route: two
rows PE1 did not touch ((Fqt,3,3), (Zp,5,2)), own arithmetic end to end,
pointwise identical to the committed JSON. Counter: 0/2 (this pass is not
clean); r2 owed on the findings below — all one-to-two-sentence repairs.**

---

## 0. THE HEADLINE CHECK (charge-designated single most important item):
## W-12.D's (A2) vs HEX3.B's exact conclusion — CLEAN

**W-12.D (A2) as stated (S1):** "r(N)/q^{nN} → 0, where r(N) := q^{nN} −
Σ_{F, x visible at N} count(F, x) — everything not in a visible core
family: the σ-undecided residue AND any window-boundary (tail) families."

**HEX3.B as stated (HEX3_PROOF_2026-08-08.md lines 118–130):**
"u(q, N) ≤ q^{2N−2}·(1 + N/(2(q+1))) ≤ N·q^{2N−2}, hence q^N ≤ U₃^σ(q,N)
≤ U₃^conv(q,N) ≤ N·q^{2N−1}, and undecided(3,q,N)/q^{3N} ≤ (1+N)·q^{−N}
→ 0, i.e. the n = 3 drainage hypothesis (A2)'s σ-undecided part vanishes
… (The full (A2) at n = 3 also needs the menu (A1) to absorb the decided
mass — that is (hMenu-3) = W12-BOX-2, untouched here; see S6.)"

**Adjudication.** The worry (A2-needs-σ, HEX3-gives-conv) dissolves in
the sound direction: the conservative reader's DECIDED exits are
separable-residual reads on fully in-window data (every consumed height
< N), which is exactly the S2.3 mechanism, so conv-decided ⟹ σ-decided,
hence σ-undecided ⊆ conv-undecided, U₃^σ ≤ U₃^conv — and this inequality
is INSIDE HEX3.B's display, not an annex afterthought (it is also the
pre-annex W-12 BOX-3 sentence "its measured U₃^TRP is an UPPER count for
the σ-convention residue"). The conv bound is moreover the RIGHT object
for (A2): TRP members that are σ-decided only by tail certification
(hence in no (A1)-admissible family) are conv-UNDECIDED by construction,
so the same N·q^{2N−1} bound drains them through (A2) exactly as
SPLIT-TAIL drains at n = 2. Independent re-derivations this pass: (a)
HEX3.A's law reproduces the committed w12 U₃ column at ALL 23 rows with
zero free parameters (my own transcription, /tmp/w12_pe2); (b) the
N·q^{2N−1} bound re-verified on all 23 rows; (c) S5.3's bound chain
re-derived (R(M) ≤ q^{M−1}(M+1)/2 ⟺ 2q + (M−1)(q−1) ≤ q(M+1) ⟺ M ≥ 1 ✓;
geometric sum in q^{−2k} ✓). **Overstatement sweep: NEGATIVE.** Every
"fires unconditionally" in the note is n = 2 (lines 48, 266, 774, 1142);
the annex wrapper keeps (hMenu-3) and the σ-law open; HEX3-BOX-4:
"No claim that W-12.D fires at n = 3 yet." The post-annex conditionality
reads exactly (hMenu-3) + [σ-bracket open at HEX3-BOX-1] — correct,
modulo FINDING 2's DBL-tail display leg. Annex faithfulness: the
verbatim block (note lines 1292–1303) is byte-identical to HEX3 §S8.1
lines 516–527 (md5 1345d5eff57114c00c98fb2d600a3676 both sides — the
commit-message pin verified).

---

## 1. FINDINGS

### FINDING 1 — JUSTIFICATION GAP (the r1 F4 repair's mixed-genre cover cite is still incomplete)

**Quote (S7, W12-ORACLE bullet, r1 text):**

> a monic cubic over ℤ with disc = 0 is (x−a)²(x−b) with a ≠ b — covered
> by W-11's square-block case through W12-L1(c) — or the exact cube
> (x−a)³, which NEITHER originally-cited lemma covers

**Classification: JUSTIFICATION GAP** (machine-bracket warrant; the
operational check is unaffected — the battery's 41,923 oracle checks
include these members and scored 0 disc-0-decided). The r1 repair fixed
the cube genre but taxonomizes by EXACT factorization while its coverage
cites act by LEVEL-0 READ: the sub-genre (x−a)²(x−b) with a ≠ b but
**a ≡ b (mod p)** has level-0 pattern (x−ā)³ — a TRP read — and W12-L1's
own fence is "Fix the level-0 pattern f̄ = (x−c̄)²(x−d̄), c̄ ≠ d̄"
(note line 578), so "covered by W-11's square-block case through
W12-L1(c)" structurally cannot reach it (the S2.1 Hensel split into
quadratic × linear branches does not even exist for it). The sub-genre is
REAL and abundant in the committed battery: my census of exact-disc-0
integer representatives on the five Z_p oracle rows gives (p,N) = (2,4):
14 DBL-read / **12 TRP-read** / 3 cubes (e.g. x³ + 14x² = x²(x + 14),
a = 0, b = −14 ≡ 0 mod 2); (2,3): 6/5/2; (3,2): 11/2/2; (3,3): 35/14/3;
(5,2): 39/6/3. What covers the TRP-read sub-genre is the SAME argument
the r1 text supplies for the cube — the conservative convention: the TRP
reader follows the double cluster (the residual is (z+ᾱ)²(z+β̄) once the
digits of a and b separate, refining forever on the exact-square block),
never reaches an all-separable state, and terminates only at
v(b₀) ≥ N ⟹ UNDECIDED. *Repair shape:* extend the r1 sentence's
taxonomy: "… with a ≠ b — DBL-read when ā ≠ b̄, covered by W-11's
square-block case through W12-L1(c); TRP-read when ā = b̄, covered by
the same conservative-convention argument as the cube — or the exact
cube …". (Inheritance note: PE1's own F4 text carried the same
two-genre taxonomy; the sub-genre is a PE2-new vein.)

### FINDING 2 — JUSTIFICATION GAP ((hExhaust-3)'s gloss undercounts (A2)'s n = 3 residue by the DBL boundary-tail leg)

**Quote (S3.4 conditionality paragraph):**

> (hExhaust-3) = (A2) at n = 3: the DBL part is proved (S3.1); MISSING:
> a vanishing U₃^TRP upper bound — W12-BOX-3.

and the S1 grade line's short form "(hExhaust-3): the U₃^TRP upper
bound, W12-BOX-3" (line 270).

**Classification: JUSTIFICATION GAP** (hypothesis-gloss display; the
reduction theorem itself is untouched). (A2)'s r(N) is defined to
include "any window-boundary (tail) families", and S3.4's own n = 2
instance routes SPLIT-TAIL through (A2) explicitly, warning that "an
(A1)-only reading would make the n = 2 instance-check incomplete". At
n = 3 the exact analogue exists on the DBL side: the transported
SPLIT-TAIL families (σ-DECIDED split-certified, per-w aggregated count
(q−1)²q^{2N−2} — verified against the committed JSON this pass, e.g.
(Zp,2,5) SPLIT-TAIL keys 256+128+128 = 512 = (q−1)²q^{2N−2}·⌊(N−1)/2⌋ —
i.e. dens would be (q−1)²q^{−N−2}, N-DEPENDENT, hence in NO
(A1)-admissible family). They are in r(N), they are NOT part of S3.1's
proved term (S3.1 proves the σ-UNDECIDED DBL mass only), and they are
NOT covered by the U₃^TRP bound (TRP stratum only) — so the displayed
"MISSING" set is an undercount by one leg. The leg is one line from
material already in the note (W12-L0's SPLIT-TAIL row × L1(c)'s q^{N−1}
fiber × q(q−1) patterns × M values of w: mass ⌊(N−1)/2⌋(q−1)²q^{2N−2},
/q^{3N} → 0), but it is nowhere displayed. Post-annex this is the ONLY
surviving undisplayed leg of (hExhaust-3), which makes the annex's
"DISCHARGED" read one line stronger than what is on the page. *Repair
shape:* one sentence in S3.4 (and/or the BOX-3 gloss): "the DBL
boundary-tail families route through (A2) exactly as at n = 2, with
vanishing mass ⌊(N−1)/2⌋(q−1)²q^{2N−2} from W12-L0 × L1(c)".

### FINDING 3 — JUSTIFICATION GAP (r1 m1's integrality clause asserts a false implication; true conclusion)

**Quote (S3.4 Step 1, r1 m1 text):**

> And the coefficients m_i are positive INTEGERS — this follows from
> ℓ_F being integer-valued on P_F with strictly positive coefficients —
> so each q^{−m_ib_i} is a bona fide element of ℚ(q).

**Classification: JUSTIFICATION GAP** (repair-introduced; zero blast
radius on the theorem). The implication is FALSE as stated:
ℓ(x) = (x+1)/2 on P = 1 + 2ℤ_{≥0} is integer-valued with strictly
positive coefficient, and m₁ = 1/2 is not an integer. What
integer-valuedness on a shifted product of APs actually gives is
m_i·b_i ∈ ℤ_{>0} (evaluate at x and x + b_ie_i) and
m₀ + Σm_ia_i = ℓ(base point) ∈ ℤ — which is EXACTLY what the Step-1
display needs (its ratio exponents are m_ib_i, its leading exponent is
ℓ(base)), so the conclusion "each factor ∈ ℚ(q)" stands via the correct
route. *Repair shape:* replace "the coefficients m_i are positive
INTEGERS" by "the products m_ib_i and the base value m₀ + Σm_ia_i are
positive integers", same derivation.

### MINOR 1 — H-e's classical cite under-prices the boxed statement

**Quote (S4.2 (H-e), r1):** "separable order-r residual ⟹ σ-decided
with (e, f) read off (the GMN order-r types theorem), which is exactly
(A0) well-posedness at composite stages."

The priced obligation is stated window-level ("σ-decided" is the note's
lift-quantified notion), and AS PRICED "= (A0) at composite stages" is
accurate. But the parenthetical attributes it to "the GMN order-r types
theorem", which is a statement about exact polynomials over O; the
window-level statement additionally needs the in-window pinning of the
consumed read data — at order 1 this is S2.3's explicit "All data the
read consumes sit at heights ≤ N−1" sentence, and at composite stages
that pinning is (H-a)/(H-b) territory. One clause ("GMN order-r types +
the (H-a)/(H-b) in-window determination") would make the cite exact.
Display-level only: the box lists all five members as jointly needed, so
no consumer can drop the companions.

### MINOR 2 — the annex wrapper's convention qualifier attaches to the wrong clause

**Quote (ANNEX wrapper, line ~1285):** "(hExhaust-3) — is DISCHARGED at
composition grade (…) FOR the disclosed conservative convention; on the
σ side the bracket … stands". Per the verbatim annex text directly below
(and HEX3.B), the EXACT LAW is conv-only while the vanishing DISCHARGE
is convention-free (it rides U₃^σ ≤ U₃^conv). The wrapper's "FOR the
… convention" invites reading the discharge as conv-scoped —
UNDER-statement, not overstatement (the verbatim block carries the
correct content), so display hygiene only.

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

**(1) The corrected W-12.A display vs S2's proof.** ALIGNED: the display
now equals S2.3's assembly verbatim — C₀ (level-0 census) ×
Π_{m_i=1} q^{d_i(N−1)} (S2.1's explicit simple-branch count, line
341–343) × Π_{m_i≥2} S_T·q^{d_iB_i} (S2.2). The corrected cell clause
matches S2.2's cell factorization × the simple-branch free digits. The
F1 repair record's dens_T re-derived: q^{d_i(N−1)}/q^{d_iN} = q^{−d_i}
per simple branch, q^{d_iB_i}/q^{d_im_iN} = q^{−d_i(Σ⌈P_i(j)⌉+L_i)} per
repeated branch — N-free ✓, restoring the shape-only clause. Both r1
verification instances re-checked: SEP-SPLIT C₀ = (q²−q)/2 (unordered
pair; the S2.1 q(q−1) is the ORDERED DBL pattern — consistent) ✓;
DBL RAM(1)@(Zp,2,5) = 2·16·1·2⁷ = 4096 == JSON ✓.

**(2) The corrected display vs the committed JSON at shapes PE1 did not
check — 12+ mixed-m_i keys on 6 rows, ALL EXACT.** Every depth-0 decided
DBL key (config {(x−c̄,2),(x−d̄,1)}: C₀ = q(q−1), simple fiber q^{N−1},
branch S_T·q^{B}, B = 2N − Σ⌈P⌉ − L) recomputed by hand and matched:
(Zp,3,3): SPLITEQ(1) = 6·9·1·3 = 162 ✓, INERTDEEP(1) = 6·9·3·3 = 486 ✓,
RAM(1) = 6·9·2·27 = 2916 ✓; (Zp,2,5): 2SIDED(1,2) = 2·16·1·16 = 512 ✓,
2SIDED(1,3) = 256 ✓; (Zp,2,6): 2SIDED(1,4) = 1024 ✓, 2SIDED(2,3) = 512
✓, RAM(5) = 2·32·1·2³ = 512 ✓, INERTDEEP(2) = 1024 ✓; (Zp,3,4):
RAM(1) = 6·27·2·3⁵ = 78732 ✓, RAM(3) = 2916 ✓, 2SIDED(1,2) = 5832 ✓,
SPLITEQ(1) = 4374 ✓, INERTDEEP(1) = 13122 ✓; (Fqt,3,4): ALL keys
identical to (Zp,3,4) ✓ (characteristic-blindness at the display level);
(Fqt,4,3): RAM(1) = 12·16·3·64 = 36864 ✓, SPLITEQ(1) = 2304 ✓,
INERTDEEP(1) = 4608 ✓; (Fqt,9,2): RAM(1) = 72·9·8·9 = 46656 ✓. SPLITEQ
absent at every q = 2 row (exact zero (q−2) = 0) ✓; 2SIDED absent at
N = 3 (2w < u ≤ N−1 infeasible) ✓. Sep-pattern cross-foot at (Zp,2,5):
LINQUAD 2·2¹² + CUBIC 2·2¹² + 3LIN 0 = 16384 = sep_total ✓.

**(3) F3 taxonomy fix: CORRECT.** Key degree at a repeated residual root
(f₁ = 1) on an e ≥ 2 side is e·f₁·d = e·d > d — the standard order-2 key
degree; matches S2.5's exhibit exactly (e = 2, d = 1 ⟹ "open a DEGREE-2
key"). The n = 3 harmlessness re-verified from the completeness tree:
every e ≥ 2 side of a 4-point (or DBL 3-point) polygon has g = 1, so no
repeated residual can sit on one; the runner's `assert e == 1` (line
~430 of the frozen runner) encodes it and never fired in the re-run. The
retained final clause ("repeated residual factors of degree ≥ 2 open
order-2 stages") is correct for every e.

**(4) F4 warrant swap:** cube genre argument re-derived and CONFIRMED
(recentered exact cube has residual (z+ū)³ at every state — char ≠ 3 by
the straight-line polygon, char 3 / p = 3 by Frobenius on z³ + ū with
the b₂, b₁ heights lifted off the hull — so the chain refines forever
and exits only at v(b₀) ≥ N ⟹ UNDECIDED; the r1 window example
3m ≥ N > 2m checks out); residual sub-genre gap = FINDING 1.

**(5) The chosen never-re-derived proof detail: S3.3 (general-n lower
bound) — SOUND.** Pattern (x−c̄)²·h̄ exists at every n ≥ 3, q ≥ 2
(irreducibles of degree n−2 ≥ 2 are non-linear; at n−2 = 1 a second
linear needs q ≥ 2) ✓; S2.1 branchwise decidedness makes {block
undecided} × {any h̄-lift} σ-undecided ✓; W-11's per-center drainage
q^{N−1} for the block × q^{(n−2)(N−1)} free digits of the simple branch
= q^{(n−1)(N−1)} ✓; n = 2 case is W-11's own law ✓; and the "conjectured
rate correct-in-order" remark checks: q^{(n−1)(N−1)}·q^{−(n−1)N} =
q^{−(n−1)} > 0 forces c_n(q) ≥ q^{−(n−1)} wherever the limit exists ✓.

**(6) m2 (P-6 scoping): VERIFIED from the artifacts.** Roster recomputed
from the committed JSON: 10 Zp × 13 Fqt rows share exactly NINE (q,N)
pairs ((2,3..7), (3,2..4), (5,2)); measured U₃ equal across kinds at all
nine; (4,2),(4,3),(8,2),(9,2) Fqt-only and (7,2) Zp-only — the r1 list
is exactly the shared nine. ✓

**(7) Annex numerics:** HEX3.A's law (my own transcription) reproduces
the committed U₃ column at ALL 23 rows, zero free parameters; the
HEX3.B bound N·q^{2N−1} holds at every row; the wrapper's "U₃^conv =
q·u exactly" and the sharpened bracket match HEX3.A/B verbatim.

## 3. MACHINE LEG

* **Seal:** `verification/openmath/w12_checks.py` md5
  7dc040d94fbbb1e8d20ac817b665d418 == `git show f669cb0:…` —
  byte-identical to the seal commit.
* **Re-run (single fresh run, this pass):** exit 0, **3,232,506 checks /
  0 violations, teeth 23/23/8/1273**, zero skips, 326.1 s. Every §S10
  family count reproduced exactly: PIN 5, LVL0 138, SHAPE 164, QRT 27,
  L0HIST 306, BLOCK 1,594,670, L1X 1,594,090, DRAIN3 1,183, ORACLE
  41,923; verdict GREEN.
* **Artifacts:** fresh JSON content-identical to committed ex-timing
  (programmatic strip-and-compare = True); committed bytes restored,
  md5s re-verified (0557b15fb08a6e6eb40bd2db7e62206b /
  05776c9e00071c5d7524abdfbe894442 == §S10's).

## 4. FRESH ROUTE (own arithmetic, no runner imports)

`/tmp/w12_pe2/fresh_route_pe2.py`, written from scratch this pass: own
ring classes (F₃[t]/t³ and ℤ/25), own hull, own finite-field root
finder, own recursive conservative TRP reader (whole-cubic recentering
per the disclosed convention), own Newton–Hensel split + own
W-11-rule block read for DBL. Rows chosen DISJOINT from PE1's fresh set:
cubic **(Fqt,3,3)** and **(Zp,5,2)**. Results — **pointwise identical to
the committed JSON on every field**: pattern censuses {1,9,8,6,3} resp.
{10,50,40,20,5}; sep/dbl/trp totals 13122/4374/2187 resp.
12500/2500/625; dbl_undecided 486 resp. 500 (== (q−1)q^{2N−1});
U₃ = 243 resp. 125 (== q·u(q,N)); species 27 resp. 25 (== q^N);
deep-decided 0/0; depth-0 keys RAM3(1) = 1458, RAM3(2) = 162,
LINRAM2(2,1) = 324 resp. RAM3(1) = 500 — each also re-derived from the
S2.4 closed forms by hand ((q−1)q^{3N−2h−2}·q etc.). 0 mismatches.

## 5. ARC / COUNTER

Arc: composed 0/2 → PE1 NOT CLEAN 1C+3G+2m (2b47711) → r1 (ba0d1a4) +
HEX3 annex (8e535d2) → **PE2 (this pass): NOT CLEAN — 0 CRITICAL +
3 JUSTIFICATION GAPS + 2 minor; counter stays 0/2; r2 owed.** All three
gaps are one-to-two-sentence display repairs (F4 sub-genre clause,
S3.4 DBL-tail routing sentence, m1 integrality clause); neither theorem
statement nor any proved chain is touched; the headline annex
interaction is clean and the machine + fresh legs are arc facts for the
record (seal intact, battery GREEN and reproducible twice, instance
layer independently confirmed on new rows).

— passPE2 verifier, fresh context, 2026-08-08.
