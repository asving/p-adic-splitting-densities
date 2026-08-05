# LIFTCORNER passPE2 — hostile verification report (fresh context, post-r1)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD**, i.e.
INCLUDING the r1 repair (commit b2dc120) that cured PE1's F1 CRITICAL by
replacing the single m-descent with the lexicographic (m, deg a) descent.
**Arc read:** PE1 report `LIFTCORNER_passPE1_report.md` (commit 30e570c,
1 CRITICAL + 3 gaps) and the r1 diff `git show b2dc120`.
**Machine legs:** (a) the SEALED runner `verification/openmath/liftcorner_checks.py`;
(b) the NEW post-hoc children generator
`verification/openmath/liftcorner_tailstab_children.py` +
`liftcorner_tailstab_children_table.txt`.
**Charge:** quote-and-classify, fix nothing; honesty defects graded (claims
stronger than evidence, stale machine quotes, un-superseded refuted text);
fences and honest boxes read as part of the statement. Special hostility toward
the repair itself, on the six charged questions (1)–(6) below.

**VERDICT: 0 CRITICAL ERRORS / 5 JUSTIFICATION GAPS.**

**F1 IS CURED.** The lexicographic repair is mathematically sound and I
re-derived every load-bearing piece of it independently: the 9 → 7 genre
mapping is total and disjoint (no genre falls through); row 7b's degree drop is
correct and its two ingredients (deg b_k < d₀ from S1; the q-child existence
condition deg(a b_{e₀−1}) ≥ d₀) are both used correctly, with no off-by-one at
deg a = 0 or deg b = 0; the deg a = 0 and d₀ = 1 emptiness claims are PROVED
(not merely measured) and both re-derivations check; the lex order well-founds
BOTH consumers, the IH is only ever invoked on strictly lex-smaller pairs, and
ρ(m, deg a) = m·d₀ + max(deg a, 0) really does strictly drop along every child
edge and hence bounds every root-to-leaf path. PE1's F2 and F4 are correctly
applied (F4's wording now matches the runner's asserts line-for-line, verified
against source). F3's rescope is self-consistent and the withdrawn
identification is gone from every consuming line.

**Both machine legs are clean.** The sealed runner re-runs bit-identically
(exit 0, 25,409/0, seal md5 `ccb4351c92573f5f962cae4ae952d8dd` intact,
0-byte diff since the seal commit). The new children table regenerates
BIT-IDENTICALLY, exit 0, and every headline figure re-derives from my own parse
of the regenerated output. **I also supplied the one assertion the generator is
missing** — that the enumerated children sum back to X — and it passes on all
752 nodes, which is the only way to rule out the "missing a child type by
construction" failure mode.

The five gaps are, in order: one **false displayed number that the note's own
committed table refutes** (the branching bound), one **honesty defect**
(PE1 credited with verifying bounds it never saw, and the r1 charge list again
points away from them), one **artifact-hygiene / decorrelation gap** on exactly
the charged completeness item, and two minor precision defects. None breaks the
chain; the r1 grade box's charge (1)–(2) does, this time, cover the region where
two of the five landed.

---

## 1. Machine leg (mandatory, two parts) — BOTH RUN, BOTH CLEAN

### (a) The SEALED runner — bit-identical, seal intact

```
$ md5sum verification/openmath/liftcorner_checks.py
ccb4351c92573f5f962cae4ae952d8dd            <- = the note's S3 claim
$ git log --oneline -1 -- verification/openmath/liftcorner_checks.py
dafc0b5 LIFT-CORNER (NR-1) SEAL commit 1 ...  <- ONLY the seal commit ever touched it
$ git diff dafc0b5 HEAD -- verification/openmath/liftcorner_checks.py | wc -l
0                                            <- byte-untouched through r1
$ python3 liftcorner_checks.py ; echo EXIT=$?
EXIT=0 ... VERDICT: ALL GREEN ... TOTAL checks 25409  elapsed 4.3s
```

Family table vs the committed `liftcorner_checks_output.txt`: **identical
line-for-line modulo the `elapsed`/per-block timestamp fields only** (diff of
the two outputs with timing normalised is empty). GATE 0/56 · AV 0/656 ·
TLAW 0/4176 · PV 0/4176 · INT 0/4176 · LOC 0/0 · CHI 0/4176 · COV 0/0 ·
WRONGLET 0/3816 · TRS 0/4176 · ENGGATE 0/1 · CERT 0 · wrong-letter fires 1576 ·
gate-passed 56 · min d1-pairs 6 · min teeth 6. **Every S3 figure in the note
matches. No stale machine quotes in S3.** The r1 header's claim that the sealed
runner is byte-untouched and the md5 unchanged is TRUE.

### (b) The NEW children generator — regenerates bit-identically; all figures re-derived independently

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe2_regen_table.txt ; echo EXIT=$?
EXIT=0
$ diff /tmp/pe2_regen_table.txt liftcorner_tailstab_children_table.txt
(empty)  -> REGENERATED TABLE BIT-IDENTICAL TO COMMITTED
$ git status --short
(empty)  -> nothing edited; I redirected the table so the committed file was never touched
```

Headline figures, **re-derived by my own parser of §2 of the regenerated file**
(not read off the script's own summary lines):

| note's figure | my independent re-derivation | verdict |
|---|---|---|
| 29 towers, p ∈ {2,3,5}, d₀ ∈ {1,2,3}, e₀ ∈ {2,…,6}, 4 lift genres, CTR = PE1's instance | roster: 29 rows; p ∈ [2,3,5]; d₀ ∈ [1,2,3]; e₀ ∈ [2,3,4,5,6]; genres {dense, midonly, pure, tailonly}; CTR = ℤ₂, d₀=2, e₀=2, h₀=1, Φ₀=x²+x+1, b₀=2, b₁=2x | MATCH |
| 752 (a, m, j) probes | Σ_inst (d₀+1) = 94 coefficient probes × 4 m-values × 2 j-values = **752** (hand-derived from the roster, independent of §5) | MATCH |
| 2,668 child rows | parsed **2,668** rows; genre counts sum 200+376+208+316+376+220+328+268+376 = 2,668 | MATCH |
| 9 machine genres | **9** normalized labels | MATCH |
| 220 m-preservers, ALL genre 7b, ALL dropping deg a | **220**; all `mid[TOP=e0-1]-q`; all deg a′ ≤ deg a − 1; all deg a ≥ 1; all d₀ ≥ 2; min gain **+2** | MATCH |
| zero no-descent | NO-DESCENT rows **0**, m-RISE rows **0**, negative gains **0** | MATCH |
| `b0-main-r` the unique label with gain set exactly {0} | only label whose observed gain set is {0}; the other eight have min gain ≥ 1 | MATCH |
| observed gains agree with the seven rows' bounds | observed min gain per label vs the note's row bound, evaluated at the roster's minimal parameters (e₁ = h₀ = h₁ = 1, e₀ = 2): key **1** vs h₁ = 1 · b0-main-r **0** vs 0 · b0-main-q **1** vs e₁h₀ = 1 · b0-tail-r **2** vs e₁e₀ = 2 · b0-tail-q **3** vs e₁e₀+e₁h₀ = 3 · mid-r (both labels) **1** vs e₁ = 1 · mid-q (both labels) **2** vs e₁(h₀+1) = 2 | MATCH, and the bounds are attained (tight) |
| A6: 752 probes / 4,438 nonzero digits / min slack 0 | §5: probes 752, digits 4,438, min slack 0, all clean | MATCH |
| A1–A6 all PASS, exit 0, ALL GREEN | §7: 0 assertion failures, A1–A6 PASS, "ANY CHILD DROPPING NEITHER COORDINATE: NO" | MATCH |
| §6 chain "machine-printed … digit for digit" | §6 tree matches the note's S4.1 numeric chain child-for-child, ω-for-ω (8 nodes, 6 leaves, depth 2) | MATCH |

I also re-did the note's counter-instance arithmetic by hand and it is correct
throughout: Φ′ = x⁴+4x³+5x²+4x+3; γ₂ = 3; ω(X) = 2; the four first-pass
children with gains +1/0/+1/+2; the second expansion's three children with NO
mid q-child; and the independent tie
xΦ₀² = (x−2)Φ′ + (6x+2)Φ₀ + (−2x+4) — I re-divided both steps: digits at
(j,i) = (1,0), (0,1), (0,0) with w₀ = 0, 1, 1 and weights 3, 3, 2 against
ω(X) = 2, slacks 1, 1, 0, equality at (0,0) = row 2's gain-0 thread. All exact.

### (b′) GENERATOR AUDIT — the failure mode a green table cannot catch

The audit question: *does the script's child enumeration match the lemma's
child definition, or could it be missing a child type by construction?*

**Structural audit (source read).** `children()` implements exactly the note's
pass identity: the key term at (m−e₀, j+1) with coefficient a unchanged; the
b₀ branch **pre-split** into main (a·ĉ′π^{h₀}) and tail (a·t₀) as the note's
S4 split prescribes; the mid branches a·b_k for k = 1..e₀−1; and each level-0
coefficient a·b re-digited ONCE by `divmod_monic(·, Φ₀)` into an r-child at
Φ₀-exponent M = m−e₀+k and a q-child at M+1, zero digits skipped. That is
term-for-term the note's identity, and one re-digit suffices because
deg(a·b) ≤ 2d₀−2 < 2d₀ (so deg q < d₀ and no cascade is possible) — the note
states this bound and it is correct. `norm_genre` can emit exactly 9 labels
(key; b0-main-r/q; b0-tail-r/q; mid[TOP]-r/q; mid[k<e0−1]-r/q), so no genre can
be dropped at the labelling stage either.

**The hole, and my closing of it.** The committed script contains NO assertion
that the enumerated children reconstruct X. A6 does not help: it recomputes the
double development of X *directly* and never calls `children()`, so a missing
branch would leave every assertion green. I therefore wrote and ran the missing
reconciliation myself (`/tmp/pe2_recon.py`, importing the committed module
read-only):

```
RECONCILIATION sum(children) == X : nodes = 752   mismatches = 0
children violating deg a' < d0 or m' < 0 : 0
max children per node by e0: {2: 7, 3: 9, 4: 11, 5: 13, 6: 15}
```

i.e. Σ_children a′·Φ₀^{m′}·Φ′^{j′} = a·Φ₀^m·Φ′^j **exactly, on every one of
the 752 nodes**, and every child is genuinely of the lemma's shape
(deg a′ < d₀, m′ ≥ 0). So the enumeration is faithful and complete — but that
is now certified by MY leg, not by the committed artifact. See G5.

**Fenced coverage limits (disclosed, no finding).** The battery probes only
m ∈ {e₀, e₀+1, 2e₀, 2e₀+1} and does not recurse outside §6, so (LEDGER) is
machine-confirmed to recursion depth ≈ 2 only; ĉ′ is always of degree ≤ 1 and
t₀/b_k always sit at exactly their minimal w₀. None of these weakens the
census (whose genres are structural, not instance-dependent), and the note's
own fence — "The table is evidence for the case split, not a substitute for
(A)–(C): it is a finite battery, and the proof above is what carries the ∀" —
is accurate.

---

## 2. FINDINGS

### G1 — JUSTIFICATION GAP (false displayed number, REFUTED BY THE NOTE'S OWN TABLE): the (C)(ii) branching bound is wrong

Offending passage (S4.1 (C)(ii)):

> "The recursion tree is finitely branching — ≤ 2e₀+1 children per node
> (row 1, rows 2–5, and ≤ e₀−1 realizations each of rows 6 and 7) — and by (A)
> has no infinite path, hence is FINITE"

The parenthetical's own arithmetic gives 1 (row 1) + 4 (rows 2–5: b₀-main r,
b₀-main q, b₀-tail r, b₀-tail q) + (e₀−1) (row 6) + (e₀−1) (rows 7a+7b) =
**2e₀+3**, not 2e₀+1. The stated number is what you get by counting rows 2–5 as
two *branches* instead of four *digits* — an inconsistent count, since rows 6/7
are counted as digits.

**Machine refutation from the note's own committed table** (`A1`, e₀ = 2, so
the claim is "≤ 5"):

```
A1  2  2  2 x+1  1  2 | key         0 1 m-DROP    1 x+1
A1  2  2  2 x+1  1  2 | b0-main-r   0 1 m-DROP    0 -2x
A1  2  2  2 x+1  1  2 | b0-main-q   1 0 m-DROP    2 -2
A1  2  2  2 x+1  1  2 | b0-tail-r   0 1 m-DROP    4 -4x
A1  2  2  2 x+1  1  2 | b0-tail-q   1 0 m-DROP    6 -4
A1  2  2  2 x+1  1  2 | mid[1]-r    1 1 m-DROP    2 -2x
A1  2  2  2 x+1  1  2 | mid[1]-q    2 0 degA-DROP 4 -2      <- SEVEN children
```

and the violation is uniform across the battery (observed max children per node
vs the claimed bound): e₀=2: **7** vs 5 · e₀=3: **9** vs 7 · e₀=4: **11** vs 9 ·
e₀=5: **13** vs 11 · e₀=6: **15** vs 13 — i.e. the true maximum is exactly
2e₀+3 at every e₀ in the battery.

**Classification: JUSTIFICATION GAP, not CRITICAL.** The only property the
consumer uses is *finite* branching (for the König step and for the finiteness
of the dev-linearity sum), and 2e₀+3 is finite; the ρ depth bound, which is the
quantitative claim that actually matters, is independent of this count and is
CORRECT (see §3(4)). But it is a displayed number that is false, it sits inside
the note's own charged item (2) ("the lex-order finiteness argument ((C)(ii):
finite branching + the ρ depth bound)"), and it is contradicted by the artifact
the note commits alongside it — a green-table-doesn't-mean-green-prose miss.

### G2 — HONESTY DEFECT / JUSTIFICATION GAP: PE1 is credited with independently verifying the r1 per-digit ω-gains, which did not exist at PE1

Offending passage (S4.1, the `[r1, F1 — CRITICAL (PE1)]` box):

> "UNCHANGED in content and re-verified by PE1 independently: the base case,
> the one-pass identity, **all ω-gains (now displayed per digit, hence sharper
> on rows 3, 5, 7 than r0's per-branch lower bounds)**, the gain-0 census
> (row 2 only), CONTENT, dev-linearity, …"

The sentence is self-refuting: bounds that are "now displayed per digit, hence
sharper … than r0's per-branch lower bounds" are by construction NOT "unchanged
in content", and cannot have been "re-verified by PE1", since PE1 read the r0
table. PE1's actual scope, verbatim from its F1 repair observation:

> "all four ω-gain rows of the branch table (checked, using
> e₀·amin(k) ≥ (e₀−k)h₀+1 which I re-derived from gcd(e₀,h₀) = 1 …)"

— **four** rows of the r0 per-branch table. The r1 table displays **eight**
gain entries (rows 1, 2, 3, 4, 5, 6, 7a, 7b), of which the sharper per-digit
bounds on rows 3, 5, 7a, 7b are new at r1 and unread by any hostile pass. And
the r1 grade box's charge list does not name them either: (1) is census
COMPLETENESS + the row-7b degree drop, (2) is lex finiteness, (3) CONTENT,
(4) READ-EQ, (5) PROP, (6) COR 2's scope — the new gain bounds appear nowhere.
That is precisely the defect PE1 recorded against r0 ("the grade box's
self-charge list … does NOT name this step — the owed arc was pointed away from
the actual flaw"), recurring one round later on a different step.

**For the record (verifier's own check, not a fix):** I re-derived all eight
bounds and they are CORRECT — row 1 = exactly +h₁; row 2 = e₁e₀[w₀(r) − w₀(a) −
h₀] ≥ 0; row 3 ≥ e₁h₀; row 4 ≥ e₁e₀; row 5 ≥ e₁e₀+e₁h₀; row 6 ≥ e₁; rows 7a/7b
≥ e₁(h₀+1); with e₀·amin(k) ≥ (e₀−k)h₀+1 re-derived from gcd(e₀,h₀)=1
(e₀ | kh₀ ⟺ e₀ | k, impossible for 1 ≤ k < e₀). The battery's per-label minima
match these bounds at the roster's minimal (e₁, h₀, e₀). So the defect is
attribution and audit-pointing, not arithmetic.

### G3 — JUSTIFICATION GAP (machine-leg decorrelation on the charged item): the generator cannot certify census completeness, which is charged item (1)

Offending passage (S4.1 (A), and the machine-leg bracket):

> "**(A) THE CHILD CENSUS — seven genres** (this case list matches the genre
> list of the r1 examples-first table under the explicit 9 ↦ 7 label mapping
> displayed in the machine-leg bracket below …)"

> "The table is evidence for the case split, not a substitute for (A)–(C)"

The note's own charge (1) is "the S4.1 seven-genre child census's
COMPLETENESS — that the pass identity, after the b₀-split and the r/q redigit,
produces no branch outside rows 1–7". The examples-first table is offered as
the evidence the case list is "DERIVED FROM", but the table structurally cannot
speak to that: `children()` is a hand transcription of the same pass identity
the prose transcribes, and no assertion (A1–A6) checks the enumeration against
X. The two legs therefore share a single point of failure — the transcription —
which is the standing "extraction-corruption decorrelation" trap (a verbatim-
pinned second leg inherits the first leg's corruption). This is a gap in the
*evidence architecture*, not (as it turns out) in the mathematics: I supplied
the missing leg (Σ children == X, 0/752 mismatches, §1(b′)) and it is clean, and
I separately re-derived completeness from the algebra (Φ₀^{e₀} = Φ′ − Σ_{k<e₀}
b_kΦ₀^k gives exactly the key + b₀ + (e₀−1) mid terms; deg(a·b) ≤ 2d₀−2 forces
exactly two digits per branch and forbids a cascade). Cure: add the
reconciliation as assertion A7 so the committed artifact carries it.

### G4 — JUSTIFICATION GAP (minor, undisclosed non-identity): "gain(q-digit) = gain(r-digit) + e₁h₀" is not an identity

Offending passage (S4.1, *The ω-gains*):

> "gain(r-digit) = e₁[e₀(w₀(a′)−w₀(a)) + (M−m)h₀] ≥ e₁[e₀β − (e₀−k)h₀] by
> CONTENT, and gain(q-digit) = gain(r-digit) + e₁h₀."

For a·b = r + qΦ₀ the ultrametric only forces min(w₀(r), w₀(q)) = w₀(a·b); the
*other* digit may sit strictly higher. When w₀(q) > w₀(r) the actual difference
is e₁[e₀(w₀(q) − w₀(r)) + h₀] ≠ e₁h₀. (Witness for the arithmetic phenomenon:
over ℤ₂ with Φ₀ = x²+x+1, a·b = 4x²+2 gives q = 4, r = −4x−2, so w₀(q) = 2 >
1 = w₀(r) = w₀(a·b).) **No consequence for the bounds:** applying CONTENT to q
directly gives w₀(q) − w₀(a) ≥ β and hence
gain(q) ≥ e₁[e₀β − (e₀−k)h₀ + h₀], which is exactly the "ω-gain ≥" column
entry the note needs; the displayed identity is a shortcut that happens to
overstate. Empirically it held on **all 896** r/q branch pairs in the battery
(I checked gain(q) − gain(r) == e₁h₀ pairwise: 0 exceptions), so the fence is
soft — but as written it is an underived and generally false step.

### G5 — JUSTIFICATION GAP (minor, false "exactly"): the d₀ = 1 characterization is refuted by the note's own table

Offending passage (S4.1 (B)):

> "(ii) at d₀ = 1 NO branch ever produces a q-digit (deg(a·b) ≤ 0 < 1 = d₀),
> so the r0 single-m induction was in fact valid **exactly** on the flat corner
> d₀ = 1"

d₀ = 1 is *sufficient*, not a characterization. The r0 clause "every child has
m′ ≤ m−1" also holds on any instance whose top mid vanishes, and the note's own
table contains two such rows at d₀ = 2: `A12` (2, 2, 2, 1, pure) and `B14`
(2, 2, 5, 1, pure) have b_k = 0 for all k ≥ 1 and contribute **zero** m′ = m
children (grep of §4 for A12/B14: 0 hits). The consumed content — "which is why
no d₀ = 1 row could have exposed the defect, and why the counter-instance below
is at d₀ = 2" — is unaffected and correct; only the word "exactly" overstates.

---

## 3. The six charged questions — results

**(1) 7-row case list vs the 9 machine genres: mapping TOTAL and DISJOINT, no
genre falls through.** The note's mapping (S4.1 machine bracket) is
key→1, b0-main-r→2, b0-main-q→3, b0-tail-r→4, b0-tail-q→5,
{mid[k<e0−1]-r, mid[TOP=e0−1]-r}→6, mid[k<e0−1]-q→7a, mid[TOP=e0−1]-q→7b.
All 9 labels are hit, each by exactly one row; conversely `norm_genre` can emit
only those 9 (source-read), so nothing escapes in either direction. Row 6's
merge is legitimate: both mid r-digits satisfy the same bound m′ = m−e₀+k ≤ m−1
for 1 ≤ k ≤ e₀−1. Row 7a's range 1 ≤ k ≤ e₀−2 is empty at e₀ = 2, and so is
the label `mid[k<e0-1]-q` there — consistent, and the battery's e₀ ≥ 3 rows
realize it (268 instances), which is why all 9 labels appear. CONFIRMED.

**(2) Row 7b's degree drop: both ingredients used correctly, no off-by-one.**

> "Its q-digit is nonzero only if deg(a b_{e₀−1}) ≥ d₀, and then, using only
> deg b_k < d₀ (S1), deg a′ = deg q = deg(a b_{e₀−1}) − d₀ ≤ deg a + (d₀−1) −
> d₀ = deg a − 1."

Both ingredients check. (i) *Existence condition.* Division by the monic Φ₀ of
degree d₀ gives q ≠ 0 iff deg(a b) ≥ d₀, and then deg q = deg(a b) − d₀
exactly — correct, monicity is what makes it an equality. (ii) *deg b_{e₀−1} ≤
d₀ − 1* is S1's `deg b_k < d₀`, used only as an upper bound. **deg a = 0 edge:**
deg(a b) ≤ 0 + (d₀−1) < d₀, so q = 0 and the row is EMPTY — the conclusion
deg a′ ≤ deg a − 1 = −1 is never asserted at a nonexistent child, so no
off-by-one. **deg b = 0 edge:** deg(a b) = deg a ≤ d₀−1 < d₀, again empty, again
no assertion. **a or b zero:** deg = −∞, no child, and the note explicitly binds
deg 0 := −∞ and "a zero coefficient contributes no digit and generates no
child". The chain is sound at every boundary. Machine corroboration: all 220
row-7b children have deg a′ = deg a − 1 exactly. CONFIRMED.

**(3) The deg a = 0 and d₀ = 1 emptiness: PROVED, not merely measured — and
the proofs re-derive.** (B) gives arguments, not measurements: at deg a = 0,
deg(a b_{e₀−1}) ≤ 0 + (d₀−1) < d₀ kills the q-digit, so every child drops m
(the four/five other genres all have m′ ≤ m−1 by e₀ ≥ 2 and k ≤ e₀−1); at
d₀ = 1, deg a = 0 forces deg(a·b) ≤ 0 < 1 = d₀ for EVERY branch factor b, so no
branch has a q-digit at all. Both re-derived and correct. They are separately
*measured* as A3/A4 (0 violations), and the note labels the table "evidence for
the case split, not a substitute" — so the proved/measured distinction is
correctly fenced. The one overstatement is the word "exactly" in the d₀ = 1
sentence (finding G5). CONFIRMED (modulo G5).

**(4) Both consumers: the lex order DOES well-found them; ρ really bounds the
recursion; the IH is only invoked on lex-smaller pairs.**
*Order.* ℕ × ({−∞} ∪ {0,…,d₀−1}) lex: ℕ is well-ordered, the second factor is
finite hence well-ordered, and the lex product of two well-orders is a
well-order — the note's "Lex products of well-orders are well-founded, which is
all the induction uses" is exactly right, and no separate second-coordinate base
is needed (as (B) says).
*IH legitimacy.* Rows 1–5 give m′ ≤ m−1 (rows 1/2/4 give m−e₀ ≤ m−2, rows 3/5
give m−e₀+1 ≤ m−1, both using e₀ ≥ 2 = the S4 setting); row 6 gives
m−e₀+k ≤ m−1 from k ≤ e₀−1; row 7a gives m−e₀+k+1 ≤ m−1 from k ≤ e₀−2; row 7b
is m′ = m with deg a′ ≤ deg a − 1. So every child is strictly lex-below, and
the IH is never invoked elsewhere. The j-uniformity is handled correctly: the
induction is on (m, deg a) with "uniformly in j" quantified inside, which is
what row 1's j ↦ j+1 requires. Children stay in the shape (deg a′ < d₀ from the
redigit; m′ ≥ 0 since m ≥ e₀) — machine-confirmed, 0 violations over 752 nodes.
*ρ.* ρ(m, deg a) := m·d₀ + max(deg a, 0) is a non-negative integer and strictly
drops on every edge: an m-drop of ≥ 1 costs ≥ d₀ while the second coordinate can
restore at most (d₀−1) − 0 = d₀−1, net ≤ −1; an m-preserving edge is row 7b,
whose child exists so a′ ≠ 0, so max(deg a′,0) = deg a′ ≤ deg a − 1 =
max(deg a,0) − 1, net ≤ −1. Hence every root-to-leaf path has length
≤ ρ(root) = m·d₀ + max(deg a,0) ≤ m·d₀ + d₀ − 1, the note's bound; and the
counter-instance's depth-2 tree sits inside 2·2+2−1 = 5, as claimed.
*Finiteness.* Finitely branching + no infinite path ⟹ finite (König) is correct,
and the note's r0 ⌈m/e₀⌉ bound is properly re-scoped to the ω-equality thread
(row 2 only, which drops m by exactly e₀) — that re-scoping is sound.
CONFIRMED, with the branching *count* wrong (G1) but its consumed property
(finiteness) intact.

**(5) F3 rescope: self-consistent, and the withdrawn identification is gone
from every consuming line.** COR 2's header is marked "(RESCOPED at r1)"; its
body claims only the displayed identity c_base = c′·ξ^{D₁} on the S1 orbit and
closes "Nothing beyond the displayed identity on the harness orbit is claimed";
the F3 box withdraws the r0 sentence verbatim and lists the two owed items
((a) orbit-membership of the transported CLASSIFIER key, needing GMN
normalization + W2-C3(ii); (b) the non-display battery legs, K12 above all),
matching PE1's F3 (a)/(b) exactly. I grepped every remaining occurrence of
W2-OPEN-1 / "RESTRICTED" / "base junction" in the note: line 59 (a source cite),
the r1 header disposition, the F3 box, and grade-box item (6) — all disclosures,
no consumer. The two nearby survivals are weaker and defensible: COR 2's "the
corner-degenerate FORM that W-2 clause 3's value-layer transport predicts" and
S3's "W-2 clause 3's prediction degenerate at the corner" both rest on S1's
displayed derivation of the corner degeneration (z₁ ↦ z₁′, the re-coordination
vacuous at g₀ = 1), not on any equivalence with W2-OPEN-1. Internal consistency:
COR 2's scope is the same set as the THEOREM's and COR 1's (S1's orbit = all
lawful monic lifts of degree e₀d₀ — I re-derived that the parametrization is
complete: a monic degree-e₀d₀ polynomial's Φ₀-adic development has top digit 1),
so the rescoping touches only the W2-OPEN-1 tie and does not silently shrink
COR 1. S5's "covariantly for the full Φ₁-orbit by the χ-law" consumes COR 2's
displayed identity, not the withdrawn identification — clean. The term "harness
monic-lift orbit" is never defined in-note (corpus jargon), but its referent is
the explicitly displayed S1 orbit, so it is unambiguous here. CONFIRMED.

**(6) PE1's F2 and F4: both actually applied.**
*F2* — the b₀-split is now bound in-note at S4, BEFORE its first load-bearing
use in the S4.1 table and S4.2:
`b₀ = ĉ′·π^{h₀} + t₀, deg ĉ′ < d₀, res(ĉ′) = c′ ≠ 0 (so w₀(ĉ′) = 0), deg t₀ <
d₀, w₀(t₀) ≥ h₀ + 1`, with wave-18 S1 cited inline and an existence/uniqueness
derivation. I checked that derivation: w₀(b₀) = h₀ makes b₀/π^{h₀} ∈ O[x] of
w₀ = 0 and degree < d₀; residues of degree-<d₀ polynomials inject into K₀, so
b₀/π^{h₀} − ĉ′ ≡ 0 mod π and w₀(t₀) ≥ h₀+1. Correct. APPLIED.
*F4* — S2 disclosure (c) now states exactly what the runner asserts, and I
verified both quotes against source: `liftcorner_checks.py:52`
`assert [tuple(c) for c in T.psi1] == psi1_base` (full ψ₁-byte carryover) and
`:179` `assert C.K2["one"] == C0.K2["one"]   # shared representation` (a
single-element smoke check, exactly as the note now says, with the r0 wording
quoted and disowned). The modulus-independence relocation also checks:
`mk_field_ext` is `grb_order2_check.py:333`, its reduction loop is verbatim
`for k in range(len(out)-1, g-1, -1)` at line 345, and at g = 1 the multiply
allocates `out = [K["zero"]]` so the range is `range(0, 0, -1)` = empty —
products never touch the reducer. APPLIED, accurately.

---

## 4. Verified perimeter (checked at r1, no findings)

- **Statement fence — checked, holds.** The note claims "statement
  byte-unchanged". I ran the r1 diff through a filter for the statement block
  and **no removed (`-`) line touches it**: not the X-shape
  ("For X = a·Φ₀^m·Φ′^j"), not `ω(X) := e₁(e₀·w₀(a) + m·h₀) + j·γ₂`, not the
  "(LEDGER) every nonzero digit obeys …" display, not the "Hence w₂(X) ≥ ω(X)"
  tie. Every removed line carrying `(LEDGER)`/`ω(X)` comes from the r0 PROOF
  body (e.g. "the ω(X)-thread", "the ultrametric close (LEDGER)"). So the r1
  edits are confined to the proof body, the (B)/(C) additions, the machine
  bracket, the F1/F2/F3/F4 boxes, and the status line. No accepted text, sealed
  falsifier, or wave-18 artifact is touched; no Lean change; the sealed runner
  is byte-untouched. The note's FENCES paragraph holds in the repo state.
- **Base case + one-pass identity.** m < e₀: deg(aΦ₀^m) ≤ (d₀−1)+(e₀−1)d₀ =
  e₀d₀−1 < deg Φ′, so dev uniqueness gives the single digit a at (i,j) = (m,j)
  with (LEDGER) at equality — re-checked. The pass identity
  X = aΦ₀^{m−e₀}Φ′^{j+1} − ab₀Φ₀^{m−e₀}Φ′^j − Σ_{k≥1}ab_kΦ₀^{m−e₀+k}Φ′^j is
  algebraically exact — re-derived, and machine-reconciled (§1(b′)).
- **(C)(i)'s close.** dev-linearity is genuinely additive here (digits of
  degree < deg Φ′ are unique, so the Φ′-development of a sum is the digit-wise
  sum — "polynomial devs carry no carries" is correct, and the same for the
  inner Φ₀-development); combined with gains ≥ 0 (so ω(child) ≥ ω(X)) and the
  ultrametric on colliding slots, (LEDGER) for X follows. Sound.
- **CONTENT sub-lemma; the (LEDGER) ⟹ w₂(X) ≥ ω(X) tie and the read-kill
  close; READ-EQ; the THEOREM; COR 1; PROP.** Unchanged at r1 and verified by
  PE1 under assume-the-conclusion; re-read here for consistency with the
  repaired TAIL-STAB (whose statement is byte-identical, so READ-EQ's
  consumption "by TAIL-STAB every digit they generate stays > Γ" is unaffected).
  No new finding.
- **Superseded text.** The r0 status sentence ("…(TAIL-STAB) is CLOSED…;
  wave-18's price sheet is settled in full") is quoted inside its own
  supersession and corrected to "settled MODULO this note's own arc, not 'in
  full'"; the r0 strict-descent clause survives only inside the F1 box that
  refutes it. No un-superseded refuted text remains.
- **Grade language.** "ATTEMPT 0/2 — r1 is a REPAIR round, not a pass",
  the W-2 consumption cap, "the r1 argument itself has NEVER been hostile-read",
  and the header's disclosure that the children table was written AFTER the
  refutation ("evidence for a repair, not a prediction") are all accurate and
  correctly placed. The r1 charge list DOES name the region where G1 landed
  (item 2) — an improvement over r0, whose list pointed away from F1 entirely.

## 5. Bottom line

The repair holds. F1 is cured by a lex descent that is well-founded, whose
one m-preserving genre genuinely drops the second coordinate, whose base
strata are proved empty rather than measured empty, and whose depth function
ρ really does bound the recursion. The census is complete — and I closed the
one hole in the evidence (Σ children == X) myself rather than accepting the
green table for it. What is left is one false displayed count that the note's
own artifact refutes (G1), one misattribution of PE1's verification scope
paired with a charge list that again omits the new material (G2), an evidence-
architecture gap on the charged completeness item (G3), and two minor precision
defects (G4, G5). Nothing here breaks the chain: "(TAIL-STAB) PROVED at attempt
grade, argument unaudited" is, after this pass, a supported description of the
r1 text — with the five items above owed.

— passPE2, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-05).
Machine legs: sealed runner exit 0, 25,409/0, bit-identical, seal md5 intact;
children generator exit 0, table bit-identical, all headline figures
independently re-derived, plus a verifier-supplied reconciliation leg
(0/752 mismatches). Nothing in the repo was edited.
