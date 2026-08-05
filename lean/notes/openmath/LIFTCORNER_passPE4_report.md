# LIFTCORNER passPE4 — hostile verification report (fresh context, post-r3; ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD**, i.e. after
repair rounds **r1** (b2dc120), **r2** (a3112dc generator + e5b3faf note) and
**r3** (feedaab, note-level only).
**Arc read in full before the note:** `LIFTCORNER_passPE1_report.md` (30e570c,
1 CRITICAL + 3 gaps), `LIFTCORNER_passPE2_report.md` (3367f3c, 0C + 5G),
`LIFTCORNER_passPE3_report.md` (39ea0db, 0C + 5G — the arc's first acceptance
attempt), and the three repair diffs.
**Cross-note read:** `ILNRES_2026-08-08.md` (the NR-1 record + S5.1 spec),
`ITERLAWN_PROOF_2026-08-08.md` S0.1 + the S9 dependency-sweep table,
`ITERLAWLIFT_CORNER_2026-08-08.md` S0/S1 (wave 18), `ITERLAW_2026-08-08.md` S6.3.
**Machine legs:** (a) sealed runner `verification/openmath/liftcorner_checks.py`;
(b) children generator `liftcorner_tailstab_children.py` + its committed table;
(c) independent exact-arithmetic re-verification of r3's F-B substitute witness.
**Charge:** quote-and-classify, fix nothing; honesty defects graded; fences and
boxes read as part of the statement. As the fourth hostile reader I was directed
at the veins the first three left unmined: **S1**'s definitions and the r1
b₀-split notation; **S4.2 READ-EQ + S4.3 THEOREM** end-to-end with a hand
re-derivation of the display for one orbit member; **COR 1 + the PROP rider**
(including PROP's rung-≥2 census clause); **S5** as the note's summary of record;
the **[r1]/[r2]/[r3] bracket system** as a system; and the **ILNRES NR-1
interplay**.

**VERDICT: 0 CRITICAL ERRORS / 6 JUSTIFICATION GAPS. NOT A CLEAN PASS —
the acceptance counter stays 0/2 and no acceptance slot opens.**

The mathematics held everywhere I pushed on it, including two things I
re-derived from scratch and one I re-derived by hand end to end: the whole
(TAIL-STAB) child census and its ω-gains; READ-EQ's δ₁ = 1 one-pass comparison
(both towers, digit by digit); the counter-instance's two passes and its
independent double-development tie, re-multiplied exactly; and the χ-ratio
algebra of COR 2 on a concrete orbit member over ℤ₂ with K₀ = 𝔽₄. Both machine
legs reproduce: the sealed runner is byte-untouched at md5
`ccb4351c92573f5f962cae4ae952d8dd` with a 0-byte diff vs the seal dafc0b5,
exits 0 at 25,409 checks / 0 violations; the children generator regenerates its
committed table **byte-identically** with A7's four legs PASS (752 nodes /
5,336 children / 0/0/0/0). r3's F-B substitute witness verifies in my own exact
integer arithmetic.

**The most consequential finding is F4-1, and it is the third recurrence of one
pattern.** r3's F-A repair — the round's own "substantive one" — corrected r1
for promoting a tautological machine assert, and then promoted the *other*
assert of the same pair as "the only substantive one … the half that can
actually fire". That claim is false: `C.K2["one"]` is a structural constant
fixed by (d₀, g₀, g₁) alone, independent of the residue c′ and even of ψ₁'s
values, so assert (ii) is exactly as incapable of firing as assert (i). I
verified this from source **and** empirically on both twist draws of the note's
own d₀ = 2 roster row. The note now applies an asymmetric standard: it traces
(i)'s mutation graph to prove it cannot fail, and stops at "compares two
distinct objects" for (ii) — where the same trace gives the same verdict.

Five more gaps, all in the evidence-description / bookkeeping layer: an r1
claim that r3's own F-A refutes but left standing at a second site (F4-2); an
r3 correction that misassigns its own defect's provenance to r2 when the source
report carried the overstatement three times (F4-3); PROP's rung-≥2 census cite
pointing at two tables that do not contain it, while the cited source's own
erratum records a consumption site PROP does not mention (F4-4); the `c′`
symbol collision inside the unit's headline identity (F4-5, PE3-declined,
numbered here); and the "NR-1 leaves the residual list" claim against NR-1 as
actually recorded in ILNRES (F4-6). **None breaks the chain. None touches the
(TAIL-STAB) proof or the S3 measurement.**

---

## 1. Machine legs (mandatory, three parts) — ALL RUN, ALL REPRODUCE

### (a) The SEALED runner — exit 0, seal intact, 0-byte diff, every counted figure matches

```
$ md5sum verification/openmath/liftcorner_checks.py
ccb4351c92573f5f962cae4ae952d8dd        <- = the note's claim (header + S3)
$ git diff dafc0b5 HEAD -- verification/openmath/liftcorner_checks.py | wc -c
0                                       <- 0 bytes, as the [r3] bracket claims
$ python3 liftcorner_checks.py ; echo EXIT=$?
... VERDICT: ALL GREEN ... TOTAL checks 25409  elapsed 4.3s ... EXIT=0
```

My family table: GATE 0/56 · AV 0/656 · TLAW 0/4176 · PV 0/4176 · INT 0/4176 ·
**LOC 0/0** · CHI 0/4176 · **COV 0/0** · WRONGLET 0/3816 · TRS 0/4176 ·
ENGGATE 0/1 · CERT 0 (internal T1/T2(nf=4)+T5) · WRONGLET total fires **1576** ·
gate-passed **56** · coverage min d1-pairs **6** · teeth min **6**.
**Every S3 figure in the note matches.** Sum check, my own:
56+656+4176+4176+4176+0+4176+0+3816+4176+1 = **25,409** ✓.

**The [r3, F-C] timestamp claim is exactly right, and I sharpen it.** `diff` of
my re-run against the committed `liftcorner_checks_output.txt` is **4 lines**,
all wall-clock: three per-block stamps (`Fpt,p=2,CB` 1.7 vs 1.8; `Fpt,p=2,CD`
2.2 vs 2.3; `Fpt,p=3,CD` 3.7 vs 3.8) and the total (`elapsed 4.3s` vs `4.4s`).
With timing normalised the diff is empty. So the note's corrected wording
("identical line-for-line *modulo the elapsed/per-block timestamp fields
only*") is accurate as a description of the artifact — see F4-3 for the defect,
which is about whose record that qualification came from.

### (b) The children generator — regenerates BYTE-IDENTICALLY; A7 all four legs PASS

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe4/children_regen.txt ; echo EXIT=$?
EXIT=0
$ diff /tmp/pe4/children_regen.txt liftcorner_tailstab_children_table.txt
(empty)   -> BYTE-IDENTICAL TO COMMITTED
```

§7 of my regeneration, verbatim:

```
assertion failures: 0
A1 lex (m, deg a) strict descent on EVERY child: PASS
A2 every m'=m child is genre mid[e0-1]-q with deg a' <= deg a - 1: PASS
A3 no m'=m child at deg a = 0: PASS
A4 no m'=m child at d0 = 1: PASS
A5 omega-gain >= 0, gain 0 only at b0-main-r: PASS
A6 LEDGER on the honest double development: PASS
A7 [r2] the enumerated children RECONSTRUCT the object A6 walks: PASS
   nodes reconciled: 752   children enumerated: 5336
   (i)   sum(children a' Phi0^m' Phi'^j') == X exactly: mismatches 0
   (ii)  every child in shape (deg a' < d0, m' >= 0): violations 0
   (iii) digit-wise dev-linearity (children's digits == X's digits): mismatches 0
   (iv)  branching <= 2e0+3: violations 0; observed max children per node by e0:
         {2: 7, 3: 9, 4: 11, 5: 13, 6: 15}  (2e0+3 = {2: 7, 3: 9, 4: 11, 5: 13, 6: 15})
ANY CHILD DROPPING NEITHER COORDINATE: NO
OVERALL: ALL GREEN
```

The r2 regeneration-discipline claim re-confirmed against git, not prose:
`git diff b2dc120 a3112dc --numstat` on the table = **7 0**, and
`grep -c '^-[^-]'` on that diff = **0** — exactly the note's "7 pure INSERTIONS
… 0 deleted and 0 modified lines".

**Hygiene note for the record (no finding against the note):** the generator's
roster uses instance tags `A1…`, and one of them is `A7` — the same token as
assertion A7. The note never quotes the instance `A7`, so nothing in the note is
ambiguous; but a future bracket citing "A7" in that table should disambiguate.

### (c) r3's F-B substitute witness — re-verified in my own exact arithmetic

Corner (ℤ₂, d₀ = 2, e₀ = 2, h₀ = 1, Φ₀ = x²+x+1). Legality of the mid:
deg b₁ = 1 < d₀ ✓; w₀(4x+2) = min(v₂(2), v₂(4)) = 1 and
amin(1) = ⌈(e₀−1)h₀/e₀⌉ = ⌈1/2⌉ = 1, so **w₀(b₁) = 1 = amin(1)** — a legal mid ✓.
Division: a·b₁ = x(4x+2) = 4x²+2x = 4·(x²+x+1) + (−2x−4), so **q = 4,
r = −2x−4** ✓ and q·Φ₀+r = a·b₁ exactly ✓. Valuations:
w₀(a·b₁) = min(v₂(2), v₂(4)) = **1**, w₀(q) = v₂(4) = **2**,
w₀(r) = min(v₂(−4), v₂(−2)) = **1**. So **w₀(q) = 2 > 1 = w₀(r) = w₀(a·b₁)** ✓,
matching the note digit for digit including its LOW→HIGH lists
(`a·b₁ = [0,2,4] → q=[4], r=[−4,−2]`).
Gain difference: gain(q) − gain(r) = e₁[e₀(w₀(q)−w₀(r)) + h₀] = e₁[2·1+1] =
**3e₁ ≠ e₁h₀ = e₁** ✓ — the stricken identity fails at a genuine mid branch.
The r2 dividend's non-realizability also re-verifies: 4x²+2 = (αx+β)(γx+δ)
forces αγ = 4, βδ = 2, αδ+βγ = 0, hence (αδ)² = −(αγ)(βδ) = −8, and
**v₂(−8) = 3 is odd** so −8 is not a square in ℚ₂ ✓; degree 2 with both factors
of degree ≤ 1 forces both = 1, so the constraint is exactly the one the note
uses ✓. And 4x²+2 = 4Φ₀ − 4x − 2 with w₀ = 1/2/1 reproduces the r2 numbers ✓.

Nothing in the repo was edited by this pass except this report.

---

## 2. FINDINGS

### F4-1 — JUSTIFICATION GAP / HONESTY DEFECT (source-verified AND machine-verified): r3's F-A promotes the SECOND tautology of the pair as "the only substantive one"; `C.K2["one"]` is a structural constant that cannot differ for any residue c′

Offending passage (S2, inside the `[r3, F-A]` bracket, second bullet):

> "* **assert (ii) is the only substantive one of the two.**
> `C.K2["one"] == C0.K2["one"]` (`liftcorner_checks.py:179`) compares two
> DISTINCT objects — the K₂ table built on the transported tower against the one
> on the base standard tower — **so it is the half that can actually fire.** It
> remains a one-element check and does not certify that the whole K₂ arithmetic
> representation is shared (r1's correction of the r0 parenthesis is right about
> that); **but a one-element check on two objects carries strictly more evidence
> than a tautology on one.**"

and the fence disclosure that instructs the reader on how to re-read the sealed
docstring:

> "Anyone reading that docstring should read it as: assert (i) is a regression
> guard, **assert (ii) is a one-element check on two objects**, and the soundness
> is in `mk_field_ext`"

and the r3 header bracket's headline for the same repair:

> "**F-A** (the substantive one) — S2 disclosure (c)'s evidential ranking of the
> runner's two asserts is INVERTED: … (ii) (`C.K2["one"] == C0.K2["one"]`),
> which r1 demoted, **is the only one of the two that compares distinct
> objects**."

**`C.K2["one"]` cannot differ between the two towers, for any input.** Trace,
from source:

* `SP.Composite.__init__` (`strata_probe.py:389`) sets `self.K2 =
  mk_field_ext(T.K1, T.psi1)`.
* `mk_field_ext(K, psi)` (`grb_order2_check.py:333`) sets
  `g = len(psi) - 1` and
  `one = tuple([K["one"]] + [K["zero"]]*(g-1))`.
  **So `K2["one"]` depends only on `g₁ = len(psi1)−1` and on `K1["one"]`,
  `K1["zero"]` — it never reads a single coefficient of ψ₁, and never reads the
  reduction data `red` built from ψ₁.**
* `T.K1 = mk_field_ext(K0, T.psi0)` with g₀ = 1, so by the same line
  `K1["one"] = (K0["one"],)` and `K1["zero"] = (K0["zero"],)` — **independent of
  `T.psi0[0]`, i.e. independent of the residue the override writes.**
* `mk_field_base` (`grb_order2_check.py:291`) fixes
  `zero = tuple([0]*d); one = tuple([1] + [0]*(d-1))` — constants of d₀ alone.
* `T` and `T0` are both `LC.make_tower(kind, p, d0, r0, r1, ·)` with the SAME
  arguments (`liftcorner_checks.py:35` and `:144`), so g₁ is the same on both.

Hence `C.K2["one"] == C0.K2["one"]` compares two occurrences of the constant
determined by (d₀, g₀, g₁). It is **structurally incapable of failing**, on
exactly the same footing as assert (i).

**Machine confirmation (my own leg, read-only, `/tmp/pe4/probe_k2one.py`)** on
the note's own d₀ = 2 roster row CB over ℤ₂ (K₀ = 𝔽₄, so both twist draws exist):

```
g0 = 1  g1 = 1  d0 = 2 ;  c0 = (0,1)
C0.K2['one'] = (((1, 0),),)
twist draws: [(1,0), (1,1)]
  c'=(1,0): C.K2['one'] = (((1, 0),),)   equal to base? True   (z1 changed: ((1,0),))
  c'=(1,1): C.K2['one'] = (((1, 0),),)   equal to base? True   (z1 changed: ((1,1),))
K2['one'] with psi1 PERTURBED (psi1[0] += 1): (((1, 0),),)  == original: True
```

The letter `z1` *does* change under the override — so the override is doing real
work — but `K2["one"]` is blind to it, and blind even to ψ₁'s values.

**Failure scenario (what the note now claims the machine can detect but cannot).**
Suppose the transported K₂ arithmetic were built on the wrong reduction data —
e.g. `mk_field_ext` reduced against a stale ψ₁, or `T.K1`'s `mul` carried a
modulus-dependent reducer at g = 1. Every K₂ product in `SP.Composite` would be
wrong, and assert (ii) would still pass silently, because it inspects only the
multiplicative identity, which is `tuple([K1["one"]] + zeros)` by construction
and never touches `red`, `mul`, or any ψ₁ coefficient. The note's claim that
(ii) "can actually fire" therefore names no state in which it fires.

**Why GAP and not CRITICAL.** No proof step consumes assert (ii): the note itself
relocates the soundness to *reading* `mk_field_ext` ("that is where the
override's soundness lives … not in the runner's asserts"), and I re-verified
that reading independently — at g = 1 the loop `range(len(out)-1, g-1, -1)` is
`range(0,0,-1)` = empty (`grb_order2_check.py:345`, with `out = [K["zero"]]`
allocated one line above at g = 1), so products never touch the reducer; and
`K1`'s elements being 1-tuples with modulus-free multiplication makes
`_field_elems`/`pick_irreducible` return c′-independent ψ₁ bytes, which is the
consequence the sheet needs. So the chain and the S3 measurement are untouched.

**Why it matters anyway, and why it is the pass's top item.** (1) It is a FALSE
claim about machine evidence, in the note's evidence-description layer, and the
note's own charge for that layer is exactly the standard r3 applied to r1.
(2) The note applies an **asymmetric standard**: it proves (i) cannot fail by
exhaustively tracing every writer of `T.psi1`, then certifies (ii) on the far
weaker ground that the two objects are distinct — a criterion that a constant
satisfies. (3) It is the **third recurrence of one pattern** in this arc: r0
described the pair as "(ψ₁ bytes equal, K₂ arithmetic representation shared)";
r1 promoted (i); r3 promoted (ii). Each round corrected the previous promotion
and made a new one. (4) The honest statement available at r3 was one sentence
longer: *neither* assert is a carryover check; (i) is a regression guard against
a future ψ₁ recomputation, (ii) is a regression guard against a future change of
(d₀, g₀, g₁) representation; the soundness is entirely in `mk_field_ext`. The
note's own "**no claim in this note consumes (i)**" is true of (ii) as well, and
is never said of (ii).

### F4-2 — JUSTIFICATION GAP (un-superseded refuted text; the bracket system's own discipline broken): the r1 F4 claim that r3's F-A refutes is still standing, unbracketed, at its second site in S5

Offending passage (S5, `STATUS LINE (r1-honest)`, final sentence — **no r3
bracket anywhere on it**):

> "The three r1 gap repairs, for the record: ĉ′/t₀ now defined in-note (F2);
> COR 2's W2-OPEN-1 identification WITHDRAWN and rescoped, with (a)/(b) owed
> (F3); **S2 disclosure (c) corrected to what the runner actually asserts (F4)**."

r3's own F-A refutes exactly that clause, in the note's own words:

> "**r1's F4 repair promoted the wrong half of its own sentence**"

and, in the r3 header bracket:

> "that F4 repair landed on the WRONG HALF of its own sentence — 'full ψ₁-byte
> carryover' is a snapshot-consistency no-op that cannot fail"

So "corrected to what the runner actually asserts" is precisely what r1's F4 did
NOT achieve: the runner does not assert ψ₁ carryover, it asserts self-identity of
a snapshot. r3 handled the **header** occurrence of the same claim correctly — the
r1 header's F4 line is immediately followed by the `[r3, F-A: …]` bracket at
lines 64–68 — but left the S5 occurrence unmarked.

This breaks the discipline the round declares for itself, twice over:

> "Dispositions, each edit carrying a dated `[r3, F-#]` bracket,
> strike-and-replace (the superseded r1/r2 wording is quoted inside the bracket
> that replaces it, **never silently deleted**)"

and the round demonstrably knew about multi-site duplication, since F-C is
labelled "corrected at **both** sites" and S5's r2 status line carries its own
`[r3, F-C — second site of the same overstatement]` bracket. F-A got one site of
two.

**Classification: GAP.** No chain step reads the S5 sentence, and a reader who
gets as far as S2 finds the correction. But PE3's §3(d) recorded "I found **no
un-superseded refuted text** anywhere in the note" as a verified property of the
r2 text, and r3 created the first violation of it — in the note's summary of
record, which is the section a downstream consumer reads first.

### F4-3 — JUSTIFICATION GAP (honesty / misassigned provenance, at both F-C sites): "an overstatement of PE2's own record" / "dropped in the r2 paraphrase" is not what PE2's report says; PE2 asserted bit-identity three times

Offending passages (r2 header bracket and S5's r2 status line, both inside
`[r3, F-C]`):

> "**[r3, F-C — "bit-identically" STRICKEN here as an overstatement of PE2's own
> record.]** The r2 wording was "both machine legs re-ran **bit-identically** at
> PE2"; **PE2's report says something weaker for the sealed leg**, verbatim: its
> family table is "identical line-for-line modulo the `elapsed`/per-block
> timestamp fields only …""

> "… with its output "identical line-for-line **modulo the `elapsed`/per-block
> timestamp fields only**" — **PE2's own qualification, dropped in the r2
> paraphrase**"

`LIFTCORNER_passPE2_report.md` states the unqualified form for the sealed runner
at **three** sites, and the qualified form at **one**:

> (line 33) "**Both machine legs are clean.** The sealed runner re-runs
> **bit-identically** (exit 0, 25,409/0, seal md5
> `ccb4351c92573f5f962cae4ae952d8dd` intact, 0-byte diff since the seal commit)."

> (line 54, section header) "### (a) The SEALED runner — **bit-identical**, seal
> intact"

> (line 471, closing machine-legs line) "Machine legs: sealed runner exit 0,
> 25,409/0, **bit-identical**, seal md5 intact"

> (line 67, the one qualified site) "Family table vs the committed
> `liftcorner_checks_output.txt`: **identical line-for-line modulo the
> `elapsed`/per-block timestamp fields only** …"

So the r2 paraphrase did not strengthen a qualified finding and did not drop a
qualification the source only ever gave qualified: it reproduced PE2's own
headline word, which PE2 used in its verdict summary, its section header and its
closing line. The defect's origin is **PE2's report**, not the r2 paraphrase.
r3's correction is right on the facts — the output file genuinely is not
bit-identical, which my own leg re-confirms at 4 differing lines (§1(a)) — but
its account of *whose record* carried the overstatement is inaccurate at both
sites.

**Classification: GAP (mildest severity class, but squarely in this pass's
charge).** This is the same species as the defect r3's own F-D fixed —
mis-stating what a hostile pass recorded — reintroduced by the round that fixed
it. The accurate wording was available and short: *"bit-identically" is false of
the output file (it carries wall-clock fields); PE2's report used the word in its
summary and qualified it in its family-table paragraph; the counted quantities
are identical.*

### F4-4 — JUSTIFICATION GAP: PROP's rung-≥2 census is cited to two tables that do not contain it, and the cited source's own erratum records a Φ₁-pin consumption site PROP does not mention

Offending passage (S4.3, PROP):

> "**PROP (propagation to every level — the S0.1 rider leg).** (ITER-LAW-n) for
> every lawful monic Φ₁ at the corner, all n: the [ILN] chain consumes Φ₁'s
> explicit bytes only through (i) monicity/degree/w₁Φ₁ = e₀g₀h₀ (shared by every
> orbit member) and (ii) the level-1 base package (= [IL], replaced here by
> COR 1; at n = 1 clause (ii) is ITERLAW S7's own display). … **VERIFY-TARGET for
> the arc: the clause-(ii) census at rungs ≥ 2 (no rung leg opens Φ₁'s bytes
> outside the level-1 package) is cited from the [ILN]/ILNRES consumption
> tables, not re-proved here.**"

**(a) Neither named table carries that census.** ITERLAWN_PROOF's table is a
22-row *dependency/exemption sweep* keyed to accepted-package consumption
("PROVED given only the [IL] base", "never consumes W-MULT, (RM-m), or any DCX
exclusion", "rung ≥ 3 steps never consume RM-1"); I read all 22 rows and **not
one is about Φ₁'s explicit bytes**. The nearest are row 1 ("the cocycle never
consumes Φ_{n+1}") and row 10 ("the canonical lift construction at level m
consumes only data of levels ≤ m") — both about *which levels* are consumed, not
about *how much of Φ₁* is opened. ILNRES's only "**Consumption census**" (S6,
closing the (DS-SUB) induction) is about engine-freeness — "division algorithm ·
S4.1 WELL-DEF existence/degree · the S2 integer layer · [IL]/[IL3]† accepted
bases. NO (RM-m) call, no weight clause, no read clause" — and says nothing
about Φ₁'s bytes either.

**(b) The cited source's own erratum names a consumption site through exactly the
pin PROP relaxes.** ITERLAWN's sweep rows 4, 12 and 19 carry status **C-r4**,
i.e. corrected this round, and the correction reads (S0.3 clause table, L6 row):

> "PROVED given only the [IL] base … **[attribution (errata r4, 2026-08-03;
> PE4-F1): + S4.1 at rungs ≥ 2 — the canonical-lift certification
> (WELL-DEF-(n)/(R1) + C_k existence) consumed via the S0.1 class pin and the
> S4.2 degree-telescope input …]**"

and ITERLAWN S0.1's class pin is, verbatim,

> "Lifts: **Φ₁ := the STANDARD LIFT of ψ₀** (grb_order2_check :499–507); for
> 1 ≤ m ≤ n−1, Φ_{m+1} := the CANONICAL ε_m-CORRECTED LIFT of ψ_m"

So at rungs ≥ 2 the L6 chain consumes S4.1 *via the very pin that fixes Φ₁ to
the standard lift*. That is the one site a Φ₁-relaxation has to clear, and PROP's
(i)/(ii) dichotomy neither names it nor argues that S4.1/WELL-DEF-(n) reads Φ₁
only through monicity, degree and w₁Φ₁. (Plausibly it does — the C_k are built
from ψ_m, γ_{m+1}, ε_m, realize_m and Φ_m, and Φ₂ = Σ C_kΦ₁^{e₁k} uses Φ₁ only
as a power — but that is an argument the note does not make and the cited tables
do not contain.)

**Classification: GAP, not CRITICAL.** The note labels the census a
VERIFY-TARGET, cited-not-proved, and the grade box charges it as item **(5)
PROP's census cite** — so nothing is presented as proved here. The defect is
that the cite's stated *location* does not hold up, and the one consumption site
the source's own erratum flags is undisclosed; an arc verifier following the
citation as written will not find the census. PE1 and PE3 both checked only that
the clause was *labelled* a verify-target ("cited not proved ✓"); neither opened
the cited tables.

### F4-5 — JUSTIFICATION GAP (minor, precision inside the unit's headline identity): `c′` denotes both the residue scalar and the cocycle in one display, and the cocycle is renamed silently between the THEOREM and COR 2

Offending passages (S1 CANDIDATE; S4.3 THEOREM; S4.3 COR 2):

> "    c′(γ,γ′) = z̄^{δ₂} · (z₁′)^{D₁},   D₁ := (s₁+s₁′−s₁″+ℓ₀γ₂δ₂)/e₀,
>      equivalently  c_base(γ,γ′) = c′(γ,γ′) · ξ^{D₁}   (the χ-ratio law),"

> "**THEOREM.** … the 2-read ITER-LAW display holds on the Φ′-tower with the
> letter the lift carries: **c(γ,γ′)** = z̄^{δ₂}·(z₁′)^{D₁}, z₁′ = −c′"

> "for every orbit member Φ′ with residue **c′** and ξ := c₀/**c′**,
>     c_base(γ,γ′) = **c′(γ,γ′)**·ξ^{D₁}   for all γ, γ′ ∈ W₂."

In S1 `c′ := res(b₀/π^{h₀})` is a **scalar in K₀**. In the same displays
`c′(γ,γ′)` is the **cocycle on the Φ′-tower**. COR 2's single displayed equation
uses both meanings — `ξ := c₀/c′` (scalar) and `c′(γ,γ′)` (function) — and a
reader can parse `c′(γ,γ′)` as the scalar applied to a pair. Separately, the
THEOREM writes the same cocycle `c(γ,γ′)` while S1 and COR 2 write `c′(γ,γ′)`,
and the note never states that they are the same function; COR 2's proof ("The
THEOREM applied on the Φ′-tower and on the base tower") is where the
identification is silently made.

**Classification: GAP, lowest severity.** Nothing is mathematically wrong and I
re-derived COR 2 through the collision without difficulty. I record it as a
numbered gap rather than an aside because (a) it sits inside the unit's headline
identity, the one display a consumer will lift, (b) PE3 found it and chose not to
number it ("Recorded here rather than numbered, to avoid severity inflation"), so
r3 had it in hand and left it unchanged, and (c) the fix PE3 named is one
substitution (`c^{Φ′}(γ,γ′)`). On an acceptance attempt an unfixed,
verifier-flagged ambiguity in the headline display is owed, not free.

### F4-6 — JUSTIFICATION GAP (cross-note bookkeeping): "NR-1 then leaves the ILNRES residual list" does not match NR-1 **as recorded in ILNRES**, whose statement includes the clause S5 simultaneously reopens

Offending passage (S5, the consequence display):

> "ITERLAWN S0.1's rider "(ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1;
> **nothing is claimed for any non-canonical lawful lift at any level**" becomes,
> on the Φ₁ axis: "(ITER-LAW-LIFT) DISCHARGED at attempt grade … ITER-LAW-n holds
> for EVERY lawful monic Φ₁, every n, at [ILN]'s own conditionality …".
> **NR-1 then leaves the ILNRES residual list**; the T-class(n) conditionality of
> record shrinks to NR-2/NR-3 (+ NR-4's own closing arc). NOT covered, said
> plainly: non-canonical lawful lifts at DEEPER levels (Φ_{m+1}, m ≥ 1) — a
> separate corner (the g_m = 1 analogue), never part of (ITER-LAW-LIFT)'s
> displayed statement (wave-18 S0), **stays open as its own priced item**."

ILNRES_2026-08-08.md S1 records NR-1's **statement** as:

> "**[NR-1] (ITER-LAW-LIFT), open exactly at g₀ = 1 ∧ δ₁ = 1.** Statement (the
> [IL] package residual, propagated by [ILN] S0.1 verbatim to every level): the
> theorem is proved for the STANDARD/canonical ε-corrected lifts only;
> "**nothing is claimed for any non-canonical lawful lift at any level**", and
> the lift-independence of the 2-read base law is open exactly at
> g₀ = 1 ∧ δ₁ = 1."

So the "at any level" clause is inside NR-1's recorded statement. S5 rewrites the
rider containing it, carves levels ≥ 2 back out as a **new, uncited priced item**
("stays open as its own priced item" — no note, spec number or ledger line is
given), and in the same breath says NR-1 leaves the list. Two frictions:

1. A residual cannot both leave the enumeration and leave a piece of its own
   recorded statement open under a new name, without saying where the new name is
   recorded.
2. ILNRES S7 records, as its load-bearing outcome, that **"S1's FOUR-MEMBER
   residual list is COMPLETE relative to the sources of record — NO FIFTH
   RESIDUAL EXISTS"**. If the deeper-level carve-out is a conditionality it is a
   fifth member; if it is a scope fence (like ILNRES's perimeter fact (iii),
   "orders ≥ 3 untouched … subsumed") it is not — and the note does not say which.

**Mitigations, stated because they are real and they keep this out of the
critical class.** (a) The exclusion is disclosed in the very next sentence, in
the note's own "said plainly" register. (b) The note's justification is
**verbatim correct**: wave-18 S0 displays the residual as "the honest OPEN
displayed lemma **(ITER-LAW-LIFT)**: ITER-LAW for every lawful monic lift Φ₁" —
Φ₁ only, which I checked at source. (c) The **spec of record the note is written
against**, ILNRES S5.1, is likewise Φ₁-only: "Extend the [IL] L7 Case-II analysis
to an arbitrary lawful lift Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride
S0.1's verbatim propagation" — and that is exactly what S4 delivers. So the
*delivery* matches the spec; the *bookkeeping sentence* over-reaches NR-1's
recorded statement.

**Classification: GAP, low severity.** One clause fixes it — naming the
carve-out's home and saying whether ILNRES's completeness claim is affected.

---

## 3. The six directed veins — results

### (a) S1: the setup, the definitions, and the r1 b₀-split — the r1 F2 cure is CORRECT and complete; the residual is the genre PE1 already dispositioned

**The b₀-split (r1's F2 repair) is correct and lands before every use.** I
re-derived its existence clause: w₀(b₀) = h₀ (S1) puts b₀/π^{h₀} in O[x] at
w₀ = 0 with degree < d₀; degree-<d₀ polynomials inject into K₀ = k[X]/(φ̄), so
c′ := res(b₀/π^{h₀}) is a well-defined nonzero K₀-element, any degree-<d₀ lift
ĉ′ has res(ĉ′) = c′ hence w₀(ĉ′) = 0, and t₀ := b₀ − ĉ′π^{h₀} has
b₀/π^{h₀} − ĉ′ ≡ 0 mod π, i.e. **w₀(t₀) ≥ h₀+1** ✓. The block sits in S4,
*before* its two consumers (the S4.1 branch table's rows 2–5 and S4.2's
b₀-main comparison) ✓, and the standard-lift specialization ("ĉ′ = lift(c′) and
t₀ = 0 and all mids b_k = 0") is exactly Φ″ as defined one paragraph above ✓.
The "uniqueness" clause is trivially true as scoped ("given a choice of the lift
ĉ′", t₀ is then determined) — no defect.

**The orbit parametrization re-derived.** Every monic Φ′ of degree e₀d₀ has
Φ₀-development Φ₀^{e₀} + Σ_{k<e₀} b_kΦ₀^k with deg b_k < d₀ and top digit 1; the
top digit contributes e₀h₀ to w₁ = min_k(e₀w₀(b_k)+kh₀), so w₁ = e₀h₀ forces
e₀w₀(b_k)+kh₀ ≥ e₀h₀ for all k; gcd(e₀,h₀) = 1 makes e₀ | (e₀−k)h₀ ⟺ e₀ | k, so
only k ∈ {0, e₀} can sit on the line, giving w₀(b_k) ≥ amin(k) strictly for
1 ≤ k ≤ e₀−1; and the nonzero order-1 residual forces w₀(b₀) = h₀ exactly with
c′ ≠ 0 ✓. So S1's display is a complete parametrization of the orbit as defined,
matching wave-18 S1's three steps with c₀ → c′ ✓. The stratification
(ψ₀^{(ξ)} := ξ^{−1}ψ₀(ξy) = ξ^{−1}(ξy+c₀) = y + c₀/ξ = y + c′ at ξ = c₀/c′; and
z₁ = −c₀ = ξ·(−c′) = ξz₁′) re-derives on one line each ✓.

**Symbol audit — the honest result.** Symbols bound in-note: amin, c′, ξ,
ψ₀^{(ξ)}, z₁′, γ₂ (S4.1), ω(X) (S4.1), ρ (S4.1), ĉ′, t₀ (S4, r1). Symbols used
without an in-note binding: **z̄, W₂, E₂, e₁, h₁, δ₁, δ₂, D₁'s constituents
s₁/s₁′/s₁″/ℓ₀, lift(·), W1/W3** — and **γ₂ is used in S1's CANDIDATE display
(line 206) but bound only in S4.1 (line 396)**, an in-note forward reference.
PE1's F2 explicitly dispositioned this genre — "Other inherited symbols — γ₂,
δ₂, s₁″, ℓ₀ — are corpus-standard from the accepted ITER-LAW display and are used
before their in-note bindings; same genre, subsumed here" — so I do **not**
number it. Two observations inside the genre, recorded not numbered:

* **W₂ vs W1/W3 is a subscript collision.** S4.3's THEOREM and COR 2 quantify
  "all γ, γ′ ∈ **W₂**" (the level-2 read window of the accepted display), while
  S2's roster line reads "windows **W1×W1** + mixed **W1×W3**" (battery window
  instances). A reader applying one subscript convention reads S2's as W₁, W₃ and
  expects W₂ among them. Disambiguated by context, so not numbered.
* `lift(·)` is never defined, but the only property consumed —
  res(lift(c′)) = c′ with degree < d₀, hence w₀(ĉ′ − lift(c′)) ≥ 1 in S4.2 — is
  forced by the name and is the only thing READ-EQ uses. No defect.

**One thing I checked because it is *not* in that genre, and it is clean.**
S1's CANDIDATE asserts "all integer data (splits, D₁, δ₂, windows)
lift-independent". That holds precisely because every orbit member shares
w₁Φ₁ = e₀g₀h₀ (part of S1's orbit definition), and the split recursion
`s₂,u₂ = eq12(γ; e₁,h₁); γ₁ = u₂ − s₂·w₁Φ₁; s₁,u₁ = eq12(γ₁; e₀,h₀)` reads Φ₁
only through w₁Φ₁ ✓. The reason is not displayed but is immediate from the
orbit definition — no finding.

### (b) S4.2 READ-EQ and S4.3 THEOREM end-to-end, re-derived by hand on one orbit member — SOUND

**The δ₁ = 1 leg, re-expanded from scratch.** With s₁, s₁′ ≤ e₀−1 (window
normalization) and δ₁ = 1, write s₁+s₁′ = e₀ + S₁″, 0 ≤ S₁″ ≤ e₀−2, U = u₁+u₁′,
S₂ = s₂+s₂′. Then P = π^UΦ₀^{e₀+S₁″}K^{S₂} and, from the split identity
γ = e₁(e₀u₁+s₁h₀) + s₂γ₂,

    ω(P) = e₁(e₀U + (e₀+S₁″)h₀) + S₂γ₂ = γ + γ′ = Γ   ✓ (both sides expanded).

One pass, children and their ledgers (all four computations mine):

| child | coefficient | (m′, j′) | ledger | gain |
|---|---|---|---|---|
| key | π^U | (S₁″, S₂+1) | Γ − e₁e₀h₀ + γ₂ = **Γ + h₁** | +h₁ |
| b₀-main (Φ′-tower) | −π^{U+h₀}ĉ′ | (S₁″, S₂) | **Γ exactly** (w₀(ĉ′) = 0) | 0 |
| b₀-main (Φ″-tower) | −π^{U+h₀}lift(c′) | (S₁″, S₂) | **Γ exactly** | 0 |
| their difference | −π^{U+h₀}(ĉ′−lift(c′)) | (S₁″, S₂) | ≥ **Γ + e₁e₀** | — |
| b₀-tail | −π^U t₀ | (S₁″, S₂) | ≥ **Γ + e₁e₀** | — |
| mid k | −π^U b_k | (S₁″+k, S₂) | Γ + e₁[e₀amin(k) − (e₀−k)h₀] ≥ **Γ + e₁** | ≥ e₁ |

So the on-Γ-line digit is the b₀-main digit on **both** towers, nonzero on both
(w₀ = U+h₀ exactly), pinning w₂(P) = Γ on both sides; everything else sits
strictly above Γ; and the two b₀-main digits differ by a term at ≥ Γ+e₁e₀, i.e.
strict π-excess at its own slot, which res kills. The Φ′-only children (t₀,
mids) are of the lemma's shape (deg a′ ≤ d₀−1 by S1, m′ ≥ 0), so **TAIL-STAB
applies verbatim** and keeps their entire subtrees at ≥ ω(child) ≥ Γ+1 ✓. Reads
agree slot by slot ✓. The δ₁ = 0 / anchor leg is immediate: deg(π^uΦ₀^s) = s·d₀ <
e₀d₀ = deg K for s < e₀, so the K-development is the single digit π^uΦ₀^s at slot
S — the same polynomial on both towers ✓.

**Interface check I re-confirmed independently:** READ-EQ's parent coefficient is
π^U, of **degree 0**, so deg(a·b) = deg b ≤ d₀−1 < d₀ for every branch factor and
**every branch of READ-EQ's one pass has q = 0** — READ-EQ lives entirely in (B)'s
deg a = 0 stratum, which is why the table above lists single digits only, and why
the r0 strict-descent defect could never have reached it. (PE3 reported the same;
I re-derived it rather than inheriting it.)

**The display, with the letter the lift carries, on one concrete orbit member.**
Take O = ℤ₂, Φ₀ = x²+x+1 so d₀ = 2 and K₀ = 𝔽₄ = 𝔽₂[x]/(x²+x+1) with ω ↔ x;
e₀ = 2, h₀ = 1, g₀ = 1. Base letter c₀ = ω, so ψ₀ = y + ω and z₁ = −c₀ = ω
(char 2). Pick the residue c′ = ω², so ĉ′ = lift(ω²) = x+1, and

    Φ′ = Φ₀² + b₁Φ₀ + b₀  with  b₀ = 2(x+1),  b₁ = 2x  (w₀ = 1 = amin(1)),  t₀ = 0
       = x⁴ + 4x³ + 5x² + 6x + 3            (expanded by hand),
    Φ″ = Φ₀² + lift(c′)·π^{h₀} = x⁴ + 2x³ + 3x² + 4x + 3.

Letters: z₁′ = −c′ = ω², ξ = c₀/c′ = ω/ω² = ω², and z₁ = ξ·z₁′ = ω²·ω² = ω⁴ = ω ✓.
THEOREM on the Φ′-tower: **c(γ,γ′) = z̄^{δ₂}·(ω²)^{D₁}**. On the base tower:
c_base = z̄^{δ₂}·ω^{D₁}. COR 2's ratio law, checked:

    c(γ,γ′)·ξ^{D₁} = z̄^{δ₂}(ω²)^{D₁}(ω²)^{D₁} = z̄^{δ₂}ω^{4D₁} = z̄^{δ₂}ω^{D₁} = c_base ✓

(using ω³ = 1). **Non-vacuity of the transport at this member:** ξ^{D₁} =
(ω²)^{D₁} ≠ 1 exactly when 3 ∤ D₁, so the ξ ≠ 1 direction genuinely moves the
value — which is what Q8's teeth clause preregisters (min 6 per block) and Q9's
1,576 WRONGLET fires measure. **READ-EQ on this member is especially clean:**
ĉ′ = lift(c′) here, so the two b₀-main digits are byte-**identical** (the
difference term is 0) and the only Φ′-only child is the mid b₁ = 2x at
ledger ≥ Γ+e₁, whose subtree TAIL-STAB closes. So the THEOREM's transport is
exact on this member with no residual term at all.

**THEOREM's citation leg, checked at source.** "Φ″ is a STANDARD-LIFT instance of
the accepted class with ψ₀ ↦ ψ₀^{(ξ)}" — Φ″'s order-1 residual is
y + res(b₀″/π^{h₀}) = y + res(lift(c′)) = y + c′ = ψ₀^{(ξ)} ✓, monic of degree 1
with ψ₀^{(ξ)}(0) = c′ ≠ 0, i.e. inside ITERLAWN S0.1's class pin for ψ₀ ✓, and
(e,h,g) data unchanged ✓. So the accepted ITER-LAW applies on the Φ″-tower and
delivers the display with **its** letter z₁′ = −c′ ✓.

### (c) COR 1 and the PROP rider

**COR 1 is airtight, and I found the reason it is *sharper* than the note claims.**
S4's Setting restricts to e₀ ≥ 2 ("at e₀ = 1 no Case II exists — COR-3's
degeneration, theorem-backed, outside this unit"), and PE3 flagged e₀ ≥ 2 as the
one hypothesis the statement does not display. I checked whether that restriction
costs COR 1 any part of the open corner: **it does not, and the corner is empty at
e₀ = 1.** δ₁ = 1 requires s₁+s₁′ ≥ e₀ with s₁, s₁′ ≤ e₀−1; at e₀ = 1 that forces
s₁ = s₁′ = 0 and s₁+s₁′ = 0 < 1, so **δ₁ ≡ 0 at e₀ = 1** — confirmed verbatim at
source by ITERLAW_2026-08-08.md S6.3 ("e₀ = 1: s₁ ≡ 0, ℓ₀ = 0 ⟹ c(γ,γ′) =
z̄^{δ₂}"). So the stratum g₀ = 1 ∧ δ₁ = 1 lies entirely inside e₀ ≥ 2 and S4
covers it in full; the COR-3 cite is belt-and-braces, not load-bearing. I also
confirmed the cite is real and correctly attributed: BRIDGE_ADJUDICATIONS and
ITERLAW3 S9 both record that "ITERLAWLIFT_CORNER's 'COR-3' reference is the
ACCEPTED order-2 note's COR-3 (e₀ = 1 leg, theorem-backed there, unaffected)",
and ITERLAW S6.3 is that leg. **No finding.**
COR 1's scope claim also checks: the lawful class is exactly the ξ = 1 slice
(c′ = c₀), and there z₁′ = z₁ so "the display holds UNCHANGED" ✓; the residual
displayed at wave-18 S0 is "ITER-LAW for every lawful monic lift Φ₁", which is
what COR 1 delivers at the corner ✓.

**PROP — one gap (F4-4) and two things that are fine.** Clause (i)'s data
(monicity, degree e₀d₀, w₁Φ₁ = e₀g₀h₀) really is shared by every orbit member, by
S1's definition ✓, and the "w₁Φ₁ = e₀g₀h₀" figure matches ITERLAWN S0.1's own
convention `w₁Φ₁ := e₀g₀h₀ = e₀g₀γ₁` verbatim ✓. The rung-≥2 census is honestly
labelled a **VERIFY-TARGET, "cited … not re-proved here"**, and is charge item
(5) — so nothing is claimed as proved. What fails is the *location* of the cite
and the non-disclosure of the S0.1-class-pin consumption site the cited source's
own r4 erratum records: **F4-4**.

### (d) S5 as the note's summary of record — one gap (F4-2), one gap (F4-6), the rest reconciles

Sentence by sentence against the post-r3 body:

* The consequence display is still correctly fenced ("ONCE THIS NOTE'S ARC CLOSES
  (and not before — no ledger or accepted text is edited now)") ✓, and its rider
  quote matches ITERLAWN S0.1 verbatim ("The (ITER-LAW-LIFT) residual propagates
  verbatim to every level: nothing is claimed for any non-canonical lawful lift at
  any level") ✓. The bookkeeping sentence around it is **F4-6**.
* `STATUS LINE (r1-honest)`: the (TAIL-STAB) description, the refutation history
  and the byte-unchanged-statement claim all match the body ✓; its F2 and F3
  items match ✓; its **F4 item is refuted by r3's own F-A and unbracketed —
  F4-2**.
* `STATUS LINE [r2]`: the r3 F-D relabelling is applied and internally consistent
  — items (1), (2), (7) now read "RE-DERIVED BY TWO HOSTILE PASSES (PE2 and PE3)
  and carry NO ACCEPTANCE CREDIT", which matches PE2 §3(1)–(4)/G2 and PE3
  §§1(b′)/3/4 as I read them ✓. The five-r2-repair list matches G1–G5 one for
  one ✓. The `[r3, F-C]` second-site bracket is present ✓ (its content is
  **F4-3**).
* `STATUS LINE [r3]`: every clause matches the body — three hostile readings,
  PE3's re-derivation list, the arc display "PE1 → r1 → PE2 → r2 → PE3 → r3 →
  PE4", "attempt 0/2, unchanged", the W-2 cap, the W-2-free decoupling fact, "the
  r3 edits themselves" unaudited, and the byte-frozen machine legs ✓. The
  five-r3-repair summary matches F-A…F-E ✓.
* **Grade-box arithmetic re-checked independently:** PE1 = 1C+3G at 30e570c ✓
  (matches `git log` and the report's own verdict line); PE2 = 0C+5G at 3367f3c ✓;
  PE3 = 0C+5G at 39ea0db ✓; counter **0/2** at all five sites with the correct
  reason each time ✓; charge list has exactly seven items with (7) marked
  `[r2, G2]` ✓. No acceptance credit is claimed anywhere in the note ✓.

### (e) The [r1]/[r2]/[r3] brackets AS A SYSTEM

**Struck text, checked against the diffs rather than the prose.** `git show
e5b3faf` on the note is 221 insertions / 12 deletions and `git show feedaab` is
note-only; I read every deleted line of both. Every refuted r0/r1/r2 claim I could
find is quoted verbatim inside the bracket that supersedes it: the r0
strict-descent clause and the r0 ⌈m/e₀⌉ close (inside the F1 box); the r0
"settled in full" sentence (inside the r1 STATUS LINE); the r1 gain identity, the
r1 "≤ 2e₀+1" parenthetical, the r1 "valid EXACTLY on d₀ = 1", the r1
"UNCHANGED … re-verified by PE1" attribution (inside [r2, G1/G2/G4/G5]); the r1
F4 bracket quoted **in full** inside [r3, F-A]; the r2 "bit-identically" wording
at both sites (inside [r3, F-C]); the r2 "unaudited"/"never been read by anyone"
clauses (inside [r3, F-D]); the r2 "Q6 LOC 0 (no δ₁ = 0 anomaly)" (inside
[r3, F-E]). **One exception: F4-2.**

**Downstream consumption of superseded text — none found.** I traced each struck
claim to its consumers: the ≤ 2e₀+1 count is consumed only for *finiteness*
(König + the one-pass sum), which 2e₀+3 supplies (and (C)(i)'s induction does not
consume (C)(ii) at all, so the count could never have broken anything); the
stricken r-to-q gain identity is replaced by two independent CONTENT applications
and the "ω-gain ≥" column is unchanged, which I re-derived; the "EXACTLY on
d₀ = 1" claim is consumed only as "d₀ = 1 rows cannot exhibit the defect", which
survives; the withdrawn W2-OPEN-1 identification has no consumer (every surviving
occurrence of "W2-OPEN-1"/"RESTRICTED"/"base junction" is a disclosure: source
cite, r1 header, F3 box, charge item (6)); and assert (i) has no consumer, which I
re-verified by walking every ψ₁ site in the note independently of the note's own
walk. **By the same argument assert (ii) has no consumer either — which is what
makes F4-1 a gap rather than a critical, and is also the sentence the note owes.**

**One structural-hygiene defect worth recording, not numbered.** The pre-seal
disclosure list runs (a), (b), (c), (d); r3 inserted ~70 lines of `[r3, F-A]`
bracket **between** (c) and (d), so item (d) now hangs off the end of the fence
disclosure's last sentence, joined by a semicolon: "… and the soundness is in
`mk_field_ext`; **(d) SP bug-detector counters recorded.**" A reader cannot tell
from the layout that (d) is part of the *sealed* pre-run disclosure rather than of
the post-hoc r3 correction. No claim changes; the list is still complete. Not
numbered because the seal record is unambiguous from the commit history.

### (f) The ILNRES NR-1 interplay

Answered in **F4-6**. The delivery matches the spec of record (ILNRES S5.1,
Φ₁-only, "then ride S0.1's verbatim propagation") and matches the residual's
*displayed* statement at wave-18 S0 ("ITER-LAW for every lawful monic lift Φ₁") —
both checked verbatim at source. The bookkeeping sentence "NR-1 then leaves the
ILNRES residual list" over-reaches NR-1's *recorded statement* in ILNRES S1,
which quotes the "at any level" clause that S5's own next sentence reopens as an
uncited new priced item, against ILNRES S7's recorded four-member completeness
claim.

---

## 4. Verified perimeter (re-checked this pass, no findings)

- **The counter-instance chain, recomputed by hand end to end.**
  Φ′ = Φ₀²+2xΦ₀+2 = x⁴+4x³+5x²+4x+3 ✓ (expanded); γ₂ = 3; ω = 2w₀(a)+m+3j;
  ω(X) = 2 at X = xΦ₀². Pass identity gives xΦ′ − 2x − 2x²Φ₀; the mid redigit is
  2x² = 2Φ₀ − 2x − 2 so r = −2x−2, q = 2 ✓. Four children with
  (a′; m′,j′; ω; gain) = (x; 0,1; 3; +1 = h₁), (−2x; 0,0; 2; 0),
  (2x+2; 1,0; 3; +1 = e₁), (−2; **2,0**; 4; +2 = e₁(h₀+1)) — the fourth at
  m′ = m = 2 with deg a′ = 0 < 1 = deg a, genre 7b ✓. Second pass on (−2, 2, 0):
  (−2; 0,1; 5; +1), (4; 0,0; 4; 0), (4x; 1,0; 5; +1) and **no mid q-child**
  because a·b₁ = −4x has degree 1 < 2 = d₀ ✓ — (B)'s prediction. 8 nodes, 6
  leaves all at m ≤ 1 < e₀, depth 2 ≤ ρ(root) = m·d₀+d₀−1 = 5 ✓. Every displayed
  number matches.
- **The independent double-development tie, re-multiplied exactly.**
  (x−2)Φ′ + (6x+2)Φ₀ + (−2x+4) = x⁵+2x⁴+3x³+2x²+x = x·(x²+x+1)² = xΦ₀² ✓.
  Digit w₀ = 0, 1, 1 at (j,i) = (1,0), (0,1), (0,0), weights 3, 3, 2 against
  ω(X) = 2, slacks 1, 1, 0, equality thread at (0,0) = row 2's gain-0 thread ✓.
- **All eight per-digit ω-gain bounds, re-derived from CONTENT, not inherited.**
  With gain = e₁[e₀(w₀(a′)−w₀(a)) + (M′−m)h₀], M = m−e₀+k, M′ = M (r) or M+1 (q),
  and CONTENT giving w₀(a′) − w₀(a) ≥ β for **either** digit separately:
  row 1 = γ₂ − e₁e₀h₀ = **h₁** exactly; row 2 (β = h₀, k = 0, r) = **0** and it is
  the unique zero; row 3 (β = h₀, k = 0, q) ≥ e₁[e₀h₀ − e₀h₀ + h₀] = **e₁h₀**;
  row 4 (β = h₀+1, k = 0, r) ≥ **e₁e₀**; row 5 (q) ≥ **e₁e₀+e₁h₀**;
  row 6 (β = amin(k), r) ≥ e₁[e₀amin(k) − (e₀−k)h₀] ≥ **e₁** by
  e₀amin(k) ≥ (e₀−k)h₀+1 (strict since e₀ | kh₀ ⟺ e₀ | k, impossible for
  1 ≤ k < e₀ at gcd(e₀,h₀) = 1); rows 7a/7b (q) ≥ **e₁(h₀+1)**, and at k = e₀−1
  this is e₁e₀·amin(e₀−1) ≥ e₁(h₀+1) ✓. All eight match the table.
- **The census, the lex order, and both consumers.** The pass identity is exact
  from Φ₀^{e₀} = Φ′ − Σ_{k<e₀}b_kΦ₀^k ✓; deg(a·b) ≤ 2d₀−2 forces exactly two
  digits per branch and forbids a cascade ✓; the 9 ↦ 7 label mapping is total and
  disjoint ✓; row 7b's drop uses monicity (deg q = deg(ab) − d₀ *exactly*) and
  deg b_k < d₀, with the deg a = 0 and deg b = 0 edges vacuous rather than
  off-by-one ✓; both emptiness strata are **proved** (deg a = 0 ⟹ deg(ab_{e₀−1}) ≤
  d₀−1 < d₀; d₀ = 1 ⟹ deg(a·b) = 0 < 1 for every branch factor) ✓; lex on
  ℕ × ({−∞} ∪ {0,…,d₀−1}) is a well-order (ℕ × finite chain) ✓;
  ρ(m, deg a) = m·d₀ + max(deg a, 0) strictly drops on every edge ✓;
  #children ≤ 2e₀+3 with the parenthetical summing 1+4+(e₀−1)+(e₀−1) ✓ and
  attainment {2:7,3:9,4:11,5:13,6:15} re-confirmed from my regeneration ✓.
- **(C)(i)'s close.** Φ′-digits (and inner Φ₀-digits) of a sum are the digit-wise
  sums because each stays below the respective degree bound, so dev-linearity is
  genuine additivity ✓; gains ≥ 0 give ω(child) ≥ ω(X); the ultrametric handles
  slot collisions and cancellation only removes digits ✓; A7(iii) machine-checks
  the additivity step at all 752 probes ✓.
- **CONTENT.** Division by a *monic* Φ never divides by a non-unit, so every
  coefficient of q and r lies in the O-module generated by F's coefficients;
  w₀(q), w₀(r) ≥ w₀(F) ✓. (Still charge item (3); unchanged since r0.)
- **S2/S3 measurement design.** Twists exist iff |K₀| = p^{d₀} > 2 ✓ (|K₀| = 2
  has one nonzero element and it is c₀); the deterministic draw is
  `[c for c in K0.elements() if nonzero and != c0][:2]` ✓; Q7 CHI is genuinely
  measured-vs-measured (`base_cc` comes from `measured_cocycle(T0,C0,…)` on base
  towers that never see TLAW/PV/INT/TRS) ✓; Q1 gates the 56 orbit towers only and
  S3 discloses that scope in the same breath ✓; Q9's two sets are computed by
  disjoint paths (`mism` from the measured cocycle vs the cached base letter,
  `pred` from ξ and D₁ alone) ✓.
- **[r3, F-E] re-verified at source, exactly as stated.** `note("LOC")` does not
  occur in the runner (the only `note(` calls are AV, PV, INT/TLAW/TRS, CHI,
  WRONGLET, GATE, ENGGATE); `viol("LOC", …)` occurs at three sites only
  (`liftcorner_checks.py:90/95/100`), each nested inside the violation branch of
  PV, INT and TLAW respectively; the committed artifact reads
  `LOC       pred 0  obs     0  (     0)  GREEN` ✓. COV's independence also
  checks: `if ncov == 0` / `if not xi1_is_one(…) and nteeth == 0` at `:123–126`
  fire on their own counters ✓.
- **Fences.** No commit in the r1–r3 range touches ILNRES / ITERLAWN / the
  wave-18 note or its runner; the sealed runner is 0-byte-diff from dafc0b5; no
  Lean change; the r2 generator amendment is 7 pure insertions with 0
  deletions/modifications in the table; r3 is note-only. The FENCES paragraph
  holds in the repo state ✓.

---

## 5. Bottom line

**Not a clean pass: 0 CRITICAL, 6 gaps. The acceptance counter stays 0/2 and no
slot opens.**

The proof is in good shape and I did not have to take any of it on trust. After
four hostile readings the (TAIL-STAB) census is complete, its descent
well-founded, its eight per-digit bounds re-derive from CONTENT alone, its two
emptiness strata are proved, its completeness leg is carried by a committed
assertion that decorrelates from the prose transcription, and its one downstream
consumer (READ-EQ) lives in the stratum where the r0 defect could not reach.
READ-EQ's δ₁ = 1 comparison re-expands digit by digit on both towers; the THEOREM
and COR 2 re-derive exactly on a concrete ℤ₂/𝔽₄ orbit member with a non-trivial
letter; COR 1's corner is *fully* covered by S4 because δ₁ = 1 is empty at
e₀ = 1; and the S3 measurement reproduces to the last counted digit.

What this pass found is that the evidence-description layer has now failed three
rounds in a row on the *same pair of machine asserts*, and that r3 — the round
whose whole content was that layer — introduced two new defects of the species it
was fixing. **F4-1** is the substantive one: r3 correctly proved assert (i) is a
tautology, then promoted assert (ii) as "the only substantive one … the half that
can actually fire", when `C.K2["one"]` is a constant of (d₀, g₀, g₁) that cannot
differ for any residue c′ — verified from source and empirically on both twist
draws of the note's own d₀ = 2 row. **F4-2** and **F4-3** are the round's own
bracket discipline turned on itself: an r1 claim that r3's F-A refutes still
stands unbracketed in S5, and F-C's correction misassigns its defect's provenance
to the r2 paraphrase when the cited report carried the overstatement in its own
verdict summary. **F4-4** is the first vein where a cite was actually opened
rather than checked for a label: PROP's rung-≥2 census is not in either table it
is cited to, and the cited source's own r4 erratum records a rung-≥2 consumption
of the S0.1 class pin — the very pin PROP relaxes — which PROP does not mention.
**F4-5** and **F4-6** are precision: the `c′` collision in the headline display
(flagged by PE3, declined, unfixed) and a residual-bookkeeping sentence that
over-reaches NR-1 as ILNRES records it.

Nothing here weakens "(TAIL-STAB) PROVED at attempt grade, argument re-derived by
three independent hostile passes, no acceptance credit" as a description of the
note, nor the W-2-capped grade, nor the honest decoupling fact (the COR 1 / ξ = 1
chain is W-2-free — I re-traced it: TAIL-STAB is division-algorithm/w₀
bookkeeping with GRTW2 cited only in a bracketed structural remark; READ-EQ uses
base facts + CONTENT + TAIL-STAB; the accepted ITER-LAW predates W-2). The six
items above are owed, and since a clean pass has not yet occurred, none has
started.

— passPE4, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-05).
Machine legs: **(a)** sealed runner `liftcorner_checks.py` exit 0,
`VERDICT: ALL GREEN`, `TOTAL checks 25409`, 0 violations in every counted family,
1,576 WRONGLET fires, coverage/teeth minima 6/6, md5
`ccb4351c92573f5f962cae4ae952d8dd`, `git diff dafc0b5 HEAD` on it **0 bytes**;
output differs from the committed artifact at exactly 4 wall-clock lines
(3 per-block stamps + `elapsed 4.3s` vs `4.4s`), empty under timing
normalisation. **(b)** children generator `liftcorner_tailstab_children.py`
exit 0, regenerated table **byte-identical** (`diff` empty), A1–A6 PASS and A7 all
four legs PASS (752 nodes / 5,336 children; sum-identity 0, shape 0, digit-wise 0,
branching 0 with observed max = 2e₀+3 at every e₀), "ANY CHILD DROPPING NEITHER
COORDINATE: NO", "OVERALL: ALL GREEN"; the r2 7-insertion/0-deletion discipline
re-confirmed by `git diff --numstat`. **(c)** r3's F-B substitute witness
re-verified in exact integer arithmetic (a = x, b₁ = 4x+2 legal at
w₀ = 1 = amin(1); q = 4, r = −2x−4, q·Φ₀+r = a·b₁ exactly; w₀ = 1/2/1, so
w₀(q) = 2 > 1 = w₀(r); gain(q)−gain(r) = 3e₁ ≠ e₁; and v₂(−8) = 3 odd, so the
r2 dividend is unfactorable at degree ≤ 1). Nothing in the repo was edited by this
pass except this report.
