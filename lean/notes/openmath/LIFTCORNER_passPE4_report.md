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
