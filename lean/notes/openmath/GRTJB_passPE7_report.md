# GRTJB-PE7 — hostile verification pass on the post-r6 J-B tree-junction note (FIFTH ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` **at HEAD** (note
last touched by **r6** = `4607824`, 241 insertions / 29 deletions, one file —
THE ONE-FENCE ROUND: (d3) re-fenced `P<q` → `P≤q` with §0M row 11 split
first, the r5 probe figure replaced by the PE6 verifier's attributed
598,500/0 record, the membership-residue wording corrected at two sites).
**Scripts re-run (all four):** `grt_jb_checks.py` (sealed) ·
`grt_jb_r1_levelcensus.py` · `grt_jb_printwalk.py` · `grt_jb_printwalk2.py`.
**Verifier:** Fable, fresh context, read-only, fixes NOTHING. Genre:
quote-and-classify (CRITICAL ERROR = breaks the logical chain, stop checking
dependents; JUSTIFICATION GAP = assume the conclusion and keep verifying).
Pass date 2026-08-06 (wallclock). Prior reports **JB-PE1** (1C+9G), **JB-PE2**
(0C+7G), **JB-PE3** (0C+8G), **JB-PE4** (0C+8G), **JB-PE5** (0C+5G),
**JB-PE6** (0C+2G+1m) read in full, and the r6 diff read line by line, before
this pass formed any judgment. This is the SEVENTH hostile reader and the
FIFTH acceptance attempt.

---

## §0. VERDICT

**0 CRITICAL, 1 JUSTIFICATION GAP, 2 minor.**

    GRTJB-PE7 FINDINGS: 0 critical, 1 gap + 2 minor / VERDICT: NOT CLEAN
    acceptance counter stays 0/2 (a pass with findings is not a clean pass)

**The r6 re-fence itself is CLEAN — mathematics, propagation, and machine
alignment all verified.** The F-1 re-fence is CORRECT at source: JA-VAL's
induction step (J-A §3.1) needs the φ_{m+1}-adic dev to BE the Φ_m-dev, so
w_{q+1} = v_{q+2} (JA-VAL at level m = q+1) needs byte agreement through
j = q — exactly `P≤q`, exactly as row 11 (a2) now says. All **12 re-fence
sites** are present and mutually consistent (row 11 split; column (a2)
consumer list; summary point (2) recounted to THREE; grade cap; §1 [r6, F-1]
amendment; §3 body (d); §3 ∎ Grade block; §3 machine bracket; §7.2 JB-VTX
row; §7.3 W-3 bullet; JB-BOX-2's enumeration; row 24 (a2) cell). The
load-bearing machine claim — "the runner's q ≤ shared_upto gate on (d3) IS
this fence, so the IND leg covers the full re-fenced range" — VERIFIED FROM
COMMITTED CODE: `shared_upto` (grt_ja_checks.py L155) is the max L with byte
agreement for all 1 ≤ j ≤ L, and since `P≤q` is a prefix condition,
q ≤ shared_upto ⟺ `P≤q` exactly; the re-fenced statement range
[0, min(qcap, L)] equals the keyed range exactly (see m-3 for the one
transcription nuance). The exclusion geography (bites at q = qcap on
T3A/T3C/T3D/T3E/I4C only) re-verified against the runner's own byte census.
The F-2 replacement is genuine: the r5 parameters are indeed unrecoverable
(r5 commit message and ledger L11242 checked — bare figure only), and **my
own independent enumerator reproduced the PE6 record EXACTLY on the first
natural attempt** (598,500 members, 0/0 violations, 1 ∉ 𝒲₁ at (2,3)) —
unlike the r5 figure, which PE6 could not reproduce at all. The strike
system is balanced at **77 spans** (156 `~~` tokens − 2 backticked literals,
toggle-parse clean), exactly r6's claim. The arc-accounting system is
consistent at HEAD as a system (the LIFT F6-1 audit): the [r6] S-STATUS, the
r6 round block, the §7.3 CONSUMES bullet and the closing dating record ALL
say six passes / six rounds / counter 0/2 / JB-PE7 next; every arc hash
(85a8dc9 … ca39044, 4607824) exists and matches its description; superseded
round-block closers stand under the note's dated-record convention that PE6
already ratified.

The one gap is **bred by the r6 diff itself, inside the m-1 fix**: both
[r6, m-1] brackets assert the carried membership hypothesis is "per-instance
a logically STRONGER hypothesis than the proviso, **not an equivalent** (or
weaker one)" — an affirmative non-equivalence claim with no derivation,
dropping PE6's explicit "strictness unproved either way" qualifier, and
**refutable at every m = 1 instance**: for every read datum,
{V ≥ 0 : u(V) ≥ 0} = 𝒲₁ exactly (four-line proof below;
machine-confirmed on 96 read data, 0 counterexamples) (F-1). The two minors:
a THIRD live site of the m-1 disease that the r6 sweep — following PE6's
two-site quote list — never reached (JB-BOX-2's [r5, F-3] bracket still says
"is **exactly** lattice MEMBERSHIP") (m-2); and all four live transcriptions
of (d3)'s machine gate omit the code's second conjunct `q + 1 <= G.RANK`
(verified redundant on the loop domain, so no coverage claim is endangered)
(m-3).

**All four machine legs reproduce bit-identically, exit 0, all four md5s
intact at HEAD, `git diff verification/` empty after the runs** — r6's
"note-only, all instruments byte-frozen" claim HOLDS.

---

## §1. MACHINE LEG (mandatory — all FOUR runners RUN, exit 0; no leg NOT-RUN)

Run from `verification/openmath/`, `python3`, no arguments, nothing edited.

| runner | md5 at HEAD | exit | reproduction |
|---|---|---|---|
| `grt_jb_checks.py` (sealed) | `55f4911eaddd8524fd91368b30ed71bd` **intact** | **0** | 18/18 families GREEN, 6,700 samples, 0 violations; output **diff-identical** to committed `_output.txt` (0 lines) |
| `grt_jb_r1_levelcensus.py` | `2bcb44fdbf839d367f0e11033a5d3fd7` **intact** | **0** | output **diff-identical** to committed `_output.txt` (0 lines) |
| `grt_jb_printwalk.py` | `f53e23e8d1c79f084a1e34eee857e37c` **intact** | **0** | 5/5 GREEN; output diff-identical (0 lines); 84 leg-A / 12 byte-unequal / 72 leg-B |
| `grt_jb_printwalk2.py` | `6c6318f7fc6570a2d454389b38441329` **intact** | **0** | 3/3 GREEN; output diff-identical (0 lines); 45 xframe / 27 degen / 28 recon |

`git diff verification/` is **EMPTY** after all four runs (0 lines,
including the three `_results.json`). Figures vs the note, all match:
EXT-GATE 1 · JB-DEV 893 · JB-KEYEQ 25 · JB-SHEAR 893 · JB-VTX 893 ·
JB-ID 34 · JB-TREE 79 (125 with chambers) · JB-LINE 194 · JB-EPS 955 ·
JB-CM 28 · JB-CREAD 79 · JB-QO 5 · JB-D0 4 · TW-JB 2,480 · teeth 3/3/3/3
caught · censuses scored 104 | boundary 21 | v = 0: 0 | R = 0: 0 |
off-perimeter tree rows 0 · byte census identical to the note's roster
statement (T3A/T3C/T3D/T3E `{1:T,2:F}`, I4C `{1:T,2:F,3:F}` — exactly the 5
shared_upto < n towers; the other 11 coincide) · level census m = 1: 45/0 ·
m = 2: 8/10 · m = 3: 3/3, 0 scope-outs, totals 13 = 0/10/3.

**Charge-1 code verification (the r6 gate claim), from committed source:**
`GJA.shared_upto(T, G)` (grt_ja_checks.py L155–163) returns the max L ≥ 0
with `T.Phi[q] == G.phi[q+1]` for ALL 1 ≤ q ≤ L (contiguous prefix; the
`break` makes non-prefix agreement irrelevant, and `P≤q` is itself a prefix
condition) — so **q ≤ shared_upto ⟺ `P≤q`, exactly**. In `jb_shear_vtx`
(grt_jb_checks.py L259–284): d2 unguarded; under `q <= L`, d1
(`minU == G.vgen(q+1,f)`) and d3 (`if q + 1 <= G.RANK and
minH != G.vgen(q+2,f)`). `G.RANK = T.NR = n+1` (GmnLeg L211 via
`gmn_from_tower` L456–459; `T.n = T.NR − 1`, iterlawn_pe_reimpl L255), and
the loop caps q ≤ qcap ≤ n, so the extra conjunct `q+1 ≤ RANK = n+1` is
ALWAYS TRUE on the loop domain — the effective d3 gate is q ≤ L, i.e.
`P≤q`, and the keyed range [0, min(qcap, L)] IS the full re-fenced
statement range, on all 16 roster towers, the QO extractions (n = 0,
RANK = 1) and the d₀ ≥ 2 shapes. The r6 claim holds; the transcription
nuance is m-3.

**The r6 replacement record, reproduced independently (read-only, /tmp):**
my own enumerator under PE6's disclosed parameters (1-, 2-, 3-level chains;
coprime (e, h), e ≤ 6, h ≤ 8 — 32 pairs; W_l ∈ {0,1,2}; a ≤ 4; j_l ≤ 6) with
the natural equal split (300 chains per level count, sampled WITH repetition
— forced: the 1-level chain space has only 32 distinct members) checked
**598,500 lattice members: u < 0 violations 0, step-(2) identity violations
0, 1 ∉ 𝒲₁ at (e, h) = (2, 3)** — the exact figure and all three verdicts,
on the FIRST natural parameterization. Count identity:
300·(5·7 + 5·7² + 5·7³) = 300·1,995 = 598,500. Residual disclosure for the
record: the 300/300/300 split and the sampling rule are not stated in
PE6's report §1 and are not arithmetically forced (35x + 245y + 1715z =
598,500, x+y+z = 900 has 80 nonnegative solutions); the count reproduces
under the natural reading and the verdicts are sample-independent (u ≥ 0 is
the displayed theorem), so this stays a disclosure, not a finding.

**The F-2 unrecoverability claim, verified:** the r5 commit message
(`f9f104e`) and the ledger entry (`BRIDGE_ADJUDICATIONS_2026-07-30.md`
L11241–11242, "fresh probe: 5,288,324 lattice members, 0 violations") carry
the bare figure only — no h-range, j-ranges, a-range or counting unit.
"Parameters unrecoverable from commit+ledger, checked" is TRUE.

---

## §2. FINDINGS

### F-1 — JUSTIFICATION GAP (charge 1, the r6 diff's one bred defect: the m-1 fix asserts non-equivalence that is unproved in general and FALSE at m = 1). Both [r6, m-1] brackets claim the membership residue is "per-instance a logically STRONGER hypothesis than the proviso, not an equivalent" — at every m = 1 instance it IS an equivalent

§0M column (b), [r6, m-1] (LIVE):

> the relation, stated precisely ("exactly" struck above as overstating
> necessity): membership IMPLIES the u ≥ 0 instance the two rows need at
> V = w_{q+1}(f) — a SUFFICIENT route, **per-instance a logically STRONGER
> hypothesis than the proviso, not an equivalent**; …

§5 SCOPE, [r6, m-1] (LIVE): "… — a SUFFICIENT route, per-instance a
logically STRONGER hypothesis, **not an equivalent or weaker one**; …"

The sufficiency direction is right and is all any consumer uses. But "not
an equivalent" is an affirmative mathematical claim, presented as "the
accurate relation", with no derivation anywhere in the note — and it is
REFUTABLE at the q = 0 (m = 1) instances, which the consuming rows 4/12
include (their quantifier is 0 ≤ q ≤ qcap):

    At m = 1, for EVERY read datum (e₀, h₀, g₀):  {V ∈ ℤ_{≥0} : u(V) ≥ 0} = 𝒲₁.
    (⊇) By the note's own four-line theorem at m = 1.
    (⊆) u(V) ≥ 0 means V = s·h₀ + u·e₀ with s := (ℓ₀V) mod e₀ ∈ [0, e₀−1]
        and u ≥ 0; take j := s ≤ e₀−1 ≤ P₀−1 (P₀ = e₀g₀, g₀ ≥ 1) and
        a := u in the displayed description
        𝒲₁ = {e₀a + h₀j : a ≥ 0, 0 ≤ j ≤ P₀−1}.  ∎

So at every m = 1 instance V = w₁(f) — any f, including the residual domain
deg f ≥ deg Φ₁, since the equivalence is a statement about V-values —
membership ⟺ the needed u ≥ 0 instance. Machine check (read-only, /tmp):
all 96 read data (e ≤ 6, h ≤ 8 coprime, g ≤ 3), V ∈ [0, 150): **0
counterexamples to the equivalence**. At m ≥ 2 the containment is typically
strict (e.g. V = e_{m−1} has u ≥ 0 but generically sits below every 𝒲_m
generator), so the true relation is: containment always; strictness
INSTANCE-DEPENDENT, never established in-note — precisely PE6's
"strictness unproved either way", the qualifier this bracket dropped while
transcribing PE6's "not an equivalent or weaker one" phrase (the same
inheritance mechanism as m-2).

Classification: gap, not critical — direction remains conservative (a
consumer carrying membership carries at least what the proviso needs;
nothing anywhere consumes non-equivalence), the row cells' operative
content is untouched, and the frontier is unaffected. But the sentence
labels itself "the relation, stated precisely" and is the r6 diff's one
piece of new mathematics beyond the re-fence; it is wrong at a whole level
class. This breaks the arc's streak: r5's and r6's re-fence prose bred no
defect, but r6's m-1 prose did.

### m-2 — MINOR (charges 2 + 4: the m-1 disease at a THIRD live site the r6 sweep never reached). JB-BOX-2's [r5, F-3] bracket still says "is exactly lattice MEMBERSHIP" — the necessity-overstating "exactly" that r6 struck at §0M column (b)

JB-BOX-2, the r1/G-5 bullet's [r5, F-3] bracket (LIVE, L2159–2165):

> What remains open at the two consuming rows (4 and 12) is **exactly**
> lattice MEMBERSHIP at their unbounded-degree quantifiers …

Same claim shape as §0M column (b)'s pre-r6 "is exactly the MEMBERSHIP
hypothesis" (struck by r6) and §5's "strictly smaller" (struck by r6): what
is strictly needed at the residual domain is the u ≥ 0 instance; membership
is the sufficient hypothesis the note CARRIES, so "exactly" overstates
necessity (and, per F-1, at m = 1 it happens to be true — which is exactly
why the blanket wording at all three sites needed the careful form, not the
absolute one). Mechanism: PE6's m-1 quoted two sites and its repair
recommendation said "one sentence at §5 and one at §0M column (b)"; r6
followed that list. PE6's own 17-surface sweep verified this bullet carried
the narrowed CONTENT but never re-audited its adverb. The verbatim-pin
inheritance genre (LIFT F6-2's third-site pattern). Minor: same grade PE6
gave the genre; the surrounding operative content ("holds by definition at
deg f < deg Φ_{q+1} … not established off it") is accurate.

### m-3 — MINOR (charge 1, transcription: every live description of (d3)'s machine gate omits the code's second conjunct). The d3 assertion runs under `q <= L` AND `q + 1 <= G.RANK`; the note says only "q ≤ shared_upto" at all four sites

`grt_jb_checks.py` L283:

    if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):

The four live transcriptions — ⟨n3⟩ ("under `q <= L` both … (d3)"), the §3
machine bracket, §7.1's JB-SHEAR row ("both under q ≤ shared_upto"), and
the r6 round block ("has ALWAYS gated (d1)/(d3) at q ≤ `shared_upto(T,G)`")
— all state the single-conjunct gate. VERIFIED IMMATERIAL: `G.RANK = T.NR =
n+1` and the loop caps q ≤ qcap ≤ n, so `q+1 ≤ RANK` is identically true on
the loop domain (it is a `vgen`-domain guard: vgen(q+2) devs against
phi[q+1], defined up to RANK+1) — every coverage claim ("the gate IS the
fence", "covers the full re-fenced range") remains TRUE. But this arc's own
standard is exact code transcription (r4/F-5 rewrote a cell for
misdescribing a sampling grid; PE6's F-1 quoted the gate from source and
also omitted the conjunct — this pass is the first to read L283 in full),
and after r6 the gate is load-bearing: it is (d3)'s OWN STATEMENT FENCE,
so its transcription should be byte-faithful. One clause at ⟨n3⟩ (the cell
the other sites cite) would cure all four.

---

## §3. CHARGE-BY-CHARGE COVERAGE, AND WHAT SURVIVED

**Charge 1 (the r6 diff line-by-line).** All 241 insertions / 29 deletions
read. (a) **The re-fence mathematics re-derived at source**: JA-VAL (J-A
§3.1) proves w_m = v_{m+1} by induction whose step needs "the φ_{m+1}-adic
dev IS the Φ_m-dev" — keys byte-equal at j = m. So (d3) = w_{q+1} = v_{q+2}
= JA-VAL at m = q+1 needs agreement through j = q = `P≤q`, NOT `P<q` —
r6's fence is the correct one, and it is the SAME rule already governing
rows 17/18 ("`P<q` read at level m" = perimeter at the consumed level) —
the system is now uniform: every JA-VAL consumption at level m is fenced at
level m. (b) **The (d1)/(d2) retention on `P<q` is sound**: (d2) is
harness-internal (T-only operators; `P<q` is over-fencing, conservative);
(d1) is print Lemma `shape` item 1 applied at the W2-C1 representative —
its inner operators (v_{q+1} recursion through φ_q, φ_{q−1}, …) consume
keys at levels ≤ q−1 = `P<q`, the outer key is the representative pin
(column (d) YES), so the shared_upto gate on d1 is genuinely an instrument
cut. The asymmetry with (d3) is principled: (d3) is a cross-frame J-A
THEOREM consumption, where W2-C1 admissibility as a rescue is exactly the
representative-pin route r3/F-4 refused at (RES); taking it at (d3) alone
would unmotivate (RES)'s fence — the r6 refusal is the consistent choice.
(c) **All 12 re-fence sites verified consistent** (list in §0; each checked
against row 11 at HEAD; JB-BOX-2's `P≤q` list carries all three consumers;
row 24 (a1) correctly still records row 11 — (d1)/(d2) remain a `P<q`
consumption). (d) **The gate-coverage claim verified from code** (§1). (e)
**F-2 verified end-to-end**: unrecoverability checked at both cited
sources; the replacement transcribes PE6 §1 faithfully (parameters
verbatim, attribution + commit); both record-layer keepers of the old
figure ([r5] round block, [r5] dating entry) carry [r6, F-2] pointers; my
own reproduction (§1) confirms the new record IS reproducible in substance
— the adjective survives its test. (f) **m-1 as applied**: the strikes at
§0M/(b) ("exactly") and §5 ("strictly smaller") are correct and the
"smaller = the open domain" reframing is accurate — but the inserted
relation overclaims (F-1) and one sibling site was missed (m-2). (g) **No
§2–§5 identity moved**: every deletion is a strike-and-annotate or arc
bookkeeping; F-1 is a strict narrowing of one sub-clause's fence. (h)
Frontier correctly UNCHANGED at FOUR: (d3) post-r6 carries a key perimeter,
not an open proviso, and its (f) cell holds an IND leg — it fails the
frontier criterion twice over.

**Charge 2 (the arc-accounting system at HEAD — the LIFT F6-1 genre).**
CONSISTENT AS A SYSTEM, first time checked post-r6: the [r6] S-STATUS
(six passes, six rounds, PE7 next, instruments byte-frozen, no probe of its
own), the r6 round block (same, with the disposition list matching the
applied diff exactly), §7.3's live CONSUMES bullet ("[r6] six hostile
passes run, six repair rounds applied; JB-PE7 …"), and the closing dating
record ([r6] entry, arc line through PE6 (0C+2G+1m) → r6 → PE7, prior arc
lines struck) agree everywhere; the [r5] S-STATUS is struck with the [r6]
supersession banner counting FIVE struck predecessors correctly. All 14 arc
hashes resolve in git with matching subjects (85a8dc9, 4c97649, 46f9452,
67bf0c4, 888e293, 2fd271e, 8acb2d1, 87c553d, 38c4754, ae0acdf, 39e16ee,
f9f104e, ca39044, 4607824). Superseded round-block closers ("JB-PE6 is the
next acceptance attempt" inside the r5 block) stand un-struck — verified to
be the note's standing dated-record convention (the r4 block's closer stood
identically at post-r5 HEAD and PE6 ratified the convention); the
authoritative surfaces all say PE7. Strike census: **156 `~~` tokens − 2
backticked literals = 154 = 77 balanced spans**, toggle-parse clean —
exactly r6's "77 (67 + 10 r6)", and the 10 r6 spans enumerate correctly
(r5 S-STATUS, row 11 (a1), "exactly", summary (2), grade cap clause, §5
probe bracket, "strictly smaller", §7.2 clause, footer counter, dating arc
line). The S-STATUS's PE6-history clause is accurate against the PE6
report (including "its F-1 closed the arc's LAST unread body vein").

**Charge 3 (fresh-eyes sweep over the six reports' re-derivation
complement).** Compiled coverage: PE1 (JB-EPS, JB-CREAD's five lines + ε′,
the shear + slope law, JB-AFF, §3(a)'s v_{q+2} half), PE2 (F1 split,
JA-GRID(c)), PE3 (JB-VTX(a)–(d), JB-ID, (VAL)/(GRID)/(RES) vs J-A verbatim,
walker2 audit), PE4 ((RM-m) recital byte-compare, §4(iii) scope), PE5
(§4(i)/(ii), 𝒲_m at source, per-edge laws vs S3.2), PE6 (four-line theorem
+ corollary + license, §2(i), §1's degree identity, v = 0 branch, §3(c),
§3(d)'s level bookkeeping). Fresh territory THIS pass entered: the full
gate conjunct at `grt_jb_checks.py` L283 (m-3 — the one line of the tie
code no pass had transcribed completely); the `shared_upto` prefix-maximality
argument (P≤q ⟺ q ≤ L needs the contiguity the `break` provides — verified);
the RANK/NR arithmetic across all three instrument object classes (roster,
QO n = 0, d₀ ≥ 2); the m = 1 membership/u ≥ 0 equivalence (F-1's
refutation — new mathematics, machine-confirmed on 96 read data); exact
reproduction of the 598,500 record (first natural attempt, count identity
displayed); the r5-parameter unrecoverability check at both sources. I also
re-derived: the four-line theorem and parity corollary (exact, including
the m = 1 corner and the two divisibility legs); §3(a)'s shear arithmetic
under the P-index dictionary (e_q^har = e_{q+1}^GMN — exact); §3(e)'s
corrected window clause (sound via JB-AFF). After this pass the complement
I can name is EMPTY: every §1–§7 body vein has now been re-derived or
source-checked by at least one of seven readers.

**Charge 4 (matrix-surface consistency, final audit).** The r6-touched
rows/cells verified against every carrying surface (charge 1(c)); the
r6-untouched surfaces spot-checked for row-11 staleness: NO live surface
still fences (d3) at `P<q` — the only residual "print-side min ties …
machine-restricted" phrasings sit inside the banner-fenced superseded
regions (r0/r2 §7.2 table L2395, r0 grade cap, r2 §7.3 display — all
retained-for-record, correctly fenced). Summary point (3) ("exactly two
rows consume u ≥ 0") still true; ⟨n3⟩'s "three keyed, (d4) unkeyed" still
true; JB-BOX-6's standing rule text (table governs; matrix edited first)
was FOLLOWED by r6 (row 11 split is the diff's first §0M hunk). The
frontier census re-walked under the criterion: rows 4, 5, 12, 22 IN; 13,
18(C-W_Q), 20 OUT with displayed reasons; row 11 (a2) correctly NOT a
candidate (no open proviso, IND leg present). Matrix vs machine: row 11's
(f) cell, ⟨n3⟩, §7.1's JB-SHEAR row and the §3 machine bracket agree with
the code on everything except the m-3 conjunct.

---

## §4. CHECKED AND CLEAN (so this pass's coverage is auditable)

* **Both PE6 gaps and the minor are genuinely discharged at their
  surfaces**: F-1 (row 11 split first, 12 surfaces re-derived, fence
  mathematically correct, machine gate = fence verified from source), F-2
  (figure struck, replacement attributed + reproducible — reproduced by
  this pass), m-1 (both quoted sites corrected; the residue is F-1/m-2 of
  this pass, in the fix's own new prose and at a third site PE6's list
  missed).
* **The four-line u ≥ 0 theorem, its corollary, and the license
  derivations re-derive exactly** (seventh reading); independently
  machine-confirmed on 598,500 members, 0/0 violations.
* **All four machine legs bit-identical to committed artifacts** (0-line
  diffs on all four outputs), exit 0, md5s intact, `git diff verification/`
  empty; every figure in §7.1/§7.4 matches the fresh runs.
* **The r6 S-STATUS's machine claims hold** (byte-frozen, note-only, no
  new probe; the one new figure is PE6's, attributed).
* **No gate claim, no gr/carrier claim, no density claim anywhere**; the
  counter is 0/2 at every live site; JB-PE7 named consistently as this
  attempt.
* **The 598,500 record's residual ambiguity disclosed but not charged**
  (§1): the 300/300/300 split is the natural reading, not a stated
  parameter; verdicts are sample-independent; nothing rides on the figure.

---

## §5. WHAT A REPAIR WOULD HAVE TO DO (for the composer, not this verifier)

1. **F-1** — at both [r6, m-1] brackets, replace "not an equivalent (or
   weaker one)" with the instance-honest relation: "membership implies the
   needed instance; the converse is instance-dependent — EQUIVALENT at
   m = 1 (the u ≥ 0 set IS 𝒲₁, j = s decomposition), containment
   possibly strict at m ≥ 2, strictness not established either way" — or
   simply restore PE6's qualifier. One sentence at §0M column (b), one at
   §5.
2. **m-2** — strike "exactly" in JB-BOX-2's [r5, F-3] bracket (L2162) with
   an [r7] pointer to column (b), completing the m-1 sweep at its third
   site.
3. **m-3** — extend ⟨n3⟩ (and, if desired, the §3 machine bracket) by the
   second conjunct: "(d3) additionally guarded `q+1 ≤ G.RANK`, a
   vgen-domain check, identically true on the loop domain since
   RANK = n+1 ≥ qcap+1".

---

## §6. Divergences from PE1–PE6 (all six read before this pass)

* **All three PE6 findings discharged as charged; none recurs in its
  original form.** The re-fence — the round's substance — is flawless: for
  the first time in the arc a fence movement propagated to all 12 surfaces
  with zero divergence found.
* **F-1 here is the first defect BRED BY a repair diff since r4** (PE5/PE6
  verified r4's dispositions exact and r5's/r6's re-fence prose clean; the
  m-1 wording fix is where r6's new prose failed). The finding sizes
  continue to shrink: one adverb-grade logical overclaim, one missed
  sibling adverb, one omitted redundant guard. Nothing moves an identity,
  a fence, a census, a grade, or a machine claim.
* **The inheritance mechanism is now the arc's dominant residual failure
  mode**: F-1 transcribed PE6's phrase minus its qualifier; m-2 transcribed
  PE6's two-site list as the sweep universe. Both are the
  verbatim-pin-against-a-report genre (LIFT F6-2/F7-1) — repair rounds
  should treat verifier reports as pointers, not as site censuses, and
  re-grep the disease pattern themselves ("exactly", "strictly smaller"
  grep at r6 would have caught L2162 in one call).
* **New verification technology this pass added**: reproduction of the
  replacement record (the first time a JB figure was INDEPENDENTLY
  reproduced rather than replayed); refutation-by-construction of a live
  logical-relation claim (the m = 1 equivalence); full-conjunct code
  transcription of the tie gate.

---

## §7. Pass hygiene

Nothing was edited. All four scripts, all committed artifacts and the note
are byte-untouched; the four re-runs regenerate all outputs and the three
`_results.json` with zero diff (`git diff verification/` empty; only
`__pycache__` written by the interpreter). My probes ran read-only with
outputs to /tmp (`pe7_probe2.py`, the m = 1 equivalence check). `git add`
is scoped to this report file alone; other agents' in-flight files were
never touched or staged. Sources consulted read-only:
`GRTJA_PROOF_2026-08-08.md` (§1 P-index dictionary + perimeter, §3.1
JA-VAL), `grt_jb_checks.py` (qcap_of, jb_shear_vtx L259–284),
`grt_ja_checks.py` (shared_upto L155–163), `grt_weld_probe.py` (GmnLeg
L196–246, vgen L316–327, gmn_from_tower L456–459), `iterlawn_pe_reimpl.py`
(L255), `BRIDGE_ADJUDICATIONS_2026-07-30.md` (L11230–11255), the six PE
reports, the r5/r6 commit messages, and the r6 diff.

No leg is NOT-RUN.

— GRTJB-PE7, Fable, fresh context, 2026-08-06 (campaign date 2026-08-08).
This pass returns findings, so it is **not** a clean pass: the acceptance
counter for the note remains **0/2**, and the fifth acceptance attempt has
not landed.
