# GRTJA pass PE5 — fifth hostile pass (acceptance attempt at 0/2, post-r3) on GRTJA_PROOF_2026-08-08.md

**Verifier:** JA-PE5 (fresh hostile Fable context; fixes nothing). The
acceptance attempt after the r3 repair: a clean pass here starts the
2-consecutive count (counter action = orchestrator's).

**Target pin:** note at HEAD (repo HEAD 615b423), md5 `52e232d2` ==
`git show 8ee86da:` (the JA-r3 repair commit — the note's last commit; no
uncommitted drift). Artifact seals verified by md5 at worktree AND pins:
runner `grt_ja_checks.py` `5972d412` == @696eae8 (SEAL); output
`0d6d0522` and JSON `13ab52ab` == @1cbf8ca (VERDICT). Supplier state at
HEAD: `GRTW2_PROOF_2026-08-08.md` last commit = **ffa1e57** (2026-08-07
08:35, = W2 r2) — the r3 pin sits exactly at the supplier's HEAD, and the
W2 note has NOT moved since (the W2-PE3 REPORT 9bd938f, 09:18, is
post-JA-r3 and note-motion-free — see observation m1);
`ITERLAWN_PROOF_2026-08-08.md` last commit = **ced7dbb** (2026-08-04) —
the §1 pin's "motion-free since" claim TRUE; blueprint (00ce2b6),
completion tree (46e583e), `grt_weld_probe.py` (55f7416),
`iterlawn_pe_reimpl.py` (e7e9151), GRB record (7598491) all motion-free
since before JA r3; JB note last moved 83f47f4 (2026-08-06, pre-JA-r2;
quotes pinned at 4c4ee56, byte-true — below).

**Charge executed:** (1) the r3 diff line-by-line, with byte-checks of
the new W-2 quotes against `git show ffa1e57:` and the carry-list against
W-2 §6.3 at that pin (§2); (2) pin-system completeness — every quoted
span in the note swept for pin status (§3); (3) ONE fresh re-derivation
by a route unused across PE1–PE4: the coset-master-lemma derivation of
the full §3/§4 exponent system + an engine-free, pool-free probe on
self-generated data (§4); (4) arc accounting at HEAD (§5). Machine leg
re-run in a /tmp sandbox (committed artifacts untouched).

---

## 1. Machine leg — RE-RUN, BIT-IDENTICAL MOD TIMING

Re-ran `grt_ja_checks.py` (full battery, /tmp copy with all 13 engine_ext
pinned artifacts): **exit 0, all 17 families GREEN, TOTAL samples 10,311,
0 violations, CK-RES boundary 16, CK-BPREF 26**; stdout line-by-line
identical to the committed `grt_ja_checks_output.txt` after stripping
wall-clock/path fields (54/54 lines, 0 mismatches); regenerated JSON
deep-compared key-for-key against the committed
`grt_ja_checks_results.json`: identical except `elapsed_s` (5.5 vs 7.4).
`violations` list empty in both. Seals intact at pins and worktree (md5s
in the header). Every §7.1 figure the note displays is reproduced.

## 2. Charge 1: the r3 diff, line-by-line — VERIFIED FAITHFUL AT EVERY EDIT SITE

The r3 diff (`git show 8ee86da`) touches exactly: §1 (the [ILN] pin
bracket), §2 clause 8 (grade-text strike + carry-list + pin bracket),
§4(i) chain-level bullet (bracket), §4 transported-chamber bullet
(bracket), §7.2 rows JA-PIN cl. 8 and §4 transport (brackets), and the
appended §8 r3 record — PE4 FINDING 1's five sites + the owed [ILN] pin +
the round block, note-only, exactly as billed. Byte-checks against
`git show ffa1e57:lean/notes/openmath/GRTW2_PROOF_2026-08-08.md`
(wrap-insensitive):

* **Quote A (§2 cl. 8 grade text):** the spans "up to and including each
  chamber's first ξ ≠ 1 junction (38/44 junction-levels" and "PROVED at
  attempt grade given §3–§4" are byte-contiguous at the pin's claims-table
  W2-C3 row; JA's "given its §3–§4" is a disclosed consumer adaptation
  (the row reads "given §3–§4"), and JA's parenthetical "(38/44
  junction-levels; 36 fully derived + 2 instance-warranted I4A/I4B
  r = 5)" faithfully folds the pin's [r2, P1] census clause ("of the 38,
  the 2 with an m ≥ 2 recorded-trivial junction below (I4A/I4B r = 5) are
  instance-warranted, the other 36 fully derived").
* **Quote B (§2 cl. 8 + §4(i) measured clause):** "MEASURED above it
  (6/44: T3A/T3C/T3D/T3E r = 4, I4C r = 4,5) riding W2-OPEN-2" —
  byte-contiguous at the pin, identical row list.
* **Quote C (machine gloss):** "machine TW-RATIO/TW-ADM 44/44" and
  "TW-STRICT SAME-adjacent" both byte-contiguous at the pin. JA's gloss
  "(NOT three independent 44/44 legs)" is not quote-marked and is
  arithmetically exact (the struck figure "44/44/44" = the three families
  TW-RATIO/TW-ADM/TW-STRICT at 44 each; the pin's §5.2 [r1] bracket
  reclassifies TW-STRICT as SAME-adjacent given TW-ADM — its own phrase
  "NOT two independent 44/44 legs" scopes the ADM/STRICT pair; both
  statements consistent). §4(i)'s "the machine figure (TW-RATIO 44/44)
  stands" attribution verified at the pin's §5.2 machine bracket
  ("TW-RATIO 44/44 junction comparisons with NO weight/support
  mismatch") — TW-RATIO is indeed the polygon/weight-agreement family
  W2-C3(i) needs.
* **The carry-list vs W-2 §6.3 at the pin — MATCHES (a)–(d) item-for-
  item:** (a) the (C-coll)/recursion split ✓; (b) W2-OPEN-1's open status
  ✓; (c) the §4.3 convention fence ✓; (d) "W2-OPEN-2's open status for
  clause 3's chain level" byte-contiguous at the pin; the grade split,
  "the chamber qualifier on W2-C1a" (JA: "the W2-C1a chamber qualifier"),
  and (OPEN-2a) with "proved only at m = 1 (W2-ID1)" (byte-contiguous at
  the pin) all carried. JA reorders §6.3's (d)-internal phrases and drops
  the pin's tail "instance-exact on the roster" and the "at m ≥ 2" noun
  qualifier — both semantically absorbed by "proved only at m = 1"
  (equivalent open-at-m ≥ 2 content); no weakening, no strengthening.
* **The struck text** "~~strictly at every level (W2-C3, attempt grade,
  machine 44/44/44)~~" is the note's OWN pre-r3 wording byte-preserved
  (diff-verified); the old closed carry-list ("the (C-coll)/recursion
  split, the §4.3 ℓ-orbit convention fence, and W2-OPEN-1 (value layer)
  OPEN") is replaced rather than struck, but its full content survives as
  items (a)/(c)/(b) and the r3 bracket explicitly records the old list —
  disclosed, faithful.
* **Bracket facts re-verified against git:** W2 r1 = 8d5e3fa 2026-08-06
  19:45, JA r2 = 5d95805 19:36 — "nine minutes after" EXACT; ffa1e57 =
  W2 r2 = the supplier's HEAD at r3 (08:35 < 08:57) AND still at repo
  HEAD; "the W2-C1 leg did not move" TRUE (the C1 claims-table row is
  grade-identical at the pin; only C1a's qualifier and C3's grade moved);
  "Grade changes: NONE" TRUE (the §7.2 grade cells gained brackets only;
  the grade cap and claims are untouched by r3); "Runner + artifacts
  BYTE-FROZEN" TRUE (md5s above). The §1 [ILN] bracket's every claim
  verified (pin ced7dbb = the file's last commit; owed since PE2 o2 /
  PE3 o3 per both records).

## 3. Charge 2: pin-system completeness — the LIVE-ARC EDGES ALL PINNED

Every double-quoted span in the note (37 spans extracted mechanically)
classified: self-quotes in repair brackets / print quotes with tex
anchors / cross-note quotes. The cross-note inventory: [ILN]† →
**ced7dbb** (§1, r3); every W-2 cite → blanket **ffa1e57** (§2 cl. 8's
"this cite — and every W-2 cite in this note" bracket; covers W2-L0/L2/L3
in §3, §4.3/§5.1/W2-C3 in §4, the §5 bullet, §7.2, JA-BOX-2/3); both JB
§0M col-(b) quotes + the col-(c) reference → **4c4ee56** (re-verified
byte-true at that pin this pass, including the "**CARRIED AND
UNDISCHARGED**" head and the "[r5, F-3 — STATUS NARROWED" bracket
opening); "the same HR-REC mechanics read backwards" (attributed to
W2-C1's proof) byte-true at ffa1e57; "the field-dependent families" = the
note's own sealed runner docstring (md5-sealed); the PE2-report quotes in
§3.4/§8 carry their commit (9040961). **No unpinned live-arc quote
remains** — the drift species PE4 graded is extinct at HEAD. Remaining
unpinned cross-DOC cites (all motion-free at HEAD, none quoted from a
moving arc): the blueprint (JA-BOX-1's display quote; motion-free since
00ce2b6, 2026-08-04, pre-seal), the completion tree (JA-MIN bracket;
motion-free since 07-31), and §5's GRB record cite "REV 11/14" (dated-REV
genre; the record's last commit 7598491 PREDATES the JA note; PE4's n1
adjudication re-confirmed — the REV 13/pass-16 brackets at source narrow
TR-3 rows to scopes JA does not consume). WM is referenced only inside
dated [JA-r2] history brackets (no live WM consumption).

## 4. Charge 3: fresh re-derivation — THE COSET-MASTER-LEMMA ROUTE (unused by PE1–PE4)

Prior routes: PE1 = direct subtraction of the displayed exponent
fractions + hand instances; PE2 = witness construction + sealed-engine
/tmp leg (396/0); PE3 = own recursion-tree walk over the sealed pools +
QO/d₀ legs; PE4 = ν-shift + SEALED W2-L2 covariance (consumed proved) +
grid-interpolation polynomial identities + conjugation-form probe over
the sealed engines. NEW ROUTE, two axes at once: (i) derivation — the
ENTIRE §3/§4 exponent system obtained as corollaries of ONE primitive,
with every integrality warrant derived rather than presupposed or
consumed; (ii) machine — the first probe of this arc that imports
NEITHER sealed engine, touches NO committed pool/roster, and uses its own
iterative extended-Euclid Bézout (PE4's probe used `pow(h, −1, e)`), on
self-generated data with EXHAUSTIVE small boxes (mod/min identities are
not polynomial, so PE4's interpolation route cannot reach them;
exhaustion can).

**MASTER LEMMA (coset form).** For e ≥ 1, gcd(e, h) = 1, V ∈ ℤ: the
integer points on hX + eY = V are exactly the abscissa coset
X ≡ ℓV (mod e), ℓ = the normalized Bézout inverse (ℓh + ℓ′e = 1,
0 ≤ ℓ < e). Hand corollaries, each re-derived in full this pass:
JA-GRID(a) (s = ℓV mod e IS the least nonnegative integer-ordinate
abscissa; u ≥ 0 ⟺ sh ≤ V — the proviso's exact content); JA-GRID(c)
(carry δ ∈ {0,1} with the ≥ e indicator); JA-EPS (ℓu = t + sℓ′ from the
Bézout split of ℓ(β − sh)/e, hence ℓ′s − ℓu = −t — no subtraction of two
displayed fractions); **the W2-L2 covariance display DERIVED FROM
SCRATCH** (s(β + kW) = s(β) and t(β + kW) = t(β) + kA from e | W and
A = ℓW/e ∈ ℤ, hence ε(β)·z^{t-at-u} = z^{kA} — PE4 consumed this sealed);
the JA-RES exponent t(i) − τ = −iA **with both integrality warrants
derived** (s_att lies in the common coset of ℓu_i and ℓβ_i because
e | ℓ·i·W — the master lemma applied at the digit's own line; prior
passes presupposed integrality or cited W2-L0); ORB-EPS (s is
ℓ-mod-e-blind, t^(κ) = t + κβ, the display exponent κβ = hs + eu = the
line equation itself); the ORB-RES exponents (t(i) ↦ t(i) − κu_i with
s_att ℓ-free as polygon data; grid ordinates u₀ − jh give the displayed
z^{−κu₀}·(z^{κh})^j); A = 0 ⟺ e = 1.

**Machine leg** (`ja_pe5_coset_probe.py`, /tmp, disclosed uncommitted,
same discipline as the PE2/PE3/PE4 probes): exhaustive box e, h ≤ 12
coprime × V ∈ −40..80 (+ V′ box for carry) PLUS 20,000 random draws
(e, h ≤ 50, β ≤ 10⁶, k ∈ −3..3 incl. NEGATIVE key-multiple shifts, which
no sealed family exercises; κ ∈ 1..4): **M0 master lemma 11,011 / C1
grid-a 7,371 / C2 carry 152,971 / C3 ε 12,397 / C4 W2-L2 display 86,779 /
C5 per-slot exponent + warrants 12,397 / C6 ORB-EPS 49,588 / C7 ORB-RES
24,794 / C8 819 — TOTAL 358,127 checks, 0 violations, exit 0.** The
note's own small-V counter-instance (e, h, V) = (2, 3, 1) ⟹ u = −1
reproduced exactly, and 1,194 u < 0 box instances confirm the JA-GRID(a)
proviso is doing real work (non-vacuous). Every displayed exponent in
§3.2, §3.3(a)/(c), §3.4 (integer layer), §4(ii)/(iii)/(iv) and the §1
A_m/W_m display is confirmed on data the sealed battery never saw.

## 5. Charge 4: arc accounting at HEAD — ONE FINDING

Round facts vs git, all EXACT: PE1 report 5e70442 (2026-08-04) → r1
ce0469a → PE2 9040961 → r2 5d95805 (2026-08-06 19:36) → PE3 c77ae6f
(2026-08-07 07:59, CLEAN, counter 1/2 at a83c108) → PE4 535e79f (08:47,
0C + 1G, counter resets) → r3 8ee86da (08:57). §8's r3 record states all
of this correctly, and the ledger at HEAD carries the matching live line
("JA 0/2 (PE5 next)"). Six [JA-r3] brackets = PE4's five sites + §1, as
billed. The r3 record's PE4 summary (machine leg, 396/396 probes, census
third-reproduced) matches the PE4 report verbatim-faithfully.

**FINDING 1 — JUSTIFICATION GAP (minor; header + §7.3 vs §8 at HEAD):
the r3 repair left the two live arc surfaces contradicting the arc record
it wrote.** At HEAD the header (genre line) still reads "acceptance ARC
OPEN: round 1 = …, round 2 = JA-PE2 …; counter 0 CLEAN passes of the 2
consecutive required; no gate fires; **next pass = JA-PE3**", and §7.3's
fence still reads "counter 0/2 CLEAN (rounds 1–2 = PE1/PE2, both
repaired; **next = PE3**, [r2])" — while §8's r3 record (same commit)
states "rounds 1–4 complete …; next pass = JA-PE5". This is an IN-NOTE
contradiction between live surfaces, the exact species JA-PE2 FINDING 4
graded a gap and r2 cured by normalizing "at every surface"; PE4's
observation n3 excused these same strings explicitly and only "by the arc
convention (a clean pass edits nothing; the note has had no repair round
since)" — a warrant that lapsed when r3 edited the note. NOT critical: no
mathematical content moves; the counter VALUE "0/2 CLEAN" happens to be
true at every surface (post-PE4 reset); the ledger and §8 carry the
truth. Cure: the one-line r2 normalization re-applied (header + §7.3
round inventory and next-pass strings).

Checked and NOT graded (candidates that fail the bar):
* The grade cap's "its lift clause consumed from W-2 **clause 1**" vs
  clause 8's three-clause display and §7.2's "clauses 1–3": defensible
  compression (the class-pin lift clause proper is W2-C1's content; the
  transported-type sentence carries C3 and is now separately pinned and
  bracketed); text unchanged since composition, stood through four
  passes including a CLEAN one.
* §2 cl. 8's carried "(OPEN-2a) … proved only at m = 1 (W2-ID1)" is
  byte-faithful to §6.3(d) at the ffa1e57 pin, and the SUPPLIER'S OWN
  later pass (W2-PE3, 9bd938f, 21 minutes after JA r3) found that W-2's
  two-sided "identification" language outruns LEMMA W2-ID1 (one
  direction proved; converse counter-instance constructed, blast radius
  contained, consumers "consume only the proved direction"). This is
  post-pin supplier adjudication with the W2 r3 repair in flight: the
  as-of pin does exactly its job, no JA derivation rides W2-ID1's
  converse, and the note's (d) is carried as OPEN conditionality either
  way — fold-owed re-quote when the supplier's r3 lands (observation m1),
  not a defect of this note at its pin.
* §8 r3's "next pass = JA-PE5 = the acceptance attempt" at counter 0/2:
  matches the dispatch's own usage (a clean PE5 starts the count);
  terminology consistent with the ledger.

---

## FINDINGS (0 critical, 1 justification gap, 0 minor)

* **FINDING 1 — GAP (minor severity; arc surfaces).** Header "next pass
  = JA-PE3" + §7.3 "next = PE3" contradict §8's "rounds 1–4 complete …
  next pass = JA-PE5" at HEAD; the staleness convention PE4 cited
  covered only the no-repair-since state, and r3 was a repair. One-line
  cure (the r2 FINDING-4 normalization re-applied to both surfaces).

**Ungraded observations:** (m1) the W2-ID1/(OPEN-2a) carried language is
faithful at the ffa1e57 pin but the supplier's PE3 has since confirmed
W2-ID1 one-directional (contained) — re-quote owed at the fold or when
W2 r3 lands. (m2) standing PE4 items n1 (GRB dated-REV cite) and o2
(census-scope wording) ride unchanged; the ILN pin debt (o3) and the
unpinned-W2 gap are now EXECUTED — the two oldest fold debts are gone.
(m3) the blueprint and completion-tree cites remain commit-unpinned
(motion-free suppliers; lowest-risk genre left).

**What survived this hostile pass (for the record):** the r3 diff
faithful at all six edit sites with the new W-2 grade text, machine
gloss, and (a)–(d) carry-list byte-checked against the supplier at
ffa1e57 (spans byte-contiguous, compressions content-exact); the pin
system covering every live-arc cross-note quote (W2/ILN/JB + sealed
self-artifacts), all pins verified at source and all pinned suppliers
motion-free since; the whole §3/§4 exponent system re-derived from the
single coset master lemma with every integrality warrant derived, and
confirmed by an engine-free, pool-free probe — 358,127 checks, 0
violations, incl. the W2-L2 display from scratch and negative-k shifts
no sealed family exercises; the machine bracket bit-identical (exit 0,
17 families, 10,311/0, boundary 16, bpref 26) with seals intact at pins
and worktree; arc round facts exact against git and the ledger.

JA-PE5 FINDINGS: 0 critical, 1 justification gap (minor), 0 minor
VERDICT: NOT CLEAN — counter stays 0/2 (orchestrator's ledger action);
the gap is a one-line arc-surface normalization, after which the next
pass is the acceptance attempt again.
