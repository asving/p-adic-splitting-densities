# GRTW2 passPE4 report — hostile pass 4 on `GRTW2_PROOF_2026-08-08.md` (post-r3; acceptance attempt)

**Verifier:** Fable hostile pass PE4, fresh context, wallclock 2026-08-07.
**Target:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` at HEAD (last note
commit 79d1d9c = the r3 repair round; working tree byte-clean, `git status`
clean on `verification/`). **Inputs read:** the PE1/PE2/PE3 reports (083adff /
79e796b / 9bd938f), the full r3 diff (9bd938f-era note ffa1e57 → 79d1d9c,
note-only +194/−41), the sealed runner `grt_w2_checks.py` + committed
artifacts + `iterlawn_pe_reimpl.py` at the cited lines, the GMN print
`docs/references/HigherNewton.tex` at the P2-anchor lines, the WM surface at
f8c2c09. I fixed nothing.
**Outage disclosure:** a first PE4 attempt was interrupted before committing;
this pass found its draft + fresh-leg script, AUDITED the script line-by-line
(independence confirmed: own PF/EXT arithmetic, own trial-division
irreducibility, own scan transcription; the sealed reimpl imported ONLY for
the enum-order cross-check), and RE-RAN every leg from scratch — machine leg,
fresh leg, census recomputation, quote byte-compare, tex anchors, hand
re-derivations. Every claim below is this pass's own verification.

## VERDICT

**0 CRITICAL ERRORS. 1 JUSTIFICATION GAP (minor). 1 minor defect. NOT CLEAN —
the counter stays 0/2** (this pass does not start the 2-clean count).
Everything r3 SET OUT to do is done correctly and faithfully: the four
PE3-flagged sites are scoped to the proved direction with accurate text; the
counter-instance block is a faithful quote of PE3's construction (verified
byte-level modulo bold markers and one terminal period) and the construction
itself is TRUE — I re-derived it from scratch with my own field arithmetic
(§B); the converse flag inside W2-OPEN-2's premise SUFFICES — the premise
does NOT need restating (adjudication §ADJ, the charge's open item: NO
finding); the machine leg reproduces (exit 0, 6,403/0, 17 GREEN, JSON
byte-identical including elapsed_s, §C); a fresh leg by a route unused by
PE1/PE2/PE3 — exhaustive selection-geography mapping at m = 1, 33,408
checks / 0 failures — confirms the counter-instance, the roster-invisibility
claim, and W2-ID1's forward direction at g ∈ {3,4} beyond all roster evidence
(§D). The gap: **r3's scoping sweep stopped at PE3's four listed sites and
missed three same-species surfaces** that still carry the pre-r3 two-sided
"identification ... proved at m = 1" vocabulary (P1). The minor: the footer
dateline was not extended with r3 (P2).

---

## P1 — JUSTIFICATION GAP (minor; residual of PE3-P1's species at sites the r3 sweep did not reach). Three surfaces still assert or implicate the two-sided identification as proved at m = 1; the note's own §5.2 now records that only the FORWARD direction is proved and that the converse is FALSE under the sealed scan's selection off-roster.

Sites, strongest first (all [r2]-era text untouched by r3):

* **§6.3(d) — the consumer carry list** (the most consumer-visible surface
  in the note: "Any consumer citing this must carry: …"): "*[r2, P1:
  including W2-OPEN-2's own premise sub-clause (OPEN-2a) — the
  recorded-ξ/byte-divergence identification at m ≥ 2, **proved only at
  m = 1 (W2-ID1)**, instance-exact on the roster].*" The identification is
  NOT proved at m = 1 — LEMMA W2-ID1 proves its forward half only, and the
  converse is false under the sealed scan's selection off-roster (the
  note's own §5.2 [r3] boundary block). Structurally identical to the §6.2
  wording ("the coincidence with first byte-divergence is W2-ID1 at m = 1")
  that PE3 graded and r3 cured.
* **§5.2, the (OPEN-2a) opening gloss:** "*the byte-equality below r₀ just
  asserted **IS the identification** 'first recorded ξ ≠ 1 junction = first
  byte-divergence', which this note does NOT prove at m ≥ 2.*" Post-r3 the
  half≠whole distinction is the note's own recorded content (the corrected
  W2-ID1 "Consequently" calls the forward statement "the HALF of the
  identification"); this sentence equates the forward half with the whole
  and implicates an m = 1 proof of the whole. The operative sub-clause
  statement and its Status line immediately below are correctly
  one-directional (PE3 §A.2 confirmed; unchanged).
* **§6.4 [r2] block:** "*the new proved lemma W2-ID1 (§5.2) closes the
  m = 1 slice of **that identification**.*" Weakest instance — a charitable
  parse reads "that identification" as (OPEN-2a)'s (one-directional)
  sub-clause, under which the sentence is true; but the label
  "identification" for the forward half is the residual conflation
  vocabulary, and the note's own repair convention annotates even dated
  arc records (r3 put an inline [r3] annotation into §8's P1(a), an equally
  dated record) — not applied here.

**Blast radius: nil (verified).** I re-read every load-bearing consumption
at HEAD: the §5.2 re-scope warrant ("recorded ξ = 1 ⟹ byte-equal … PROVED
at m = 1 … at m ≥ 2 … (OPEN-2a)"), (OPEN-2a)'s sub-clause statement, the
36+2 census (below-chain = TH-BASE + W2-ID1), and the corrected grade-cap /
§6.2 / S-STATUS / §8 sites — each consumes ONLY the proved direction, and my
own census recomputation (§E) confirms the numbers they carry. The three
sites above are display surfaces. Repair: one clause each, the same scoping
r3 applied elsewhere. Classification: JUSTIFICATION GAP (minor) — an
unproved statement asserted as proved on live display surfaces, the exact
species PE3 graded minor.

## P2 — minor defect (arc-surface staleness). The footer dateline enumerates repair rounds and stops at r2.

Footer at HEAD: "*— W-2 COMPOSER unit, campaign date 2026-08-08; r1
2026-08-06; r2 2026-08-07.*" Verified across all four note commits: r1
appended "r1 2026-08-06" (8d5e3fa), r2 appended "r2 2026-08-07" (ffa1e57) —
the arc's own convention is that each round extends the dateline — and r3
(79d1d9c) did not append r3. S-STATUS and §9 record THREE repair rounds; a
reader of the footer alone infers two. Same species as JA PE5's arc-surface
finding (surfaces disagreeing with the arc record after a repair round);
one-token cure. No content rides on it.

---

## §ADJ. The charge's open item — the [r3]-flagged converse-consuming spot in W2-OPEN-2's premise: **THE FLAG SUFFICES; the premise does NOT need restating. NO finding.**

The clause: "*byte-DIFFERENT for r₀ ≤ q < r*" + the [r3] flag ("unproved at
every m and FALSE under the sealed scan's selection off-roster … it stands
here as part of this OPEN box's premise, alongside (OPEN-2a), not as a
proved fact"). Adjudication:

1. **The clause functions as scope, not warrant.** W2-OPEN-2 is an OPEN
   box; its premise DEFINES the situation the conjecture addresses.
   Premises of open boxes may contain unproved clauses when marked — this
   one is marked loudly, with the mechanism and a cross-reference to the
   recorded counter-instance.
2. **Restating to the proved direction would change the box's mathematical
   content, not repair it.** The box exists to bridge the criterion across
   byte-DIVERGENT same-type lower keys (the live above-twist region);
   deleting or weakening the byte-DIFFERENT clause would either widen the
   claim to chambers with byte-equal keys at q ≥ r₀ — a different (and
   partially trivial) statement — or lose the description of the region
   the 6 MEASURED junction-levels live in. The honest treatment is exactly
   what r3 did: keep the descriptive premise, mark it unproved.
3. **No consumer needs the clause to be true off-roster.** The only
   consumption of W2-OPEN-2 is the MEASURED grade at the roster's 6
   above-twist junction-levels, where the premise is instance-verified
   (my recomputation: all 6 SKIP junctions byte-RED; 22/22 walked
   equivalence; every below-r₀ junction byte-GREEN — §E). A class-pin
   chamber violating the clause (a spurious-twist chamber) simply falls
   outside the box's premise; the note claims nothing there — and W2-C3's
   proved scope at-or-below r₀ is selection-robust (any satisfying pair
   makes Φ^har a strict representative of the corresponding conjugate;
   the spurious re-coordination touches only above-r₀ data).

One imprecision, recorded as an OBSERVATION (o-a below): the flag attributes
the whole clause to "the CONVERSE direction of the identification"; strictly
only the q = r₀ instance is the converse (recorded ξ ≠ 1 ⟹ byte-RED at r₀) —
at r₀ < q < r the clause is the box's own persistence assertion ((iii)'s
"persistent unit ratios"), open for a different reason. The operative
marking ("part of this OPEN box's premise … not as a proved fact") covers
all q, so this does not rise to a defect.

## §A. The r3 diff, line-by-line — FAITHFUL at every edit site

* **Genre line + [r3, o2]:** the r0 "no acceptance arc opened" parenthetical
  struck with an accurate supersession note ✓ (the parallel §6.4 sentence
  was already [r1]-struck ✓).
* **S-STATUS rewrite:** all arc facts verified against git — 5463f2a
  (2026-08-04 15:59) → PE1 083adff (08-06 19:16, 0C+2G+5m ✓ vs the PE1
  report's verdict) → r1 8d5e3fa (19:45) → PE2 79e796b (08-07 08:20,
  0C+2G+1m ✓) → r2 ffa1e57 (08:35) → PE3 9bd938f (09:18, 0C+1G minor ✓) →
  r3 79d1d9c (09:31). The [r3] arc sentence states the P1 cure precisely
  (forward proved / converse unproved-at-every-m / counter-instance
  recorded / flag added / surfaces re-checked) ✓.
* **Grade-cap [r2, P1] bracket:** struck two-sided text + [r3, PE3-P1]
  replacement — accurate; the replacement's logic (no byte-divergence
  strictly below the first recorded twist = all the proved scope needs) is
  correct: junctions strictly below r₀ have recorded ξ = 1, so TH-BASE +
  W2-ID1/(OPEN-2a) give byte-equality ascending; nothing below r₀ consumes
  the converse ✓.
* **W2-ID1 "Consequently" rewrite:** the struck sentence and its
  replacement state the proved half exactly; "the HALF … that every
  consuming surface of this note uses" verified by my own re-read of the
  three consuming surfaces ✓; the converse's diagnosis (a property of the
  never-pinned selection rule; §5.1 step 1 says only "record the junction
  pair"; §3.4 rk. 2 non-uniqueness) verified against the note's own text ✓.
* **The counter-instance block:** faithful quote of PE3 §P1 (byte-compared;
  differs only by dropped bold markers and a terminal period inside the
  quotes); source citations verified line-exact — `orbit_scan` at runner
  lines 135–163 (cited "135–164"; 164 is the trailing blank — content-true),
  `Ext.elems` at reimpl line 220 ✓, "only g in {1,2} implemented" at reimpl
  line 311 ✓. Construction re-verified from scratch: §B. The closing
  disclosure condition ("only where no nontrivial support-stabilizing unit
  precedes 1 in enumeration order") is the EXACT characterization — my
  sweep (§D) confirms it with zero exceptions over 4,173 cases, and it is
  sharper than PE3's own repair-queue phrasing ("only over prime-field
  layers"), correctly generalized.
* **W2-OPEN-2 premise flag:** adjudicated §ADJ — suffices ✓.
* **§6.2 W2-C3 row [r3] bracket:** accurate ("forward direction only …
  all the proved scope needs") ✓.
* **§6.4 [r3] block:** accurate; "open boxes unchanged in count" ✓ (the
  counter-instance is a record next to the lemma, not a new box).
* **§8 P1(a) inline [r3] annotation:** accurate ✓.
* **Fold item [r3, o1]:** verified at source — `git show f8c2c09` (WM r5):
  "its only commit" sits at WM line 111 exactly ✓; line drift only, the
  parenthetical IS still stale (W2 has post-5463f2a commits) ✓.
* **§9 round block:** matches the PE3 report clause-by-clause (verdict,
  the five CONFIRMED items, the fresh-leg description, the repair map
  (a)–(d), the alternative-cure-not-taken rationale — which is correct:
  pinning a ξ = 1 preference would misdescribe the byte-frozen scan's
  off-roster behavior) ✓. o3 correctly billed to JA's ledger ✓.
* **Freeze:** runner sha256 71f8fc90…ba52 ✓ byte-identical at working tree
  and HEAD; probe leg 107c92b6…4ea9 ✓; both artifacts committed-byte clean ✓.

## §B. The counter-instance re-verified from scratch (charge 2) — TRUE

Own implementation (`/tmp/w2_pe4_fresh.py`, no runner imports in the
arithmetic): own prime/extension field classes, own Bézout normalization,
own trial-division irreducibility, own transcription of the scan loop's
semantics from the sealed source (runner lines 135–163, read directly).
Results (checks B1–B8, all PASS): normalized Bézout at e₀ = 1 gives ℓ₀ = 0
⟹ A₁ = ℓ₀g₀γ₁ = 0 ⟹ c₁ = c = 1 ⟹ the §3.4 rk. 3 byte law holds trivially —
byte-equal junction, formula pair (1,1) ✓; ψ₁ = y³ + ζ monic, ψ₁(0) = ζ ≠ 0,
irreducible over F₄ by exhaustive trial division ✓; x³ = 1 for all nine…
all THREE elements of F₄* ✓, so all three units satisfy the orbit equations
(count = 3, verified) ✓; the enumeration order of the SEALED
`Ext.elems` — cross-checked directly against the sealed reimpl (import,
list, compare): (0,1) = ζ strictly precedes (1,0) = 1, and the sealed order
equals my independent product-lex model element-for-element for F₄ and F₉ ✓;
the scan therefore records **(ζ, 1) — recorded ξ ≠ 1 at a byte-equal
junction** ✓. The class-pin membership items (gcd(e,h) = 1 both reads,
ψ(0) ≠ 0 both levels, monic irreducible moduli) each re-checked ✓. The
ROSTER-INVISIBILITY argument verified analytically AND exhaustively (§D):
g = 1 stabilizer trivial; g = 2 sparse stabilizer {±1} with nonzero
constant term (char-2: {1}; odd char: −1 enumerates after 1) — so on a
g ≤ 2 roster the enumeration order realizes the ξ = 1 preference
everywhere ✓, consistent with the 22/22 census.

## §C. Machine leg (re-run this pass)

* **Seals:** `grt_w2_checks.py` sha256 `71f8fc90…ba52` ✓ (= the S-STATUS
  figure; git log shows the runner untouched since seal commit 5463f2a);
  `grt_weld_probe.py` sha256 `107c92b6…4ea9` ✓.
* **Re-run: exit 0. 6,403 samples, 0 violations, 17 families GREEN, teeth
  MT-TW caught, boundary junctions = 1 (I4B r = 5).** Per-family counts
  match §6.1 exactly (CK-MM 4,396 · CK-HR1/VD1 156 · CK-REC 55 · CK-SLOT
  44/16 · CK-XI 22 · CK-BYTE 28 · TW-RATIO/ADM/STRICT 44 · TW-F3/F3b 684 ·
  TW-PARI 12 · TW-QO 7 · CK-T3E 2 · MT-TW 2). Run executed in a /tmp COPY
  of the three sealed modules (runner + reimpl + probe leg), so the
  committed bytes were untouched by construction; the produced results
  JSON is **byte-identical to the committed artifact including elapsed_s
  (3.2)** — `diff` empty; stdout differs from the committed output in
  exactly one intermediate timing figure (1.0 → 0.9 s at the T3D row) plus
  the JSON-path line (expected from the /tmp cwd). `git diff verification/`
  empty throughout.

## §D. Fresh leg (route unused by PE1/PE2/PE3): exhaustive SELECTION-GEOGRAPHY mapping at m = 1 — 33,408 checks, 0 failures

PE1 derived the closed form; PE2 evaluated it at the m = 1 roster slice;
PE3 evaluated it at full roster scope modulo the stabilizer and probed the
single counter-instance with the scan's copied loop. THIS pass mapped the
recorded-pair SELECTION RULE itself, exhaustively, with fully independent
arithmetic (`/tmp/w2_pe4_fresh.py`, exit 0):

* **(A) enum-order decorrelation:** my product-lex model == the sealed
  reimpl's `Ext.elems` element-for-element (F₄, F₉); ζ precedes 1; tuple
  convention (ascending coefficients, one = (1,0)) verified against the
  sealed `one()`/`reduce_list` ✓ — the note's line-220 claim confirmed at
  source and independently.
* **(C) the sweep:** ALL monic irreducible ψ with ψ(0) ≠ 0, deg g ∈ 1..4,
  over F₂/F₃/F₄/F₅/F₇/F₈/F₉ — 4,173 polynomials. At the byte-equal
  residual, the enum-order scan records ξ ≠ 1 (spurious) in exactly 6
  instances, forming two families: **(F₄, g = 3, supp {0,3})** — the PE3
  counter-instance family (ψ = y³+ζ, y³+ζ²) — and (F₉ with modulus y²+1,
  g = 4, supp {0,4}) (ζ⁴ = 1 there). **ZERO spurious instances at
  g ≤ 2** — the roster-invisibility claim exhaustively confirmed — and the
  characterization *spurious ⟺ the support stabilizer contains a unit
  preceding 1 in enumeration order (zero constant coefficient)* holds with
  0 exceptions in all 4,173 cases — the r3 block's disclosure condition is
  exact. "The failure needs g_m ≥ 3" confirmed (found at g = 3 and 4,
  none below).
* **(D) W2-ID1's forward direction beyond the roster:** for every field,
  every such ψ, and EVERY unit ξ_f (29,223 grid points), with R = ψ(ξ_f·y)
  per the unconditional m = 1 display: recorded ξ = 1 under the enum-order
  scan ⟹ the strict/byte law — **0 violations, including g ∈ {3,4}**,
  where the roster (g ≤ 2 builder limit) has no instances at all. The
  lemma's algebra holds exactly where its proof says it does, and the
  counter-instances found are all converse-side — none forward-side.

## §E. Statement-level truth at HEAD (charge 3) + census recomputation

Core: PE1's full re-derivation + PE2/PE3 audits stand; this pass re-derived
LEMMA W2-ID1's chain by hand (c = c₁^{e₁g₁} = ξ_f^{g₁}, z₁^{A₁e₁j} =
ξ_f^{−j}, w forced to 1 at j = 0, ξ_f^j = 1 on supp incl. the monic top —
sound) and re-verified the P2 anchor lines in the print (tex 1431/1433
Def-`t(i)` = (s − ℓu)/e arrangement; tex 1373 u_i = v_r(a_iφ_r^i); tex
1447 `rescoeff`; tex 1200–1201 construct child exponent (ℓu_j − 𝔰_j)/e
with 𝔰_j the ideal abscissa — all as the [r2, P2] brackets state). My own
recomputation from the committed JSON: 44 junction-levels = 16 r = 2 + 28
r ≥ 3 ✓; 22 walked + 6 SKIP, all 6 SKIPs byte-RED, walked split 12 RED /
10 GREEN (→ 18/10) ✓; recorded ξ ≠ 1 ⟺ byte-RED at 22/22 with 0
exceptions ✓; every below-r₀ junction byte-GREEN ✓; first-twist census
T2A/C/D/G = 3, T3A/C/D/E = 3, T3B/F = 4, I4B = 5, I4C = 3, T2B/E/F + I4A
none ✓; above-twist = exactly {T3A,T3C,T3D,T3E r = 4; I4C r = 4,5} ⟹ 38
proved-scope ✓; instance-warranted = exactly {I4A r = 5, I4B r = 5} ⟹
36 + 2 ✓; I4B ledger [(3,(1,1)), (4,(1,1)), (5,(−1,−1))] with r = 5
byte-RED ✓. Grade caps, fences, and open boxes internally consistent at
HEAD **except the three P1 residual surfaces**. Residual defects: P1 + P2
only.

## §F. Arc accounting (charge 5) — CONSISTENT AND TRUE except the footer

Header S-STATUS / §6.4 [r1]+[r2]+[r3] / §7 / §8 / §9 agree: composed
5463f2a → PE1 083adff (0C+2G+5m) → r1 8d5e3fa → PE2 79e796b (0C+2G+1m) →
r2 ffa1e57 → PE3 9bd938f (0C+1G minor) → r3 79d1d9c; counter 0/2, repair
rounds are not passes, PE4 = this pass, "PE4 next" at all three pointer
surfaces ✓. All hashes and dates verified against git ✓. Open boxes
W2-OPEN-1 + W2-OPEN-2 (carrying (OPEN-2a) + the [r3] converse flag) +
W2-BOX-1 + the §4.3 fence — count unchanged as stated ✓. Runner and both
artifacts byte-frozen through all three repair rounds ✓. The one
inconsistency is the footer dateline (P2).

**Ungraded observations (no defect grade):**
* (o-a) The [r3] flag inside W2-OPEN-2 attributes the whole "byte-DIFFERENT
  for r₀ ≤ q < r" clause to the identification's converse; strictly the
  q = r₀ instance is the converse and r₀ < q < r is the box's own
  persistence assertion. The operative marking covers all q (§ADJ).
* (o-b) §5.2 [r1, F1] block: "ABOVE r₀ the transported print keys and the
  harness keys are byte-DIFFERENT" — as a universal, this is the same
  unproved converse+persistence content (instance-true on the roster: my
  6/6 SKIP byte-RED recomputation); its attribution "(the persistent unit
  ratios of (iii)'s own wording)" inherits (iii)'s measured grade, and the
  block's conclusion (clauses 1–2 as proved do not apply above r₀) consumes
  only the ABSENCE of the byte-share warrant, which holds either way — so
  the conclusion is conservative. A "(roster instance; in general
  unproved)" qualifier would make it exact; candidate for the P1 sweep.
* (o-c) The counter-instance block cites "grt_w2_checks.py lines 135–164";
  `orbit_scan` spans 135–163 (`return out` at 163; 164 blank). Same figure
  PE3 used; content-true.
* (o-d) §6.2's W2-ID1 row: the statement column is correctly one-directional
  ("recorded ξ = 1 ⟹ byte-equal at m = 1 junctions"), but its appositive
  label "(the boundary identification, m = 1 case)" equates that forward
  half with the (two-sided) identification — the same residual vocabulary
  as P1's sites, weakest form (the exact statement is displayed right
  there). Candidate for the P1 sweep.
* (o-e) The W2-OPEN-2 [r3] flag says the byte-DIFFERENT clause "is …
  FALSE under the sealed scan's selection off-roster (the counter-instance
  recorded at LEMMA W2-ID1 above)". Precision: the recorded chamber has
  only 2 reads, so its top junction IS r₀ and the box's premise range
  r > r₀ is empty there — instantiating the premise clause's falsity
  strictly requires appending any third read (immediate: appending a read
  leaves all lower junction data unchanged, and at q = r₀ the keys are
  byte-equal as recorded). The flag's mathematical content — the clause is
  not valid in general under the sealed selection — is TRUE; only the
  parenthetical's cross-reference compresses this one trivial extension
  step. No defect.

## Repair queue implied (for the composer; I fix nothing)

R-P1 (one clause each, the r3 scoping applied at the missed surfaces):
scope §6.3(d)'s "proved only at m = 1 (W2-ID1)", the §5.2 (OPEN-2a) gloss's
"IS the identification … does NOT prove at m ≥ 2", and §6.4 [r2]'s "closes
the m = 1 slice of that identification" to the forward direction (optionally
also the o-b qualifier and the o-d appositive). R-P2 (one token): append
"; r3 2026-08-07" to the footer dateline. No other repair owed by this pass.

— PE4, GRTW2 acceptance arc, 2026-08-07.
