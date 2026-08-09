# GENHN passPE3 — third hostile pass (2026-08-09, at r3 HEAD)

**VERDICT: CLEAN — 0 CRITICAL + 0 GAP + 2 MINOR (+2 remarks).
Nothing at GAP-or-worse survived this pass's verification; the
clean count moves 0/2 → 1/2.** The r3's four repairs are each
verified at the arithmetic level (the item-(6) box's derived
data re-computed by hand AND extended by machine to a second
iterated key; the depth-split displays consistent at the three
charged sites; the (CS-3) rider's full-side scoping correct with
the PE2-P witness re-checked; the F3 sign identity re-derived at
two further genres; the F4 denominator verified against the supp
runner's `continue`). LEMMA GENHN-T(b)′ (i)–(iii) HELD at two
never-tested configurations — the FIRST e₂ = 3 tower genre and
the FIRST p = 3 tower σ legs with genuine η₂-letter (K₂ = F₉)
composed INERT/SPLIT — via a fresh instrument
(`genhn_pe3_fresh.py`, GREEN 176 checks / 0 violations on its
FIRST full run, 3 teeth incl. a fired floor tooth). The two
MINORs are display-precision residues around the held content:
(F-1) item (6)(α)'s witness sentence over-attributes the
intermediate development's one-sidedness to the "exact carry
cancellation" (refuted as a mechanism-description by a second,
cancellation-free iterated key, PARI-exact); (F-2) the passPE2-F2
scope word ("full inner sides") reached 3 of 4 echo sites — the
S9.1 box preamble and two same-species site phrasings still read
unscoped, each disambiguated within a few lines.

Target: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` at HEAD
(r3 = f985a39/ff66d59/08ec526/beadeeb; note byte-identical
beadeeb → HEAD, sealed runners untouched since r2 — verified by
git diff). Arc: [r1] → [e2] → PE1 (T(b) REFUTED) → r2 (T(b)′
PROVED) → PE2 (T(b)′ HELD, 2 coverage GAPs) → r3 (this target).

---

## FINDINGS

### F-1 — MINOR. [GENHN-TOW-1] item (6)(α): "TRUE at the witness
### by an EXACT CARRY CANCELLATION" over-attributes; the
### cancellation is witness-specific arithmetic, not the mechanism
### the general hole needs.

**Quoted claim** (item (6), S9.1): "(α) the level-by-level ascent
... needs the Φ′-adic development of Φ₃ to be ONE-SIDED of slope
κ₂ with residual a ψ₂-power. TRUE at the witness by an EXACT
CARRY CANCELLATION — Φ₃ = Φ′⁴ − 8xΦ′² + 16x² − 16Φ′, and the
x-overflow carry 16x² = 16Φ′ + 32 kills the −16Φ′ term exactly
... — but the genre-general carry-cancellation bookkeeping is
genuine Okutsu-optimality content, unproved here."

**The defect.** The displayed arithmetic is all correct
(re-computed: Φ₂² = Φ′⁴ − 8xΦ′² + 16Φ′ + 32, and k̂₀ = 16Φ′ kills
the carry term). But the cancellation is NOT what makes the
development one-sided: the would-be surviving b = 1 term 16Φ′
sits at dv 8 > 15/2 = the side height at b = 1 — STRICTLY ABOVE
the side either way (b = 1 pins have integer dv, the side height
there is half-integral: no b = 1 term can ever sit ON this side).
What the witness's one-sidedness actually rides is the carry
CONSTANT 32 landing exactly on the side endpoint (0,10) (without
it Φ′ | Φ₃). Machine confirmation (FR3): the SECOND iterated key
Φ₃ = Φ₂² − 16xΦ′ (u₃ = 23 = 4·4+2·1+5·1, n̂₂(23) = 16xΦ′,
gcd(23,2) = 1, κ₃ = 23/2 > 8) keeps its carry UNCANCELLED —
development Φ′⁴ − 8xΦ′² + (16−16x)Φ′ + 32, machine pins
(0,10),(1,8),(2,7),(4,0) — and is one-sided of slope 5/2 with
residual T² + 1 = ψ₂², carrier (8,1) with the FULL intermediate
ascent data exact by nfeltval (v_pr(x), v_pr(Φ′), v_pr(Φ₂)) =
(4, 10, 23), and its n = 16 leaf RAM(93) → {(16,1)} PARI-exact
on both routes (parse-gated at all three levels). So the general
(α) obstruction is carry terms CLEARING the side with the
constant landing exactly — which is still Okutsu-optimality
content, so the box's bottom line (one-sidedness unproved in
general) STANDS unchanged.

**Failure scenario.** A T(b)″ prover reads the box as "prove the
carries cancel exactly at general genres" and targets a FALSE
general lemma (FR3's key is a valid iterated key where they do
not cancel) — a wasted proof round. No σ or count is priced
through the box (item (6) is open), so nothing downstream moves.
Cure: one clause ("the carry terms clear the side — at the
witness they cancel exactly").

### F-2 — MINOR. The passPE2-F2 scope word ("full inner sides")
### propagated to 3 of 4 echo sites; three same-species phrasings
### still read unscoped (each locally disambiguated).

Enumerated sites (this is a scoped list, not a quantified claim):
1. **S9.1 [GENHN-TOW-1] preamble** (L1383–1386): "T(b)′ (S8
   annex) PROVES the composed carrier, the composed slot lemma
   GENHN-2′, the corrected leaf read with inner-μ₂ = 2 σ, and the
   stage-shadow faithfulness criterion" — no full-side scope word
   (the r3 added it at the GENHN.B (CS-3) rider, the corrected
   conditionality display, and S9.2 item 2b, but not here). The
   box's own item (4) declares partial sides OPEN six lines
   later, so the paragraph self-disambiguates — but preamble and
   item list read inconsistently as a pair.
2. **GENHN.B tower clause, [r3] depth split** (L311–312): "T(b)′
   is ONE composition step, so it carries the DEPTH-2 towers" —
   without the "(item (4) where the inner side is partial)"
   parenthetical its conditionality-display twin (L365–367)
   carries; the same sentence does box [GENHN-TOW-1] as a whole.
3. **The one-breath title-line rider** (L53–58, [r2]): "the
   composition FORMULA survives but its carrier is the COMPOSED
   KEY (LEMMA GENHN-T(b)′, S8 annex)" — not updated with the r3
   depth split (at depth ≥ 3 the carrier is item (6)'s unproved
   iteration; T(b)′ is one step). "Survives" (= not refuted)
   remains accurate; the citation is one-step-scoped by the annex
   itself.

**Failure scenario.** A reader citing site 1 or 2 alone prices a
partial-side depth-2 μ₂ = 2 leaf through T(b)′ — the PE2-F2
over-cover pattern — but unlike the r2 rider, none of these
sites carries a quantifier ("every tower leaf"), and each is
disambiguated within its own display (item (4) below; the boxed
[GENHN-TOW-1] in the same sentence; the S8 annex's FULL-side
setting line). Loud failure at use (the corrected reader refuses
partial-side developments — re-verified at PE2-P's n = 10
member by PE2's re-run this pass). Cure: two scope parentheticals
and one depth clause.

## REMARKS (no grade)

* **R1.** Item (6)'s derived Φ₃ grammar has a K₂-digit-lift
  clause ("k̂_t a dv₂-height ladder lift of c_t ∈ K₂ ... needs
  (ii)'s slot grammar") whose f₃ ≥ 2 branch is machine-unwitnessed
  ANYWHERE (the supp's three SUPP-C instances and this pass's FR3
  all have ψ₃ linear, k̂ a single ladder monomial). The box does
  not claim a witness for it — disclosed here as the natural
  target for the next depth-≥ 3 machine contact.
* **R2 (positive).** The T-FLOOR tooth fired: the below-floor
  FR1 member f = Φ₂² + 2Φ′ (p₀ = 13 < 43 = the composed-floor
  minimum) has PARI σ {(2,1),(10,1)} against the naive dictionary
  {(12,1)} — the first machine demonstration that (iii)'s
  tower-node-locus hypothesis (pins above the composed floor
  dv₂(Y₂) > e₂f₂u₂) is load-bearing for the leaf read's warrant,
  not bookkeeping.

## CLEAN CHARGES (attacked and held)

1. **Item (6)'s derived data at the witness** (attack 1).
   Re-computed by hand: n̂₂(21) = 16Φ′ = π⁴x⁰Φ′¹ with
   21 = 4·4 + 2·0 + 5·1, UNIQUE in range i < 2, b < 2 (mod-2 then
   mod-e₁ elimination per GENHN-2′, existence checked); Φ₃ =
   Φ₂² − 16Φ′ = Φ′⁴ − 8xΦ′² + 32 with pins (4,0),(0,10) on the
   slope-5/2 side, (2,7) above, residual T² + 1 = ψ₂²; e₃f₃ = 2
   with ψ₃ = T − 1, u₃ = 21, k̂₀ = n̂₂(21) consistent with the
   displayed Φ₃ := Φ₂^{e₃f₃} − Σ k̂_tΦ₂^{e₃t}; (β)'s floor
   arithmetic 21/2 > dv₂(x⁴) = 8 with the correct level-2
   analogue ([r1]: κ₂ > D′h). The supp citation verified at the
   file: genhnr2_supp.py (md5 51154c95…) L388–389 IS the
   PHI3/n₂(21) construction; SUPP-C output sigmas
   {(16,1)}/{(16,1)}/{(8,1),(8,1)} as cited, both routes, in the
   bit-reproduced artifact 664036bc…. The box claims NO more than
   derived: every general clause is marked unproved ((α)
   "unproved here", (β) "no proved provenance", "machine-witnessed
   TRUE ... and unproved").
2. **The depth-split displays, three sites** (attack 1b).
   GENHN.B tower clause, corrected-conditionality display, S9.2
   item 2b + the box's own trailer ("items (1)–(5) first live
   n = 8; item (6) first live n = 16") — mutually consistent. The
   R1 arithmetic re-derived: a depth-3 event needs an inner CS
   event inside the (μ₂, K₂) system, so μ₂ ≥ 4 (GENIND.A(IV)),
   inner side length e₂f₂μ₂ ≤ μ₁ (full OR partial), e₂f₂ ≥ 2
   (composite inner), hence μ₁ ≥ 8 and n ≥ e₁f₁μ₁ ≥ 16 with
   e₁f₁ ≥ 2 (composite outer); n = 16 attained (SUPP-C, FR3). So
   "depth 2 exhausts the tower genres at n ∈ {8, …, 15}" is
   sound, and item (6)'s "first live n = 16" is exact.
3. **The (CS-3) rider's r3 scoping** (attack 2). The rider now
   states (iii)'s proved perimeter (full side, e₂f₂μ₂ = μ₁)
   and routes partial sides to item (4) with the PE2-P witness
   quoted correctly (n = 10, genre (2,1,5), polygon
   (0,13)–(1,10)–(5,0), slope-5/2 side of length 4 < 5 carrying
   (T+1)²; the reader's loud refusal + PARI {(2,1),(4,1),(4,1)}
   match PE2's report and re-ran GREEN in PE2's bit-identical
   isolated re-run). Sweep of the tower-consuming sentences:
   the residual unscoped echoes are F-2's three enumerated sites,
   none quantified.
4. **The F3 sign repair at two further genres** (attack 3).
   old − correct = h(1 − (μ−j)(f₁−1)) re-derived symbolically;
   fresh instances: (1,3,2), h = 1, j = 0, i = 0: old 3 vs
   correct 6 (undershoot 3 = (μ−j)(f₁−1)h − h with 2·2 − 1);
   (2,2,3), h = 1, j = 1, i = 1: old 5/2 vs correct 7/2
   (undershoot 1 = 2·1 − 1). The [r3] text's coincidence clause
   ((μ−j)(f₁−1) = 1) and the retained f₁ = 1 "+h" clause both
   check; the genre-F instance (3 < 4) re-verified.
5. **The F4 denominator repair** (attack area). The supp runner's
   divergence loop carries `if fam == 'SUPP-C': continue` BEFORE
   the pin tally (verified at source); meta has 38 rows, 3
   SUPP-C → 35 compared, output line "35 pin rows ... (of 38
   tower rows)" — "35/35 COMPARED rows" is the honest figure and
   both [r3] correction sites (the (iv) clause and the table
   note) state it with the exclusion reason.
6. **T(b)′(i)+(ii)+(iii) at the FIRST e₂ = 3 configuration**
   (attack 4; FR1). Genre (2,1,6)→(3,1,2) over ℚ₂, u₂ = 7
   (κ₂ = 7/3 > D′h = 2, gcd(7,3) = 1), Φ₂ = Φ′³ − 8x: carrier
   (6,1) on BOTH oracle routes with v_pr(Φ′(ξ)) = 7 EXACT
   (first e₂ = 3 composed carrier ever tested); slot lemma
   exactness 40/40 direct nfeltval legs (classes 3a + 7b all
   distinct mod 6 — the no-tie branch as (ii) predicts at
   f₁f₂ = 1); dictionary at n = 12: RAM(43) → {(12,1)} (×2
   member shapes), INERT(44,22) → {(6,2)} (forced T² + T + 1),
   2SIDED(45,22) → {(6,1),(6,1)}, each + deep perturbation,
   8/8 members exact on both routes, disc ≠ 0 — first e₂ = 3
   entries of every branch.
7. **T(b)′(i)+(ii)+(iii) at the FIRST p = 3 tower configuration
   with η₂-letters** (attack 4; FR2). Genre (2,1,4)→(1,2,2) over
   ℚ₃, ψ₂ = T² + 1 irreducible /F₃, Φ₂ = Φ′² + 27: carrier (2,2)
   both routes, v_pr(Φ′(ξ)) = 3 exact; slot lemma at the
   WITHIN-CLASS branch (e₂ = 1, f₂ = 2 — slot classes NOT
   distinct mod 2): 30 random + 6 constructed tie legs
   (c·3⁵Φ′ + c′·3⁶x, both height 13) ALL EXACT by direct
   nfeltval — the η₂-independence physically at valuation level
   (first direct tie contact at f₂ = 2; the supp's SUPP-B touched
   this branch through pins only). Dictionary at n = 8 with
   GENUINE F₉ residual arithmetic: INERT via digit 2 + 2η₂
   (−d₀ = 1 + η₂ NON-square in F₉, robust to the ψ₂-root choice)
   → {(2,4)}; SPLITEQ via digit 2η₂ (−d₀ = η₂ = (1−η₂)² a
   square) → {(2,2),(2,2)}; RAM(13) and RAM-tie(13) → {(4,2)};
   2SIDED(15,7) → {(2,2),(2,2)}; all + perturbations, 10/10
   exact both routes. The square/non-square discrimination is
   the first composed-level residual decision over F₉ — PARI
   adjudicated it and the T-DICT-F9 tooth (both swaps) fired.
8. **The composed floor's warrant** (R2's content): the (iii)
   dictionary was additionally verified to FAIL below the floor
   exactly as the lemma's hypotheses demand (T-FLOOR fired) —
   the naive read off-locus is refuted by PARI, so (iii)'s
   perimeter is neither vacuous nor slack at this instance.
9. **The [r3] arc line's numbers.** 219/0 = 5+72+119+3+16+4
   (recomputed from the PE2 artifact); pins 4a28246e/10b685b0
   verified; "additive citations only, sealed artifacts
   byte-untouched" verified by git diff (r3 touches only the
   note; runners byte-identical since r2).

## MACHINE LEG (integrity)

* **Pins:** genhn_checks.py 637427dc… ✓, artifacts dd9edbea… /
  7d4a3e86… ✓, genhnr2_supp.py 51154c95… + output 664036bc… ✓,
  genhn_pe2_fresh.py 4a28246e… + output 10b685b0… ✓ (all as
  cited in S11.A + the [r2]/[r3] blocks).
* **Sealed battery isolated re-run** (fresh dir, 12-module import
  closure + 3 pinned jsons): **GREEN — 2,223,050 checks / 0
  violations, teeth 2/2/2/2/1, 448.3 s**; results JSON
  content-identical to the committed artifact except `elapsed_s`
  (448.3 vs 450.0); output txt timing-stripped diff EMPTY; the
  V p=2 diagnostic tail 1,216/349 reproduced deterministically.
* **genhnr2_supp.py isolated re-run:** exit 0, output
  BIT-IDENTICAL (md5 664036bc…), GREEN 147/0.
* **genhn_pe1_fresh.py isolated re-run:** exit 0, GREEN
  (0 violations; FR-D refutation tallies reproduced), output
  identical to the committed artifact.
* **genhn_pe2_fresh.py isolated re-run:** exit 0, output
  BIT-IDENTICAL (md5 10b685b0…), GREEN 219/0, 4 teeth.
* **Tautology audit (this pass's instrument):** predictions
  derived by hand in the docstring BEFORE the first run from the
  note's displayed formulas; PARI is the only oracle (route 1 =
  global factor + nfinit + idealprimedec; route 2 = factorpadic +
  per-factor lift); slot legs compare the formula against
  nfeltval directly; the teeth mutate the dictionary and the slot
  offset and demand refusal. No imports from any prior GENHN
  runner. cypari2 unavailable on this box — gp subprocess as in
  the prior instruments.

## FRESH ROUTE (disjointness)

`verification/openmath/genhn_pe3_fresh.py` (md5 f70d3d56…,
artifact b484e7fa…): **GREEN — 176 checks / 0 violations on the
FIRST full run (no smoke run, no reseal events), teeth
T-SLOT-E3 ×18, T-DICT-F9 ×2 (both swaps refused), T-FLOOR
fired.** Territory never touched by the battery (no tower leaf
rows), PE1 ((1,3,2) sweeps + (2,1,4) refutations), the supp
(outer-f₁ = 1, e₂ ∈ {1,2}, q = 2, u₃ = 21), or PE2 (outer-f₁ = 2,
boundary u₂, Q = 4 base change): FIRST e₂ = 3 tower genre; FIRST
p = 3 tower σ legs (all prior tower σ contact was p = 2,
incl. PE2's F₄-residue legs); FIRST f₂ = 2 composed INERT/SPLIT
with genuine η₂-letters (K₂ = F₉ square/non-square adjudication);
FIRST direct-nfeltval tie legs at the within-class branch; and a
SECOND depth-3 iterated key (u₃ = 23, carry-uncancelled) with
full intermediate ascent data. Not attempted (disclosed): e₂ ≥ 3
with f₂ ≥ 2 simultaneously; f₃ ≥ 2 third-stage keys (R1); d ≥ 2
ambients; inner μ₂ ≥ 3 (that is [GENHN-HE], out of scope).

## GRADE LINE

**passPE3 = CLEAN under the charge bar: CRITICAL ×0, GAP ×0,
MINOR ×2 (F-1 the item-(6)(α) carry-cancellation attribution;
F-2 the three enumerated unscoped echo sites). Clean count
0/2 → 1/2.** What this pass positively establishes: the r3
repairs are arithmetically sound where checkable and honestly
boxed where not; T(b)′'s proved clauses held at two genuinely
new configurations (e₂ = 3; p = 3/F₉) with the floor hypothesis
shown load-bearing; item (6)'s derived iterated-key grammar
extends to a second machine instance (evidence FOR the box's
content, against one word of its witness commentary). Repair
scope: F-1 one clause inside item (6); F-2 two scope
parentheticals + one depth clause — none moves a theorem,
a count, or σ. PE4 next; consumers unchanged (GENIND's
n ≥ 10 / n ≥ 16 inheritance stays an orchestrator fold, as
flagged in the [r3] arc line).
