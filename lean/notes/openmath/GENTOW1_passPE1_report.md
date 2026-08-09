# GENTOW1 passPE1 — hostile verification report

**VERDICT: NOT CLEAN — 1 GAP (F-1, the gauge-naive key-display
inheritance; machine-confirmed at an η ≠ 1 frame) + 2 MINOR. Counter
stays 0/2. Every owned mathematical surface EXCEPT the ĉ_t display
held under re-derivation; the machine leg is bit-exact and
non-tautological; the fresh route is GREEN 373/0 with all gauge
teeth fired.**

Target: `GENTOW1_PROOF_2026-08-09.md` at HEAD (composed 59d0350 →
5eca905, 2026-08-09 14:48–15:16). Protocol: quote-and-classify, fix
nothing. Verifier: fresh context, zero prior stake.

## F-1 (GAP — consumption seam, would be CRITICAL if the naive
## reading were pinned): the composed key's lift coefficients ĉ_t
## are the gauge-naive T(b)′ display; the note predates erratum
## 59c1966 and never pins the η^{W(t)} correction

QUOTES. S0: "Composed key Phi2 = Phi'^{e2f2} - Sum_{t<f2} chat_t
n(u2(f2-t)) Phi'^{e2t}" — ĉ_t is never defined in the note. S2
Step 1: "the weight-E2 graded layer = psi2's coefficients at the
side lattice (the T(b)' display...)". S2 Step 5: "the height-E2
residue under the coherent height-E2 normalizer is
(unit)·psi2(eta2(x0))". S6: "consumes LEMMA GENHN-T(b)'
(i)/(ii)/(iii) (GENHN accepted 2/2 at PE4)".

THE SEAM. GENTOW1's verdict commit is 5eca905 (08-09 15:16). The
GENHN dated erratum 59c1966 (08-09 20:13, from HETOW PE1 F-1) later
established that T(b)′'s DISPLAY of ĉ_t (plain lift of c_t) is
gauge-naive: the coherent-normalizer slot residue of the displayed
key is c_t·η^{−W(t)}, W(t) = ⌊(f₂−t)i(u₂)/e₁⌋, and the corrected
display is ĉ_t := lift(c_t·η^{W(t)}); the erratum instructs
"downstream consumers ... must transcribe THIS display". GENTOW1
consumed the pre-erratum display ~5 h earlier and carries no gauge
annex. Steps 1/3/5 of LEMMA GENTOW-1 and the frame of LEMMA GENTOW-2
all need "graded layer of Φ₂ = ψ₂ under the coherent normalizers" —
true at the CORRECTED key only.

FAILURE SCENARIO (machine-confirmed, `gentow1_pe1_fresh.py` @
6993b7c, output 225c6212). Frame F1: p = 3, Φ′ = x² − 6 (η = 2 ≠ 1),
(e₂,f₂) = (1,2), u₂ = 3, ψ₂ = Z² + Z + 2, μ₂ = 2, n = 8. Naive key
Φ₂ᴺ = Φ′² + 3xΦ′ + 54; corrected Φ₂ᶜ = Φ′² + 3xΦ′ + 108. With Φ₂
read as the naive display: (i) the key is not the composed carrier —
PARI ef(Φ₂ᴺ) = {(4,1)} ≠ {(2,2)} (twisted residual
ψ̃ = T² + T + 1 = (T−1)² over F₃, degenerate); (ii) GENTOW-1(d)
FAILS: at 20/20 scored primes of corrected-frame members,
nfeltval(Φ₂ᴺ) = 3·pr.e EXACTLY (no ψ-cancellation; ψ̃(η₂) = 2 ≠ 0),
while nfeltval(Φ₂ᶜ) > 3·pr.e strict at every row; (iii) members
built in the naive key's budget box read σ = {(8,1)} ≠ {(4,2)}, the
tRAM prediction — GENTOW-1(a)'s ⟸ direction is false at the naive
key. All five committed battery families sit at η = 1 (q = 2 with
Φ′ = x²−2; q = 3 with Φ′ = x²−3), where naive = corrected — the
sealed battery is structurally blind to this seam.

SCOPE (what survives — verified, not assumed). The note's operative
convention ("the same S4-cocycle convention as the entry lifts
chat_t", S3; "coherent normalization, wrap units included",
GENTOW-2(iv)) resolves to the corrected reading, under which every
proof step re-runs: the fresh route confirms floors, node pins,
field floor, refine transport (old pins (14,7) both alive at q = 3 →
new (19,11), σ {(4,2)} both oracles), and window content at the
corrected η ≠ 1 key — the BUDGETS are valuation-level and
wrap-immune exactly as HETOW PE3's gauge-invariance finding
predicts; the FRAME (key normalization, residual, σ) is gauge-live.
REPAIR SHAPE (not executed here): a dated gauge annex pinning
ĉ_t := lift(c_t·η^{W(t)}) (and the erratum pin added to S6's
conditionality stack line).

## m-1 (MINOR): prediction P-1 sealed but never scored

The sealed docstring preregisters "P-1 (KEY): Phi2 irreducible with
single prime (e,f) = (e1e2, f1f2); nfeltval...", but no runner row
scores the base keys' ef (GP-EF's 8 rows are the REFINED keys Kp
only), and S5's per-prediction list "What the scored rows ...
verified" silently starts at P-2. Content is indirectly covered
(GP-NODE valuations at members; fresh route scored ef(Φ₂ᶜ) = {(2,2)}
directly), but a sealed prediction with no scored row should be
disclosed as such. Failure scenario: none mathematical; seal-
discipline bookkeeping only.

## m-2 (MINOR): GENTOW-BOX-1's claimed retirement by GENTOW5 has no
## back-pointer at GENTOW1, and consumers should read layer 3's
## general-μ₂ conditionality through layer 1

GENTOW5 S1.5 declares "GENTOW-BOX-1 ... RETIRED as a mathematical
box; the residue is grade-only" with honest 0/2 conditionality
stated THERE; GENTOW1 at HEAD carries the box as live with no dated
cross-pointer (per the consumption-path convention this waits for
the hostile arcs, so this is hygiene, not error). Caution for
consumers: GENTOW-2 layer 3's image clause consumes (ii) (= layer
1), so at μ₂ ≥ 3 the BIJECTION inherits the graded-frame
conditionality too — GENTOW5 L56's "layers 2–3 are PROVED at general
mu2 in GENTOW1_PROOF S3" should be read with that inheritance (the
status-table phrase "general mu2 layer-1 via graded frame" names the
correct bottleneck).

## CLEAN CHARGES (attacked, held under independent re-derivation)

1. **Step 0 carry monotonicity (the hinge).** Both displays
   re-derived exactly: x-carry tail wt gain e₂(e₁g − (D′−c)h) ≥ 0
   from Φ′'s one side; Φ′-part strictly raised by u₂ > e₂D′h; lift
   terms exact at E₂ (n(m) wt = e₂m); two-directional rewriting
   closes; "wt ≥ μ₂E₂+1 per slot ⟺ v ≥ displayed floor" is exact
   ceil arithmetic (pin = +1 ⟺ e₁e₂ | (μ₂−j)E₂ − w, and the
   lattice-slot congruence makes wt ≥ μ₂E₂+1 auto-bump to
   μ₂E₂+e₁e₂, matching Step 3's one-digit-higher cancellation).
   Step 0 is VALUE-BLIND (heights only) — wrap-immune, unaffected
   by F-1. LEVEL-AGNOSTICISM: Step 0 as written is the two-level
   instance and claims nothing more; GENTOW5-D re-proves the
   general-depth statement with its own uniform displays and
   correctly cites Step 0 as the i = 2 instance — no consumption
   overreach on GENTOW1's text.
2. **The [pin] clause at e₁e₂-lattice slots.** Pin count per pinned
   height = f₁f₂ (two-step separation: unique (i,b) per class,
   × f₁f₂ within-class slots) — matches S1's read-off (ii) (one pin
   at f₁f₂ = 1; two at f₂ = 2, slots (0,0)/(1,1)). M > 0 always
   (E₂ − w ≥ u₂ − (e₁−1)e₂h > 0), so the "≥ 0" proviso is vacuous
   but harmless.
3. **Triangular-unimodular bijection incl. onto.** Unipotent in the
   x-degree filtration (monic division by Φ₂ then Φ′); image = box
   by Steps 2+3; onto via window cardinality + GENTOW-5(e)'s mod-π^N
   bijection; ROUNDTRIP 150 machine-side. Step 2's outer-grammar
   display re-derived (x-height ≥ u₂ + (μ₁−1)e₂D′h + 1 > n·e₂h) and
   the level-1/weight equivalence e₂·dvh + Ju₂ ≥ μ₂E₂+1 ⟺ pin
   strictly above the inner side is an exact integer equivalence.
4. **COR GENTOW-1.1 (the sharper depth-3 floor).** Re-derived: min
   side slope ≥ min_j ((μ₂−j)E₂+1)/(μ₂−j) = E₂ + 1/μ₂ > E₂, and
   E₂ = e₂f₂u₂ > e₂f₂e₂D′h = D₂e₂h strict by the [r1] floor. The
   sharpening over the box's conjectured κ₃ > dv₂(x^{D₂}) is REAL
   (strict at every legal frame) and TIGHT (the all-floors member
   realizes one side of slope exactly E₂ + 1/μ₂; witness FAM-A5:
   21/2 > 10 > 8 checks). Item (6)(β)'s discharge-into-item-(1)
   claim is scope-accurate; (6)(α) correctly kept boxed.
5. **LEMMA GENTOW-2 at μ₂ = 2.** (i)'s x-side bound
   lam − (e₂f₂−1)(u₂−e₂D′h) > D₂e₂h re-derived; layer-2 strictness
   (μ₂−j)lam + 1 checks; (iv)'s binomial display re-derived (q = 2:
   j = 1 pin dies, 2s = 0; q = 3: both pins) — all 8 refine-table
   rows recomputed by hand (lam values from the normalizer heights,
   old/new pins consistent); fresh route adds the first η ≠ 1
   refine row with both q = 3 pins and kills, plus wrong-flavor and
   wrong-height teeth at η ≠ 1.
6. **LEMMA GENTOW-5.** (a)'s first-band flavor geometry verified
   independently: at m = e₁e₂N the only out-of-window flavor is the
   w = 0 slot (w ≡ 0 mod e₁e₂ ∧ w > 0 ⟹ w ≥ e₁e₂ ⟹ in-window), so
   GENHN-2′-independence gives value-exactness; (b) string-end
   arithmetic; (c) the congruence; (d) via layer 2; (e) unipotence
   mod π^N. The scope remark honestly excludes the band trichotomy
   and BOX-4's extraction seams (item (4)).
7. **S1 tables.** All five families' floor tables, node floors,
   NODE-EQ anchors (16Φ′/32xΦ′/64x/64Φ′/729x), mutant bases
   (8/8/4/18/4 vs E₂ = 10/14/6/21/6), and key displays re-derived
   by hand from the constants — every entry exact.

## MACHINE LEG (integrity verified)

* Pins: runner md5 6df4b213... and output md5 25667bf6... both
  match the note's S5 figures at HEAD; seal commit 982abe7 and
  post-seal redisclosure 07f41e0 (15:12) precede the verdict run
  (15:16) as claimed.
* Isolated re-run (fresh /tmp copy, this pass): GREEN, 1,128
  checks / 0 violations, 5/5 teeth; output BYTE-IDENTICAL to the
  committed artifact (same md5), tally identical (NEC 350 ... TEETH
  5, sums to 1,128); 8 unscored diagnostics as disclosed.
* Tautology audit: NEGATIVE (no circularity found). The level-1
  entry gate computes the actual Φ′-adic development (dv(A₀) exact
  + pins vs the inner side) — decorrelated from the composed floor
  formula; NEC members are built by level-1 recipes, not from the
  floors; both σ oracles are genuinely distinct (factor+nfinit/
  idealprimedec vs factorpadic+liftall+ef); T-MUTFLOOR/T-BELOWNODE/
  T-REFWRONG/T-UNDERCUT are live teeth (wrong constants really
  enter the tested objects). Caveat recorded: the gate checks the
  polygon clause of 𝒯 only — the residual-ψ₂^{μ₂} clause is
  enforced by construction on NEC rows and by the σ oracle
  indirectly on REAL rows (no violation; noted for future
  instrument work).

## FRESH ROUTE (disjoint frames; sealed 9e9d994, run @ 6993b7c)

GREEN — 373 checks, 0 violations; teeth GAUGE-NODE ×20,
GAUGE-SIGMA ×2, REFWRONG ×2 all fired. Frame F1 = the program's
first η ≠ 1 tower-ENTRY contact (p = 3, Φ′ = x²−6, ord(η) = 2,
f₂ = 2, K₂ = F₉): floors/gate/strict-above/node pins at the
corrected key all green including 3 deep (v = 40) perturbations;
node oracle strict at 20/20 prime rows; NODE-EQ anchor (13, tRAM)
σ = {(4,2)} both oracles; SPLTAIL (16,7) σ = {(2,2)}×2 both
oracles; refine at η ≠ 1 green (see F-1 and clean charge 5). Frame
F2 = first e₁ = 3 tower frame (p = 2, Φ′ = x³−2, e₂ = 2,
e₁e₂ = 6 with the 3·2 factorization new vs FAM-C's 2·3): floors
(all six residue classes single-slot), gate, node oracle
(6·val(Φ₂) > 14·pr.e strict, 3·val(x) = pr.e, 6·val(Φ′) = 7·pr.e),
anchor (29, tRAM) σ = {(12,1)} both oracles, SPLTAIL (32,15)
σ = {(6,1)}×2. One instrument erratum (mine): the F2 SPLTAIL C₁ was
first transcribed at height 29 instead of 15 — redisclosed in the
docstring, fixed, prediction unchanged. NOT RUN (disclosed):
non-prime q (d = 2 ambient) — rnf cost; μ₂ ≥ 3 rows (GENTOW-BOX-1
scope).

## GRADE LINE

passPE1 verdict: **NOT CLEAN (1 GAP + 2 MINOR)** — the acceptance
counter stays **0/2**; the bar resets on the F-1 repair (dated
gauge annex transcribing the corrected ĉ_t display + erratum pin in
the conditionality stack). The note's mathematical mechanism held
everywhere I could break it EXCEPT the inherited display: at the
corrected key every owned claim survived hand re-derivation, an
isolated bit-identical machine re-run, and a two-frame fresh route
at the seam's live geography. Consumers (GENTOW3/5/6, HETOW) should
carry the F-1 caveat until the annex lands: cite GENTOW-1's budgets
WITH the corrected-key reading pinned.

— GENTOW1 passPE1 hostile verifier, 2026-08-09
