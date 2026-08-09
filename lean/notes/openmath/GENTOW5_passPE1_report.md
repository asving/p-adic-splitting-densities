# GENTOW5 passPE1 — HOSTILE VERIFIER REPORT

**VERDICT: NOT CLEAN — 1 CRITICAL + 2 GAP + 3 MINOR. Counter stays
0/2.** The CRITICAL is the gauge seam AT THE NOTE'S OWN DISPLAY:
DEF GENTOW5-1's composed key recipe is the gauge-NAIVE lift form
that GENHN's dated erratum (59c1966) corrected one level down, and
the fresh route machine-refutes THEOREM GENTOW5-B (a)/(b) at the
displayed recipe on a legal η ≠ 1 frame (naive key σ = {(4,1)} ≠
{(2,2)} = carrier; corrected key GREEN with exact ladder). TARGET 1
(THEOREM GENTOW5-A + A0/A1, the GENTOW-BOX-1 retirement) is
seam-correct and SURVIVES this pass's attacks. Machine leg: seal
verified, both artifacts re-run isolated BIT-IDENTICAL (86/0 exact,
92/0 full, exit 0). Fresh route (3 disjoint probes, 15 checks / 0
violations): the seam tooth fired; the grammar itself passed its
first slack-floor depth-3 chain and its first p = 3 depth-3 chain,
both on dual oracles.

**Pass:** GENTOW5-passPE1, fresh context, zero prior stake,
2026-08-09. **Target:** `GENTOW5_PROOF_2026-08-09.md` @ HEAD
(composed 9212530..d3389e2, 15:36–15:53). Protocol:
quote-and-classify, fix nothing. Context read: the note in full;
GENHN dated erratum (59c1966) + HETOW r1 (5335ae3); GENTOW1_PROOF
head/S0/S2 Step 0 + its r1 gauge annex commit (477b1b1);
GENTOW2_PROOF B-2/B′ passages ([r1]/[r2] state); GENTOW1_passPE1
report; HE7 annexpass 1+2 verdict heads; `gentow5_checks.py` in
full + sealed-vs-HEAD diff.

TIMELINE FACT (drives findings 1, 2, 4): the note was composed
15:36–15:53; the gauge seam landed 20:12–20:14 (HETOW r1 + GENHN
erratum); GENTOW2 r1/r2 landed 20:03–23:20; GENTOW1 r1's gauge
annex landed 23:26. GENTOW5 is the ONLY note of the tower campaign
not yet folded for the seam.

---

## S1. FINDINGS

### F-1 CRITICAL — DEF GENTOW5-1's key recipe is the gauge-naive
### display; GENTOW5-B (a)/(b) FAIL at it on letter-live frames
### (machine counter-instance, this pass's fresh route)

Quote (S2.1, THE COMPOSED KEY RECIPE):

    Phi_{i+1} := Phi_i^{e_{i+1} f_{i+1}}
                 - Sum_{t < f_{i+1}} khat_t * Phi_i^{e_{i+1} t},
    khat_t := lift_i(c_t; u_{i+1}(f_{i+1} - t))   (0 if c_t = 0),

and "At i = 1 this is T(b)''s Phi2".

This is the plain-lift (gauge-naive) prescription. GENHN's dated
erratum (59c1966, post-dating this note by ~4.5 h) corrects exactly
this display one level down: the normalizer monomials are not
multiplicative — n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^h)^{W(t)},
W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋ — so the naive coefficient's slot residue
is c_t·η^{−W(t)}, and the corrected lift is ĉ_t :=
lift(c_t·η^{W(t)}). At i ≥ 2 the analogous correction is the
vartheta/tau_i-telescope twist — the very units the note's OWN
S1.2/S2.3 machinery tracks in the reading direction but the recipe
does not apply in the building direction. "At i = 1 this is T(b)''s
Phi2" now points at an errata'd display (GENTOW1 r1, 477b1b1,
pinned the corrected ĉ_t at every consumption site; GENTOW5 has no
such pin).

Consequences inside this note: THEOREM GENTOW5-B (a)
"R_{nu_i}(Phi_{i+1}) = psi_{i+1}" and (b) "the recipe's roots ARE
depth-(i+1) node points" are FALSE at the displayed recipe on
frames with a live wrap letter and f_{i+1} ≥ 2. Verified this pass
(fresh instrument `gentow5_pe1_fresh.py`, FR-1 = the erratum's
frame X transported into the note's own letters): p = 3, Phi_1 =
x²−6 (η = 2), stage (e₂,f₂) = (1,2), u₂ = 3, psi₂ = y²+y+2 — a
frame satisfying every DEF GENTOW5-1 hypothesis (properness 2,
floor 3 > 2, gcd = 1, c₀ ≠ 0). The note-displayed recipe gives
Phi₂ = Phi₁² − 6x·Phi₁ − 27 (khat₁ = 2·n̂(3) = 6x, khat₀ = 1·n̂(6)
= 27): PARI σ = **{(4,1)}** — f = 1, so R(Phi₂) cannot be the
irreducible deg-2 psi₂ and no root carries a psi₂-root residue
class. The corrected key Phi₁² − 6x·Phi₁ − 54 (c₀·η^{W(0)} = 2,
W(0) = 1) is the carrier: one deg-4 factor, σ = (2,2),
nfeltval(Phi₁) = 3 exact. Failure scenario: any depth-r consumer
instantiates the recipe at a letter-live frame (η ≠ 1 with
f_stage ≥ 2, or deeper vartheta ≠ 1) and (a)/(b) — hence (c)'s
entry-ladder ascent, (d)'s refine target, and (e)'s node corollary
AT THAT KEY — read off the wrong object.

Blindness of the committed battery (disclosed nowhere in S6's
coverage box, which predates the seam): CHECK-B is q = 2 (η = 1
forcibly, all K_i = F₂ — seam-blind, as the charge anticipated);
CHECK-A's only η ≠ 1 frame (A-2/A-4, p = 3, η = 2) has f₂ = 1,
where W ≡ 0 and naive = corrected. The seam axis is absent from
GENTOW5-BOX-A's named coverage gaps.

Scope fence (what F-1 does NOT touch): TARGET 1. S1's THEOREM
GENTOW5-A works in the READING direction at a single event height
(θ₁ = 1 — the two conventions coincide there, stated correctly at
S1.3), and LEMMA GENTOW5-A1 is the seam-correct dictionary (the
convention tooth T-A4W is its machine leg). The depth-4 witness
computations are exact and correct as instances (naive = corrected
at q = 2). Repair shape (not executed here): the GENTOW1-r1
pattern — a dated pin restating khat_t := lift_i(c_t · twist_t; ·)
with twist_t the S2.3 step-(3) telescope unit, + a letter-live
recipe row in the battery (FR-1 of this pass is exactly that row).

### F-2 GAP — GENTOW5-B (a)'s (B-2) leg rests on the y → εy
### fallback that its own source note has since deleted as FALSE

Quote (S3 (a)):

    (B-2 at level i) ... a fixed-unit mismatch only re-parameterizes
    psi_{i+1} (y -> epsilon*y), preserving
    monic-irreducible-of-degree-f_{i+1} and every clause consumed;
    the robustness argument is verbatim.

GENTOW2 r1 (dd44d20, post-dating): "**F3 (GAP, false fallback
clause) → CURED.** The y ↦ εy sentence is deleted; the corrected
clause displays the true transformation law (B′(5): R = y^{f₃} −
Σ u(β_t)c_t y^t), the digit re-parameterization c_t ↦
u(β_t)^{−1}c_t ... the verifier's F₄ counter-instance ..." — the
unit family is per-grade u(β_t), not a single ε, and the ε-form has
a displayed counter-instance. Moreover GENTOW2-B′ re-attributes B-2
itself ("u = 1 at each grade the recipe uses") as FIRST MADE THERE,
**disclosed-not-derived**, supported only on letter-dead geography
(f₁ = 1, q = 2, z₁ = 1 witnesses), and states explicitly:
"GENTOW5-A1 checked and shown repo-internal (its ϑ_t compares two
repo conventions; it cannot supply the cross-frame u)." So (a)'s
level-general key certificate consumes (i) a deleted-as-false
argument form and (ii) an underlying disclosure that is open even
at level 2 — and this note's own A1 cannot close it. Failure
scenario: a grade-varying u(β) family at an f ≥ 2 stage makes the
recipe's residual a u-twisted polynomial; irreducibility of
psi_{i+1} no longer transfers by any single-ε substitution, and
(a)'s "= psi_{i+1}" claim silently changes content. (Distinct from
F-1: F-1 is the repo-internal wrap seam; F-2 is the repo↔FGMN
dictionary leg.)

### F-3 GAP — LEMMA GENTOW5-D: the top-grid weight is undefined,
### and the strictness clause contradicts the lemma's own claimed
### i = 2 instance

The weight display defines interior coefficients exactly but ends
"+ J_i * E-part as applicable at the top grid" — never defined. The
proof prices every key-part uniformly: "the Phi_{j+1}-part has wt =
(ehat_i/ehat_{j+2}) u_{j+2} > ... STRICT by the floor chain at
j+1". For the TOP carry (j = i−1) this reads the top variable at
weight u_{i+1}/e_{i+1} — not the stated "E-part", non-integer, and
its strictness consumes floor rung i; at the top grid of a depth-r
tower (i = r) rung r references u_{r+1}, which is EVENT data, not
tower data (the statement's floor chain supplies rungs only through
the stages that exist). The note's claimed instance ("GENTOW-1's
Step 0 is the i = 2 instance") prices that same carry the OTHER
way: GENTOW1_PROOF S2 Step 0 has "the Phi2-part at weight E2
exactly" — PRESERVED — directly contradicting GENTOW5-D's blanket
"the key-part of each carry strictly raises it". The lemma is
repairable (E-part := E_i, top key-part weight-preserving, strict
clause restricted to interior carries — nondecreasing is all any
named consumer uses; the flow-up strictness in GENTOW5-A Step B and
S3(c) comes from lam > E separately), and the floor-chain induction
DOES close under that convention (audited: x-carry = rung 1,
interior Phi_j-carries = rungs 2..i−1, all in the datum; S3(e)'s
self-feeding is non-circular since the theorem assumes the full
chain and (e) only shows it propagates at leaves). But as displayed,
statement and proof disagree at the top carry. Failure scenario: a
reader instantiates "strictly raises" at the top carry of the
witness chain (e.g. Phi_3² → Phi_4-part at grid 4) with E-part =
E_4 = 170: wt(Phi_3²) = 2·85·2 = 340 → Phi_4-part 170·2 = 340 —
equality, not strict; any downstream argument leaning on that
strictness (none found in THIS note — checked) would be unsound.

### F-4 MINOR — the HE7-ANNEX-R grade-cap pin is stale (moot in the
### conservative direction)

S2.3/S3/S6 pin LEMMA GENTOW5-C's precedent as "POST-RATIFICATION,
UNPASSED (annex grade)" and S6 declares "THE GRADE CAP FOR DEPTH
>= 3 CLAIMS IS THIS PIN plus this note's arc". Since composition,
HE7's annex stack was ACCEPTED 2/2 (HE7_annexpass_report CLEAN 1/2;
HE7_annexpass2_report CLEAN — "the annex stack is ACCEPTED 2/2",
with R1-b/R1-c's fresh-route probes GREEN). The pin claims WEAKER
support than the truth, so nothing consumed is at risk; the
orchestrator's dated fold should re-word the cap (the remaining
depth ≥ 3 cap is this note's own arc + the F-1/F-2 seam).

### F-5 MINOR — P-C3's chk lines are weaker than the sealed
### prediction

Docstring P-C3 predicts "one deg-4 factor with e=4" at both refined
keys; the code asserts only `"C3a nfactors=1" ... count("deg=4")>=1`
and `"C3b nfactors=1"` — e = 4 (and C3b's deg) are printed to the
artifact but never machine-asserted. The artifact lines (`C3a/C3b
... e=4 f=1`) are quoted in the note's S5, so the values were
human-verified; instrument-strength defect only.

### F-6 MINOR — the PARI-free route's standalone strength is
### overstated by one clause

S4.2 (P-C): "infeasibility disclosed, not fatal (P-B4 is the exact
witness either way)". v₂(Res(f32, g)) certifies Σ_{roots} v(g(ξ))
(32·v only GIVEN one prime over 2); per-root exactness of the
ladder needs the single-prime read — which is the PARI leg (C1/C2)
or the polygon theory under witness. With C1/C2 GREEN the composed
record is sound as claimed ("two independent routes" is fair for
the record AS RUN); only the counterfactual "either way" clause
overstates. No live defect.

---

## S2. CLEAN CHARGES (attacked and survived)

* **THEOREM GENTOW5-A + A0 + A1 (TARGET 1).** A0 re-derived (graded
  division ring; homogeneous invertibility from the valuation
  identity). Step A re-derived: per-term heights (j−k)λ + (μ₂−j)λ
  match, the substitution identity is binomial-transient and
  char-free, w = ι(s) legitimately via θ₁ = 1; Step B's flow-up
  pricing (μ₂−k)λ − E₂ > (μ₂−k−1)λ from λ > E₂ checks; A'(i)'s
  reverse-transport residue binom(μ₂,j)(−w)^{μ₂−j} sign-checked.
  A1's telescope ϑ_{t+1} = ϑ_t·res(τ(tλ, λ)) and the two-wrap
  letters consume accepted pins only (GENHN S4 z-letter,
  T(b)'(iii)/(T22)); the convention-consequence paragraph (why
  μ₂ = 2 batteries never saw the twist) is honest and correct. The
  A-row kills (first μ₂ = 3 anywhere, incl. char 3 and K₂ = F₄) and
  the convention tooth T-A4W verified in the committed artifacts +
  re-run. GENTOW-BOX-1's retirement stands AT DEPTH 2 as stated.
* **LEMMA GENTOW5-C's transport table.** The four-clause
  instantiation ((a)–(d)) is coherent; the residue display carries
  the ϑ_t twists (seam-correct in the reading direction); the
  tower-vs-HE7-base remark correctly consumes J-D0 and correctly
  refuses mid-argument system changes (HE7-T-BADTWIST named).
* **S3 (e).** Convexity two-liner re-derived; the telescoping
  E_{i+1} > D_{i+1}(ehat_{i+1}/e₁)h checked (equality only at the
  base rung); non-circularity of the self-feeding chain audited
  (F-3's caveat aside, the induction closes).
* **S2.2 worked pins.** n̂₃(85) = 2⁸·Phi₂ and n̂₂(21) = 16·Phi′
  re-solved by hand; this pass's fresh instrument re-implemented the
  n̂-recursion independently at three NEW chains and every derived
  normalizer was confirmed by exact PARI ladders.
* **S4/S5 arithmetic.** Floor chain, side heights, first-live
  n = 2^{r+1}, T-B1's drain factorization (Phi₂² − 16Phi₁ = Phi₃
  hits the key relation) all re-derived; the 86-check count
  re-derived from the code (34 A + 52 B); the T-A1W run-1 repair is
  exactly the committed diff and matches its disclosure.

## S3. MACHINE-LEG INTEGRITY

* **Pins:** runner md5 5fa684c7... = note's claim; artifacts
  dc499a49... (exact) and 839a8660... (full) = note's claims.
* **Seal:** `git diff 4b279a7..HEAD` on the runner = ONLY the
  disclosed T-A1W membership fix + docstring disclosure (commit
  31357eb, pre-re-run, no prediction changed) — seal discipline
  honest.
* **Isolated re-run** (/tmp copy, this pass): exact leg 86/0 exit
  0, full leg 92/0 — both outputs BIT-IDENTICAL to the committed
  artifacts (diff empty).
* **Tautology audit:** predictions are hand-derived docstring
  constants; the resultant leg (fraction-free Bareiss) and the gp
  leg are mutually independent and independent of the slot-weight
  engine; kill-checks read a different object (refined development)
  than pin-checks. Weakness = F-5 only.

## S4. FRESH ROUTE (disjoint; `gentow5_pe1_fresh.py`, 15/0)

Fresh code (own poly arithmetic + exact-fraction Sylvester;
oracles: integer resultants + gp factorpadic/nfinit/idealprimedec/
nfeltval — both oracles wherever σ is claimed):
* **FR-1 seam probe at the note's recipe** (p = 3, η = 2, f₂ = 2):
  corrected key = carrier, σ (2,2), nfeltval(Phi₁) = 3 EXACT; the
  note-displayed naive key σ = {(4,1)} — **the F-1 tooth fired.**
* **FR-2 slack-floor depth-3 chain, q = 2** (u = 7, 31, top 125 —
  rungs 1–2 slack by 3; the first non-tight-floor witness anywhere;
  also the first composite-monomial top normalizer, n̂₃(125) =
  1024·Phi₁Phi₂): resultant ladder (8, 28, 62, 125) and Phi₃ ladder
  (4, 14, 31) EXACT; PARI σ (16,1), nfeltval ladder EXACT — the
  floor chain's inequality direction carries slack. TOOTH: the
  floor-BREACH mutant u₃′ = 27 < 28 splits, σ {(2,1),(6,1)} —
  caught.
* **FR-3 p = 3 tight depth-3 chain** (u = 5, 21, top 85; first
  depth-3 contact off q = 2): resultant ladders (8, 20, 42, 85) /
  (4, 10, 21) EXACT; PARI σ (16,1), ladder EXACT — the grammar's
  arithmetic is char-robust where its binomial coincidences are not.

## S5. GRADE LINE

NOT CLEAN: 1 CRITICAL (F-1) + 2 GAP (F-2, F-3) + 3 MINOR (F-4, F-5,
F-6). Counter stays 0/2; a repair round (gauge pin on the recipe +
(B-2) re-point to GENTOW2-B′'s true law + the GENTOW5-D top-grid
convention + the stale annex-pin fold) is owed before PE2. TARGET
1's content and the depth-4/depth-3 witness records are not at
stake in F-1..F-3; the LEVEL-GENERAL claims of TARGET 2 are, at
letter-live frames, until the recipe display is repaired.

Verifier artifacts: `verification/openmath/gentow5_pe1_fresh.py` +
`gentow5_pe1_fresh_output.txt` (committed with this report).
