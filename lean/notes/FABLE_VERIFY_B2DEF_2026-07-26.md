# FABLE (fresh-instance) adversarial verification of §B2-DEF — 2026-07-26

Target: `MOVES_2026-07-24.md` §B2-DEF (lines ~1856–2545), read against accepted
§0 (Facts A/B), §A, §B1. Verifier: Claude (Fable), fresh context, independent of
the Codex pass chain (passes 9–21). Method: quote-and-classify; CRITICAL ERROR
vs JUSTIFICATION GAP; no fixes. Pass records read only AFTER forming my own view.

## Status of this document

- [x] Skeleton created
- [x] Independent read of D.0–D.7 (findings below)
- [x] Independent read of D.8–D.12 (findings below)
- [x] Concrete trace 1 (configuration chosen by me)
- [x] Concrete trace 2 (configuration chosen by me)
- [x] Cross-check against pass records 9–21 (live-text drift check)
- [x] Verdict

## Findings (numbered; classification in header)

(to be appended)

## Traces

(to be appended)

## Pass-record drift check

(to be appended)

## Verdict

(to be appended)

## Findings (independent read, BEFORE consulting pass records 9-21)

### F1. JUSTIFICATION GAP (minor, false sub-claim, conclusion survives) — D.4 ROOT case
Quote (D.4): "ROOT: on the initial cluster (non-lead coefficients ≡ 0 mod p, key x,
w(x) normalized to 0), every side has slope ≥ 1 > 0."
The claim "slope ≥ 1" is FALSE: f = x² + px + p is an initial cluster (f̄ = x²) whose
polygon has the single side (0,1)–(2,0) of slope 1/2 < 1. What (I-aug) needs at the
root is only λ > w(x) = 0, which holds (all sides of an initial-cluster polygon have
slope ≥ 1/n > 0). Chain survives; the stated bound is wrong.

### F2. JUSTIFICATION GAP (bookkeeping misstatement) — D.4 closing sentence
Quote (D.4): "It is consumed exactly once: D.7(ii)'s strict-depth step."
False as a DAG statement: (I-aug) is also consumed in D.5's (S6b) range check ("h >
e·w_prev(Φ) ≥ w_prev(Φ) by (I-aug) at the current read"), in D.7(viii)'s recursion
("> w_prevprev(Φ_prev) by (I-aug) at the PREVIOUS read") and its CONSUMERS clause
(items (i)-(ii)), and in D.9(c) ("by (I-aug), every read of the child polygon has
slope > w_r(Φ_{r+1})"). Harmless to the math; wrong as stated.

### F3. JUSTIFICATION GAP (load-bearing counting bridge is a sketch) — D.3(e)(ii)
Quote: "pinning the residual jet of B at the side heights (the values a stratum
reads) is, in these coordinates, a UNITRIANGULAR system of digit equations — each
equation pins one digit coordinate as an F-polynomial function of strictly earlier
coordinates (the accumulated affine carries are exactly the unitriangular part and
never spoil solvability-per-coordinate)."
This is the ONLY bridge from residual conditions to mass counts (consumed by D.8's
"Counts" step and by D.11's second equality), and it is asserted at paragraph level:
(a) no proof that the map {stratum condition} → {pinned digit coordinate} is
INJECTIVE (two jet conditions must never pin the same digit coordinate); (b) the
identification "one F'-digit of a Ĉ-coefficient = one block of g·g_prev·…·f₀ base
digit coordinates" (needed so that "alphabet size" in D.11 is well-defined and the
factors multiply) is implicit; (c) the ordering ("strictly earlier") mixing tower
level, height, and slot is not displayed. I believe the claim (Fact A iterated does
supply it), but as written this is a gap, not a proof.

### F4. JUSTIFICATION GAP (recursion described, not proved) — D.8 (TRANSPORT)
Quote: "DOWNWARD: C_μ := (anchored c_μ) mod ψ; for j > μ, C_j := (anchored c_j +
carry_j) mod ψ, carry_j := the accumulated ψ-overflow of the terms below j — each
C_j a deterministic F-polynomial function of the parent slot data".
Two unproved sub-points: (a) the individual anchored slot terms z^{−a}c_j need not be
z-POLYNOMIALS (a = ord_z of the SUM; bottom z-coefficients of distinct slot terms can
cancel), so "the accumulated ψ-overflow" must be defined on Laurent data — workable
(z̄ is a unit mod ψ) but not displayed; (b) the UPWARD inversion fixes each c_j from
its congruence class "once its z-support base is fixed" — the support window of c_j
(positions p_j..p_j+g−1) is indeed forced, but the sentence never verifies that the
downward map's output (C_j, plus the anchor a) determines the carries uniquely on the
way back up (it does — same greedy recursion — but this is asserted, not shown).
Assume-and-continue: downstream use (D.11 pinned-digit count invariance) survives.

### F5. JUSTIFICATION GAP (wording that contradicts the construction) — D.7(iii)
Quote: "its value group is renormalized to ℤ (S1')."
No renormalization is possible or needed: the value group of w' as defined IS ℤ
(coefficient weights fill e'·(cofinite subset of ℤ) whose differences generate e'ℤ,
and gcd(e', h') = 1 adds h'). If "renormalized" were read literally (rescale w'),
every scale conversion downstream (e'-stretch, h', D.9) would break. As read
charitably (= "and it is ℤ"), correct; the word is a landmine, flagged.

### F6. JUSTIFICATION GAP (citation inaccuracy) — D.2 base (S4)
Quote: "L = F[π^{±1}, y^{±1}] (§A.2's accepted Laurent localization)".
§A.2 (accepted) inverts only π: "localize — gr A ≅ F_Q[π, y] ↪ F_Q[π, π⁻¹, y] =: L".
The base stage here also inverts y (per D.0's "Y adjoined separately"). The further
localization is harmless (graded domain), but the parenthetical cites §A.2 for a ring
§A.2 did not construct. Cosmetic-to-minor.

## Traces (configurations chosen to be ABSENT from all pass records)

### Trace 1 — increment machinery at p = 5, (e,h) = (2,3), ψ = z²+2, Bézout (s,t) = (2,−1)
Base stage: key φ = x, F = F₅, w = min(2v(aᵢ) + 3i); T = π²y^{−1}, z = y²π^{−3}.
- D.3(b): R(x) = y·T^{−3} = y⁴π^{−6} = z². Matches z^s = z². PASS.
- S5: B = p^v·u: R(B) = ū·π^{v−4v}y^{2v} = ū·z^v = ū·z^{−t·v}. PASS.
- D.5 standard lift for ψ = z²+2 (irreducible /F₅: 3 ∉ squares{0,1,4}; ψ₁ = 0 slot
  ABSENT): Φ̂ = x⁴ + 2p⁶ (t₀ = 2p⁶: parent weight h(g−0) = 6, scalar 2). Predicted
  R(Φ̂) = z^{m̂}ψ, m̂ = −thg = 6. Direct: R(x⁴) = z⁸, R(2p⁶) = 2z⁶, distinct
  exponents, sum z⁶(z²+2). PASS. w(Φ̂) = ehg = 12. PASS.
- D.8 at μ = 1: f = Φ̂ + p⁷x. Minimizing φ-slots {0,4} (weights 12,17,12 — anchor
  congruence 0 ≡ 4 mod 2 PASS); R(f) = z⁶ψ, ord_ψ = 1, a = 6. Φ̂-development
  (B₀,B₁) = (p⁷x, 1): (BOX) w(B₀) = 17 > 12 PASS; (VERTEX) 0 + 12 = 12 PASS,
  dig'(B₁) = z̄^{−m̂}·(z⁶ mod ψ) = z̄^{−6}z̄⁶ = 1 = R(1) mod ψ. PASS.
- Lemma DIV with a REAL division: B = x², B″ = x³ (∈ Ĉ). x⁵ = x·Φ̂ − 2p⁶x:
  Q = x, R_dev = −2p⁶x. w(R_dev) = 15 = 6 + 9 EXACT. F' = F₂₅ = F₅[z̄], z̄² = 3:
  dig'(x²) = z̄⁴ = 4; dig'(x³) = z̄⁶ = 2; product 8 = 3. dig'(R_dev) = −2·z̄⁸ =
  −2·16 = 3. PASS. Full identity (ii) with δ₁ = 1: z⁴·z⁶ = z²·z⁶ψ + (−2z⁸) =
  z^{10} + 2z⁸ − 2z⁸ = z^{10}. PASS (the Q-term genuinely fires and cancels).
- TRANS spot-check at (e',h') = (1,13) (I-aug: 13 > w(Φ̂) = 12): V' = in(p)²in(x)^{−1}
  has w'-degree 2·2−3 = 1 = e' PASS; S5' scalar of x²: R'(x²) = class of x⁸p^{−12} =
  z^{16}z^{−12} mod ψ = z̄⁴ = 4 = dig'(x²), position 0 (t' = 0). PASS.

### Trace 2 — recentering with a > 0 AND a co-factor root, p = 3, base (e,h) = (1,1)
Key x, F = F₃, w = min(v(aᵢ) + i), T = π, z = yπ^{−1}, R(x) = z (s = 1).
f = x⁴ + 2·3x³ + 2·3²x² + 3³x + 3⁵: on-line digits (slots 1..4) = 1, 2, 2, 1; slot 0
strictly above the line (v = 5 > 4). R(f) = z⁴ − z³ + 2z² + z = z(z−1)²(z−2) in
F₃[z]. Stratum at ψ' = z − c̃, c̃ = 1: μ = 2, anchor a = 1, co-factor h(z) = z−2,
h(1) = −1 ≠ 0. Recentering t = 3 (v = 1 = λ″... side value at slot 1; dig = 1 = c̃),
Φ' = x − 3.
- D.10 predicts R'(f) = R(f)(z'+1) = (z'+1)z'²(z'−1) = z'⁴ − z'²; a' = μ = 2;
  vertex digit = c̃^a·h(c̃) = −1; R'_anch = (z'+1)(z'−1).
- Direct Taylor at 3: f(3) = 729 (v = 6 > 4: slot-0 BOX PASS); f'(3) = 405 = 3⁴·5
  (v = 4 > 3: slot-1 BOX PASS — μ = 2 vanishings both exact);
  f''(3)/2 = 126 = 3²·14 (v = 2 = line: VERTEX digit 14 ≡ −1 mod 3 PASS);
  f'''(3)/6 = 18 (v = 2 > 1: transported slot-3 digit 0 — matching the z'³
  coefficient 0 of R'(f), a slot LEAVING the minimizing set under transport PASS);
  slot 4: monic, digit 1 PASS. v'(f) = min(6, 5, 4, 5, 4) = 4 = v(f): v = v' PASS.
- Note: this trace also confirms the polynomiality resolution at e_read = 1 stages
  (R(f) has only slots j ≥ 0 at position j, so ord_z R(f) = a ≥ 0 and the
  substitution z = z'+c̃ of a POLYNOMIAL is well-typed; at a < 0 the display
  "(z'+c̃)^a" would leave F[z'^{±1}] — I checked that a < 0 is IMPOSSIBLE at
  e_read = 1 stages, which is the only place D.10 is invoked; the text nowhere
  says this, see F7 below).

### F7. JUSTIFICATION GAP (unstated well-typedness fact) — D.10 substitution display
Quote (D.10): "The anchored display: on the stratum R(f) = z^{a}·(z − c̃)^{μ}·h(z)
(ψ'-order μ, anchor a, ψ' ∤ z^a h): the primed polynomial is
(z' + c̃)^{a}·z'^{μ}·h(z' + c̃)".
For a < 0 this "primed polynomial" is NOT an element of F[z'^{±1}] ((z'+c̃) is not a
unit there), while R'(f) intrinsically IS one — the display would be ill-typed. It
is rescued by a fact the text never states: at an e_read = 1 stage T is
coefficient-pure and all digit positions are 0, so R(f) = Σ_{min j} c_j z^j has
ONLY non-negative z-exponents, forcing a = ord_z R(f) ≥ 0. One sentence is missing;
with it, the display is exact. (Similarly D.8's "z^{−a}R(f) ∈ F[z]" at general
stages needs a = ord_z ≥ min position — true by definition of ord_z of a Laurent
polynomial, fine there.)

## Pass-record drift check (records 9–21 read AFTER the independent pass)

Method: every recorded repair (pass 9 findings 1–10; pass 10: 1–6; pass 11: 1–6;
pass 12: 1–4; pass 13: 1–3; pass 14: 1–3; pass 15: 1; pass 16: 1–2; pass 18: 1;
pass 19: 1) was checked against the live D.0–D.12 text. Result: all repairs ARE
present in the live text in their FINAL form (several morphed across revisions —
e.g. pass-12 finding 2's threshold Θ := bound + (eg−1)h became the clean threshold
w_prev(Φ), re-confirmed at pass 13; pass-11 finding 4's sign fix became pass-12
finding 4's rule deletion — the live text carries the deletions, correctly).
TWO drift defects found:

### F8. JUSTIFICATION GAP (stale cross-reference contradicting the live text) — (S6a) consumer audit vs D.7(v)
Quote (D.2 (S6a)): "D.7(v) consumes LOCALIZED F-multiplication, not integral
scalars (see its rev-D⁶ form)."
Quote (live D.7(v)(3)): "[rev D⁷, pass-15 finding 1 — no localized action, no
embedding lemma] … (S6b) AT THE CURRENT STAGE … supplies, for each slot j and each
prescribed c_j ∈ F …, an INTEGRAL realizer at that slot and weight."
These contradict each other: the (S6a) consumer-audit sentence describes the
rev-D⁶ mechanism that pass 15 explicitly replaced ("no localized action"), and it
even directs the reader to the superseded form. The MATH is unharmed — the actual
consumer (large-weight integral (S6b) realizers) is compatible with (S6a)'s
closing claim "Nothing consumes current-field scalars at shallow indices
integrally" (the large-weight regime is above the threshold). But the live text's
own consumer audit misdescribes its own DAG: this is exactly the pass-15 repair
NOT fully folded into D.2. Neither pass 17, 20, nor 21 caught it.

### F9. JUSTIFICATION GAP (revision-label slip) — D.12
Quote (D.12): "CENSUS-PINNED AT REV D⁸ (updating the pre-gate text; pass-18
finding 1)". The pass-18 record says "[Repaired at rev D⁹: D.12 updated …]" —
pass 18 ran ON rev D⁸ and produced rev D⁹, so the live label "AT REV D⁸"
misnames the revision that contains the update. Content matches the record
otherwise (perimeter E/F/F-odd/G/H/I/G2/J/K(v2), level-3 gate queued). Trivial.

### Checks that PASS (recorded here so the gaps above are read in proportion)
- D.3(b) monomial identity, D.3(c) stride integrality/monotonicity, D.3(d) width
  bound: verified symbolically (independent recomputation, incl. exponent
  arithmetic k − thg, egs = g − thg in D.5).
- D.5 equal weights, monicity, absent-slot convention, (S6b) range check via
  (I-aug); K1 proof (ψ prime in F[z^{±1}], distinct ψ-orders): all verified.
- D.6 DIV: verified symbolically AND on a fresh instance with a genuinely firing
  Q-term (trace 1: p = 5, δ₁ = 1, identity (ii) exact).
- D.7(i) strict-depth spill, (ii) definitional K1, (iii) domain via DIV(iii) +
  slot decomposition, (iv) unit survival, (v) large-weight span (incl. my
  independent verification that e | γ holds automatically because w(p) is
  divisible by e at every stage — the unstated reason powers of p suffice),
  (vi) F'-lines/exponent group, (vii) T'-transport degrees, (viii) offset-P-lift
  arithmetic (j₀ congruence, h_prev/e_prev > w_prevprev(Φ_prev) chain, base
  bottoming): all verified independently.
- D.9 (a)-(d): recursion, cofiniteness, domination chain e_rf_r + (e_r−1)h_r <
  e_rh_r ≤ w_r(Φ_{r+1}), and the e_read = 1 realizability chain: verified,
  including the scale reconstruction (the recentering's coefficient space is Ĉ
  whose weight set is cofinite in ℤ — NOT the e·ℤ-restricted C).
- D.10: species lemma, v = v', g = 1 instance typing, substitution identity in
  L_both, scope-clauses lift independence, RS-landing two-sidedness: verified;
  plus end-to-end numeric trace 2 (fresh configuration, a = 1 > 0, co-factor,
  transported digit LEAVING the minimizing set) — every predicted digit exact.
- D.11: both equalities verified given D.3(e)(ii) (see F3).
- D.2 base stage: all six axioms re-derived from accepted §A/§B1.
- Scale conversions audited at every interface (e-stretch at S5, e' in 𝒜',
  parent-scale (S6b), δ/(e'e) − rh in D.7(v), D.9's rescaling): no error found.
- Degenerate cases: μ = 1 (BOX vacuous at slot 0 — consistent), g = 1 (F' = F,
  recentering as instance), e = 1 (T = V, positions 0), ψ ≠ z everywhere it is
  consumed, zero-slot conventions in DIV: all type-check.

## Verdict

Count: **0 CRITICAL ERRORS, 9 JUSTIFICATION GAPS** (F1–F9).

No defect breaks the logical chain: both landing theorems (D.8, D.10), the stage
induction (D.7 + TRANS-RS), and the per-move ledger (D.11) stand under
assume-and-continue at every gap. The two traces I chose (configurations absent
from all records — p = 5/(e,h) = (2,3)/ψ = z²+2 with a firing division term, and
p = 3 recentering with anchor a = 1 plus a co-factor and a slot leaving the
minimizing set) close exactly, end to end.

But under this repo's standard (a clean pass = 0 critical AND 0 gaps; §A and
§B2-DEF itself were held to that bar), the honest verdict on the live text is:

**NOT CLEAN — 0 critical / 9 justification gaps.**

The three that matter (the rest are wording/label slips):
1. F3 — D.3(e)(ii), the unitriangular-digit-system bridge, is the sole support of
   ALL mass statements (D.8 counts, D.11) and is a paragraph-level sketch:
   equation→coordinate injectivity, the F'-digit-to-base-digit-block unpacking,
   and the global coordinate order are asserted, not displayed. (Pass 20 called
   this its "self-chosen weakest point" and passed it; I do not.)
2. F8 — the live (S6a) consumer audit contradicts the live D.7(v): it still
   describes the rev-D⁶ "localized F-multiplication" mechanism that pass 15
   replaced, and points the reader to the superseded form. A pass-15 repair not
   fully folded in; survived three "clean" passes (17, 20, 21).
3. F7 — D.10's anchored substitution display "(z'+c̃)^a·z'^μ·h(z'+c̃)" is
   well-typed only because a ≥ 0 at e_read = 1 stages (T coefficient-pure ⟹
   R(f) is a z-POLYNOMIAL there); this one-sentence fact is nowhere stated, and
   without it the display leaves F[z'^{±1}].

Codex-blind-spot note: Codex's 13 passes converged on scalar groups, scales, and
typing — and every one of its recorded repairs is genuinely in the live text in
final form. What it systematically did NOT do is (i) re-audit OLD sections after
LATER repairs (F8 is precisely such a cross-section staleness), and (ii) demand
displays for the counting bridge it repeatedly waved through (F3). Neither
invalidates the mathematics; both are exactly where a decorrelated verifier
should push before this section is cited as load-bearing for §C.

— Fable, fresh instance, 2026-07-26.
