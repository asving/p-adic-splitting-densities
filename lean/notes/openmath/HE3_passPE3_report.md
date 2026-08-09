# HE3 passPE3 — THIRD FRESH-CONTEXT HOSTILE PASS (Fable, zero prior stake)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 1 MINOR. The counter starts:
0/2 → 1/2.** Each surface on this pass's attack list was re-derived or
machine-adjudicated independently and HELD: the [r2] coherent-convention
pin (the W(k) wrap formula re-derived from monomial arithmetic, its
integrality proved, the non-affine claim confirmed, the coboundary
cancellations verified at both propagated identity sites, the witness
recomputed to the digit), the Ψ-comparison node route (closure at μ ≤ 3
exhaustive on my own case split; no-circularity verified consumer by
consumer), HE3-2(a) under vanishing binomials (sound under the residue-sum
reading the lemma's own repair block pins), and the F-3/F-4/F-5 repairs.
The fresh route ran GREEN (0 violations) at three geographies disjoint
from every prior leg — the letter-starved corner ((2,1) and (3,1),
including a depth-2 ALPHA cascade at K^× = {1}), a μ = 3 coherent-read
family at the new (e₁,f₁) = (3,1), and non-prime q = 4 over F₄[[t]] —
with the coherent-vs-naive flip PARI- or construction-adjudicated at all
three, siding with the coherent read each time. The one MINOR is a
display imprecision in §S1 (iii)'s starved-corner list; its fence is
conservative, so nothing downstream moves.

**Pass metadata.** Target `HE3_PROOF_2026-08-08.md` at HEAD (r2 =
b78e56a/79b604c/f045ee4/5aca99b/5babe16 on PE2 @ 6d0ff09, r1 on PE1 @
7950ee4). Protocol: quote-and-classify, fix nothing. PE1's and PE2's
routes not re-walked; this pass's surfaces per the charge: the [r2]
repairs as displayed, the PE2-suggested PE3 charges, and a fresh route
disjoint from PE1 legs A/B/C, PE2 FR-A/B/C/D, and the note's §S8/§S9′
rows.

---

## FINDINGS (ranked)

### M-1 — MINOR. §S1 (iii)'s starved-corner characterization is not exact
### in either of its two possible readings; the fence is conservative, so
### the chain is unharmed.

QUOTE (§S1 (iii)): "needing |K^×| = Q^{f₁} − 1 ≤ d_λ ≤ μ (at μ ≤ 3 only
(Q,f₁) ∈ {(2,1), (3,1), (2,2)} can be starved)". Two readings, neither
matching the list: (i) under the displayed bound d_λ ≤ μ = 3, the
geography (Q,f₁) = (4,1) also satisfies |F₄^×| = 3 ≤ 3 (Q ranges over
prime powers in this program — the equal-char F₄[[t]] base is legal, and
this pass's FR3 runs one) yet is omitted from the "only" list; (ii) in
the display's own context the sample is needed only while refuting a
hypothetical low side, which occupies horizontal length ≥ 1 of the
μ-budget, so the κ = D′h+1 side has d_λ ≤ μ − 1 ≤ 2 and the true
starvable list is {(2,1), (3,1)} — the listed (2,2) is unreachable
there, and (4,1) is excluded for the same reason. Because the fence
consumes GENHN's [r1] erratum on the LISTED corner, a superset of the
true in-context corner, no conclusion of the display rests on the
imprecision. FAILURE SCENARIO: a consumer re-using the parenthetical's
list at a site where the starved side can fill the whole polygon
(d_λ = μ, e.g. a future single-side sampling argument) would omit Q = 4
base rings from the fence; at THIS site nothing fails.

---

## CLEAN CHARGES (attacked, survived this pass's own verification)

* **Attack 1a — the W(k) wrap formula (DEFINITION 1 [r2]).** Re-derived
  from scratch: with n(κ) = x^{i₀(κ)}π^{(κ−i₀(κ)h)/e₁}, the monomial
  ratio n(κ₀−ku)·n(u)^k/n(κ₀) works out to exactly
  (x^{e₁}π^{−h})^{W(k)} with W(k) = (i₀(κ₀−ku) + k·i₀(u) − i₀(κ₀))/e₁
  — x-exponents give e₁W, π-exponents independently give −hW, total dv
  0, residue η^{W(k)}. INTEGRALITY: i₀(κ₀−ku) + k·i₀(u) ≡
  h^{−1}(κ₀−ku) + kh^{−1}u = h^{−1}κ₀ ≡ i₀(κ₀) (mod e₁) since
  gcd(h,e₁) = 1, so e₁ | the numerator — W ∈ ℤ, as the display
  presumes. NON-AFFINE: at (e₁,h) = (2,1), λ = 3, κ₀ = 9 I compute
  W = (0,0,1,1) (increments 1,0 — not affine), matching the Remark's
  hand check; at the witness (κ₀,u) = (10,5): W = (0,1,1) ✓; at ℓ ≥ 2
  the same congruence runs on κ₀ − ku with u ∈ ℤ, so the formula and
  its integrality cover fractional slopes.
* **Attack 1b — the coboundary statement at the propagated sites.** All
  five [r2, F1] sites grep-present (§S3 HE3-1′ proof, §S4 (ii), §S5 (b)
  display, §S5 (b) proof, §S6.2 HE3-4). The two identity-site
  cancellations verified by direct computation: (HE3-1′) the k-th
  attaining summand's residue factors as ã_k·ι(s)^{j₀+k}·
  res(n(κ₀)n(λ)^{j₀}/n(c)) with the second factor k-INDEPENDENT of dv 0
  (c = κ₀ + j₀λ), so the sum is one global K-factor times
  s^{j₀}R_λ(s), exactly the [r2] insertion; (HE3-2(b)) with
  M_j = n(c)/n(λ)^j the (i → j) summand's ratio M_i·n(λ)^{i−j}/M_j
  telescopes to 1 identically as monomials, so g″_j =
  Σ binom̄(i,j)s^{i−j}g_i = [Z^j]G(Z+s) wrap-free; and g_{T+k} =
  ã_k·res(n(κ₀)n(λ)^T/n(c)) gives G = const·Z^T·R_λ with no diagonal —
  the three [r2] displays are exactly these three computations.
* **Attack 1c — the witness reconciliation.** Recomputed: pins (2,0),
  (1,5), (0,10) on the λ = 5 line ✓; naive a = (1,1,1) → (Z−1)² in
  char 3 ✓; W = (0,1,1) from i₀(10) = 0, i₀(5) = 1 ✓; ã = (1,η,η) →
  η(Z² + Z − η) with η(Z²+Z−η) = ηZ²+ηZ+1 ✓ (η² = −1); disc = 1+4η =
  1+η in char 3, and (F₉^×)² = {±1, ±η} (squares recomputed) excludes
  it → irreducible ✓; s = 1 is not a root of the coherent residual
  (R(1) = η(2−η) ≠ 0), consistent with the measured above-λ length 0.
  The Z ↦ −Z reconciliation with PE2's Z² − Z − η is a geometric
  rescaling (c = −1), same type — the claim is correct. MACHINE TIE
  (this pass, FR2b): PARI nfmodpr computes the DEF-1 coherent
  coefficients of the witness directly (no W formula, no slot formula):
  (1, η, η) exactly.
* **Attack 2 — the Ψ-comparison node route (§S1 (ii)).** Re-derived in
  full. The j = 0 pin: HE3-1 at Φ″ = Φ′ (hypothesis trivially met),
  Σ_ρ dv(Φ′(ρ)) > D′μ·D′h from the locus computation — sound, and the
  ψ-cancellation argument for dv(Φ′(ρ)) > D′h checks (entry-side slots
  i = e₁t, residue sum = ψ(η_ρ) = 0). The general pin: the hull-mean
  argument (a failing pin at j* puts the hull at j* at height
  ≤ (μ−j*)D′h, forcing a side of slope ≤ D′h), COUNT from HE3-0(iii) +
  length sum, R(κ) from the two exact reads, and R(κ) − κ·COUNT = (∗∗)
  all verified. THE μ ≤ 3 ENUMERATION IS EXHAUSTIVE on my own case
  split: no-mid → all summands of Σ_low D′L_λ(κ−λ) strictly positive
  (κ−λ ≥ 1) — contradiction, and this subsumes the all-low degenerate
  case; mid → length budget forces exactly {low 1, mid 2} at μ = 3
  (mid needs ℓd ≥ 2; two mids or mid ≥ 3 overflow; μ = 2 cannot host a
  mid), κ = D′h+1 is then NOT a slope so the sample is legal
  unconditionally, and c_mid = −c_low = D′ gives λ_low = λ_mid, absurd.
  Per-root exactness at λ_ρ = κ: β_ρ ∈ roots(ι_ρ(R_κ)), ι_ρ(s) not
  (field embedding, R_κ(s) ≠ 0) — verified against HE3-0(iii)'s
  provenance. NO-CIRCULARITY: HE3-1 consumes dv(Φ″−Φ′) > D′h only
  (resultant symmetry + norm); HE3-1′'s proof consumes the slot lemma
  at θ″ + coherent reads; (★) is polygon geometry; HE3-1L and HE6-0″
  consume the locus only; HE3-0(iii) is the classical read at ρ — none
  consults the node. Letter availability at κ = D′h+1 > (D′−1)h ✓.
  The honest scope (iii) is honest (its one imprecision is M-1), and
  the GENHN [r1] fence stands as independent support.
* **Attack 3 — HE3-2(a) under vanishing binomials (PE2's suggested
  charge).** The (a) display's equality clause is sound under the
  residue-sum reading, which the lemma's own [REPAIR, PE1 finding 4]
  block pins two paragraphs below: "residues cancel" = the sum of the
  attaining summands' residues (each carrying the binomial coefficient
  through its image in K) vanishes — a single attaining summand with
  p | binom(i,j) has residue 0 and is a degenerate cancellation, so
  equality correctly fails there; the block itself warns "Only the
  INEQUALITY in (a) survives summand-wise". The multiplicity fact
  (Z−s)^m ‖ R_λ ⟹ Z^m ‖ R_λ(Z+s) is binomial-free in every
  characteristic (R_λ(Z+s) = Z^m·g(Z+s), g(s) ≠ 0). Grep: no site in
  the note consumes "(a)"'s equality clause by name; (b)'s proof is
  run at the residue level and consumes only the inequality plus the
  substitution identity. No finding.
* **Attack 4 — the F-3/F-4/F-5 repairs.** F-3: the re-keyed step (2)
  parenthetical is correct AND the mechanism is genuinely exact — the
  attaining slots of C at ρ live in one class i₀ + e₁t (distinct
  classes cannot share the integer min, h invertible mod e₁), each
  attaining res(c_i) ≠ 0, and an F_Q-combination of {η_ρ^t} with a
  nonzero coefficient is nonzero — so dv(C(ρ)) = κ exactly, no
  level-1 cancellation. F-4: the §S9′ disclosure matches the code (P4
  extracts slot digits, verified quasi-tautological on inspection);
  docstring corrected; FR-C correctly cited as the decorrelated leg;
  pins updated and verified below. F-5: the geography scope block at
  P2-N1 states the (3,2) demo vs the (2,1) live-gap geography and
  cites PE2 FR-D accurately (checked against the FR-D output shape at
  6d0ff09).
* **Free hunt (r1+r2 text).** §S4 (ii)'s convention-matching insert is
  consistent with the self-normalizing n-read (both sides anchored at
  n(κ₀)(·), n(u)(·)); DEF 1 [r2]'s "pin strictly above the line
  contributes 0" and the vertex reads at k = 0, d_λ check; the
  geometric-freedom claim (anchor swap = one global scalar + Z ↦ cZ)
  verified by the ratio argument (ϖ^{κ₀−ku} vs M_k differ by
  η^{A+Bk}); the §S0″ record's five-row table matches PE2's report;
  HE3-BOX-1's arc line matches the actual arc.

## MACHINE LEG (pins, byte-freeze, isolated re-run, tautology audit)

* **Pins re-verified at HEAD**: `he3r1_supp.py` md5 =
  93681e8d47d447dcbfd46db0ddfe0c55 = the §S9′ [r2] pin; committed
  output md5 = 65ed06e49f4c54abf1b143513633f143 = the §S9′ pin; the
  r2 runner diff (b78e56a) is docstring-only, as §S0″ claims.
* **Byte-freeze verified**: DEFINITION 1's blockquote and the (★)
  display + proof are byte-identical to HE3 @ 7a95449 (HE6's frozen
  pin) — diff empty on both extracts; `he3_checks.py` + both battery
  artifacts last touched at 872327b (pre-r1), per git log.
* **Isolated re-run** (`/tmp/he3pe3_iso`, runner copied alone): exit 0,
  stdout BYTE-IDENTICAL to the committed `he3r1_supp_output.txt`,
  results JSON content-identical. GREEN, 0 violations.
* **Tautology audit**: the note's [r2] claim that the battery/supp
  measurement route consults the coherent object automatically is
  correct (the measurement is dv(B₀) at test keys — convention-free);
  P4's quasi-tautology is now disclosed in both the runner docstring
  and §S9′ (F-4 executed as recorded). This pass's own fresh legs are
  decorrelated: members built as explicit products or from hand-picked
  developments, predictions hand-derived from the displays before
  running, oracles = PARI factorpadic/idealprimedec (ℤ_p rows),
  explicit construction (F₄[[t]] row), and nfeltval/nfmodpr residue
  arithmetic (W-direct leg, no slot or W formula in the loop).

## FRESH ROUTE (`verification/openmath/he3_pe3fresh.py`, GREEN, exit 0,
## 0 violations — geographies disjoint from PE1 A/B/C, PE2 FR-A/B/C/D,
## and the note's own rows)

* **FR1a/FR1b — the letter-starved corner at (Q,f₁) = (2,1)** (the
  honest scope's own geography, never run as a starved-σ family):
  e₁ = 1 member (x−14)(x−22)(x−10) over ℤ₂ — base {2:2, 3:1}, ALPHA at
  the single letter, measured m = 2, recentered polygon {2:1, 3:1, 4:1}
  with the collapsed λ-side of length 1 and residue 1 = −s (HE3-2(b)'s
  [r1] collapse clause quantitatively confirmed), PARI σ = {(1,1)}³;
  e₁ = 2, μ = 3 member (x²−2x−10)(x²−2x−34)(x²−2x−130) at Φ′ = x²−2 —
  single side λ = 3 = D′h+1, d = 3, all letters 1 (starved ALPHA,
  m = 3), sub-block slopes {6,10,14} at Φ″ = x²−2x−2, HE3-1a asserted,
  PARI σ = {(2,1)}³. Depth-2 cascade entirely inside K^× = {1}.
* **FR1c — starved slope + coherent adjudicator at f₁ = 1, (3,1)** (a
  NEW seam geography: PE2's witness was f₁ = 2): Φ′ = x²+3 over ℤ₃
  (η = −1), f = Φ′² − 9Φ′ + 27 = (x²−3x+3)(x²+3x+3), single side
  λ = 3 = D′h+1, middle pin lifted. Naive read Z²+1 — IRREDUCIBLE over
  F₃, would predict σ = {(2,2)} and m ≡ 0; coherent read (W = (0,1,1),
  η = −1) = −(Z−1)(Z+1) — split at BOTH letters, a genuinely starved
  slope. PARI: σ = {(2,1),(2,1)}; measured m = {1:1, 2:1}. The
  coherent read wins at f₁ = 1. FR1d: (3,1) e₁ = 2 μ = 3 with the
  slope-3 side consuming all of K^× — σ = {(2,1)}³, 3/3.
* **FR2 — μ = 3 coherent family at the new (e₁,f₁) = (3,1)**:
  Φ′ = x³+3 over ℤ₃ (D′ = 3, D′h = 3, η = −1), λ = 4 line, κ₀ = 12,
  W = (0,1,1,1) (non-affine). f = Φ′³ − 3xΦ′² + 9x²Φ′ − 81 (degree 9,
  pins (0,12),(1,8),(2,4) on the line). Naive (Z−1)(Z²+1) would
  predict {(3,1),(3,2)} and m_1 = 1; coherent −(Z³−Z²+Z+1) is an
  irreducible cubic predicting {(3,3)}. PARI: σ = {(3,3)} — one nonic,
  e = 3, f = 3; measured m = {1:0, 2:0}. Coherent confirmed at e₁ = 3.
* **FR2b — the W-formula DIRECT leg**: the coherent coefficients
  res(A_k(θ)n(u)(θ)^k/n(κ₀)(θ)) computed by PARI residue arithmetic
  (nfeltval/nfmodpr — neither the slot formula nor the W formula in
  the loop): FR2 member → (2,2,1,2) = the formula's η^W-twisted values;
  PE2's witness `ma` → (1, η, η) = the §S3 Remark [r2] display. The
  DEF 1 [r2] construction is machine-real coefficient-by-coefficient.
* **FR3 — non-prime q = 4 on the coherent displays, equal char, BY
  CONSTRUCTION**: O = F₄[[t]], Φ′ = x² + ωt (η = ω), f = g₁g₂ with
  g₁ = x²+tx+ωt (letter 1), g₂ = x²+ωtx+ωt (letter ω) — both slope-1/2
  irreducible, so σ = {(2,1),(2,1)} is KNOWN with no oracle.
  Development verified exactly: A₁ = ω²tx+ωt², A₀ = ω²t³, pins
  (0,6),(1,3),(2,0) on the λ = 3 line. Naive read (ω²,ω²,1): NO
  F₄-root — would predict the inert type {(2,2)}. Coherent read
  (W = (0,1,1), η = ω): (ω²,1,ω) = ω(Z−1)(Z−ω) — split exactly at the
  two letters. The direct symbolic residues in F₄[t][θ]/(θ²−ωt) equal
  the W-formula values. First run of the coherent seam at a non-prime
  base anywhere in the arc.

## GRADE LINE

**Pass verdict: CLEAN (1 MINOR, 0 GAP, 0 CRITICAL — the bar is
GAP-or-worse). Counter: 0/2 → 1/2.** The r2 repairs held under this
pass's attacks; the fresh route sided with the note's displays at each
of its three new geographies, and the machine pins/freezes are exact.
Suggested next-pass charges (PE4, for the orchestrator): the M-1
corner-list display (one-line repair candidate); HE3-5's clause (ii)
boundary at e₁N = m₁ − λ(j−j₁) + 1 (never separately attacked); a
starved (2,2)-geography σ family (K = F₄ over a ramified-quadratic
stage, the one listed corner geography no pass has machine-run); and
the §S6.3 stage-α onward-read sentence as repaired at [r1, F5].
