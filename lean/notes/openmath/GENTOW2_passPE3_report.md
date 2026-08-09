# GENTOW2 passPE3 — HOSTILE VERIFIER REPORT (fresh context), 2026-08-09

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 2 MINOR. The [r2] canonical
LETTER FORMULA z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} was re-derived by me from the
rendered PDF pages themselves (Def 3.12 + §3.2/§3.3 data + Prop 1.15,
pp.7/15/16/17) and is CORRECT, with provenance rows 17–19 MATCHING on
both legs (visual page read AND layout-extraction cross-check); the
repaired h-step was re-derived in full — the division argument, the
e₃ ≥ 2 value-group leg, and the e₃ = 1 y-degree contradiction each
check against Cor 4.4/Cor 4.7/Lemma 3.17/eq (14) read at their pages,
so the unit-q corner is genuinely CLOSED; the N1 grade-7 worked trace
recomputes exactly (including the corrected 17/2). The machine legs
are frozen and reproduce bit-identically (4 isolated re-runs). A NEW
fresh route at the first z₂ ≠ 1 letter-live frames anywhere in the
record (p = 3, F₉ residues — LP1's z₂ was 1) came back 50/0 GREEN
first-run-under-seal with the tooth firing on both frames, in the
direction OPPOSITE to LP1's. The two MINORs are one implicit
one-line evaluation-extension step inside the letter-formula
derivation and a stale STATUS header. Counter starts: 0/2 → 1/2.**

Target: lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md at HEAD
(r2 = c7c4416 + d56e439 + 100d1ea; folded at 5ea9a60). PE1 (61daa69)
+ PE2 (aff457c) reports read, their routes not re-walked. Charge:
quote-and-classify, fix nothing; CLEAN bar = nothing GAP-or-worse.

## F. FINDINGS

**[m1] MINOR — the letter-formula derivation evaluates value-0
RATIONAL functions under a citation stated for polynomial classes
(S5.1, the derivation's first display).** Quoted: "Under Prop
1.15(1) (p.7) the class evaluates: z₂ = res(γ₂(x₀)) =
res(Φ′(x₀)^{e₂}/π₂(x₀)^{u₂})." Prop 1.15(1) (verified p.7) defines
the evaluation map on polynomial classes g(x) + P₀⁺ ↦ g(θ) + m_φ;
γ₂ = Φ′^{e₂}π₂^{−u₂} is a rational function (as is the γ₁^k residue
step). The missing bridge is one standard line: pick a polynomial
representative b with H_{µ₂}(b) = y₂, i.e. µ₂(bπ₂^{u₂} − Φ′^{e₂}) >
e₂(w₂+λ₂) after clearing the monomial denominator; evaluate at x₀
using v ≥ µ₂ on polynomials and the EXACT stable value v(π₂(x₀)) =
1/e(µ₁) of the denominator (Lemma 3.13(1), a [r2] supporting pin);
divide to get v(b(x₀) − γ₂(x₀)) > 0, hence res(b(x₀)) = res(γ₂(x₀)).
I checked this line goes through; the formula's conclusion is
additionally machine-true at LP1 and at both new LV frames. No
failure scenario for any current consumer — the defect is that a
fresh reader cannot check the display from the quoted Prop 1.15
alone. (The other two identification use-sites — the (R-repo)
display and the R_{3,0}(ẑ_d) = d step — apply Prop 1.15/Thm 4.8 to
POLYNOMIAL classes and are exactly in scope; no finding there.)

**[m2] MINOR — the STATUS header (note lines 5–14) is stale at r2:
its arc bracket ends "[r1 ...; record in S9 ... Grade stays 0/2;
PE2 next.]" with no [r2] entry, while S10 records the r2 round and
says "Next: PE3".** A reader of the STATUS block alone would place
the note one round behind (and miss that the letter-live probe
exists). The body's [r2] tags and S10 are complete and accurate;
bookkeeping only.

## A. ATTACK 1 — the [r2] canonical LETTER FORMULA (re-derived, CORRECT)

My own derivation from the PDF, decorrelated from the note's and
from PE2's (which I read only after): Def 3.12 (p.16, verified
visually + layout L813–821): γ₂ = (Φ₂^{FGMN})^{e₂}π₂^{−h₂} with
Φ₂^{FGMN} = φ₂π₂^{−V₂}, so γ₂ = Φ′^{e₂}π₂^{−u₂}, u₂ := e₂V₂ + h₂;
§3.2 data table (p.15, L785–806): V₂ = e(µ₁)w₂, h₂ = e(µ₂)λ₂ ⟹
u₂ = e(µ₂)(w₂+λ₂) = dv₂(Φ′) — the S2 dictionary's u₂; §3.3 (p.16):
ℓ₁h₁ + ℓ′₁e₁ = 1, 0 ≤ ℓ₁ < e₁, π₂ = Φ₁^{ℓ₁}π^{ℓ′₁} = x^{ℓ₁}π^{ℓ′₁}
(V₁ = 0 at the Gauss base); p.17 (L855–863): y₂ = H_{µ₂}(γ₂),
z₂ = image in F₃, ψ₂ = minpoly(z₂); Prop 1.15 (p.7, L340–344):
F₃ ≅ F_{φ₃} by evaluation at a Φ₂-root x₀. Then: the ratio
n̂(u₂)/π₂^{u₂} = x^{i−ℓ₁u₂}π^{a−ℓ′₁u₂} has exact value 0 at x₀
(both numerator and denominator sit at dv₁-height u₂); a value-0
monomial x^{e₁k}π^{−h₁k} = γ₁^k has residue z₁^k (gcd(h₁,e₁) = 1
forces e₁ | i−ℓ₁u₂); 0 ≤ i < e₁ pins i = ℓ₁u₂ mod e₁, k =
−⌊ℓ₁u₂/e₁⌋ (floor valid: ℓ₁u₂ ≥ 0). Multiplying residues:
z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}. IDENTICAL to the note's display, each
cited source matching its page. Witness check e₁ = 2, u₂ = 5,
ℓ₁ = 1: z₂ = η₂z₁^{−2} ✓. Rows 17–19 of S6.1: MATCH on both legs
(I read pp.7, 15, 16 + the p.17 supporting pins off the rendered
PDF and cross-checked the layout lines 340–344, 785–806, 813–821,
855–863). The S2 ψ₂-row, S4 clause-(c), and consumption-note twist
propagation each state the formula's consequence accurately; the
"on the nose exactly when the twist fixes ψ₂" hedge is correct
(minpoly(η₂c) = c^{f₂}ψ₂^{repo}(y/c), c = z₁^{−⌊·⌋} ∈ F₂).

## B. ATTACK 2 — the h-step repair (re-derived, corner CLOSED)

Statement checks at the rendered pages: Lemma 3.17 (p.19) vanishes
R_{i,α} on P_α^+ ✓; Cor 4.4 (p.21): (1) exact grade ⟺ R ≠ 0, (3)
deg R = ⌊s′/e_i⌋, ord_y = ⌊s/e_i⌋ ⟹ y-degree 0 for deg < m₃
single-point-polygon elements ✓; Cor 4.7 (p.22): (2) needs ONE
grade in Γ₂ and carries no degree hypothesis ✓; eq (14) (p.19):
R_{3,α}(φ₃^s) = y^{⌊s/e₃⌋} ✓; Thm 4.8 (p.22): restriction to
F₃ ⊂ ∆₃ is the identity ✓. Division: deg ẑ_d, deg n̂₂ ≤ m₃−1 ⟹
deg q ≤ m₃−2 ✓ Φ₂-free. (h-i): ρ(x₀) = ẑ_d(x₀)n̂₂(x₀) since
Φ₂(x₀) = 0; digit d ≠ 0; B-1 in scope ⟹ ν(ρ) = β exact ✓. (h-ii)
✓. (h-iii) leg e₃ ≥ 2: λ₃ ∈ Γ₂ ⟺ e₃ | h₃ ⟺ e₃ = 1 (gcd(h₃,e₃)=1),
so ν(qΦ₂) = ν(q) + w₃ + λ₃ ∉ Γ₂ ∋ β, strict ✓. Leg e₃ = 1 (the
PE2-flagged corner): if ν(qΦ₂) = β, then ν(q) = β − w₃ − λ₃ ∈ Γ₂
(λ₃ ∈ Γ₂ at e₃ = 1) is q's EXACT grade; Cor 4.7(2) (q in the
Γ₂-slot) + eq (14) at s = 1, e₃ = 1 give R_{3,β}(qΦ₂) =
R_{3,ν(q)}(q)·y with R_{3,ν(q)}(q) ≠ 0 (Cor 4.4(1), single-point
polygon at exact grade), y-degree exactly 1; the left side
R_{3,0}(ẑ_d)·R_{3,β}(n̂₂) and R_{3,β}(ρ) have y-degree 0 (Cor
4.4(3)); additivity then equates a y-degree-0 element to something
carrying a nonzero y-linear term — contradiction ✓. The corner is
CLOSED by the displayed algebra, not fenced. (h-iv) ✓. s₃(β) = 0
via eq (12) (p.17) ✓ (at e₃ = 1 it forces s ≡ 0 outright). Worked
N1 trace recomputed: ẑ_{η₂} = xΦ′/4 (ν = 0), n̂₂(7) = 8x, product
2x²Φ′ deg 4 = m₃ (B-1 inapplicable as written — PE2 F2 confirmed
real); division against Φ₂b = Φ′²−2xΦ′−8 gives q = 2, ρ =
4xΦ′+4Φ′+16 (my own division, via x² = Φ′+2) ✓; ρ-pins 7, 8, 8 ✓;
digit(ρ) = d·z₁^{−1} = d at z₁ = 1 ✓ (and the general (h-i) needs
only the evaluation identity, which is z₁-free); dv₂(2Φ₂b) =
2 + 2·(13/4) = 17/2 > 7 ✓ — the note's correction of PE2's "9" is
right and the inequality stands.

## C. ATTACK 3 — the LP1 probe instrument

Seal chain: probe blob at d56e439 = blob at HEAD (md5 d0c0ebeb...);
output added only at 100d1ea — first-run-under-seal confirmed by
commit order. Frame data recomputed by hand: PH = x⁴+2x²+4 has pins
(0,2),(2,1),(4,0) on slope −1/2 with residual y²+y+1 irreducible
/F₂ (f₁ = 2) ✓; w₂ = 2, λ₂ = 1/4 (v(8x³) = 9/2 = 2(w₂+λ₂)) ✓;
e(µ₂) = 4, u₂ = 9, ℓ₁ = 1, n̂(9) = 16x ✓; η₂ = res(x₀²/2) = z₁,
z₂ = res(8/x₀⁶) = z₁^{−3} = 1, ⌊9/2⌋ = 4 ✓. The 14 B-route
predictions and 5 A-route resultant valuations re-derived by hand
(v(x₀²−2) = 1 exact ⟺ z₁ ≠ 1 → 8; the x⁶−8 = (x²−2)PH identity —
expanded by hand, exact — plus v = 13/4 → 26 proves z₁³ = 1 hence
z₂ = 1 with no residue arithmetic; v(x₀⁸−16) = 4 exact ⟺ z₁⁴ =
z₁ ≠ 1 → 32) ✓. Route decorrelation: A-route = repo Bareiss
integer resultants + exact polynomial identities; B-route = PARI
factorpadic/nfeltval/nfmodpr in a subprocess; predictions are
docstring literals. Import audit: gentow2_checks has a __main__
guard — the probe's 21 checks are its own. Tautology audit: the
B-route booleans are interlocked as mathematical facts but each is
computed independently by nfmodpr in F₄; the TOOTH (η₂ ≠ z₂) is a
genuine machine refutation of the pre-repair parenthetical. Honest
scope note verified: LP1's z₂ = 1 means variants of the formula
agreeing with it mod ord(z₁) = 3 in the exponent were untestable
there — exactly the hole my fresh route (E) targets.

## D. ATTACK 4 — cross-round coherence + free hunt

* r2 commit sweep: c7c4416 = note-only; d56e439 = probe-only (+150
  lines); 100d1ea = note S10 + probe output. Zero modifications to
  the 6 previously sealed artifacts across the r2 range; md5 pins
  at HEAD match the PE1/PE2 report pins (list in section M).
* The 13-witness letter-blindness census (5 battery-committed + 2
  battery-new + 3 PE1 + 3 PE2) checks against the runners; each of
  those frames has f₁ = 1 over q = 2 (z₁ = 1) as claimed.
* The F3/F4 minor repairs read as PE2's guidance asked: the
  fallback hypothesis now sits in B′(3)'s direction; B′(4) states
  the per-grade biconditional with the consumed scope (u(β_t) = 1
  at used grades) separated.
* S6 "Statements consumed" [r2] addendum consistent with S6.1 rows
  17–19; the [r2] supporting pins (z_i display L855–863, Lemma 3.13
  L836–840, the §3.2 Prop-1.15 identification sentence p.15) each
  verified on the rendered pages this pass.
* Free hunt at the S4/S2 seams found nothing beyond [m1]/[m2]: the
  Cor 4.4(4) degree-consistency parenthetical (ℓ₂/e₂ = f₂e₃f₃ =
  deg ψ₂^{e₃f₃}) checks; the (h-f) hypothesis audit and Cor 6.4
  instantiation were PE1/PE2 territory and were not re-walked.

## E. FRESH ROUTE (this pass; runner gentow2_pe3_fresh.py SEALED at
## 0e80968 before its first run; output gentow2_pe3_fresh_output.txt
## — 50 checks / 0 violations, GREEN; committed ce43fe0)

Route disjoint from the sealed battery, PE1's F₄ × f₃ = 2 corner,
PE2's f₃ = 3 family, and r2's LP1 (p = 2, z₂ = 1): the FIRST
z₂ ≠ 1 letter-live contacts anywhere in the record, at a DIFFERENT
p (p = 3, residues in F₉). Base: PH = x⁴ + 9 (λ₁ = 1/2, ψ₁ = y²+1
irreducible /F₃, z₁² = −1, ord(z₁) = 4); stage 2 at u₂ = 11 (w₂ =
2, λ₂ = 3/4, e₂ = 2, e(µ₂) = 4), twist exponent ⌊11/2⌋ = 5 with
z₁⁵ = z₁ ≠ 1 LIVE; n̂(11) = 243x; predicted and got (e,f) = (4,2),
single prime, both frames:

* **LV1** = (x⁴+9)² − 243x: η₂ = res(243x₀/(243x₀)) = 1 (exact
  algebra — the correction term IS the normalizer line), z₂ =
  res(243/x₀^{10}) = z₁^{−5} = −z₁ ∈ F₉∖F₃. The FGMN letter is
  DETECTABLY nontrivial for the first time; the formula predicts it
  from a trivial repo letter. TOOTH fired in the direction OPPOSITE
  to LP1 (there η₂ ≠ 1 = z₂; here η₂ = 1 ≠ z₂) — the pre-repair
  "η₂ ↔ z₂" is now machine-dead in both twist directions.
* **LV2** = (x⁴+9)² + 243x: η₂ = −1, z₂ = z₁ — BOTH letters
  nontrivial AND distinct; the formula carries −1 to z₁ across the
  F₉∖F₃ boundary: η₂·z₁^{−5} = (−1)(−z₁) = z₁ = z₂ ✓.
* Dual oracles, 50 checks: A-route = 2 expansion identities + 14
  exact v₃-resultants (per frame: 4, 22, 8, 8, 16, 40, 62 — the
  x^{12}+729 → 62 value is an exact certificate of res(x₀^{12}/729)
  = −1, which pins z₂ = −z₁ on LV1 and z₂ = z₁ on LV2 given the
  exact-algebra η₂ legs; hand-derivation of 62 via x₀^{12}+729 =
  PH(x₀)(±243x₀ − 27PH(x₀) + 243), inner minimum unique at v = 5);
  B-route = PARI factorpadic/idealprimedec/nfeltval + nfmodpr in
  F₉ (34 checks incl. FORMULA and TOOTH per frame). Predictions
  hand-derived and sealed in the docstring; no smoke run; every
  check EXACT on first run.

## M. MACHINE-LEG SUMMARY

Pins at HEAD, 9 for 9 EXACT: PDF da846c82f1fcb619cefb3feb8164191e /
518,522 bytes; gentow2_checks.py 2603eb7c...; run2 output
832aa838...; pe1_fresh a70dd986... / e66e8ea5...; pe2_fresh
f2d6f1fa... (= 090f501 seal blob); r2 probe d0c0ebeb... (= d56e439
seal blob) / output b79121a2.... Isolated re-runs (fresh /tmp
copies, this pass): battery 41/0 BIT-IDENTICAL exit 0; r2 probe
21/0 BIT-IDENTICAL; pe1_fresh 20/0 BIT-IDENTICAL; pe2_fresh 22/0
BIT-IDENTICAL. Fresh route: 50/0 GREEN first-run-under-seal.

## G. GRADE LINE

**passPE3 verdict: CLEAN (0 CRITICAL, 0 GAP; 2 MINOR: [m1] the
implicit rational-function evaluation-extension line inside the
S5.1 letter-formula derivation, [m2] stale STATUS header lacking an
[r2] arc entry). The r2 repairs held under independent
re-derivation: the canonical letter formula is correct and
correctly sourced (rows 17–19 MATCH, dual-leg), the h-step's e₃ = 1
corner is closed by sound algebra, the LP1 probe is a genuine
decorrelated instrument, and the new z₂ ≠ 1 fresh route (50/0,
first-run-under-seal, teeth on both frames) gives the formula its
first detectably-nonzero-value machine contact. Acceptance counter
STARTS on the item-(6) cite note: 0/2 → 1/2. Fresh-route artifacts
committed: verification/openmath/gentow2_pe3_fresh.py (sealed
0e80968) + gentow2_pe3_fresh_output.txt (ce43fe0).**
