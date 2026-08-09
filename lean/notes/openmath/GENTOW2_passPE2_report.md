# GENTOW2 passPE2 — HOSTILE VERIFIER REPORT (fresh context), 2026-08-09

**VERDICT: NOT CLEAN — 0 CRITICAL + 2 JUSTIFICATION GAPS + 2 MINOR,
both GAPs inside the [r1]-new LEMMA GENTOW2-B′ (S5.1). Everything
PE1 flagged is CURED and everything the r1 round claims about the
PDF is TRUE: I re-opened the PDF myself and all 16 provenance rows
plus 8 supporting pins MATCH at the claimed pages (Thm 6.3 p.28 and
Cor 6.4/eq (23) p.29 verbatim-exact); the local PDF is bit-identical
to a fresh arXiv fetch I ran myself (md5 da846c82, 518,522 bytes);
the machine legs re-ran bit-identical; and a NEW fresh route at the
never-witnessed f₃ = 3 branch came back 22/0 GREEN with the tooth
firing. The two GAPs: (1) B′'s "η₂ ↔ z₂" identification parenthetical
is false in general (canonically z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}) and
mis-attributed to T(b)′(iii) — the same provenance-error class PE1-F2
caught, one clause over; (2) B′'s h-step applies B-1 outside its
stated deg < D₂ scope (the lift product ẑ_d·n̂₂(β̂) reaches deg = m₃
at the record's own frames). Neither breaks the theorem chain — B′
survives under the canonical evaluation identification, with a
mostly-mechanical repair for (2) — but both sit in a load-bearing new
lemma. Counter stays 0/2.**

Target: lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md at HEAD
(r1 = 1e091d1 + dd44d20 + 2146c23; folded at 2631d94). PE1 report
read first (61daa69; target blob then 531c212). Charge:
quote-and-classify, fix nothing; CLEAN bar = nothing GAP-or-worse.

## F. FINDINGS

**[F1] GAP — S5.1's residue-field identification parenthetical
"(η₂ ↔ z₂, level-1 letter ↔ z₁)" is false in general and is
mis-attributed to T(b)′(iii) (S5.1, (R-repo) display + the proof's
final step; also S2 dictionary row "ψ₂ = R₂(φ₃) (Cor 5.6(2))" and
the S4 clause-(c) bullet "FGMN's ψ₂ = R₂(φ₃) is the repo ψ₂").**
Quoted (B′ proof): "the repo-vs-FGMN match of grade-0 reads IS the
accepted residue-field identification (T(b)′(iii): η₂ ↔ z₂, level-1
letter ↔ z₁ — the clause the pre-repair B-2 pointer legitimately
covered)". Two defects, verified by my own derivation from the PDF's
Def 3.12 + eq (9) data (pp.15–16) and Prop 1.15 (p.7):
(i) *Attribution*: GENHN T(b)′(iii) (GENHN_PROOF L1168–1211) defines
the repo leaf read and the repo field K₂ = F_Q(η, η₂); it makes no
contact with FGMN's z₂ — the identification k(L2) ≅ F₃ is not there.
The identification that makes B′'s proof work needs NO repo cite at
all: it is FGMN's own canonical evaluation isomorphism
F₃ = Im(∆₂ → ∆₃) ≅ F_{φ₃} = k(L2), g ↦ res(g(x₀)) (Prop 1.15(2)),
under which the Thm 4.8 grade-0 step is exact.
(ii) *The letter claim*: under THAT canonical identification the
letters do not correspond. Computation: z₂ = image of H_{µ₂}(γ₂),
γ₂ = Φ₂^{e₂}π₂^{−h₂} = φ₂^{e₂}·π₂^{−u₂} (Def 3.12; u₂ = e₂V₂ + h₂),
π₂ = x^{ℓ₁}π^{ℓ′₁} (0 ≤ ℓ₁ < e₁, §3.3); the repo η₂ =
res(Φ′(x₀)^{e₂}/n̂(u₂)(x₀)) with n̂(u₂) = x^{i}π^{a}, i < e₁
(T(b)′(i)). The ratio n̂(u₂)/π₂^{u₂} = x^{i−ℓ₁u₂}π^{a−ℓ′₁u₂} has
value 0 and residue z₁^{(i−ℓ₁u₂)/e₁} (exponent an integer since
i ≡ ℓ₁u₂ mod e₁), hence canonically

    z₂ = η₂ · z₁^{−⌊ℓ₁u₂/e₁⌋}.

At the S2 witness (e₁ = 2, h = 1, u₂ = 5, ℓ₁ = 1, i = 1):
z₂ = η₂·z₁^{−2}. Correspondingly FGMN-ψ₂ = minpoly(z₂) is the
z₁^{⌊ℓ₁u₂/e₁⌋}-twist of the repo ψ₂ = minpoly(η₂), so the S2 row and
the S4-(c) parenthetical "FGMN's ψ₂ = the repo ψ₂" are exactly-true
only when the twist fixes ψ₂. Every committed and fresh machine
witness (10 + the 3 added this pass) has f₁ = 1 over q = 2, forcing
z₁ = 1 — the record is letter-blind, the same battery-gauge-blindness
pattern HETOW PE1 caught at the wrap cocycle. What SURVIVES (my
verification, not just charity): LEMMA B′'s statement and proof are
correct verbatim under the canonical identification (u(β) as defined,
x₀- and g-freeness intact — modulo [F2] below), and the item-(6)(α)
consumption "η₂(ξ) is a ψ₂-root" survives letter-twist because both
letters are images under the ONE field embedding F₃ → k(L₃)
(η₂(ξ) = σ(z₂·z₁^{⌊ℓ₁u₂/e₁⌋}) = σ(root of repo-ψ₂)) — so no
downstream clause of GENTOW2-A is falsified. Failure scenario: a
depth-3 or letter-live (f₁ ≥ 2, z₁ ≠ 1) consumer takes "η₂ ↔ z₂" as
accepted corpus, translates an FGMN residual into a repo digit string
dropping the z₁^{⌊ℓ₁u₂/e₁⌋} factor, and prescribes a wrong digit at
an f₃ ≥ 2 slot — flipping irreducible ↔ split exactly as the G3/F3
teeth demonstrate digits can.

**[F2] GAP — B′'s h-step applies B-1 outside B-1's stated scope
(S5.1 proof).** Quoted: "The element h := g − ẑ_d·n̂₂(β̂) has repo
digit 0 at grade β, hence ν(h) > β by B-1's no-cancellation clause".
B-1 (S5 honesty box) is stated for "a deg < D₂ ladder element". But
deg(ẑ_d·n̂₂(β̂)) reaches m₃ = D₂ at the record's own frames: in the
N1 frame the minimal grade-0 monomial lift of η₂ is ẑ_{η₂} = xΦ′/4
(deg 3 — every grade-0 lift of an F₄∖F₂ class needs a deg-3 ladder
monomial there), and n̂₂(β̂) at odd β̂ is π^{a}x (deg 1), so the
product has deg 4 = m₃ and h is not Φ₂-free — e.g. grade 7, the very
grade the battery's F2 witness and PE1's digit table use:
ẑ_{η₂}·n̂₂(7) = (xΦ′/4)·8x = 2x²Φ′ = 2Φ₂b + 4xΦ′ + 4Φ′ + 16.
Repair (checked at this example): divide by Φ₂, kill the qΦ₂ part
with Lemma 3.17 once ν(qΦ₂) > β (here dv₂(2Φ₂b) = 2 + 7 = 9 > 7),
apply B-1 to the deg < D₂ remainder — automatic whenever e₃ ≥ 2
(λ₃ ∉ Γ₂ forces strictness) or ν(q) > 0; the residual corner
(e₃ = 1 with a unit-q overflow landing exactly AT grade) is not
excluded by anything written in the note. As written the derivation
has a scope hole at configurations the lemma quantifies over; the
conclusion held at each configuration I traced. Failure scenario: a
frame with e₃ = 1 and a unit-leading-coefficient lift product would
make the displayed proof's key inequality unjustified, and (3) at
that grade would rest on nothing.

**[F3] MINOR — unit-direction slip between the S5 fallback clause
and B′(5) (S5 honesty box).** The clause's hypothesis reads "repo
digit = u(β)·(ε-normalized digit)", which is the INVERSE of B′(3)'s
convention (R_{3,β}(g) = u(β)·digit(g), i.e. ε-normalized =
u·repo); with the box's u the law it then displays via "LEMMA
GENTOW2-B′(5)" would read y^{f₃} − Σ u(β_t)^{−1}c_t y^t. No
consequence — u ranges over arbitrary unit families and the
re-parameterization c_t ↦ u^{−1}c_t neutralizes either convention —
but the box and the lemma it cites disagree by u ↔ u^{−1}.

**[F4] MINOR — B′(4)'s biconditional conflates B-2's stated scope
with the consumed scope (S5.1).** "(4) B-2 ⟺ u(β) = 1 at each grade
the recipe uses": B-2 as stated in the honesty box quantifies over
Φ₂-free ladder elements at their grades (per-grade family), while the
displayed ⟺ is grade-restricted; the precise statement is per-grade
((digit = ε-coordinate at grade β) ⟺ u(β) = 1) plus "recipe needs
only the used grades". The honest-residue paragraph states the
consumed form correctly, so nothing downstream moves.

## A. WHAT I VERIFIED AND FOUND EXACT (the r1 surfaces, attacked)

* **The PDF identity leg, reproduced independently**: local
  docs/references/fgmn_residual_ideals_1305.0775v3.pdf has md5
  da846c82f1fcb619cefb3feb8164191e, sha256 651b0cef...f615f35,
  518,522 bytes — matching S6.1's pins — and my own fresh fetch of
  https://arxiv.org/pdf/1305.0775v3 (this pass, 2026-08-09) is
  BIT-IDENTICAL (same md5, same size). Page 1 carries the v3 stamp.
* **Provenance table: 16/16 rows re-verified against the rendered
  PDF pages by my own visual read** (charge asked for 5): Lemma 1.11
  p.6; Cor 1.13 p.7; Def 5.2 + Lemma 5.3 p.24; Cor 4.4 p.21; Cor 4.7
  pp.21–22; Cor 4.12 + proof construction p.22 INCLUDING the "degre"
  typo, visually present; Prop 5.7 p.25; eq (14) p.19; Cor 5.6 p.24;
  Thm 5.8 + degree-forcing display p.25; **Thm 6.3 + proof opening
  p.28 and Cor 6.4 + eq (23) p.29 — the load-bearing pair — verbatim
  down to "In particular, ℓᵢ = eᵢfᵢℓᵢ₊₁ for all 1 ≤ i < r" and "If
  F = φ, then both conditions φ|µF and v(φ(θ)) > µ(φ) hold"**; and
  the three [r1]-added cites: Cor 3.3 p.12 (single-pin existence,
  exactly as consumed), Lemma 3.17 p.19 (R_{i,α} vanishes on
  P_α^+(µᵢ), exactly the h-step's cite), Thm 4.8 p.22 (R̄_{r,0}
  F_r-algebra isomorphism; its proof's deg < φ_r, µ = 0 evaluation
  clause is precisely the grade-0 read B′ uses). Supporting pins
  also re-verified on the same pages: Prop 1.9 (p.6), Lemma 2.4
  shear (p.9), Def 3.1 + display (4) (p.12), eq (9) data (pp.15–16),
  eq (12) + operators (p.17), Def 3.15/3.16 (p.18), Def 3.18 + j₀
  (p.19), §6 header at the BOTTOM OF p.27 (the F5 repair is right),
  and — free hunt — Lemma 3.5 (p.13)/Prop 3.7 (p.14) fit the (H-f)
  improper-stage-collapse cite.
* **The corrected ledger-claim sentences (S1/S3/S6)**: each now
  states the true method (visual PDF read, decorrelated from the
  pdftotext layout) and the true prior scope (63091ce =
  local-extraction, GRTJC's set, overlap only Cor 4.7 + eq (14)) —
  consistent with PE1-F1's record and with what I re-checked.
* **B′ re-derivation**: the eq-(12) abscissa argument (gcd(h₃,e₃)=1
  forces s(β) = 0), the single-j₀ Def-3.16 instantiation R_{3,β}(g)
  = ε₂(β)·R_{2,β}(g)(z₂), u(β) ≠ 0 via exact grade + Cor 4.4(1),
  degree-0 via Cor 4.4(3), the Cor 4.7(1)/(2) additivity and
  grade-0-factor multiplicativity steps (β ∈ Γ₂ hypothesis holds at
  each use — Prop 1.9 for Φ₂-free elements), x₀- and g-freeness of
  u(β) — each step checks, subject to [F1] (identification label)
  and [F2] (the h-step's scope). Consequences (4)/(5) follow.
* **The corrected transformation law (F3 repair)**: the law
  R = y^{f₃} − Σ u(β_t)c_t y^t is what B′(5) gives; the digit
  re-parameterization c_t ↦ u(β_t)^{−1}c_t restores any admissible
  ψ₃; GENTOW2-A consumes only hypothesis (ii) so it is untouched; I
  re-ran PE1's F₄ counter-instance THROUGH the law (u ≡ ω fixed:
  recipe at (ω, 1) realizes y² + ω²y + ω, reducible — matches; the
  re-parameterized digits (1·? →) c′₁ = ω³ = 1, c′₀ = ω² restore
  y² + ωy + 1) — the counter-instance is now correctly a consequence
  of the law, not a defect of it; the f₃ ≤ 1 scope sentence is right
  (y − δc₀ monic irreducible, δc₀ ≠ 0). Modulo the [F3]-minor
  direction slip, the repair is sound.
* **GENTOW5-A1 non-supply**: checked GENTOW5_PROOF L129–170 — its
  ϑ_t compares per-height coherent digits against the multiplicative
  side residual, both against the SAME ladder normalizers n̂; it is
  repo-internal as the note now says, and cannot produce the
  cross-frame u(β).
* **S2 (e₃,f₃) row (F6 repair)**: eq (9) on p.16 does give
  m₄ = e₃f₃m₃; the witness recomputation checks by my own arithmetic
  (ν(Φ₂) = 21/8, e(µ₃) = 8, e(µ₂) = 4, e₃ = 2). Prop 5.7
  KP-membership one-liner (F4 repair): Lemma 5.3(1) applies to
  Φ₂ = φ₃ verbatim.
* **S9 repair record**: r1 commits touched only the note (zero diffs
  under verification/openmath/ for gentow2_* between 61daa69 and
  2146c23); sealed artifact md5s unchanged from PE1's pins.

## B. MACHINE-LEG INTEGRITY

* Pins re-verified at HEAD: gentow2_checks.py md5
  2603eb7c315da43146beb64cf5cf11af (= PE1 pin), run2 output
  832aa838497fdf5fa870a19fece0eb35 (= PE1 pin), gentow2_pe1_fresh.py
  a70dd986..., its output e66e8ea5....
* Isolated re-runs (fresh /tmp copies, this pass): sealed battery →
  BIT-IDENTICAL output (md5 832aa838...), 41 checks / 0 violations,
  teeth {T1: True, T2p: True}, GREEN; PE1 fresh runner →
  BIT-IDENTICAL (md5 e66e8ea5...), 20/0 GREEN.
* Tautology audit (delta over PE1's, which I re-checked in outline):
  the PE2 fresh runner below reuses only the A-route integer
  arithmetic + gp harness; every prediction is a hand-derived literal
  in its sealed docstring; A-route (own polynomial division, Bareiss
  determinants) and B-route (PARI factorpadic/idealprimedec/nfeltval
  in a subprocess) remain computationally decorrelated.

## E. FRESH ROUTE (this pass; runner gentow2_pe2_fresh.py SEALED at
## 090f501 before its first run; output gentow2_pe2_fresh_output.txt
## — 22 checks / 0 violations, GREEN)

Route disjoint from the sealed battery (f₃ ≤ 2 throughout) and PE1's
corner (f₃ = 2): the FIRST f₃ = 3 witnesses anywhere, N1 frame,
e₃ = 1, u₃ = κ₃ = 7 > 6 = floor, deg Φ₃ = 12, plus the first side
whose ψ₂-power residual support is NOT full:

* **G1** = Φ₂b³ − 32xΦ′Φ₂b − 1024x (ψ₃ = y³ + ωy + 1, no F₄ root):
  predicted and got sig [(2,6)], nfeltval (1,3,7), resultants
  (6,18,42), Φ₂b-pins {0:21, 1:14, 3:0} on side of slope 7 with
  support {0,1,3} = supp(ψ₃), and — the sharp new clause-(c) test —
  Φ′-side support {0,1,3,5,6} = supp(ψ₂³ = T⁶+T⁵+T³+T+1) with the
  j = 2, 4 pins STRICTLY ABOVE the side (got 14 > 12 and 7 > 6).
  EXACT on both oracles.
* **G2** = Φ₂b³ − 4Φ′Φ₂b² − 1024x (ψ₃ = y³ + ωy² + 1 — the first
  witness anywhere with a nonzero y²-digit): sig [(2,6)], triple
  (1,3,7), pins {0:21, 2:7, 3:0}, support {0,2,3}. EXACT.
* **G3 (tooth, FIRED)** = Φ₂b³ − 32xΦ′Φ₂b − 512Φ′ (c₀ flipped
  1 → ω: ψ₃ = y³ + ωy + ω = (y+ω)(y²+ωy+1), split into DISTINCT
  irreducible factors): A-route polygon AND supports bit-identical
  to G1 at both levels, yet PARI returns [(2,2),(2,4)] exactly as
  Thm 6.6 predicts (deg-4 piece (2,2) for the linear factor, deg-8
  piece (2,4) for the quadratic). Three digits, three grades, and
  the digit string alone separates G1 from G3 — the ψ₃-provisos and
  the digit reading are load-bearing at f₃ = 3.

What the route does NOT touch (recorded per [F1]): each witness here,
as in the sealed record, has f₁ = 1 over q = 2 (z₁ = 1), so the
letter-twist surface of [F1] and the u ≢ 1 surface of B-2 stay
machine-untested; a letter-live probe needs an f₁ ≥ 2 tower (first
candidate geography: HETOW's frame-Y family) and is the natural PE3
fresh route if a repair round lands.

## G. GRADE LINE

**passPE2 verdict: NOT CLEAN (2 GAP: F1 identification
label/attribution in S5.1 with the explicit canonical formula
z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}; F2 B-1 scope overflow in B′'s h-step; +
2 MINOR: F3 unit-direction slip, F4 scope conflation in B′(4)).
Zero CRITICAL: the r1 repairs of PE1's F1–F6 each held under
re-derivation and PDF re-reading; the FGMN citation surfaces
(16/16 rows), the theorem chain S4/S5, the corrected transformation
law, the machine legs (bit-identical isolated re-runs), and the new
f₃ = 3 fresh route (22/0, tooth fired) all survived. The counter
does NOT start: 0/2 stands. Repair guidance: F1 — restate the
identification as the canonical Prop-1.15 evaluation isomorphism,
display the letter formula (or prove η₂ ↔ z₂ where true), and fix
the S2 row/S4-(c) parenthetical to "equal up to the z₁-twist,
coherent under the single embedding"; F2 — add the divide-by-Φ₂ +
Lemma 3.17 step with the e₃ = 1 corner argued or fenced; F3/F4 —
one-line rewordings. Fresh-route artifacts committed:
verification/openmath/gentow2_pe2_fresh.py (sealed 090f501) +
gentow2_pe2_fresh_output.txt.**
