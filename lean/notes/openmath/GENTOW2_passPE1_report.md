# GENTOW2 passPE1 — HOSTILE VERIFIER REPORT (fresh context), 2026-08-09

**VERDICT: NOT CLEAN — 0 CRITICAL + 3 JUSTIFICATION GAPS + 3 MINOR. The
FGMN citation itself is FAITHFUL where I could test it: 10/10 verbatim
quotes match the local print character-for-character at the claimed line
numbers, the instantiation map holds at each walked hypothesis, the
machine leg is bit-identical on isolated re-run (41/0, exit 0), and a
NEW fresh-route family at the machine-unwitnessed F₄ × f₃ = 2 corner
came back 20/0 GREEN with the tooth firing. The three GAPs are two
PROVENANCE over-claims (the numbering-ledger method/scope; B-2's
"accepted corpus" pointer) plus a false robustness clause inside the
B-2 honesty box — none breaks the theorem chain, but each misstates
what the record rests on. Counter stays 0/2.**

Target: lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md at HEAD (531c212).
Charge: quote-and-classify, fix nothing; CLEAN bar = nothing GAP-or-worse.
Source print: docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt
(2057 lines). Ledger commit examined: 63091ce. Runner seal chain examined:
c33f10e → 85f59f6 → HEAD.

## F. FINDINGS

**[F1] GAP — the numbering-provenance sentence over-claims the ledger's
method AND scope (S6, note L301–302; also S1 L18, S3 L81).** Quoted
(S6): "numbering verified against the arXiv v3 PDF at ledger 63091ce."
The ledger annex itself (BRIDGE_ADJUDICATIONS_2026-07-30.md L12001–12016
+ the GRTJC annex written at 63091ce) says the opposite on method —
"Caveat (extraction-decorrelation rule): verified against the local text
extraction" — and its scope is GRTJC's cite set only: Thm 4.2 @1028,
Thm 4.8 @1136, Cor 2.7 @525, Cor 4.7 @1121, eq (14) @1004, Lemma 5.13
@1403, Cor 4.9 @1153. Of GENTOW2's 12 consumed statements, exactly 2
(Cor 4.7, eq (14)) are in that set; Lemma 1.11, Cor 1.13, Def 5.2,
Lemma 5.3, Cor 4.4, Cor 4.12, Prop 5.7, Cor 5.6, Thm 5.8, Thm 6.3 and
**Cor 6.4 — THE theorem** — have no ledger coverage and no PDF leg
anywhere in the repo. Failure scenario: an extraction artifact in the
print's §5–§6 text (the corpus has precedent — the GRB Def-3.15
extraction artifact) would propagate into the "verified" cite while the
provenance sentence points at a ledger that never looked there.
Mitigation established BY THIS PASS, not by the note: section A below
re-verifies the 10 quotes against the print, and the battery + fresh
route give Cor 6.4's content a non-textual leg at 10 witnesses.

**[F2] GAP — B-2's provenance pointer is unsubstantiated (S5 honesty
box, note L284–287).** Quoted: "(B-2) the repo's K₂-digit alphabet is
the ε₂-normalized F₃-coordinate of FGMN's Def 3.16 (this is the [W-2]
graded-dictionary identification at level 2, the same one T(b)′'s proof
already uses to read residuals ...)". Checked both pointers: GRTW2 (the
W-2 note) contains zero occurrences of "FGMN"/"1305.0775"/"3.16" — its
dictionary is with a different source (tex 1431); GENHN_PROOF (T(b)′,
S8 annex) contains zero occurrences of Def-3.16/ε-normalization. The
identification repo-digit ↔ FGMN Def-3.16 ε₂-coordinate is FIRST made
in GENTOW2 itself. The disclosure as consumed-not-reproved is honest
and correctly quarantines it outside the FGMN citation; the "accepted
corpus" attribution is not correct as pointed. Failure scenario: a
future audit treats B-2 as already 2/2-accepted via [W-2] and builds on
it without an arc. Mitigation (this pass): the fresh-route pair F2/F3
(section E) machine-tests exactly this identification at a non-F₂ digit
(c₁ = η₂ ∈ F₄∖F₂) — a twist would have flipped irreducible ↔ split —
and it held exactly.

**[F3] GAP — the B-2 fallback clause is false as stated for f₃ ≥ 2
(S5 honesty box, note L287–294).** Quoted: "if a future audit finds the
repo digit differs from the ε-normalized digit by a fixed unit, the
recipe's c_t simply re-parameterizes — ψ₃ changes by the substitution
y ↦ εy ... and every clause of GENTOW2-A survives verbatim". Two
defects. (i) Mechanism mismatch: a FIXED unit discrepancy δ on the
digits gives R = y^{f₃} − δ·Σc_t y^t, while y ↦ εy rescales coefficient
t by ε^{t−f₃} — the geometric (grade-covariant) pattern, not the fixed
one; the two agree only at f₃ ≤ 1. (ii) Counter-instance to "survives
verbatim": over K₂ = F₄, ψ₃ = y² + ωy + 1 is irreducible (no F₄ root),
but a fixed-unit discrepancy δ = ω gives y² + ω²y + ω, which has the
root y = 1 (1 + ω² + ω = 0) — reducible, so hypothesis (ii) of
GENTOW2-A dies and clause (a) fails. Also (iii): Def 3.15's ε₂ is
multiplicative only up to a z₂-carry cocycle (eq (12), print L881:
u(α)eᵢ + s(α)hᵢ = e(µᵢ)α with 0 ≤ s(α) < eᵢ, so s is a bounded residue,
not additive), i.e. the grade-VARYING discrepancy mode — the one the
campaign already met as GENTOW-4's η₂-cocycle/coh() finding — is not
covered by the clause at all. The main chain is unaffected (it consumes
B-2 on the nose), but the box's robustness sentence should not survive
a repair round as written.

**[F4] MINOR — Prop 5.7 is applied to the pair (Φ₃, Φ₂) without noting
Φ₂ ∈ KP(ν) (S4, note L198–202).** The (2)⇔(3) equivalence quoted at
[Q7] requires both arguments in KP(µ); Φ₂ = φ₃ ∈ KP(ν) follows from
Lemma 5.3(1) (deg φ₃ = m₃, φ₃ ∼_ν φ₃), one line the note omits.

**[F5] MINOR — §6-header pin off by one (S4, note L155).** "their §6
header, L1434": the header "6. MacLane-Okutsu invariants of prime
polynomials" is at print L1433 (L1434 is the section's first sentence).
The other 14 line-number pins I checked are exact (section A).

**[F6] MINOR — S2 dictionary row "FGMN e₄-level data" (note L57).**
The (e₃, f₃) row names the fourth-augmentation data "e₄-level" without
definition; it means the data of the augmentation [ν; (Φ₃, ·)] (FGMN's
e_{r+1} with r = 3). Harmless but a fresh reader cannot resolve "e₄"
from the note.

## A. FAITHFULNESS AUDIT — the core charge

**A.1 Quotes vs the local print: 10/10 MATCH.** Each of [Q1]–[Q10]
was read at the claimed lines and compared character-for-character
(modulo three disclosed-by-convention transcription classes: the
print's OCR "6=" for ≠, lost overlines K v → K̄v, and superscript
reconstruction φℓi i → φi^{ℓi}). Line pins verified exact: Q1
Lemma 1.11 @275; Q2 Cor 1.13 @315; Q3 Def 5.2 @1238–1239; Q4
Lemma 5.3 @1240–1244; Q5 Cor 4.12 @1161–1163 + construction
@1164–1166; Q6 Thm 5.8 display @1296–1302; Q7 Prop 5.7 @1276–1281 +
eq (14) @1004; Q8 Cor 4.7 @1121–1126; Q9 Thm 6.3 @1458–1464 + proof
opening @1465; Q10 Cor 6.4 @1523–1527. Supporting pins verified: N_i
@871, ψ_i @862, Cor 5.6 @1263–1265, data table @785–803, Def 3.1 +
display (4) @608–615, Lemma 2.4 @464, Def 3.16 @916–923, Def 3.18
@994–1000 (j₀ formula @1000), Cor 4.4(4) @1089, Prop 1.9 @258. The
note even preserves the print's typo "degre" in Q5 — transcription is
verbatim, not paraphrase. Two ellipses (Q5, Q6) drop only attribution
clauses ("by item 2 of Corollary 4.12"), no mathematical content.
The print-vs-arXiv leg is NOT closed by the note's cited ledger — that
is finding [F1]; the internal cross-reference structure of the print
(Cor 6.4's proof citing Cor 5.4/5.15, Thm 6.3, Lemmas 2.2/3.4, all
present at consistent numbering) is coherent, and the mathematical
content of the load-bearing statements is machine-confirmed (D, E).

**A.2 Instantiation map: each hypothesis walked, HOLDS.**
(i) F ∈ P: Φ₃ monic (hyp), irreducible in K_v[x] by Lemma 1.11 once
Φ₃ ∈ KP(ν), O-coefficients by Cor 1.13 — and KP-membership is the
degree-forcing argument of Q6 run on Φ₃: deg Φ₃ = e₃f₃m₃ ≥ s′m₃ ≥
(s′−s)m₃ = e₃(deg ψ₃)m₃ = deg Φ₃ (middle equality = Cor 4.4(4) with
deg R₃(Φ₃) = f₃), forcing s = 0, deg = s′m₃ — Lemma 5.3(2) verbatim.
Sound. (ii) φ|_ν F at F = φ: quoted from the print's own proof opening
(L1465). (iii) φ ≁_ν φ₃: eq (14) gives R₃(Φ₂) = 1, hypothesis gives
R₃(Φ₃) = ψ₃ ≠ 1, Prop 5.7 (2)⇔(3) separates — modulo [F4]'s one-line
omission. (iv) Chain of length 3 as in (4): the tower's stages with
strictly growing degrees; properness e₂f₂ ≥ 2, e₃f₃ ≥ 2 displayed as
provisos. (v) Cor 4.7(2)'s grade hypothesis β ∈ Γ_{i−1}: both grades
in the S5 application land in Γ₂ (β = ν(k̂_t) = µ₂(k̂_t) ∈ Γ₂;
α_t = e₃t(w₃+λ₃) ∈ Γ₂ since e₃(w₃+λ₃) = e₃w₃ + e₃λ₃ ∈ Γ₂) — holds
under either role assignment. (vi) s(α) = 0 for α = e₃f₃(w₃+λ₃):
α ∈ Γ₂ as above, so the eq-(12) residue vanishes — the S5 abscissa
bookkeeping is right.

**A.3 The normalization shear: consistent in both directions.** The
map (j, y) ↦ (j, y/e(µ₁) + j·w₂) is affine, abscissa-preserving,
invertible; it carries repo pins (j, dv₁(a_j)) to FGMN pins
(j, µ₁(a_j) + jw₂) exactly when dv₁ = e(µ₁)v on the sub-deg-Φ′
coefficients (B-1 territory, see B below). One-sidedness incl. the
endpoint conditions (Def 5.2: s = 0, s′ > 0) transports because
abscissas are fixed. Witness re-computed by hand: w₂ = µ₁(x²−2) =
min(2·½, 1) = 1, e(µ₁) = 2; (4,0) ↦ (4,4), (2,7) ↦ (2,11/2),
(0,10) ↦ (0,5); repo slope 5/2 ↔ FGMN slope −¼ = −λ₂ under
κ₂ = e(µ₁)(w₂+λ₂) = 5/2. Exact.

**A.4 Cor 6.4's conclusions → clauses (b)(c)(d)(e): faithful.**
ℓ₂ = e₂f₂ℓ₃ is the quoted "in particular"; ℓ₃ = deg Φ₃/deg Φ₂ = e₃f₃
from (23) at i = 3; R₂(Φ₃) = ψ₂^{ℓ₃} is (23)'s residual clause at
i = 3 with FGMN-ψ₂ = repo-ψ₂ via Cor 5.6(2); µ(φᵢ) = v(φᵢ(θ)) at
i = 1,2,3 gives (d) for each root of the irreducible F (θ arbitrary
root — stated per-root in Thm 6.3's setting). The degree consistency
check deg R₂ = ℓ₂/e₂ = f₂e₃f₃ re-verified via Cor 4.4(4). No
statement stretched beyond its quoted content.

## B. BRIDGE LEMMA GENTOW2-B + B-1/B-2

**Structure sound given B-1/B-2.** Additivity (Cor 4.7(1)) needs each
term in P_α(µ₃) with exact grade — supplied by ν(k̂_t) = µ₂(k̂_t) =
dv₂-height/e(µ₂) (B-1; the Φ₂-freeness leg is Prop 1.9 as cited, since
deg k̂_t < deg Φ₂ and Φ₂ is µ₂-minimal). B-1 itself is thinner than
its billing: for ladder MONOMIALS π^a x^i Φ′^b the value
µ₂ = (ae₁e₂ + ie₂h + bu₂)/(e₁e₂) is direct FGMN Def-1.8 arithmetic
(augmented valuations are DEFINED as expansion-minima); GENHN-2′ is
needed only for exactness on multi-monomial K₂-digit lifts (its
no-cancellation/class-separation clause). Consumed-as-corpus: fine.
B-2 is the real identification and carries findings [F2]/[F3]; its
on-the-nose form is what the proof uses, DISCLOSED, and now
machine-supported at the corner configuration (section E). The
adjudication asked for: disclosed ≠ derived — correct, B-2 is NOT
derived anywhere in the corpus I could find; the note's conditionality
disclosure is honest, its provenance pointer is not ([F2]).

## C. PROVISOS + CONSUMERS

The three provisos (ψ₃ monic irreducible /K₂ with ψ₃(0) ≠ 0;
e₃f₃ ≥ 2; λ₃ > 0 i.e. κ₃ > e₂f₂u₂) are displayed in the theorem
statement and again in S6 (H-f)/(what-the-cite-does-NOT-give (ii)).
GENTOW5 (the consumer at HEAD): carries properness l_i ≥ 2 explicitly
in DEF GENTOW5-1 with the GENTOW2 S6 (H-f) cite; carries the floor as
"heights u_i satisfying the floor chain u_{i+1} > ..." (its L476);
stage residuals are minimal polynomials (irreducible by construction).
No consumer found dropping a proviso. The (β)-rides-GENTOW-1 claim
cross-checked: GENTOW1_PROOF's status table has the quoted rows
("(1) rider: depth-3 floor (6)(beta) | COR GENTOW-1.1 | PROVED
(S2.4)"), cited as in-flight 0/2 — accurate, honest. The GENHN
consumption-side wording ("v(Φ′(ξ)) = u₂/(e₁e₂) exact with η₂(ξ) a
ψ₂-root...") matches GENHN_PROOF L1421–1423 verbatim; GENTOW2-A(c)+(d)
do discharge (α) as stated there.

## D. MACHINE-LEG INTEGRITY

* **Seal chain**: runner sealed at c33f10e (355 lines, predictions
  P-W1..P-N2 + teeth T1/T2 in docstring, note S8 marked PENDING);
  85f59f6 = the disclosed T2-failure + T2′ reseal — diff inspected:
  docstring disclosure + PHI3T2P + scoring switch ONLY, sealed
  predictions untouched, T2 kept as unscored record; HEAD runner
  byte-identical to 85f59f6 (md5 2603eb7c315da43146beb64cf5cf11af).
  T2′ preregistered before its first run per the commit sequence
  (85f59f6 before the run2 artifact at 2b19fbc). Seal discipline held.
* **Isolated re-run** (/tmp copy, this pass): output BIT-IDENTICAL to
  the committed gentow2_checks_output_run2.txt (md5
  832aa838497fdf5fa870a19fece0eb35 both), 41 checks / 0 violations,
  teeth {T1: True, T2p: True}, exit code 0.
* **Tautology audit: PASS.** A-route pins/hull/support/resultants are
  exact integer arithmetic (own polynomial division + Bareiss dets);
  predictions are hard-coded literals; B-route is PARI factorpadic +
  idealprimedec + nfeltval in a separate process. The two (d)-legs are
  computationally decorrelated: Σ-over-all-roots (resultant 2-adic
  valuations, deg·v) vs single-prime nfeltval (e·v). The on-side
  support sets genuinely test clause (c)'s ψ₂-power law (e.g. N1:
  {0,2,4} = supp(T⁴+T²+1) = supp(ψ₂²) at e₂ = 1). T1's h0 is
  self-referenced (pinsT1.get(0)) but T1 asserts a NEGATIVE, so no
  tautology. The T2-failed-as-designed record is reproduced and the
  corrected reading (prime power ≠ reducible; Thm 6.6 splits across
  distinct (λ, L) only) is the correct reading of the print.
* **Coverage hole (feeds [F2]/[F3], now closed by E)**: no sealed
  witness has BOTH K₂ = F₄ AND f₃ ≥ 2 — N1 is F₄ with f₃ = 1 (single
  digit, class 1), N2 is f₃ = 2 over K₂ = F₂ (ε-effects invisible).
  The sealed battery therefore never exercised a non-F₂ digit.

## E. FRESH ROUTE (this pass; runner gentow2_pe1_fresh.py, output
## gentow2_pe1_fresh_output.txt — 20 checks / 0 violations, GREEN)

Three new witnesses at the N1 tower (K₂ = F₄, η₂ = class(Φ′/2x)),
predictions preregistered in the script docstring before the run,
derived by hand from GENTOW2-A/B + the digit table (heights 7/13/14):

* **F1** = Φ₂b² − 32Φ′ (f₃ = 1, e₃ = 2, digit η₂ ∈ F₄∖F₂ — first
  non-F₂ digit anywhere): predicted sig [(4,2)], nfeltval (2,6,13),
  Φ′-side (0,12)–(4,0) support {0,2,4}, resultants (4,12,26) — ALL
  EXACT on both oracles.
* **F2** = Φ₂b² − 4Φ′Φ₂b − 128 (the machine-unwitnessed corner:
  f₃ = 2 AND K₂ = F₄; digits (c₁,c₀) = (η₂,1), ψ₃ = y²+ωy+1
  irreducible over F₄): predicted irreducible, sig [(2,4)], nfeltval
  (1,3,7), Φ₂b-pins {0:14,1:7,2:0} all on side, resultants (4,12,28)
  — ALL EXACT. This is the configuration where a B-2 twist would
  strike; it did not.
* **F3 (tooth, fired)** = Φ₂b² − 4Φ′Φ₂b − 32xΦ′ − 128 (c₀ flipped
  1 → ω²; ψ₃ = y²+ωy+ω² = (y+1)(y+ω²) splits with DISTINCT roots):
  A-route polygon IDENTICAL to F2's (one-sided, full support), yet
  PARI factors [(2,2),(2,2)] as Thm 6.6 predicts. The polygon cannot
  separate F2 from F3 — only the K₂-digit can, and the ε-normalized
  digit reading called both correctly. Confirms the ψ₃-irreducibility
  proviso is load-bearing at the F₄ corner and gives B-2 its first
  nontrivial-unit machine support.

## G. GRADE LINE

**passPE1 verdict: NOT CLEAN (3 GAP: F1 provenance-method/scope, F2
provenance-pointer, F3 false fallback clause; + 3 MINOR: F4/F5/F6).
Zero CRITICAL: the citation's mathematical content, instantiation, and
machine legs each survived hostile re-derivation, isolated re-run, and
a new boundary-family attack. Acceptance counter stays 0/2; the three
GAPs are repairable by rewording (F1: state the ledger's true method +
add a print-vs-PDF or second-extraction leg for the §5/§6 statements;
F2: re-point B-2 as a NEW disclosed identification of this note; F3:
delete or correctly scope the fallback sentence). Fresh-route artifacts
committed: verification/openmath/gentow2_pe1_fresh.py +
gentow2_pe1_fresh_output.txt.**
