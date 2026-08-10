# GENTOW6 passPE1 — HOSTILE VERIFIER REPORT (first pass), 2026-08-10

**Target:** `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md` @ HEAD
(verdict commit 5fb8fd7, 2026-08-09 19:48). Grade at entry: 0/2
(attempt, arc unopened). Protocol: quote-and-classify, fix nothing.

**VERDICT: NOT CLEAN — 1 CRITICAL (F-1, the gauge/f1 seam at
THEOREM GENTOW-6.3's genre quantifier) + 1 GAP (F-2, GENTOW-5(a)
consumed at f out of its proved 𝒯 scope) + 4 MINOR. The S1 tie
(LEMMA GENTOW-6.1) and the S2 block layer survived every leg I ran;
CERT-TOP (6.3(b)) survived re-derivation and a fresh corner witness
at f1 = 1 — the CRITICAL is the theorem's claimed scope, not its
f1 = 1 content. Machine leg reproduced bit-equivalent; fresh route
GREEN 22/0 on two out-of-battery frames. Counter stays 0/2.**

## Timeline fact (governs the gauge audit)

All five GENTOW6 commits (9f88663 16:30 → 5fb8fd7 19:48, 08-09)
PREDATE the GENHN dated gauge erratum 59c1966 (08-09 20:13,
ĉ_t := lift(c_t·η^{W(t)}), W(t) = floor((f2−t)i(u2)/e1)). The note
carries NO gauge pin; both sibling notes it restates its S3 setting
from have since needed one (GENTOW1 GT1-r1 S7.1; GENTOW3 GT3-r1
S7.1, 2026-08-10 — which also re-scoped the x-free i-test to
f1 = 1 and derived the f1 ≥ 2 lift shape this pass uses in F-1).

## FINDINGS

### F-1 (CRITICAL) — THEOREM GENTOW-6.3 (a)/(c)/quadrichotomy read
### the key's lift coefficients as x-free scalars; the "at any tower
### genre" quantifier fails at f1 ≥ 2 under the corrected lifts

Quotes (S3): theorem head "**THEOREM GENTOW-6.3 (attainment at
mu2 = 2, every genre).** For f = Phi2^2 at any tower genre"; setting
"Phi2 = Phi'^{e2f2} − Sum_{t in T} chat_t·nhat(u2(f2−t))·Phi'^{e2t}"
(chat_t a scalar; no gauge pin); (a)'s census "the pair terms
chat_t chat_{t'} nhat_t nhat_{t'} Y^{e2(t+t')} of x-degree
i_t + i_{t'}"; (c) "if i_t + i_{t'} < D' for every pair (t, t') in
T^2, then the level-1 development of Phi2^2 equals K2(x, Y)^2 term
by term on the grid (no x-carry ever fires)"; setting "X-FREE genre
⟺ i_t = 0 for every t in T (GENTOW-3's definition)".

The defect. At f1 ≥ 2 the composed key's lift coefficient is NOT
scalar·monomial: per GENTOW3 S7.1 (GT3-r1, accepted repair) and
HETOW r1 F-4, the height-m_t lift of c_t·η^{W(t)} ∈ K = F_{Q^{f1}}
has x-support {i_t + e1·r : λ_r ≠ 0} (λ_r the η-basis components),
pairwise distinct, all < D'. Consequences at f1 ≥ 2:
* (c) is FALSE-in-general there: its hypothesis holds at EVERY
  f1 ≥ 2 genre (i_t + i_{t'} ≤ 2e1−2 < e1f1 = D'), yet whenever
  some c_t·η^{W(t)} ∉ F_Q the pair (t,t) product carries the
  monomial x^{2(i_t+e1·r_max)} of degree ≥ 2e1 ≥ D' (f1 = 2) with
  unit coefficient λ_{r_max}² — an x-carry fires and "equals K2²
  term by term" fails. Failure scenario: Q = 2, f1 = 2, K = F_4,
  any genre datum with a ψ2-coefficient c_t·η^{W(t)} ∈ F_4 ∖ F_2
  (realizable as a residual by FGMN Cor 4.12); a consumer applies
  (c), prices the key power shadow-EXACT, and the shadow diverges.
* (a)'s overflow census (pairs classified by i_t + i_{t'} ≥ D',
  branch positions (x^{i_t+i_{t'}}, Y^{e2(t+t')})) misses the
  chat-driven monomials at those genres; the regime boundaries of
  the "QUADRICHOTOMY" inherit this.
* (b) [CERT-TOP] is VACUOUS at f1 ≥ 2 — 2i_{t*} ≤ 2e1−2 < e1f1 =
  D', so regime 2 is an f1 = 1 phenomenon — hence not false; but
  the note nowhere says so, and the S5 consumption line
  "GENTOW3-BOX-1 CLOSED AT mu2 = 2" silently includes f1 ≥ 2
  genres where nothing is delivered (GENTOW3-BOX-1's ask was
  "genre-general").
* The adopted X-FREE i-test is exactly the clause GT3-r1 proved
  f1 = 1-only; regime (1) of the quadrichotomy consumes it.

At f1 = 1 the proof of (a)/(b)/(c) is CORRECT: I re-derived the
weight ledger (all K2² terms at 2E2 exactly; extraction = +delta;
lift-emission steps lower absolute Y-position by e2(f2−s) ≥
e2(f2−t*) > 0; quotient transfers position-invariant), the (t*,t*)
uniqueness at absolute position B*+1, the division-vs-development
branch match (the shadow's reduced quotient·K2 products drop
exactly the development-time Phi'-branches — one surviving branch
per overflowing pair), and the digit (chat_{t*})²π^{2a_{t*}}·unit;
and my fresh corner witness (leg B below) confirms the display at
an out-of-battery geometry. Repair shape: an f1 = 1 scope pin on
6.3(a)/(c)/(d) + the quadrichotomy + the S5 consumption line (or a
re-derivation at the (LIFT)-shaped coefficients), plus the missing
gauge pin on the S3 setting (GT1-r1/GT3-r1 pattern). Machine leg is
structurally blind: every frame f1 = 1 (see F-3).

### F-2 (GAP) — COR GENTOW-6.2C(d) consumes GENTOW-5(a) at f, out
### of GENTOW-5's proved scope

Quote (S2, proof of 6.2C(d)): "a block digit consulted at block
height m corresponds through HE6R1-2(b) to f-data at height
m + c_g, and **f's window-N cap is e1e2·N (GENTOW-5(a) at f)**, so
the block read is lift-stable below e1e2·N − c_g."

LEMMA GENTOW-5 is stated and proved "**On 𝒯**" (GENTOW1 S4) — the
FULL-side locus. The f here is a partial-side member (deg n >
mu2*·D2, non-monic composed top): not on 𝒯. The undercut half of
the cap is 𝒯-free, but the in-window-stability half rides
GENTOW-5(e) → GENTOW-1(b) triangularity, both proved on 𝒯 only.
Failure scenario: a consumer runs the block budget test through
f's window-N data per (d) at a partial-side member; the claim that
every consulted f-datum below e1e2·N is lift-stable has no proved
supplier, so a window lift could flip a consulted digit and the
"caps consulted block heights at e1e2·N − c_g" display silently
over-trusts. Likely repairable (GENTOW-1 Step 3's triangularity
display is division-algebraic and does not visibly consume 𝒯
membership) — but that extension is nowhere written; downstream is
the cap, not the ledger (GENTOW6-BOX-2 is not implicated).

### F-3 (MINOR) — the machine-scope fence omits the gauge axis

S5 "Machine scope" names FAM-P5-geography limits and the missing
l·deg r = 4 row, but not: every frame in all three legs sits at
f1 = 1 AND level-1 η = 1 (Phi' ∈ {x²−2, x³−2, x²−3}: A5/A7/B/C/E/
R2X over Q2, P5/P3/P3b/D over Q3) — the sealed battery is
structurally blind to the gauge seam, the exact blindness GT3-r1
S7.1 disclosed for the same imported families. Exposed faces:
S1 Step I's "R^{(C)} = r^{k_r} exactly" / 6.2's "twist-coherent
residual psi2^{mu2*} exactly" monicity clauses (top-digit argument
stated but never machine-exercised at η ≠ 1; the tie itself is
scalar-robust — Step III's UFD match absorbs units into gamma*),
and the S3 digit values. No false sentence found; the fence is
under-disclosed.

### F-4 (MINOR) — cite-provenance over-attribution on Theorem 2.8

S0 header: "the FGMN local print (…layout.txt), **numbering
verified at GENTOW2's ledger**"; S1 Step II: "Quotes at the
verified layout numbering". GENTOW2's S6.1 PDF-provenance table
(22 rows + supporting pins) contains Cor 4.4 (row 5) and Cor 4.7
(row 6) but **NOT Theorem 2.8** — the polygon-additivity leg of
(MULT) rode the pdftotext extraction alone, exactly the
extraction-corruption seam the standing rule guards. The note's S5
partially discloses ("the S1 cite leg wants a PDF-provenance
re-verification in its own pass"). THIS PASS CLOSES THE LEG: PDF
p.10 read visually — "Theorem 2.8. Let µ be a valuation and φ a
key polynomial for µ. Then, N⁻_{µ,φ}(gh) = N⁻_{µ,φ}(g) +
N⁻_{µ,φ}(h) for any non-zero g, h ∈ K[x]" — verbatim MATCH with
the note's quote (layout L546; the note's "L543–546" includes the
preceding join-of-sides paragraph, which also supports the
"Minkowski sum, per-slope lengths add" gloss via Cor 2.7:
S_λ(gh) = S_λ(g) + S_λ(h), p.10). Cor 4.4(4) and Cor 4.7(3)
re-confirmed at layout L1084–1090 / L1121–1134 against the note's
quotes; PDF md5 da846c82f1fcb619cefb3feb8164191e confirmed. No
content corruption found — the finding is the attribution, not the
quote.

### F-5 (MINOR) — consumption-census slips

(i) COR GENTOW-6.2C fires "COROLLARY GENTOW-1.1" and "LEMMA
GENTOW-2 (at its stated scope)" — neither is itemized in S0's
sources line (GENTOW1_PROOF is listed, but its item list reads
"LEMMA GENTOW-1, Step 0, LEMMA GENTOW-5, E2"). (ii) S4 does not
print the runner/output md5s or the seal commit (sibling verdicts
do); the seal/verdict identity had to be reconstructed from git
(done below — clean).

### F-6 (MINOR) — COR GENTOW-6.1C(c) claims HE7-BOX-4's content in
### a sentence

"The same two ingredients … tie k = the multiplicity of r in
R_lambda at HE7-13'(a)'s level-2 blocks; this is HE7-BOX-4's
content" — an unexecuted level-2 transport (one more FGMN chain
link, level-2 coherent normalization unchecked) asserted as
content. It is properly fenced from consumption ("NOT consumed by
anything here"), so MINOR: the sentence should be marked as a
sketch/conjecture, not a result.

## BOX-FENCE AUDIT (charge item 3)

* **GENTOW6-BOX-1 (mu2 ≥ 3 attainment): HONEST.** THEOREM 6.3 and
  the quadrichotomy are scoped to mu2 = 2 at every display; the S5
  consumption line closes GENTOW3-BOX-1 "AT mu2 = 2" only; nothing
  in the note consumes mu2 ≥ 3 attainment. (The box text's own
  "the diagonal argument LOOKS uniform" is a flagged temptation,
  not a claim.)
* **GENTOW6-BOX-2 (partial-side count LEDGER): HONEST as to its
  named content.** S2 delivers the per-block budget/count layer
  only; the product-measure pricing of (f_S, g) ↦ f_S·g is named
  open and consumed nowhere. Adjacent leak: the window-CAP claim
  at partial-side f (F-2) sits outside every box — it is not the
  boxed ledger, but it is an unproved partial-side claim that
  escaped fencing.
* **GENTOW6-BOX-3 (regime-3 classification): HONEST.** 6.3(d) and
  quadrichotomy clause (3) are display-only ("NOT claimed as a
  theorem"); E-ENTRY is a PARI-adjudicated construction. The
  regime BOUNDARIES themselves inherit F-1's f1 = 1 scope.
* **Cite-conditionality box (S1/S5): HONEST** — "the cite alone
  carries the load", GENTOW2's upstream grade named; see F-4 for
  the one provenance slip.

## SIBLING-ARC LESSONS (charge checklist)

1. **GAUGE SEAM: HIT** — F-1 (+F-3). The note predates erratum
   59c1966 and carries no ĉ_t pin; 7/7 sibling first-passes now.
2. **ψ vs ψ^{(w)}: VERIFIED CLEAN.** The tie consumes the depth-2
   chain only (µ₀ →(x,h/e1)→ µ₁ →(Φ',λ)→ µ₂; R₂); w :=
   R_{3,κ̄}(n̂₂(u₃)) is level-3 and enters no display. The twist
   that does enter — GENTOW2's [r2] z₁-twist row, minpoly(η₂c) =
   c^{f₂}ψ₂(y/c), c = z₁^{−⌊ℓ₁u₂/e₁⌋} ∈ F₁ fixed per side — is a
   fixed variable rescaling: a K-algebra automorphism of K[T]
   preserving irreducibility, degrees, multiplicities, which is
   all Step II transports; Step III's UFD match runs entirely in
   the repo normalization (both sides of the displayed equation),
   so no factor-identity transport is consumed. The PE6 walk's
   "w-free, twist absorbed" reading is confirmed at the displays.
3. **Certificate-free attainment sentences: CLEAN at f1 = 1** —
   6.3(b) IS the certificate (re-derived; fresh corner witness);
   regime-3 attainment correctly boxed (BOX-3). Scope caveat = F-1.
4. **Universal records: CLEAN** — the S5 record block is
   enumerative (battery rows only); no universal quantifier found
   in record sentences.
5. **Stage-index conflation: CLEAN** — repo "level-1 residual" =
   FGMN depth-2 R₂ throughout, consistent with GENTOW2's
   dictionary (ψ₂ = R₂(φ₃), Cor 5.6(2) at L1263); the per-side
   chain instantiation (λ = shear image of κ, valid since κ > D'h
   by GENTOW-4.1(a), acknowledged in the scope remark) is coherent.
6. **Supplier census: two slips (F-5(i))**; everything else
   consumed is listed (HE7-5/6/11, HE6-3/4, HE7-13'(a), HE6R1-2,
   GENTOW-4.A/4.2/4.C, GENTOW-3 Step 2, GENTOW-1/5, FGMN print).
   HE6-3/HE6-4 hypotheses at f_C re-checked against HE6_PROOF
   (monic ✓, disc ≠ 0 as divisor of f ✓, Phi' ∤ f_C ✓, rootwise
   opening locus ✓; the letter β_ρ is intrinsic to ρ, so the
   HE6-4 class-tie r' = r argument is sound within HE6's
   normalization).

## MACHINE LEG (charge item 4)

* **Seal integrity:** runner md5 121e5c4a95a19692db7910b9ffedfd6e
  IDENTICAL at seal commit 59ea785, verdict commit 5fb8fd7, and
  HEAD; output artifact md5 1bcb950618de39f26fe8e0c298abb783 at
  HEAD; no post-seal edit.
* **Isolated re-run (this pass):** GREEN — 401 checks, 0
  violations, 4/4 teeth (T-TIE-CONST x22, T-CERT-V x7, T-ODDP x2,
  T-SHEXACT x1), exit 0; output content-identical to the committed
  artifact modulo one environmental gp stack-size stderr line and
  the timing suffix. Cert digits 16/64/4/64/64/324/81 reproduced.
* **Tautology audit: PASS** — m_r and mu2*(r) are measured by
  disjoint code paths (level-1 res_factor on side digits vs
  composed_read at the class key), with the PARI nodev6
  class-degree sums as a third, out-of-process leg; the cert rows'
  digit values have the hand-derivation as their decorrelated leg
  (disclosed as observed in the pre-seal smoke). T-TIE-CONST is an
  implicit-count tooth (m ≠ 2 rows), weaker than a mutant-run but
  legitimate; the smoke disclosure (reproduction-row PEEL fix,
  digits observed pre-seal) is honest.
* **Constants re-derived by hand:** A5/A7/B/C/R2X/P3/P3b (i_t,
  a_t, t*, a*, b*, j*, E2, delta, THETA, v* = 2a_{t*}) — all seven
  rows' preregistered values check out, including GEN-R2X's
  (a*,b*) = (1,1), v = 6, THETA_0 = 49 and FAM-B's two-coordinate
  grid; "the four B1 families sit in regime 2" verified (2i_{t*}
  ≥ D' at each).

## FRESH ROUTE (charge: out-of-battery mixed-side frame, both sides
## live + a unit-square corner case)

Instrument `verification/openmath/gentow6_pe1_fresh.py` (this pass;
independent code, no import of the note's runners; predictions
preregistered in the docstring from the note's displays before the
run). **GREEN — 22 checks, 0 violations, exit 0.**

* **LEG A — the (2,2) tie, both sides live.** Q3, Phi' = x²−3,
  inner slope 5/2; f = f_+·f_-·(Phi'−27), deg 18, mu1 = 9: a MIXED
  side [1,9] with BOTH classes REPEATED — residual (T+1)²(T−1)²,
  profile (2,2), absent from the battery's four profiles — plus a
  live sibling side (slope 6, length 1; every battery mixed row
  was single-side). Results: level-1 hull (0,26)–(1,20)–(9,0)
  exact; residual multiplicities {1:2, 2:2}; composed reads at
  BOTH class keys give mu2* = 2 = m_r (hulls (0,51)/(0,58)–(2,25)–
  (4,5); >T2 segment = [0,2], c_g = 25); PARI factorpadic: disc ≠
  0, factors 2+8+8 with the GENTOW-1(d) field-floor classifier
  (per-root v(Phi2_s) > 5/2) putting deg 8 in class 1, deg 8 in
  class 2, the sibling in neither — class degree sums 8 = D2·m_r
  each, LEMMA 6.1's degree display exact on a frame the battery
  never saw.
* **LEG B — CERT-TOP at the b* = 0 quotient-transfer corner.** Q3,
  Phi' = x²−3, (e2,f2) = (1,5), u2 = 3, ψ2 = T⁵+T²+T+2
  (irreducible /F₃, t* = 2): the certificate position 2e2t*+1 = 5
  = e2f2 EXACTLY, so j* = 1, b* = 0, a* = 0 — the branch must
  quotient-transfer into the next coordinate's (0,0) slot (the
  corner of the grid; every battery row had b* ≥ 1; first f2 = 5
  certificate anywhere). Results: honest read DRAIN; ShC_1 pin 16
  = THETA_1 with the UNIQUE minimal slot (0,0), vp = 8 = 2a_{t*},
  digit unit ≡ c_2² (mod 3) — the unit square, wrap unit 1 at this
  η = 1 frame; ShC_0 pin 31 = THETA_0 (the sub-top pairs (0,0)/
  (0,2)/(2,0) land exactly on the floor). 6.3(b)'s position
  bookkeeping (quotient transfers absolute-position-invariant,
  lift emissions strictly lowering) confirmed at the corner.

Both fresh legs are f1 = 1 by construction — they confirm the
note's f1 = 1 content and cannot touch F-1.

## GRADE LINE

**NOT CLEAN: 1 CRITICAL (F-1) + 1 GAP (F-2) + 4 MINOR (F-3..F-6).
Counter stays 0/2.** Repair round owed before PE2: F-1 wants the
f1 = 1 scope pin + the dated gauge annex (GT1-r1/GT3-r1 pattern;
re-derive from GENTOW3 S7.1's lift shape, not from this report's
sentences); F-2 wants either a 𝒯-free cap lemma or a re-scope of
6.2C(d)'s window sentence. The S1 tie and S2 block layer carried
every check I could throw at them, including a genuinely new
multiplicity profile — the box closures BOX-1(GENTOW4) and the
budget half of BOX-2(GENTOW4) look durable at their honest scopes.

Verifier: GENTOW6 passPE1 (fresh context, zero prior stake).
Artifacts: gentow6_pe1_fresh.py (md5
59fe76cefd36e4ffc8688adfd8e5f01e) + gentow6_pe1_fresh_output.txt
(md5 9de61325ef9b07dd2f52954d9d3e3f12, exit 0) + this report.
Isolated battery re-run transcript not committed
(content-identical to the sealed artifact modulo the gp stderr
line + timing).
