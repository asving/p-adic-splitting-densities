# HE3 passPE2 — SECOND FRESH-CONTEXT HOSTILE PASS (Fable, zero prior stake)

**VERDICT: NOT CLEAN — 2 GAP + 3 MINOR survive this pass's own verification.
Counter stays 0/2. No CRITICAL: the eight PE1 repairs and the self-found N1
supplement all HOLD as repaired, and the fresh route at the never-run
e₁ ≥ 2 ∧ f₁ ≥ 2 geography is GREEN (7/7 PARI-confirmed members).** The two
GAPs are both convention/justification defects, not refutations of any
theorem statement: (1) the residual-polynomial TWIST seam — DEFINITION 1
never pins R_λ's construction and the §S3 Remark's twist-invariance claim
is FALSE as stated, with a machine-adjudicated member at (e₁,f₁) = (2,2)
where the naive untwisted reading flips the factorization type (PARI sides
with the coherent reading); (2) the §S1 node re-derivation's inference
from root values to polygon slopes is a non-sequitur (fenced by the
independent GENHN [r1] consumption).

**Pass metadata.** Target `HE3_PROOF_2026-08-08.md` at HEAD (r1 =
3320039/34de897/dbfc496/ccb7e9a on PE1 @ 7950ee4). Protocol:
quote-and-classify, fix nothing. PE1's routes not re-walked; this pass's
surfaces per the charge: HE3-1L, the six re-keyed thresholds, the N1
supplement, HE3-5 (never audited before), HE3-6, the consumer trace, and
the fresh e₁ ≥ 2 ∧ f₁ ≥ 2 family the r1 supp's own coverage note names.

---

## FINDINGS (ranked)

### F-1 — GAP (CONFIRMED by machine adjudication). The residual polynomial
### R_λ is construction-unpinned, and the §S3 Remark's twist-invariance
### claim is false as displayed; at e₁ ≥ 2 the naive reading flips
### factorization types on this pass's constructed member.

QUOTE (§S3 Remark after LEMMA HE3-1′): "The wrap factors ẑ^{fl} are
nonzero constants of K ...; they rescale the coefficients of R_λ by a
fixed nonzero diagonal, hence change neither its root set up to that
rescaling nor its factorization TYPE. All uses below consult only (a)
whether R_λ(s) = 0 and (b) the degrees of the irreducible factors of R_λ,
**both twist-invariant**." QUOTE (DEFINITION 1): "a residual polynomial
R_λ ∈ K[Z] of degree d_λ with R_λ(0) ≠ 0" — no construction displayed.

A non-geometric diagonal does NOT preserve root sets or factorization
type; the wraps that actually occur are non-geometric relative to the
naive n(κ)-read. Verified by hand at (e₁,h) = (2,1), λ = 3, m = 9:
the per-slot wrap exponents on the line are (0,0,1,1) — not affine in j.
CONCRETE ADJUDICATED INSTANCE (fresh-route member `ma`, genre
(3;2,2,2;1), Φ′ = x⁴+9, K = F₉, η² = −1): f = Φ′² + 9x·Φ′ + 243, all
three pins ON the λ = 5 line. Naive untwisted n-read residual:
Z² + Z + 1 = (Z−1)² in char 3 → a repeated K-rational root → stage-α
refine, and HE3-2(b) would predict above-λ length 2 at s = 1. Coherent
residual (HE6's frozen ϖ-CONVENTION, ϖ = x here; equivalently GENHN §S4's
"side residuals assembled with coherent normalizers are z-power-twisted
slot digits ... LETTERS are twisted"): Z² − Z − η, discriminant 1 + η a
NON-SQUARE in F₉ → irreducible → σ = {(2,4)}. **PARI: σ(ma) = {(2,4)};
and the measured peel profile is m_s = 0 at ALL 8 letters of F₉^×
(above-λ length 0 at s = 1, refuting the naive HE3-2(b) prediction).**
The chain is SOUND under the coherent reading — this pass verified the
wrap exponents form a COBOUNDARY (w′_{i,j} = W(i) − W(j)), which is
exactly why HE3-2(b)'s substitution identity G″ = G(Z+s) and HE3-1′'s
"precisely R_λ(s) up to a nonzero K-factor" hold with twisted reads on
both sides, and why the n-read residual is a geometric rescaling of the
ϖ-read one (same factorization type). But HE3's text neither states nor
proves this; its only display addressing twists (the Remark) is a false
general principle, and HE3-2(b)'s "up to the twist rescaling" and the
proof's "G(Z) = Z^T·R_λ(Z) up to the twist diagonal" leave the reader
free to take the naive object. FAILURE SCENARIO: a reader or Lean
transcription that builds R_λ from the untwisted slot residues Σα_jZ^j
(the reading HE3-1L's own n(κ)-read display suggests) emits (Z−1)² on
`ma`, schedules a phantom stage-α refine, finds an EMPTY sub-block
(measured length 0), and mis-reads f_s — wrong σ at e₁ ≥ 2, inside the
μ ≤ 3 headline's scope. At e₁ = 1 (all of the r1 supp's sweeps) the
wraps vanish and the defect is invisible; the (2,1)-geography battery
rows are immune only because the battery MEASURES cancellations instead
of constructing R_λ. REPAIR (not executed): pin DEFINITION 1's R_λ to
HE6's ϖ-convention (or GENHN §S4's twisted assembly) and replace the
Remark's false invariance sentence with the coboundary/geometric-
rescaling statement.

### F-2 — GAP. The §S1 [r1, F2] node re-derivation infers polygon slopes
### from root values without the attainment direction.

QUOTE (§S1): "hence dv(Φ′(ρ)) > D′h ...; **hence every side of P(F) has
dv-slope > D′h**; hence every pin lies strictly above the line". The
first "hence" needs every slope of P(F) to be ATTAINED by a root of f
(HE3-0(iii) gives roots → slopes, not the converse); attainment at
HE3-3-strength is proved only later, and HE3-3's own sampling (κ > D′h)
cannot separate hypothetical sub-D′h slopes. Only the pin (0, dv(A₀))
follows directly (HE3-1 at Φ″ = Φ′: D′·dv(A₀) = Σ_ρ dv(Φ′(ρ)) > D′μD′h).
A correct route exists inside the note's own instruments (Ψ-comparison at
κ = D′h+1: test side D′·min_j(dv(A_j)+jκ) < D′μκ = root side if some
dv(A_{j*}) ≤ (μ−j*)D′h — contradiction), but it is not displayed.
FENCED: the corrected node is ALSO consumed from GENHN's [r1] erratum at
HEAD (its own derivation, supplier at accepted-track), so no conclusion
rests on the re-derivation; the defect is the displayed proof. FAILURE
SCENARIO: a Lean transcription of §S1's derivation as displayed has an
unclosable goal at the roots→sides step.

### F-3 — MINOR. HE3-3 step (2)'s justification is stale under the [r1]
### C-carriers.

QUOTE (§S6.1 step (2)): "dv(w(ρ)) = κ because ρ satisfies (T1), **so
dv(n(κ)(ρ)) = κ**". After [r1, F1/F8], w = −C_{κ,s} is no longer the
monomial ŝ·n(κ); the true reason is the ξ-form slot read at ρ (HE6-0″/
HE3-1L mechanism: slot residue Σ res(c_t)η_ρ^t ≠ 0 by F_Q-independence
of {η_ρ^t}). The fact is true and provable; the displayed reason
references the retired carrier.

### F-4 — MINOR (machine). The r1 supp's P4 leg is quasi-tautological, and
### its docstring misstates the resultant route.

`he3r1_supp.py` P4 computes the "realized residues" BY the slot-digit
extraction the lemma itself derives (`c0 = (C[0]//3**kap)%3 ...`), so it
verifies the T(κ) bookkeeping, not the residue arithmetic; §S9′'s "the
enumerated realized residues res(C(theta)/n(kappa)(theta)) equal the
displayed span" overstates the leg's independence. Also the docstring
says "sympy integer resultants" while the code is the no-sympy Bareiss
route. The missing decorrelated leg is supplied by this pass (FR-C: PARI
`nfeltval` heights + `nfmodpr` residues at (2,2,1), κ = 0..5, matching
the T(κ)-span exactly, including the boundary κ = 3 = (i₀+e₁(f₁−1))h).

### F-5 — MINOR (coverage labeling). The [r1-N1] machine demo ran only at
### a geography where the N1 gap is not live.

§S9′ P2-N1's "both branches machine-demonstrated" ran at (Q,f₁) = (3,2)
(K = F₉, letters abundant); the gap exists only at (Q,f₁) = (2,1)
(K^× = {1}). The actual gap geography was machine-run nowhere until this
pass (FR-D, ℤ₂, Φ′ = x−2, slopes 2,3,4: PARI σ = {(1,1)}³; A₀′ = 0
branch: quotient dev slopes {2,3}; junk variant: slopes {2,3,6} with the
non-slope 4 in the gap). Both branches behave exactly as the supplement
states — substance intact, label loose.

---

## CLEAN CHARGES (attacked, survived this pass)

* **LEMMA HE3-1L (attack 1)**: statement and proof verified line-by-line —
  slot classes i = i₀ + e₁t, the exact monomial arithmetic
  c_iθ^{i₀+e₁t}/n(κ)(θ) = u·(θ^{e₁}π^{−h})^t (π-exponents cancel to −th:
  re-derived, correct), F_Q-independence of {η^t} ⟹ no level-1
  cancellation ⟹ the punctured T(κ)-span is EXACT. The cancellation of
  HE6's coset factor η^{−q(κ)} in the n(κ)-read is genuinely PROVED (the
  read is self-normalizing: residues are taken against n(κ) itself), not
  asserted; consistent with HE6's frozen RIDER. Fullness iff
  κ ≥ (i₀(κ)+e₁(f₁−1))h verified INCLUDING the boundary: FR-C at (2,2,1)
  shows full K^× at κ = 3 exactly, and already at even κ = 2 < (D′−1)h =
  3 — the i₀(κ)-dependence is real and machine-visible. (D′−1)h
  sufficiency arithmetic checked. Empty set at κ < i₀(κ)h consistent.
* **The six re-keyed >D′h sites (attack 2)**: HE3-1 (invariant
  maintenance re-derivation: dv(w) > D′h ⟹ v(w_i) > (D′−i)h/e₁ per
  coefficient ⟹ same entry polygon + same residual ψ ⟹ irreducible,
  e = e₁, f = f₁, (T1)/(T2) — sound; boundary counter-instances x²+18/
  x²+27 verified as recorded); HE3-1′; HE3-2 incl. (c)'s corrected
  justification (the key's side height IS D′h at abscissa 0); §S6.1's Ψ
  definition + HE3-1L existence cite (κ > D′h > (D′−1)h ✓); (SEP)'s
  index set; the corrected sample recipe. The node forces all slopes
  > D′h, so every recentering height is inside HE3-1L's fullness range —
  no site consumes a letter below (D′−1)h.
* **The [r1-N1] supplement, both branches (attack 3)**: re-derived
  independently. CASE A₀′ ≠ 0: P(F″) = {a, a+1, δ ≥ a+3}; the system
  {root count, sample at the non-slope a+2, above-δ samples} is
  triangular with determinant ≠ 0; the Φ″-classes are the Φ′-classes
  (collapse residue −s ≠ 0; β = 1 forced at d = 1 since R_{a+2} is
  linear). CASE A₀′ = 0: Φ″ ‖ f by disc ≠ 0; the quotient development is
  the left shift; 2×2 inversion; A₁′ = 0 is impossible (it would break
  HE3-2(b)'s preserved slope-(a+1) side). Machine: FR-D at the true
  (2,1) geography (see F-5).
* **LEMMA HE3-5, end-to-end (attack 4)**: sound. This pass proved the
  displayed (i)/(ii) iff-condition is EQUIVALENT to m₁ < e₁N (recentered
  span pins sit on-or-above the λ-line by HE3-2(a)-convexity; line
  heights decrease along the side; so a failing pin forces the left
  endpoint ≥ cap, and then no earlier pin can be certified either — the
  necessity direction closes, and the leading-coefficient corner cannot
  arise). Bullet 1 (decided as soon as e₁N > μλ) is exactly this
  equivalence at j₁ = 0; the ALPHA one-more-window bullet is the
  sub-block's own deeper read, consistent with the HE-BND two-step (0 at
  N=4, bulk at N=5, ALPHA remainder at N=6). No defect; the iff could be
  DISPLAYED more simply as m₁ < e₁N.
* **LEMMA HE3-6 (attack 5)**: proof verified — Φ′, n(λ), n(u) have
  Galois-fixed coefficients with nonnegative π-exponents (λ > D′h ≥
  (e₁−1)h ≥ i₀h checked); v Galois-invariant; ι_{gρ} = ḡ∘ι_ρ by
  uniqueness of the F_Q-embedding on the generator η; distinct
  irreducible factors are coprime so the label of gρ is well-defined;
  both the ℓ = 1 and ℓ ≥ 2 residue reads covered.
* **Consumer trace (attack 6)**: HE6 row — DEF 1 byte-identical at
  7a95449 vs HEAD (diff empty); the (★) display + proof byte-identical
  (the only diff in that region is step (2)'s re-key, outside (★));
  HE3-0's consumed clause ((T1)/(T2)) unchanged, (iii)'s ℓ ≥ 2 read
  re-proved inside HE6 as HE6-2″ and not consumed (grep-verified);
  HE6's DEFINITION HE6-1 requires κ > D′h (its lines 179/202), inside
  the corrected band exactly as the trace claims; HE6 §S6.3 consumes
  "class size D′m_s from HE3-2(b) + HE3-3" — the above-λ-length = m
  clause, which survives verbatim in the corrected (b). GENHN row: the
  [r1 2026-08-08] node erratum present at HEAD (line 169) and §S1's
  display now matches it. GENIND row: `grep -c HE3` = 0 — trivially
  safe, as claimed.
* **HE3-4's direct route + μ ≤ 3 subtraction bullet**: verified (the
  one-clause equivalence dv(Φ″(ρ)) > λ ⟺ residue cancellation; the
  collapse behavior; |S| = D′m with no above-λ subtraction), and
  machine-exercised at (2,2) by FR-A's peel profiles.

## MACHINE LEG (pins, isolated re-run, tautology audit)

* **Sealed battery byte-frozen through r1**: `he3_checks.py` and both
  artifacts last touched at commit 872327b (pre-r1); VERIFIED by git log.
* **Pins**: `he3r1_supp.py` md5 = 9cd132a8ce174f5703542757675f7960 =
  the §S9′ pin; committed output md5 = 65ed06e49f4c54abf1b143513633f143 =
  the §S9′ pin.
* **Isolated re-run** (`/tmp/he3pe2_iso`, runner copied alone): exit 0,
  stdout BYTE-IDENTICAL to the committed `he3r1_supp_output.txt`,
  `he3r1_supp_results.json` content-identical to the committed artifact.
* **Tautology audit**: P1–P3 are decorrelated (members constructed by
  ring arithmetic, predictions from the dictionary, PARI factorpadic +
  idealprimedec as oracle, m_s measured from the development polygon);
  P4 is quasi-tautological (F-4). The `above_line` reader counts the
  A₀′ = 0 infinite pin as above — disclosed in its docstring, correct
  for the [r1-N1] branch semantics.

## FRESH ROUTE (`verification/openmath/he3_pe2fresh.py`, GREEN,
## 0 violations, exit 0 — the e₁ ≥ 2 ∧ f₁ ≥ 2 geography, never run
## anywhere before this pass)

Genre (3; 2, 2, μ; 1), Φ′ = x⁴+9 over ℤ₃ (D′ = 4, D′h = 4, K = F₉),
h-invertibility and i₀(κ)-cycling live (e₁ = 2), K∖F_Q letters live
(f₁ = 2) — both PE1-CRITICAL mechanisms simultaneously:

* **FR-A (7 members, PARI σ vs dictionary, 7/7)**: {η,−η} letters
  {(2,2)²}; {1,η} {(2,2)²}; ℓ = 2 side λ = 11/2 {(4,2)}; μ = 3
  {1,η,−η} {(2,2)³} (degree 12); irreducible-quadratic residual
  {(2,4)}; split-quadratic Z²−η with roots ±(1−η) {(2,2)²}; plus `ma`
  (FR-B). HE3-1a (HE-NORM) asserted at the entry key AND every test key
  of every peeled member at e₁ = 2 (exact Bareiss resultants;
  2·v₃(Res) = 4·dv(B₀)) — the identity's first machine run at e₁ ≥ 2 on
  the HE3 side. Peel profiles exact over all of F₉^× on 5 members,
  including the verifier-error catch: the split-quadratic's letters are
  ±(1−η) (whose square is η in char 3), not the first-drafted ±(1+η) —
  the exact instrument corrected this pass's own hand arithmetic.
* **FR-B (the twist adjudicator)**: PARI σ = {(2,4)} — coherent
  ϖ-convention residual confirmed, naive untwisted read refuted (F-1).
* **FR-C (HE3-1L independent leg)**: realized residues at (2,2,1)
  computed by PARI valuations + residue-field reduction (no slot
  formula): sizes {κ=0:2, 1:2, 2:8, 3:8, 4:8, 5:8} = the T(κ)-span
  exactly; boundary κ = 3 = (i₀+e₁(f₁−1))h full, κ = 1 only F₃^×.
* **FR-D (N1 at its real geography)**: see F-5 — both branches at
  (Q,f₁) = (2,1) over ℤ₂, PARI-confirmed.

## GRADE LINE

**Pass verdict: NOT CLEAN (F-1, F-2 GAP; F-3, F-4, F-5 MINOR). Counter:
0/2 — unchanged; a GAP-or-worse finding blocks the count.** No CRITICAL:
every PE1 repair holds as displayed, HE3-1L / HE3-5 / HE3-6 / the N1
supplement are sound, the consumer trace is accurate, and the σ-law is
machine-real at the previously never-run e₁ ≥ 2 ∧ f₁ ≥ 2 geography.
Suggested repair round (for the composer, not executed here): (F-1) pin
DEFINITION 1's R_λ to the coherent twisted construction (HE6 CONVENTION /
GENHN §S4) and replace the §S3 Remark's invariance sentence with the
coboundary statement; (F-2) either display the Ψ-comparison step or
demote the §S1 re-derivation to a consumption of GENHN [r1]; (F-3)
re-key step (2)'s parenthetical; (F-4/F-5) relabel the two machine legs
(this pass's FR-C/FR-D can be cited as the decorrelated cover). A PE3
after these repairs could be charged at: the coherent-convention
displays as repaired, HE3-2(a)'s equality clause under vanishing
binomials, and an e₁ ≥ 2 ∧ f₁ ≥ 2 row folded into the note's own §S9′.
