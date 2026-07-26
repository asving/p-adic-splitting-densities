# FABLE (fresh-instance) CONFIRMING verification of §B2-DEF rev D¹¹d — 2026-07-26

Target: `MOVES_2026-07-24.md` §B2-DEF live text (lines ~1856–2754) at rev D¹¹d,
plus the REV D¹¹/D¹¹b/D¹¹c record (~3269–3337). Second half of the dual bar:
Codex judged this exact text CLEAN (CODEX_CONFIRM_D11D); this pass is
decorrelated and does NOT defer to it. Predecessor Fable pass:
FABLE_VERIFY_B2DEF_2026-07-26.md (0 critical / 9 gaps F1–F9 on the accepted
pre-D¹¹ text). Method: quote-and-classify; verify repairs GENUINE against the
live text; own instances, own trace, own sweep.

## Status
- [ ] (a) F1–F9 repair-genuineness audit (quotes from live text)
- [ ] (b1) Attainable-block accounting: OWN shallow instance (fresh, not recorded)
- [ ] (b2) Admissibility dichotomy audit
- [ ] (b3) (ii.2) scale audit
- [ ] (c) End-to-end trace on an unrecorded configuration (incl. shallow height)
- [ ] (d) Fresh sweep (own emphasis)
- [ ] Verdict

## (a) F1–F9 repair audit
(to be appended)

## (b) Successor-repair audits
(to be appended)

## (c) End-to-end trace
(to be appended)

## (d) Fresh sweep
(to be appended)

## Verdict
(to be appended)

## (a) F1–F9 repair audit — ALL NINE GENUINE (live text quoted)

- F1 GENUINE (D.4 ROOT): "every side's slope is ≥ 1/deg f > 0 — and positivity is
  all (I-aug) asserts here (λ > w(x) = 0)". Math checked: unit lead at (deg f, 0),
  integer drops, hull descent ⟹ slope ≥ 1/deg f. The false "≥ 1" is gone; the
  x²+px+p counterexample is cited in place.
- F2 GENUINE (D.4 close): "Its consumers, per the DAG [...]: D.7(i)'s strict-depth
  step (re-cited at D.7(ii)); D.5's (S6b) range check (h > e·w_prev(Φ)); D.7(viii)'s
  two-line recursion [...] CONSUMERS clause (i)–(ii); and D.9(c)". I checked each
  listed site in the live text: all four do consume (I-aug); none is missing
  (D.7(i) hosts the strict-depth inequality, correctly re-attributed from (ii)).
- F3 GENUINE as a display (D.3(e)(ii) now (ii.1)–(ii.4)): digit-level Fact-A carry
  law + global well-order (ii.1); the F′-digit → leaf-block unpacking with per-space
  height scales, forced anchor slot, and forced unit u(γ) (ii.2); equation→coordinate
  injectivity via disjoint subtrees / distinct slot classes / distinct heights
  (ii.3); unit-diagonal count (ii.4). Correctness audited in (b) below.
- F4 GENUINE (D.8 TRANSPORT): downward recursion displayed on Laurent data —
  "with every division EXACT in F[z^{±1}]" — I re-derived both congruence
  inductions (S − Σ_{i<j}C_iψ^i ≡ 0 mod ψ^j; carry_j's numerator ≡ 0 mod ψ^j) and
  the identification C_j = C*_j with the canonical ψ-adic digits; upward recovery
  via "z^{q}·{deg < g} is a full system of representatives mod ψ" checked (z unit
  mod ψ; window base q_j forced by γ_j = w(f) − j·w(Φ̂) and the D.3(d) width-g
  window). Exercised on a genuinely Laurent instance with nonzero carry in (c).
- F5 GENUINE (D.7(iii)): "its value group IS ℤ as defined — nothing is (or could
  be) renormalized"; the displayed generation (e′·cofinite differences give e′ℤ,
  plus h′ with gcd(e′,h′) = 1) is correct. The "renormalized" landmine is gone.
- F6 GENUINE (D.2 (S4)): "§A.2's accepted localization inverts π only [...]; the
  base stage further inverts y, per D.0's separate adjunction of Y — harmless, a
  localization of a graded domain at the homogeneous y (D.1(d))". Honest cite.
- F7 GENUINE (D.10): the WELL-TYPEDNESS LEMMA is displayed: t = 0 at e_read = 1 ⟹
  positions p_j(γ) = j ≥ 0 ⟹ R(f) ∈ F[z], "a := ord_z R(f) ≥ 0", typing (z′+c̃)^a
  inside F[z′]. Exactly the missing sentence F7 demanded, with its proof.
- F8 GENUINE (D.2 (S6a)): "D.7(v) consumes (S6b) AT THE CURRENT STAGE in its
  LARGE-WEIGHT regime — INTEGRAL realizers [...] (its rev-D⁷ form, pass-15
  finding 1: no localized action, no embedding lemma)". Now agrees verbatim with
  live D.7(v)(3); the stale rev-D⁶ pointer is replaced.
- F9 GENUINE (D.12): "CENSUS-PINNED AT REV D⁹ (the pass-18 repair, run ON rev D⁸)".
  Label matches the pass-18 record's own statement.

## (b) The three successor repairs — audited hardest

### (b3) The (ii.2) scale (rev D¹¹b) — CORRECT
Typing re-derived independently: B ∈ C_{k+1} = stage-k's Ĉ carries its OWN stage
scale γ ∈ 𝒲_{k+1} ⊆ e_{k+1}·ℤ (D.0: w_{k+1} = e_{k+1}·w_k on coefficients), so
γ* := γ/e_{k+1} is exactly the stage-k weight at which the Φ_k-development is
read (γ* := γ at the top, where no K+1 read exists — 𝒲̂_K is already stage-K).
Then w_k(B_j) = γ* − j·h_k at a minimizing slot IS a stage-k weight: γ_i with
"NO division" is the only consistent typing; the lattice landing γ_i ≡
γ*(1 − h_k·t_k) ≡ 0 (mod e_k) checked (j₀ ≡ t_k·γ*, h_k t_k ≡ 1). The old /e_k
formula conflated w_k(B_j) with w_{k−1}(B_j) — Codex's D11 critical was real and
this fix is the right one. u(γ) forced-by-γ verified on an instance: top space,
p = 7 tower of (c), γ = 2: u(2) = z̄^{p_{j₀}(γ*)} = z̄, and the direct digit of
b₁x is b̄₁z̄ — exact. (ii.3)/(ii.4) consume only pins and blocks — unchanged. ✓

### (b2) Attainable-block accounting (rev D¹¹c) — CORRECT; OWN instance passes
The repair: I(γ) := {i < g_k : γ_i ∈ 𝒲_k}; unattainable summands ABSENT (no
zero-filled coordinate); 𝔸(γ) := the value set, = u(γ)·⊕_{i∈I(γ)}𝔸_k(γ_i)z̄^i,
an F_p-subspace of size Π|𝔸_k(γ_i)|; |β(B,γ)| = log_p|𝔸(γ)| PER-HEIGHT.
I re-derived: the domain {w ≥ γ} is the product of per-slot domains (K1 min
formula) — slot independence holds; distinct attainable tuples give distinct
values ((1,…,z̄^{g_k−1}) an F_k-basis, u(γ) a unit); F_p-subspace by induction
(base 𝔸₁ = F₁ onto). The full-threshold clause (γ_{g_k−1} ≥ e_k f_k ⟹ I full)
checked against D.9(b). OWN SHALLOW INSTANCE, in no record — p = 3, base read
(e₁,h₁) = (3,1) (records used (2,3), (2,1), (1,1)), ψ = z²+1 over F₃, top space
C₂ = {deg < 6}, γ = 2: j₀ = 2, γ₀ = 0 ∈ 𝒲₁, γ₁ = −3 ∉ 𝒲₁ ⟹ I(2) = {0},
u(2) = z̄⁰ = 1, prediction 𝔸(2) = F₃ (3 of 9 values; 1 leaf digit; factor 1/3).
Python enumeration of the full level-2 box (3¹² developments): domain mass
59049/531441 = 1/9 — itself the attainable product for the two zero-pins at
heights 0,1 (each |𝔸| = 3, both with I = {0}); exactly 3 values attained, all
on the F₃-line, each at mass 1/3 of the domain; the 6 off-line F₉-values have
count 0 (empty loci). The old uniform display (9 values at 1/9, 2 leaf digits)
is falsified on this instance; the attainable accounting is exact. ✓

### (b1) The admissibility dichotomy (rev D¹¹d) — CORRECT and exhaustive
D.3(e)(ii): "Pinning d_γ(B) = X is solvable iff X ∈ 𝔸(γ)" — literally the
definition of the value set, both directions. Joint systems: blocks disjoint
(ii.3), each equation pins the fresh leaves of its own block with unit diagonal
(ii.4) "whatever those predecessors are" — so individually-admissible pins are
automatically JOINTLY solvable with mass exactly Π|𝔸^{(i)}|^{−1}: no third case
between admissible (product) and inadmissible (empty). D.11's typing is scoped
correctly: the equality is asserted for admissible cylinders; "landing cylinders
of actual strata are always admissible — D.8 transports pins from actual loci"
— checked against D.8's closing step: every transported value is a digit of an
actual member of the domain, hence in the value set; the off-alphabet guard
cannot fire on a nonempty stratum. Zero-pins admissible always (0 ∈ 𝔸: 𝒲_k
cofinite ⟹ deeper elements exist). Transported right-hand sides (functions of
earlier data) are covered by the same unit-diagonal argument branchwise. ✓

## (c) End-to-end trace — configuration in NO record
p = 7, base key x (d = 1), read (e,h) = (3,2), Bézout (s,t) = (1,−1), T = πy^{−1},
z = y³π^{−2}, ψ = z²+1 (irreducible /F₇: −1 ∉ {1,2,4}), g = 2, F′ = F₄₉.
[No record uses p = 7 or (e,h) = (3,2); designed so the anchor is set by slot-
CANCELLATION, making the transport data genuinely Laurent — the F4 machinery.]
- D.3(b): R(x) = Y·T^{−2} = y³π^{−2} = z^s = z ✓. S5: dig(c·p^v) = c̄·z^{+v}
  (t = −1) ✓. D.5: Φ̂ = x⁶ + p⁴ (t₀ realizer: w = 12, scalar ψ₀ = 1, position
  k(t₀) = 4 forced); R(Φ̂) = z⁶ + z⁴ = z⁴ψ, m̂ = −thg = 4 ✓; w(Φ̂) = 12 ✓.
- D.8 landing: f = Φ̂² + B₁Φ̂ + B₀, B₁ := 6p⁴ + p²x³ (w = 12; R(B₁) = 6z⁴+z⁵),
  B₀ := p⁹ (w = 27 > 24: BOX ✓). R(f) = z⁴R(B₁)ψ + z⁸ψ² = z⁹(z+1)ψ (python-
  verified in F₇): μ = 1, anchor a = 9 — the z⁸ bottoms CANCEL (6+1 ≡ 0),
  pushing a past both slot bases.
- TRANSPORT (Laurent, with a real carry): S = z^{−9}R(f) = (z+1)ψ; slot data
  d₁ = z^{−9}z⁴R(B₁) = 6z^{−1}+1, d₂ = z^{−1} — both LAURENT, not polynomials
  (exactly the F4 scenario). Identity S = d₁ψ + d₂ψ² verified. Downward: C₁ =
  rep(d₁ mod ψ) = z+1 (z^{−1} ≡ 6z); carry₂ = (d₁−C₁)/ψ = 6z^{−1} — EXACT
  division verified (z(d₁−C₁) = 6+6z² = 6ψ), a NONZERO carry; C₂ =
  rep((z^{−1}+6z^{−1}) mod ψ) = rep(7z^{−1}) = 0 — matches the canonical digits
  of S = (z+1)ψ + 0·ψ² exactly. Upward: windows q₁ = 4+4−9 = −1, q₂ = 0+8−9 =
  −1 (both forced); class z+1 in z^{−1}{deg<2} has the UNIQUE rep 6z^{−1}+1 =
  d₁ ✓; carry₂ from d₁ alone; class C₂−carry₂ = −6z^{−1} ≡ z^{−1} recovers
  d₂ = z^{−1} ✓. Both directions close on genuinely Laurent data.
- (VERTEX): predicted dig′(B₁) = z̄^{−m̂}·((R(f)/ψ) mod ψ) = 1·(z̄⁹(z̄+1)) =
  z̄+6 (z̄⁴ = 1); direct dig′(B₁) = 6z̄⁴+z̄⁵ = 6+z̄ ✓ EXACT.
- SHALLOW HEIGHT in the same tower: γ = 2 ∈ 𝒲̂₁: j₀ = 1 (≡ −2 mod 3), γ₀ = 0 ∈
  𝒲₁, γ₁ = −6 ∉ 𝒲₁ ⟹ I(2) = {0}, 𝔸(2) = z̄·F₇ (7 of 49 values, 1 leaf digit
  b₁ mod 7, factor 1/7 not 1/49); direct: only slot 1 at v(b₁) = 0 can realize
  weight 2 (slot 4 would need the unattainable −6), d₂(B) = b̄₁z̄ ✓; off-line
  pins empty ✓. u(2) = z̄^{p₁(2)} = z̄ confirmed directly.
Every predicted quantity exact; no deviation found. ∎

## (d) Fresh sweep (own emphasis: edge typing, forced windows, record hygiene)

Checks that PASS (beyond (a)-(c)):
- Legal-γ consistency: heights are indexed by the space's ATTAINED scale
  (γ ∈ 𝒲_k resp. 𝒲̂_K), so I(γ) ≠ ∅ automatically (an attaining B has a
  minimizing, hence congruent-attainable, slot); the (ii.2) formulas also
  type-check at the vacuous edge. Zero-pins always admissible (𝒲_k cofinite
  ⟹ deeper elements exist ⟹ 0 ∈ 𝔸(γ)).
- D.8 upward windows: the width-g window is anchored at the least CONGRUENT
  slot's position — forced by γ_j = w(f) − j·w(Φ̂) mod e alone (the occupied
  window is a subset; predecessor verified the same point). Recovery unique.
- D.11 free-mass bookkeeping: count = p^{nN−Σ|β_i|} = p^{nN}·Π|𝔸^{(i)}|^{−1}
  with the initial-segment zero conditions included as (admissible) pins. ✓
- D.5 range check h > e·w_prev(Φ) ⟺ (I-aug) at the current read; D.7(v)(2)'s
  δ ≥ e′·(bound + egh) arithmetic; D.9(a) "minima of achievable are achievable";
  (ii.3) stretch-injectivity; block addresses value-independent (needed for
  cylinder counting). All re-derived, all pass.

REMARKS (non-blocking; none is a critical error or a justification gap):
- R1 (wording): D.8's "window base q_j forced by the stride/width data (slot
  j's S5 position, plus jm̂ − a)" would be sharper as "the least CONGRUENT
  slot's position at weight w(f) − j·w(Φ̂)"; the forcing is real and one line
  from D.3(a)+(c). My Laurent trace used exactly this reading and closed.
- R2 (record hygiene): the dual-verification record (line ~4453) cites
  CODEX_CONFIRM_D11{,B,C,D}; no "C" file exists (the D¹¹c verification lives
  inside CODEX_CONFIRM_D11D). Also the REV D¹¹ RECORD's bullet list ends at
  D¹¹c — D¹¹d is documented only by inline tags in D.11 and the dual record.
- R3 (evidence perimeter, optional): the interior stretch clause (k+1 ≤ K,
  e_{k+1} ≥ 2 — γ* := γ/e_{k+1}) is proved by the displayed typing but has no
  recorded NUMERIC instance (all recorded block instances sit at the top
  space, stretch trivial); a 3-level gate would strengthen the census.
- §C consumer flag (out of scope, already on record in D¹¹c): C.0's BLOCK
  CONVENTION still displays the uniform field-size factor and needs the
  per-height retype — correctly flagged, not silently absorbed.

## Verdict

(a) F1–F9: all nine repairs GENUINE in the live text (quotes above).
(b) Successors: (ii.2) scale CORRECT (typing re-derived; instance-verified);
attainable blocks CORRECT (own fresh shallow instance p = 3, (e,h) = (3,1),
ψ = z²+1, γ = 2: enumeration exact, old uniform display falsified on it);
admissibility dichotomy CORRECT and exhaustive (value-set definition + unit
diagonal; D.8/D.11 scoping verified).
(c) End-to-end trace p = 7, (e,h) = (3,2), ψ = z²+1 (no record): D.3(b), D.5,
D.8 BOX/VERTEX/TRANSPORT with genuinely Laurent slot data and a NONZERO carry,
upward recovery, and a shallow height (I(2) = {0}, 𝔸(2) = z̄F₇) — all exact.
(d) Sweep: no new defect at the bar; 3 remarks + 1 out-of-scope flag.

**Count: 0 CRITICAL ERRORS, 0 JUSTIFICATION GAPS. CLEAN.**

§B2-DEF rev D¹¹d passes the Fable half of the dual bar on the identical text
Codex judged clean. Remarks R1–R3 are recorded for optional polish; none
blocks acceptance under the repo standard.

— Fable, fresh confirming instance, 2026-07-26.
