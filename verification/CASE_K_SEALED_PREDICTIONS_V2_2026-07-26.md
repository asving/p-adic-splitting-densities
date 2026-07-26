# CASE-K SEALED GATE v2 — p = 3, F₉, FRESH configuration (corrected predictions)

*(2026-07-26. SEALED BEFORE ANY CENSUS AT THIS CONFIGURATION. The v1 gate
(CASE_K_SEALED_PREDICTIONS_2026-07-25.md) FAILED AS SEALED; the adjudication
(MOVES ledger, 2026-07-26 record) traced all three failures to
prediction-derivation errors, corrected here and derived from the SAME theory
(§B2-DEF D.8/D.10 rev D‴, incl. the lift-independence SCOPE clause). The
configuration is FRESH (different heights than v1; no data at these heights has
been examined), so this is a genuine seal, not a refit.)*

## Configuration

p = 3, n = 4, N = 12. Parent stratum as v1 (side (0,4)–(4,0), residual
(z²+1)², ψ = z²+1, Φ̂ = x²+9, F₉ = F₃[z̄]/(z̄²+1)). Weights and digits as v1.
FRESH probe sub-stratum: SUB′ := { w(B₀) = 8 exact, w(B₁) = 4 exact } — the
level-2 side (0,8)–(2,0) of slope 4; cells (d₁, d₀) ∈ F₉ˣ × F₉ˣ; residual
R₂(z₂) = z₂² + d₁z₂ + d₀. Candidates: weight-4 lifts t = c₁·27·x + c₀·81,
(c₁,c₀) ∈ {0,1,2}²∖{(0,0)}, digit τ = c₁z̄ + c₀ (all of F₉ˣ); wrong-weight
controls t = 27 (weight 3), t = 243 (weight 5); recentered key Φ̂ − t (verify
the division sign against genuine division as in v1 and use whichever
reproduces literal Φ̂ − t). μ(τ) := multiplicity of τ as root of R₂ over F₉.

## Sealed predictions (v2 — the conditioned laws)

Q1 (cells): all 64 cells non-empty, equal masses, d₁ ⫫ d₀.
Q2 (the conditioned substitution law; member-by-member): with R′(z′) :=
    R₂(z′ + τ) = z′² + (2τ + d₁)z′ + R₂(τ), for every weight-4 candidate τ:
    - B₀′-clause: if R₂(τ) ≠ 0: w(B₀′) = 8 exact with dig(B₀′) = R₂(τ) on
      EVERY member. If R₂(τ) = 0: w(B₀′) ≥ 9 on every member.
    - B₁′-clause: if 2τ + d₁ ≠ 0: w(B₁′) = 4 exact with dig(B₁′) = 2τ + d₁ on
      EVERY member. If 2τ + d₁ = 0 (the char-3 edge, μ arbitrary): w(B₁′) ≥ 5
      on every member.
Q3 (genericity, F₉-pair law): wherever a clause above gives ≥ (a died digit),
    the next height's digit is fresh-generic: exactly 8/9 of the affected cell
    sits at the next height exactly (nonzero F₉-pair), 1/9 deeper.
Q4 (discriminating selection): on a cell with d₀ = d₁² (double root, center
    τ = d₁ — char 3: −d₁/2 = d₁), the UNIQUE both-rise candidate (w(B₀′) ≥ 9
    AND w(B₁′) ≥ 5) is τ = d₁; every other candidate leaves at least one of
    the two clauses at its exact weight with the Q2 digit value.
Q5 (controls): t = 27 (weight 3, below the side): no member keeps
    w(B₀′) ≥ 8. t = 243 (weight 5, above): every member keeps (8, d₀) and
    (4, d₁) unchanged.
Q6 (lift independence WITH SCOPE): for two candidates t and t + 243 (differ at
    weight 5): the (w, dig) tables TRUNCATED AT THE READ DATA (w(B₀′) ∧ 9,
    w(B₁′) ∧ 5, digits only at the exact heights 8 resp. 4) are IDENTICAL
    cell-for-cell; differences may occur only in slices at exposed depth ≥ 5
    (w(B₁′) ≥ 5 content) resp. ≥ 9, on the cells where the corresponding digit
    died.

FALSIFIERS: any member violating a Q2 clause; Q3 fractions ≠ 8/9 beyond
cap-noise; a both-rise off τ = d₁ or a non-both-rise at it on a d₀ = d₁² cell;
any Q5 violation; any Q6 difference within the truncated tables. Any falsifier
⟹ the gate FAILS and D.8/D.10's formulas are wrong at p = 3.
