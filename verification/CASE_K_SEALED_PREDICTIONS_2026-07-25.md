# CASE-K SEALED GATE — p = 3, F₉ level-2 recentering (predictions preregistered)

*(2026-07-25. SEALED BEFORE THE CENSUS IS RUN — this file is committed first; the
census script and its output land in a later commit. Source of every prediction:
§B2-DEF D.8 + D.10 of `lean/notes/MOVES_2026-07-24.md` (the substitution identity
R′(z′) = R(z′ + τ)), evaluated on this configuration. The p = 2 exploration
(`case_k_explore.py`, raw) informed the DESIGN but no p = 3 data has been looked
at. The gate validates formulas, never the general algebra.)*

## Configuration

p = 3, n = 4, N = 12 (mod 3¹²), v = v₃. Parent stratum (side slope −1 through
(0,4)–(4,0), residual (z²+1)² = z⁴ + 2z² + 1 over F₃; ψ = z² + 1 irreducible,
ψ ≠ z):

  v(a₃) ≥ 2,  digit₂(a₂) = 2 (v = 2 exact),  v(a₁) ≥ 4,  digit₄(a₀) = 1
  (v = 4 exact),

nominal mass 3⁻⁸·(2/3)²-normalized — the census reports its own exact count.
Level-2 key: Φ̂ = x² + 9 (standard lift of ψ). Development f = Φ̂² + B₁Φ̂ + B₀,
B = b₁x + b₀, w(B) := min(v(b₀), v(b₁) + 1). F₉ := F₃[z̄]/(z̄² + 1); the digit of
B at m = w(B) is d = ε_x·z̄ + ε_c with ε_c = digit_m(b₀) if v(b₀) = m else 0,
ε_x = digit_{m−1}(b₁) if v(b₁) = m − 1 else 0 (values in {0,1,2}).

Probe sub-stratum: SUB := { w(B₀) = 6 exact, w(B₁) = 3 exact }, cells keyed by
(d₁, d₀) := (dig B₁, dig B₀) ∈ F₉ˣ × F₉ˣ (64 cells).
Level-2 side residual: R₂(z₂) = z₂² + d₁·z₂ + d₀.

Candidates: t = 9·(c₁x + c₀·3-scaled) — concretely t = c₁·9·x + c₀·27 for
(c₁, c₀) ∈ {0,1,2}²∖{(0,0)} (weight 3, digit τ = c₁z̄ + c₀ — all 8 elements of
F₉ˣ), plus τ = 0 realized as no-move sanity, plus wrong-weight controls t = 9
(weight 2) and t = 81 (weight 4). SIGN CONVENTION (this is a char ≠ 2 gate: signs
are live): the recentered key is Φ̂′ := Φ̂ − t, and the residual variable shifts
by z = z′ + τ (D.10; the center killed is the root τ of R₂).

## Sealed predictions

Let μ(τ) := the multiplicity of τ as a root of R₂ in F₉ (0, 1, or 2;
μ = 2 ⟺ d₀ = d₁² and τ = d₁ — note −d₁/2 = d₁ in char 3).

P1 (cell structure): the 64 (d₁, d₀)-cells are non-empty with EQUAL masses, and
    dig-independence holds (d₁ ⫫ d₀).
P2 (the substitution law, the heart): for every weight-3 candidate τ and every
    SUB member, the re-developed (B₁′, B₀′) satisfy, with
    R′(z′) := R₂(z′ + τ) = z′² + (2τ + d₁)z′ + (τ² + d₁τ + d₀):
    - if μ(τ) = 0:  w(B₀′) = 6 exact with dig(B₀′) = τ² + d₁τ + d₀ = R₂(τ), and
                    w(B₁′) = 3 exact with dig(B₁′) = 2τ + d₁ = R₂′(τ).
    - if μ(τ) = 1:  w(B₀′) ≥ 7, and w(B₁′) = 3 exact with dig(B₁′) = 2τ + d₁ ≠ 0.
    - if μ(τ) = 2:  w(B₀′) ≥ 7 AND w(B₁′) ≥ 4 (both side digits die; the vertex
                    moves to slot 2).
    These digit values are DETERMINISTIC (hold member-by-member, not just in
    distribution).
P3 (the discriminating F₉ content): on a cell with d₀ = d₁² (double root at
    τ = d₁ ∈ F₉∖F₃ for suitable d₁), the UNIQUE both-rise candidate is τ = d₁;
    in particular for d₁ = z̄ the matched lift is t = 9x (c₁ = 1, c₀ = 0) and
    e.g. t = 9x + 27 (τ = z̄ + 1) must NOT produce the B₁′-rise — it must show
    dig(B₁′) = 2(z̄+1) + z̄·... = 2τ + d₁ evaluated: 2(z̄+1) + z̄ = 3z̄ + 2 = 2.
P4 (fresh-digit genericity): on μ(τ) ≥ 1 candidates, w(B₀′) = 7 exactly for 2/3
    of the affected cell (a generic fresh digit at height 7), ≥ 8 for 1/3; on
    μ(τ) = 2, w(B₁′) = 4 exactly for 2/3, ≥ 5 for 1/3.
P5 (controls): t = 9 (weight 2, below the side): the primed development has
    w(B₀′) = 4 exact with dig(B₀′) = 1 (= the digit of t² at height 4:
    (z+τ·wrong-scale)-analysis collapses to the t²-term) — the census may refine
    this prediction's mechanism but MUST see: no member keeps w(B₀′) ≥ 6.
    t = 81 (weight 4, above the side): w(B₀′) = 6 exact and w(B₁′) = 3 exact with
    UNCHANGED digits (d₁, d₀) on every member.
P6 (lift independence): replacing any candidate t by t + (anything of weight ≥ 4)
    changes NO table (same (w, dig) joint tables cell-for-cell).

FALSIFIERS: any deterministic digit law violated on any member; any cell mass
deviation; a both-rise at μ ≤ 1 or a non-rise at the matched candidate; a P6
table difference. Any falsifier = the gate FAILS and §B2-DEF's D.10 is wrong at
p = 3 regardless of its proofs.
