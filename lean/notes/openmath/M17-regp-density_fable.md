# M17-regp-density — attempt (Fable, 2026-07-31)

Target: theoremU's one per-prime hypothesis `RegP (inst p hp).D` (the (REG-p)
schema, `MovesU/Defs.lean:209`). Question: at which primes does it hold; prove
cofiniteness / density 1 or characterize the failing set.

RESULT IN ONE LINE: at every pinned instance the failing set is FINITE, with an
exact characterization (Theorem A), the one symbolic hypothesis it needs is
already a corpus theorem (Theorem B), the failure channels are confined to
determinant-numerator vanishing at an explicit finite set of composite depths
(Theorem C), and finiteness is optimal — the corpus's own compiled countermodel
exhibits an admissible instance whose failing set is exactly {2}.

## 0. Setting and notation

Fix n ≥ 2 and one instance pack C (Lean: `UCarriers n`) — table, measured side,
rationality burdens, shape family, chain. All of it is p-independent. Write:

- S_e (e ∈ [1, n]) — the finite state set of block e; K_e ∈ M_{S_e}(ℚ(q)) the
  kernel matrix (Lean `MovesS.Kmat`); Φ_e := det(1 − K_e) ∈ ℚ(q).
- Δ ⊂ ℤ_{≥1} — the finite consumed-depth set (Lean: the ℕ-image of
  `MovesS.consumedDeltas C.T C.Fam`), 1 ∈ Δ. F ⊂ ℤ_{≥1} — the finite set of
  single base-change factors (`MovesS.deltaFactors`); Δ ⊆ M_n where
  M_k := {products of at most k elements of F} (empty product 1 included).
- For f ∈ ℚ(q) write f = N_f / D_f in lowest terms (D_f ≠ 0 monic; Mathlib's
  `RatFunc.num/denom`). "f is defined at x" means D_f(x) ≠ 0; the evaluation
  `RatFunc.eval` is N_f(x)/D_f(x), with junk value 0 when D_f(x) = 0.
  P(f) := {x ∈ ℚ : D_f(x) = 0} (poles), Z(f) := {x ∈ ℚ : N_f(x) = 0} (zeros of
  the numerator; for f ≠ 0 this is the zero set of f where defined).
- DetHyp (the symbolic determinant hypothesis, Lean `MovesS.DetHyp`):
  Φ_e ≠ 0 in ℚ(q) for every e ∈ [1, n].
- Under DetHyp, E(e) ⊂ ℚ(q) denotes the REAL entry list of block e: the
  entries of K_e; the designated terminal rows Σ_{σ′ ∈ verdictImage(e,τ)}
  bTerm_e(σ′)(τ); the split rows Σ_{σ′ ∈ Sigmas} bSplit_e(σ′)(τ) (legs = the
  triangular solve `blockSolve`); the entrances ι_e(τ); the per-cell J values;
  the shape weights W_Ŝ; and the β-legs q ↦ Σ_{σ′ ∈ Sigmas}
  blockSolve_{e′,τ′}(σ′)(q^δ), one per continuing member (e′, τ′) of each split
  row of block e and per δ ∈ Δ. E(e) is a fixed FINITE subset of ℚ(q).
- For a prime p, D_p denotes any `RegData p` equipped with a pin
  `RegPin C D_p` (as every `UInstance` supplies). Pool(p) := {p^δ : δ ∈ Δ}.

Every statement below is labeled (a) known, (b) new proof of known, or
(c) claimed new. "Corpus theorem" = a sorry-free Lean theorem in this repo.

## 1. Lemma 0 (the dictionary): RegP at a pinned record is a concrete
##    arithmetic condition, and the act-agreement conjunct is free

**Lemma 0** *(c; assembled from the pin fields)*. Let p be prime and D_p pinned.

(i) If DetHyp holds, then

    RegP D_p  ⟺  ∀ δ ∈ Δ, ∀ e ∈ [1, n]:
                 p^δ ∉ Z(Φ_e) ∪ P(Φ_e)          — clause (r1) —
                 and  ∀ g ∈ E(e): p^δ ∉ P(g).    — clause (r2) —

(ii) If DetHyp fails — Φ_{e₀} = 0 in ℚ(q) for some e₀ — then RegP D_p is FALSE
for every prime p.

(iii) In particular the truth value of RegP D_p depends only on (C, p), not on
the choice of pinned record D_p (instance-independence).

*Proof.* Throughout, q₀ := p^δ ∈ Pool(p) with δ ∈ Δ; the pin field `pool_eq`
plus `depth_pin` give `D_p.Pool = Δ.image (p^·)`, so the abstract quantifier
"∀ q₀ ∈ D.Pool" is exactly "∀ δ ∈ Δ at q₀ = p^δ". Note q₀ ≥ 2 always (p ≥ 2,
δ ≥ 1). Fix an abstract block b; via the pin equivalence `blk` it corresponds
to a real e ∈ [1, n], and `st b` identifies the abstract index type with S_e.

(r1). By `K_pin`, the abstract matrix 1 − D.K b is the (st b, st b)-submatrix
of 1 − K_e along a bijection, so det(1 − D.K b) = Φ_e (determinants are
invariant under simultaneous reindexing by an equivalence; this is literally
the computation inside the corpus proof `RegPin.detHyp`,
`MovesU/DefsLedger.lean:536`). The clause demands D_{Φ_e}(q₀) ≠ 0 (definedness)
and eval ≠ 0. Given definedness, eval = N_{Φ_e}(q₀)/D_{Φ_e}(q₀) ≠ 0 ⟺
N_{Φ_e}(q₀) ≠ 0. If D_{Φ_e}(q₀) = 0 the first conjunct fails. So
(r1) at (q₀, e) ⟺ q₀ ∉ P(Φ_e) ∪ Z(Φ_e). Exact, both directions.

(r2). First, the abstract entry Finset `D.entryList b` EQUALS E(e) as a set of
rational functions: the K/bterm/bsplit/ι families are pinned entrywise along
the index bijections (`K_pin`, `bterm_pin`, `bsplit_pin` — the latter under
DetHyp — and `iota_pin`), the J and W families are pinned as IMAGES
(`Jcell_pin`, `W_pin`), and the β-legs are pinned per label and depth
(`betaLeg_pin` under DetHyp, at every δ ∈ D.depthSet, all positive) with the
label set bijective to the real roster (`legEquiv`, `legSt_pin`); `entryList`
is by definition the union of exactly these images with the β-legs collected
over `depthSet` = Δ. So membership g ∈ D.entryList b ⟺ g ∈ E(e).

Next, the agreement conjunct is FREE given definedness: `act_pin` states that
for any g defined at q₀ (g ∈ OKat q₀), D.act g q₀ = evalAt q₀ g, and evalAt is
definitionally `RatFunc.eval (RingHom.id ℚ) q₀` — the very expression on the
clause's left side. (This is the same one-line observation the corpus already
uses in `SolveSeam.R_agree`, whose proof after `act_pin` is `rfl`.) So:
if q₀ ∉ P(g), both conjuncts of the g-clause hold; if q₀ ∈ P(g), the
definedness conjunct fails. Hence (r2) at (q₀, e) ⟺ ∀ g ∈ E(e): q₀ ∉ P(g).
Exact, both directions. This proves (i).

(ii). Suppose Φ_{e₀} = 0. Take b := blk⁻¹(e₀). As above det(1 − D.K b) = Φ_{e₀}
= 0, whose numerator is 0; the evaluation of the zero rational function is 0 at
every point, so the second conjunct of (r1) fails at q₀ = p ∈ D.Pool (the pool
is nonempty: 1 ∈ Δ). Note only `K_pin` was used — no DetHyp needed to run this
branch. Hence RegP D_p fails, for every p.

(iii). The right-hand sides of (i)/(ii) mention only (C, p). ∎

Remark (quantifier bookkeeping). The ⟸ of (i) needs every clause verified for
every (q₀, b); the proof above is uniform in (q₀, b), so this is complete —
no clause of the schema is left unverified: (r1) has exactly the two conjuncts
treated, and (r2) quantifies over exactly the union treated.

## 2. Two standard lemmas

**Lemma 1** *(a — standard)*. Under DetHyp the set

    B := ⋃_{e=1}^{n} ( Z(Φ_e) ∪ P(Φ_e) ∪ ⋃_{g ∈ E(e)} P(g) ) ⊂ ℚ

is finite, with |B| ≤ Σ_e ( deg N_{Φ_e} + deg D_{Φ_e} + Σ_{g ∈ E(e)} deg D_g ).

*Proof.* Each E(e) is finite; each D_g is a nonzero polynomial, so P(g) is
finite (≤ deg D_g roots — a nonzero polynomial over a field has at most its
degree many roots); DetHyp makes N_{Φ_e} nonzero, so Z(Φ_e) is finite; P(Φ_e)
is always finite. Finite unions of finite sets. ∎

**Lemma 2** *(a — folklore; prime-power escape)*. For any finite B ⊂ ℚ and any
finite Δ ⊂ ℤ_{≥1}, the set  Bad(B, Δ) := {p prime : ∃ δ ∈ Δ, p^δ ∈ B}  is
finite; indeed |Bad| ≤ #{ξ ∈ B : ξ is an integer prime power ≥ 2}, and every
p ∈ Bad satisfies p ≤ max(B ∩ ℤ).

*Proof.* If p^δ = ξ ∈ B then ξ is an integer ≥ 2^1 = 2 and a prime power, and
by unique factorization its base prime is determined by ξ; so the map sending
each bad prime to (any) witness ξ is injective into B ∩ {prime powers ≥ 2}.
And p ≤ p^δ = ξ ≤ max(B ∩ ℤ). ∎

## 3. Theorem A: the dichotomy and the exact failing set

**Theorem A** *(c — claimed new as a statement about this schema; proof
assembled from Lemmas 0–2)*. Fix the instance pack C and, for each prime p, any
pinned record D_p. Exactly one of:

(A-i) DetHyp holds. Then, with B as in Lemma 1,

    {p prime : RegP D_p fails}  =  {p : ∃ δ ∈ Δ, p^δ ∈ B},

an EXACT equality; this set is finite, of cardinality at most
#{ξ ∈ B : ξ an integer prime power ≥ 2} ≤ |B|, and every member is
≤ max(B ∩ ℤ). In particular RegP D_p holds for every prime
p > max(B ∩ ℤ), and the set of applicable primes has relative natural
density 1 (it is cofinite).

(A-ii) DetHyp fails. Then RegP D_p fails at EVERY prime.

*Proof.* Lemma 0(i) says RegP D_p fails iff some pool value p^δ lies in B —
that is the exact equality of (A-i); Lemmas 1–2 give finiteness and the bounds.
Lemma 0(ii) is (A-ii). The two cases are exclusive and exhaustive by
definition of DetHyp. ∎

Effectivity: B is computed from the instance data by finitely many gcd/root
computations in ℚ[q] (reduce each entry, factor numerators and denominators);
Δ is computed by the closure construction. So the failing set is decidable
from the instance data, with the explicit prime bound max(B ∩ ℤ).

## 4. Theorem B: the symbolic hypothesis costs nothing

**Theorem B** *(b — already a corpus theorem; recorded here because Theorem A
consumes it)*. At every instance pack C carrying the chain laws, DetHyp holds —
so branch (A-ii) never fires and Theorem A(-i) applies unconditionally.

*Proof (the corpus's, `rs3_det_symbolic`, `MovesS/Rs3DetSymbolic.lean`,
sorry-free).* The rationality burden carries, per (e, τ) and per activity cell,
a nonzero polynomial of bounded degree whose nonvanishing at q₀ characterizes
activity (`cellP_nonzero`, `act_iff`); hence only finitely many pool values
fail all-activity (`allActive_cofinite`). Base-prime pools are infinite
(infinitude of primes), so some base pool q₀* is all-active. The chain field
`pools_e0` supplies an escape package there: the full evaluated matrix
A = K_e(q₀*) has nonnegative rational entries and A^k 𝟙 → 0. If Φ_e were the
zero rational function, its evaluation at q₀* (where every entry, hence the
determinant, is defined — the subring `OKat q₀*` is closed under the
determinant polynomial) would be det(1 − A) = 0, giving a nonzero fixed vector
of A; but A^k v = v for all k with A^k 𝟙 → 0 and entrywise nonnegativity
forces v = 0 (`e0_det_ne_zero`, `pow_fixed_vector`, `mulVec_abs_bound`) —
contradiction. So Φ_e ≠ 0. ∎

## 5. Corollary: theoremU is unconditional at a density-1 set of primes

**Corollary U** *(c)*. In theoremU's frame (fixed n, C, kernels, S, and
`inst : ∀ p hp, UInstance n C KC K7 S p hp`), there is a finite, effectively
bounded set S_bad of primes — S_bad = {p : ∃ δ ∈ Δ, p^δ ∈ B} — such that for
EVERY prime p ∉ S_bad all five conclusion clauses of theoremU hold at p (the
two-sided bracket at every level, ρ_σ(p) = R_σ(p), the true-type and ℤ_p-read
densities equal to R_σ(p), and undecided mass → 0). The applicable primes are
cofinite, hence of relative density 1.

*Proof.* Each `inst p hp` carries `Dpin : RegPin C (inst p hp).D`, so Theorem
A + Theorem B give RegP (inst p hp).D for all p ∉ S_bad (one fixed B for all
p, by Lemma 0(iii) the set does not depend on which pinned record the instance
chose); theoremU's conclusion then fires at every such p. ∎

This is deliverable (D4) of the brief: the per-p hypothesis is converted into
"all primes outside an explicit finite set", i.e. an unconditional statement
about the density of applicable primes.

## 6. Theorem C: where the failures can live (structure of B at prime powers)

Theorem A's B is exact but opaque (poles of the ASSEMBLED entries). The
denominators actually available are highly constrained; this section pins the
failure channels. Let A* ⊂ ℤ_{≥1} be the (finite) set of exponents a occurring
in any carried denominator bound q^b·∏_a (1 − q^a) of any PolyGeom datum
(fields `geom_denom_dvd`), and recall M_k = {products of ≤ k elements of F}.
Set the composite-depth set  M̂ := M_{3n−1}  (finite, computable; it contains
Δ·Δ·M_{n−1} — see the proof).

**Lemma C.1** *(a — localization principle)*. Let 𝒮 ⊂ ℚ[q] be a multiplicative
set of nonzero polynomials and f ∈ ℚ(q) an element of the localization
ℚ[q][𝒮^{-1}] (i.e. f = P/s with P ∈ ℚ[q], s a product of elements of 𝒮). Then
the reduced denominator D_f divides s; hence P(f) ⊆ ⋃_{gen s' ∈ 𝒮 used} {roots
of s'}, and if no generator vanishes at a point x then f is defined at x.

*Proof.* N_f·s = P·D_f with gcd(N_f, D_f) = 1 in the PID ℚ[q], so D_f ∣ s. ∎

**Lemma C.2** *(c — denominator control for the triangular solve)*. For every
e ∈ [1, n], every state τ and verdict multiset σ′, blockSolve_{e,τ}(σ′) lies in
the localization of ℚ[q] at the multiplicative set generated by

    {q} ∪ {1 − q^{am} : a ∈ A*, m ∈ M_{e−1}} ∪ {N_{Φ_{e′}}(q^m) : e′ ≤ e, m ∈ M_{e−1}}.

*Proof (strong induction on e).* Facts used:
(f1) every PolyGeom value has reduced denominator dividing q^b·∏(1 − q^a),
a ∈ A* (carried field) — so it lies in the localization at the m = 1 static
generators; (f2) K_e entries and bTerm rows are finite sums of PolyGeom values
and zeros, and localizations are subrings of ℚ(q), so they lie there too;
(f3) the substitution homomorphism q ↦ q^μ (Lean `powSubst μ`, a ring
endomorphism of ℚ(q)) maps the localization at a generator set G into the
localization at {s(q^μ) : s ∈ G}, and it maps the three generator shapes into
themselves with all exponents multiplied by μ.

Base e = 1: M_0 = {1}. bSplit at block 1 has no continuing member of smaller
size (sizes ≥ 1 and < 1 impossible; the corpus's dite guard returns 0 there),
so its legs are verdict indicators (0/1); with (f2) the exit vector lies in the
static localization. Cramer: (1 − K_1)^{-1} = adj(1 − K_1)/Φ_1, adjugate
entries are polynomials in the K_1 entries (static localization), and
1/Φ_1 = D_{Φ_1}/N_{Φ_1} lies in the localization at the static generators
together with N_{Φ_1}(q^1). Products and sums close up. ✓

Step e: by induction each leg blockSolve_{e′}, e′ ≤ e − 1, lies in the
localization with exponents in M_{e′−1}; a split-row leg reads it through
q ↦ q^{δ_μ} with δ_μ ∈ F (the member's base-change factor — by definition of F
every continuing split member's δ is in F), so by (f3) it lands in the
localization with exponents in M_{e′−1}·F ⊆ M_{e−1}. The σ′-decomposition sum
is finite and the J factors are static, so bSplit_e lies there; adding bTerm_e
(static) and applying Cramer at block e (adjugate static; 1/Φ_e adds the
generator N_{Φ_e}(q^1), 1 ∈ M_{e−1}) completes the step. ∎

**Theorem C** *(c)*. Assume DetHyp (free by Theorem B). Then:

(C1) *The five static families never fail, at any prime.* Every entry of K_e,
every designated bTerm row, every ι, J, W value, and also D_{Φ_e} itself, has
reduced denominator dividing a product of q and (1 − q^a) (a ∈ A*); the
rational roots of such products are {0, 1, −1} (x^a = 1 in ℚ forces |x| = 1,
so x = ±1), and pool values p^δ ≥ 2 never hit them. Hence: the definedness
half of (r1) holds at every prime and pool value, and (r2) restricted to the
K/bterm/ι/J/W families holds at every prime and pool value.

(C2) *Necessary condition for failure.* Every member of E(e) lies in the
localization of Lemma C.2's shape with exponents in M_{2n−1}: the bsplit rows
directly (exponents in M_{n−1}), the β-legs after one more substitution
q ↦ q^δ with δ ∈ Δ ⊆ M_n (exponents in M_{n−1}·M_n ⊆ M_{2n−1}). Evaluating at
a pool value p^{δ′} (δ′ ∈ Δ ⊆ M_n): the static generators are nonzero there by
(C1)'s root computation, and the remaining generators evaluate to
N_{Φ_{e′}}(p^{δ′·m}), δ′·m ∈ M_{3n−1} = M̂. By Lemma C.1, therefore:

    RegP D_p fails  ⟹  ∃ e′ ∈ [1, n], ∃ m ∈ M̂ : N_{Φ_{e′}}(p^m) = 0.

(C3) *Sufficient condition at direct depths.* If N_{Φ_e}(p^δ) = 0 for some
δ ∈ Δ and e, then (r1)'s value clause fails at (p^δ, e) (the determinant is
DEFINED there by (C1), so its junk-free evaluation is genuinely 0), so RegP
D_p fails. Hence the sandwich

    {p : ∃ e, ∃ δ ∈ Δ : N_{Φ_e}(p^δ) = 0}
      ⊆ {p : RegP D_p fails}
      ⊆ {p : ∃ e, ∃ m ∈ M̂ : N_{Φ_e}(p^m) = 0}.

Between the two (numerator vanishing only at descent depths m ∈ M̂ \ Δ),
failure depends on whether the pole survives the σ′-sum's cancellation — not
decided by the schema; Theorem A's B remains the exact criterion.

(C4) *Escape exclusion at covered depths.* For δ ∈ Δ such that ALL states of
all blocks are active at p^δ (all cell-count polynomials nonvanishing —
`act_iff`), the chain's package at that pool (`legs_reg`, available at every
prime and every δ ∈ Δ) has Act = the full state set, and the corpus argument
of `bridge_r1_on_activeLocus` (PROVED, `MovesU/BridgeRosterPins.lean:339`)
gives N_{Φ_e}(p^δ) ≠ 0. So the LEFT set in (C3) is contained in the set of
primes with a non-all-active ("wild") pool value at some direct depth — i.e.
p with some p^δ a root of a cell-count polynomial. No such exclusion is
available at descent depths m ∈ M̂ \ Δ (the chain carries no package there —
exactly the corpus's recorded IB-B16 as-built gap), which is why (C2)'s
superset genuinely needs M̂.

*Proof.* (C1): the divisibility claims are (f1)/(f2) of Lemma C.2 plus
closure of "reduced denominator divides a product of the generators" under sum
and product (denominators of sums/products divide products of denominators —
Mathlib `RatFunc.denom_add_dvd`/`denom_mul_dvd`; for the determinant, det is a
polynomial combination of the entries). The root computation is elementary.
(C2): Lemma C.2 + (f3) for the outer δ, then Lemma C.1. (C3): direct. (C4):
the cited corpus proof: evaluation commutes with det on the subring OKat, the
full evaluated matrix equals the package's active matrix when Act = univ, and
escape kills any nonzero fixed vector, so det(1 − K_e(p^δ)) ≠ 0; combined with
(C1)-definedness this is N_{Φ_e}(p^δ) ≠ 0. ∎

## 7. Sharpness: finiteness cannot be improved to emptiness at schema level

The corpus's compiled countermodel (`MovesU/BridgeB15a_r2Neg.lean`, sorry-free)
is an admissible n = 2 pack — every carried chain law holds, DetHyp holds —
with Φ_1 = (q − 4)²(q² − 2)/q⁴ and one split row at block 2 whose continuing
member has depth δ = 2, so F = {2}, Δ = {1, 2, 4}. There:

- N_{Φ_1} = (q − 4)²(q² − 2) has rational zero set {4}; 4 = 2² = p^δ at
  (p, δ) = (2, 2) ∈ prime × Δ — so by (C3) (REG-2) fails at the direct depth 2;
- the block-2 split row is t̂₁(q²) with t̂₁ = ((q−4)²(q²−2)+1)/(2(q−4)²(q²−2)),
  whose reduced denominator has rational roots {±2}: the same failure shows up
  as an (r2) pole at the base pool q₀ = 2 (the corpus's own exhibited clause);
- the full B of Theorem A there: 4 (zero of N_{Φ_1}, and again the pole of the
  δ = 1 β-leg t̂₁(q)), ±2 (poles of the bsplit row / the δ = 2 β-leg t̂₁(q²));
  the δ = 4 β-leg's candidate poles (q⁴ ∈ {4, 2}) are irrational, and all
  remaining denominators are static. Prime powers in B: {2, 4}, both with base
  prime 2 — so by Theorem A the failing set is EXACTLY {2}, and for every
  p ≥ 3, δ ∈ {1, 2, 4}, every clause of (REG-p) holds.

So: nonempty failing sets occur at admissible instances (no proof from the
carried laws can give "(REG-p) for all p"), and Theorem A's finiteness with
exact characterization is the optimal general statement. Consistently, the
corpus's own attempt at "for every p on the active locus" (IB-B15a) was
refuted by exactly this countermodel, while the finiteness statement proved
here is untouched by it.

## 8. The intended instance, and one genuinely open question

For the REAL degree-2 instance (`MovesS/N2*.lean`): Δ = {1}, Φ_1 = 1,
Φ_2 = (q³ − 1)/q³, so N_{Φ_e}-zeros are {1} — not a prime power — and every
E(e) member is static or has denominators dividing powers of q (block 1's
solve has K_1 = 0, so no determinant denominators enter the legs). By Theorem
A/C: **the failing set of the real n = 2 instance is EMPTY — (REG-p) holds at
every prime p.** (This also matches the corpus's separate proof of the
MovesS-level packages at every prime, `n2_pools_all`.)

**Open question OL-1** *(explicitly not settled here)*. For the intended
(Okutsu–Montes) instance at general n, is the failing set empty — i.e. does
N_{Φ_e}(p^m) ≠ 0 hold at every prime power, including wild pools and descent
depths m ∈ M̂ \ Δ? Plausibility: at the intended instance the entries of
K_e(p^m) are volumes of continuation events, so the matrix should be
substochastic with termination mass > 0 at EVERY prime power, giving
spectral radius < 1 — but the schema does not carry this at wild pools (the
countermodel exploits precisely that), so it is a property of the intended
instance to be proved separately, not of the ledger. Theorem A does not need
it.

## 9. Lean-implementability notes (for a future unit; no proofs claimed here)

- Lemma 0 is pin-rewriting; its (r1) leg is the existing `RegPin.detHyp`
  computation run at fixed q₀, and its act-freeness leg is the existing
  `SolveSeam.R_agree` pattern (`act_pin` then `rfl`).
- Lemma 1: `Polynomial.setOf_root_finite`-style facts; Mathlib's
  `Polynomial.roots` is a Multiset, finiteness is built in.
- Lemma 2: injectivity into B via unique factorization
  (`Nat.Prime.pow_injOn`-style; or directly `Nat.pow_left_injective` +
  uniqueness of the prime divisor of a prime power).
- Theorem B is `MovesS.rs3_det_symbolic` verbatim.
- Theorem A then assembles; the statement could be typed as: ∃ S : Finset ℕ,
  ∀ p, p.Prime → p ∉ S → RegP (inst p hp).D. This would upgrade theoremU to a
  cofinite-conclusion corollary without touching its statement (statement
  fence respected: RegP itself unchanged).

## VERDICT

VERDICT: PROVED (Theorems A + B + Corollary U: at every pinned instance the
set of primes failing (REG-p) is finite with an exact, effectively computable
characterization, hence theoremU applies at a cofinite — density-1 — set of
primes; Theorem C confines all failure channels to determinant-numerator
vanishing at an explicit finite composite-depth set; emptiness of the failing
set is REFUTED at schema level by the corpus countermodel and is proved for
the real n = 2 instance; emptiness for the intended instance at general n
remains open as OL-1).

## NUMERIC-TESTS

All tests are exact rational arithmetic (sympy); no p-adic library needed for
T1/T2/T4. Scripts would live in `verification/`.

EXECUTED (2026-07-31, this session, sympy from
`verification/.venv-openmath`): the cores of T1 and T2. Results, all exact:
(i) countermodel identity 1 − k = (q−4)²(q²−2)/q⁴ verified; k(m) ∈ (0,1) at
prime powers m ∈ {2,3,5,7,8,9,16,25,27,32} and k(4) = 1 (the escape claims);
(ii) reduced denominator of the bsplit row t̂₁(q²) factors as
2(q−2)²(q+2)²(q⁴−2), rational roots exactly {±2}; N_{Φ_1} rational roots
exactly {4}; (iii) full clause scan over p < 550, δ ∈ {1,2,4}: empirical
failing prime set = {2} EXACTLY — Theorem A's predicted set, confirming the
dictionary's exactness on the countermodel; (iv) real n = 2 instance: rational
roots of N_{Φ_2} = q³−1 are exactly {1}, det-channel failing primes over
p < 550: none — confirming §8's empty failing set on the determinant channel.
Remaining to run: T1's full (r2) family transcription, T3, T4, T5.

**T1 (real n = 2 instance: failing set empty).** Data: Φ_2(q) = (q³−1)/q³,
Φ_1 = 1, Δ = {1}; entry families with denominators dividing powers of q
(transcribe the eight n2 PolyGeom values from `MovesS/N2PolyGeom.lean` /
`N2ScsData.lean`). Compute: rational roots of N_{Φ_2} = q³−1 (sympy
`nroots`/`factor_list`) → expect exactly {1}; for p in the first 200 primes
and δ ∈ Δ check D_g(p^δ) ≠ 0 for every transcribed g and N_{Φ_e}(p^δ) ≠ 0.
CONFIRMS Theorem A/§8 if zero failures; ANY failing prime refutes §8.

**T2 (countermodel sharpness: failing set exactly {2}).** Data (from
`BridgeB15a_r2Neg.lean` header): k(q) = (8(q−2)q² + 2(q−4)²)/q⁴. Verify
symbolically: 1 − k = (q−4)²(q²−2)/q⁴; t̂₁ = ((q−4)²(q²−2)+1)/(2(q−4)²(q²−2));
bsplit row = t̂₁(q²). Compute B: rational roots of the reduced numerators and
denominators of {Φ_1, Φ_2, all entries, t̂₁(q²), t̂₁(q^{2δ}) for δ ∈ {1,2,4}}.
Expect B ∩ {prime powers ≥ 2} = {4} ∪ {2 from the t̂₁(q²) pole} → predicted
failing set {2}. Then scan p ∈ first 100 primes, δ ∈ {1,2,4}: evaluate every
(r1)/(r2) clause literally. CONFIRMS Theorem A's exactness iff the empirical
failing set is exactly {2}; any p ≥ 3 failure, or a clean pass at p = 2,
refutes the dictionary (Lemma 0).

**T3 (end-to-end density read at n = 2).** Using the existing PARI oracle
pattern (`verification/quartic_oracle.py`, cypari2 `factorpadic`): for
p ∈ {2, 3, 5, 7, 11, 13} and N = 6, enumerate (or sample 10⁵ of) the monic
quadratics over ℤ/p^N, classify the ℚ_p-factorization type of lifts, and
compare empirical σ-densities against the corpus's R_σ(p) values (from
`MovesS/N2SolveVals.lean`). Expect agreement within O(p^{−N}·counting error)
at EVERY probed p including p = 2 — consistent with §8's empty failing set
(a persistent discrepancy at some small p would suggest a real (REG-p)
failure for the intended instance, refuting §8/OL-1 optimism).

**T4 (fuzz of the dictionary + escape bound).** Generate ~200 random schema
instances: block count ≤ 3, state sets of size ≤ 3, entries random
c·q^{−b}·∏(1−q^{−a})^{ε} in the PolyGeom class, random F ⊆ {2, 3}, Δ the ≤
n-fold closure. For each: compute B symbolically; predict the failing set via
Theorem A; then scan all p ≤ 10⁴, δ ∈ Δ, evaluating every clause exactly.
CONFIRMS if predicted = observed on every instance and |observed| ≤ #(B ∩
prime powers) and max(observed) ≤ max(B ∩ ℤ); any mismatch refutes Lemma 0 /
Lemma 2 bookkeeping.

**T5 (Theorem C's M̂ bound).** On T4's instances with nontrivial split
nesting, additionally compute the reduced denominator of every assembled
bsplit/β-leg entry and check its rational roots ξ satisfy: ξ ∈ {0, ±1} or
ξ^m ∈ roots(N_{Φ_{e′}}) for some m ∈ M̂, e′. CONFIRMS Lemma C.2's generator
bookkeeping; a root outside the predicted classes refutes the exponent
accounting (M_{3n−1}).

