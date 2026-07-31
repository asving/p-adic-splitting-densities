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
