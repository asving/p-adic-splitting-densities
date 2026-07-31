# M17-regp-density — problem brief (neutral, self-contained)

## One-line statement

Theorem U — the corpus's capstone: "for each splitting type σ of degree n there is
ONE rational function R_σ ∈ ℚ(q) whose value at q = p is the density of monic
degree-n polynomials over ℤ_p of factorization type σ, at every prime p" — carries
exactly one per-prime hypothesis, a regularity predicate (REG-p). Determine at
which primes (REG-p) holds: prove it holds for all but finitely many p (or at
least at a set of primes of relative density 1), or characterize the failing set.
This converts the per-p hypothesis into an unconditional statement about the
density of primes to which the theorem applies.

## Background: the fixed instance data (all of it p-independent)

The corpus proves the uniformity theorem through a transfer-matrix ("depth
resummation") linear system. Fix the degree n ≥ 2. A *splitting type* σ of degree
n is a multiset of pairs (e, f) with all entries ≥ 1 and Σ e·f = n (the
ramification indices and residue degrees of the ℚ_p-irreducible factors). The
classification engine resolves a polynomial block by block; the bookkeeping is a
fixed finite table, and the solve produces, for each σ, one rational function
R_σ(q) ∈ ℚ(q). The following data is fixed once (independent of the prime p):

- **Blocks and states.** For each block degree e ∈ {1, …, n}, a finite set S_e of
  classifier states.
- **The kernel matrix.** For each e, a matrix K_e ∈ M_{S_e×S_e}(ℚ(q)): the (τ, β)
  entry is the total rational mass of the "whole-block continuation" rows leading
  from state τ to state β. Write Φ_e := det(1 − K_e) ∈ ℚ(q).
- **Exit vectors.** For each e and state τ: a terminal row b_e^{term}(τ) ∈ ℚ(q)
  (the mass of rows that halt, summed over the emitted verdict multisets in the
  row's displayed support) and a split row b_e^{split}(τ) ∈ ℚ(q) (branching rows:
  a per-branching-cell mass J times, for each branch member, either a verdict
  indicator or a lower-block solution evaluated at q^δ, where δ ≥ 1 is the base-
  change depth carried by that member).
- **Lower-block solutions.** β_{e,τ}(σ′) ∈ ℚ(q) ("blockSolve") is defined by the
  triangular Cramer solve, bottom-up in e:
      β_e = (1 − K_e)^{-1} · (b_e^{term} + b_e^{split}[legs ← β_{e′}, e′ < e]),
  where inside b^{split} each continuing member of size e′ < e feeds back
  β_{e′,τ′}(σ″) composed with the substitution q ↦ q^{δ} (its base-change depth).
  These exist as rational functions provided the *symbolic determinant
  hypothesis* holds: Φ_e ≠ 0 in ℚ(q) for every e ∈ {1, …, n}.
- **Entrance masses** ι_e(τ) ∈ ℚ(q), **per-branching-cell masses** J (a finite
  family in ℚ(q)), and **shallow-shape weights** W_Ŝ (a finite family in ℚ(q)).
- **The depth set.** A finite set Δ ⊂ ℤ_{≥1} with 1 ∈ Δ: the multiplicative
  closure, allowing products of at most n factors, of all base-change depths δ
  consumed by the table's split rows and shape legs. (In the corpus:
  `consumedDeltas`; in the n = 2 instance Δ = {1}.)

A structural fact carried by the corpus (field `geom_denom_dvd` of the
"rationality burden" record): each of K_e's entries, each b^{term} row, each ι, J,
and W entry is of the form (polynomial) × g where the reduced denominator of g
divides q^b · ∏_{a ∈ A} (1 − q^a) for some b ≥ 0 and finite A ⊂ ℤ_{≥1} (the
q-geometric denominator class of the height resummations).

## The precise obligation

For a prime p, the *pool* of p is Q(p) := {p^δ : δ ∈ Δ}. The hypothesis (REG-p)
is: for every pool value q₀ ∈ Q(p) and every block e ∈ {1, …, n},

- **(r1)** Φ_e = det(1 − K_e) is *defined* at q₀ (the reduced denominator does
  not vanish at q₀) and its value there is ≠ 0 — the FULL determinant, all
  states included (no restriction to an "active" subsystem);
- **(r2)** every member g of the *entry list* E(e) is defined at q₀ and its
  literal evaluation g(q₀) equals the instance's designated "active value"
  act(g, q₀), where

  E(e) := {entries of K_e} ∪ {b_e^{term}(τ) : τ} ∪ {b_e^{split}(τ) : τ}
          ∪ {ι_e(τ) : τ} ∪ {J cells of block e} ∪ {W_Ŝ : all shapes Ŝ}
          ∪ {q ↦ Σ_{σ′} β_{e′,τ′}(σ′)(q^δ) : one entry per continuing member
             (e′, τ′) of each split row of block e, for EVERY δ ∈ Δ},

  the σ′-sum running over the exact degree-n verdict index of the solve.

The Lean form (`lean/LeanUrat/MovesU/Defs.lean`, the normative statement):

```lean
def RegP {p : ℕ} (D : RegData p) : Prop :=
  ∀ q₀ ∈ D.Pool, ∀ e : D.Block,
    (letI := D.instBi e; letI := D.instBd e;
     DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
     (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0) ∧
    ∀ g ∈ D.entryList e,
      DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀
```

with `DefinedAt g q₀ := g.denom.eval q₀ ≠ 0` (reduced denominator; Mathlib's
`RatFunc` is always in lowest terms, and `.eval` returns the junk value 0 at a
pole). Here `D : RegData p` is an abstract per-prime data record: a finite block
type, per-block index types for states/cells/shapes/legs, matrices and entry
families over ℚ(q), the pool `D.Pool = D.depthSet.image (p ^ ·)`, and an
"active-value" map `D.act : RatFunc ℚ → ℕ → ℚ`. `D.entryList e` is the Finset
union of the seven displayed families (the β legs collected at every
δ ∈ D.depthSet).

The abstract record is tied to the fixed instance data by a *pin* record
(`RegPin C D`, `lean/LeanUrat/MovesU/DefsLedger.lean`), which forces: the blocks
biject with {1, …, n}; the per-block index types biject with the real state
sets; `D.K`/`D.iota`/`D.bterm` equal the real K_e/ι_e/designated-b^{term} rows
entrywise; the J and W families have exactly the real value images; `D.depthSet`
equals Δ; `D.bsplit` and `D.betaLeg` equal the real split rows and β-legs
(these two pins are stated under the symbolic determinant hypothesis, which the
solve needs to define β at all); and `D.act` agrees with literal evaluation of
the (reduced) rational function on its defined locus:

```lean
act_pin : ∀ (g : RatFunc ℚ) (q₀ : ℕ) (hok : g ∈ MovesS.OKat (q₀ : ℚ)),
    D.act g q₀ = MovesS.evalAt (q₀ : ℚ) ⟨g, hok⟩
```

(`OKat q₀` = the subring of rational functions whose reduced denominator does
not vanish at q₀; `evalAt` = evaluation there, definitionally
`RatFunc.eval (RingHom.id ℚ) q₀`.)

## How the obligation is consumed

The capstone (`lean/LeanUrat/MovesU/U10_theoremU.lean`):

```lean
theorem theoremU (n : ℕ) (hn : 2 ≤ n) … 
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) :
    ∃ R : SplittingType n → RatFunc ℚ,
      R = S.R ∧ (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime), RegP (inst p hp).D →
        (… two-sided counting bracket at every level N …)
        ∧ (∀ σ, Tendsto (dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))     -- ρ_σ(p) = R_σ(p)
        ∧ (∀ σ, Tendsto (trueDmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))  -- true-type density
        ∧ (∀ σ, Tendsto (zpDmass … σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))  -- ℤ_p-read density
        ∧ Tendsto env atTop (𝓝 0)                                 -- undecided mass → 0
```

Every `UInstance` carries `D : RegData p` together with `Dpin : RegPin C D`, so
the question is posed at pinned records. At a prime failing (REG-p) the theorem
makes NO claim. (REG-p) is the ONLY per-prime hypothesis; everything else in the
signature is p-uniform. So: the set {p prime : RegP (inst p hp).D} is exactly
the set of primes at which the capstone's conclusions fire, and the open math is
its size.

## What is already proved in the corpus (all sorry-free unless noted)

1. **Per-pool escape packages at every prime** (`RS4Chain.legs_reg`, a carried
   hypothesis of the framework; `MovesS.RegP`, a DIFFERENT and weaker predicate
   than the (REG-p) above): for every prime p, every δ ∈ Δ, every e, there is a
   designated subset Act ⊆ S_e of "active" states at q₀ = p^δ such that all
   entries of K_e restricted to Act×Act are defined at q₀, the evaluated active
   matrix A = K_e(q₀)|_{Act×Act} has nonnegative entries with
   A^k · 𝟙 → 0 as k → ∞ ("escape"), and every (active row, inactive column)
   entry evaluates to 0. Inactive ("junk") rows are unconstrained.
2. **Activity is cofinite in the pool variable** (`allActive_cofinite`,
   `lean/LeanUrat/MovesS/AllActiveCofinite.lean`): a state is active at q₀ iff
   none of its finitely many nonzero "cell-count" polynomials (each of degree
   bounded by a table constant) vanishes at q₀; hence only finitely many pool
   values in the ambient pool set fail all-activity.
3. **The symbolic determinant hypothesis is a theorem** (`rs3_det_symbolic`,
   `lean/LeanUrat/MovesS/Rs3DetSymbolic.lean`): from 1 + 2 and the infinitude of
   primes, Φ_e ≠ 0 in ℚ(q) for every e (`MovesS.DetHyp`).
4. **(r1) holds at all-active pool values** (`bridge_r1_on_activeLocus`,
   `lean/LeanUrat/MovesU/BridgeRosterPins.lean`, PROVED): for every prime p and
   every δ ∈ Δ such that ALL states of every block are active at p^δ, clause
   (r1) holds at (p^δ, e) for every e — via evaluation-commutes-with-det on the
   local subring plus "escape ⟹ no nonzero fixed vector ⟹ det(1 − A) ≠ 0"
   (`e0_det_ne_zero`).
5. **(r2)-at-every-prime-on-the-active-locus is FALSE at schema level**
   (`lean/LeanUrat/MovesU/BridgeB15a_r2Neg.lean`, a COMPILED countermodel,
   sorry-free): there is an admissible n = 2 instance pack satisfying every
   carried chain law, with the symbolic determinant hypothesis TRUE, and a prime
   (p = 2) at which (r2) fails at an all-active pool value: a split-row entry
   reads a lower-block solution through q ↦ q², importing a genuine pole from
   the pool value 4 = 2² down to the base pool q₀ = 2. So no argument from the
   carried laws alone can prove "(REG-p) at EVERY prime"; any correct result
   must tolerate a nonempty finite exceptional set at adversarial instances.
   In that countermodel Δ = {1, 2, 4} and the failing prime set is {2}.
6. **The n = 2 probe instance** (`lean/LeanUrat/MovesS/N2*.lean`): the real
   degree-2 table has singleton state sets, Δ = {1}, K_1 = 0 (so Φ_1 = 1), and
   Φ_2 = (q³ − 1)/q³ (`n2_det`); the packages of item 1 are proved there at
   every prime. No compiled proof of the (REG-p) predicate above exists at any
   probed (instance, p) — the MovesS-level packages (item 1) are the certified
   gates.
7. **The wild-pool gap record** (IB-B16, `BridgeRosterPins.lean`): on
   non-all-active pool values the (r1) clause demands MORE than the source
   proof note warrants (the note records junk-block determinant zeros as
   findings, not failures); the corpus deliberately leaves (REG-p) as an
   explicit hypothesis there.

## What a proof must deliver

Primary target, at an arbitrary instance satisfying the carried laws (items 1–3
above are available as hypotheses; the pin fixes all objects):

- **(D1)** A theorem: the set {p prime : (REG-p) fails at the pinned record} is
  finite — or, if that is not provable, a density-1 statement, or a compiled-
  countermodel-style refutation. By item 5 the theorem cannot conclude the set
  is empty; by item 5 any claimed characterization must contain {2} for the
  countermodel instance and (by item 6, expectedly) be empty for the real n = 2
  instance.
- **(D2)** A characterization of the failing set in terms of the fixed instance
  data (exact if possible; otherwise an explicit finite superset), effective
  enough to be computed for a concrete instance.
- **(D3)** An honest statement of which clauses of (REG-p) can fail at all
  ((r1) vs (r2), which entry families), and of any hypotheses used beyond the
  carried chain laws.
- **(D4)** The consequence for Theorem U, stated: with the per-p hypothesis
  replaced by "p outside the finite set of (D2)", the conclusion clauses hold
  unconditionally at all remaining primes (relative density 1 of applicable
  primes).

Instance-independence should be addressed: (REG-p) is stated on an abstract
record `D`, but two records at the same prime pinned to the same instance data
should have the same (REG-p) truth value; a proof should either show this or
work uniformly over all pinned records.

Reader assumptions: p-adic fields, Newton polygons, Okutsu–Montes/MacLane
theory, Igusa/Denef rationality are assumed known; every project-internal name
used above has been re-expanded here — the Lean files quoted are the normative
statements.
