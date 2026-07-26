# ASSEMBLY_PLAN_2026-07-26 — the final campaign: from accepted §C to the complete wild-uniformity theorem

*Plan architect: Fable, 2026-07-26. Directive (Asvin, 2026-07-26): iterate on the math with
Codex until either a COMPLETE math proof of wild uniformity exists or the approach is shown
conclusively to not work. This plan is the architecture for everything between the accepted
§C (MOVES_2026-07-24.md, passes 12+13 CLEAN) and the endpoint theorem.*

## 0. The endpoint and the certified inputs

**THEOREM U (the target).** For each degree n and factorization type σ (a multiset of
(e, f) pairs with Σ e·f = n), there is ONE rational function R_σ ∈ ℚ(q) such that for
EVERY prime p — wild p ≤ n included — the density of monic degree-n f ∈ ℤ_p[x] with
type σ equals R_σ(p); and Σ_σ R_σ = 1 identically in q.

**Certified perimeter this plan consumes (nothing else is assumed):**
- **§C / Theorem C** (MOVES ledger, ACCEPTED): for every REALIZABLE lift-carrying history
  H = (ν₀,…,ν_k) and admissible terminal system Z, at every N ≥ N(H, Z):
  #{f mod p^N ∈ S(H, Z)} = p^{nN} · ∏ᵢ vol(E_fresh(νᵢ)) · vol(Z), with Ψ_H a mass-exact
  bijection onto the image locus. Each vol(E_fresh(νᵢ)) = product of per-digit factors
  (alphabet cardinality)⁻¹, a power of p determined by the history's SHAPE data (C.3).
- **§B2-DEF** (ACCEPTED): the per-move ledger D.11 at all tower stages (the order-r
  induction TRANS), increments at any (e, h, g, μ, a), recenterings at e_read = 1,
  lift-independence D.10, realizability (NA)/(HV).
- **§A, §B1 (surviving parts), JOINT-D1**; eleven sealed census gates (Cases E…L).
- **The decomposition note** (`MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md`, ACCEPTED):
  Lemma 3.2 (depth ⟹ ind ⟹ v_p(disc); GMN pins (P1)–(P3)), Lemma 3.3 (discriminant
  tail (3b), elementary), Cor 3.4 (Desc_d envelope (3c)), Thm 2.1 (N-stability),
  Lemma 3.1/3.4′ scaffolding, the OPEN-D4 statement (3i) + its (R1)/(R2) reduction
  shape, §4 (the conditional resummation blueprint 4.1–4.5), L3/Claim 4.3
  (per-shape counts are universal polynomials in the pool size Q).
- **L5fix** (`L5fix_complete.md`, accepted long since): termination invariants; the
  cluster-tree shape menu 𝒯_n is finite and p-independent (Serre different bound).
- **The n=2 precedent** (W5/W6/W6q, machine-checked): chain menus → geometric series
  (`msW_eighth_le` fixpoint) → two-sided squeeze (U) → `montes_uniform_n2` with fixed
  (num, den) per type. This is the pattern each note below generalizes.

## 1. The DAG of the remaining notes

Five notes. Arrows = "consumes the accepted statement of".

```
      §C (Theorem C)          decomposition note §3 (3.2/3.3/3.4)
       │        │                      │
       ▼        ▼                      ▼
   [1] D4-R   [2] MENU            [5] EXHAUST
       │        │   │                  │      (tie-in: MOVES depth ⟹ Desc_d)
       │        │   └──────────┐       │
       ▼        ▼              │       │
      [3] RESUM ◄──────────────┘       │
           │  (abs. convergence ◄──────┤
           ▼                           │
      [4] SQUEEZE ◄────────────────────┘
           │
           ▼
   THEOREM U  (assembly capstone paragraph inside [4])
```

- **[1] D4-R** — *the per-shape-prefix mass law*: restates OPEN-D4 with Theorem C
  replacing joint-D1; the first aggregation-over-VALUES statement (fixed shape-prefix,
  sum over realizable digit values). Small note; the warm-up layer for [3].
- **[2] MENU** — *shape-menu finiteness at general n*: MOVES histories, quotiented by
  their ℕ-valued depth/height parameters, form a finite p-independent combinatorial
  menu 𝒮_n (the L5fix-analog at history granularity).
- **[5] EXHAUST** — *the discriminant-tail tie-in*: every depth-d realizable MOVES
  history's stratum lies in Desc_d, so undecided/deep mass ≤ (n−1)·p^{−⌈(2d−n·v_p(n))/(n−1)⌉}.
  Pointwise, rate-free of per-depth identities (the wall stays sidestepped).
- **[3] RESUM** — *the depth resummation*: aggregating Theorem C's per-history products
  over the menu into a finite TRIANGULAR linear system over ℚ(q) (the engine's β_e
  fixpoint form), solved bottom-up in cluster size; solution = R_σ ∈ ℚ(q); p-uniformity
  derived, never imported.
- **[4] SQUEEZE** — *the two-sided finite-level bound*: decided_σ(N) ≤ R_σ(p)·p^{nN}
  (the fixpoint upper bound, n=2 (U)-pattern generalized) and ≥ (R_σ(p) − env(N))·p^{nN}
  (box partition + EXHAUST), hence ρ_σ exists and equals R_σ(p) — Theorem U.

**Execution order:** [1] → [2] ∥ [5] → [3] → [4]. [1] first (smallest, sharpens the
aggregation vocabulary all later notes use). [2] and [5] are independent of each other.
[3] is the campaign's center of mass. [4] closes.

**Format per note (sections 2–6 below):** key definitions · load-bearing lemmas with
proof sketches · kernels (fresh-context derivation-grade, C10B/C15-style) · the sealed
gate that must PASS before the note may be trusted (§7 protocol). All gates are at
n = 3 (both p = 2 and p = 3 are wild there) — the first genuinely-general-n gates.

## 2. NOTE [1] D4-R — the per-shape-prefix mass law (Theorem C consumed)

**What D4 was.** Decomposition note (3i): for class-3 read-prefixes P,
μ(P) ≤ p^{−A_net(P)}, A_net(P) := A(P) − W(P), with A(P) the ledger exponent and
W(P) = Σ_r w_r·d_r the pool dimension — UNIFORMLY in p. Its reduction (R1)/(R2) ran
through joint-D1's conditional-on-ancestors clause. §C now supplies that clause in
proved form: C.1.5(1) — mass(Σ_i ∩ stratum(ν_{i+1})) = mass(Σ_i)·vol_nom(E_fresh(ν_{i+1}))
— IS the chain rule (R2) needed, and Theorem C(b) with Z = ∅ is its closed composition.

**Key definitions.**
- SHAPE-PREFIX P̂: a history prefix with node VALUES forgotten — species, (e, h, g, μ, a),
  strides, residue degrees w_r retained; the side-digit tuples (d_j) and lifts forgotten.
- The value fiber: Hist(P̂) := { realizable lift-carrying histories H with shape P̂ },
  taken up to lift-transport (C.0's LIFT-TRANSLATION REMARK: transported pairs have
  equal masses; MENU's Lemma M3 makes this quotient honest).
- C_P̂(p) := #(value assignments realizing P̂) — realizability = (NA)/(HV) per node.

**Load-bearing lemmas.**
- **D4R.1 (exact prefix mass).** μ(P̂) = Σ_{H ∈ Hist(P̂)} ∏ᵢ vol(E_fresh(νᵢ))
  = C_P̂(p)·p^{−A(P̂)}. *Sketch:* strata of distinct realizable H are disjoint (the
  reader is deterministic; fixed shape ⟹ same read frame, different values ⟹ disjoint
  digit cylinders); each mass is Theorem C(b) with Z = ∅; vol(E_fresh) depends only on
  shape (C.3), so the sum factors as (count) × (common p-power).
- **D4R.2 (pool bound, p-uniform).** C_P̂(p) ≤ p^{W(P̂)}: each read's value choices
  live in ≤ d_r digit functionals over a pool of size Q_r = p^{w_r}; (NA)/(HV) only
  shrink the count. Hence (3i) verbatim: μ(P̂) ≤ p^{−A_net(P̂)}.
- **D4R.3 ((HV)-uniformity — the torus lemma).** The number of side-pattern values with
  a GIVEN residual shape and GIVEN lead value vtx ∈ F_{i+1}ˣ is independent of the vtx
  value: the count for lead = c equals the count for lead = 1 (scale the pattern by the
  torus action z ↦ u·z, u ∈ Fˣ, which permutes shapes' realizations shape-preservingly).
  *This is what makes C_P̂(p) a function of the SHAPE alone* — realizability (HV) pins a
  lead to an ancestor-determined value, and without this lemma the count could depend on
  which value, killing the universal-polynomial form downstream.
- **D4R.4 (N-stability).** μ(P̂) is computed at any N ≥ max_H N(H, ∅) — finite because
  Hist(P̂) is finite (fixed shape bounds all heights). [Thm 2.1 of the decomposition
  note re-derived from Theorem C's N(H, Z) clause.]

**Kernels (derivation-grade):** D4R.3 (the torus lemma — a fresh-context derivation with
explicit small-field examples; watch the μ ≥ 2 case where the ψ^μ-normalization
interacts with the scaling) and the disjointness argument in D4R.1 (same-shape distinct-
value strata: the FIRST differing digit separates the cylinders — must be argued at the
transported coordinates, not the nominal ones).

**Sealed gate D4-n3 (new formula layer: the aggregated prefix mass).** n = 3, class-3
prefix: root read with residual shape (irreducible quadratic)·(linear) → deg-2 key
φ lifting the quadratic → one depth-1 descend at the deg-2 key (side data fixed, μ = 1).
Seal BEFORE running: the exact count C_P̂(p) (from D4R.2/D4R.3's formula), A(P̂), and
the predicted #{f mod p^N ∈ P̂} = C_P̂(p)·p^{3N−A} at p = 2 AND p = 3, two levels N
each; plus the net bound check. PASS = all exact. (Extends Case-E/JOINT-D1 gates, which
fixed values; this is the first VALUE-AGGREGATED sealed prediction.)

## 3. NOTE [2] MENU — shape-menu finiteness at general n

**The statement to prove.**
> **Theorem MENU.** Fix n. Define the shape of a realizable lift-carrying history by
> forgetting: all side HEIGHTS h (per read), all self-loop repetition counts (depths),
> all lifts, all digit values — retaining the finite tree of reads with per-node
> species (increment / recentering / root), slope denominators e, key degrees,
> multiplicities μ, residual SHAPES (degree–multiplicity partitions of the residual
> polynomial), residue degrees w, stride/anchor combinatorics, and the flank/co-factor
> pattern. Then the set 𝒮_n of shapes is FINITE and INDEPENDENT of p, and every
> realizable history is a shape + a tuple of ℕ-parameters (heights, depths) ranging
> over explicit per-shape cones.

**Load-bearing lemmas.**
- **M1 (per-node data bounded).** At any node: key degree ≤ n, e ≤ n, μ ≤ n, residual
  degree ≤ n, w ≤ n!-bounded (residue degrees multiply along the tower, Σ e·f ≤ n at
  each stage), #sides ≤ n, strides/anchors bounded by the side width ≤ n. *Sketch:*
  the stage data of §B2-DEF D.0 carries deg Φ_r · (Σ over sides) ≤ n throughout; every
  bound is a degree budget.
- **M2 (skeleton bounded — the L5fix transport).** Quotient the read tree by (i) ladder
  directions (heights within one read) and (ii) tower directions (self-loop chains at
  fixed key data — consecutive recenterings/descends that change no retained datum).
  The quotiented skeleton has ≤ n − 1 proper-refinement internal nodes (each strictly
  refines the (e, f)-partition or strictly increases Σ eᵢfᵢ toward n — L5fix Invariant 1
  transported to MOVES nodes), and self-loop PHASES per node are bounded p-independently
  (L5fix §2: the Serre different bound (n−1) + n·log₂n caps the distinct wild phases).
- **M3 (lift quotient is mass-honest).** Two admissible lifts at a node differ by a
  weight-> side-value element; the conjugating translation transports the joint stratum
  mass-equally with correspondingly transported downstream data (C.0 remark, accepted).
  Hence mass and E_fresh-volume are functions of the lift-transport CLASS; the menu may
  and does quotient lifts.
- **M4 (parameter cones explicit).** For each shape S ∈ 𝒮_n, the realizable histories
  of shape S are exactly the lattice points of an explicit product of cones
  (height cones: strictly-decreasing-slope conditions per polygon; depth cones: ℕ^k),
  and vol(E_fresh)-exponents are AFFINE in these parameters with positive weights.
  *Sketch:* D.3's stride rule makes the per-digit pin count affine in h; the (‡) ledger
  arithmetic of the decomposition note §2, now unconditional via §B2-DEF/§C.*
- **M5 (menu completeness).** Every monic f with terminating resolution has its history
  of some shape in 𝒮_n — i.e. the retained data really is closed under the classifier's
  moves. *Sketch:* §B2-DEF TRANS constructs stage r+1 data of exactly the retained
  vocabulary; nothing else occurs.

**Kernels:** M4 (the affine-exponent bookkeeping — this is where the (‡) lattice
arithmetic gets its unconditional general-n derivation; derivation-grade, with the
Case-J anchor-monomial a > 0 exponents as worked instances) and M2's tower-quotient
well-definedness (what exactly a "self-loop at fixed key data" is at order r ≥ 2 —
the e_birth vs e_read threading must be re-walked once here).

**Sealed gate MENU-n3.** Enumerate 𝒮_3 (the finite list, with per-shape parameter
cones) BEFORE any census. Then brute-force p = 2, p = 3, and tame control p = 7:
classify ~10⁶ random monic cubics, extract each realized history's shape; PASS =
(i) every realized shape is on the sealed list; (ii) every sealed shape with nonempty
predicted pool at that p is realized (given the sample size, per its predicted mass);
(iii) the realized parameter tuples lie in the sealed cones. This gate discriminates:
a missing menu entry (completeness failure) or a stray realized shape kills the note.

## 4. NOTE [3] RESUM — the depth resummation into rational functions of q

**The algebraic form (identified).** NOT a general generating-function fixpoint: a
FINITE TRIANGULAR LINEAR system over ℚ(q), indexed by cluster size e ≤ n (with
base-change substitutions q ↦ q^δ for residue degree δ), exactly the form the numeric
engine already computes (`verification/om_density_engine.py`, BB3_infinity §4.1):

  (R_e)   β_e = q^{−e(e−1)/2} · FULLMONIC(e)[β_e] + SHALLOW_e            (e = 1, …, n)

where β_e : {types of degree e} → ℚ(q) is the single-cluster type law; SHALLOW_e
collects the strata whose root read decides or branches (coefficients: universal
polynomials in q from MENU shapes + L3 counts); FULLMONIC(e) is LINEAR in the unknown
β_e (the e-fold-at-one-point self-loop leg) with knowns β_m(q^δ), m < e — triangular in
e, so solvable bottom-up; the pivot is 1 − w(e) ≠ 0 (BB3_infinity (⋆⋆)). The n = 2
instance is W6's geometric series (β₂ denominator q²+q+1 pattern; `msW_eighth_le` is
its p = 2 inequality shadow). Then R_σ := the σ-component of the full-space assembly
of the β_e over root residual shapes (the L3 Gauss/necklace layer).

**Key definitions.** Per-shape weight w(S) ∈ ℚ(q)-monomials: by MENU M4 the fresh-volume
exponent is affine in the shape's ℕ-parameters, so the sum over one ladder/tower
direction is a geometric series with ratio q^{−(positive weight)}; per-shape VALUE count:
C_S(q) := the universal polynomial (Claim 4.3 + D4R.3's torus lemma at depth).

**Load-bearing lemmas.**
- **RS.1 (the aggregation identity).** For each type σ: Σ_{complete realizable H of
  type σ} mass(H) — an absolutely convergent positive series (bound: EXHAUST's
  geometric depth tail + M4's height tails) — equals, after grouping by MENU shape and
  resumming each parameter cone, the σ-component of the solution of (R_e). *Sketch:*
  Theorem C gives mass(H) = ∏ vol(E_fresh); group by shape (MENU M5: nothing is
  missed); per shape, Fubini the cone sum (absolute convergence justifies ALL
  rearrangements — Thm 4.1(i) of the decomposition note, now unconditional via [5]);
  per-cone sums are products of geometric series (M4 affine exponents); the self-loop
  directions are exactly the β_e-recursion legs (a depth-k chain at cluster size e =
  k-fold composition of the same linear operator: the geometric FIXPOINT is the
  triangular solve, not a new sum).
- **RS.2 (coefficient p-independence).** Every coefficient of (R_e) is one fixed
  element of ℚ(q): shapes are p-independent (MENU), value counts are universal
  polynomials in the pool sizes Q = q^w (L3 + torus lemma — including at wild p, where
  per-shape emptiness is the polynomial vanishing, W1's pool-size effect), exponents
  are shape arithmetic. NO per-p import: p enters only at evaluation q = p.
- **RS.3 (solvability + uniqueness).** The system is triangular in e with pivots
  1 − q^{−e(e−1)/2}·(unit-leg coefficient) ≠ 0 in ℚ(q) and nonvanishing at every
  q = p ≥ 2 (each pivot is 1 − (positive mass < 1) at every evaluation — the same
  positivity that makes the series converge). Solution: R_σ ∈ ℚ(q), one per σ.
- **RS.4 (checksum).** Σ_σ R_σ = 1 identically in q. *Sketch:* the identity holds for
  the series at every p (total mass 1 minus zero undecided — [5]); a rational function
  agreeing with 1 at infinitely many q is 1. (Doubles as the note's cheapest sanity
  invariant at every intermediate layer.)
- **RS.5 (engine agreement).** The solved R_σ coincide with `alpha_full(n)[σ]` of the
  engine for n = 2, 3, 4, 5 (symbolic identity, not numerics) — the decomposition
  note's Thm 4.5 regrouping claim, now proved rather than conditional.

**Kernels (derivation-grade — the two biggest of the campaign):**
1. **The aggregation identity RS.1**: the regrouping from "sum over histories" to "the
   triangular system" — where n = 2 intuition most likely mismatches general n. The
   fresh derivation must handle: multi-side reads (the strictly-decreasing-slope cone
   and the gap substitution `_sum_by_gaps`), the conditional-on-ancestors chain (via
   C.1.5 stepwise, NOT via any independence assumption), and the base-changed
   sub-cluster laws β_m(q^δ) appearing when a residual factor has degree δ > 1
   (JOINT-D1's q ↦ q^w clause, now through Theorem C).
2. **The depth-leg linearity**: that a self-loop step multiplies the cluster law by a
   FIXED ℚ(q)-factor independent of the loop's own depth position — the general-n
   analogue of the n = 2 per-step ratio 1/(q²+q+1). This is M4's affine exponents +
   D4R.3 at the loop node; a wrong anchor-exponent (Case-J territory, a > 0) would
   silently corrupt every deep coefficient — derive with the Case-J exponents inline.

**Sealed gate RESUM-n3 (the headline gate — the first general-n formula).** Solve (R_e)
for n = 3 symbolically. Seal BEFORE any census: the FIVE rational functions R_σ, σ ∈
{(1,1)³, (1,1)+(1,2), (1,3), (1,1)+(2,1), (3,1)}, their values at p = 2, 3 (both wild),
5, 7 (tame controls), and the checksum. Census: ~10⁶–10⁷ monic cubics per prime with
the PARI `factorpadic` oracle (`verification/quartic_oracle.py` pattern) for ground-truth
types; PASS = per-type frequencies match R_σ(p) within the sealed EXHAUST tail bound +
sampling σ-bands at all four primes, AND partial sums by depth reproduce the sealed
per-depth ledger at p = 2. Any exact-arithmetic mismatch beyond the sealed tolerance is
a structural failure (see §8 risk R1). Cross-check: RS.5's symbolic identity against
`om_density_engine.alpha_full(3)` and `reconcile_om_bcfg.py` moments.

## 5. NOTE [5] EXHAUST — the discriminant-tail tie-in (do before RESUM)

**What already stands (decomposition note §3, accepted):** Lemma 3.2 (still descending
at depth d ⟹ v_p(disc f) ≥ 2d — GMN theorem of the index, pins (P1)–(P3) verbatim in
`GMN_citations.md`), Lemma 3.3 (elementary tail: μ{v_p(disc) ≥ D} ≤
(n−1)·p^{−⌈(D−n·v_p(n))/(n−1)⌉}), Cor 3.4 (Desc_d envelope, geometric in d). Pointwise
depth ⟹ disc; NO per-depth identities (the SELFLOOP wall stays sidestepped).

**What the tie-in must add (the note's entire content — small but load-bearing):**
- **X.1 (the move–event dictionary).** Every non-root node of a realizable MOVES
  history is a GMN descend/refinement event contributing ind_r ≥ 1 (the on-side lattice
  point (P3); recenterings ARE refinements and are counted — GMN Thm 4.18's "including
  refinements", pinned). Hence: joint stratum of a depth-d history ⊆ Desc_d ⊆
  {v_p(disc) ≥ 2d}. *Sketch:* per node, exhibit the (s+e, u+(d−1)h) on-side point in
  the node's OWN polygon under the (P1) on-or-below convention; the §B2-DEF stage
  dictionary (D.12 literature note) aligns the MOVES polygon with GMN's.
- **X.2 (undecided-at-level ⊆ deep-or-tail).** μ(Undec(N)) is bounded by the depth-d
  envelope + the per-shape height tails beyond threshold N (MENU M4 exponents): the
  general-n replacement for 3.4′(a), giving an EXPLICIT env(N) → 0 with named constants
  (form: env(N) ≤ c₁(n)·p^{−c₂(n)·N} after balancing d against N). This is what
  SQUEEZE and the RESUM-n3 gate tolerance consume.
- **X.3 (termination a.e. + N-stability restated).** μ(non-terminating) = 0; every
  terminating f is decided at its finite threshold; the stratum series per σ sums the
  full type density. (3.2 + 3.3 + Thm 2.1, quoted — no new content, restated in MOVES
  vocabulary so [3]/[4] can cite one place.)

**Kernels:** X.1's per-species event accounting — the one place a MOVES-node species
could fail to be a GMN event is the recentering with unchanged polygon data (improvement
steps of zero index gain); the derivation must either show ind_r ≥ 1 for the recenterings
MOVES actually records, or bound the number of zero-gain recenterings between genuine
events (L5fix Invariant 2's different budget). Treat as derivation-grade: this exact
subtlety (what counts as an "event") produced the (P1) convention hunt.

**Sealed gate EXHAUST-n3.** Seal: (i) the pointwise inclusion — on 10⁶ cubics at
p = 2 and p = 3, every f still descending at depth d has v_p(disc f) ≥ 2d (0 violations
tolerated); (ii) the (3b) constant at D = 2…8 vs exact counts; (iii) X.2's env(N) at
N = 4…10 vs the measured undecided mass, both primes. A single pointwise violation in
(i) is adjudicated against the dictionary X.1, not patched.

## 6. NOTE [4] SQUEEZE — the two-sided general-n bound, and THEOREM U

**The n = 2 pattern to generalize (W6):** (U) decided_σ(N) ≤ (value)·p^{2N} via the
fixpoint inequality `msW_eighth_le`, plus decided_σ(N) ≥ (value − env(N))·p^{2N} via the
box partition (each OTHER type's (U) + undecided envelope). Generalization:

- **SQ.1 (budgeted covering).** Every f in the level-N box is in exactly one of:
  (a) the stratum of one complete realizable history with threshold ≤ N (decided), or
  (b) Undec(N). *Sketch:* the classifier is deterministic and total; MENU M5 says its
  histories have menu shapes; this is `cluster_covering` at general n — strong induction
  on the remaining degree budget, the decision tree of the decomposition note 3.4′(a).
- **SQ.2 (the fixpoint upper bound — the (U) analogue).** For every N and σ:
  decided_σ(N) ≤ R_σ(p)·p^{nN}. *Sketch:* the depth-≤D, height-≤H partial sums of
  RS.1's series are ≤ the full sum (positive terms), and the finite-N decided set is
  covered by strata of finite partial-sum families (SQ.1); the fixpoint SOLUTION
  dominates every partial sum because the iteration map is monotone with positive
  coefficients — the general-n `msW_eighth_le`. NOTE: needs R_σ(p) ≥ 0 and pivot
  positivity at q = p (RS.3), not just formal solvability.
- **SQ.3 (the lower bound).** decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN}: box partition
  p^{nN} = Σ_τ decided_τ(N) + undec(N), apply SQ.2 to every τ ≠ σ, RS.4's checksum,
  and X.2's envelope.
- **SQ.4 = THEOREM U.** ρ_σ := lim decided_σ(N)/p^{nN} exists and equals R_σ(p) for
  every p; R_σ ∈ ℚ(q) is the p-independent solution of (R_e); Σ_σ R_σ = 1. Assembled
  from SQ.2 + SQ.3 + X.2. State with the honest normalization sentence (monic-box
  density; projective/palindromy OUT OF SCOPE per the standing directive).

**Kernels:** SQ.2's monotone-fixpoint domination at general n — at n = 2 this was a
hand geometric estimate; at general n it must be an induction over the triangular
system (dominate β_1-legs first, then β_2 given β_1, …), and the mixed legs β_m(q^δ)
need the induction hypothesis at BASE-CHANGED arguments: derive freshly, this ordering
is where a circularity could hide.

**Sealed gate SQUEEZE-n3.** Seal, at p = 2 and p = 3, for N = 4, 6, 8: the exact
integers ⌈(R_σ(p) − env(N))·p^{3N}⌉ ≤ decided_σ(N) ≤ ⌊R_σ(p)·p^{3N}⌋ for all five σ
(upper bound must hold EXACTLY — any single-f overshoot falsifies SQ.2), against an
exhaustive or stratified-exact census. Plus the checksum row at each N.

## 7. Verification protocol (the dual standard, now in force)

Per note, in order; no step may be skipped, no note trusted early:
1. **Draft** in the MOVES ledger style (self-contained displays, explicit scope
   clauses, evidence perimeter section). Kernels get FRESH-CONTEXT derivations first
   (separate C10B/C15-style notes, `<KERNEL>_DERIVATION_<date>.md`), then transfer.
2. **Dual adversarial verification — BOTH verifiers, every pass:** (a) Codex
   (`codex exec`, fresh context, quote-and-classify: critical error vs justification
   gap, fix nothing); (b) a fresh-Fable verifier subagent under the identical charge.
   The two reports are adjudicated jointly; disagreement between verifiers is itself
   a finding to resolve, not average away.
3. **Acceptance = two consecutive CLEAN passes from BOTH verifiers on identical text**
   (the §B2-DEF/§C standard). Pass records appended verbatim to the ledger.
4. **Sealed gates BEFORE trust:** the note's gate predictions are written and committed
   (numbers, exact counts, tolerance provenance) BEFORE the census code runs — the
   Case-K discipline: a FAIL is adjudicated on record (prediction-derivation error vs
   theory error), then RE-SEALED fresh; never silently re-run. One gate per new formula
   layer: D4-n3, MENU-n3, EXHAUST-n3, RESUM-n3, SQUEEZE-n3 (§§2–6). Gate scripts live
   in `verification/`, predictions in `verification/*_SEALED_PREDICTIONS_<date>.md`.
5. **Update `docs/PROJECT_STATE.md` + the MOVES ledger** at every acceptance
   (update-then-act); axiom changes (none planned — X.1 cites the already-pinned GMN
   material) would additionally require the semantic-guardian triple test.
6. Check `codex-limits` before each heavy verification round; adversarial verification
   is the LAST Codex use to cut.

## 8. Honest risk register (where this could structurally fail, and what would show it)

- **R1 — p-dependence that does not cancel (the theorem-killer).** If some wild-only
  shape family's aggregated mass at p ≤ n genuinely differs from the ℚ(q) value —
  i.e. RS.2 fails because a value count is NOT a universal polynomial in q (e.g. a
  depth-node pool constrained by (HV) to a count depending on the specific transported
  vertex value, breaking D4R.3 at some μ ≥ 2 or a > 0 configuration) — the whole
  approach (and possibly the theorem's monic form) fails. DEMONSTRATED BY: an exact-
  arithmetic RESUM-n3 gate failure at a wild prime that survives adjudication (no
  prediction-derivation error found) AND a minimal two-shape census isolating the
  non-polynomial count. This is the directive's "conclusive obstruction" test.
- **R2 — the aggregation is not a finite triangular system.** Deep class-3 conditioning
  could couple shapes so that the self-loop legs are not position-independent (kernel 2
  of §4 fails): the system would need infinitely many unknowns. DEMONSTRATED BY: two
  Theorem-C instances, same shape, different loop positions, with provably different
  per-step ℚ(q) ratios. FALLBACK: none within this architecture — this would force a
  genuinely new resummation idea (record as the structural wall if hit).
- **R3 — menu completeness failure (M5).** A realized history species outside the
  retained vocabulary (e.g. a recentering at e_read ≥ 2 that §B2-DEF's accepted
  perimeter does not cover, or an order-r move TRANS does not construct). DEMONSTRATED
  BY: a stray shape in the MENU-n3 census. NOTE: n = 3 may not exercise every deep
  species; if MENU-n3 passes but a species-coverage argument (M5) resists proof, add a
  targeted n = 4 or depth-3 census before trusting M5 (the D.12 level-3 gate, promoted
  from optional).
- **R4 — the recentering event-count gap (X.1).** If zero-index-gain recenterings can
  repeat unboundedly between genuine descend events, depth ⇏ disc for MOVES depth and
  the envelope fails. DEMONSTRATED BY: an EXHAUST-n3(i) pointwise violation, or the
  X.1 derivation finding a legal infinite improvement chain (L5fix Invariant 2 should
  forbid it — if it does not, that is a real hole in the termination story too).
- **R5 — fixpoint domination circularity (SQ.2).** The monotone-iteration bound could
  secretly assume the value it proves at base-changed arguments β_m(q^δ). DEMONSTRATED
  BY: the kernel derivation failing to find a well-founded induction order, or a
  SQUEEZE-n3 upper-bound overshoot by even one f. FALLBACK: a two-sided finite-window
  version (window K partial systems, monotone in K — the W3→W6 route) at the cost of a
  longer note.
- **R6 — silent scope debt from accepted inputs.** §C covers recenterings at
  e_read = 1 and any-(e, h, g, μ, a) increments; levels ≥ 3 of the tower rest on proofs
  alone (D.12). The assembly inherits these perimeters; MENU-n3/RESUM-n3 gates at
  p = 2, 3 exercise order-2 content only lightly. MITIGATION: the gates' shape logs
  must RECORD which species/levels were actually exercised (an unexercised menu row is
  listed in each note's evidence perimeter as proofs-only, the D.12 convention).
- **R7 — normalization mismatch at the finish.** Theorem U is a MONIC-box density;
  the paper's headline is weight-normalized projective with palindromy — OUT OF SCOPE
  by the standing directive (2026-07-22). The capstone must state this boundary
  explicitly to avoid a false "full theorem" claim in PROJECT_STATE.

## 9. Effort map (for scheduling, not for skipping)

[1] D4-R: 1 unit (mostly restatement + one kernel). [2] MENU: 2 units (M4 kernel is
real arithmetic). [5] EXHAUST: 1 unit (one kernel, one gate). [3] RESUM: 3–4 units
(two campaign-scale kernels + the headline gate). [4] SQUEEZE: 2 units. Verification
multiplies each by the usual ~2× (the §C precedent: 13 passes). Gates are cheap
(CPU-only, `verification/` patterns exist); seal discipline is the cost.
