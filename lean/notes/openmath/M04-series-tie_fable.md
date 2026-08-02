# M04-series-tie — attempt (Fable, 2026-07-31)

Target row (normative Lean form, `MovesU/BridgeKernels.lean:223`):

```lean
series_tie : ∀ σ : SplittingType n,
    F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
```

## 0. Results in this note

* **Theorem 1 + Corollary 1.1 (PROVED):** at the interface level, given only the
  interface law `mem_slice_iff` (plus, for 1.1, the sibling seam row
  `count_tie`), the row is EQUIVALENT to the limiting-density identity
  (D_σ): lim_{N→∞} decided_σ(N)/p^{nN} = Rval(vmap σ)(p),
  with the limit existing unconditionally as a nondecreasing limit, and the
  finiteness clause free.
* **Theorem 2 (PROVED, relative to the named sibling rows):** the σ-SUMMED form
  of the row is DERIVABLE from `count_tie` + `env_tendsto` + the chain laws;
  the row's genuine content is exactly the per-σ refinement (|Sigmas| − 1 real
  identities per prime), and all-but-one σ implies the last.
* **Finding F1 (numeric certificate, decisive):** the as-built n = 2 chain
  instance (`n2Chain`) is incompatible with the row at any pairing whose fiber
  masses carry the true ℤ_p densities: the device Rval triple has a zero entry
  and two distinct entries, while the true triple is (p/(2(p+1)), p/(2(p+1)),
  1/(p+1)) — two equal positive entries, no zero. At p = 2: (1/3,1/3,1/3) vs
  (4/7, 3/7, 0). The n = 2 discharge therefore requires the S-area's REAL n = 2
  pack; the device chain is an interface inhabitant only. (Its values ARE
  internally coherent as a 1-state geometric resummation — verified, §4.)
* **Theorem 4 (REDUCTION, glue proved):** at the intended instantiation the row
  follows from four named open kernels (K1 per-tree product formula
  TREE-EXP/(SIB)/(JC-multi)/CUT-WD; K2 spectral escape E0; K3 value-correctness
  of the symbolic tables; K4 mass semantics — shared with M02/count_tie) via an
  abstract resummation core (Lemmas 3.1–3.3: least-fixed-point = tree series;
  Bekić triangular decomposition; Neumann/Cramer under ρ < 1; shallow-cut
  Tonelli), which is PROVED here self-contained. The core is known mathematics
  (branching processes / algebraic series); the instantiated row is claimed-new
  and NOT literature-axiom-eligible.

Nothing below asserts the row itself. Verdict line and numeric tests at the end.

## 1. Logical status of the row

`series_tie` is a field of the Prop structures `BridgeKernels`/`SolveSeam`; at
the abstract parameters nothing is provable or refutable — the structures are
carried hypotheses. The mathematical obligation is at the final wiring: X, F,
seam bound to the built classifier/fiber family (`bridgeFibers` over the pinned
models; designer data `bridgePol`/`bridgeTm` still sorried), C bound to a per-n
real `UCarriers` pack. All statements below are therefore either (i)
interface-level equivalences valid for EVERY instantiation, or (ii) statements
about the intended/as-built instances, flagged as such.

## 2. Theorem 1 — the slice-limit form (proved; interface-level)

**Theorem 1.** For any `F : FiberSeries n p X` and any σ,
`F.seriesSum σ = ⨆_{N∈ℕ} Σ_{T ∈ F.thrSlice σ N} F.mass σ T`,
and N ↦ Σ_{T ∈ thrSlice σ N} mass is nondecreasing (so the ⨆ is a limit).

*Proof.* Monotonicity: N ≤ N′ gives thrSlice σ N ⊆ thrSlice σ N′ by
`mem_slice_iff` (thr T ≤ N ≤ N′), and sums of [0,∞]-terms grow with the finite
index set. In ℝ≥0∞, `∑′ T, mass T` is the supremum of finite partial sums
(`ENNReal.tsum_eq_iSup_sum`). (≥): each slice is a finite subset, so each slice
sum is ≤ ∑′. (≤): a finite A ⊆ Tree σ satisfies A ⊆ thrSlice σ N_A with
N_A := max_{T∈A} thr T (A = ∅ trivial) by `mem_slice_iff`; hence
Σ_A ≤ Σ_{thrSlice σ N_A} ≤ ⨆_N. Take ⨆ over A. ∎

Only the interface law `mem_slice_iff` is used — no open row.

**Corollary 1.1.** Assume the sibling seam row `count_tie` (equivalently its
proved consequence `TreeSeam.finiteness_stack`: decided_σ(N) = p^{nN} ·
Σ_{thrSlice σ N} mass). Then for every N,
Σ_{T ∈ thrSlice σ N} mass = decided_σ(N)/p^{nN} in ℝ≥0∞ (division legitimate:
0 < p^{nN} < ∞), hence by Theorem 1

> seriesSum σ = lim_{N→∞} decided_σ(N)·p^{−nN}  (nondecreasing limit),

and since each term is ≤ 1, seriesSum σ ≤ 1 < ∞ — the finiteness clause of
`SolveSeam.solve_stack` is free given `count_tie`. Consequently, GIVEN
`count_tie`, the row `series_tie` is **equivalent** to

> **(D_σ)**  lim_{N→∞} decided_σ(N)/p^{nN} = Rval(vmap σ)(p)   (in ℝ, both
> sides in [0,1]),

the statement "the classifier's limiting decided-σ density equals the measured
chain value". ∎

*Cross-check (independent of count_tie):* the monotonicity of
decided_σ(N)/p^{nN} also follows from the interface law `canonical_stable`
alone — each level-N decided-σ class lifts to exactly p^{n(N′−N)} level-N′
classes, all decided σ by stability — a consistency constraint between
`count_tie` and the classifier interface, and an independently testable
prediction (test T1).

## 3. Theorem 2 — the σ-sum is forced; the per-σ refinement is the content

**Theorem 2.** Assume `count_tie` and `env_tendsto` (env(N) :=
undec(N)/p^{nN} → 0). Then
(i) Σ_{σ : SplittingType n} seriesSum σ = 1 = Σ_σ ofReal(Rval(vmap σ)(p));
(ii) if `series_tie` holds at every σ except possibly one σ*, it holds at σ*.

*Proof.* (a) At each level N the verdict map f ↦ canonical N f partitions the
p^{nN}-element box into the σ-fibers and the none-fiber:
Σ_σ decided_σ(N) + undec(N) = p^{nN} (SplittingType n is a Fintype — unit U0b;
pure counting). (b) Divide by p^{nN}: Σ_σ dmass_σ(N) = 1 − env(N). (c) Let
N → ∞: each dmass_σ(N) ↑ seriesSum σ (Cor 1.1), the σ-index is finite, so the
finite sum of nondecreasing limits converges to Σ_σ seriesSum σ = 1; all terms
≤ 1. (d) Chain side: Σ_σ Rval(vmap σ)(p) = Σ_{s ∈ Sigmas} Rval s p
(`sum_vmap_eq_sum_Sigmas`, proved) = decidedTotal p (`rs1_equates`) = 1
(`x3_total`); each term ∈ [0,1] (`r_bdd` at (p:ℚ) ∈ Pools via
`prime_sub`/`prime_base`), so ofReal is additive across the sum. (e) For (ii)
subtract the equal finite totals. ∎

*Reading.* The σ-summed tie costs nothing beyond the sibling rows; `series_tie`
is exactly the per-σ refinement — at n = 2 it pins TWO extra real identities
per prime beyond the derivable total. No derivation of the per-σ form from the
other ledger rows is possible in general: the other rows constrain only totals
and interface shapes, and Rval's per-σ values enter no other row except through
`rsh_interp` (which ties Rval to Rsh, not to the classifier). I probed for a
countermodel-style independence argument and record it as an open (but
low-value) exercise: exhibit two chains, both satisfying every RS4Chain law,
whose Rval differ by a transposition of two equal-degree verdict multisets —
blocked only by the labor of re-certifying `rsh_interp` for the transposed Rsh.

## 4. Finding F1 — the as-built n = 2 pairing obstruction (with certificate)

The only existing chain instance is `n2Chain` (`MovesS/N2Sigmas.lean`):
Rval({(1,2)}) = (q+1)/(q²+q+1), Rval({(1,1),(1,1)}) = q²/(q²+q+1),
Rval({(2,1)}) = 0.

The project's own validated ground truth (`verification/padic_types.py`,
`monic_quad_pred`, oracle-validated) for the TRUE monic quadratic splitting
densities over ℤ_p: ρ_split = p/(2(p+1)), ρ_inert = p/(2(p+1)),
ρ_ram = 1/(p+1).

**Proposition F1.** Fix n = 2 and any prime p. There is NO pairing
(X, F, seam) satisfying jointly: `count_tie`, `env_tendsto`, `series_tie` at
the chain `n2Chain`, AND the truth identification (TI): lim_N
decided_σ(N)/p^{2N} = ρ_σ(p) for each σ (the identity the soundness/fidelity
rows vp_sound + the ℤ_p bridge + exhaustiveness are designed to force at the
real classifier).

*Proof.* Cor 1.1 + (TI) give seriesSum σ = ρ_σ(p) > 0 for all three σ; but
`series_tie` at `n2Chain` forces seriesSum({(2,1)}-type) =
ofReal(0) = 0. Contradiction. (In fact no bijective re-assignment of the three
verdict multisets helps: the true triple has two equal positive entries, the
device triple has a zero and two distinct entries.) ∎

Numeric certificate (computed, exact rationals):

| p | device (split, inert, ram) | true (split, inert, ram) |
|---|---------------------------|--------------------------|
| 2 | 4/7, 3/7, 0               | 1/3, 1/3, 1/3            |
| 3 | 9/13, 4/13, 0             | 3/8, 3/8, 1/4            |
| 5 | 25/31, 6/31, 0            | 5/12, 5/12, 1/6          |
| 7 | 49/57, 8/57, 0            | 7/16, 7/16, 1/8          |

**Consequences.** (1) The n = 2 discharge of `series_tie` requires the real
n = 2 chain (Rval = ρ); `n2Chain` is an interface witness only — consistent
with its own docstring ("the two note-displayed solve evaluations") and with
`BridgeKernels.lean`'s header gating IB-C6 on the S-area's real n = 2 pack.
This should be recorded as a wiring fence: the final n = 2 wiring MUST NOT bind
C to `n2Chain` while binding F to true-mass fibers. (2) If instead the wiring
pairs the device chain with device fiber masses (designer data), the row
becomes a device-level identity — provable but carrying no ℤ_p content; the
honesty ledger should say which pairing the capstone claims.

**Device coherence (verified).** The device values ARE the exit values of a
single-state grammar with continue-weight q^{−3} and exit weights (1 − 1/q)
and (q² − 1)/q³:

> q²/(q²+q+1) = (1 − q^{−1})/(1 − q^{−3}),  (q+1)/(q²+q+1) = ((q²−1)/q³)/(1 − q^{−3}),

verified at 7 exact rational points q ∈ {2,3,5,7,11,13,101} (both sides are
ratios of polynomials of degree ≤ 3, so 7 points force the identities; also
checksum device-split + device-inert = 1 and 2ρ_split + ρ_ram = 1 verified).
So a device-side discharge of the row is exactly a geometric-series summation
— an instance of Lemma 3.2 below with a 1×1 matrix A = (q₀^{−3}).

## 5. The reduction at the intended instantiation (Theorem 4)

### 5.1 The abstract object: a triangular weighted verdict grammar

Data 𝒢: block sizes e ∈ {1,…,n}; finite state sets S_e; a finite verdict
alphabet V with degrees ≥ 1; per state τ ∈ S_e a finite outcome roster O(τ),
each outcome o carrying, per pool q₀ (pools = a set of positive reals closed
under q₀ ↦ q₀^δ), a numeric weight w_o(q₀) ∈ [0,∞), and a route:
* continue(τ′ ∈ S_e) — one child, same block;
* exit(v(o)) — leaf with verdict multiset v(o) over V;
* split((e_j, τ_j, δ_j)_{j≤m}; halted verdicts) — children in strictly
  smaller blocks e_j < e, each tagged δ_j ∈ ℕ+, plus verdict-halted leaf
  members.

Derivations from (e,τ) at pool q₀: finite trees of outcome choices; each node
is priced at the pool obtained by MULTIPLYING the δ tags along its root path
(matching the project's absolute-δ convention and `consumedDeltas`'
multiplicative closure); weight(D) := ∏_nodes w; verdict(D) := ⊎ leaf verdicts.
The set of derivations is countable (finite trees over finite rosters). Define

> B_{e,τ}(σ′)(q₀) := Σ_{D from (e,τ) at q₀, verdict(D) = σ′} weight(D) ∈ [0,∞].

### 5.2 Lemma 3.1 — tree series = least fixed point (proved)

**Lemma 3.1.** B is the LEAST solution over [0,∞] of the system (all (e,τ),
σ′, pools q₀):

x_{e,τ}(σ′)(q₀) = Σ_{o cont→τ′} w_o(q₀)·x_{e,τ′}(σ′)(q₀)
 + Σ_{o exit, v(o)=σ′} w_o(q₀)
 + Σ_{o split} w_o(q₀)·Σ_{σ′ = halt(o) ⊎ ⊎_j σ_j} ∏_j x_{e_j,τ_j}(σ_j)(q₀^{δ_j}).

*Proof.* Let Φ be the right side, a self-map of the complete lattice
L = [0,∞]^{(states)×(verdict multisets)×(pool closure)}. Φ is monotone and
ω-continuous: it is a composition of +, ·, and countable sums, and in [0,∞]
both + and · commute with suprema of nondecreasing sequences (the 0·∞ corner
is safe: if the constant factor is 0, both sides are 0). By Kleene,
lfp Φ = ⨆_h Φ^h(0). Let B^{(h)} := the sum restricted to derivations of height
≤ h. Then B^{(0)} = 0 and B^{(h+1)} = Φ(B^{(h)}): a derivation of height
≤ h+1 is uniquely (root outcome, children derivations of height ≤ h), its
weight the product; regrouping the [0,∞]-valued sum along this bijection and
factoring products of sums across children is Tonelli for countable families
in [0,∞]. Every derivation has finite height, and any finite set of
derivations lies in one height class, so ⨆_h B^{(h)} = B (Theorem-1-style
supremum argument). Hence B = lfp Φ; any solution y dominates every iterate,
hence B. ∎

### 5.3 Lemma 3.2 — linear resummation under spectral escape (proved)

**Lemma 3.2.** Fix e and a pool q₀. Suppose all smaller-block values entering
block e's split outcomes at q₀ are finite, so the exit-plus-split vector
c(σ′) ∈ [0,∞)^{S_e} is finite entrywise (finite rosters; finitely many
decompositions of a bounded multiset). Let A ∈ [0,∞)^{S_e×S_e},
A_{τ,τ′} := Σ_{o cont τ→τ′} w_o(q₀). Note the continue route does not touch
σ′, so the block-e subsystem decouples per σ′ with the COMMON matrix A:
x = A x + c(σ′). Then:
(i) B's block-e slice is the least [0,∞]-solution, and equals
⨆_K Σ_{k<K} A^k c = (Σ_{k≥0} A^k) c (Kleene iterates of the affine map);
(ii) if A^k·𝟙 → 0 (⟺ ρ(A) < 1 for a finite nonnegative matrix: ρ(A)^k =
ρ(A^k) ≤ max-row-sum(A^k) → 0), then Σ_k A^k = (I − A)^{−1} (Neumann),
entrywise finite, and the slice is the UNIQUE real solution
(I − A)^{−1} c(σ′) — in particular det(I − A) ≠ 0.
The passage from the FULL system's least solution to the block subsystem is
Bekić's modular-fixpoint lemma (triangularity: split legs reference strictly
smaller blocks only, so lfp = bottom-up composition of per-block lfps). ∎

### 5.4 Lemma 3.3 — the shallow cut (proved, given the cut bijection)

**Lemma 3.3.** Suppose a countable shape family {Ŝ} with numeric weights
W(Ŝ)(p) ∈ [0,∞), entrance lists ((e_i,τ_i,δ_i))_{i≤k(Ŝ)}, halted verdicts
σ₀(Ŝ), and a WEIGHT-PRESERVING BIJECTION
{complete trees T of type σ} ≅ ⨆_Ŝ {(D_i)_{i≤k(Ŝ)} : σ₀(Ŝ) ⊎ ⊎_i verdict(D_i)
= σ}, under which μ(fiber T) = W(Ŝ)·∏_i weight(D_i). Then
Σ_{T type σ} μ(fiber T) = Σ_Ŝ W(Ŝ)(p)·Σ_{σ = σ₀(Ŝ) ⊎ ⊎_i σ_i}
∏_i B_{e_i,τ_i}(σ_i)(p^{δ_i}).
*Proof.* Regroup along the bijection; for fixed Ŝ group tuples by their
verdict tuple and factor (Tonelli in [0,∞]). ∎

### 5.5 Theorem 4 — the reduction (glue proved; kernels named)

*Scope pin [(K1-CANON) discharge, ed-1(c), 2026-08-02]:* throughout this
subsection "canonical tree" and the type-σ tree corpus denote (q-4)'s pinned
notion — complete finite realizable, ALL leaves (τ-irr)/(τ-hen), the
(q-3)/TREE-N scope (provenance of the pin: D-11 r4 pass-1 gap 5 / pass-2 gap 3;
discharge record `K1CANON_discharge_2026-08-02.md`; HDISCHARGE_H9 §3).

**Theorem 4.** Fix a prime p and the intended instantiation. `series_tie`
holds at every σ provided:

* **(K1) per-tree product + cut** [= TREE-EXP + (SIB) + (JC-multi) + CUT-WD;
  MOVES note §T.4/§S.2; ledger rows `sibjc` and the [3t] kernels]: each
  complete finite realizable canonical tree's (canonical tree := (q-4)'s
  pinned notion — complete finite realizable, ALL leaves (τ-irr)/(τ-hen), the
  (q-3)/TREE-N scope; at the wired instance the `bridgeTree` carrier, whose
  `MovesT.NsFree` clause equals this guard's MARK COMPONENT at realized trees
  [H9-U3/U5]) fiber mass factors as the
  grammar weight of its derivation, with outcome weights the MEASURED one-step
  conditional masses (`M.rowVal`, J, ι/W) at the composed pools, and the
  type-σ corpus decomposes along shallow shapes as in Lemma 3.3 with W(Ŝ)(p)
  the measured shallow-shape mass;
* **(K2) spectral escape** [= ESCAPE(E0), CL-1, §S.4]: at every consumed pool
  q₀ = p^δ (δ ∈ the multiplicative closure), the active one-step matrix
  A(q₀) satisfies A(q₀)^k·𝟙 → 0;
* **(K3) value correctness** [= (iv)-POLY/CL-6 + INIT-RAT + (J-RAT) +
  CL-17(ii) + CTS-M(ii-c); partly carried as `RatBurdens`' interpolation
  laws]: the numeric grammar weights equal the evaluations at the pools of the
  symbolic ℚ(q) entries K_e, b^{term}, J, W_Ŝ consumed by
  `blockSolve`/`Rsh`, with the active-subsystem agreement-after-cancellation
  read (AVAgree) at non-all-active pools;
* **(K4) mass semantics** [shared with M02]: `bridgeMass` T (the normalized
  level-L fiber count, L = max(thr T,1)) equals μ(fiber T) — level-exact
  cylinder reading; plus (ns-null) excluding infinite trees (closed at [3t]
  §T.2 per the note, not re-proved here).

*Proof.* K4 turns the LHS into Σ_{T type σ} μ(fiber T) (the sum over the SAME
pinned corpus — the carrier's type-σ trees). K1 + Lemma 3.3 turn it
into the shallow convolution of the numeric B's. Lemma 3.1 + Bekić + Lemma 3.2
with K2, by induction on the block size e (smaller blocks' consumed pools are
pool powers, covered by K2), give B_{e,·}(σ′)(q₀) = (I − A(q₀))^{−1} c(σ′)
with c built from evaluated smaller-block solves; K3 identifies this, again
inductively, with the evaluation at q₀ of `blockSolve` — the evaluation passes
through the finite sums/products by the ring-hom property of `evalAt` on the
regular subring (memberships supplied by K3/`wsh_ok`/`rsh_interp`), and
det(I − A) ≠ 0 comes from Lemma 3.2(ii) on the active part, with the inactive
part handled by K3's agreement clause. Assembling over shapes gives the
evaluation at p of `Rsh`(vmap σ); by `rsh_interp` (a carried chain law) that
is Rval(vmap σ)(p) ∈ [0,1] (`r_bdd`), so `ENNReal.ofReal` is faithful. ∎

**Honesty inventory.** K1–K3 are the project's own open kernels — they are WHY
the row is open; the reduction adds no new open content. What it contributes
beyond the note's §S.2 sketch: (a) Theorems 1–2's interface-level location of
the row's content (per-σ refinement of a derivable total; finiteness free);
(b) the precise lfp/Bekić/Neumann glue with proofs — including the
σ′-decoupling of the linear layer (the continue matrix is verdict-blind, so
ONE matrix serves all σ′ — this is what lets the ℚ(q) Cramer solve, a
per-σ′-vector with a common denominator det(1 − K_e), meet the numeric least
solution) and the uniqueness step; (c) the [0,∞] bookkeeping: no convergence
hypothesis is consumed anywhere before K2 enters.

**Open lemmas (explicit, in the project's sense).** OL-1 := K1 (per-tree
product; the note's TREE-EXP is proved GIVEN (SIB)+(JC-multi), which remain
open — rows `sibjc`); OL-2 := K2 (E0); OL-3 := K3 (the table-value burdens);
OL-4 := K4's level-exactness (M02's territory). A full proof of the row =
OL-1…OL-4 + Theorem 4.

## 6. Literature

* **The abstract core is known** (my Lemmas 3.1–3.3 are self-contained
  restatements with proofs; citations corroborative, labeled (b) new
  write-up of known results):
  - T. E. Harris, *The Theory of Branching Processes*, Springer 1963, Ch. II —
    extinction/exit probabilities of multitype processes as MINIMAL
    nonnegative roots of the fixed-point system.
  - K. Etessami, M. Yannakakis, *Recursive Markov chains, stochastic grammars,
    and monotone systems of nonlinear equations*, J. ACM 56(1), 2009 — the
    termination-probability vector of a recursive Markov chain/SCFG is the
    least nonnegative solution of its monotone polynomial system, reached by
    value iteration (their Theorem 3.1; statement match with Lemma 3.1's
    stochastic case).
  - W. Kuich, *Semirings and formal power series*, Handbook of Formal
    Languages vol. 1 ch. 9 — algebraic systems over continuous semirings:
    least solutions exist and equal the approximation supremum
    (Kleene–Schützenberger; [0,∞] is a continuous semiring).
  - H. Bekić, *Definable operations in general algebras* (1969; LNCS 177,
    1984) — the modular/triangular fixpoint decomposition (Lemma 3.2's
    block-by-block passage).
  - E. Seneta, *Non-negative Matrices and Markov Chains*, Springer — Neumann
    series and ρ < 1 for nonnegative matrices.
* **The instantiated row is claimed new** (label (c)): no publication states
  the identity for this project's classifier trees and chain carriers.
  Adjacent results, labeled precisely:
  - J. Denef, *The rationality of the Poincaré series associated to the p-adic
    points on a variety*, Invent. Math. 77 (1984) — PER-PRIME rationality of
    p-adic counting series by cell decomposition; no uniformity in p; no
    statement match.
  - M. Bhargava, J. Cremona, T. Fisher, S. Gajović, *The density of
    polynomials of degree n over ℤ_p having exactly r roots in ℚ_p*
    (arXiv:2101.09590; Proc. Lond. Math. Soc. 2022 — venue/year flagged for
    lookup): that coarser density (number of roots, not full splitting type)
    is a fixed rational function of p, uniform in p — the closest published
    uniformity statement; NOT a statement match with the row.
  - The repo's excluded self-citation 2212.00294 (out of scope per project
    goal #72).
  - I. Del Corso, R. Dvornicich (tame splitting uniformity) — used elsewhere
    in this project (retired axiom htameFE); not this row.
* **LITERATURE-AXIOM-ELIGIBLE: NO.** The row quantifies over project-internal
  carriers (the canonical-policy tree corpus, the chain's Rval); no citation
  matches its exact statement. Only the abstract core (Lemmas 3.1–3.3) could
  ever be cited in, and it is cheaper to prove than to axiomatize.

## 7. VERDICT and NUMERIC-TESTS

**VERDICT: REDUCED** — the row is equivalent (given the sibling row
`count_tie`) to the limiting-density identity (D_σ); its σ-sum is derivable
from the sibling rows (Theorem 2), so its content is the per-σ refinement; at
the intended instantiation it reduces to the four named open kernels K1–K4 via
the proved abstract resummation core (Lemmas 3.1–3.3 + Theorem 4); and the
as-built n = 2 device pairing is REFUTED as a discharge site (Proposition F1,
numeric certificate). Not literature-axiom-eligible.

### NUMERIC-TESTS

* **T1 (limit form at the real n = 2 chain; tests (D_σ) + monotonicity).**
  For p ∈ {2,3,5}, N up to (13, 8, 5) resp. (cap p^{2N} ≤ 10^8): enumerate all
  (b,c) ∈ (ℤ/p^N)², d := b² − 4c. Decision rule: v := v_p(d) if d ≠ 0 in
  ℤ/p^N else undecided; p odd: decided iff v < N — v odd ⟹ ramified, v even ⟹
  split iff unit part is a QR mod p, else inert; p = 2: decided iff
  v ≤ N − 3 — v odd ⟹ ramified, v even: unit part u mod 8 ∈ {1} split, {5}
  inert, {3,7} ramified. CONFIRMS if: each decided_σ(N)/p^{2N} is
  nondecreasing in N and → ρ_σ(p) ∈ {p/(2(p+1)), p/(2(p+1)), 1/(p+1)} with
  gap ≤ env(N) := 1 − Σ_σ dmass_σ(N), and env(N) = Θ(p^{−N}). REFUTES (D_σ)
  at the real chain if any σ-limit separates from ρ_σ(p) by more than env.
* **T2a (n = 3 value test, Monte-Carlo).** p ∈ {2,3,5}: sample 10^7 random
  monic cubics over ℤ_p (40 digits each), type via PARI `factorpadic`
  (cypari2) at precision 60 reading (e,f) per factor; compare frequencies to
  `padic_types.monic_cubic_pred(p)` (five types; e.g. at p = 2:
  4/93, 28/93, 24/93, 22/93, 15/93). Binomial 3σ ≈ 5·10^{−4}: decisive.
  CONFIRMS the limit identity's VALUES where the deep (wild) recursion
  genuinely engages; any type off by > 3σ REFUTES the engine/chain value.
* **T2b (n = 3 monotonicity/exact, small N).** p = 2, N ≤ 6 (2^{18} boxes):
  enumerate monic cubics mod 2^N, decide with the sound Krasner-style guard
  2·v_2(disc) + 1 ≤ N; CONFIRM monotone growth of dmass_σ(N) and env′ decay
  ~ p^{−N/2}. (Value convergence too slow here — that is T2a's job.)
* **T3 (device separation; RUN, PASSED).** Exact rationals, p ∈ {2,3,5,7}:
  device triple (q²,q+1,0)/(q²+q+1) vs true (p/(2(p+1)), p/(2(p+1)),
  1/(p+1)) — no entry-wise match under any bijection (table in §4). Certifies
  Proposition F1's premise.
* **T4 (device resummation identities; RUN, PASSED).** Verified at q ∈
  {2,3,5,7,11,13,101} (7 points ≥ degree bound + 1): q²/(q²+q+1) =
  (1−q^{−1})/(1−q^{−3}); (q+1)/(q²+q+1) = ((q²−1)/q³)/(1−q^{−3}); both
  checksums = 1. Certifies §4's device-coherence remark.
* **T5 (E0 spectral probe, K2).** From `verification/om_density_engine.py`'s
  block recursion extract the same-size (self-loop) coupling at e = 2, 3 —
  the coefficient of the unknown β_e in (R), the q^{−e(e−1)/2}·(FULLMONIC
  linear part) — and evaluate at q₀ ∈ {2,3,4,5,8,9}: report all |entries| and
  the spectral radius of the active block. CONFIRMS K2 at probed pools if
  ρ < 1 (expect ρ ≤ q₀^{−1}); ρ ≥ 1 anywhere REFUTES E0 and kills the route.
* **T6 (Neumann-vs-Cramer mechanical, Lemma 3.2 orientation guard).** Random
  substochastic A (exact `Fraction` entries, sizes ≤ 6, row sums ≤ 7/8),
  random nonneg c: check Σ_{k<K} A^k c ↑, gap to the linear-solve value
  (I − A)^{−1}c bounded by ‖A‖_∞^K·‖(I−A)^{−1}c‖_∞, exact match of the limit.
  Guards row/column orientation for any future Lean formalization of the core.

Suggested placement: `verification/openmath/M04_series_tie_tests.py` (T1, T2b,
T3, T4, T6 pure Python/fractions; T2a and T5 need the cypari2/sympy env).

