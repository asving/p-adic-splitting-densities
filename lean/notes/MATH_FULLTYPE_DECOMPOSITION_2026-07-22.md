# MATH_FULLTYPE_DECOMPOSITION — the full decided per-type density as a convergent sum over terminating OM strata

**Date: 2026-07-22. Role: the math-first ground truth for Lean waves 4–6** (directive 2026-07-22:
math first → blueprint → implementation). This note decomposes the FULL per-type decided density
`ρ_dec(n, σ; p)` (monic counting normalization over ℤ_p) as a convergent sum over an explicitly
indexed tree of TERMINATING strata, and classifies every ingredient as
**[COUNT]** pure cylinder-counting (provable, no import), **[MONTES]** Montes-paper content
(axiomatizable under the standing faithfulness discipline, GMN pins per
`notes/GMN_citations.md`), or **[OPEN-Dk]** an explicit open lemma (honest `sorry`-analogue).
Claim-novelty labels per the workspace discipline: (a) known, (b) new proof/organization of known
content, (c) claimed new (in this project's context).

Established base, cited not re-derived: `docs/PROJECT_STATE.md` §2; the Wave 1–3 blueprints
(`notes/WILD_WAVE{1,2,3}_BLUEPRINT_2026-07-21.md`); the wall analysis
(`notes/SELFLOOP_GENERALK_WALL.md`, confronted in §3.6); `notes/BB3_infinity.md` (§4 recursion,
§8 GAP-1/GAP-2 ledger); `notes/HUMAN_PROOF.md` §§3–9; the engine
`verification/om_density_engine.py`; `LeanUrat/OM/Drainage.lean`.

---

## 0. The object and conventions

Fix a prime `p`, base `K = ℚ_p` (residue field `F_q`, `q = p`; every count below is a universal
polynomial identity, so the unramified-base generalization is the substitution `q ↦ q^δ` exactly as
in the engine's `beta_scaled` and HUMAN_PROOF L1(4) — used *internally* at residue points of degree
`δ > 1`, see §1). `monicBox(p,N,n)` = monic degree-`n` polynomials over `ℤ/p^N` (coefficient space
`(ℤ/p^N)^n`, its normalized count = Haar mass of the corresponding cylinder in ℤ_p^n).

> **Definition 0.1 (the target).** For a factorization type `σ` (multiset of `(e,f)`,
> `Σeᵢfᵢ = n`):
> ```
> ρ_dec(n, σ; p) := μ{ f ∈ ℤ_p[x] monic, deg n : the OM resolution of f terminates
>                                              and assigns type σ }            (0)
> ```
> with `μ` the normalized Haar (coefficient) measure. Equivalently (Theorem 3.5 below) the limit of
> normalized level-`N` decided counts — the shape the Lean capstones use (`countingDensity`,
> `OM/RealInstanceV2/W/W3`). Since non-termination has measure zero (Lemma 3.2 / Cor 4.19),
> `ρ_dec` IS the full monic type density `α(n,σ;p)` of `HUMAN_PROOF.md`.

Status marker of (0) itself: the *identification* "decided density = full type density" is exactly
what §3 proves (modulo the marked imports); until then the two must not be conflated (the repo's
current certified values are K-windowed decided sub-densities — PROJECT_STATE §2).

---

## 1. The stratum tree

The tree formalizes the classifier's read-history. Everything in this section is *definition* (finite
combinatorial data + residue-field values); no measure claims yet.

> **Definition 1.1 (read, root).** The **root read** of monic `f` is the factorization shape of
> `f̄ ∈ F_q[x]`: the set of distinct irreducible factors `ḡ_j` with degrees `δ_j` and
> multiplicities `m_j`, `Σ m_j δ_j = n`. Each `m_j = 1` factor is a **leaf** with
> `(e,f) = (1, δ_j)` [MONTES: Hensel + Cor 1.20 at `m=1`; measure-exactness is L1, proved-solid
> `HUMAN_PROOF §3`]. Each `m_j ≥ 2` factor opens a **cluster node** `(φ_j := the canonical lift of
> ḡ_j, m_j, δ_j)`.

> **Definition 1.2 (read, cluster node).** At a cluster node with key polynomial `φ` (monic, degree
> `m_φ`), current node field `F_r` (`Q_r := |F_r| = q^{δ·f_1⋯f_{r-1}}`), the read of `f` is:
> 1. the **φ-adic development** `f = Σ_i a_i(f) φ^i`, `deg a_i < m_φ` — for fixed `φ` the map
>    `f ↦ (a_i(f))` is a **linear, unipotent-triangular** bijection of coefficient space (division
>    by a fixed monic polynomial) [COUNT — elementary linear algebra];
> 2. the **principal Newton polygon** (lower hull) of `{(i, v_r(a_i))}` restricted to the node's
>    window: a list of sides `S = (slope −h/e in lowest terms, lattice length ℓ, degree
>    d_S = ℓ/e)`, strictly decreasing slopes [MONTES: Def 2.3/Def 1.1 for the order-`r`
>    normalization `v_r` (Def 2.5); at `r ≤ 1` this is the plain coefficient polygon, COUNT];
> 3. per side, the **residual polynomial** `R_S(f) ∈ F_r'[y]`, monic degree `d_S`, `R_S(0) ≠ 0`,
>    over `F_r' = F_r` extended by the side data [MONTES Def 2.21; at order ≤ 1 base field: COUNT,
>    the explicit digit read of `CellCard`/`CellMenu`], and its factorization shape
>    `R_S ~ ∏_k ψ_k^{μ_k}` (distinct monic irreducibles `ψ_k`, degrees `f_{ψ_k}`).
> 4. **Outcome per residual factor** `(ψ, μ)`:
>    - `μ = 1`: **leaf**, with `(e,f)` given by the order-`r` product law (§6) [MONTES Cor 1.20 /
>      Cor 3.8];
>    - `μ ≥ 2`: **descend** — open a child node with key `φ' := ` the canonical lift of `ψ`
>      composed into the tower. Two sub-cases, exactly as the task sheet demands:
>      * `deg ψ = 1`, `ψ = y − c̃`, integer slope `m` (so `e = 1`): the child read is the read of
>        the **literally recentered** polynomial `x ↦ x + ĉ p^m·(current frame)`, `ĉ` the canonical
>        (Teichmüller) lift of `c̃`. Recentering is a fixed unipotent-triangular affine bijection of
>        the coefficient space [COUNT]. This is the μ≥2 "self-loop-like" descent (Drainage's
>        `selfLoopCell` family and the engine's rescale branch live here).
>      * `deg ψ ≥ 2` (or `e ≥ 2` with `μ ≥ 2`): the child read is the `φ'`-adic development step
>        with `deg φ' = m_φ·e·f_ψ` [MONTES Thm 2.11/Def 2.12: existence + degree of the
>        representative; the development itself is again a fixed linear-triangular map once `φ'` is
>        fixed — COUNT]. The child node field is `F_{r+1} = F_r[y]/(ψ)`, `|F_{r+1}| = Q_r^{f_ψ}`
>      [MONTES §2.1 tower — fact (I)].
>
> **Canonical lifts.** All lifts (`φ_j`, `ĉ`, `φ'`) are made by a FIXED choice function (Teichmüller
> digits / minimal-support lifts). That the resulting reads compute the same leaves/(e,f) as any
> admissible-lift Montes run is lift-invariance [MONTES §2–3 admissible-representative invariance;
> exact GMN pin to be fixed at axiom-declaration time — flagged]. With canonical lifts, every read
> along the tree is a **fixed, f-independent** triangular coordinate change followed by digit
> inspections — the load-bearing structural observation of this note.

> **Definition 1.3 (stratum; terminating vs descending).** A **read-history** `s` is: a root-read
> outcome, and recursively, for every opened cluster node, a finite (possibly empty) sequence of
> cluster-read outcomes (Def 1.2 data: polygon, per-side residual shape, per-descend-factor the
> residual value `ψ` — value, not just degree). `S_s ⊆` box is the set of `f` realizing `s`.
> `s` is **TERMINATING** if every branch has ended in leaves (every residual factor everywhere has
> `μ = 1`, every opened node fully read); it is **DESCENDING (open)** if some child node is still
> unread. The **depth** `d(s)` = the number of descend events along its deepest branch.

> **Definition 1.4 (the index — finite data per node) [COUNT, (b)].** A stratum is a finite
> labelled tree; each node carries: the polygon (a finite list of pairs `(h_i, e_i, ℓ_i)` of
> bounded denominators `e ≤ n` but UNBOUNDED heights `h`), per side a residual shape (a partition
> of `d_S` into `(degree, multiplicity)` parts — finitely many, degrees ≤ n), per descend factor a
> residual value `ψ ∈ F_r'[y]` (finitely many per field). The tree is **countable**, and splits as
> ```
>   INDEX = SHAPE (p-independent: polygons + shapes + degree data)
>           × VALUES (p-dependent: the residual values ψ / c̃ per descend, and
>                     the residue points of the root read)                       (†)
> ```
> The SHAPE quotient is the grouping under which rationality is proved (§4); the VALUES fiber is
> what the per-shape choice-counts count. Unboundedness enters in exactly two ways: heights within
> a read (the H-ladders) and depth `d` (descend chains); both are resummed in §4.

*Boundary bookkeeping (needed for §3):* a read can fail only when a needed development coefficient
vanishes identically (`v = ∞`), i.e. `f(ĉ·frame) = 0` exactly or `φ' | f` exactly — for each fixed
node a proper Zariski-closed (hyperplane-type) condition, countably many over the tree. Call the
union `Z_∞`; `μ(Z_∞) = 0` [COUNT — countable union of measure-zero polynomial loci].

---

## 2. Cylinder counting per stratum

> **Theorem 2.1 (strata are cylinders) [COUNT, (b)].** Each read-history `s` determines
> `N₀(s) < ∞` (its threshold: the total number of base-`p` digits its reads inspect, ≈
> `Σ_reads (F_r-digit cost) ≤ Σ heights + depth-shifts`) such that `S_s` is a finite union of
> cylinders of level `N₀(s)`: membership of `f` depends only on `f mod p^{N₀(s)}`.
> *Proof sketch.* Induction along the tree. Each read is (fixed triangular bijection) ∘ (finitely
> many digit equalities/inequalities `v = h` / `v ≥ ⌈line⌉` and residual-digit values). A fixed
> triangular bijection of ℤ_p^n induces a bijection of `monicBox(p,N,n)` for every `N` (unipotent
> integral matrices + polynomial lower-order terms reduce mod `p^N`), so digit conditions on the
> transformed coordinates are digit conditions on the originals. ∎
> Consequence (**N-stability**): `#(S_s ∩ monicBox(p,N,n)) · p^{-nN}` is constant for
> `N ≥ N₀(s)`. [Lean instances at order ≤ 1: `StratumOrder1.stratumCount1` fibers;
> `normRamCountAt_levelConst` (`OM/WildMenuW3.lean`); small-`N` vanishing below threshold:
> `stratumCount_ramShapeAt_smallN`.]

> **Theorem 2.2 (exact count formula — status split).** For a terminating stratum `s` and
> `N ≥ N₀(s)`:
> ```
>   #(S_s ∩ monicBox(p,N,n)) = C_s(p) · p^{nN − A_s},          normalized mass
>   μ(S_s) = C_s(p) · p^{−A_s},                                               (‡)
> ```
> where, node by node (matching the engine's cell volume and BB1_r):
> - `A_s` = Σ over reads `r` of `w_r · A(Π_r)`, `A(Π) = Σ_i ⌈h_i⌉` the lattice ceiling-sum of the
>   read's polygon (BB1/L4 exponent, `notes/BB1_exponent.md` closed form), `w_r` = the base-`p`
>   digit weight of the node's coefficient ring (`w_r = δ·f_1⋯f_{r-1}·m-frame` — each `F_r`-digit
>   is `w_r` base-`p` digits), plus the depth-shift costs of recenterings (the `m·e(e+1)/2`-type
>   lattice shifts; at `n=2` this is the `3m−1` exponent verified in §7);
> - `C_s(p)` = ∏ over reads of [per-side residual **choice counts**: the number of shape-compatible
>   residual values, a universal necklace/Gauss polynomial (L3) evaluated at `Q_r'`] ×
>   `(p^{w}−1)`-type unit factors at polygon vertices (`(1−Q^{-1})^V` in mass form).
>
> **Status by stratum class:**
> 1. Order ≤ 1 reads over the base pool (root read + first polygon + residual shapes over `F_q`):
>    **[COUNT — PROVED in Lean]**: `StratumOrder1.stratumCount1_eq_closed`
>    `= prodSC p sh · p ^ freeExp s N P` (`CellCard.freeExp` is exactly `nN − A_s` in the
>    order-1 window); counting limits `hnode_selfloop_over_Bclassify_R`
>    (`OM/ClassifierBridgeFiber2.lean`), multi-side product `hnode_multiSideShape`/
>    `hnode_multiSideProduct` (`OM/ClassifierBridgeMultiSide2.lean`, `PathShapeMultiSideTree`),
>    order-0 legs `Order0RealDensity`.
> 2. Any depth of **`deg ψ = 1` recenterings over the base field** (all descents linear, all pools
>    over `F_q` — includes ALL of `n = 2` and every constant-e H-tower): **[COUNT — provable now,
>    (b)]** by Lemma 2.3; not yet in Lean beyond depth 0 (this is Wave 5's core).
> 3. Reads with **`deg φ ≥ 2`** (root points of degree `δ ≥ 2` with multiplicity, or descend
>    factors with `f_ψ ≥ 2` / `e ≥ 2, μ ≥ 2`): the cylinder structure and the FORM (‡) hold as
>    stated, but the proof that the read digits are jointly free with the displayed pool counts is
>    **[OPEN-D1]** (the development-digit ledger), and the pool counts over `F_{Q}` with `Q = q^w`
>    are **[OPEN-D2]** in Lean (math-solid: L3 holds over every finite field, `HUMAN_PROOF §4`;
>    Lean's `CellCard.shapeCount` is `ZMod p` only — the `UnramifiedBase`/tower work).

> **Lemma 2.3 (recenter–rescale bijection, linear case) [COUNT — proof, (b)].** Let a node's read
> select an integer slope `m`, full-side repeated residual `(y−c̃)^s` on a size-`s` cluster (frame:
> coefficients `a_1,…,a_{s}` of the current recentered window). Then the map
> `f ↦ g, g(y) := f(ĉp^m + p^m y)/p^{sm}` restricted to the stratum's cylinder is an affine
> unipotent-triangular measure-isomorphism onto `{residual digits = c̃-data} × (fresh size-s
> cluster box)`, carrying normalized level-`N` counts to level-`(N − sm)`-frame counts.
> *Proof.* Binomial expansion: the coefficient map of `x ↦ ĉp^m + p^m x` is triangular with unit
> diagonal `p`-powers matched by the `p^{sm}` normalization; the stratum's defining digit
> conditions (side exact, residual root `c̃`) consume exactly the fixed digits, leaving the fresh
> box digits free — verified digit-by-digit at `n=2` in §7 (Case A ledger), general `s` identical
> in structure (the Vieta/binomial matrix is independent of `f`). ∎
> Consequence: depth adds exponents and multiplies choice counts in (‡) — the per-stratum masses of
> a descend chain are the PRODUCTS of per-step masses in fresh frames. This is the count-level
> content that the engine's self-similar recursion uses at the `e=1` node, obtained here WITHOUT
> any path-independence axiom (the bijection is explicit per stratum).

> **[OPEN-D1] (development-digit ledger, `deg φ ≥ 2`) — the precise open lemma.** For a fixed
> canonical key `φ` (degree `m_φ ≥ 2`) over node ring `O_r` and a fixed read of its polygon/
> residual data: the joint distribution, under uniform `f mod p^N`, of the inspected digits — the
> `F_r'`-residues of the on-side development coefficients `a_i(f)` at their polygon heights — is
> uniform and independent over their pools (endpoint units, interior free), with all uninspected
> digits free; equivalently, count = (‡) with the displayed `C_s, A_s`. *Route (recorded, not
> proved):* the development is linear-triangular for fixed φ (Def 1.2.1), so D1 reduces to tracking
> which base-`p` digit functionals the `v_r`-heights inspect — the `RESTART_LEMMA.md` unipotent-
> triangular route, = the count-level content of BB3_infinity's GAP-1/GAP-2 in the ONLY place this
> note needs it. At order 1 with `deg φ = 1` it is proved (`CellCard.cell_card_raw`). **This is the
> single riskiest lemma of the program** (§8).

---

## 3. Mass accounting / exhaustion (the crux)

### 3.1 The per-level identity — pure counting

> **Lemma 3.1 (finite-depth/finite-level partition) [COUNT, (b)].** Fix `N`. Classify every
> `f ∈ monicBox(p,N,n)` by running reads until (i) termination, (ii) a descend whose child read
> would inspect digits beyond level `N` (STUCK/tail), or (iii) an unreadable coefficient
> (`a_i ≡ 0 mod p^{N−·}` where a side endpoint is needed — the tail proper). Then EXACTLY
> ```
>   p^{nN} = Σ_{s terminating, N₀(s) ≤ N} #S_s(N)  +  Σ_{s' open, active at level N} #S_{s'}(N)   (3a)
> ```
> — a finite partition of a finite set by classifier outcome; both sums finite (heights ≤ N).
> *Status:* order-1 instance PROVED in Lean: `StratumOrder1.stratumCount1_partition`
> (`Σ_{c ∈ cellMenu} stratumCount1 + tailCount1 = p^{s(N−1)}` on the cluster box) and
> `Drainage.card_undecided1_index`. The general-depth version is the same argument (outcomes of a
> total reader partition the box) — pure counting, no import. ∎

### 3.2 The envelope: still-descending mass → 0 via the discriminant

Two independent bounds; (ENV-1) is the clean axiomatizable one, (ENV-2) the elementary scaffold.

> **Lemma 3.2 (depth ⟹ index ⟹ discriminant) [MONTES — axiomatizable].** For monic separable
> `f`: the OM resolution performs at most `ind(f)` descend events (including refinements), and it
> terminates; moreover `2·ind(f) ≤ v_p(disc f)`.
> *Citation:* GMN Thm 4.18 (theorem of the index, `ind(f) ≥ ind_1 + ⋯ + ind_r`) + Cor 4.19
> (termination) + GMN §-intro "This result guarantees that the factorization process finishes at
> most in `ind(f)` steps" (`GMN_citations.md §2.3`); `2·ind ≤ v_p(disc)` is the classical
> index–discriminant relation (`v_p(disc f) = 2·ind(f) + Σ_i v_p(disc L_i) ≥ 2·ind(f)`, Ore/GMN
> §4). *Faithfulness note for the future axiom:* the repo already carries the index theorem in
> arising-key form (`omReadValuation_lt_of_certLevel_fkeyed`); the new declaration should be the
> DEPTH consequence only — "still descending at depth d ⟹ v_p(disc f) ≥ 2d" — existence-free,
> measure-free, pointwise, hence auditable by the standard triple test. The exact on/below lattice
> convention of GMN's `ind(N)` must be pinned at declaration time (flag).

> **Lemma 3.3 (discriminant tail — elementary) [COUNT — proof, (b): folklore technique, new to
> this corpus].** For every `n ≥ 2`, prime `p`, and `D ≥ 0`:
> ```
>   μ{ f monic deg n : v_p(disc f) ≥ D }  ≤  (n−1) · p^{ −⌈ (D − n·v_p(n)) / (n−1) ⌉ }.       (3b)
> ```
> *Proof.* `disc f = ± Res(f, f')` and `Res(f, f') = ± n^n ∏_{j} f(β_j)` over the `n−1` roots
> `β_j` of `f'` in `K̄` (with multiplicity; `lc(f') = n ≠ 0` in char 0). The `β_j` and the value
> `f(β_j) − a_0` depend only on the higher coefficients `a_1,…,a_{n−1}`, NOT on `a_0`. So
> `v(disc) ≥ D ⟹ Σ_j v(a_0 − c_j) ≥ D − n·v_p(n)` with `c_j := −(f − a_0)(β_j)` fixed by the
> higher coefficients `⟹ ∃j: v(a_0 − c_j) ≥ (D − n v_p(n))/(n−1)`. For fixed higher coefficients,
> each event `{a_0 ∈ ℤ_p : v(a_0 − c_j) ≥ t}` has measure `≤ p^{−⌈t⌉}` (a ball, possibly empty —
> `v` extended to `K̄`). Union bound over `j`, then Fubini over the higher coefficients. ∎
> (Immediate corollaries: `μ{disc = 0} = 0`; `μ(Z_∞) = 0` re-derived.)

> **Corollary 3.4 (the descending envelope).** By 3.2 + 3.3, the still-descending-at-depth-`d`
> set `Desc_d := ⋃_{s open, d(s) ≥ d} S_s` satisfies
> ```
>   μ(Desc_d) ≤ (n−1) · p^{ −⌈ (2d − n·v_p(n)) / (n−1) ⌉ }  → 0 geometrically in d.          (3c)
> ```
> **Nothing else is used**: no per-depth count identity, no pivot, no ×q, no child-law
> identification — (3c) is a POINTWISE inclusion `Desc_d ⊆ {v_p(disc) ≥ 2d}` [MONTES] followed by
> an unconditional measure bound [COUNT].

> **Lemma 3.4′ (level tail, for the N-limit) [COUNT + classical NP].** The level-`N` undecided
> mass (stuck + tail in Lemma 3.1) is `≤ μ{v_p(disc f) ≥ c_n·N − c'_n} + 0` for explicit
> `c_n = 2/n`-type constants: an `f` undecided at level `N` has all reads consistent with two roots
> at mutual valuation `≥ (N − consumed)/n`-type depth, and `v_p(disc) = 2Σ_{i<j} v(α_i − α_j)`
> (monic; Vandermonde) with `v(α_i − α_j) ≥ min` accumulated depth (ultrametric). The polygon ⟹
> root-valuation direction is classical Newton-polygon theory [(a); MONTES Thm 1.15 direction or
> elementary hensel-field NP — either import works]. Combined with (3b): undecided-at-`N` mass
> `→ 0` like `p^{−c·N}`. *Order-1 Lean instance of the tail half:*
> `Drainage.tendsto_tailDensity_zero`; the order-1 STUCK mass is the `N`-independent self-loop
> constant (`Drainage.tendsto_undecidedDensity`) — which is exactly why finite-ORDER reading does
> not drain and DEPTH (this note's tree) is the right exhaustion variable.

### 3.5 Exhaustion

> **Theorem 3.5 (decomposition of the full decided density) [(b); statuses inline].** The
> terminating strata are pairwise disjoint, each of exact mass (‡), and
> ```
>   μ(box) = Σ_{s terminating} μ(S_s),   and per type:
>   ρ_dec(n, σ; p) = Σ_{s terminating, σ(s) = σ} μ(S_s)      (σ(s) as in §6),               (3d)
> ```
> the series converging absolutely (positive terms). Moreover the level-`N` normalized decided
> count equals the partial sum over `{s : N₀(s) ≤ N}` up to the envelope error (3c)+(3.4′), so the
> Lean counting limits converge to (3d).
> *Proof.* Disjointness: distinct read-histories are incompatible outcomes of the same
> deterministic reader [COUNT]. Cover: `f` outside `Z_∞ ∪ {disc = 0}` (measure zero, 3.3) has a
> terminating history by Lemma 3.2 [MONTES]. Countable additivity of Haar measure gives (3d); the
> quantitative form is Lemma 3.1 + Corollary 3.4 + Lemma 3.4′. ∎
> The only [MONTES] content: termination + depth-index (3.2), polygon⟹root-valuations (3.4′),
> lift-invariance (Def 1.2). The only [OPEN] content: the VALUE of each `μ(S_s)` via (‡) in class
> 3 (D1/D2). **Exhaustion itself needs neither D1 nor D2** — (3d) with abstract masses is
> COUNT+MONTES only.

### 3.6 Confronting the wall (`SELFLOOP_GENERALK_WALL.md`)

The wall refuted five (then six) routes that tried to prove: *the finite-`N` census, decomposed by
self-loop depth `k`, matches the engine's ×q-exposed geometric tower `depth0·(q·slBox)^k`, whose
resummation is the pivot `1/(1 − q^{−w})`.* Its conclusion stands: no finite-`N` box count realizes
the ×q-exposed per-depth form (FACT B: `P(deep|verdict)(N) → slBox`, bare).

**This note never forms that object.** Point by point:

1. **No per-depth ↔ pivot identity is ever used.** The decomposition (3d) sums per-stratum masses;
   the engine's pivot form re-enters only in §4 as a FORMAL resummation of an absolutely
   convergent series of exactly-known terms — an identity in ℚ, not a finite-`N` count identity.
2. **The envelope (3c) replaces the geometric per-depth census.** The wall's routes needed the
   depth-`k` mass to EQUAL a geometric term; we need only that the OPEN mass is `≤` a geometric
   envelope, and (3c) delivers that from the pointwise discriminant inclusion — an object the wall
   never touched (none of the five routes involved `disc`).
3. **Where the ×q "went".** In the tree, each recentering level carries its residual-value index:
   the descend-at-slope-`m` strata have the `(p−1)`-fold choice of `c̃ ∈ F_q^×` (Drainage's
   `(p−1)·slBox` seed — the machine-checked census!), while the engine's per-level `q·slBox`
   aggregates ACROSS reads (its rescale branch also swallows the `c̃ = 0`-direction mass as
   deeper-`H` strata of the SAME read). The two are different groupings of the same series; they
   agree after summation (verified symbolically at `n=2` in §7, Case A: both give `q/(q+1)`).
   FACT B is thereby *explained*: the per-depth conditional census sees the bare
   `(p−1)slBox + deeper-H` split, never the regrouped `q·slBox` — which is a property of the
   engine's normal form, not of any stratum.
4. **Honest residue.** The wall's deep reason ("the ×q is measure-theoretic") survives in exactly
   one place: for `deg φ ≥ 2` descents the per-stratum count formula (class 3) is OPEN-D1 — the
   same content as GAP-1/GAP-2's count-level half. For `deg ψ = 1` chains (the wall's own `e=1`
   self-loop regime!) Lemma 2.3 makes it elementary — consistent with the wall, because Lemma 2.3
   produces per-STRATUM masses in fresh frames, not the fixed-box per-depth census the wall
   demanded. If D1 turns out to genuinely require non-Montes measure content, that is precisely
   BB3_infinity GAP-1/GAP-2 resurfacing — the finding is: **it is confined to D1, and touches
   neither exhaustion (§3) nor the linear-descent strata (class 2).**

---

## 4. The series and its rationality

> **Theorem 4.1 (convergence, per fixed p) [(b)].** The series (3d) converges absolutely;
> moreover grouped by (depth `d`, max height `H`), the tail beyond `(d, H)` is
> `O(p^{−c·d} + p^{−c'·H})` by Corollary 3.4 and the height ladder in (‡) (heights enter `A_s`
> linearly with positive weight). [COUNT given §2 statuses.]

> **Definition 4.2 (shape grouping).** Group strata by SHAPE (†): the p-independent tree of
> polygons, side data `(h, e, ℓ)`, residual SHAPES (degree–multiplicity partitions), and residue
> degrees. Per shape `T`, the VALUES-fiber count is the product of residual choice counts.

> **Claim 4.3 (per-shape counts are universal polynomials) — status split.**
> Per read over pool field of size `Q`: #{monic degree-`d`, `R(0) ≠ 0`, given shape} is a single
> polynomial in `Q` (necklace/Gauss counts; falling factorials over irreducible pools) — (a) known,
> L3 (`HUMAN_PROOF §4`, verified all wild fields). With `Q = q^{w_r}` this is p-independent IN q.
> **Lean status:** proved over `ZMod p` (`L3.lean`, `L3Gauss`, `CellCard.shapeCount_*`); extension
> pools = [OPEN-D2] (the deferred `UnramifiedBase`/tower vocabulary — no new math, real Lean work).
> *Honest-empty note:* these polynomials vanish at small `q` for some shapes (split needs
> `q ≥ 3`: Wave-1's machine-checked pool-size effect) — per-shape emptiness is a feature the
> universal-polynomial form carries correctly.

> **Claim 4.4 (geometric closure of the two infinite directions) — status split.**
> (i) **H-ladders** (heights within one read, everything else fixed): masses are
> `const · p^{−(linear in H)}` by (‡), so each ladder sums to a rational function with denominator
> `1 − q^{−(ladder weight)}` — (a)/(b): exactly the engine's `_geom_sum_inf`/`_cone_sum` and
> L5fix(d); Lean pattern exists (window-K staircases, `normSum_omMenuW3_mono`; the K→∞ sum is
> Wave 6). Multi-side reads sum over the strictly-decreasing-slope cone via the gap substitution —
> engine `_sum_by_gaps`, pure lattice algebra [COUNT].
> (ii) **Depth towers**: by Lemma 2.3, a `deg ψ = 1` descend multiplies masses by a fixed
> per-step total ratio (e.g. `Σ_m (1−q^{-1})q^{−(3m−1)} = 1/(q²+q+1)` at `n=2`); chains resum
> geometrically [COUNT via 2.3]. For `deg φ ≥ 2` descents the same closure holds GIVEN D1 (the
> per-step masses then being class-3 (‡) values with base-changed `q ↦ q^{w}`) [OPEN-D1].
> (iii) Everything else (slopes' denominators, shapes, residue degrees, number of sides, depth of
> the SHAPE tree after quotienting ladders/towers) is finite and p-independent — (a): L5fix(b),
> `HUMAN_PROOF §9`; the menu `T_n` finiteness.

> **Theorem 4.5 (conditional rationality; agreement with the engine) [(b), conditional].** Modulo
> D1+D2 for class-3 strata: for each `n, σ` the sum (3d), grouped by shape and resummed by 4.4, is
> a single rational function of `q` evaluated at `q = p`, equal to the engine's
> `alpha_full(n)[σ]` (the `beta_e` fixpoint assembly of `om_density_engine.py`) — the regrouping
> from the tree's by-reads normal form to the engine's rescale normal form is a rearrangement of
> an absolutely convergent positive series [justified by Thm 4.1], and both closed forms satisfy
> the same non-degenerate linear fixpoint (`(⋆⋆)` of BB3_infinity §4, pivot `1 − q^{−w(e)} ≠ 0`).
> For strata classes 1–2 (order ≤ 1 + linear towers) the rationality is UNCONDITIONAL
> [COUNT+MONTES]. p-independence of the assembled function: derived, never imported (the
> GMN-citations discipline: per-p imports of p-free shape).

---

## 5. The Montes-axiom boundary (per ingredient)

| # | Ingredient | Class | Citation / proof locus |
|---|---|---|---|
| 1 | Root read + Hensel measure split (L1) | [MONTES]/(a) solid | `HUMAN_PROOF §3`; Igusa §7.4; Lean order-0 legs proved |
| 2 | φ-adic development = fixed triangular bijection | [COUNT] | Def 1.2.1 (division by fixed monic; elementary) |
| 3 | Polygon/residual READ definitions at order r | [MONTES defs] | GMN Def 2.3/2.5/2.21; order ≤ 1: repo `CellMenu` [COUNT] |
| 4 | Leaf dichotomy + (e,f) product law | [MONTES] | Cor 1.20 (order 1), Thm 3.1/3.7 + Cor 3.8 (order r); repo axiom `om_leaf_faithful` is the menu-scoped instance — extend fiber-scoped per new menus (Wave 4/5 pattern, W3c re-scope precedent) |
| 5 | Lift admissibility/invariance (canonical lifts read the same tree) | [MONTES] | GMN §2.4–3 representatives; exact pin TBD at declaration (flag) |
| 6 | Termination + depth ≤ ind ≤ ½·v_p(disc) | [MONTES] | Thm 4.18 + Cor 4.19 + §-intro bound; declare as pointwise depth⟹disc (Lemma 3.2 form); repo precedent `omReadValuation_lt_of_certLevel_fkeyed` |
| 7 | Discriminant tail (3b) | [COUNT — proved here] | Lemma 3.3 (elementary; Lean-able: resultant product + Fubini + ball bound) |
| 8 | Per-level partition (3a) | [COUNT — order-1 proved] | `stratumCount1_partition`; general = same pattern |
| 9 | Per-stratum counts, classes 1–2 | [COUNT — proved/provable] | §2 Thm 2.2.1–2, Lemma 2.3 |
| 10 | Per-stratum counts, class 3 (`deg φ ≥ 2`) | **[OPEN-D1]** | the development-digit ledger; = count-level GAP-1/GAP-2 (`BB3_infinity §4.2/§8`); route: RESTART_LEMMA triangular coordinates |
| 11 | Pool counts over `F_{q^w}` in Lean | **[OPEN-D2]** | math (a)-known (L3 all finite fields); Lean `UnramifiedBase` tower work |
| 12 | Residual equidistribution as an AXIOM | **excluded** | standing non-import (no GMN counterpart — `M6_lemma.md`, PROJECT_STATE); its role is absorbed by D1 as a provable count statement |
| 13 | Geometric/cone resummation | [COUNT] | §4.4; engine `_sum_by_gaps`; L5fix(d) |
| 14 | Exhaustion (3d) | [COUNT+MONTES 6] | Thm 3.5 — needs NO open item |

**Answer to the task's (iii):** nothing in the decomposition/exhaustion/convergence genuinely
requires non-Montes content. The only candidates for genuinely-new measure content are D1 (count
form at `deg φ ≥ 2` — believed provable as pure counting via triangular coordinates, but open; if
it fails, that failure IS GAP-1/GAP-2 and must be reported as such) and nothing else. The
palindromy/htameFE layer stays outside this note's scope (declared endpoint boundary,
PROJECT_STATE §5.1).

---

## 6. σ-keying at depth

> **Definition 6.1 (leaf invariants) [MONTES Cor 3.8].** A leaf reached through root point of
> degree `δ`, reads with slope denominators `e_1, …, e_r` (integer-slope recenterings contribute
> `e_i = 1`), residual factor degrees `f_1, …, f_{r−1}` along the path, terminal factor `ψ` of
> degree `f_r` with `μ = 1`:
> ```
>   e(leaf) = e_1 e_2 ⋯ e_r ,    f(leaf) = δ · f_1 ⋯ f_{r−1} · f_r .                        (6a)
> ```

> **Proposition 6.2 (the type of a stratum) [(b), MONTES for faithfulness].** For a terminating
> stratum `s`: `σ(s) :=` the multiset union of `(e,f)(leaf)` over ALL leaves of ALL branches —
> across root points (CRT/L1 type-additivity), across sides of each polygon (multi-slope), across
> residual factors of each side, and across descend children (depth). Mixed-e types arise exactly
> from strata whose leaves see different `∏ e_i` — e.g. multi-slope polygons (one read, different
> side denominators) or towers of distinct denominators along different branches. That every
> `g ∈ S_s` genuinely factors over ℚ_p with type `σ(s)` is the fiber-scoped faithfulness axiom
> family (boundary table #4; Wave-2 `menuFiber_hasType` pattern). The keying itself (reading (6a)
> off the index) is definitional [COUNT] — the O1 lesson: σ enters only through the menu.

---

## 7. Numeric validation plan (run BEFORE any Lean; brute force + PARI oracle)

All targets are exact rationals from (‡); check both COUNT (cylinder census mod `p^N`) and TYPE
(`verification/quartic_oracle.py` `full_type` on samples from each cylinder). **Count-side status
(2026-07-22, run during the writing of this note; scratch scripts, not committed):** the full
`n=2` census partition at `(p,N) = (2,9), (3,6)` is exact at every level and converges to `β₂`
with geometrically small undecided remainder; the Case-A per-stratum ledger (ramH 1/2, 1/16,
1/128, 1/1024; inert/descend 1/8, 1/64, 1/512) is EXACT and N-stable; Case C = 1/16 exact;
Case D = 1458 at `N=4` exact; Case E = 3/64 exact **in original coordinates via genuine φ-adic
division** (the first empirical pass of D1's linear-bijection mechanism). The two-sided split
ledger values are the ideal cylinder masses (a naive census that routes `v(a₀) ≥ N` to the tail
undercounts them by exactly that tail — a bookkeeping caveat for the Lean statements, not an
error). TYPE-side (PARI `full_type` per cylinder) deferred to the wave gates.

**Case A — `n = 2`, `p = 2`, the complete tree (the master example).** Cluster-conditional at one
residue point (cluster box `v(a₁) ≥ 1, v(a₀) ≥ 1`, conditional measure):
- H-ladder (terminating, H odd): mass `(1−1/q)·q^{−3(H−1)/2}` = 1/2, 1/16, 1/128, … → sum
  `4/7`; full-box per point `(q−1)q^{−3−3(H−1)/2}`: H=1: 1/8, H=3: 1/64 — **must reproduce the
  Lean-certified Wave-1/3 anchors 1/8 and 9/64 (window K=3)**.
- even-H separable (inert at q=2; split empty — honest-empty pool): `m ≥ 1`: mass `(1/8)·8^{1−m}`,
  sum `1/7`.
- two-sided polygons (split): `k ≥ 1`: `(1/2)·2^{−(3k−1)}`, sum `1/7`.
- descend (μ=2 at slope m; `v(a₀)=2m` exact, `v(a₁) ≥ m+1`): `(1/2)·2^{−(3m−1)}`: 1/8, 1/64, …,
  sum `1/7`; depth-0 total `4/7+1/7+1/7+1/7 = 1` ✓.
- Fixpoint by Lemma 2.3: `β_ram = (4/7)/(1 − 1/7) = 2/3 = q/(q+1)` ✓; inert `1/6`, split `1/6` ✓
  (= `padic_types` β₂). Full-box ramified density `q·q^{−2}·β_ram = 1/(q+1) = 1/3`.
  **Checks:** census mod `2^N` (N ≤ 8) of every family above; symbolic identity of the two
  groupings (tree normal form vs engine rescale normal form).

**Case B — `n = 2`, `p = 3` (odd-p residual geometry).** Descend locus = parabola `disc̄ = 0`
(`v(a₁) = m` exact, `a₀`-digit determined): per-m mass `(1−1/q)q^{−(3m−1)}` — same universal
polynomial as p=2 (merge-map count `q−1`, different subvariety: the BB3 point). Ladder sum
`9/13`, descend ratio `1/13`, `β_ram = 3/4 = q/(q+1)` ✓. Census mod `3^N`, N ≤ 5.

**Case C — `n = 2`, `p = 2`, the X²−12 stratum (depth-1 compound).** Conditions: `v(a₁) ≥ 2`,
`v(a₀) = 2` (unit digit ⟹ `c̃ = 1`), recentered child `g(y) = f(2c̃ + 2y)/4` in H=1 stratum.
Expected mass (Lemma 2.3): `(1/8)·(1/2)` cluster-conditional = `1/64` full-box per point.
Membership probe: `f = x² − 12` (recenter `x ↦ x+2`: `x² + 4x − 8`, child polygon `(0,3)–(2,0)`
slope `−3/2`, leaf `(2,1)`) — the worked μ≥2 descent of the task sheet. Check count mod `2^N`
(N ≥ 4) and PARI type `{(2,1)}` on samples.

**Case D — `n = 4`, `p = 3`, mixed-e multi-slope (class 1–2, order ≤ 1).** Polygon
`(0,3)–(2,1)–(4,0)`: side 1 slope −1, d=2, residual split (choices `(q−1)(q−2)/2`); side 2 slope
−1/2, leaf `(2,1)`. σ = `{(2,1),(1,1),(1,1)}`. Digit ledger (derived above, matches
BB1 `(1−1/q)^V q^{−A}`, `V=2, A=7`): mass `= (q−1)²(q−2)/2 · q^{−10}` = `2·3^{−10}` at p=3;
count at `N=4`: `2·3^6 = 1458` of `3^{16}`. At `p=2`: EMPTY (pool `(q−2) = 0`) — the honest-empty
gate. PARI-type samples must give the mixed-e σ.

**Case E — `n = 4`, `p = 2`, `deg φ = 2` descent (the D1 probe).** Root read `f̄ = ḡ²`,
`ḡ = x² + x + 1`; development `f = φ² + a₁φ + a₀` (`φ` the canonical lift), minimal stratum
`v(a₀) = 1` exact (unit `F_4`-digit), `v(a₁) ≥ 1`: leaf `(e,f) = (2,2)`. Expected mass
`(Q−1)·Q^{−3}` with `Q = q² = 4`: `3/64` (one root point at q=2). Count mod `2^N` (`N ≥ 2`;
`N=2`: 12 of 256) + PARI type `{(2,2)}`. **This is the decisive empirical gate for OPEN-D1's
count form before any Lean work on class-3 strata.**

---

## 8. Verdict and recommended wave order

**Wall verdict: SIDESTEPPED** (§3.6) — the decomposition never forms a per-depth fixed-box census
against the pivot; exhaustion runs through the pointwise discriminant inclusion (Lemma 3.2
[MONTES]) plus the elementary tail (Lemma 3.3 [COUNT]); the engine's ×q-exposed tower is recovered
only as a rearrangement of an absolutely convergent series of exactly-counted stratum masses. The
wall's content survives, confined to OPEN-D1 (class-3 count forms), which exhaustion does not need.

**The three claim classes (contents):**
- **[COUNT/provable]:** development & recenter triangular bijections; strata are N-stable cylinder
  unions; per-stratum counts for order ≤ 1 pools (PROVED in Lean) and all `deg ψ = 1` towers
  (Lemma 2.3 — includes ALL of n=2); the per-level partition (3a) (order-1 PROVED); the
  discriminant tail (3b); the geometric/cone resummations; convergence.
- **[MONTES/axiomatizable]:** Hensel/L1 root split; order-r read definitions; leaf dichotomy +
  (e,f) product law (Cor 1.20/3.8 — extend `om_leaf_faithful` fiber-scoped per menu wave); lift
  invariance; termination/depth ≤ ind ≤ ½v_p(disc) (Thm 4.18/Cor 4.19 — new axiom candidate in the
  pointwise depth⟹disc form).
- **[OPEN]:** **D1** — the development-digit ledger for `deg φ ≥ 2` (count-level GAP-1/GAP-2;
  believed pure counting via fixed triangular coordinates; Case E is its empirical gate);
  **D2** — L3 pool counts over `F_{q^w}` in Lean (math known; tower vocabulary work).

**Recommended wave order** (each preceded by its §7 numeric gate):
1. **Wave 4 (mixed-e, order ≤ 1)** — class-1 strata only: menu = multi-slope shapes, counting legs
   already banked (`hnode_multiSideProduct`); gate Case D. Lowest risk.
2. **Wave 5 (μ≥2 linear descents)** — Lemma 2.3 in Lean + the depth-indexed menu for `n=2`-style
   full-side recenter chains; gates Cases A/B/C. Closes the FIRST complete per-type tower
   (`n = 2` all types, exact `q/(q+1)`-family values) with no new axiom beyond the depth⟹disc
   declaration (boundary #6) if the envelope is wired.
3. **Wave 6 (series assembly)** — infinite menu with per-level finite support; partial sums = the
   window staircases (Wave-3 pattern); exhaustion clause via (3a)+(3c)+(3.4′) discharging
   `hExhaust` on the linear-tower fragment.
4. **Wave 7 (class 3 / D1)** — only after Case E passes and D1 is proved on paper for one `deg φ = 2`
   order-1 read; if D1 resists pure counting, STOP and report it as GAP-1/GAP-2 resurfacing — do
   not axiomatize it (non-import #12).

**Single riskiest open lemma: OPEN-D1** (the development-digit ledger at `deg φ ≥ 2`). Everything
else in this note is either proved, provable by the exhibited elementary arguments, or a
faithful-scope extension of the existing Montes axiom pattern.
