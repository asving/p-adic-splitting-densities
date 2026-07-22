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
> 3. per side, the **residual polynomial** `R_S(f) ∈ F_r[y]`, monic degree `d_S`, `R_S(0) ≠ 0` —
>    over the node field `F_r` ITSELF, not an extension [MONTES Def 2.21; at order ≤ 1 base field:
>    COUNT, the explicit digit read of `CellCard`/`CellMenu`], and its factorization shape
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
> exact GMN pin TBD at axiom-declaration time (standard Montes content, citation pending) —
> flagged]. With canonical lifts, every read
> along the tree is a **fixed, f-independent** triangular coordinate change followed by digit
> inspections — the load-bearing structural observation of this note.

> **Definition 1.3 (stratum; terminating vs descending).** A **read-history** `s` is: a root-read
> outcome, and recursively, for every opened cluster node, a finite (possibly empty) sequence of
> cluster-read outcomes (Def 1.2 data: polygon, per-side residual shape, per-descend-factor the
> residual value `ψ` — value, not just degree). `S_s ⊆` box is the set of `f` realizing `s`.
> `s` is **TERMINATING** if every branch has ended in leaves — recursively: every residual factor
> with `μ ≥ 2` has an opened child node whose read-history is itself recursively resolved
> (terminating), and every TERMINAL (unopened) residual factor has `μ = 1`; it is
> **DESCENDING (open)** if some child node is still unread. The **depth** `d(s)` = the number of
> descend events along its deepest branch.
> **Descend events are exactly the Def 1.2.4 `μ ≥ 2` outcomes at cluster reads; the ROOT read's
> opening of a cluster node (Def 1.1, `m_j ≥ 2`) is NOT a descend event and contributes 0 to
> `d(s)`.** This exclusion is load-bearing for (3c): at `n = 2`, `p` odd, `f = x² − p` has
> `f̄ = x²` (a root cluster opens) yet its first cluster read is already a leaf (side `(0,1)–(2,0)`,
> `d_S = 1`), and `v_p(disc f) = v_p(4p) = 1 < 2` — so counting the opening as a descend event
> would falsify the depth-1 pointwise inclusion `Desc_1 ⊆ {v_p(disc) ≥ 2}`; in mass terms, the
> root-cluster locus has measure `~p^{−1}`, far above (3c)'s `d = 1` bound `p^{−2}`.

> **Definition 1.4 (the index — finite data per node) [COUNT, (b)].** A stratum is a finite
> labelled tree; each node carries: the polygon (a finite list of pairs `(h_i, e_i, ℓ_i)` of
> bounded denominators `e ≤ n` but UNBOUNDED heights `h`), per side a residual shape (a partition
> of `d_S` into `(degree, multiplicity)` parts — finitely many, degrees ≤ n), per descend factor a
> residual value `ψ ∈ F_r[y]` (finitely many per field). The tree is **countable**, and splits as
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
> many digit equalities/inequalities `v = h` / `v ≥ ⌈line⌉` and residual-digit values). For the
> UNIPOTENT steps (developments, recenterings) a fixed unipotent-triangular bijection of ℤ_p^n
> induces a bijection of `monicBox(p,N,n)` for every `N` (unipotent integral matrices +
> polynomial lower-order terms reduce mod `p^N`), so digit conditions on the transformed
> coordinates are digit conditions on the originals; the RESCALE steps (Lemma 2.3) are NOT
> level-preserving bijections — they are `p`-power-to-one across levels, carrying level-`N` boxes
> to level-`(N − sm)` frames with exact `p`-power count factors, which is the form the induction
> uses at descend steps. ∎
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
>   residual values, a universal necklace/Gauss polynomial (L3) evaluated at `Q_r`] ×
>   `(p^{w}−1)`-type unit factors at polygon vertices (`(1−Q^{-1})^V` in mass form).
>
> **Status by stratum class (the classes are a PARTITION of terminating strata — re-cut this
> revision, 2026-07-22, after pass-2 found the old classes 1/3 overlapping).** Partition key: the
> KEY DEGREES of the stratum's node reads. Call a stratum **all-linear** if every opened window
> (every cluster node, at every depth) has a degree-1 key — equivalently: every opened root
> cluster sits at a residue point of degree `δ = 1`, and every descend event has `deg ψ = 1`,
> `e = 1`. (Root LEAVES of degree `δ ≥ 2` open no window and are compatible with all-linear —
> they are the proved order-0 Hensel legs. All-linear forces every pool field `= F_q`, so
> "order ≤ 1 over the base pool" is not an extra condition but a consequence.) Then:
> - **class 1 := all-linear, depth 0** (no descend events);
> - **class 2 := all-linear, depth ≥ 1**;
> - **class 3 := not all-linear** (some window ANYWHERE in the tree has key degree ≥ 2: a
>   `δ ≥ 2` root point opened with multiplicity, or a `f_ψ ≥ 2` / `e ≥ 2, μ ≥ 2` descend —
>   whether at the root, at depth 5, or on one branch of an otherwise linear stratum).
> Every terminating stratum is in exactly one class. Statuses:
> 1. **Class 1 [COUNT — PROVED in Lean for the banked menus; general class 1 = same pattern +
>    L1 cross-cluster split [MONTES #1]]**: `StratumOrder1.stratumCount1_eq_closed`
>    `= prodSC p sh · p ^ freeExp s N P` (`CellCard.freeExp` is exactly `nN − A_s` in the
>    order-1 window); counting limits `hnode_selfloop_over_Bclassify_R`
>    (`OM/ClassifierBridgeFiber2.lean`), multi-side product `hnode_multiSideShape`/
>    `hnode_multiSideProduct` (`OM/ClassifierBridgeMultiSide2.lean`, `PathShapeMultiSideTree`),
>    order-0 legs `Order0RealDensity`. Exact masses for strata spanning several root clusters
>    multiply across clusters by L1's product measure [MONTES #1, solid].
> 2. **Class 2 — status split by descend geometry:**
>    * **whole-window towers** (every descend's side spans its whole window — includes ALL of
>      `n = 2`, where a `μ ≥ 2` side is automatically whole-window, and every constant-e
>      H-tower): **[COUNT — PROVED]**, Lemma 2.3 (general `s`, `m`, depth; full proof below;
>      cross-cluster assembly of multi-cluster strata as in class 1, via L1 [MONTES #1]);
>      not yet in Lean beyond depth 0 (this is Wave 5's core).
>    * **partial-side linear descents** (residual `(y−c̃)^s · (coprime rest)` on one side,
>      `n ≥ 3` only): **[OPEN-D3]**.
>    * **mid-polygon full-side linear descents** (side full but a proper side of a multi-side
>      window polygon, `n ≥ 3` only): **[OPEN-D5]** (new this revision).
> 3. **Class 3**: the cylinder structure (Thm 2.1) holds, hence each `μ(S_s)` is unconditionally
>    a rational number of the form `(integer)·p^{−nN₀(s)}` [COUNT]; but the DISPLAYED (‡) values
>    `C_s, A_s` — i.e. that the read digits, across ALL reads of the history, are jointly free
>    with the displayed pool counts — are
>    **[OPEN-D1]** (the development-digit ledger, JOINT form — exactly what a whole-stratum (‡)
>    value needs), and the pool counts over `F_Q`, `Q = q^w`, are
>    **[OPEN-D2]** in Lean (math-solid: L3 holds over every finite field, `HUMAN_PROOF §4`;
>    Lean's `CellCard.shapeCount` is `ZMod p` only — the `UnramifiedBase`/tower work). Do NOT
>    read "the FORM (‡) holds" as proved for class 3: only the p-power-rationality is.

> **Lemma 2.3 (recenter–rescale bijection, whole-window linear case) [COUNT — PROVED, (b);
> general `s`, general `m`, general depth — full proof this revision, 2026-07-22].**
> **Scope (marked restriction, 2026-07-22):** the descend side spans the WHOLE window polygon —
> single side `(0, sm)–(s, 0)` on a size-`s` window, residual `(y−c̃)^s` (up to the unit leading
> residue), `m ≥ 1` an integer, `c̃ ∈ F_q^×`. Full-side descends on a PROPER side of a multi-side
> window polygon (possible only at `n ≥ 3`) are NOT covered — they are the new **[OPEN-D5]**
> below. All of `n = 2` and all constant-window H-towers are whole-window, so Waves 5–6 sit
> entirely inside this scope.
>
> *Setting.* Window vector `(a_0, …, a_{s−1}; a_s)` with `a_s` a fixed unit (`a_s = 1` for a
> monic window; at a size-`s` root cluster of `f`, the `a_i` are the Taylor/φ-adic development
> coefficients and `a_s` is a unit by size-exactness; coefficients above the window enter only
> through the `p^m`-divisible tail terms of (2.3a), handled below). **Frame:** the free
> coordinates `(a_0,…,a_{s−1})` are jointly uniform on a MONOTONE STAIRCASE box
> `∏_{i<s} ℤ/p^{L_i}`, `L_0 ≤ L_1 ≤ … ≤ L_{s−1}` (base case: `L_i = N` constant), conditionally
> on everything else (tail coefficients, previously consumed digits). Budget `B := L_0 ≥ sm + 1`.
> **Stratum conditions at this read:**
> (S1) `v(a_i) ≥ m(s−i)` for `i < s` (points on/above the side);
> (S2) residual `= ā_s·(y−c̃)^s`, i.e. `(a_i/p^{m(s−i)}) ≡ ā_s·C(s,i)(−c̃)^{s−i} (mod p)` for
> `i < s` — together: the base-`p` digits of `a_i` at positions `0,…,m(s−i)` are prescribed,
> `Σ_{i<s}(m(s−i)+1) = m·s(s+1)/2 + s` digits in all.
>
> *Claim.* With `ĉ` the Teichmüller lift of `c̃` and `g(y) := f(ĉp^m + p^m y)/p^{sm}` the child
> (window coefficients `b_0,…,b_{s−1}; b_s`), the map `f ↦ g` restricted to (S1)∧(S2) is a
> bijection onto the CHILD STAIRCASE CLUSTER BOX
> `{ (b_k mod p^{M_k})_{k<s} : b_k ≡ 0 (mod p) }`, `M_k := L_k − m(s−k)` (again a monotone
> staircase, child budget `B′ = M_0 = B − sm`); consequently, conditionally on the stratum the
> child window is UNIFORM on that box, and the stratum's frame-relative mass is exactly
> `p^{−s − m·s(s+1)/2}` per `(m, c̃)`.
>
> *Proof.* **(1) Coefficient identity.** Binomial expansion of `g(y) = f(ĉp^m + p^m y)/p^{sm}`
> gives, for `i, k ≤ s` and with `ã_i := a_i / p^{m(s−i)}` (defined on (S1)),
> ```
>   b_k = Σ_{i=k}^{s} C(i,k) ĉ^{i−k} ã_i  +  t_k ,      t_k ≡ 0 (mod p^m),               (2.3a)
> ```
> where `t_k` := the contribution of the coefficients ABOVE the window (`t_k = Σ_{i>s}
> C(i,k)ĉ^{i−k}p^{m(i−s)}a_i`) — a fixed additive constant given the conditioning, absent for a
> monic window (`t_k = 0`). Equivalently `Σ_i ã_i y^i = Σ_k (b_k − t_k)(y−ĉ)^k`: the map
> `(ã_i) ↦ (b_k)` is affine UNIPOTENT upper-triangular over ℤ_p, inverse
> `ã_i = Σ_{k≥i} C(k,i)(−ĉ)^{k−i}(b_k − t_k)`.
> **(2) Staircase bijection.** At levels `M_k = L_k − m(s−k)`: `ã_i mod p^{M_i}` needs
> `b_k mod p^{M_i}` for `k ≥ i` only, and `M_k ≥ M_i` for `k ≥ i` (monotonicity: both `L_k` and
> `−m(s−k)` are non-decreasing in `k`); the inverse shift likewise. So (2.3a) induces mutually
> inverse maps on staircase boxes — a bijection; composing with the digit shift
> `a_i = p^{m(s−i)}·ã_i` (a bijection `ℤ/p^{M_i} → p^{m(s−i)}·ℤ/p^{L_i}`, exactly condition (S1))
> exhibits every (S1)-window as `Φ(b)` for a unique staircase `b`.
> **(3) Residual identity.** Reducing `Σ_i ã_i y^i = Σ_k (b_k − t_k)(y−ĉ)^k` mod `p` — the tail
> dies, `t̄_k = 0` since `m ≥ 1`:
> ```
>   R_S(y) = ḡ_w(y − c̃),    ḡ_w(z) := Σ_{k≤s} b̄_k z^k ,                              (2.3b)
> ```
> so (S2) `R_S = ā_s (y−c̃)^s  ⟺  ḡ_w(z) = ā_s z^s  ⟺  b̄_k = 0 for all k < s` — the stratum's
> residual condition IS the child cluster condition; no digit is left over and none is missing.
> **(4) Mass and child law.** By (2)+(3), Φ bijects `{staircase b : b̄ = 0}` onto the stratum
> slice; uniform measure pushes through a bijection, so the child is uniform on the staircase
> cluster box, and
> ```
>   μ_frame(S1 ∧ S2) = ∏_{k<s} p^{M_k − 1} / ∏_{i<s} p^{L_i} = p^{−s − m·s(s+1)/2}.     (2.3c)
> ```
> The child budget is `B′ = B − sm` — the level pin `N′ = N − sm` in the constant-staircase base
> case. **(5) Chains.** The child frame (staircase cluster box, monotone) is a frame of the same
> form, so (1)–(4) iterate; at every step past the first, the `s` cluster digits are already part
> of the frame (each step's (S1) re-uses the cluster condition its predecessor delivered), so a
> depth-`k` chain `(m_1,c̃_1),…,(m_k,c̃_k)` of whole-window descends has exact frame-relative mass
> `p^{−s} · ∏_t p^{−m_t·s(s+1)/2}` — the cluster digits priced ONCE, the per-step conditional
> factor being `p^{−m_t·s(s+1)/2}` per `c̃_t` (checked against §7 Case C:
> `p^{−2}·p^{−3}·(1/2) = 1/64` ✓) — child budget `B − s·Σ_t m_t`, and
> uniform staircase-cluster law at the bottom — so any terminating read at the bottom frame whose
> digits sit within budget has the same conditional mass as in a box-uniform frame. ∎
> *Numerics (2026-07-22, this revision):* (2.3c) + the bijection + the staircase support verified
> by brute force at `(p,s,m) ∈ {(2,3,1),(3,3,1),(2,3,2),(2,2,1),(3,2,2)}` and, in the embedded
> form (unit `a_s`, tails with `p`-divisible entries, `n = 4, 5`), at five more configurations —
> every child fiber hit exactly once, support exactly the staircase cluster box; the depth-2
> chain mass `p^{−s}·p^{−m_1·w}·p^{−m_2·w}` verified exactly at `n = 2, p = 2, m = (1,1)`
> (`= 2^{−8}`, census mod `2^{10}`).
> Consequence: depth adds exponents and multiplies choice counts in (‡) — the per-stratum masses of
> a descend chain are the PRODUCTS of per-step masses in fresh frames. This is the count-level
> content that the engine's self-similar recursion uses at the `e=1` node, obtained here WITHOUT
> any path-independence axiom (the bijection is explicit per stratum).

> **[OPEN-D3] (partial-side linear descend window-freeness — a `deg φ = 1` mini-analogue of D1).**
> For a read whose side of integer slope `m` carries residual `R_S ~ (y−c̃)^s · (coprime rest)`
> with `s ≥ 2` and the rest nontrivial (a PARTIAL side; possible only for `n ≥ 3`): the
> recenter–rescale map of Lemma 2.3, restricted to the stratum's cylinder, still carries the
> conditional measure onto `{fixed digits} × (fresh size-s cluster box)` — i.e. the fresh-window
> digits are jointly free of the co-side factors' residual conditions. Trivially satisfied when
> the residual fills the side (Lemma 2.3's hypothesis, which covers all of `n = 2` and all Wave-5
> needs); OPEN in the partial case — the same "jointly free" content as D1, but for a single
> `deg φ = 1` read, hence expected far easier. Until proved, class-2 status (Thm 2.2.2,
> Claim 4.4(ii)) extends only to WHOLE-WINDOW full-side linear towers.

> **[OPEN-D5] (mid-polygon full-side linear descend — new this revision, 2026-07-22).** For a
> read whose window polygon has SEVERAL sides, one of which (of integer slope `−m`, lattice
> length `ℓ ≥ 2`, NOT spanning the whole window) carries residual `(y−c̃)^ℓ`, `c̃ ∈ F_q^×`: the
> child read is the read of the literally recentered polynomial (Def 1.2.4), so the child's
> conditions are exact digit conditions on the coefficients of `F := f(window recentered by
> ĉp^m)` at abscissas `≤ ℓ` — a DIFFERENT unipotent frame from the parent's. The open content:
> the joint distribution of the child's inspected `F`-digits with the parent's OTHER sides'
> conditions (which live in the parent's frame) is the product of their separate laws with the
> displayed pool counts — the exact failing step when Lemma 2.3's proof is attempted here: the
> staircase bijection (2.3a)–(2.3c) needs the diagonal rescale to absorb the WHOLE window
> (`a_i = p^{m(s−i)}ã_i` for every window coordinate); for a proper side the co-side coordinates
> are rescaled at the WRONG heights (their polygon lines are not `m(s−i)`), so the bijection onto
> a product frame fails as stated, and no elementary replacement is known. Possible only at
> `n ≥ 3` (a size-2 window polygon carrying a `μ ≥ 2` side is automatically whole-window). A
> sibling of D1 (one linear read across the frame change instead of a `deg φ ≥ 2` development);
> expected to follow from an extension of the D1 ledger method, but NO formal reduction is
> supplied — D1 as stated concerns `deg φ ≥ 2` keys and does not logically imply this
> `deg φ = 1` cross-frame statement. Not needed for `n = 2` or Waves 5–6.

> **[OPEN-D1] (development-digit ledger, `deg φ ≥ 2`) — the precise open lemma, JOINT form
> (restated this revision, 2026-07-22, pass 4: the previous statement gave only the single-read
> marginal below, while every consumer needs the joint ledger).** For a complete fixed
> read-HISTORY/prefix `s` containing some `deg φ ≥ 2` development step (a class-3 history; ALL
> its reads — the `deg φ ≥ 2` steps included — are priced jointly, so this scope matches the
> class-3 consumers and leaves the all-linear D3/D5 strata outside, as before), under uniform
> `f mod p^N`, `N ≥ N₀(s)`: the full collection of inspected digit
> functionals — for each read, the `F_r`-residues of the on-side development coefficients
> `a_i(f)` at their polygon heights — is JOINTLY uniform and independent over their pools
> (endpoint units, interior free), with all uninspected digits free. Equivalently: each read's
> displayed law holds CONDITIONALLY on every compatible ancestor-stratum cylinder (the
> conditional law of a read's inspected digits, given any compatible outcome of all earlier
> reads, is the same uniform-product law); equivalently, count = (‡) with the displayed
> `C_s, A_s` — the whole-stratum count formula IS the joint statement, which is why the marginal
> form below does not suffice for any (‡) consumer.
> **D1-marginal (corollary/special case — the pre-pass-4 statement of this item):** for a fixed
> canonical key `φ` (degree `m_φ ≥ 2`) over node ring `O_r` and a fixed SINGLE read of its
> polygon/residual data, the joint distribution of that read's inspected digits is uniform and
> independent over their pools, with all uninspected digits free.
> *Route (recorded, not proved):* the development is linear-triangular for fixed φ (Def 1.2.1),
> and each descend's frame change is itself a fixed triangular map, so joint-D1 reduces to
> tracking which base-`p` digit functionals the `v_r`-heights inspect across the whole history —
> the `RESTART_LEMMA.md` unipotent-triangular route, = the count-level content of BB3_infinity's
> GAP-1/GAP-2 in the ONLY place this note needs it. At order 1 with `deg φ = 1` the MARGINAL
> analogue is proved (`CellCard.cell_card_raw`); the joint analogue for whole-window linear
> chains is Lemma 2.3(4)–(5) [COUNT — proved]. **This is the single riskiest lemma of the
> program** (§8).

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
> *Citation & pins:* GMN Thm 4.18 (theorem of the index, `ind(f) ≥ ind_1 + ⋯ + ind_r`) + Cor 4.19
> (termination) + GMN §-intro "This result guarantees that the factorization process finishes at
> most in `ind(f)` steps" (`GMN_citations.md §2.3`). The depth⟹disc chain rests on exactly the
> **three pins (P1)–(P3) of `GMN_citations.md` §"§4 index machinery"**:
> **(P1)** the definition of `ind(f)`/`ind(N)` with the lattice-point convention — previously the
> flagged unknown, now pinned verbatim: GMN counts **ON-OR-BELOW** (Remark 4.14 "below or on";
> discriminating witness `x² + 6x + 36` over `ℤ₃` recorded there: one depth-1 descend, true
> `ind = 1` = on-or-below count, strictly-below count 0);
> **(P2)** the index–discriminant identity
> `v_p(disc f) = 2·ind(f) + Σ_i v_p(disc L_i) ≥ 2·ind(f)` (GMN §4.2 verbatim "well-known
> relationship" for irreducible `F`; reducible case via GMN Def 4.11 + elementary
> `disc(PQ) = disc P · disc Q · Res(P,Q)²`; independent textbook pin still TO-VERIFY, see (P2));
> **(P3)** the per-descend-event increment `ind_r ≥ 1`, via the ON-SIDE lattice point
> `(s+e, u+(d−1)h)` of the descend side (`d(S) ≥ 2`) — a point ON the polygon, so it needs
> (P1)'s on-or-below convention.
> *Faithfulness note for the future axiom:* the repo already carries the index theorem in
> arising-key form (`omReadValuation_lt_of_certLevel_fkeyed`); the new declaration should be the
> DEPTH consequence only — "still descending at depth d ⟹ v_p(disc f) ≥ 2d" — existence-free,
> measure-free, pointwise, hence auditable by the standard triple test; the remaining
> declaration-time caveats (`v_r`-normalized heights; representative-dependence of `ind_t`; root
> openings are not events, Def 1.3) are listed at (P3).

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
> (Immediate corollary: `μ{disc = 0} = 0`.)

> **Corollary 3.4 (the descending envelope).** By 3.2 + 3.3, the still-descending-at-depth-`d`
> set `Desc_d := ⋃_{s open, d(s) ≥ d} S_s` satisfies
> ```
>   μ(Desc_d) ≤ (n−1) · p^{ −⌈ (2d − n·v_p(n)) / (n−1) ⌉ }  → 0 geometrically in d.          (3c)
> ```
> **Nothing else is used**: no per-depth count identity, no pivot, no ×q, no child-law
> identification — (3c) is a POINTWISE inclusion `Desc_d ⊆ {v_p(disc) ≥ 2d}` [MONTES] followed by
> an unconditional measure bound [COUNT].

> **Lemma 3.4′ (level tail — the undecided-mass envelope). Status split: (a) `n = 2` PROVED with
> explicit constants [COUNT via 2.3]; (b) whole-window linear fragment, general `n`, PROVED with
> explicit constants [COUNT via 2.3]; (c) prefixes leaving the fragment [OPEN-D4 / D3 / D5].**
> Let `Undec(N)` be the level-`N`
> undecided set (stuck + tail in Lemma 3.1). By (3a), N-stability (Thm 2.1) and
> `μ(non-terminating) = 0` (3.2 + 3.3),
> ```
>   μ(Undec(N)) = Σ_{s terminating, N₀(s) > N} μ(S_s)                                       (3e)
> ```
> — the level tail IS the threshold-ordered tail of the stratum series. This is the quantitative
> link Lean's finite-`N` counting needs (`hExhaust`, Wave 6).
>
> **(a) `n = 2`, all `p`, all `N ≥ 4` [COUNT via 2.3 — proved]:**
> ```
>   μ(Undec(N)) ≤ (⌊N/2⌋ + 1) · p^{−(N−1)}     (full box; cluster-conditional: · p^{−(N−2)}).
> ```
> *Proof.* Separable root reads decide at level 1, so `Undec(N)` lies in the `p` root-cluster
> translates (total mass `p^{−1}`). Work in one cluster frame with remaining budget `B`
> (initially `B = N`), conditional measure on the fresh box `{v(a₁) ≥ 1, v(a₀) ≥ 1}`. (i) *Stall
> containment:* the Def-1.2 reader stalls at this frame only if `v(a₀) ≥ B − 1` — in every other
> configuration (one-sided even/odd, two-sided, descend-certified) all needed digits (vertex
> heights, endpoint comparisons `2v(a₁)` vs `v(a₀)`, residual digits) sit at positions
> `≤ v(a₀) + 1 ≤ B − 1` — an event of conditional mass `≤ p^{−(B−2)}`. (ii) *Per-step ledger:* a
> certified full-side descend at slope `m` has EXACT conditional mass `(1−1/p)·p^{−(3m−1)}`
> summed over `c̃` (Lemma 2.3 = §7 Cases A/B), needs `2m ≤ B − 1` to certify, and hands the child
> frame the budget `B − 2m` with the fresh-box UNIFORM conditional law (Lemma 2.3's
> measure-isomorphism — this is what makes the chain rule exact). (iii) *Chain sum:* each
> undecided `f` stalls at exactly one frame of its deterministic read, so, over certified chains
> `(m₁,…,m_k)` (which satisfy `2Σmᵢ ≤ N − 1` — each step certifies with `2m ≤ B − 1`, leaving
> bottom budget `≥ 1`, per (ii); relaxed to the weaker `2Σmᵢ ≤ N` in the display — deeper chains
> cannot certify within budget and their `f`'s already stalled shallower),
> ```
>   μ_cond(Undec(N)) ≤ Σ_{k≥0} Σ_{2Σm≤N} ∏ᵢ (1−1/p)p^{−(3mᵢ−1)} · p^{−(N−2Σmᵢ−2)}
>                    ≤ p^{−(N−2)} · Σ_{k≤N/2} [Σ_m (1−1/p)p^{−(m−1)}]^k
>                    = p^{−(N−2)} · (⌊N/2⌋ + 1),
> ```
> (the second `≤` relaxes the joint constraint `2Σmᵢ ≤ N` to independent unrestricted sums over
> the `mᵢ`, keeping only `k ≤ N/2` — an over-count), and the last `=` holds since
> `Σ_{m≥1} (1−1/p)p^{−(m−1)} = 1` EXACTLY. Multiply by the cluster mass `p^{−1}`. ∎
> [The exact criticality `Σ_m(...) = 1` is the `s = 2` tower's signature: undecidedness drains
> like `N·p^{−N}` — geometrically with one polynomial factor, not faster.]
>
> **(b) whole-window linear fragment, general `n` [COUNT via 2.3 — PROVED, explicit constants;
> rewritten this revision, 2026-07-22, after pass-2 found the old assembly incomplete].**
> **The fragment `F₀`** := read histories all of whose descend events are whole-window full-side
> linear (Lemma 2.3's scope: at a `δ = 1` root cluster, every descend a single side `(0, sm)–(s,0)`
> with residual `(y−c̃)^s`). In `F₀` a window never branches before descending, so each opened
> cluster runs a CONSTANT-size chain until it terminates or stalls — there is no mixed-size
> assembly (the old text's "mixed sizes" and `n^n` branch-shape count are gone, not hidden).
> `Undec_F(N)` := the level-`N` undecided `f` whose level-`N` read history lies in `F₀`; the
> complement `Undec(N) ∖ Undec_F(N)` (some read outside `F₀`: a `deg φ ≥ 2` descend → class 3, or
> a partial-side/mid-polygon linear descend → D3/D5) is (c)'s scope, NOT bounded here. At `n = 2`,
> `Undec_F = Undec`. Claim:
> ```
>   μ(Undec_F(N)) ≤ 6 · (⌊N/2⌋ + 1) · p^{−N}         for every n ≥ 2, p, N ≥ 1.
> ```
> *Proof.* Every `f ∈ Undec_F(N)` stalls at some cluster of its (deterministic) read: at a residue
> point `c ∈ F_q`, cluster size `s ∈ {2,…,n}`, after a certified chain `(m_1,c̃_1),…,(m_k,c̃_k)`
> (`k ≥ 0`) of whole-window descends. Union bound over `(c, s)` and chains. Fix `(c, s)`; work in
> the cluster's window coordinates `a_0,…,a_{s−1}` (the φ-adic/Taylor development at `c`, a
> unipotent-triangular level-preserving function of `f`'s coefficients — Thm 2.1), which are
> jointly uniform at level `N` conditionally on any fixed values of the remaining development
> coordinates; every event below is a digit event in these `s` coordinates alone, so its mass is
> computed exactly in this frame and all sibling conditions (other clusters, multiplicity-
> exactness, root shape) are DROPPED — an upper bound; no L1 and no cross-cluster independence is
> used. Three displayed ingredients:
> (i) *Stall containment.* At a frame of budget `B` (free coordinates staircase-uniform with
> minimum level `B`, Lemma 2.3(5)), if `v(a_i) < B` for every `i < s` then the read COMPLETES —
> whatever its polygon shape (multi-side terminating reads included): all heights are visible
> (`v(a_i) < B ≤` known level; the endpoint `v(a_s) = 0` is conditioned tail data), the polygon
> is determined, every residual digit sits at an on-line position `≤ v(a_0) < B` (the polygon's
> maximal height), and a certified descend's digits (S1)∧(S2) sit at positions
> `≤ sm ≤ v(a_0) < B`. Hence
> ```
>   {stall at this frame} ⊆ ⋃_{i<s} {v(a_i) ≥ B},   conditional mass ≤ s · p^{−(B−1)}      (3f)
> ```
> (each event: one coordinate, `B−1` further zero digits beyond the cluster digit, within the
> staircase's known levels since `M_i ≥ B`).
> (ii) *Per-step ledger.* A certified whole-window descend at slope `m` has exact conditional
> mass `(q−1)·p^{−m·s(s+1)/2}` summed over the `q−1` values of `c̃` (Lemma 2.3, (2.3c)), and hands
> the child a budget smaller by `s·m` with the staircase-cluster UNIFORM law (Lemma 2.3(4)–(5) —
> this is what makes the chain product exact, per stratum, with no independence assumption).
> Certification within budget forces `s·Σ_t m_t ≤ B − 1` (Lemma 2.3 leaves the bottom frame a
> budget `≥ 1`); this is relaxed below to the weaker `s·Σ_t m_t ≤ B`, so `k ≤ B/2`. The
> budget-recovery-adjusted per-step factor is
> ```
>   r_s := Σ_{m≥1} (q−1) p^{−m·s(s+1)/2 + sm} = (q−1)/(p^{s(s−1)/2} − 1)
>        = 1 at s = 2 (critical),  < 1 for s ≥ 3  (e.g. r_3 = 1/(p²+p+1)).               (3g)
> ```
> (iii) *Chain sum.* With `B = N` at the top frame (the window coordinates are exact level-`N`
> data — no level loss), summing over chains and applying (3f) at the stalled frame with budget
> `N − sΣm`:
> ```
>   μ_cond(stall in this cluster) ≤ Σ_{k≥0} Σ_{sΣm≤N} ∏_t (q−1)p^{−m_t s(s+1)/2} · s·p^{−(N−sΣm−1)}
>                                 ≤ s·p^{−(N−1)} · Σ_{k≤N/2} r_s^k
>                                 ≤ s·(⌊N/2⌋+1)·p^{−(N−1)},                              (3h)
> ```
> the second `≤` relaxing the joint constraint `sΣm ≤ N` to independent unrestricted sums over
> the `m_t` (keeping only `k ≤ N/2` — an over-count), the third using `r_s ≤ 1` (equality only
> at `s = 2`, which is what forces the polynomial factor).
> *Assembly* (all displayed, no "similarly"): the cluster-box mass at `(c, s)` is `p^{−s}`
> (`s` cluster digits), so
> ```
>   μ(Undec_F(N)) ≤ Σ_{c∈F_q} Σ_{s=2}^{n} p^{−s} · s·(⌊N/2⌋+1)·p^{−(N−1)}
>                 ≤ q · 6p^{−2} · (⌊N/2⌋+1) · p^{−(N−1)} = 6·(⌊N/2⌋+1)·p^{−N},
> ```
> where `Σ_{s≥2} s·p^{−s} ≤ 6p^{−2}` (equality-check at `p = 2`: `Σ_{s≥2} s·2^{−s} = 3/2 = 6·2^{−2}`;
> the sum decreases in `p`). ∎
> (`n = 2` cross-check: (b) gives `6(⌊N/2⌋+1)p^{−N}`, (a) gives `(⌊N/2⌋+1)p^{−(N−1)}` — both
> valid, neither implies the other; (a)'s constants stay the sharp ones for Wave 5/6 at `n = 2`.)
>
> **(c) general `n`, read-prefixes leaving the fragment — precisely scoped opens.** For prefixes
> whose exit step is a `deg φ ≥ 2` descend, the same scheme needs, across that descend, an upper
> bound `μ(prefix ∧ child-read conditions) ≤ C·p^{−(A(prefix) + child exponent)}` — the one-sided
> (upper-bound) half of D1's development-digit ledger. Single-read conditions have exact product
> mass in their own development coordinates [COUNT], but the JOINT of parent and child conditions
> across a `deg φ ≥ 2` descend is exactly D1's content (GAP-2's count half); no elementary route
> is known. **OPEN-D4 :=** for class-3 read-prefixes, `μ(prefix) ≤ C(n)·p^{−A(prefix)}` with `A`
> the prefix's ledger exponent (implied by JOINT-D1, whose conditional-on-ancestors form prices
> the whole prefix; the single-read D1-marginal does NOT imply it — the joint across reads is
> exactly what it lacks; strictly weaker than joint-D1). For prefixes whose exit step is a
> partial-side or mid-polygon LINEAR descend, the needed one-sided bound is the corresponding
> upper-bound half of **D3 / D5** (strictly easier than D4). None of D3/D4/D5 is needed for
> Waves 5–6 — (b) covers `hExhaust` on the whole-window linear fragment (§8) — and rate-free
> exhaustion (Thm 3.5(i)) needs none of them.
>
> *Mechanism correction (pass-1).* The previous sketch routed (3e) through "undecided ⟹ two
> roots at mutual valuation `≥ (N−consumed)/n` ⟹ `v_p(disc)` large" plus the classical
> polygon⟹root-valuation import. That pointwise route is FALSE for degree-1 high sides: at
> `n = 2`, `v(a₁) = 1`, `v(a₀) ≥ N` with `N ≥ 3` is undecided under the strict Def-1.2 reader at
> that level, yet `v_p(disc) = 2·v(a₁) = 2` for odd `p` (the `N ≥ 3` matters: it forces
> `v(4a₀) ≥ 3 > 2 = v(a₁²)`, so no cancellation in `disc = a₁² − 4a₀`; at `N = 2` the two terms
> can cancel to `v(disc) > 2`; the cleanest witness is `a₀ = 0`, `f = x² + a₁x` with `v(a₁) = 1`,
> undecided at EVERY level) — the unread height measures root-to-CENTER
> depth, not root-to-root depth. The counting proof above replaces it; the classical NP import
> drops out of 3.4′ entirely. *Order-1 Lean instance of the tail half:*
> `Drainage.tendsto_tailDensity_zero`; the order-1 STUCK mass is the `N`-independent self-loop
> constant (`Drainage.tendsto_undecidedDensity`) — which is exactly why finite-ORDER reading does
> not drain and DEPTH (this note's tree) is the right exhaustion variable.

### 3.5 Exhaustion

> **Theorem 3.5 (decomposition of the full decided density) — split into three statements of
> distinct strength (this revision, 2026-07-22; pass-2 found the old single statement asserting
> (‡)-masses for EVERY stratum unconditionally, which contradicted the D1/D2 ledger).**
>
> **(i) Unconditional qualitative decomposition [COUNT + MONTES #4 + #5 + #6 — NO open D-lemma,
> NO (‡) values, NO rate; #4 (leaf/type faithfulness) enters the per-type clause `σ(s) = σ`,
> #5 (lift invariance) identifies the canonical-lift tree with a Montes run — boundary #5's
> exact GMN pin is TBD at axiom-declaration time (standard Montes content, citation pending),
> #6 is termination + depth⟹disc].** The terminating strata are pairwise disjoint and, with their ABSTRACT
> masses `μ(S_s)` (well-defined: each `S_s` is a finite union of cylinders, Thm 2.1),
> ```
>   μ(box) = Σ_{s terminating} μ(S_s),   and per type:
>   ρ_dec(n, σ; p) = Σ_{s terminating, σ(s) = σ} μ(S_s)      (σ(s) as in §6),               (3d)
> ```
> the series converging absolutely (positive terms). Moreover `μ(Undec(N)) → 0` as `N → ∞`
> WITHOUT any rate input: decisions are stable under refinement (a read visible at level `N`
> stays visible at `N+1`), so `Undec(N)` is non-increasing with intersection ⊆ (non-terminating
> ∪ `Z_∞`), which has measure zero by 3.2 + 3.3 — monotone convergence. Hence the level-`N`
> normalized decided counts converge to (3d).
> *Proof.* Disjointness: distinct read-histories are incompatible outcomes of the same
> deterministic reader [COUNT]. Cover: `f` outside `Z_∞ ∪ {disc = 0}` (measure zero, 3.3) has a
> terminating history by Lemma 3.2 [MONTES]. Countable additivity of Haar measure gives (3d);
> the tail statement is the displayed monotone-convergence argument. ∎
>
> **(ii) Quantitative form on the proved fragment [COUNT via 2.3 + L1].** For class-1 strata and
> class-2 WHOLE-WINDOW towers, each `μ(S_s)` equals its (‡) value (Thm 2.2.1–2, Lemma 2.3), and
> the level-`N` decided count over these strata equals the partial sum over `{s : N₀(s) ≤ N}` up
> to the explicit envelope errors (3c) + 3.4′(a)/(b). This is the exact input Wave 6's `hExhaust`
> consumes at `n = 2` (where the fragment is everything).
>
> **(iii) Conditional quantitative form [OPEN-gated].** For class-3 strata the (‡) values of
> `μ(S_s)` are conditional on JOINT-D1 (+ D2 in Lean; a whole-stratum (‡) value is a joint
> statement, so the marginal form would not suffice); for class-2 partial-side/mid-polygon strata, on
> D3/D5; the corresponding level-tail RATES are conditional on D4 (resp. the D3/D5 upper-bound
> halves), per 3.4′(c). Nothing in (i) depends on (iii).
>
> Import summary: the [MONTES] content in (i) is termination + depth-index (3.2, boundary #6),
> lift-invariance (Def 1.2, boundary #5), and — for the per-type clause of (3d) — leaf/type
> faithfulness (§6, boundary #4); the only [OPEN] content anywhere is confined to (iii).
> **Exhaustion itself needs neither D1 nor D2 nor any rate** — that is exactly statement (i).

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
   FACT B is explained by Lemma 2.3's child-uniformity, not by this grouping: the
   recenter–rescale bijection carries the conditional measure on each depth-`k` descend stratum
   to the UNIFORM measure on a fresh cluster box, so the conditional probability that the next
   verdict is a further descend is the bare fresh-box constant `slBox` — matching the wall's
   measured `1/8` (p=2) and `1/27` (p=3). The regrouped `q·slBox` is a property of the engine's
   normal form, not of any stratum's conditional law.
4. **Honest residue.** The wall's deep reason ("the ×q is measure-theoretic") survives in exactly
   one place: for `deg φ ≥ 2` descents the per-stratum count formula (class 3) is OPEN-D1 — the
   same content as GAP-1/GAP-2's count-level half (with the linear-but-cross-frame shadows D3/D5
   as its `deg φ = 1` siblings). For WHOLE-WINDOW full-side `deg ψ = 1` chains (the wall's
   own `e=1` self-loop regime!) Lemma 2.3 now proves it elementarily — consistent with the wall, because Lemma 2.3
   produces per-STRATUM masses in fresh frames, not the fixed-box per-depth census the wall
   demanded. If D1 turns out to genuinely require non-Montes measure content, that is precisely
   BB3_infinity GAP-1/GAP-2 resurfacing — the finding is: **it is confined to D1 (and its
   linear cross-frame shadows D3/D5), and touches neither exhaustion (§3) nor the whole-window
   linear towers (class 2's proved core, all of `n = 2`).**

---

## 4. The series and its rationality

> **Theorem 4.1 (convergence, per fixed p) [(b); split this revision, 2026-07-22 — the old
> single statement priced the `H`-tail through the (‡) ledger without conditioning].**
> (i) [UNCONDITIONAL] The series (3d) converges absolutely (positive terms, total ≤ 1 — Thm
> 3.5(i)); and the DEPTH tail is geometric: `Σ_{s terminating, d(s) ≥ d} μ(S_s) ≤ μ{v_p(disc) ≥ 2d}
> ≤ (n−1)·p^{−⌈(2d − n·v_p(n))/(n−1)⌉}` — the pointwise inclusion of Lemma 3.2 applies verbatim
> to strata that PERFORMED `≥ d` descend events, terminating or not, so this is Corollary 3.4's
> bound [MONTES 3.2 + COUNT 3.3], no (‡) input.
> (ii) [proved fragment] Within class 1 and class-2 whole-window towers, the HEIGHT tail is also
> geometric with explicit constants: heights enter `A_s` linearly with positive weight ((‡),
> proved there via Thm 2.2.1–2 + Lemma 2.3), so the tail beyond max height `H` at bounded depth
> is `O(p^{−c'·H})` [COUNT].
> (iii) [conditional] The same two-parameter bound `O(p^{−c·d} + p^{−c'·H})` over ALL strata
> (class 3, partial-side/mid-polygon class 2) holds GIVEN the one-sided ledger halves (D4, resp.
> D3/D5 upper bounds) — the `H`-tail of an unproved-(‡) stratum family has no unconditional
> price yet.

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
> (i) **H-ladders** (heights within one read, everything else fixed) — split like Thm 4.1:
> (i-a) [proved fragment] within class 1 and class-2 WHOLE-WINDOW towers the masses are
> `const · p^{−(linear in H)}` by the PROVED (‡) instances (Thm 2.2.1–2, Lemma 2.3), so each
> ladder sums to a rational function with denominator `1 − q^{−(ladder weight)}` [COUNT] —
> (a)/(b): exactly the engine's `_geom_sum_inf`/`_cone_sum` and L5fix(d); Lean pattern exists
> (window-K staircases, `normSum_omMenuW3_mono`; the K→∞ sum is Wave 6).
> (i-b) [conditional] for class-3 ladders the same closure holds GIVEN joint-D1 (+ D2 in Lean); for
> the class-2 partial-side/mid-polygon portions, GIVEN D3/D5 — the (‡) form there is exactly
> what those opens supply. Multi-side reads sum over the strictly-decreasing-slope cone via the
> gap substitution — engine `_sum_by_gaps`, pure lattice algebra [COUNT].
> (ii) **Depth towers**: by Lemma 2.3, a WHOLE-WINDOW full-side `deg ψ = 1` descend multiplies
> masses by a fixed per-step total ratio (e.g. `Σ_m (1−q^{-1})q^{−(3m−1)} = 1/(q²+q+1)` at
> `n=2`); chains resum geometrically [COUNT via 2.3 — PROVED]. Partial-side linear descents
> (`n ≥ 3` only) need [OPEN-D3]; mid-polygon full-side linear descents (`n ≥ 3` only) need
> [OPEN-D5]. For `deg φ ≥ 2` descents the same closure holds GIVEN joint-D1 (the
> per-step masses then being class-3 (‡) values with base-changed `q ↦ q^{w}`, each conditional
> on its ancestor cylinder — the conditional-on-ancestors form is exactly what joint-D1
> supplies) [OPEN-D1].
> (iii) Everything else (slopes' denominators, shapes, residue degrees, number of sides, depth of
> the SHAPE tree after quotienting ladders/towers) is finite and p-independent — (a): L5fix(b),
> `HUMAN_PROOF §9`; the menu `T_n` finiteness.

> **Theorem 4.5 (conditional rationality; agreement with the engine) [(b), conditional].** Modulo
> D1+D2 (the class-3 strata) AND D3+D5 (the class-2 partial-side/mid-polygon remainder), the D1
> gate meaning JOINT-D1 (§2's restated form — under the joint ledger every class-3 stratum's (‡)
> mass and its ladder/tower closures (Claim 4.4) follow, so the gate is SUFFICIENT; the marginal
> form alone would not be): for each
> `n, σ` the sum (3d), grouped by shape and resummed by 4.4, is
> a single rational function of `q` evaluated at `q = p`, equal to the engine's
> `alpha_full(n)[σ]` (the `beta_e` fixpoint assembly of `om_density_engine.py`) — the engine
> normal form is a REGROUPING of the stratum series (a rearrangement of an absolutely convergent
> positive series [justified by Thm 4.1]): verified symbolically at `n = 2` (§7 Case A — both
> groupings give `q/(q+1)`), conditional at general `n`; the resummation's pivot (`(⋆⋆)` of
> BB3_infinity §4) is `1 − w(e) ≠ 0`.
> Separately and UNCONDITIONALLY [COUNT+MONTES]: the partial sum over class-1 strata and class-2
> WHOLE-WINDOW towers is a single rational function of `q` (the proved fragment; at `n = 2` the
> fragment is everything, so there the full statement holds unconditionally). p-independence
> of the assembled function: derived, never imported (the GMN-citations discipline: per-p imports
> of p-free shape).

---

## 5. The Montes-axiom boundary (per ingredient)

| # | Ingredient | Class | Citation / proof locus |
|---|---|---|---|
| 1 | Root read + Hensel measure split (L1) | [MONTES]/(a) solid | `HUMAN_PROOF §3`; Igusa §7.4; Lean order-0 legs proved |
| 2 | φ-adic development = fixed triangular bijection | [COUNT] | Def 1.2.1 (division by fixed monic; elementary) |
| 3 | Polygon/residual READ definitions at order r | [MONTES defs] | GMN Def 2.3/2.5/2.21; order ≤ 1: repo `CellMenu` [COUNT] |
| 4 | Leaf dichotomy + (e,f) product law | [MONTES] | Cor 1.20 (order 1), Thm 3.1/3.7 + Cor 3.8 (order r); repo axiom `om_leaf_faithful` is the menu-scoped instance — extend fiber-scoped per new menus (Wave 4/5 pattern, W3c re-scope precedent) |
| 5 | Lift admissibility/invariance (canonical lifts read the same tree) | [MONTES] | GMN §2.4–3 representatives; exact pin TBD at declaration (flag) |
| 6 | Termination + depth ≤ ind ≤ ½·v_p(disc) | [MONTES] | Thm 4.18 + Cor 4.19 + §-intro bound; **pins (P1)–(P3), `GMN_citations.md` §"§4 index machinery"** (ind definition + ON-OR-BELOW convention, now pinned verbatim; index–disc identity, textbook pin TO-VERIFY; per-event increment via the on-side witness point); declare as pointwise depth⟹disc (Lemma 3.2 form); repo precedent `omReadValuation_lt_of_certLevel_fkeyed` |
| 7 | Discriminant tail (3b) | [COUNT — proved here] | Lemma 3.3 (elementary; Lean-able: resultant product + Fubini + ball bound) |
| 8 | Per-level partition (3a) | [COUNT — order-1 proved] | `stratumCount1_partition`; general = same pattern |
| 9 | Per-stratum counts, classes 1–2 | [COUNT — class 1 + whole-window class 2 PROVED] | §2 Thm 2.2.1–2, Lemma 2.3 (whole-window towers, general `s,m,depth` — proved this revision); class-2 remainder: partial-side = **[OPEN-D3]**, mid-polygon full-side = **[OPEN-D5]**, both `n ≥ 3` only |
| 10 | Per-stratum counts, class 3 (`deg φ ≥ 2`) | **[OPEN-D1]** | the development-digit ledger, JOINT form (restated pass 4 — whole-stratum counts need the joint, not the single-read marginal); = count-level GAP-1/GAP-2 (`BB3_infinity §4.2/§8`); route: RESTART_LEMMA triangular coordinates |
| 11 | Pool counts over `F_{q^w}` in Lean | **[OPEN-D2]** | math (a)-known (L3 all finite fields); Lean `UnramifiedBase` tower work |
| 12 | Residual equidistribution as an AXIOM | **excluded** | standing non-import (no GMN counterpart — `M6_lemma.md`, PROJECT_STATE); its role is absorbed by D1 as a provable count statement |
| 13 | Geometric/cone resummation | [COUNT] | §4.4; engine `_sum_by_gaps`; L5fix(d) |
| 14 | Exhaustion (3d), abstract masses + qualitative tail | [COUNT+MONTES #4/#5/#6] | Thm 3.5(i) — needs NO open D-lemma; boundary #5's exact GMN pin is TBD at axiom-declaration time (standard Montes content, citation pending); the (‡)-valued quantitative forms are 3.5(ii) [proved fragment] and 3.5(iii) [conditional] |
| 15 | Level-tail rate (3e) | [COUNT via 2.3 — proved on the whole-window linear fragment, explicit constants; out-of-fragment rates **[OPEN-D4 / D3 / D5]**] | Lemma 3.4′(a)/(b)/(c) — Waves 5–6 need only the fragment |

**Answer to the task's (iii):** nothing in the decomposition/exhaustion/convergence genuinely
requires non-Montes content. The only candidate for genuinely-new measure content is D1 (the
JOINT count ledger at `deg φ ≥ 2` — believed provable as pure counting via triangular
coordinates, but open; if
it fails, that failure IS GAP-1/GAP-2 and must be reported as such); its three
shadows D3 (partial-side linear window-freeness), D5 (mid-polygon full-side linear cross-frame
freeness) and D4 (class-3 prefix upper bound, Lemma 3.4′(c)) add no new candidate content —
D4 is implied by JOINT-D1 (Lemma 3.4′(c); the implication survives ONLY in the joint form — a
single-read marginal does not bound a multi-read prefix); D3/D5 are expected to follow from an
extension of the D1
ledger method (no formal reduction supplied). The
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
count form before any Lean work on class-3 strata** (a depth-0, single-development instance —
it exercises D1-marginal conditioned on the root read; the joint ledger at depth ≥ 1 needs a
deeper class-3 probe on top).

---

## 8. Verdict and recommended wave order

**Wall verdict: SIDESTEPPED** (§3.6) — the decomposition never forms a per-depth fixed-box census
against the pivot; exhaustion runs through the pointwise discriminant inclusion (Lemma 3.2
[MONTES]) plus the elementary tail (Lemma 3.3 [COUNT]); the engine's ×q-exposed tower is recovered
only as a rearrangement of an absolutely convergent series of exactly-counted stratum masses. The
wall's content survives, confined to OPEN-D1 (class-3 count forms), which exhaustion does not need.

**The three claim classes (contents; stratum classes 1/2/3 are the PARTITION of Thm 2.2):**
- **[COUNT/proved]:** development & recenter triangular bijections; strata are N-stable cylinder
  unions; per-stratum counts for class 1 (PROVED in Lean for banked menus) and all WHOLE-WINDOW
  `deg ψ = 1` towers (Lemma 2.3, now a full digit-by-digit proof at general `s, m`, depth —
  includes ALL of n=2); the per-level partition (3a) (order-1 PROVED); the
  discriminant tail (3b); the level-tail rate (3.4′) with explicit constants at `n = 2` and on
  the whole-window linear fragment (`6(⌊N/2⌋+1)p^{−N}`); the geometric/cone resummations;
  convergence and qualitative exhaustion (Thm 3.5(i), rate-free).
- **[MONTES/axiomatizable]:** Hensel/L1 root split; order-r read definitions; leaf dichotomy +
  (e,f) product law (Cor 1.20/3.8 — extend `om_leaf_faithful` fiber-scoped per menu wave); lift
  invariance; termination/depth ≤ ind ≤ ½v_p(disc) (Thm 4.18/Cor 4.19 — new axiom candidate in the
  pointwise depth⟹disc form).
- **[OPEN]:** **D1** — the development-digit ledger for `deg φ ≥ 2`, in the JOINT form (all
  reads of a history jointly free — restated pass 4; the single-read marginal is a corollary,
  D1-marginal) (count-level GAP-1/GAP-2;
  believed pure counting via fixed triangular coordinates; Case E is the empirical gate for its
  depth-0 instance);
  **D2** — L3 pool counts over `F_{q^w}` in Lean (math known; tower vocabulary work);
  **D3** — partial-side linear descend window-freeness (`deg φ = 1` mini-analogue of D1;
  `n ≥ 3` only, not needed for Wave 5); **D4** — the class-3 prefix upper bound / level-tail
  rate (Lemma 3.4′(c); implied by JOINT-D1 only — the marginal does not give it; not needed for
  Waves 5–6); **D5** — mid-polygon full-side
  linear descend cross-frame freeness (`n ≥ 3` only; the exact failing step of extending
  Lemma 2.3 past whole-window sides — the diagonal rescale absorbs the whole window or nothing;
  not needed for Waves 5–6).

**Recommended wave order** (each preceded by its §7 numeric gate):
1. **Wave 4 (mixed-e, order ≤ 1)** — class-1 strata only: menu = multi-slope shapes, counting legs
   already banked (`hnode_multiSideProduct`); gate Case D. Lowest risk.
2. **Wave 5 (μ≥2 linear descents)** — Lemma 2.3 in Lean + the depth-indexed menu for `n=2`-style
   whole-window recenter chains; gates Cases A/B/C. Closes the FIRST complete per-type tower
   (`n = 2` all types, exact `q/(q+1)`-family values) with no new axiom beyond the depth⟹disc
   declaration (boundary #6) if the envelope is wired.
3. **Wave 6 (series assembly)** — infinite menu with per-level finite support; partial sums = the
   window staircases (Wave-3 pattern); exhaustion clause via (3a)+(3c)+(3.4′) discharging
   `hExhaust` on the linear-tower fragment.
4. **Wave 7 (class 3 / D1)** — only after Case E passes and D1 is proved on paper for one `deg φ = 2`
   order-1 read (the D1-marginal instance; the Wave-7 target is the JOINT ledger along full
   class-3 histories); if D1 resists pure counting, STOP and report it as GAP-1/GAP-2
   resurfacing — do not axiomatize it (non-import #12).

**Single riskiest open lemma: OPEN-D1** (the development-digit ledger at `deg φ ≥ 2`, joint
form). Everything
else in this note is either proved, provable by the exhibited elementary arguments, or a
faithful-scope extension of the existing Montes axiom pattern.

---

## 9. Verification record

**Pass 1 (adversarial verification, fresh context, 2026-07-22): NO CRITICAL ERRORS; 8
justification gaps + 6 minor defects.** The verifier's independent confirmations: the Case D
census (`n = 4, p = 3` mixed-e multi-slope) EXACT (1458 at `N = 4`); the X²−12 stratum (Case C)
mass `1/16` cluster-conditional EXACT; the 46-stratum depth-3 census EXACT; the
discriminant-tail (3b) numerics PASS; the pointwise inclusion `Desc_d ⊆ {v_p(disc) ≥ 2d}` —
ZERO failures.

**Fixes applied 2026-07-22 (this revision):**
1. *(blocking for the W5/W6 axiom)* The depth⟹disc axiom's three dependency pins **(P1)–(P3)**
   added as `GMN_citations.md` §"§4 index machinery", sourced from a fresh re-extraction of
   arXiv:0807.2620v2: the ON-OR-BELOW convention RESOLVED verbatim (Remark 4.14 "below or on"),
   the verifier's discriminating witness (`x² + 6x + 36`/ℤ₃) recorded, the index–disc identity
   pinned to GMN §4.2's verbatim "well-known relationship" (independent textbook pin still
   TO-VERIFY), the per-event increment's on-side witness point verified. Def 1.3 now EXCLUDES
   root cluster-openings from descend events (counterexample `x² − p`, `p` odd, recorded);
   Lemma 3.2 and boundary #6 rewired to the pins.
2. Thm 2.2 class 2 / Claim 4.4(ii) / §8 restricted to FULL-SIDE linear towers (all of `n = 2`,
   all Wave-5 needs); partial-side named **[OPEN-D3]**.
3. Def 1.2.3 misattribution fixed: the residual polynomial lives in `F_r[y]` (GMN Def 2.21);
   the phantom extension field deleted; `Q_r′ → Q_r` throughout.
4. Lemma 3.4′ re-proved: `n = 2` with fully explicit constants and the full-side linear fragment
   with crude explicit constants, both [COUNT via 2.3]; the old two-close-roots mechanism shown
   FALSE for degree-1 high sides and documented; the class-3 rate scoped as **[OPEN-D4]**; the
   classical-NP import dropped from 3.4′ (Thm 3.5's import list updated accordingly).
5. Cosmetics: Thm 4.5 pivot corrected to `1 − w(e)` and the engine-agreement claim downgraded to
   "regrouping, verified symbolically at n=2, conditional at general n"; §3.6.3 FACT-B mechanism
   corrected (Lemma 2.3 child-uniformity ⟹ bare `slBox`, matching the wall's 1/8 and 1/27);
   Lemma 2.3 wording fixed (triangular with diagonal `p^{m(s−i)}`, measure-scaling, not
   unipotent); Lemma 3.3's `μ(Z_∞)` parenthetical dropped; Thm 2.1's bijection line qualified to
   the unipotent steps (rescale steps are `p`-power-to-one across levels).

**Pass 2 (adversarial verification, fresh context/model, 2026-07-22): pass-1 fixes ACCEPTED**
(per-descend lattice mechanism, reducible-disc derivation via Def 4.11 + `disc(PQ) =
disc P·disc Q·Res²`, the `n = 2` tail arithmetic, the root-opening counterexample), **with NEW
findings:** (1) BLOCKING — 3.4′(b)'s general-`n` bound not proved (factors + mixed-size assembly
incomplete); (2) BLOCKING — old classes 1/3 overlapped, letting open extension-field reads carry
"proved" labels; (3) BLOCKING — Thm 3.5 asserted (‡)-masses for EVERY stratum unconditionally
while D1/D2 were open; (4) substantial — (4a) Lemma 2.3's general-`s` child uniformity asserted
from the `n = 2` ledger + "identical in structure", not proved; (4b) Thm 3.5's quantitative
clause cited 3.4′ with no class restriction; (4c) Thm 4.1's `H`-tail priced through (‡) without
conditioning; (5) small — the old-mechanism witness needed `N ≥ 3` or `a₀ = 0`.

**Fixes applied 2026-07-22 (second revision):**
1. *(4a — the central repair)* Lemma 2.3 re-proved digit-by-digit at general `s`, general `m`,
   general depth: the coefficient identity (2.3a) (unipotent binomial shift × diagonal
   `p^{m(s−i)}`), the monotone-STAIRCASE bijection (child levels `M_k = N − m(s−k)`, level pin
   `N′ = N − sm`), the residual identity (2.3b) `R_S(y) = ḡ_w(y−c̃)` making the stratum's
   residual condition EXACTLY the child cluster condition, the exact mass (2.3c)
   `p^{−s−m·s(s+1)/2}` per `(m,c̃)`, and the chain corollary — all verified by brute force at
   `s = 3` (five configurations) and in the embedded-window form (unit `a_s`, `p`-divisible
   tails, `n = 4,5`; five more). **Honest scope boundary found:** the proof works iff the descend
   side spans the WHOLE window (the diagonal rescale must absorb every window coordinate);
   mid-polygon full-side descends (`n ≥ 3` only) are the new **[OPEN-D5]** with the failing step
   named (cross-frame joint freeness). All of `n = 2` and Waves 5–6 sit inside the proved scope.
2. *(1)* 3.4′(b) restated on the fragment `F₀` (all descends whole-window) and re-proved with
   displayed identities (3f)–(3h), no "similarly": stall containment (stall ⟹ some window
   coefficient has `v ≥ B`), per-step ledger from (2.3c) with the critical factor
   `r_s = (q−1)/(p^{s(s−1)/2}−1)`, chain sum, and an assembly that needs NO L1 and no branch-shape
   count (in `F₀` windows never branch before descending — the old `n^{n+1}(N+2)` bound's
   mixed-size assembly is gone, replaced by `6(⌊N/2⌋+1)p^{−N}`); out-of-fragment prefixes
   explicitly routed to (c) [D4/D3/D5].
3. *(2)* Classes made a PARTITION (Thm 2.2): class 3 = some key degree ≥ 2 ANYWHERE; classes 1–2
   = all-linear (which provably forces base-field pools), split by depth 0 / ≥ 1; the Thm 2.2
   status labels re-cut against it (class-3 masses: only p-power-rationality unconditional;
   `δ ≥ 2` root LEAVES stay order-0-proved). *Correction (pass 3): the claim originally recorded
   here — that EVERY "proved" label in the note had been re-audited against the partition — was
   overstated; pass 3 found stale gating/import lines in Thm 4.5, Claim 4.4(i), and Thm 3.5(i),
   fixed in the third revision below.*
4. *(3, 4b, 4c)* Thm 3.5 split into (i) unconditional qualitative (abstract masses + rate-free
   monotone-convergence exhaustion), (ii) proved-fragment quantitative, (iii) D-conditional;
   Thm 4.1 split likewise (depth tail unconditional via 3.2+3.3; height tail proved on the
   fragment, conditional beyond); Thm 4.5 and Claim 4.4(ii) scoped to match.
5. *(5)* Witness fixed: `v(a₁) = 1, v(a₀) ≥ N` with `N ≥ 3` (cancellation at `N = 2` noted), or
   `a₀ = 0`.

**Pass 3 (adversarial verification, fresh context, 2026-07-22): ALL core mathematics CLEAN** —
Lemma 2.3 (statement, proof, chain corollary), the 3.4′(a)/(b) tail arithmetic, the Thm 2.2
class partition, the D5 scoping, and the `n = 2` scope claims verified clean. Six precise
stale/gating defects found (no new mathematical content — all are bookkeeping of what gates
what):
(1) CRITICAL — Def 1.3's terminating characterization ("every residual factor everywhere has
`μ = 1`, every opened node fully read"), read literally, emptied class 2: a depth-`k ≥ 1`
history necessarily contains ancestor `μ ≥ 2` factors.
(2) CRITICAL — Thm 4.5's opening gate ("Modulo D1+D2 for class-3 strata") contradicted its own
closing sentence conditioning the class-2 remainder on D3/D5; the full rationality needs
D1+D2+D3+D5.
(3) CRITICAL — Claim 4.4(i) asserted the H-ladder closure via (‡) unqualified, though (‡) is
proved only on the fragment (class 1 + whole-window class 2).
(4) GAP — the chain-sum displays in 3.4′(a) and (3h) wrote "=" at steps that relax the joint
budget constraint (`2Σmᵢ ≤ N` resp. `sΣm ≤ N`) to independent unrestricted sums; and the chain
certification bound was stated as `≤ B` where Lemma 2.3's bottom budget `≥ 1` gives `≤ B − 1`.
(5) GAP — Thm 3.5(i)'s import line claimed "[COUNT + MONTES #6 only]", but the per-type clause
of (3d) also uses boundary #4 (leaf/type faithfulness) and #5 (lift invariance).
(6) GAP — the D5 block claimed D5 "implied by D1's ledger mechanism"; D1 concerns `deg φ ≥ 2`
keys and does not logically imply the `deg φ = 1` cross-frame D5.

**Fixes applied 2026-07-22 (third revision) — exactly the six, no content change elsewhere:**
1. Def 1.3: terminating recharacterized recursively (every `μ ≥ 2` residual factor has an opened
   child whose history is recursively resolved; every TERMINAL unopened factor has `μ = 1`).
2. Thm 4.5: full-rationality gate corrected to D1+D2+D3+D5; the unconditional fragment
   rationality (class 1 + whole-window class 2; everything at `n = 2`) stated separately.
3. Claim 4.4(i): split into (i-a) proved-fragment (whole-window ladders via the proved (‡)
   instances) and (i-b) D-conditional (class 3 GIVEN D1(+D2); class-2 partial-side/mid-polygon
   GIVEN D3/D5), mirroring the Thm 4.1 split.
4. 3.4′(a) + (3h): the relaxation steps now display `≤` with the relaxation named (joint budget
   constraint dropped to independent unrestricted sums, only `k ≤ N/2` kept); certification
   bounds stated sharp first (`2Σmᵢ ≤ N − 1` resp. `s·Σ_t m_t ≤ B − 1`, Lemma 2.3 leaving bottom
   budget `≥ 1`) and explicitly relaxed.
5. Thm 3.5(i): import line corrected to [COUNT + MONTES #4 + #5 + #6]; the in-theorem import
   summary and boundary-table row 14 brought into line.
6. D5 dependency downgraded to "expected to follow from an extension of the D1 ledger method
   (no formal reduction supplied)" — in the [OPEN-D5] block and §5's closing answer; the
   overstated "every proved label re-audited" line of the pass-2 record corrected in place
   (annotation at pass-2 fix 3 above).

**Pass 4 (adversarial verification, fresh context, 2026-07-22): all six pass-3 fixes CLEAN** —
Def 1.3's recursive terminating characterization, Thm 4.5's D1+D2+D3+D5 gate, the Claim 4.4(i)
split, the 3.4′(a)/(3h) relaxation displays, Thm 3.5(i)'s import line, and the D5 dependency
downgrade all verified in place. **Waves 5 and 6 declared mathematically unblocked** (their
inputs lie in the proved whole-window fragment — Lemma 2.3, 3.4′(a)/(b), Thm 3.5(i)–(ii) — per
§8's wave order). TWO defects remain:
(1) CRITICAL — [OPEN-D1] was stated at single-read MARGINAL strength ("for a fixed canonical
key `φ` and a fixed read: the joint distribution, under uniform `f mod p^N`, of the inspected
digits is uniform and independent over their pools") while its consumers price MULTIPLE reads
jointly: the "equivalently, count = (‡)" line inside the D1 block itself, the
D4-implied-by-D1 claims (Lemma 3.4′(c), §5's answer, §8), and Thm 4.5's D1+D2+D3+D5 gate.
(2) GAP — Thm 3.5(i)'s bracket "NO open item" conflated mathematical import with
axiom-declaration readiness: boundary #5's exact GMN pin is still TBD at declaration time.

**Fixes applied 2026-07-22 (fourth revision) — exactly the two, no other content change:**
1. [OPEN-D1] restated at JOINT-ledger strength: for a complete fixed read-history/prefix
   containing a `deg φ ≥ 2` development step (class-3 scope — the all-linear D3/D5 strata stay
   outside, as before), the inspected digit functionals of ALL its reads are JOINTLY uniform
   and independent over their pools — equivalently, each read's displayed law holds
   CONDITIONALLY on every compatible ancestor-stratum cylinder; the old single-read form kept
   as the labeled corollary **D1-marginal**. The named citing sites re-audited: the
   "count = (‡)" equivalence now attaches to the JOINT form (a whole-stratum count IS a joint
   statement); D4 ⟸ D1 confirmed to survive ONLY under joint-D1 and annotated so at 3.4′(c),
   §5's answer, and §8; Thm 4.5's gate annotated to mean JOINT-D1, under which the gate is
   sufficient. Grep-audit of every remaining D1 citation: Thm 2.2.3 (class-3 (‡) values),
   Thm 3.5(iii), Claim 4.4(i-b)/(ii), boundary row 10 marked joint; §7 Case E and the Wave-7
   entry gate marked as depth-0/marginal instances (the Wave-7 target is the joint ledger).
   No [COUNT]/proved label was changed; the proved order-1 instance is now cited precisely
   (marginal: `CellCard.cell_card_raw`; joint analogue on whole-window linear chains:
   Lemma 2.3(4)–(5), already [COUNT — proved]).
2. Thm 3.5(i)'s bracket softened to distinguish mathematical import from declaration
   readiness: "NO open D-lemma; boundary #5's exact GMN pin is TBD at axiom-declaration time
   (standard Montes content, citation pending)"; the same phrasing harmonized at Def 1.2's
   lift-invariance flag and boundary-table row 14.

**Status: fixes applied 2026-07-22 (fourth revision), awaiting pass 5.**
