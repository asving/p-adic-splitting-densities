# WILD_WAVE6Q_BLUEPRINT — n = 2 ALL-PRIMES uniformity: one fixed rational function per type
*(2026-07-22. Ground truth: `MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` (ACCEPTED) §§1–4, 7–8 —
the note is general-q throughout; W5/W6 formalized its p = 2 instance. Directive (Asvin,
2026-07-22, post-W6c): palindromy is OUT OF SCOPE entirely; the end goal is the uniformity
statement itself. Status: DRAFT pending Codex adversarial pass on §1/§3.)*

## §0. The prize

**`montes_uniform_n2`**: fixed polynomials (numₛ, denₛ) per degree-2 type σ — defined ONCE,
before any prime is mentioned — with, for EVERY prime p (wild p = 2 included):

  (M7 p).countingDensity σ = numₛ.eval p / denₛ.eval p,     denₛ.eval p ≠ 0,

where `M7 p : CountingModel p 2` is the general-p full counting model (the W6 `realMW6`
construction at arbitrary p), with the exhaustion clause discharged at every p (pure counting,
no new axiom), and faithfulness (every counted fiber Montes-faithful) via the already-general-p
masters + one axiom re-scope (#6). The fixed functions:

  R_ram = 1/(q+1) · · · R_inert = q/(2(q+1)) · · · R_split = q/(2(q+1)),   Σ = 1.

This is the paper's theorem at n = 2: the density is ONE rational function of the prime,
uniformly over all primes including the wild one. Palindromy/htameFE: not touched, per the
directive. Note's Thm 4.5: at n = 2 the proved fragment is EVERYTHING — no D1–D5
conditionality enters.

**Numeric gates already passed (2026-07-22, this session + the note's record):**
- p = 2: the W6 machine-checked values 1/3, 1/3, 1/3 = R_σ(2) ✓ (recovery gate).
- p = 3 census mod 3⁷ (fresh, this session): ram 182/729, inert = split = 91/243, undecided
  EXACTLY 1/729; targets R_σ(3) = 1/4, 3/8, 3/8 all inside the envelope from below ✓.
- p = 3 mod 3⁶ (the note §7 Case B, independent run): ladder sum 9/13, descend ratio 1/13,
  β_ram = 3/4 = q/(q+1) ✓.
- splitU pool check at q = 3 (hand enumeration): exactly (q−1)(q−2)/2 = 1 ✓.

## §1. Math ground truth (general q; n = 2 throughout)

Everything below instantiates the ACCEPTED note at n = 2; the ledger arithmetic is
re-derived here in closed form and was validated numerically (§0). q := p; all "mass" =
normalized cylinder count (box fraction), exact at each level.

### 1.1 The stratum tree at n = 2, general q

**Order-0 (root read of f̄ = x² + ā₁x + ā₀ over F_q):**
- split cell: f̄ has two DISTINCT roots (any, 0 allowed) — pool q(q−1)/2 of q² residual pairs;
  mass (q−1)/(2q). Leaf {(1,1),(1,1)} by Hensel at the two simple roots.
- inert cell: f̄ irreducible (⟺ root-free, quadratic) — pool q(q−1)/2; mass (q−1)/(2q). Leaf
  {(1,2)}.
- cluster locus: f̄ = (x − c̄)², one per c̄ ∈ F_q — q points, mass q·q^{−2} = 1/q. Each opens a
  cluster node; recenter x ↦ x + ĉ (the c-translate; `RecenterBox.affineEquiv`, general p).
  [At p = 2 this reproduces W6's digit cells: the split pool is the single pair {0,1}
  (mass 1/4 = (q−1)/(2q) at q=2 ✓), the inert pool the single x²+x+1.]

**Cluster reads (after recentering to y² + b₁y + b₀, cluster: v(b₀) ≥ 1, v(b₁) ≥ 1 — at n = 2
the recentered cluster forces both ≥ 1; all masses below CLUSTER-CONDITIONAL per residue
point, i.e. relative to the point's q^{−2} box):**

| family | conditions | pool / count per height | keyed σ | per-height mass | family sum |
|---|---|---|---|---|---|
| ram H (H odd ≥ 1) | v(b₀) = H exact, v(b₁) ≥ (H+1)/2 | q−1 (the unit digit) | {(2,1)} | (1−1/q)·q^{−3(H−1)/2} | q²/(q²+q+1) |
| inert m (m ≥ 1) | v(b₀) = 2m, v(b₁) ≥ m, residual root-free | q(q−1)/2 | {(1,2)} | [q(q−1)/2]·q^{−3m} | q/(2(q²+q+1)) |
| **splitU m (m ≥ 1) — NEW at q > 2** | v(b₀) = 2m, v(b₁) ≥ m, residual two distinct roots, both ≠ 0 | (q−1)(q−2)/2 | {(1,1),(1,1)} | [(q−1)(q−2)/2]·q^{−3m} | (q−2)/(2(q²+q+1)) |
| split k (k ≥ 1, two-sided) | v(b₁) = k exact, v(b₀) ≥ 2k+1 | q−1 | {(1,1),(1,1)} | (1−1/q)·q^{−(3k−1)} | 1/(q²+q+1) |
| descend m (m ≥ 1) | residual a SQUARE (z−c̃)², c̃ ∈ F_qˣ (v(b₀)=2m-frame; the `StratumPair` (S1)∧(S2) digit conditions) | q−1 | (recurse) | (1−1/q)·q^{−(3m−1)} | 1/(q²+q+1) |

**(L) The even-height separable line.** At height 2m the separable-residual strata (residual
z² + w̄₁z + w̄₀, w̄₀ ≠ 0, disc̄ ≠ 0) have combined pool (q−1)² [root-free q(q−1)/2 +
two-distinct-nonzero-roots (q−1)(q−2)/2; CHECK: (q−1)(q + q−2)/2 = (q−1)²], per-m combined
mass (q−1)²·q^{−3m} [at q=2: 2^{−3m} = the W6 inert-only line ✓]. Family sums and the exact
(q−1)-cancellations are in §1.2: inert_0 = q/(2(q²+q+1)), splitU_0 = (q−2)/(2(q²+q+1)).
At q = 2: 1/7 and 0 ✓ (splitU honestly EMPTY — the pool polynomial vanishes; the
universal-polynomial form carries emptiness correctly, note Claim 4.3). Also the full pool
bookkeeping at an exact even height: q(q−1)/2 + (q−1)(q−2)/2 + (q−1) [squares, the descend
pool] = q(q−1) = all pairs with w̄₀ ≠ 0 ✓ — the trichotomy separable-rootfree / separable-
two-roots / square is exhaustive per residual.

**Depth-0 checksum (cluster-conditional):** q²/(q²+q+1) + (q−1)/(q²+q+1) + 1/(q²+q+1)
+ 1/(q²+q+1) = 1 ✓ [ram + even-H separable + two-sided + descend].

**Sanity for the descend stratum at both parities.** The residual-square condition is
uniform: z² + w̄₁z + w̄₀ = (z − c̃)² with c̃ = −w̄₁/2 at odd q; at q = 2, squares are exactly
w̄₁ = 0 (Frobenius), c̃ = √w̄₀. The count is q − 1 (c̃ ∈ F_qˣ; c̃ = 0 is the stall/deeper-
cluster direction) in both cases — this is `RecenterBox.StratumPair`'s existing general-p
digit form (already formalized and audited; the blueprint takes it as-is, and the covering
proof of §2 must USE it rather than re-derive parity cases).

### 1.2 The tower and the fixed values

**Per-family depth-0 masses from digit freedom** (cluster-conditional coordinates: on the
cluster locus write b₀ = q·β₀, b₁ = q·β₁ with (β₀, β₁) uniform; each family = pinned zero
digits × one specified residual pair × free tail; per SPECIFIED residual pair the mass is
q^{−(pinned digit count)}):

  ram H: (1−1/q)·q^{−3(H−1)/2}       [q−1 unit digits at position H−1 of β₀, (H−1)/2 zeros of β₁]
  even-height 2m, per specified pair (w̄₀ ≠ 0, w̄₁): q^{−3m}   [(2m−1)+(m−1) zeros + 2 digits]
  two-sided k: (1−1/q)·q^{−(3k−1)}
  descend m (pool q−1): (q−1)·q^{−3m}

Family sums (Σ_m q^{−3m} = 1/(q³−1) and (q³−1) = (q−1)(q²+q+1) — the (q−1) CANCELLATIONS
below are load-bearing; an earlier draft of this section dropped one and produced a fake
q = 3 contradiction, caught by the census cross-check):

  ram_0     = (1−1/q)·Σ_{H odd} q^{−3(H−1)/2} = q²/(q²+q+1)
  inert_0   = [q(q−1)/2]·(1/(q³−1))           = q/(2(q²+q+1))        ⟨q=2: 1/7 ✓⟩
  splitU_0  = [(q−1)(q−2)/2]·(1/(q³−1))       = (q−2)/(2(q²+q+1))    ⟨q=2: 0 ✓; q=3: 1/26⟩
  twoSided_0 = (1−1/q)·Σ_k q^{−(3k−1)}        = 1/(q²+q+1)
  descend_0  = (q−1)·(1/(q³−1))               = 1/(q²+q+1) =: r(q)   ⟨q=2: 1/7, q=3: 1/13 ✓⟩

  Depth-0 checksum: [q² + q/2 + (q−2)/2 + 1 + 1]/(q²+q+1) = (q²+q+1)/(q²+q+1) = 1 ✓.

**Fixpoints** (Lemma 2.3: each descend re-enters an identical cluster distribution, ratio r;
1 − r = (q²+q)/(q²+q+1)):

  β_ram   = ram_0/(1−r)                    = q²/(q²+q)          = q/(q+1)
  β_inert = inert_0/(1−r)                  = (q/2)/(q²+q)       = 1/(2(q+1))
  β_split = (splitU_0 + twoSided_0)/(1−r)  = ((q−2)/2 + 1)/(q²+q) = 1/(2(q+1))

  Σβ = q/(q+1) + 1/(q+1) = 1 ✓.  ⟨q=2: 2/3, 1/6, 1/6 = the W6/note values ✓;
  q=3: 3/4, 1/8, 1/8 — census-exact (§0: β_split(3) forced = 3·[3/8 − 1/3] = 1/8 ✓)⟩

**Full-box per-type (the FIXED functions):** cluster locus mass = q·q^{−2} = 1/q;
order-0 leaves contribute (q−1)/(2q) to each of split/inert. So
R_ram = (1/q)·β_ram = 1/(q+1);
R_inert = (q−1)/(2q) + (1/q)·β_inert = [(q²−1) + 1]/(2q(q+1)) = q/(2(q+1));
R_split identically = q/(2(q+1)). Checksum Σ R = 1 ✓. ⟨q=2: 1/3 ×3 = W6 ✓;
q=3: 1/4, 3/8, 3/8 = the §0 census ✓⟩

### 1.3 The envelope at general q

The W6 pure-counting envelope generalizes in structure: stall containment (v(b₀) ≥ B−1 at
some frame of the read — a pointwise digit statement, no q in its shape) + the ≤-relaxed
chain sum. The q-dependence enters ONLY through per-step weights, and the discipline that
closes it (this replaces the earlier draft's "expected to survive" — Codex pass-1 gap #1):
**carry each step's pool factor and digit probability as ONE combined weight, never
separately.** The combined relaxed per-step weight at slope m is w_m(q) := (q−1)·q^{−2m}
(pool q−1 recentering digits × the two pinned coordinate digits at the (2m, m)-staircase,
relaxed exactly as in W6: the b₁-side digit released). Then:

  **Lemma (per-step domination).** Σ_{m ≥ 1} w_m(q) = (q−1)·q^{−2}/(1−q^{−2}) =
  (q−1)/(q²−1) = 1/(q+1) ≤ 1/3 < 1/2 for every q ≥ 2; and the single-step weight
  w_1(q) = (q−1)/q² ≤ 1/2 for every q ≥ 2 (⟺ (q−1)² + 1 > 0). Hence every W6 chain-sum
  relaxation that used the q = 2 numeric bounds (Σ_ms (1/2)^{Σm} ≤ D+1; the stall bound's
  (p−1)^k·p^{L₁−Σm} with the pool folded in) goes through at general q with the SAME
  polynomial-in-N constant once pools are folded into weights: the folded weights are
  monotone non-increasing in q on q ≥ 2.

Target statement: undecided(N)/q^{2N} ≤ (⌊N/2⌋+1)·(q−1)·q^{−(N−1)}-form (any C(N)
polynomial in N with a q-uniform coefficient suffices; the note §8 records the n = 2
constant 6(⌊N/2⌋+1)p^{−N}). Implementer proves the folded-weight inequalities as named
lemmas FIRST (they are one-line `nlinarith`/`positivity` facts at q ≥ 2 from Fact p.Prime),
then transcribes the W6 envelope proof against them.

### 1.4 The squeeze at general q

As W6: (U) decided ≤ R_σ(q)·box per type via the per-step fixpoint bound — the general-q
analogue of msW_eighth_le is Σ_ms r(q)-weighted ≤ 1/(1 − r(q)) = (q²+q+1)/(q²+q), closing
exactly at the full values; (≥) decided ≥ (R_σ(q) − envelope)·box via the box partition +
(U) for the other two types. Both directions are RatFn inequalities in q with q ≥ 2 — the
Lean statements should keep them as exact rational-function identities evaluated at the
prime (ℚ-arithmetic with (q : ℚ) = (p : ℚ), positivity from p ≥ 2).

### 1.5 σ-keying and faithfulness (delta over W6c)

All W6c masters are ALREADY general-p (ram all odd H; inert all m ≥ 0; split all k ≥ 0;
unwind; bundle pullback). NEW needs:
- **splitU master** (axiom-free): even-height rescale h(z) = g(q^m z)/q^{2m} = z² + w₁z + w₀
  with residual having two DISTINCT simple roots r̄ ≠ s̄ (both ≠ 0 irrelevant to the proof);
  h̄'(r̄) = 2r̄ + w̄₁ = r̄ − s̄ ≠ 0 (valid at p = 2 as well), Hensel at each root, transport —
  verbatim the (S) proof with the two roots general instead of {0, −w̄₁}. Conclusion:
  ∃ certificate {(1,1),(1,1)}.
- **order-0 split-cell master at general p** (axiom-free): f̄ has two distinct roots r̄ ≠ s̄
  (not necessarily 0,1): same Hensel-at-two-simple-roots core (the (S0)/p=2 version had
  roots {0,1}; generalize the root pair).
- order-0 inert cell at general p: already the m = 0 inert master (general p) + the
  general-p glue SepInertCell_p → classify = sepShape (the W6c glue was p = 2-specific in
  its digit decoding; the general-p version goes through the SAME banked
  `Order0.classify_eq_sepShape_iff` with the residual-irreducibility hypothesis now "the
  residual quadratic is root-free over F_p" — no q = 2 case analysis).
- **Axiom re-scope #6**: menu gains the splitU literals (per-family fiber = the even-height
  digit conditions with the two-distinct-roots residual pool — a `chainLit`-style literal
  with a new leaf head; statement map: single side (0,2m)–(2,0) slope −m/1, e = 1, residual
  separable with two distinct degree-1 factors — Thm 1.19 gives two leaves, each (1,1);
  guarded by the axiom-free splitU master, hence redundant-in-consumers like every
  split-keyed leg). General-p order-0/ram/inert/split literals: ALREADY in scope (the menu
  was always general-p). Guardian audit #7.

### 1.6 Delta list vs the W6 Lean (what must generalize)

| W6 (p = 2) asset | W6q (general p) need |
|---|---|
| `SepSplitCell`/`SepInertCell` digit cells | residual-SHAPE cells (two-distinct-roots / root-free) + banked L3/`CellCard.shapeCount` counts |
| residue points {0,1} | all c̄ ∈ F_q (q translates; `transMap` at general p — `affineEquiv` already general) |
| `ChainLeaf` (ram/inert/split) | + splitU leaf (DESIGN: parallel predicate `LeafPairU`/`ChainPairU` sharing `descendPair` — do NOT extend the `ChainLeaf` inductive, which would break every `cases leaf` proof; a wrapper index `ChainLeaf7 := old ⊕ splitU m` may package the menu) |
| `cluster_covering` (p=2 residual arithmetic) | general-p four-way covering using `StratumPair`'s uniform square-residual form (§1.1 sanity note) |
| envelope constants at q=2 | general-q constants (§1.3) |
| `msW_eighth_le` (7/6 fixpoint at q=2) | 1/(1−r(q)) fixpoint bounds (§1.4) |
| capstone at realP | `montes_uniform_n2` ∀ p + p=2 recovery gate + p=3 value gates |

## §2. Lean wave plan

- **W6q-a (counting core, general p):** splitU leaf predicate + pool (`rootedPairs p` :=
  distinct-nonzero-root residual pairs, card (q−1)(q−2)/2 via Vieta/Sym2 off-diagonal —
  mirror `noRootPairs`) + `LeafPairU`/`ChainPairU` + counts + emptiness + the q=2-empty gate
  (card = 0 at p = 2). General-p order-0 cells + counts from banked `CellCard`/`L3`.
- **W6q-b (model + covering):** `M7 p : CountingModel p 2` — decided counts = order-0 cells
  + Σ_{c̄ ∈ F_q} translated chain fibers over the FOUR leaf families; the general-p
  `cluster_covering` (decision tree: at a cluster frame, the residual is EITHER separable
  (root-free → inert leaf / two-distinct → splitU leaf / [two-sided applies at v(b₁) < m
  reads: the exact frame trichotomy per the W6 proof]) OR a square (unit c̃ → descend;
  c̃ = 0 → stall) — follow the W6 proof structure with `StratumPair` as-is); undecided =
  box − Σ decided.
- **W6q-c (envelope + squeeze + THE CAPSTONE):** general-q envelope (§1.3); the corrected
  per-family ledger (§1.2 diagnosis) as exact per-level count identities; the squeeze to the
  FIXED R_σ; `montes_uniform_n2 (p) [Fact p.Prime] (σ) (hσ : σ.degree = 2) : …density =
  numₛ.eval p / denₛ.eval p ∧ …` with (numₛ, denₛ) global constants; gates: p = 2 recovery
  (= 1/3 = W6 values), p = 3 values (1/4, 3/8, 3/8 — census-anchored), q=2 splitU-emptiness.
- **W6q-d (faithfulness):** splitU + general order-0 masters (§1.5, axiom-free); general-p
  translate commutation; re-scope #6 + `fullFiber7_hasType` (∀ p!); guardian audit #7.
- **W6q-e (gates/census/external):** witness fibers at p = 3 (a splitU witness — e.g.
  residual (z−1)(z−2) at m = 1: y² + 3·? … implementer constructs, PARI/disc-oracle-checked);
  mutation probes at the new literal; committed `verification/census_n2_uniform.py` (the §0
  census, extended per-family); full build + AxChk (capstones byte-identical).
- **W6q-f (docs):** PROJECT_STATE §2/§5 (the uniformity capstone becomes THE headline),
  audit log, commit/push.

Order (corrected per Codex pass-1 gap #3): W6q-a FIRST (b consumes its splitU
predicates/pools/counts); then W6q-b; W6q-d can run in parallel with b (it consumes a's
masters and the menu machinery only); W6q-c consumes a+b; e/f close the wave.

## §3. Re-scope #6 statement design (for the guardian)

Delta: splitU literals only (new leaf head in the `chainLit` encoding or a parallel literal
family; exact decode; n = 2 only; window (D, K)). Fiber: the `ChainPairU` digit fiber (the
even-height separable-split-residual conditions). Statement map (per literal): single side
(0, 2m)–(2, 0), slope −m/1 lowest terms ⟹ e = 1, side degree 2; residual separable with two
distinct linear factors ⟹ Thm 1.19: two coprime factors, each with (e, f) = (1, 1) by
Cor 1.20 (a_i = 1, deg ψ = 1). No uniformity/measure/translation content (unchanged).
Non-vacuity: p = 3 witness (pool nonempty ⟺ q ≥ 3); the q = 2 emptiness is machine-checked
as the pool-size effect (the W1 honest-empty pattern). Guard: the axiom-free splitU master
(certificate proved outright). "Redundant-in-consumers" is a REQUIREMENT, not an
observation (Codex pass-1 gap #2): `fullFiber7_hasType`'s splitU and every other
split-keyed branch MUST consume the axiom-free masters, never the axiom; the split-keyed
corollary is packaged separately with a machine-checked CORE-ONLY footprint (the W6c
`fullFiber_split_hasType_axfree` pattern), and the census section asserts exactly this
split: assembled theorem = core + om_leaf_faithful (via ram/inert existence legs only),
split-keyed corollary = core only. A census line showing the axiom inside the split-keyed
corollary's cone is a stop-the-line defect.
Order-0 general-p legs: already inside the standing scope (sepShapes general-p since W1).

## §4. Risks & fallbacks

1. **RESOLVED in this draft (recorded as a method note):** the first §1.2 derivation
   dropped a (q−1) cancellation and produced a fake q=3 contradiction; the census
   cross-check caught it and the corrected digit-freedom derivation closes exactly at
   q = 2, 3. Standing mitigation: every family sum in the Lean work must carry its census
   anchor at BOTH p = 2 and p = 3 (per-family census gates in W6q-e).
2. General-p covering trichotomy complexity: mitigate by literally transcribing the W6
   `cluster_covering` proof shape and replacing only the residual-classification step.
3. RatFn-inequality plumbing at general q (division-free forms): state all bounds as
   cleared-denominator polynomial inequalities with q ≥ 2.
4. Census-target byte-identity: any capstone footprint change = stop the line.

## §5. Definition of done

1. `montes_uniform_n2` lands with FIXED (numₛ, denₛ), footprint Lean-core-only, ∀ p.
2. p = 2 recovery gate ties to the W6 values; p = 3 gates tie to the census.
3. `fullFiber7_hasType` at ∀ p, core + `om_leaf_faithful`; splitU legs axiom-free.
4. Guardian audit #7 ACCEPT; envelope discharged at ∀ p with no new axiom.
5. Docs updated; committed and pushed.
