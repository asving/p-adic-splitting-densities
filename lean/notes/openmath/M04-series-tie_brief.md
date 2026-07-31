# M04-series-tie — problem brief

*(Self-contained statement of one open obligation of the uniformity-theorem
formalization. 2026-07-31. Sources: `lean/LeanUrat/MovesU/BridgeKernels.lean`
(the row), `MovesU/DefsLedger.lean`, `MovesU/Defs.lean`, `MovesU/DefsCarriers.lean`,
`MovesS/Interfaces.lean`, `MovesS/RshDef.lean`, `MovesS/BlockSolve.lean`. The Lean
statement is the normative form.)*

## 1. Ambient goal (context only)

The project formalizes: for each degree n and each splitting type σ of degree n,
the Haar density of monic degree-n polynomials over ℤ_p whose factorization over
ℚ_p has type σ is the value at q = p of a single rational function R_σ(q) ∈ ℚ(q),
the same function at every prime p. The formalization is organized as a ledger of
typed hypothesis rows over interface structures; a "row" is a field of a
Prop-valued structure, and discharging a row means proving it for the concrete
objects the final assembly binds to the structure's parameters. This brief
concerns the row named `series_tie`.

## 2. The Lean statement (verbatim)

The row appears twice, byte-identically. As a field of the kernel pack
(`lean/LeanUrat/MovesU/BridgeKernels.lean`, lines 206–224):

```lean
structure BridgeKernels (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (p : ℕ) (hp : p.Prime)
    (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (seam : TreeSeam n p X F) (Tpin : @TreePin n p ⟨hp⟩ X F seam) : Prop where
  ...
  series_tie : ∀ σ : SplittingType n,
    F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
```

and as the field `series_tie` of `structure SolveSeam`
(`MovesU/DefsLedger.lean:571–574`), same formula. It is consumed by
`bridgeSolveSeam` (`MovesU/BridgeSolve.lean:245–253`) as an explicit hypothesis
binder `hseries`, and fed from the pack into the capstone assembly in
`MovesU/BridgeMk.lean` (`ssrc := bridgeSolveSeam C BD.F BP.hdet BD.BK.series_tie`).

Because `BridgeKernels` is a Prop structure, the obligation is: **prove the
displayed equation for the objects bound at the final wiring** — `X`, `F`, `seam`
bound to the constructed classifier/fiber-family/seam (built in the
`BridgeD*`-series units, over designer data still pending, see §5c), and `C` bound
to a per-n instance of the real solve corpus `UCarriers n` (for n = 2 the corpus
currently contains the gate instance described in §5c).

## 3. The vocabulary, unfolded to standard mathematics

Throughout p is a prime, n ≥ 1 a fixed degree.

### 3.1 Splitting types

`SplittingType n` := multisets σ of pairs (e, f) of positive integers with
Σ_{(e,f)∈σ} e·f = n (`MovesU/Defs.lean:30`). Intended meaning: unordered
factorization data over ℚ_p — one pair per irreducible factor, e the
ramification index, f the residue degree. This type is a Fintype.

### 3.2 Boxes and the classifier (the parameter X)

`Box p n N := Fin n → ZMod (p^N)`: the n non-leading coefficients of a monic
degree-n polynomial modulo p^N — p^{nN} classes, each a Haar-measure-p^{−nN}
cylinder in the space of monic degree-n polynomials over ℤ_p.

`X : ClassifierSpec n p` carries `canonical : ∀ N, Box p n N → Option
(SplittingType n)` — a level-N verdict map ("the classifier decides σ from the
first N coefficient digits, or abstains"), with a stability law (a verdict at
level N persists to all higher levels). Intended instance: the verdict of the
project's canonical Okutsu–Montes/Newton-polygon factorization tree, run on the
level-N residue data under a fixed choice-free policy.

### 3.3 The tree-fiber series (the parameter F): the LEFT side

`F : FiberSeries n p X` (`MovesU/Defs.lean:227–238`) carries:

* `Tree σ : Type` — an abstract index family; intended: the complete finite
  realizable canonical trees of verdict type σ. "Canonical tree" = the full
  branching record of the classifier's run: root residue factorization, then per
  branch the sequence of Newton-polygon window reads, branchings, and
  (τ-irr)/(τ-hen) leaf certificates, each leaf carrying a verdict pair (e,f);
  "type σ" = the leaf multiset is σ; "complete finite realizable" = every branch
  ends in a leaf, finitely many nodes, and some coefficient class actually
  realizes the tree.
* `mass : Tree σ → ℝ≥0∞` — intended (built as `bridgeMass`,
  `MovesU/BridgeD12_mass.lean:48`): with L := max(thr T, 1) the tree's
  certification level,
  `mass T = #{x ∈ Box p n L : the classifier run on x realizes exactly T} / p^{nL}`
  — the normalized level-L fiber count, i.e. the Haar measure of the union of
  level-L cylinders whose classifier tree is exactly T.
* `thr : Tree σ → ℕ` — the decision threshold (the least level at which the tree
  is fully certified), with `thrSlice σ N : Finset (Tree σ)` the finite slice
  characterized by `T ∈ thrSlice σ N ↔ thr T ≤ N`, and the definitional law
  `slice_exhausts : T ∈ thrSlice σ (thr T)`.

The LEFT side of the row is
`F.seriesSum σ := ∑' T : F.Tree σ, F.mass σ T` (`Defs.lean:242`) — the
unordered sum in the extended nonnegative reals [0, ∞] (= the supremum of finite
partial sums; always defined, possibly ∞).

### 3.4 The measured chain (the parameter C.chain): the RIGHT side

`C : UCarriers n` (`MovesU/DefsCarriers.lean:81`) packages the solve-side corpus:

* `C.T : TableShape n` — a finite-state transition table: for each block size
  e ∈ [1, n] a finite state set `State e`; a finite verdict-type set
  `VType ≃ {(e,f) : ℕ+ × ℕ+ // e·f ≤ n}` with degree map vdeg(v) = e·f; per state
  a finite outcome roster, each outcome routed as `kcol` (single same-size
  continuation), `termFin` (leaf with a verdict multiset), or `split` (finitely
  many members, each either verdict-halted or continuing into a strictly smaller
  block state with a base-change index δ ∈ ℕ+). Intended meaning: the states are
  the size-e cluster states of the classifier's depth recursion; `kcol` is the
  same-size descend/recenter step; `split` is a Newton-polygon branching.
* `C.MS : MeasuredSide C.T` — the measured (numeric) side: pools
  Q = {p^δ} ⊆ ℚ, per-outcome measured row values `rowVal e τ o q₀ ∈ ℝ`
  (intended: one-step conditional Haar masses of the outcome's digit event in
  the base-changed theory at pool q₀), cell/entrance carriers.
* `C.RB : RatBurdens C.T C.MS` — ℚ(q)-presentations of the measured rows: for
  each outcome a `PolyGeom` (two ℚ-count-polynomials × a geometric height factor
  whose denominator divides X^b·∏(1−X^a)), with interpolation laws: the
  presentation's evaluation at every pool q₀ equals the measured `rowVal` there.
* From these, definitions (all in `MovesS/`):
  - `Kmat T RB e` (K_e): the |State e|×|State e| matrix over ℚ(q) whose (τ,β)
    entry sums the presentations of the `kcol` outcomes from τ targeting β.
  - `bTerm` (b_e^{term}): per verdict multiset σ′, the vector of summed `termFin`
    presentations with verdict σ′.
  - `bSplit` (b_e^{split}): per σ′, Σ_{o split} J_{τ,o}(q) · Σ_{σ′ = ⊎_j σ_j}
    ∏_j (leg factor of member j), where a halted member's leg factor is the
    indicator [σ_j = {its verdict}] and a continuing member's leg factor is the
    strictly-smaller-block solve at argument q^{δ_j}
    (`MovesS/BSplitDef.lean`).
  - `blockSolve` (β_{e,τ}(σ′) ∈ ℚ(q)): the triangular recursion
    `β_e = (1 − K_e)^{−1} (b_e^{term} + b_e^{split})` (matrix inverse over ℚ(q),
    licensed by the carried hypothesis `DetHyp`: det(1 − K_e) ≠ 0 in ℚ(q) for
    all e), well-founded because split legs go to strictly smaller e
    (`MovesS/BlockSolve.lean`, equation `blockSolve_eq`).
  - Shapes: `Shape C.T` = a tuple (k, (e_i, τ_i, δ_i)_{i<k}, σ₀) — intended: a
    "shallow tree shape", the finite root layer of a canonical tree from the
    root down to its k block entrances (each entering state τ_i of block e_i
    with base-change index δ_i), with σ₀ the verdict multiset of the shallow
    leaves; `C.Fam : ShapeFam C.T` a finite family of shapes.
  - `Rsh` (THE rational function; `MovesS/RshDef.lean:57`):
    `Rsh σ := Σ_{Ŝ ∈ Fam.Sh} W_Ŝ · Σ_{σ = σ₀(Ŝ) + Σ_i g_i} ∏_{i<k(Ŝ)}
    β_{e_i(Ŝ), τ_i(Ŝ)}(g_i)(q^{δ_i})` ∈ ℚ(q), where W_Ŝ = `(WshP Ŝ).val` is the
    chain's ℚ(q)-presentation of the shallow shape's resummed mass.
* `C.chain : RS4Chain …` (`MovesS/Interfaces.lean:129–183`) carries, among
  others, the DATA field **`Rval : Multiset C.T.VType → ℚ → ℝ`** and its laws:
  - `r_bdd`: Rval σ q₀ ∈ [0,1] at every pool;
  - `Sigmas : Finset (Multiset VType)` with `sig_exact`: σ ∈ Sigmas ↔ its
    verdict degrees sum to n;
  - `rs1_equates` + `x3_total`: Σ_{σ∈Sigmas} Rval σ p = decidedTotal p = 1 at
    every prime p;
  - **`rsh_interp`**: for σ ∈ Sigmas, prime p, and any `hdet : DetHyp`, the
    rational function `Rsh … σ` is regular at q = p (its reduced denominator
    does not vanish there — membership in the subring `OKat p`) and its
    evaluation there equals Rval σ p.

  So at primes, Rval IS the evaluation of the explicit rational function `Rsh`;
  `Rval` is nevertheless carried as a field (it is also defined at non-prime
  pools p^δ, and it is the object the measured-side laws speak about).

### 3.5 The vocabulary bridge and the coercion

`vmap C.T σ : Multiset C.T.VType` (`DefsCarriers.lean:35`) reads a splitting
type σ (multiset of (e,f) pairs) as a multiset of table verdict types through
the structural equivalence `vEquiv`; `vmap` is a bijection onto
`{s // s ∈ C.chain.Sigmas}` (`MovesU/BridgeDict.lean:180`, `vmapEquiv`), and the
sum-transport lemma `sum_vmap_eq_sum_Sigmas` (ibid.:203) is proved.
`ENNReal.ofReal x` = max(x,0) coerced into [0,∞]; by `r_bdd` the argument lies
in [0,1], so no clamping occurs at pools.

## 4. The statement in standard mathematical language

For every prime p and every splitting type σ of degree n:

> **(series-tie)**  Σ_{T ∈ 𝒯_σ} μ(fiber T) = R_σ(p),

where 𝒯_σ is the family of complete finite realizable canonical classifier
trees of verdict type σ, μ(fiber T) is the Haar mass of T's fiber (read as the
normalized level-L fiber count at T's own certification level L, §3.3), the sum
is an unordered sum in [0,∞], and R_σ(p) is the value at q = p of the single
rational function R_σ = `Rsh`(vmap σ) ∈ ℚ(q) assembled by the triangular block
solve and the shallow convolution (§3.4) — a value in [0,1], well-defined by the
chain's own regularity law. The equation is in [0,∞]: in particular it asserts
the finiteness of the left side, and for σ with R_σ(p) = 0 it asserts the
vanishing of every tree mass of type σ.

## 5. What already exists in the corpus

**(a) Proved theorems adjacent to the row** (all sorry-free at HEAD unless noted):

* `TreeSeam.finiteness_stack` (`DefsLedger.lean:243`): DERIVED from the sibling
  open row `count_tie` (see (b)): decided_σ(N) = p^{nN} · Σ_{T ∈ thrSlice σ N}
  mass T, where decided_σ(N) := #{f ∈ Box p n N : canonical N f = some σ}.
* `U2_tonelli` (`MovesU/U2_tonelli.lean`): Σ_{T ∈ thrSlice σ N} mass T ≤
  seriesSum σ. `U3_sq2_partial`: decided_σ(N) ≤ p^{nN} · seriesSum σ given the
  seam.
* `bridge_slice_finite` (`BridgeKernels.lean:182`): threshold slices of the
  built tree carrier are finite.
* `rs4_checksum_bridge` (`BridgeSolve.lean`): Σ_{σ : SplittingType n}
  Rsh(vmap σ) = 1 identically in ℚ(q) (proved from the chain laws by prime
  interpolation).
* `SolveSeam.solve_stack`, `SolveSeam.evalℝ_eq_Rval`, `SolveSeam.R_defined`,
  `SolveSeam.rs4_eval` (`DefsLedger.lean:583–676`): GIVEN the row (and the
  regularity pack), finiteness of seriesSum, its identification with the
  literal evaluation of R_σ, and the evaluated checksum all follow.
* `vmapEquiv` / `sum_vmap_eq_sum_Sigmas` (`BridgeDict.lean`): the vocabulary
  bridge is a bijection onto Sigmas, sums transport.

**(b) Open sibling rows** (named hypotheses in the same ledger; NOT available as
theorems): `count_tie` (per-tree fiber count at every level N ≥ thr T:
mass T · p^{nN} = #{decided-σ classes at level N assigned tree T} — the TREE-N
row, a separate obligation, M02 of this series); `env_tendsto` (the undecided
mass p^{−nN}·#{canonical N = none} → 0); `vp_sound`; `sibjc` ((SIB)/(JC-multi)
sibling-independence laws at the pinned models); `transfer`; `slice_bound`;
`cl6`/`cl11`/`cl17`/`cl19` (table-law rows). The project's source note
(`lean/notes/MOVES_2026-07-24.md`, §S-RESUM and §T-ASSEMBLY) states the
intended mathematics of these rows; the row `series_tie` is that note's named
open premise "[3t] solve-side seam".

**(c) As-built instances.** The only existing `RS4Chain` instance is the n = 2
gate `n2Chain` (`MovesS/N2Sigmas.lean`): its `Rval` is
`(q+1)/(q²+q+1)` on {(1,2)}, `q²/(q²+q+1)` on {(1,1),(1,1)}, and `0` on every
other multiset including {(2,1)}; its shallow carriers are the device
one-height/weight-1 family, and its docstring describes the values as "the two
note-displayed solve evaluations". The built fiber family `bridgeFibers`
(`MovesU/BridgeD14_fiberSeries.lean`) rests on designer data
(`bridgePol`/`bridgeTm`, IB-D1) that are declared data-sorries pending a
scheduled designer round. The final wiring binding both to `BridgeKernels` has
not been executed; `BridgeKernels.lean`'s header records that the n = 2
consistency display is gated on a future real n = 2 `UCarriers` pack from the
S-area.

**(d) Numeric ground truth available in `verification/`** (Python, validated in
this repo): `padic_types.py` has closed forms for the true monic splitting-type
densities over ℤ_p at n = 2 (split: q/(2(q+1)), inert: q/(2(q+1)), ramified:
1/(q+1)) and n = 3 (five types), validated against a PARI `factorpadic` oracle;
`om_density_engine.py` computes projective factorization-type densities
ρ(n,σ;q) as exact rational functions with validation gates at n ≤ 5.

## 6. What a proof must deliver

1. **Primary form.** For the intended instantiation (§2, last paragraph): a
   proof, at every prime p and every σ : SplittingType n, of
   seriesSum σ = ofReal(Rval(vmap σ)(p)) — equivalently (by `rsh_interp`) of
   (series-tie) in §4 — from stated hypotheses. Any input that cannot be proved
   outright must be isolated as an explicitly named open lemma with a precise
   statement (the project's honesty discipline; unproven steps may not be
   papered over). The equation is in ℝ≥0∞ and must include the finiteness of
   the left side and the zero-value cases.
2. **Alternative deliverables**, each acceptable: a reduction of the row to
   cleaner, independently attackable statements (with the reduction proved
   rigorously); a refutation of the row at a specific intended pairing (a σ, a
   prime p, and a computable discrepancy certificate); or a precise literature
   identification (publication, theorem number, hypotheses, and an exact match
   analysis against the Lean statement — noting anything the Lean row asserts
   beyond the citation).
3. **Scope.** The row binds one prime p at a time (p-uniformity is carried by
   other rows); but the right side is the SAME rational function at every p.
   The row quantifies over ALL σ of degree n, including those whose chain value
   vanishes. Statement changes are out of scope: the Lean form above is
   normative.
