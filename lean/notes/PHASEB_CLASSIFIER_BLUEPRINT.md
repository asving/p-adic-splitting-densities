# PHASEB_CLASSIFIER_BLUEPRINT — the genuine order-≥1 classifier and the road to F-C

2026-07-04. Companion to `PIN_ARCHITECTURE_BLUEPRINT.md` (Layer-C recursion, pins, retirement
plan R0–R6) and `RESTART_FORMALIZATION_BLUEPRINT.md` (F-A done, F-B in flight, F-C gated on THIS
document). PIN §5 marks this work "the long pole, human-supervised — agent sweeps have
fake-closed here twice". Accordingly: every wave below has a numeric gate BEFORE Lean, a named
falsifiability probe, an enumerated-consumers list for any body change (the childCtxOfSize
joint-landing precedent), and a STOP-and-revert rule. No wave lands partially.

DEFINITION OF DONE for Phase B: the classifier emits genuine order-r shapes (real polygons, real
residual factorization shapes over the real residue tower, faithful child payloads); the ef-law
(`GMNNodeEfLaw`) is a THEOREM about emitted shapes; `node_limit` (h_node-v2, PIN §1.4) is
statable against the genuine classifier and DISCHARGED on the order-1 slice; drainage (h_env-v2)
is statable and gated. F-C (the restart lemma in Lean, retiring `AX_cellRecursion`) is then a
statement, not a hope.

## §0 Inventory: genuine today vs schematic (2026-07-04, post-landings)

GENUINE (banked, core-only or sanctioned-sorry-free):
* Order-0 step: `boxCoeffData` (D7 on-side guard), `M4.residualPoly`, `rootResidual` with degree
  guards; `classify`/`classifyAux` order-0 semantics; `classify_eq_sepShape` (Order0Classify).
* Cells: A2 semantics (`childSize := μ·deg ψ`, child iff `μ·deg ψ < cs`, self-loop = no-child
  cell); A3 payload (`encodeCells T` faithful at the CURRENT node); F4/SIGMA-3 child order slot
  `(T.order + 1, childSize, 0)` (landed 2026-07-04).
* Reduce-stability chain (`boxCoeffData_reduce_stable_R`, `certLevel_stabilizes`,
  `classify_reductionStable`) against the SINGLE sanctioned scalar cite
  `omReadValuation_lt_of_certLevel_fkeyed` (Classifier.lean:653: `ind(f) ≤ v_p(disc f)`
  read-set-restricted, bulk-gated; user-authorized import; refutation-tested against `xⁿ + p^N`).
* F-A: `developEquiv` (Development.lean) — the φ-adic development bijection at level N, any monic
  φ, core-only. THE order-r coordinate change exists.
* F-B1: `LinearFiber.lean` (linear fiber counts). F-B2 (`HenselCount.lean`, torsor) in flight.
* Hull layer: `boxValSupport`, `npSides`, `hullDots` + the banked convex-hull primitives and
  `boxValSupport_reduce_stable_R`; `GuardSuppR`/`GuardSideR` consume `npSides` today.

SCHEMATIC (the Phase-B debt, each with file:line):
* `childCtxOfSize (r s)` (Classifier.lean:262): child context carries ONLY (order, size); the
  slots `Fr := ZMod 2, δ := 1, Nr := trivial, Rr := 0, dr := 0, keyDeg := 0` are shells.
* Child payloads inside `ShapeCell.children` are single-tuple shapes
  `⟨[(order+1, childSize, 0)], []⟩` (the documented A3 caveat, Classifier.lean:296).
* No order-≥1 STEP exists: `omStep` computes polygon/residuals of `f` itself (order 0/1 w.r.t.
  the x-adic development); there is no development w.r.t. a genuine higher key, no residual over
  an extension field, no recursion into genuine child data.
* Three sanctioned sorries (Classifier.lean:777 `npVertices_stable_of_hull_preserved` hull
  adjacency, :1112 `boxCoeffData_endpoints_ne_zero` LEM B.1, :1258 `classify_separable_leaf`
  LEM B.8) — off every checked footprint; B.1 and B.8 are Phase-B fill targets (W2/W4 below),
  the hull-adjacency sorry becomes MOOT under the menu-checking design (§3).
  ⚠ W2-FINDING (2026-07-04): LEM B.1 AS FROZEN IS FALSE — it quantifies over arbitrary `S`/`f`
  with no vertex hypothesis; counterexample `S = ⟨0,1,0,0⟩, f = Xⁿ` (guard false, endpoint
  coefficient 0). This violates the Layer-B "every sorry over a TRUE-intended contract" rule:
  W3 MUST rescope it to hull-selected sides or delete it as moot. The genuine content is
  already banked: `CellMenu.residual_endpoint_units` (matched-side endpoints are units, from
  vertex exactness + F5). The :777 adjacency sorry is confirmed UNUSED by the landed W2
  (cell_unique closed without it).
* `GMNNodeEfLaw` (LevelNCount.lean:997): predicate exists, violated by the shells; must become a
  theorem of the genuine child contexts (W3 gate).

## §1 Design decision D-CTX: the child residue tower

`ResidueTower`/`OMType` (OMType.lean:51) carry actual `Type` fields with `Field`/`Finite`
instances. The genuine child of a node with tower `Fr` and residual factor `ψ̄` (irreducible of
degree `D` over `Fr`) must carry a field of size `|Fr|^D`.

Options considered:
(a) `AdjoinRoot ψ̄` — canonical, but the TYPE depends on runtime data (the factor), so shapes
    with equal combinatorics get unequal types; shape equality/menu membership becomes
    transport hell. REJECTED for the emitted shapes; acceptable INTERNALLY per-step.
(b) canonical-by-cardinality: `GaloisField p k` with `k := (tower degree over F0)·D` — types
    depend only on ℕ data, shapes comparable, `Fintype`/`Field` instances in mathlib; the
    residual factor is transported through a CHOSEN iso `AdjoinRoot ψ̄ ≃ₐ GaloisField p k`
    (Classical.choice; mathlib has uniqueness of finite fields via `GaloisField.algEquivGaloisField` /
    `FiniteField` unique-up-to-iso machinery — verify exact name at W2).
(c) numeric towers only: keep `Fr := ZMod p`, track δ numerically, do all residual arithmetic in
    `(ZMod p)[y] / (chosen irreducible)` — concrete but re-implements field extensions by hand.

DECISION: (b), GaloisField-canonical. Rationale: the emitted SHAPE must be a decidable-equality
combinatorial object (menus, Finsets); (b) is the only option where the field slot is a function
of ℕ data. The chosen-iso transport is confined to the STEP function (where Classical.choice is
already endemic via `Polynomial.factors`); nothing downstream reads the iso, only images under
it. Falsifiability note: the transport must be an `AlgEquiv` over the PARENT field (not a bare
ring iso), or Frobenius bookkeeping in the f-descent breaks; state the transport lemma with the
algebra structure explicit.

## §2 Design decision D-STEP: menu-checking, not hull-scanning

The classifier does NOT need to COMPUTE lower convex hulls. For a cluster of budget `s` there are
finitely many candidate polygons (lattice lower-convex paths of width `s`, bounded height ≤ N·s),
and finitely many residual-shape assignments per polygon: the CELL MENU. The order-r step can be
a MEMBERSHIP CHECK against each menu cell: a cell is the conjunction of
  (i) valuation ≥ pattern for on/above-polygon digit positions,
  (ii) exact valuation + prescribed unit-residue-factorization-shape at the on-side positions,
and the step returns the unique matching cell.

* Uniqueness lemma (`cell_unique`): at most one menu polygon matches a given digit-valuation
  vector — "if the pattern of P holds then P is the lower hull, and hulls are unique". Provable
  from the banked primitives WITHOUT the sorried adjacency lemma (:777): the pattern of P pins
  the valuation vector's hull pointwise (every dot on/above P, a dot ON P at each vertex), and
  two distinct lower-convex paths cannot both be pointwise-maximal-below the same vector. This
  makes the :777 sorry MOOT for the classifier path (it stays only as an optional nicety).
  ⚠ W0-ERRATUM F4 (load-bearing for uniqueness): the menu contains MAXIMAL-side paths only —
  strictly increasing slopes, strictly decreasing integer vertex heights; paths with collinear
  interior vertices are EXCLUDED (else `x²+2x+4` at p=2 N=3 matches two cells). W0 verified
  uniqueness on all 336 boxes only under this convention.
* Exhaustiveness lemma (`cell_exists`): every digit vector matches SOME menu cell.
  ⚠ W0-ERRATUM F1 (REFUTED as originally written): the original gate "in the bulk
  `v_p(disc) < N` all read valuations are < N" is FALSE — witnesses `x²+2x` and `x²+6x` at
  p=2, N=3 (disc valuation 2 < 3, but `v(a₀) ≥ 3`: the left polygon endpoint is unreadable;
  the truncated-valuation alternative was examined and REJECTED — the truncated residual is
  not a function of the box element). CORRECT gate at order 1 (W0's sharp law, verified on
  all 336 boxes at s ∈ {2,3,4}): a box element matches exactly one menu cell ⟺ the LEFT
  ENDPOINT is readable, `v_p(a₀) < N`. State `cell_exists` gated on left-endpoint
  readability, NOT on `v_p(disc) < N`; the unreadable boxes (`a₀ ≡ 0 mod p^N`, exactly
  `p^{(s−1)·(N−1)}·…` of them — the exact census is in W0's tables) are the TAIL, handed to
  the drainage census (§6), whose mass fraction `~ q^{−(N−1)} → 0`. (Classically these are
  the boxes whose cluster contains a root exactly at the center — the OM step splits off the
  exact `x`-power; at level N that split is below resolution, and drainage absorbs it.)
  ⚠ W0-ERRATUM F5: height bound `H ≤ N−1` suffices for matchable cells (the `N·s` bound in
  the original text is dead weight); size the Lean menu Finset by `N−1`.
  ⚠ W0-ERRATUM F2 (gate design): at p=2, N=3, s=4 the disc-bulk is EMPTY (min disc valuation
  4); disc-conditioned numeric gates for s = 4 need N ≥ 5. Left-endpoint-conditioned gates
  are non-vacuous at all tested (s, N).
  W0 artifacts: /workspace-vast/asving/tmp/phaseb_w0/ (menu_semantics.py, per-g tables,
  SUMMARY.md; residual convention F3 pinned there: t = 0 at the LEFT vertex, above-side
  pattern positions contribute 0, monic-normalize before shape read — matches the gateD
  classifier and oracle f-values, 0 mismatches incl. all 250 matched squarefree boxes).
* This matches the counting side exactly: PIN §1.2's `NodeConfig` IS a menu cell; the classifier
  and the counter consume the SAME menu object. Define the menu ONCE (`cellMenu s N : Finset
  NodeConfig`-like) and share it — the classifier checks membership, the counter sums over it.
  This single-source-of-truth kills the classifier/counter drift class of bugs (the V1 vacuity).

## §3 The order-r step (B-STEP), assembled from banked parts

Given: level-N box element g, current context T (genuine tower, key degree m, budget s).
1. KEY: the child key polynomial at level N, constructed explicitly (GMN §2 construction):
   `φ' := (lift of ψ̃ to the tower)(normalized φ-power)`-shape; representation: an element of
   the monic box of degree `m' = e·D·m`. The construction is explicit box arithmetic (no
   choice beyond the §1 transport). W2 delivers `childKey` + `childKey_natDegree` + the
   Eisenstein-type property needed by B-RING (§5).
2. DEVELOP: `developEquiv` (F-A) w.r.t. φ' on the cluster block: digits `b_j`, `deg b_j < m'`.
3. VALUATION READ: digit valuations at level N via the recursive `v_r` reader; soundness in the
   bulk from the :653 cite (reads < N are exact). The reader for order r is defined by recursion
   on r through the tower's key stack; W2 scope: ORDER 1 ONLY (reader = `zmodValuation` of
   x-adic digits — already exists), W6 generalizes.
4. CELL MATCH: §2 membership check against `cellMenu`.
5. RESIDUAL: on-side normalized unit residues (`boxCoeffData` generalized to the tower: values
   in Fr' via the §1 transport), assembled into the residual polynomial over Fr'; its
   factorization SHAPE (via `Polynomial.factors` multiset, noncomputable, as order-0 does).
6. EMIT: the ShapeCell with genuine (S, D, μ) children; child contexts via §4.

## §4 The recursion re-land (B-REC) — JOINT LANDING #2

`classifyAux` recurses through `genuineChildCtx T cell child` (order+1, tower extended by D,
key degree m', budget μ·D... — NOTE the budget-unit convention: A2's `childSize := μ·deg ψ` is
in PARENT-residue units; the genuine child budget in CHILD units is `μ` with the D absorbed into
the tower. Pin ONE convention in W2 and write the conversion lemma; the engine's convention is
child budget μ at residue q^{δD} — follow the engine).

BREAKING CHANGE, enumerated consumers (grep 2026-07-04):
* `classifyAux_indep` (Classifier.lean:585) — currently `rfl` because the context chain is
  f-independent. With genuine child contexts the tree depends on f THROUGH THE EMITTED CELL
  (that is the point). Rescope to: `classifyAux_ctx_factors`: the recursion context is a
  function of (T, emitted cell) alone. Consumers: :591-598 (in-file corollary), :1236
  (reduce-stability chain docstring — the chain itself consumes the corollary at the ROOT
  context only, where f-independence is genuine and survives). NO consumers outside
  Classifier.lean (grep clean). STOP-and-revert if the reduce-stability chain (certLevel_stabilizes)
  does not survive the rescope.
* `Order0Classify.classifyAux_unfold` / `classifyAux_of_childless` — respell (the JOINT-landing
  precedent applies verbatim; these spell the recursion body literally).
* `Order0Fiber.classifyAux_head_payload` — expected to survive (existential); verify.
* `treeSize_classifyAux` (Classifier.lean:1175) — reads the head tuple; verify.
Faithful child payloads land in the SAME wave (children := recursive `encodeCells` of the child
run), since both touch the same recursion body and two joint landings are worse than one.
Termination: unchanged (strong rec on budget; self-loop cells emit no child — the emitted shape
records the self-loop cell and the DEPTH CAP is N (certLevel); drainage in §6).

## §5 B-RING: the level-N avatar of O_L (new leaf module, F-B1-style delegable)

The restart target ring: `Rphi := ZMod (p^N) [X] ⧸ (φ')` for the Eisenstein-type child key φ'.
Facts to bank (each elementary, PARI-gateable):
* `Rphi` is a finite local ring; `card Rphi = p^(N·m')`.
* The digit identification: `degreeLT (ZMod (p^N)) m' ≃ₗ Rphi` (evaluation/quotient map) —
  composing with `developEquiv` gives the COUNT form of Lemma A + evaluation: the monic box of
  degree k·m' ≅ (Fin k → Rphi), cardinality-preserving. This is RESTART_LEMMA §10's
  "b ↦ b(θ) carries digit spaces to O_L" at level N.
* The π-adic filtration: powers of the maximal ideal, `card (m^j) = p^(N·m' − ⌈…⌉)` — the
  index law `[Rphi : π^j] = Q^j` in its level-N form (Q = p^{δfD·…}: spell per convention).
* The valuation reader `vphi : Rphi → ℕ∞` (order in the π-filtration) + unit residues into the
  residue field (which is the §1 canonical field — ONE lemma ties `Rphi ⧸ m ≃ GaloisField p k`).
GATE (F2′): brute-force at p = 2, N ≤ 3, φ' = x² − 2c: card, filtration sizes, vphi table vs
PARI. This module is delegable NOW (it does not depend on W1-W3 landing) with the F-B1 prompt
pattern; it consumes only Development.lean.

## §6 Drainage (h_env-v2) and the depth cap

Level-N truncation admits ≤ N orders of refinement (each order costs ≥ 1 in certified
discriminant valuation; bulk gate `v_p(disc) < N`). Undecided mass at level N = boxes whose
classification hits the cap or the tail. Statement shape:
`undecidedCount n N ≤ C(n) · q^(nN) · q^(−N)` (the B2-filtration-gated bound: each self-loop
iteration costs `q^(−(e(e+1)/2−1)) ≤ q^(−2)`, each tail membership costs `q^(−N)`), hence
`undecidedDensity → 0`. Numeric gate exists (the §2.7/B2 filtration battery, p ∈ {2,3,5}
identical). Lean scope: state over the genuine classifier only (W5); do NOT state over shells
(falsifiability probe: the shell classifier decides everything at order 0, making drainage
vacuous — the probe must FAIL on shells, i.e. the statement must mention genuine cells).

## §7 F-C: the restart lemma in Lean (the target statement)

With W1-W5 landed, h_node-v2 (`node_limit`, PIN §1.4) is discharged on the order-1 slice by:
  (i) cell decomposition: box = disjoint union over `cellMenu` of cell fibers (§2 uniqueness +
      exhaustiveness) — the Order0Fiber pattern one level up;
  (ii) per-cell count: `card (cell fiber) = m_cell(c,q) · q^(nN − B(c))` — digit coordinates
      (F-A) + per-digit valuation counts (F-B1 atoms `card_range/ker_mul_pow`) + residual-shape
      counts over the tower (Necklace + L3 over GaloisField — L3 lemmas are field-generic;
      verify instances);
  (iii) the block split: cell fiber ≅ product of block fibers × p^(cross-block budget) — F-B2/
      F-B3 (HenselCount torsor + assembly) with the resultant valuation pinned by F-B4;
  (iv) the child re-coordinatization: block fiber over the parent ≅ fresh box over `Rphi` (§5),
      and the child's cell conditions transport through `vphi` (GMN Prop 2.9 at level N — the
      dictionary lemma, W4's hardest item; TRANSCRIBE RESTART_LEMMA §10's proof, do not
      re-derive).
Then `AX_cellRecursion` (PadicMeasure.lean:438) is dischargeable-or-retirable: the count-native
capstone chain never consumed it (it is on the R5 quarantine path), so F-C lands as the POSITIVE
theorem `stratumCount_factor_card`-v2 with `node_limit` discharged, and R5 proceeds.

The f ≥ 2 descent (Weil restriction, conjugate blocks) is W6, AFTER the f = 1 spine works
end-to-end at order 1 (mirrors the paper's two-step descent and Gate D's tested case).

## §8 Wave plan (each: numeric gate → Lean → 7-gate audit → bank)

* W0 (gate only): classifier ground truth at order 1 — reuse the calibrated
  `restart_gates` classifier; brute-force `p = 2, N = 3, n ∈ {2,3,4}`: every box element's
  order-1 cell vs the menu semantics of §2. Zero mismatches required. ALSO: R0 (PIN §3) is
  running (launched 2026-07-04); its report's conventions BIND this document's §4 budget-unit
  and §5 Q-spelling choices.
* W1: B-RING module (§5) — delegable now, F-B1-style spec + gate.
* W2: `cellMenu` + order-1 B-STEP behind a NEW function (`classify1`), no body change to
  `classifyAux`; parity lemma `classify1 = classify` on order-0-decided strata; LEM B.1 (:1112)
  discharged here (endpoint units from vertex-exactness of the matched cell). Numeric gate: W0
  table vs `classify1` on the same boxes (transcribed values).
* W3: B-REC joint landing #2 (§4) + faithful payloads + `GMNNodeEfLaw` becomes a theorem;
  LEM B.8 (:1258) discharged (separable ⟹ no cell matches with a child).
* W4: h_node-v2 order-1 discharge (§7 i-iv). This is the F-C core.

  **W4 SPEC (pinned 2026-07-04 against landed signatures — all inputs now machine-checked:
  F-A `developEquiv`, F-B1 `LinearFiber` atoms, F-B2/3 `HenselCount.fiber_card/image_card`,
  F-B4 `SparseResultant.resultant_sparseTwist_isUnit/_cross` + dominant-transversal,
  W1 `RphiRing.digitEquiv/card_span_theta_pow/vphi`, R1 `OMCountV2.mCell/volExp/omChildCount`,
  W2 `CellMenu.InCell/cell_unique/cell_exists/classify1`).** Four statements, in order:
  - **W4a `cell_partition`** (easy, from W2): the readable cluster box is the disjoint union of
    the `InCell` fibers over `cellMenu s N`; card version via `cell_unique` + `cell_exists`.
  - **W4b `cell_card`** (delegable first): for `c ∈ cellMenu s N`,
    `card {f | InCell f c} = mCell(c, p) · p^(free(c, N))` with the explicit free-digit exponent
    (per-coefficient independence: each ≥-floor at height m contributes `p^(N−m)` — F-B1 atom
    `card_range_mul_pow` shape; each vertex =-condition `(p−1)·p^(N−m−1)`; the joint
    residual-shape condition on on-side unit residues contributes the shape count — Necklace/L3
    over the unit residues, with the `(p−1)`-normalization folded per R1's `choicePoly`).
    MANDATORY numeric gate: the formula must reproduce W0's exact per-cell census at
    p=2, N=3, s ∈ {2,3,4} (e.g. the slope −1/2 cell's total-match counts) as proved `decide`/
    `norm_num` examples. Consistency corollary: summing W4b over the menu against W4a must
    reproduce the readable-box card — state it, it is free and catches exponent bugs.
  - **W4c `block_split`** (the Master Lemma applied): for cells whose data has k ≥ 2 coprime
    blocks (distinct sides, or coprime residual factors on one side): the `InCell` fiber is in
    bijection with (product of per-block fibers) × (a `p^crossBudget`-torsor) — via
    `HenselCount.fiber_card` with `hres` supplied by the SINGLE-POINT value at the cell's
    standard representative (`resultant_sparseTwist_isUnit` same-side / `_cross` cross-side —
    build the representative as an explicit PRODUCT, never factor) + `resultant_stable` across
    the cell (pin depth vs c margin: record the inequality per cell, it is a menu datum).
  - **W4d `child_restart`** (the heart; transcribe RESTART_LEMMA §10, do NOT re-derive): for a
    child (S, root c̃, μ) of a cell, with φ := X^e − C(c̃)·C(p)^h (the W1 `RphiRing.phi`):
    conditioned on `InCell f c`, the child's digit avatars under `developEquiv` ∘ `digitEquiv`
    are `Rphi`-uniform on the pattern coset, and the child's further refinement census over
    `Rphi` (at `vphi`-level, `e`-rescaled) equals the fresh cluster census at residue size p
    (f = 1 spine; the level bookkeeping: parent level N ⟹ child `vphi`-budget `N·e − (polygon
    offset)` — spell against `card_span_theta_pow`). Scope: order-1, f = 1, h = 1 FIRST
    (matches W1's banked layer); general h needs W1's tower extension — schedule as W4d′.
  - **W4d2-surj (NAMED OBLIGATION, verifier finding 2026-07-05 — theorem of the product at
    level N).** The landed multi-block theorems (`h_node1_at_A/C`, `h_node1_census`,
    `h_node1_general`, `caseA/C_node_census`) count `imageSet` = the image of the block-coset
    product under polynomial multiplication, and tie THAT to the counting recursion. They do
    NOT identify `imageSet` with the classifier's multi-block `InCell` fiber; indeed no
    multi-block `InCell` is defined in `CellMenu` yet (W2 scope was single-side). The
    identification `imageSet = {f | multi-block InCell f c}` — the "sides add, residuals
    multiply" theorem of the product / Hensel factorization surjectivity — is GATE-VERIFIED
    numerically (d2-0: the fiber counts 8192/81/19683 equal the image counts, and the mult map
    was checked surjective onto the fiber box-by-box) but is NOT formalized. Closing it: (a)
    define `InCellMulti` in CellMenu for a multi-side / multi-coprime-factor cell (concatenated
    polygon + per-side residual shapes); (b) prove `InCellMulti f c ↔ ∃ factorization f = Π gᵢ
    with gᵢ ∈ block cell` (⊇ is polygon concatenation; ⊆ is coprime-Hensel lifting — the
    resultant-unit ⟹ Bezout ⟹ split argument, or mathlib's coprime factorization); (c) transport
    the em-square count. The SINGLE-block restart needs none of this — `RestartEquiv.restartEquiv`
    is already a genuine bijection to the classifier fiber. This joins {deeper-order v_r reader,
    f ≥ 2 Weil descent, general-h tower} on the named-open list; it does not affect any checked
    footprint's soundness (the imageSet theorems are true as stated).
  - **W4d2-surj STATUS 2026-07-05 (CONSOLIDATED to ONE lemma):** ⊇ condition (iii) residual
    multiplicativity is CLOSED (`M4.residualPoly_mul` ResidualPolynomial.lean:133 + `residualOf_mul_of_conv`
    ProductTheorem:239, core-only); the (ii) building blocks are proven (`zmodValuation_mul` :184,
    `zmodUnitResidue_mul` :206 — valuations add / unit residues multiply below the cap). CRITICAL
    FINDING: BOTH the remaining (ii) vertex-exactness AND the ⊆ Hensel surjectivity now funnel
    through a SINGLE missing lemma `on_side_conv` — the on-side dominant-term convolution law
    (`boxCoeffData(A·B) t = Σ_{s+u=t} boxCoeffData A s · boxCoeffData B u`) + "valuation/unit-residue
    of a sum with a UNIQUE dominant term is that term's". This is exactly the
    `SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal` philosophy — the graded engine
    already banked. So the ENTIRE theorem of the product (both inclusions) reduces to `on_side_conv`
    + applying it. Assembly (`imageSet_subset_inCellMulti`, `card_imageSet_le_fiber`, the fiber
    identity) is banked as precise obligations (NOT sorry-theorems) pending `on_side_conv`. Sympy-
    gated 0 violations (coeff_conv_check.py cases B,C). This is now the single highest-value
    remaining Phase-B lemma.
  - **W4d2-surj STATUS 2026-07-05 (crux PROVEN, remainder = plumbing + Hensel):** the dominant-term
    valuation LAWS are now machine-checked and reusable — `ProductTheorem.zmodValuation_sum_unique_min`
    :358 (unique-min ⟹ sum = p^V·unit; scalar analogue of `det_eq_pow_mul_unit_of_dominant_transversal`)
    and `zmodUnitResidue_sum_common_min` :466 (the convolution's actual need: several on-lattice
    splits at the same min valuation, residues ADD mod p) — both core-only, sympy-verified 5400
    cases / 0 violations. The theorem of the product now decomposes into exactly THREE remaining,
    NONE of them new analytic math: (P1) `on_side_conv` = antidiagonal-geometry WIRING of the banked
    laws (per-coeff "A exactly on side" interface + `Finset.antidiagonal` reindex on/off-lattice +
    cofactor supply) — touches `boxCoeffData`/`Matches` in CellMenu/Classifier; (P2) the ⊇ assembly
    needs an out-of-module BRIDGE `cellOf : List Block → NodeConfig` — `BlockProduct.Block` carries
    only {center,deg,coset}, no side datum, so a Block-structure enrichment (parallel BlockWithSide
    or side-data carrier; adding a field breaks constructors); (P3) ⊆ `obligation_hensel_surjective`
    = existence of a block factorization, needs the W4d2′ graded margin. NEXT WAVE (coordinated,
    touches ProductTheorem + BlockProduct + CellMenu): P2 bridge, then P1 wiring, then ⊇ assembly
    becomes real theorems; P3 (Hensel) last and hardest.
  - **⊇ CLOSED (Matches-free) 2026-07-06 for the gate cell shapes.** `on_side_conv` proven;
    `offBlock_unit_on_side` :1401 (off-side blocks are units ⟹ drop from the residual shape);
    `product_matches_single_side` / `product_matches_two_distinct` :1454; the Matches-free
    inclusions `imageSet_subset_inCellMulti_{single,two_distinct}_free` :1347/:1495. So products
    PROVABLY lie in the classifier cell (1-block + 2-distinct-block = cases A/B/C), core-only.
    Remaining ⊇ increment: the general k-block fold (incremental bookkeeping over the 1/2 cases).
  - **P3 REBLUEPRINTED 2026-07-06 — the CARDINALITY route (avoids constructive Hensel):** the ⊆
    direction / full identity `{f | InCellMulti f c} = imageSet` need NOT be a Hensel existence
    proof. We already have (a) `imageSet ⊆ fiber` (the ⊇ Matches-free inclusion above) and (b)
    `image_eq_of_subset_of_card_le` :769 (`A ⊆ B ∧ #B ≤ #A ⟹ A = B`, unconditional). So it
    suffices to show `#fiber ≤ #imageSet`, and since `#imageSet · p^X = Π coset`
    (`blocks_card_graded`), it suffices to prove the INDEPENDENT fiber count
    `#{f | InCellMulti f (cellOf l)} · p^X = Π coset` — a COUNTING argument, not existence.
    Route: `CellCard.cell_card_raw` is ALREADY general over multi-side polygons+shapes (it proved
    the S3C3 TWO-sided cell = 8); apply it to `cellOf l`'s concatenated polygon + per-side shapes
    to get `#fiber = prodSC · p^freeExp`, then the arithmetic identity
    `prodSC · p^freeExp · p^X = Π (per-block coset card)` (freeExp + shape-count vs the per-block
    freeExps + the cross exponent X = Σ mᵢmⱼwᵢⱼ — a lattice bookkeeping check, sympy-gateable
    against the d2-0 numbers 81/8192/19683). Then forcing ⟹ `inCellMulti_eq_image` = the FULL
    theorem of the product, and the genuine classifier-fiber node identity
    `#{f | InCellMulti f c} · p^X = Π coset`. This is the tractable close — mostly reusing
    cell_card_raw + an exponent identity, NO Hensel lifting. Gate first: the freeExp/X arithmetic
    at cases B (81), A (8192), C (19683) must balance exactly. DELEGABLE after build #15 (owns
    ProductTheorem; consumes CellCard.cell_card_raw + BlockProduct/GradedHensel counts).
  - **P3 FIXED-ROOT-PIN LANDED 2026-07-06 (case C node identity CLOSED OUTRIGHT):** the prodSC>1
    gap named above is closed. ProductTheorem §15/§15a (core-only [propext, Classical.choice,
    Quot.sound], no sorry/axiom/native_decide, in-file elaboration exit 0). The FIXED-root pin fixes
    the per-side residual to a SPECIFIC monic prime-to-X polynomial R* (product of on-side block
    residuals), collapsing the `prodSC = shapeCount l` shape-matching residuals to ONE: the
    fixed-target pattern-block count is a SINGLETON (`card_patPart_fixed` = 1, vs
    `CellCard.card_patPart` = shapeCount l), everything else identical, so the box count drops
    prodSC·p^freeExp → p^freeExp. Single-side chain built in ProductTheorem (owns file; consumes
    CellCard.{card_supp_split, card_pi_fiber, card_digit_fiber, coeffEquiv, matches_iff,
    residualOf_eq_sidePolyR, sidePolyA/R}): `card_sideSet_fixed` → `card_digCond_fixed_single` →
    `cell_card_raw_fixed_single` (= p^freeExp) → `inCellMulti_single_fixed` →
    `card_inCellMulti_fixedpin_fiber_single`. Case C: `card_inCellMulti_fixedpin_caseC` = 19683 = 3^9
    OUTRIGHT (R* = (X−1)(X−2)² over ZMod 3, `residC_shape` gives polyShape = [(1,1),(1,2)]); then
    `gate_node_C_closed`: #{fixed-pin InCellMulti fiber}·3⁴ = 19683·3⁴ = Π coset
    (`BlockProduct.gateC_coset_product`) — the node identity for case C, no ⊇ forcing needed for the
    count form. Cases A/B (prodSC=1) unchanged: fixed pin = tautological pin, `gate_node_A/B` intact.
    py gate FIRST (/workspace-vast/asving/tmp/phaseb_fixedpin/): direct digit enumeration proves case
    C's 2 residual classes EQUINUMEROUS (each 27·729 = 19683 = p^freeExp; 2·19683 = 39366 = shape
    fiber). REMAINING (not overclaimed): general k-block / multi-side fixed-pin count (only single-side
    B,C covered; A prodSC=1), and the fixed-pin ⊇ SET-identity {fixed-pin fiber} = imageSet (needs the
    per-element residualOf(Πgᵢ) = R* factorization) — the count-form node identity is closed for C.
  - **W4e `h_node1`** (assembly): for order-1 cluster-bearing menu shapes, the level-N stratum
    census factorizes per the omCount node identity — extending `h_node0_proved` beyond the
    separable slice; this discharges `node_limit`'s order-1 slice (PIN §1.4) and IS the
    restart lemma at order 1 in count form. F-C's remaining gap after W4e: deeper orders (the
    v_r reader, W6) and f ≥ 2 (W6), then the full statement (W7).
  Delegation order: W4b now (after build #2 green); W4c after W4b (consumes its per-block
  counts); W4d after W4c — W4d is the candidate for coordinator-led work if agents wobble
  (PIN §5's fake-close warning applies most strongly here).

  **STATUS 2026-07-04 (late): W4a + W4b ✅ LANDED** — `LeanUrat/OM/CellCard.lean` (2273 lines,
  20 theorems core-only, exit 0). `cell_partition` :1705 (+ disjoint/cover/readable);
  `card_clusterBox = p^(s(N−1))` :1716, `card_readableBox = p^(s(N−1)) − p^((s−1)(N−1))` :1787
  (both GENERAL, not just gated); `cell_card_raw` :1579 GENERAL closed form
  `prodSC · p^(freeExp)` via the right-anchored telescope (per-side residual anchored at the
  monic cap — anchor-independence is what makes vertex-shared chains multiply exactly);
  `cell_card_mCell` :2095 (mCell tie, per-shape ties banked for [(1,1)],[(1,μ)],[(2,1)],
  split@p=2; the fully-general multiplicity-multiset tie = sanctioned remainder). ALL SEVEN W0
  census gates proved exactly (8/2/2/0/32/8/128) + consistency sums 12/48/192.
  **SEQUENCING REVISION:** `cell_card_raw` counts multi-side/multi-factor cells DIRECTLY
  (S3C3 two-sided = 8 proved without any block splitting), so a standalone W4c is NOT needed
  for the bare per-node count. W4c's genuine content — conditional independence of the
  CHILDREN's further refinements across blocks (HenselCount torsor + SparseResultant
  single-point + stability) — folds INTO W4d, where it is actually consumed. W4d is next,
  coordinator-blueprinted before any delegation. CellCard.lean not yet imported from root
  LeanUrat.lean (one line at integration; AxChk imports it directly meanwhile).
* W5: drainage (§6).

## W4d SPEC (pinned 2026-07-04, coordinator-authored — the child restart at level N)

Scope ladder: (d0) numeric gate; (d1) the single-block restart equivalence; (d2) multi-block
composition. Order-1, f = 1, h = 1 throughout (W1's banked RphiRing layer); general h = W4d′
after W1's tower extension.

**The statement shape is ONE equivalence, not a census formula.** For the single-side
single-repeated-root cell `c` (polygon = one side of slope −1/e, length s = e·μ, μ ≥ 2,
residual (y − c̃)^μ, c̃ unit — NOTE e = 1 is the SELF-LOOP cell: φ = X − c̃·p is the
recentering key, Rphi ≅ ZMod (p^N), and this simplest instance is exactly what the tower
induction consumes at self-loops; e ≥ 2 is the genuine ramified restart, Gate D's shape):

```
restartEquiv : {f : monicBox p N s // InCell p f c}
             ≃ {β : Fin μ → Rphi // FreshClusterPattern c β}
```

where `restartDigits f := digitEquiv ∘ developEquiv_φ f` (F-A + W1 composed; φ := RphiRing.phi
with e, c̃-lift, h = 1) and `FreshClusterPattern` is the D0-VERIFIED pattern (2026-07-04 gate,
9 cases p ∈ {2,3}, N ≤ 4, μ ∈ {2,3}, bijection verified three ways per case, child transport
0 mismatches on 268 readable boxes × 4 lifts; /workspace-vast/asving/tmp/phaseb_w4d0/):
```
FreshClusterPattern c β := ∀ j < μ, β j ∈ (span {θ})^(e·(μ−j) + 1)
```
PURE ideal membership: e-SCALED, STRICT (+1), and RESIDUE-FREE — three corrections to the
originally pinned display (`≥ μ−j` with endpoint exactness + unit residues), which was wrong:
spec-literal gives 512 vs true fiber 16 at the s=4 case; rescaled-but-not-strict gives 64.
The parent's exactness/unit-residue pins (incl. the nonzero binomials at p = 3, μ = 3) are
carried EXACTLY by the cap `φ^μ`'s coefficients `C(μ,t)(−c̃'p)^(μ−t)`, not by the digits — the
digit space is a clean coset. Fiber card = `p^(μ(Ne−1) − eμ(μ+1)/2)` (via W1
`card_span_theta_pow` per slot). Fresh determinacy law confirmed one level down (mirrors W0's
sharp law): decided ⟺ `vphi (β 0) < N·e`. Errata: the RESTART_LEMMA display referenced is
§13.1's (not §10's); no p = 3, N = 2, μ ≥ 2, h = 1 cell exists (left vertex height μ > N−1) —
p = 3 gates need N ≥ 3.
Census corollaries are then DEFINITIONAL: for ANY predicate Q on the β-space,
`card {f | InCell f c ∧ Q (restartDigits f)} = card {β | Pattern β ∧ Q β}` — the child's
refinement census IS the fresh conditioned-cluster census over Rphi. No division, no measure.

**The technical heart (the dictionary lemma):** InCell reads x-adic coefficients `a_i` of f;
the pattern reads `vphi (β j)`. The bridge: `f = φ^μ + Σ b_j φ^j` with
`φ^j = Σ_k C(j,k)(−c̃p)^(j−k) X^(ek)` — a p-weighted TRIANGULAR (sparse-twist-shaped) transform
between the a-coefficients and the b-digit coefficients. Prove the valuation dictionary
`(InCell pattern on a) ⟺ (vphi pattern on β)` by triangular induction (the same
dominance structure SparseResultant's transversal lemma formalizes; strictly-above-polygon
digits influence nothing — GMN Prop 2.9's level-N shadow, here elementary because order 1).
Numeric ground truth FIRST (d0): extend menu_semantics.py — at p = 2, N = 3, enumerate the
s = 2 self-loop cell (e = 1, μ = 2; 2 boxes) and the s = 4 slope −1/2 {(1,2)} cell (e = 2,
μ = 2; 16 boxes): compute β-digits by explicit division, verify the bijection box-by-box, and
verify the child-data transport (classify the β-tuple over Rphi-mod-θ-powers vs the direct
order-2 refinement read of f) — zero mismatches required. Also run one p = 3 case (the gates
so far are all p = 2; the dictionary must not silently use p = 2 facts).

**(d2) multi-block cells — GATE-CORRECTED FORM (d2-0 passed 2026-07-04, torsor constants
16 = 2⁴ / 9 = 3² / 81 = 3⁴ all MATCHING the §8 w-table; /workspace-vast/asving/tmp/
phaseb_w4d2_0/):** the naive `fiber ≃ Π blocks × torsor` is FALSE (off by p^(2X) in case A).
The verified law: `|fiber| · p^X = Π_i |P_i|` with `X = Σ_{i<j} m_i m_j w_ij` — equivalently
**{(f, level-N factorization of f)} ≃ Π_i P_i** (the multiplication map Π cosets → fiber is
exactly p^X-to-1). This is PRECISELY the k-block iteration of the banked
`HenselCount.image_card`, with per-block cosets given by `RestartEquiv.FreshClusterPattern`
(child-bearing blocks, floor e(μ−j)+1) and the SAME formula at floor e+1 for decided μ = 1
blocks (uniform bookkeeping; shape-only cells additionally multiply by the residual-assignment
count). `hres` per pair from SparseResultant single-point at the standard PRODUCT
representative + `resultant_stable`. INDEPENDENCE is census-level only (exact product law on
factorization censuses — Gate C correctly stated); per-f section independence FAILS (violations
confined to torsor-deep reads) — do NOT state section-wise. Marginal restart law verified:
marginal class census = standalone block census × |fiber|/|C_i| exactly. N-margin erratum
recurs: multi-block cells need the left-vertex height ≤ N−1 (case A needs N ≥ 5, C needs
N ≥ 4). Only after (d1) — now landed, so DELEGABLE.

**STATUS 2026-07-04 (late): W4d2-1 ✅ LANDED, with a NAMED remaining obligation.**
`BlockProduct.lean` (682 lines, 21 declarations core-only): `pair_card`/`pair_card_pattern`
(:162/:205, sub-cell product law under explicit margins `c+1 ≤ floors ≤ N−c`), `blocks_card`
:471 (k-block fold), `mul_image_saturated` :271 (one-step adjugate Hensel, margin
`N ≤ 2(m−c)`), `caseB_hres` :543 (hres pinned at the RphiRing-shaped representatives via the
new bridge `phi_eq_sparseTwist` :526). Gate instances proved DIRECTLY: `gateB_law` :621
(`81·3² = 27·27` by decide), A/C closed-form coset products :654/:669. **HONEST GAP, precisely
named (no-wall discipline): the flat margins are gate-EMPTY** — `2c < N` fails at all three
real cells (`gate_margin_*` :496–502) and the pattern floors are neither in-cell nor
kernel-saturated (`gate_floor_B` :507). **W4d2′ (the closing lemma): redo the HenselCount
bootstrap in the θ/polygon-GRADED filtration** — per-slot floors vs the graded resultant
valuation, with `SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal` as the kernel
engine (the graded Sylvester matrix is dominant-transversal; the graded kernel bound replaces
the flat `p^(N−c)`-divisibility). Until W4d2′: W4e proceeds for single-block cells (RestartEquiv
is margin-free) + the gate-verified multi-block instances; multi-block h_node1 in general form
is hypothesis-gated on the graded margin.

Delegation: (d0) delegable immediately (python); (d1) delegable ONLY with (d0)'s box-by-box
tables as the gate and the dictionary lemma named as the single hard obligation — STOP-and-
report if the triangular induction resists; (d2) after (d1). W4e assembles (d1)+(d2)+W4b into
`h_node1` (the order-1 restart identity).
* W6: f ≥ 2 descent; deeper orders (the v_r reader recursion). SCOPED (2026-07-06) into three
  independent sub-directions, ordered by tractability — each gate-first, each a separate wave:
  - **W6a — general-h RphiRing filtration ✅ LANDED 2026-07-06 (with a load-bearing REFUTATION).**
    `RphiRingGenH.lean` (441 lines, 33 decls core-only, additive on stable W1 RphiRing). GATE
    REFUTED my naive scoping: on the LEVEL-N ring you cannot divide by p, so the attainable
    vL-values form the NUMERICAL SEMIGROUP ⟨e,h⟩ = {i·h + k·e}, which for gcd(e,h)=1, e,h≥2 has
    GAPS (⟨2,3⟩ misses 1). Consequences (all gate-verified 0-mismatch, py refutation FAILS the
    naive claim): (i) there is NO valuation-1 uniformizer, so `card{vL ≥ j} = p^(Ne−j)` is FALSE
    for h≥2 — the correct count is the PER-DIGIT PRODUCT
    `card(filtIdeal j) = p^(Σ_{i<e}(N − min(N, ⌈(j−ih)/e⌉⁺)))`, collapsing to p^(Ne−j) at h=1;
    (ii) the maximal ideal is `span{θ, p}` NOT `span{θ}` for h≥2 (p ∉ (θ) when e<h), collapsing
    to span{θ} at h=1. BANKED: `vL` via honest `filtIdeal`+findGreatest, `isLocalRing`,
    `maximalIdeal_eq_span_theta_p`, residue field F_p (resHom, card_residueField = p, f=1
    unchanged), filtIdeal_antitone/theta_mem/natCast_p_mem, lower bounds le_vL_theta (h ≤ vL θ) /
    le_vL_natCast_p (e ≤ vL p), and the h=1 COMPAT vL_eq_vphi_of_h_one +
    span_theta_p_eq_span_theta_of_h_one (recovers RphiRing exactly). NAMED RESIDUAL: the reverse
    anchors vL θ = h / vL p = e and the product-count for h≥2 need the ⟨e,h⟩-graded strictness
    (fresh per-digit proof; e=2 tractable, e≥3 harder). LESSON for W6b/W6c: the general-h restart
    is genuinely more subtle than h=1 (gapped value semigroup) — the digit-coset structure of a
    gapped filtration must be handled, not assumed θ-adic.
  - **W6b — f ≥ 2 unramified descent** (the paper's Step 1). RphiRing is f=1 (residue F_p);
    f≥2 needs the residue tower GaloisField p (k·f) per D-CTX. The Master Lemma / SidedBlock
    already model the block split; W6b adds the unramified extension O'' and the Galois-conjugate
    block factorization G = ∏ Frob^i(G_1) (RESTART_LEMMA §8 f-descent). Deliverable: the f≥2
    child-restart equivalence (RestartEquiv is f=1) — the conjugate-block product = Weil
    restriction, constant-Jacobian by the Master Lemma. Numeric gate: the Gate-B f=2 μ=2 cell
    (already in phaseb_w4d0 case B — the f=2 transport was verified there). Owns a NEW module.
  - **W6c — deeper-order v_r reader** (order ≥ 2; the hardest, subsumes the tower induction).
    CellMenu's classify1 reads order-1 (x-adic) data; order ≥ 2 needs the recursive valuation
    reader through the key-poly tower (the SelfLoopTower two_level_census is the e=1 order-2
    base case — already banked). Deliverable: classify_r / the v_r reader recursing through
    childKey; the two_level_census generalizes to k-fold via induction. This is where the full
    F-C tower induction lives. Blueprint further (own §) before delegating — the recursion-body
    change touches Classifier (enumerated-consumers discipline, the childCtxOfSize precedent).
  Order: W6a (self-contained, unblocks general-h everywhere) → W6b (f≥2, needs GaloisField tower)
  → W6c (deeper orders, needs W6a+W6b + the tower induction). Each is a genuine wave, not a lemma.
* W7: F-C full statement; R4/R5 retirements proceed per PIN §3.

Standing rules: numeric gate BEFORE each Lean wave; no wave without its falsifiability probe
(shells must FAIL genuine statements); enumerated consumers before any recursion-body change;
STOP-and-revert on parity/gate failure; footprint harness in the same build as every landing.
