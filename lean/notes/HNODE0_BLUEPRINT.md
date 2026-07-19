# HNODE0_BLUEPRINT — discharging `h_node0` (making `montes_order0` unconditional on Lean core)

**Status: 2026-07-02, written BEFORE the Lean (blueprint-first).** Target: the hypothesis of
`LeanUrat.OM.Order0.montes_order0` —

```
h_node0 : ∀ T ∈ sepShapesOf n σ,
  Tendsto (fun N => M8.stratumCount (M9.rawCount n) T N / realP^(n·N)) atTop
          (nhds (rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T realP))
```

— becomes a THEOREM at `realP = 2` (and, with the same proofs, any pinned prime `p`). Every cited
signature below was verified against the live tree on 2026-07-02.

---

## §0 — D7: `boxCoeffData` is WRONG OFF-SIDE (blocking defect; fix FIRST)

**The defect (Classifier.lean:110-113).**
`boxCoeffData p N S f t := PadicLift.zmodUnitResidue p N (f.coeff (S.i₀ + t·S.e))` — the unit residue
of the coefficient UNCONDITIONALLY. The GMN residual coefficient (Def 2.20, and the definition's own
docstring: "divide out the side height `v_t`") is the unit part ONLY when the dot `(i₀ + t·e, v)`
LIES ON the side; it is `0` when the dot lies strictly ABOVE. `zmodUnitResidue` divides out the
coefficient's OWN valuation, so an above-side coefficient contributes its unit part instead of `0`.

**Concrete counterexample** (`p = 2`, `n = 2`, flat side): `f = x² + 2x + 1`. Genuine residual =
`f̄ = x² + 1 = (x+1)²` (non-separable, double root). Current code: `c₁ = zmodUnitResidue(2) = 1`, so
the computed residual is `x² + x + 1` — IRREDUCIBLE over `F₂`. The classifier calls a non-separable
reduction "inert-separable": the strata are wrong wherever any coefficient sits strictly above the
selected side. (All previous rounds were blind to this: with the old degree guard the residual was
zeroed anyway.)

**The fix.** Add the on-side guard. The side `S` from `(i₀, v₀)` to `(j₀, v₁)` in lowest terms
(`slope = h/e`, `Side.e = slope.den`, `Side.h = slope.num`, NewtonPolygon.lean:201-204) has integer
lattice heights at the step abscissae: `height(t) = v₀ + t·h` (an integer since `slope·(t·e) = t·h`).

```lean
noncomputable def boxCoeffData (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (S : NewtonPolygon.Side) (f : QuotientBox.monicBox p N n) : ℕ → ZMod p :=
  fun t =>
    if (PadicLift.zmodValuation p N ((f.1).coeff (S.i₀ + t * S.e)) : ℤ) = (S.v₀ : ℤ) + t * S.h
    then PadicLift.zmodUnitResidue p N ((f.1).coeff (S.i₀ + t * S.e))
    else 0
```

*Notes.* (i) On the FLAT side (`v₀ = 0`, `h = 0`) the guard reads `zmodValuation = 0`, i.e. the
coefficient is a unit; then `zmodUnitResidue = the plain mod-p reduction`, and off-guard `c_t = 0` —
so `residualPoly (boxCoeffData …) (flatSide n) = f̄` EXACTLY (γ3 below). (ii) `zmodValuation` of a
ZERO coefficient is `N` (PadicLift.lean:83-84) — the zero coefficient is never on-side for `N` large;
for small `N` (reads at the precision boundary) the guard behaves like the truncated read, which is
the correct level-`N` semantics. (iii) A coefficient BELOW the side cannot exist (the side is on the
lower hull of the support) — no clause needed, but do NOT assume it in proofs; the guard is an
equality test either way.

**Ripple analysis** (grep `boxCoeffData` — sites verified): `rootResidual`/`fRootCtx` (definitional,
no proof change); `boxCoeffData_endpoints_ne_zero` (Classifier sorry at ≈:1059 — with the guard this
becomes PROVABLE: the endpoints of a genuine `npSides` side are hull VERTICES, so their dots are
on-side by construction and their unit residues are nonzero by `zmodUnitResidue_ne_zero`); the Layer-B
reduction-stability lemmas (`boxValSupport_reduce_stable_R` cluster) — they prove `boxCoeffData`
stability under `boxReduce` from valuation-read stability; the guard consumes exactly the same
ingredients (valuation equality is `zmodValuation_reduce_stable`) plus the height equality, which is
side-data (stable by `npSides_congr`). Also `cellsOfType_omStep`/`classify` consumers: definitional.

**Numeric gate for D7 (run BEFORE the Lean edit).** Brute-force over `ZMod(p^N)`, `p ∈ {2,3}`,
`n = 2, 3`, `N = 2, 3`: for every monic `f` with unit `a₀`, check
`residualPoly(fixed boxCoeffData)(flat side) = f mod p` coefficientwise, and re-derive the λ-stratum
counts of the FIXED classifier = `m_λ`-table of VACUITY_SIGMA_BLUEPRINT §2.5 (they must now agree —
the earlier gates validated the intended semantics, not the code).

---

## §1 — (γ) the face-equality gate: `classify p n N f = sepShape n λ(f̄)` on the generic stratum

For `f ∈ monicBox p N n` with `zmodValuation (f.coeff 0) = 0` (unit constant coefficient) and `f̄`
(:= mod-p reduction) SEPARABLE with factor-degree pattern λ. Chain (each node a separate lemma):

**γ1 (flat hull).** `npSides (boxValSupport p N f) _ = [flatSide n]`.
* Support facts: `(0, 0) ∈ boxValSupport` (unit `a₀` ⟹ `a₀ ≠ 0` ⟹ `0 ∈ f.support`, valuation 0);
  `(n, 0) ∈ boxValSupport` (monic); every dot `(i, v)` has `v ≥ 0` (ℕ) and `i ≤ n` (degree).
* Hull: the line through `(0,0)–(n,0)` is VALID (all heights ≥ 0), so `npHeight ≥ 0`-chord = 0 on
  `[0, n]`; and `npHeight ≤ 0` at the two anchor dots (`npHeight_le`); with convexity ⟹
  `npHeight ≡ 0` on `[0, n]`. Banked ingredients: `npHeight_le`, `npHeight_convexOn`,
  `npHeight_eq_pairLine_of_validLine` (the breakpoint lemma — applied to the flat valid line it gives
  `npHeight ≡ 0` on `[0,n]` DIRECTLY, no convexity juggling: the chord through `(0,0),(n,0)` is valid
  and flat).
* `hullDots = the height-0 dots`; `hullAbscissae` = their sorted abscissae (0 and n present);
  `npVerticesFull` = the height-0 dots at those abscissae; **`dropCollinear` collapses the interior
  height-0 dots to the endpoints** — READ `dropCollinear`'s definition before stating this lemma
  precisely (the hull agent's banked `npVertices_zeroPair`/`npVertices_zeroSingleton`/
  `hullDots_of_heights_zero` are the model proofs; the needed generalization is
  `npVertices_of_flat : (0,0) ∈ S → (n,0) ∈ S → (∀ (i,v) ∈ S, i ≤ n) → 0 < n →
   npVertices S _ = [(0, 0), (n, 0)]`).
* Then `npSides` = zip-map of `[(0,0),(n,0)]` = `[⟨0, n, 0, 0⟩] = [flatSide n]` (npSides def,
  NewtonPolygon.lean:345-347 — literal).

**γ2 (side selection).** `rootSide p N hN f = some (flatSide n)` (head of γ1's list — `rfl`-level);
`rootFace = M7.toSideFace (flatSide n) = flatFace n` (definitional).

**γ3 (residual = reduction).** With the D7-FIXED `boxCoeffData`, on `flatSide n` (`i₀ = 0`, `e = 1`
— check: `slope = 0`, `Rat.den 0 = 1` ✓; `h = 0`; `residualDeg = n/1 = n`):
`c_t = if zmodValuation (f.coeff t) = 0 then (unit residue = plain reduction) else 0 = (f.coeff t) mod p`.
So `rootResidual = residualPoly = Σ_t C(f̄.coeff t)·X^t = f̄` (`residualPoly_coeff` gives the
coefficient extraction; the mod-p reduction of the monic box polynomial is `Polynomial.map (ZMod.castHom …)`
— state the equality against that map). `natDegree = n` (leading coefficient 1 ≠ 0), so the `≤ n`
guard keeps it; `dr = n`; root tuple `(0, n, n)` ✓ = `sepShape`'s.

**γ4 (cells determined).** `M5.cells (fRootCtx …)` factorizes `Rr = f̄` via
`Classical.choice (M4.factorize_any f̄)`. `ResidualFactorization` (ResidualPolynomial.lean:239-255)
pins: factors monic + irreducible, `prod_eq : R = C(leadingCoeff)·∏ ψ^mult`, degree budget. Over the
field `ZMod p` the monic-irreducible factorization is UNIQUE, so ANY two `ResidualFactorization f̄`
have the same `factors` Finset and the same `mult` ON the factors — prove the uniqueness lemma
`ResidualFactorization.factors_eq` (from `prod_eq` + `UniqueFactorizationMonoid.normalizedFactors`
uniqueness; `mult ψ = (normalizedFactors R).count ψ` is even the stated intent of the `mult`
docstring). For SEPARABLE `f̄`: `mult ≡ 1` on factors (squarefree ⟺ all multiplicities 1 — the
in-repo M4 separability lemmas `residual_separable_iff_squarefree` + squarefree ⟹ count ≤ 1). Then
every cell is childless (`mult < 2` branch), one cell per factor, `dS = ψ.natDegree`.

**γ5 (payload equality).** `classifyAux` emits payload `M5.encodeCells (fRootCtx …)` = the
`mergeSort`-by-degree cell erasures = a list of `⟨d, 1, flatFace n, []⟩` sorted ascending by `d`.
`sepShape n λ`'s payload = `(λ.parts.sort (· ≤ ·)).map (fun d => ⟨d, 1, flatFace n, []⟩)`. Equality
reduces to: two ascending-sorted `List ℕ` with the same multiset are EQUAL
(`List.eq_of_perm_of_sorted` / `Multiset.sort` uniqueness), where the multiset of factor degrees = λ
BY DEFINITION of the pattern; then `map` of equal lists. (Entries with equal `d` are IDENTICAL
ShapeCells, so stability/tie-order is irrelevant — this is exactly why the A5 canonicalization sort
suffices for separable payloads.) ⚠ Check the tree slot too: children flatMap is empty (γ4), so
`tree = [(0, n, n)]` ✓.

**γ6 (converse / stratum characterization).** `classify p n N f = sepShape n λ` ⟹ `f` is generic-λ:
* the payload's polygon slot forces `rootFace f = flatFace n`: a non-unit `a₀` gives a first side
  with `v₀ > 0`, whose `toSideFace` has a positive ceil-height — ≠ `flatFace n` (prove
  `toSideFace_injective_enough`: distinct heights ⟹ distinct faces; or simpler, compare a single
  field). Take care with the DEGENERATE no-side case (`rootSide = none`: singleton polygon — happens
  only for `n = 0`; the capstone can carry `0 < n`).
* `Σ dS = n` over the payload forces the residual degree `n` (flat side selected, full budget);
  childlessness forces separability (a repeated factor with `μ·D < n` would emit a child; the
  full-budget `μ·D = n` self-loop case has `Σ dS = D < n` — WRONG payload); the dS-multiset = λ.
* Result: `{f : classify N f = sepShape n λ} = {f : zmodValuation (f.coeff 0) = 0 ∧ (f mod p) separable with pattern λ}`
  — a set depending ONLY on `f mod p`.

---

## §2 — (α) mod-p cylinder stability ⟹ the limit is a constant sequence

From γ6, the fiber `{f ∈ monicBox p N n : classify N f = sepShape n λ}` is the FULL preimage of the
level-1 set `Sep₁(λ) := {g ∈ monicBox p 1 n : unit a₀, separable pattern λ}` under the reduction
`monicBox p N n → monicBox p 1 n`. Then

```
stratumCount (sepShape λ) N = #Sep₁(λ) · p^{n(N−1)}          (N ≥ 1)
```

by the banked fiber-cardinality machinery (`CountingModel.boxReduce_fiber_card = p^n` per level +
`cylinder_count_stable(_LE)` — CHECK their exact statements before writing; they were built for
exactly this). Hence `stratumCount/p^{nN} = #Sep₁(λ)/p^n`, CONSTANT in `N ≥ 1`, and the `h_node0`
limit is `tendsto_const_nhds` — provided the constant equals `rootCount (sepShape λ) p`, which is §3.
(Also needed: level `N = 0` is a single point — `atTop` limits ignore finitely many terms; use
`Filter.Tendsto` congruence on `N ≥ 1` — `tendsto_atTop_of_eventually_const` or
`Filter.EventuallyEq` with `eventually_atTop`.)

⚠ SUBTLETY: γ1–γ5 prove the forward inclusion at EVERY `N ≥ 1` with the SAME level-1 data — the
reduction-read stability (unit valuations read 0 at every level; `zmodUnitResidue` commutes with the
tower on units — the banked PadicLift Layer-A lemmas). Confirm `boxReduce`'s direction (level `N+1 → N`
vs `N → 1`); if only one-digit reduction exists, iterate (an easy induction, or the `_LE` variant).

---

## §3 — (β) the level-1 count identity

`(#Sep₁(λ) : ℚ)/p^n = rootCount (sepShape λ) p = (∏_d ff(avail_d(p), k_d)/k_d!) · p^{−n}` — i.e.

```
#Sep₁(λ) = ∏_d C(#Irr_d − [d = 1], k_d) · k_d!-normalized …  (choices of k_d distinct irreducibles,
           excluding X at degree 1)
```

* **β1 (bijection).** `Sep₁(λ) ≃ Π_d (k_d-subsets of Irr_d \ {X at d = 1})`: a squarefree monic
  polynomial with unit constant term IS the product of its distinct monic irreducible factors, none
  equal to `X`; conversely any such product is squarefree monic with unit constant term and pattern
  λ. Lean: build the map by `Finset.prod`, injectivity from unique factorization
  (`UniqueFactorizationMonoid`), surjectivity from factorization existence (M4.factorize_any + γ4's
  uniqueness). Count: `Finset.card_eq_of_bijective` or an explicit `Fintype.card` computation over
  the sigma/pi structure (`Fintype.card_pi`-style over the degree-indexed factors).
* **β2 (pool sizes).** `#Irr_1 = p` (linears `X − c`); `#(Irr_1 \ {X}) = p − 1 = availPoly 1 eval p`.
  `#Irr_d = necklaceQ d p` for `d ≥ 2`: the CROSS-TIE
  `necklaceQ d (Nat.card F) = Nat.card (L3.monicIrreducibleDegree F d)` from
  `L3Gauss.gauss_necklace_count` (`d·card = Σ μ(e)·q^{d/e}` in ℚ — divide by `d`; `necklaceQ` is
  literally that sum over `d`). One lemma, `[core]`.
* **β3 (subset counts).** `#(k-subsets of an m-set) = m.choose k` (`Finset.card_powersetCard` /
  `Fintype.card_finset_len` — check the modern name) and the cast identity
  `(m.choose k : ℚ) = ff(m, k)/k!` (`Nat.cast_choose_eq_...`? mathlib has
  `Nat.choose_eq_descFactorial_div_factorial` + `Nat.cast_descFactorial` — verify names; the ff-poly
  eval ties in via `ffPoly (availPoly d) k` eval at `p` = `descFactorial`-cast, one small lemma per
  branch of `availPoly`).
* **β4 (assembly).** Multiply over `d ∈ λ.parts.toFinset`; independence across degrees (a subset
  choice per degree, disjoint pools) — `Fintype.card_pi` over the finitely many `d`. Then divide by
  `p^n` and match `rootCount`'s eval (unfold `nodeChoicePolyQ (cellsOfShapeWF (sepShape λ))` via
  `cellsOfShapeWF_sepShape`: the dS-list is `λ.parts.sort`, counts `k_d`, δ = 1 ⟹ `comp (X^1)` — a
  `simp [Polynomial.comp]`-grade normalization; `nodeVolumeExp = newtonExponent (flatFace n) + n`
  and **prove `newtonExponent (flatFace n) = 0`** — read `toSideFace`'s ceilHeights on the flat side:
  all zero — one small lemma).

β is the longest package (real combinatorics) but fully classical; every ingredient named above
exists or is a standard mathlib pattern.

---

## §4 — implementation order, owners, gates

1. **D7 numeric gate** (Python, §0) → **D7 Lean fix** in Classifier.lean + fallout
   (`boxCoeffData_endpoints_ne_zero` becomes provable — attempt it; Layer-B stability lemmas re-check).
   Rebuild chain. [me]
2. **γ1 hull lemma** (`npVertices_of_flat`) — read `dropCollinear` first; reuse the banked zero-height
   lemmas. [agent, bounded, NewtonPolygon.lean]
3. **γ3 + γ4 + γ5** (residual = reduction; factorization uniqueness; payload equality) — γ4's
   `ResidualFactorization.factors_eq` is the pivot lemma. [agent(s), bounded, after 1-2]
4. **γ6 + α** (stratum characterization + constant-sequence limit). [me + agent]
5. **β** (count identity; the L3Gauss cross-tie first — it is independent and unblocks the numeric
   shape). [agent, bounded]
6. **Assemble `h_node0_proved`** in Order0Capstone; fire `montes_order0` unconditionally; full build +
   `#print axioms` (target: `[propext, Classical.choice, Quot.sound]`); update AxChk.
7. Gates at every step: the transcription tables must keep matching (§2.7); the `cells := []`-style
   falsifiability test on every new ∀-statement; NO new axiom, NO sorry on the capstone path.

Estimated: D7+γ ≈ the bulk (hull + classifier walk); β parallel; α short once γ6 lands.

---

## §5 — ADDENDUM (2026-07-02, post γ1/γ2/γ3/β): the γ5/γ6/α detailed design

**Banked so far:** γ1 (`Order0Hull.npSides_of_flat` + flatSide corollaries), γ2+γ3
(`Order0Root.rootSide_eq_flat`, `rootResidual_eq_reduction` [residual = f̄], `rootResidual_natDegree = n`,
`fRootCtx_dr/Rr/Nr`), β (`Order0Count.card_sepStratum` + `necklaceQ_eq_card` +
`cast_choose_eq_prod_range_div` + pool lemmas), γ4 (in flight: `mem_factors_iff`,
`mult_eq_one_of_squarefree`, degree-multiset tie). D7 fix built green.

**γ5 (forward: `classify_eq_sepShape`).** For `0 < N`, `0 < n`, `hunit`, `f̄` squarefree with
`¬X ∣ f̄` and `(normalizedFactors f̄).map natDegree = lam.parts`:
`B.classify p n N f = sepShape n lam`.
* One-step unfold: `classifyAux` is `Nat.strongRecOn budget ind Tctx hT`; `Nat.strongRecOn_eq`
  (batteries, Batteries/Data/Nat/Lemmas.lean:52) + beta gives
  `classifyAux … = ⟨(T.order, clusterSize T, T.dr) :: (omStep …).flatMap …, M5.encodeCells T⟩`.
* `rootCtx = fRootCtx` (dif_pos hN); tree head = `(0, n, n)` by `fRootCtx_dr` (γ3).
* Children flatMap = `[]`: every cell of `M5.cells (fRootCtx …)` is childless — γ4's
  `mult_eq_one_of_squarefree` applied to `Rr = f̄` (γ3) kills the `2 ≤ μ` branch.
* Payload: `encodeCells (fRootCtx …)` = mergeSort-by-degree of one `⟨deg ψ, 1, flatFace n, []⟩` per
  factor (children [] as above; polygon = `fRootCtx_Nr`; δ = 1). Equality with
  `(lam.parts.sort (· ≤ ·)).map (fun d => ⟨d, 1, flatFace n, []⟩)`:
  map both through `natDegree`; LHS degree list is Pairwise-≤ (mergeSort sorted by the dS key) with
  multiset = factor-degree multiset = `(normalizedFactors f̄).map natDegree` (γ4 item 3) =
  `lam.parts`; RHS = `Multiset.sort` — two ≤-sorted ℕ-lists with equal multisets are equal
  (`List.eq_of_perm_of_sorted`, antisymmetry of ≤ on ℕ); entries are DETERMINED by their degree
  (`⟨d, 1, flatFace n, []⟩`), so the ShapeCell lists are the images of equal ℕ-lists — equal.
  (Lemma shape: `payload = degreeList.map mk` on both sides + `degreeList_LHS = degreeList_RHS`.)

**γ6 (converse: fiber characterization).** `B.classify p n N f = sepShape n lam` (with `0 < n`,
`0 < N`) ⟹ `hunit ∧ Squarefree f̄ ∧ ¬X ∣ f̄ ∧ (normalizedFactors f̄).map natDegree = lam.parts`.
Extraction chain from the shape equality (payload is NONEMPTY since `lam.parts ≠ 0` for `n > 0`):
1. `rootSide ≠ none` (else `Rr = 0` ⟹ `cells = []` ⟹ payload `[]` — contradiction). Let `S` be
   the selected side.
2. Payload cells all have `polygon = flatFace n` ⟹ `toSideFace S = flatFace n` ⟹ `S = flatSide n`:
   `toSideFace` height arithmetic — read `M7.toSideFace` (CellPartition.lean:60) FIRST; the needed
   injectivity is only on the reachable sides: width `= n` forces `j₀ − i₀ = n` with `j₀ ≤ n`
   (support bound) ⟹ `i₀ = 0, j₀ = n`; `ceilHeights 0 = v₀ = 0`; the hull's right endpoint at the
   monic dot forces `v₁ = 0` (or: heights ≡ 0 + width-(n−1) height forces `v₀/n ≤ 0`). ⚠ If
   `ceilHeights` excludes the right endpoint, derive `v₁ = 0` from `S ∈ npSides` (sides end at hull
   vertices; the last vertex is `(n, 0)` — the monic dot is on the hull) — state whichever is
   cleanest after reading the defs; this is the fiddliest sub-lemma.
3. `i₀ = 0` + the side's left endpoint is a SUPPORT dot with valuation `v₀ = 0` ⟹
   `zmodValuation (f.coeff 0) = 0` = `hunit`. (If `a₀ = 0` in the box, `0 ∉ support` and no side can
   start at abscissa 0 — the same step.)
4. With `hunit`, γ3 applies: `Rr = f̄`, `dr = n`. Payload dS-sum: `Σ_c dS = Σ lam.parts = n`
   (partition) and LHS `= Σ_{distinct ψ} deg ψ ≤ Σ_ψ mult·deg = natDegree f̄ = n` with equality iff
   all `mult = 1` ⟹ `Squarefree f̄` (squarefree ⟺ all normalized-factor multiplicities 1 —
   γ4/L3Squarefree API). Childlessness is then automatic; `¬X ∣ f̄` from `hunit`
   (unit constant coefficient ⟹ `f̄(0) ≠ 0`); the dS-multiset equality gives the pattern.
   ⚠ ALTERNATIVE if step 2's face-injectivity turns ugly: replace the payload-polygon discrimination
   by a TREE-slot discrimination — the tree head is `(0, n, dr(f))` and `dr(f) = n` forces
   `residualDeg S = natDegree(residualPoly) ≤ residualDeg S = length/e ≤ n` with equality forcing
   `e = 1 ∧ length = n` ⟹ `i₀ = 0, j₀ = n` — then only `v₀ = 0` needs the face/hull argument
   (slope integrality: `e = 1` + heights: hull left endpoint at abscissa 0 is `(0, v(a₀))`; the
   NON-flat candidate `v₀ > 0` has `dr` after the ≤-n guard... note the slope-(-1) side (0,n)–(n,0)
   HAS `e = 1, residualDeg = n` — it is discriminated ONLY by the payload polygon or by `v₀` read
   through the face. So step 2/face-reading cannot be entirely avoided; budget for it.)

**α (the count).** Set `Sep₁(lam) ⊆ monicBox p 1 n` := the γ6 predicate on the reduction. Then for
`N ≥ 1`: `{f ∈ box_N : classify N f = sepShape lam} = (reduce₁)⁻¹(Sep₁ lam)` where
`reduce₁ : box_N → box_1` is the coefficientwise `ZMod.castHom` reduction — because BOTH γ5's
hypotheses and γ6's conclusions are conditions on `f mod p` (unit-ness of `a₀` at level N ⟺ the
mod-p reduction is nonzero — `zmodValuation = 0 ↔ castHom x ≠ 0`, an Order0Root-adjacent lemma).
Fiber count: `#(reduce₁)⁻¹(g) = p^{n(N−1)}` for every `g` (coefficientwise; reuse/iterate the banked
`CountingModel.boxReduce_fiber_card = p^n` or the SchwartzZippel `castHom_fiber_card`; alternatively
a direct product count over `n` free coefficients of `ZMod(p^N) → ZMod p` fibers `= p^{N−1}` each).
Hence `stratumCount (sepShape lam) N = #Sep₁(lam) · p^{n(N−1)}` and
`stratumCount / p^{nN} = #Sep₁(lam)/p^n` for all `N ≥ 1` — `Tendsto` by
`tendsto_const_nhds` + `Filter.EventuallyEq` on `N ≥ 1` (`Filter.eventually_atTop`).

**Assembly (the last step).** `#Sep₁(lam) = card_sepStratum` (β; F = ZMod p — check the two stratum
presentations match: β's `sepStratum` uses `¬X ∣ f ∧ Monic ∧ natDegree = n ∧ Squarefree ∧ pattern`;
γ6's predicate is on box₁ elements — a `monicBox p 1 n` subtype vs β's set-in-`F[X]`; ONE bridge
lemma). Then
`#Sep₁/p^n = (∏_d choose(avail_d, k_d))/p^n = rootCount (sepShape lam) p`
via `cast_choose_eq_prod_range_div` + `necklaceQ_eq_card` + eval-pushing on
`nodeChoicePolyQ (cellsOfShapeWF_sepShape …)` (`Polynomial.eval_prod`, `eval_comp`, `eval_mul`,
`nodeDelta = 1` ⟹ `comp (X^1)` trivial; `nodeVolumeExp = newtonExponent (flatFace n) + n` with
**`newtonExponent (flatFace n) = 0`** — one small lemma reading `toSideFace`'s ceilHeights on the
flat side). Then `h_node0` is proved; `montes_order0` fires unconditionally on Lean core.
