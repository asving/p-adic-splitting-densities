# MINIMAL_PADIC_AXIOMS — frozen spec for de-axiomatizing `clusterVolume_rational`

**Date:** 2026-06-18. **Role:** the synthesized, frozen minimal standard-fact p-adic-integration
axiom interface that turns `Interface.clusterVolume_rational` from an *asserted axiom* into a
*derived theorem*. This is the lead-architect + faithfulness-referee synthesis of three independent
designs (`design_design_igusa_cell.md`, `design_design_mathlib_maximal.md`,
`design_design_primitive_facts.md`), each cross-checked against the actual mathlib v4.31.0 source and
against the project's honesty rules.

**Scope.** Only the *rationality* half (per-shape `clusterVolume` is a uniform rational function of
`q`, hence per-type `density` is). The functional-equation / palindromy half stays the
`tame_functionalEquation` axiom + L7 transfer, untouched (palindromy is easy once uniformity holds).

**Bottom line we deliver.** After implementing this spec:

> `clusterVolume_rational` is a **THEOREM**, not an axiom. `density`-uniformity (`L6M4.density_rational`)
> and the Goal's rationality half then follow as before. `goal_theorem`'s `#print axioms` footprint
> becomes
> `[propext, Classical.choice, Quot.sound, AX_cellRecursion, AX_columnMeasure,
>   AX_GMN_residual, AX_GMN_polygon, AX_GMN_descend, tame_functionalEquation]`
> — i.e. the conclusion-shaped axiom `clusterVolume_rational` is **gone**, replaced by three GMN
> structural axioms + two standard cited p-adic-integration axioms (Igusa/Denef), with the rationality
> now flowing through the proved blocks (`OMInduction.clusterVol_isRational`, `T_BB1`, `T_BB3`,
> `L5fix.selfLoop_geometric`, `RatFn`, `L6M4`). The p-adic Haar measure is **not constructed**; the two
> analytic facts are clearly-labeled cited interface axioms, exactly as `L4.cellVolume_eq`'s `hfactor`
> already is. The remaining boundary is honestly **{two Igusa/Denef volume-evaluation facts + GMN
> structure + Lean core}**.

---

## 0. Mathlib reality-check (load-bearing claims, grepped against `.lake/packages/mathlib`)

PRESENT and USED directly (so **NOT** axiomatized):

- `MeasureTheory.measure_biUnion_finset` — `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:185`
  (and `measure_biUnion_finset₀` :179). Finite additivity over a finite disjoint measurable
  partition. **DERIVES** the cell-sum step (ii) and the density decomposition mechanism.
- `MeasureTheory.Measure.pi_pi` — `Mathlib/MeasureTheory/Constructions/Pi.lean:292`. Finite product
  measure / Fubini (the box factorization).
- `Subgroup.index_mul_measure` / `AddSubgroup.index_mul_measure` —
  `Mathlib/MeasureTheory/Group/Measure.lean:279-280`. `index H * μ H = μ univ` for a measurable
  finite-index subgroup under a left-invariant measure (the lower primitive behind the box law).
- `Module.card_eq_pow_finrank` / `Module.natCard_eq_pow_finrank` — used at
  `Mathlib/FieldTheory/Finite/GaloisField.lean:94-95,292-300`. `Nat.card F = base ^ finrank`. **This
  is the linchpin that makes the A0 finrank tie a PROVED lemma, not an axiom.**
- `MeasureTheory.Measure.haarMeasure` and abstract Haar existence/uniqueness — `Mathlib/.../Haar/Basic.lean`.
- `PadicInt.instCompactSpace` etc. — `Mathlib/NumberTheory/Padics/ProperSpace.lean:55` (ℤ_[p] compact;
  ℚ_[p] proper). Topology exists; measure does not.
- Finite-field perfectness / `Separable ↔ Squarefree` (`PerfectField.*`), polynomial counting
  (`L3`, `L3Squarefree` PROVED in-project), `RatFn` closure (PROVED), `OMInduction` (PROVED).

ABSENT (genuine gaps → must be axiomatized as cited interface facts):

- **No `Padic`/`PadicInt` anywhere under `Mathlib/MeasureTheory/`** (grep empty). No
  `MeasureSpace`/`BorelSpace`/`haarMeasure` instance on `PadicInt`, on any DVR, or on any valuation
  ring (grep over `RingTheory/Valuation`, `RingTheory/DiscreteValuationRing` empty). The abstract Haar
  machinery exists but **has never been instantiated on a p-adic ring** — that instantiation is the gap.
- **No Igusa local-zeta integral, no Denef cell decomposition** (grep `Igusa`/`Denef` empty). The
  p-adic change-of-variables/Jacobian exists only for finite-dim REAL vector spaces, not for O_K.

So the two analytic axioms below are stated as **interface facts** (named axioms with literature
citations), in the established "recorded-via-hypothesis" style of `L4.cellVolume_eq`'s `hfactor`.

---

## 1. The final axiom interface (frozen)

Five axioms total: **three GMN structural** (replacing/upgrading the current `descend`/`descend_size_lt`
stubs, with the A0 anti-caricature constraints enforced) and **two standard p-adic-integration**
(Igusa/Denef). Each is structural; **none is a rationality/uniformity/volume conclusion**. The cell
volume `(1-Q⁻¹)^V Q^{-A}` (T_BB1), the residual count `Q_r^{d_r-1}` (T_BB3), the finrank↔card tie, the
self-loop pivot, the OM recursion's rationality, and `clusterVolume_rational` itself are all DERIVED or
PROVED, never axiomatized.

### A0-FIX (prerequisite, NOT an axiom — a PROVED structural constraint on `OMShape`)

Before any axiom is faithful, `OMShape` (`BB3inf.lean:57`) must tie its degree fields to their real
meaning (independent verification D2). Add invariants:

```lean
structure OMShape where
  size order : ℕ
  Fr : Type
  [instField : Field Fr] [instFinite : Finite Fr]
  baseField : Type
  [instBaseField : Field baseField] [instBaseFinite : Finite baseField]
  [instAlg : Algebra baseField Fr]
  residual : Polynomial Fr
  polygon : L4.LatticePolygon
  -- A0 ties (invariants, NOT free fields):
  residueDeg : ℕ
  hResidueDeg : residueDeg = Module.finrank baseField Fr     -- a REAL extension degree
  residualDeg : ℕ
  hResidualDeg : residualDeg = residual.natDegree            -- the ACTUAL residual degree
```

Then `Nat.card Fr = q^residueDeg` (when `Nat.card baseField = q`) is a **PROVED lemma**
(`Module.natCard_eq_pow_finrank`), so `bb3CellCount T q = (q^residueDeg)^(residualDeg-1)` is genuinely
`T_BB3`'s count over the shape's OWN residual, not a monomial in free integers. `bb3CellCount_eq_count`
is re-proved against `T.Fr` (not an external arbitrary `F`). This kills the D2 caricature.

> NOTE on `DecidableEq`/Type-valued `Fr`: `OMShape` need not derive `DecidableEq` (the OM induction
> uses `Nat.strong_induction_on` on `size`, not decidable equality of shapes). The Type-valued `Fr`
> lives only on `OMShape`; the Goal's `ClusterShape` (which IS `DecidableEq`) is bridged to `OMShape`
> by a `decode : ClusterShape → OMShape` (implementation step 6), not identified with it.

---

### AX_GMN_residual  (GMN fact I — finite-field residual at every order)

- **Informal.** For an `OMShape` of order `r`, the order-`r` residual polynomial `R` lives in `F_r[y]`
  with `F_r` a **finite** field and `[F_r : 𝔽] = f₀…f_{r-1}` a genuine residue-field extension degree
  (a divisor of `n`), of degree exactly `d = ℓ(S)/e_r` (polygon-side length over the slope
  denominator), leading coefficient a unit, `y ∤ R`. (Monic only after normalization; GMN works up to
  `∼`.) The A0 ties (`residualDeg = residual.natDegree`, `residueDeg = finrank`) carry this; the axiom
  asserts the GMN existence/shape of the tower and side-length relation `residualDeg = ℓ(S)/e_r`.
- **Lean type sketch.**
  ```lean
  -- Realized by the OMShape structure fields + invariants above, plus the GMN side-length axiom:
  axiom AX_GMN_residual_sideLength (T : OMShape) :
    T.residualDeg = T.polygon /-side-length-/ /- ℓ(S) -/ / T.slopeDenominator
  -- (the finite-field-tower content is carried by [Finite Fr] + hResidueDeg, both PROVED-tieable)
  ```
- **Citation.** GMN (Guàrdia–Montes–Nart, Trans. AMS 364 (2012) 361–416, arXiv:0807.2620) §2.1 finite-
  field tower `F=F₀⊆…⊆F_r`, `[F_r:F]=f₀…f_{r-1}`; **Def 2.21** residual polynomial (degree exactly `d`,
  leading coeff a unit, `y ∤ R`). AXIOM_FAITHFULNESS.md AX-GMN-I (drop unqualified "monic").
- **mathlib-status.** GENUINE-GAP (structural). The finite-field perfectness machinery `T_BB3` consumes
  is in mathlib (PROVED via `L3Squarefree`); the GMN tower existence is the cited external fact. The A0
  tie is PROVED via `Module.natCard_eq_pow_finrank` / `Polynomial.natDegree` (NOT axiomatized).

### AX_GMN_polygon  (GMN fact II — lattice Newton polygon at every order)

- **Informal.** The order-`r` Newton polygon `N_r` is a principal (integer-lattice) polygon for the
  order-`r` valuation `v_r`; its faces/lengths/heights are lattice data; the index of `v_r` over `v` is
  `e₁…e_{r-1} = D_r`, dividing `e₁…e_r = e(L/K) ∣ e`. (No "p-independent" adjective in the STATEMENT;
  that is derived T_BB1.)
- **Lean type sketch.** Reuse `L4.LatticePolygon` as `OMShape.polygon`; the axiom is the existence of
  this lattice polygon object with side data feeding `residualDeg` via `AX_GMN_residual_sideLength`.
  ```lean
  -- OMShape.polygon : L4.LatticePolygon  (the lattice object; T_BB1 consumes it, PROVED)
  ```
- **Citation.** GMN **Def 1.1** (principal polygon, semigroup `PP`), **§2.5** (definition of `N_r`,
  line 2174), **Def 2.5 / Prop 2.6** (`v_r` integer-valued, index `e₁…e_{r-1}`). AXIOM_FAITHFULNESS.md
  AX-GMN-II (corrected citation; the `1/D_r` lattice is the project's `v(p)=1` renormalization, NOT part
  of the axiom; remove Def 2.3 / Lemma 2.4).
- **mathlib-status.** GENUINE-GAP (structural). `L4.LatticePolygon` and `T_BB1`'s rational-function
  shape are PROVED in-project; the "polygon is lattice" fact is the cited external input.

### AX_GMN_descend  (GMN fact III — leaf/descend dichotomy + strict size drop)

- **Informal.** A multiplicity-1 order-`r` residual factor is an irreducible p-adic **leaf** with
  `(e*,f*) = (e₁…e_r, f₀…f_r)`; a multiplicity-`≥2` factor **descends** to order `r+1`, recursing into a
  child cluster of **strictly smaller** cluster size (off the self-loop); descent past order `r` is
  triggered exactly when some order-`r` residual is non-separable (equivalently, finite-field
  perfectness, non-squarefree). Termination: for separable input the descent stops at finite order
  (well-founded on cluster size).
- **Lean type sketch.** (Strengthen the existing `descend`/`descend_size_lt`; the children must be tied
  to the mult-≥2 repeated factors of `T.residual` — the A0/D2 fix at the descent level.)
  ```lean
  axiom descend : OMShape → List OMShape
  axiom descend_size_lt : ∀ (T : OMShape), ∀ c ∈ descend T, c.size < T.size
  -- STRENGTHENED: descend fires only at mult≥2 factors of T.residual; records peeled residue degree f.
  axiom descend_children_of_factors :
    ∀ (T : OMShape), ∀ c ∈ descend T, ∃ (P : Polynomial T.Fr) (μ : ℕ),
      2 ≤ μ ∧ (P^μ ∣ T.residual) ∧ c.size = μ /- and c.residueDeg = T.residueDeg * P.natDegree -/
  ```
- **Citation.** GMN **Cor 1.20 / Cor 3.8** (mult-1 ⇒ irreducible leaf with the stated `(e*,f*)`),
  **Lemma 3.11(3)** (non-separable residual = descent trigger), **Thm 4.18 / Cor 4.19** (finite
  termination). AXIOM_FAITHFULNESS.md AX-GMN-III (FAITHFUL) + AX-GMN-IV (trim to existence statement).
- **mathlib-status.** GENUINE-GAP. `descend`/`descend_size_lt` already declared (`BB3inf.lean:90,95`);
  the current versions are weaker stubs. `descend_children_of_factors` is the D2-at-descent faithful
  strengthening. **DROP `AX_GMN_IV_terminates`** (`BB3inf.lean:101`): it is dead weight — independently
  provable from `InvImage.wf` and not in any footprint (independent verification §2).

### AX_columnMeasure  (Igusa box/shell — single-coordinate Haar value)

- **Informal.** Over the unramified `O_δ` with residue size `Q = q^δ`, the normalized Haar measure of a
  single-coordinate valuation condition is `μ{v(c) ≥ h} = Q^{-h}` (ball/box) and
  `μ{v(c) = h} = (1-Q⁻¹)Q^{-h}` (shell), and the columns of an OM cell are mutually independent so the
  cell measure is the **finite product** of the per-column measures. A finite list of rational scalars;
  **not** the construction of the measure. Uses only `[O_δ : p^m O_δ] = Q^m` (`v(p)=1`, unramified) +
  product Haar.
- **Lean type sketch.** This is exactly `L4.columnMeasure` + the product-structure `hfactor` already in
  `L4.cellVolume_eq`. State it as the `hfactor` law:
  ```lean
  axiom AX_columnMeasure (cellVol : L4.LatticePolygon → ℕ → ℚ) (pg : L4.LatticePolygon) (Q : ℕ) :
    cellVol pg Q = ∏ i : Fin pg.width, L4.columnMeasure pg Q i
  -- columnMeasure i = if isVertex i then (1-Q⁻¹)·(Q^{h i})⁻¹ else (Q^{h i})⁻¹  (already in L4)
  ```
- **Citation.** Igusa, *Local Zeta Functions* §7.4 (box/shell normalization
  `μ{v(c)≥h}=Q^{-h}`, `μ{v(c)=h}=(1-Q⁻¹)Q^{-h}`); standard local-field Haar `[O_δ:p^mO_δ]=Q^m`.
  Derivable from `AddSubgroup.index_mul_measure` + index `q^k` *once O_K has a measure*; absent that, an
  interface field. AXIOM_FAITHFULNESS.md AX-MEASURE(a),(b) (graded FAITHFUL, minimal).
- **mathlib-status.** GENUINE-GAP (the scalar value; no p-adic measure instance), but the CONSEQUENCE —
  cell volume `(1-Q⁻¹)^V Q^{-A} = bb1Value` — is **NOT axiomatized**: it is PROVED in
  `L4.cellVolume_eq`. So this axiom asserts strictly LESS than the cell volume.

### AX_cellRecursion  (Igusa/Denef per-cell decomposition) — **THE load-bearing axiom**

- **Informal.** On a single OM cell `c` of shape `T` (one residual-shape stratum on one Newton-polygon
  face), the conditional p-adic Haar cluster measure factors as
  `cellMeasure(c,q) = (residual point-count of c over T's residue field) × (box/shell Haar volume of c)
  × (∏ over c's descent children of clusterMeasure(child,q))`, and the whole cluster measure is the
  finite sum over OM cells of these, with the unique non-progressing self-loop cell contributing a
  geometric series (resummed by `1 - q^{-w}`). This is the Igusa stationary-phase / Denef cell-
  decomposition identity read on one cell: the residual-coefficient map is a Haar submersion onto
  `𝔸^{d_r}(F_r)`, so integrating the cell condition factors a finite-field point-count × the lattice
  box volume × the child sub-integrals. **A STRUCTURAL measure-factorization identity, NOT a
  rationality claim:** the three factors are honest cardinal/measure quantities.
- **Lean type sketch** (faithful eq-(4.2) form — multi-child product, residual count from the ACTUAL
  residual; this is the D3 fix):
  ```lean
  axiom AX_cellRecursion (clusterMeasure : OMShape → ℕ → ℚ) (T : OMShape) (q : ℕ) (hq : 1 < q) :
    clusterMeasure T q =
      ( ( (omCells T).map (fun c =>
            (Nat.card {R : Polynomial T.Fr //                       -- residual point-count (→ T_BB3)
                R.Monic ∧ R.natDegree = c.residualDeg ∧ ¬ Squarefree R} : ℚ)
            * L4.bb1Value c.polygon q                               -- box volume (→ AX_columnMeasure→T_BB1)
            * (c.children.map (fun ch => clusterMeasure ch q)).prod) -- multi-child ∏ (recursive)
        ).sum )
      / omPivot T q                                                  -- self-loop pivot (→ L5fix), 1 if no loop
  ```
  where `omCells T : List Cell` is the GMN finite cell partition (one per face × residual stratum) and
  `omPivot` is `L5fix`'s pole-free self-loop factor. Each of the three factors is **supplied** by a
  proved block (count by `T_BB3`/`bb3CellCount_eq_count`, box by `T_BB1`/`cellVolume_eq`, children by
  the IH); rationality is **never** asserted in this axiom.
- **Citation.** Igusa, *Local Zeta Functions* §7.4 / Prop 7.4.1 (p-adic change of variables `|Jac|_p`;
  unit-Jacobian ⇒ measure-preserving; cell decomposition of a local zeta integral); **Denef**, *The
  rationality of the Poincaré series associated to the p-adic points on a variety*, Invent. Math. **77**
  (1984) 1–23 (cell decomposition of p-adic integrals over definable cells). `BB3_infinity.md` eq
  (4.1)/(4.2) §4.2. Self-loop geometric closure: `L5fix.selfLoop_geometric` (PROVED).
- **mathlib-status.** GENUINE-GAP. mathlib has `Measure.prod`/`pi_pi` (Fubini) and `lintegral_map`
  (CoV) abstractly, but NO Igusa local zeta, NO Denef cell decomposition, and no p-adic measure to state
  them over. The count factor is PROVED (`T_BB3`), the box factor is PROVED (`T_BB1`); only the measure-
  factorization IDENTITY is the gap. This is the honest analytic boundary, parallel to
  `L4.cellVolume_eq`'s `hfactor`.

---

## 2. Derivation plan — recursion, decomposition, uniformity

### (a) The recursion `hrec` is DERIVED (not asserted)

Let `clusterMeasure : OMShape → ℕ → ℚ` be the abstract conditional per-shape Haar volume (a plain
function; NO measure is constructed).

1. **Additivity (step ii, pure mathlib).** The shape-`T` cluster locus is the finite disjoint
   measurable union over the GMN order-`r` OM cells (`omCells T`); by
   `MeasureTheory.measure_biUnion_finset`, the cluster measure is the finite sum of cell measures. The
   *partition existence* (finite, disjoint, measurable, one self-loop cell) is GMN-structural
   (`AX_GMN_polygon` faces × `AX_GMN_residual` strata, finite by `AX_GMN_descend` termination); the
   *additivity itself is mathlib*.
2. **Per-cell factorization (step iii, `AX_cellRecursion`).** Each `cellMeasure(c) =
   residualCount(c) × boxVolume(c) × ∏_{children} clusterMeasure(child)`. THE one substantive p-adic
   axiom.
3. **Evaluate the three factors (all PROVED).**
   - `residualCount(c)` = `T_BB3` over `c`'s own residue field `T.Fr` of size `q^residueDeg`: the count
     of non-squarefree monic degree-`residualDeg` residuals is `q^{residueDeg·(residualDeg−1)} =
     bb3CellCount`, **via the A0-tied `bb3CellCount_eq_count`** (now over `T.Fr`, not an external field).
   - `boxVolume(c)` = `L4.cellVolume_eq` from `AX_columnMeasure`: `(1-q⁻¹)^V q^{-A} = bb1Value c.polygon q`.
   - `clusterMeasure(child)` = recursive, with children strictly smaller by `AX_GMN_descend`
     (`descend_size_lt`).
4. **Self-loop (step iv, PROVED).** The unique non-progressing cell sums a geometric series with pivot
   `1 − q^{−(e(e+1)/2−1)}`, positive on `q>1` by `L5fix.selfLoop_geometric`; packaged by `omPivot`.

Combining 1–4 yields exactly the `hrec` hypothesis of `OMInduction.clusterVol_isRational` in the
**faithful eq-(4.2) form** (multi-child `∏children`, per-cell count product — the D3 fix to
`omContribs`). Because `AX_cellRecursion` asserts only the measure FACTORIZATION and the rationality of
each factor is supplied independently by proved blocks, rationality is **never** assumed.

### (b) Uniformity (`clusterVolume_rational` as a THEOREM)

Feed the derived `hrec` into the **already-proved** `OMInduction.clusterVol_isRational` with:
`hdescend` from `descend_size_lt`; `hcoeff` from `RatFn.isRationalFn_mul (T_BB1 c.polygon)
(bb3CellCount_isRational c)`; `hpivot_rat` from `omPivot_isRational`; `hpivot_ne` from `omPivot_ne` (←
`selfLoop_geometric`). Output: `∀ T : OMShape, IsRationalFn (clusterMeasure T)`. Composed with the
`decode : ClusterShape → OMShape` bridge (step 6), this discharges `Interface.clusterVolume_rational`'s
exact existential — turning it into a **theorem**.

### (c) Decomposition (one level up — DERIVED, already wired)

The density decomposition `ρ(n,σ;q) = ∑_{T∈shapes} multiplicity(T)(q)·clusterVolume(T)(q)` is the SAME
`measure_biUnion_finset` additivity applied at the type level (L1 Hensel-splitting + cluster-tree
stratification of `P^n(O_K)/M_n` into shape loci, each with `m_T(q)` residue-config representatives, a
polynomial in `q` by L3). It is **already** the `DensityFoundation.decomposition` field consumed
sorry-free by `L6M4.density_rational`; it is STRUCTURAL (multiplicities/volumes arbitrary), not a
rationality claim. With the now-derived `clusterVolume_rational`, `L6M4.sum_clusterVol_rational`
(PROVED, common-denominator induction over the `Finset` of shapes) yields `density_rational`, which
`goal_theorem` consumes. **No change to L6M4's statement; only L6M4.lean:52 re-points from the raw axiom
to the new theorem.**

---

## 3. Ordered implementation steps (Lean, v4.31.0, no measure construction)

1. **Measure-interface file** `LeanUrat/PadicMeasure.lean` (new): declare `AX_columnMeasure` (= the
   `hfactor` law, reusing `L4.columnMeasure`) and `AX_cellRecursion` (the Igusa/Denef factorization, in
   the faithful eq-(4.2) form over an abstract `clusterMeasure`/`cellMeasure : OMShape → ℕ → ℚ`). Both
   named axioms with the §1 docstrings + citations. NO measure instance.
2. **A0 fix on `OMShape`** (`BB3inf.lean`): add `baseField` + `Algebra baseField Fr`, and the invariant
   fields `hResidueDeg : residueDeg = Module.finrank baseField Fr`, `hResidualDeg : residualDeg =
   residual.natDegree`. Prove the helper `Nat.card Fr = q^residueDeg` from
   `Module.natCard_eq_pow_finrank`. Re-prove `bb3CellCount_eq_count` against `T.Fr`/`T.residual` (drop
   the external `F`/`hF`). (Kills D2.)
3. **A0 fix on descent**: strengthen `descend` with `descend_children_of_factors` (children tied to
   mult-≥2 factors of `T.residual`, peeled residue degree recorded). **Delete `AX_GMN_IV_terminates`**
   (dead weight).
4. **Rewrite `omContribs` / introduce `omCells`** (D3 fix): carry the multi-child product
   `∏children` and the per-cell residual-count product, matching eq (4.2). `OMInduction.clusterVol_
   isRational` already takes `List Shape` per contribution, so this is a contribs rewrite, NOT an engine
   change.
5. **Derive `hrec`** as a theorem `clusterMeasure_rec` from `AX_cellRecursion` + `measure_biUnion_finset`
   (additivity) + `T_BB1`/`cellVolume_eq` (box) + `T_BB3`/`bb3CellCount_eq_count` (count) +
   `L5fix.selfLoop_geometric` (self-loop) + an `ENNReal→ℚ` bookkeeping bridge if `clusterMeasure` is
   stated in `ENNReal` (finiteness: total mass ≤ 1; or state `clusterMeasure` directly in `ℚ` to avoid
   the coercion). Feed it into `clusterVol_isRational` → `∀ T, IsRationalFn (clusterMeasure T)`.
6. **`OMShape ↔ ClusterShape` bridge** (D1, the hardest step): define `decode : ClusterShape → OMShape`
   (or re-type `DensityFoundation.clusterVolume` over `OMShape`) so that
   `IsRationalFn (clusterMeasure (decode T))` yields exactly `Interface.clusterVolume_rational`'s
   existential. Keep `ClusterShape`'s `DecidableEq`; do NOT push `Fr`'s Type-valued field onto it.
7. **Convert `clusterVolume_rational` from `axiom` to `theorem`** (`Interface.lean:228`): state the same
   signature; prove it via step 6 + step 5. (Or: leave the axiom name as a `theorem` alias so L6M4/Goal
   need no edit beyond the import.)
8. **Re-point `L6M4.lean:52`** from the raw axiom to the new theorem (one `import` + same call). Re-build
   `Goal`; confirm `#print axioms goal_theorem` drops `clusterVolume_rational` and lists the five new
   structural/analytic axioms + `tame_functionalEquation` + Lean core.
9. **Axiom audit**: write a uniquely-named temp `LeanUrat/AxChk_minpadic.lean` with `#print axioms
   goal_theorem` + `#print axioms clusterVolume_rational`, build with `lake env lean` (single-file), read,
   then DELETE. Confirm no `sorryAx`, no `clusterVolume_rational` as an axiom.

Steps 2,3,4,5 are mechanical given the proved blocks. **Step 6 (bridge) is the genuine new work** and is
the current D1 disconnection. Step 5's `ENNReal→ℚ` is avoidable by keeping `clusterMeasure : OMShape →
ℕ → ℚ` (the project's convention) and stating `AX_cellRecursion` directly in `ℚ`.

---

## 4. Faithfulness section — per-axiom grade + single biggest risk

Grading rubric (AXIOM_FAITHFULNESS.md): an axiom FAILS if it (a) claims more than the cited theorem;
(b) is the conclusion in disguise; (c) mis-states the math; (d) is a caricature; (e) cites the wrong
theorem.

| Axiom | Standard cited fact? | Conclusion in disguise? | Grade | Notes |
|---|---|---|---|---|
| `AX_GMN_residual` | YES — GMN §2.1 + Def 2.21 | NO (finite-field shape only) | **SAFE, fix-applied** | drop "monic"; A0 ties (`residualDeg=natDegree`, `residueDeg=finrank`) PROVED, not free. |
| `AX_GMN_polygon` | YES — GMN Def 1.1 + §2.5 + Def 2.5/Prop 2.6 | NO (lattice object only) | **SAFE, fix-applied** | corrected citation; strip "p-independent" from statement. |
| `AX_GMN_descend` | YES — GMN Cor 1.20/3.8 + Lemma 3.11(3) + Thm 4.18/Cor 4.19 | NO (descent structure only) | **SAFE, strengthened** | children tied to mult-≥2 factors of `T.residual`; `AX_GMN_IV_terminates` dropped. |
| `AX_columnMeasure` | YES — Igusa §7.4 / standard local-field Haar | NO (a specific scalar value `Q^{-h}`) | **SAFE** | the assembled cell volume is PROVED (`cellVolume_eq`), not this axiom. |
| `AX_cellRecursion` | YES — Igusa §7.4 / Denef 1984 | **NO — iff stated as factorization** | **LOAD-BEARING; SAFE iff §1 form** | see below. |

**`AX_cellRecursion` is the single load-bearing axiom and the one to watch.** It is a genuine standard
fact (cell decomposition of a p-adic integral). Two failure modes, both blocked by the §1 form:
- (i) **It must NOT assert "cellMeasure/clusterMeasure is rational"** — that is the conclusion in
  disguise (the OLD `clusterVolume_rational` did exactly this). As designed it asserts only the measure
  FACTORIZATION `count × box × ∏children`, summed over cells, self-loop resummed; the three factors are
  honest `Nat.card`/Haar quantities, and rationality emerges ONLY downstream from
  `clusterVol_isRational` applied to the closure lemmas.
- (ii) **The A0/D2 caricature** — if the "count" were `bb3CellCount` as a monomial in FREE integers
  (untied to the actual `residual : Polynomial T.Fr`), the finite-field content would be vacuous. The
  §1 form references `Nat.card {R : Polynomial T.Fr // … ¬ Squarefree R}` with `residualDeg =
  residual.natDegree` and `residueDeg = finrank` — the A0 ties, PROVED via mathlib. This must be
  enforced or `AX_cellRecursion + T_BB3` is decorative.
- Non-vacuity confirmation (independent verification D4): instantiating the OM induction on a
  non-rational `q↦q!` leaves an unsolvable obligation, so `hrec`/`AX_cellRecursion` genuinely PINS the
  function — the axiom cannot prove an arbitrary function rational.

**Single biggest faithfulness risk:** `AX_cellRecursion` being mis-stated so that it (a) re-asserts
rationality (making it the conclusion in disguise, re-introducing the historical vacuity bug) or (b)
uses A0-untied free-integer counts (making the finite-field/Frobenius content vacuous). Both are avoided
by stating it strictly as the structural factorization with `count` = `Nat.card` of the ACTUAL residual's
non-squarefree locus over `T.Fr`, `box` = `AX_columnMeasure`-supplied, `children` = recursive measures.
Secondary risk: the pervasive base-field SCOPE over-claim ("GMN over an arbitrary complete DVF") — strip
it from all axiom STATEMENTS (each axiom is per-`p`, `K/Q_p` finite unramified, GMN's true scope);
substantively harmless but must not appear as an imported justification for p-independence.

---

## 5. Honest feasibility ledger

- **Achievable this run (a THEOREM):** `clusterVolume_rational` derived from
  `{AX_cellRecursion, AX_columnMeasure, AX_GMN_residual, AX_GMN_polygon, AX_GMN_descend}` + the proved
  blocks (`OMInduction`, `T_BB1`, `T_BB3`, `L5fix`, `RatFn`, `L6M4`), with the A0 ties PROVED and the
  recursion DERIVED — WITHOUT constructing the p-adic Haar measure. This is a strictly stronger and more
  faithful statement than the current asserted axiom.
- **Stays a labeled cited axiom (the honest boundary):** `AX_cellRecursion` (Denef/Igusa cell
  decomposition) and `AX_columnMeasure` (Igusa box/shell). PROVING these needs `MeasurableSpace` +
  `BorelSpace` + local-compactness on O_K and the Denef machinery — none in mathlib v4.31.0. The GMN
  structural axioms stay cited external facts (re-deriving MacLane–Okutsu–Montes valuations is a separate
  large project).
- **Hardest sub-steps:** (1) the `ClusterShape ↔ OMShape` bridge (D1) — real plumbing, currently
  missing; (2) enforcing the A0 finrank tie without making `OMShape` unwieldy (Type-valued `Fr` vs
  `ClusterShape`'s `DecidableEq` — solved by NOT identifying them, bridging via `decode`); (3) the
  faithful eq-(4.2) `omContribs` rewrite (D3).
- **Out of reach (honest):** PROVING the two analytic axioms; "rationality at all primes proved
  unconditionally." The deliverable is *"`clusterVolume_rational` is a THEOREM modulo the standard
  p-adic-integration interface (Igusa/Denef) + GMN structural axioms"* — the conclusion-shaped axiom is
  removed, the one substantive analytic axiom (`AX_cellRecursion`) is isolated and labeled as the
  boundary.

---

## 6. What was rejected (non-minimal / unfaithful / infeasible)

- **A bundled `PadicHaar` structure with `normalized : μ univ = 1` + `additive` + `product` fields**
  (Proposal 1's A1). REJECTED as non-minimal: `additive` is `measure_biUnion_finset` (in mathlib) and
  `product` is `pi_pi` (in mathlib) — bundling them into an axiom re-axiomatizes what mathlib provides.
  Keep `clusterMeasure`/`cellMeasure` as plain `ℚ`-valued functions and DERIVE additivity from mathlib.
  The only genuine new content of that proposal's A1 (a measure on O_K existing at all) is exactly what
  `AX_cellRecursion`/`AX_columnMeasure` encode as interface facts without claiming a constructed measure.
- **`AX_GMN_IV_terminates` (the explicit `WellFounded` axiom).** REJECTED: dead weight, independently
  provable from `InvImage.wf` / `descend_size_lt`, in no footprint. Drop it.
- **Stating `ballVolume` as an independent axiom separate from the cell `hfactor`** (Proposal 1's A2 as a
  standalone). FOLDED into `AX_columnMeasure`: the per-column values + product structure are exactly the
  `L4.cellVolume_eq` `hfactor` law already battle-tested; no need for a second axiom.
- **Any axiom asserting `clusterVolume`/`density`/`cellMeasure` is rational or uniform.** REJECTED
  categorically — that is the conclusion in disguise (the historical vacuity bug). Rationality is a
  THEOREM via `OMInduction.clusterVol_isRational`.
- **A `MeasureSpace (PadicInt p)` / p-adic Haar construction.** OUT OF SCOPE (explicitly): not in
  mathlib v4.31.0, not required — the interface-axiom approach delivers the theorem without it.
