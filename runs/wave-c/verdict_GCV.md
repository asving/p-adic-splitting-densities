# UNIT GCV — VERDICT: THE DEEP-BOX DRAINS CLOSE AT EVERY POSITIVE MASS SPLIT — the
`primo` value stack is summed in closed form (`Σ'_v primo(q,δ,e,v)·q^{−v} = q^{δe}`,
the recursion's fixed point), the Cauchy product assembles it over patterns and monics
into VA23's named identity `Σ'_v zed(K,n,v)·q^{−v} = q^{2n}` (the full-box strata
masses sum to 1), and `DeepStratumDrain n₁ n₂` fires OUTRIGHT for ALL `n₁, n₂ ≥ 1`
(the charged `min ≥ 2` remainder closes AND VA23's `min = 1` fires are subsumed) —
the census and capstone masters are recomputed with the drain premise GONE — while
the charge's items (a) genre-restricted cluster values and (c) collision limits
honestly do NOT close (the charged mechanisms conflate residual patterns with decided
types resp. presuppose one-cluster-per-cell; exact reasons below), so the convolution
row does not fall outright and now rests on exactly {cluster values, collision
limits} (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG73.lean` (849 lines, ZERO sorries,
zero errors, zero warnings; 11 AxCheck footer rows).  **Axiom fence, machine-exact:**
EIGHT rows PURE Lean core `{propext, Classical.choice, Quot.sound}` — the entire
value-stack layer (§§1–3) AND both drain theorems (`deepStratumDrain_all`,
`deepStratumDrain_min_two`): **the drain is an unconditional Lean-core theorem**
(GNA's census, IGV's transport, VCL's box partition, VA23's GE partition are all
Lean-core).  The re-based row + census master carry exactly the owner-signed B.42
cite `Uniformity.Density.Leaf.exists_slope_factorization` (inherited through VA23's
assembly — never re-consumed); the capstone master adds exactly
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).
**C.33 and `AX_cellRecursion` do NOT occur.**  Zero new definitions — all currencies
are VA23's.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG73.lean` (6 increments, each GREEN
before the next — increments 1–5 first-attempt or one mechanical repair; final run:
exactly the 11 footprint infos); targeted `lake build Uniformity.ChapI.IFCG73` GREEN
(9047 jobs); sanctioned aggregator import inserted after IFCG71's line, aggregator
`lake env lean Uniformity/ChapI.lean` GREEN (exit 0, with IFCG72's import — the other
unit's — also present and green).  IFCG72.lean untouched.  NO git operations.

## ★★★ THE HEADLINES

    theorem tsum_primo_mul :                        -- ★ THE PRIMARY VALUE STACK
      Σ'_v primo(q,δ,e,v)·q^{−v} = q^{δe}           -- the recursion's fixed point:
                                                    -- self-loop x^E·S + telescoped
                                                    -- peels (q^E − 1); S = q^E
    theorem summable_tsum_patRate_mul :             -- ★ THE PATTERN STACK
      Σ'_v coeff_v(patRate q λ)·q^{−v} = q^{weight λ}  -- Cauchy product over blocks
    theorem tsum_zed_mul :                          -- ★★ VA23'S NAMED IDENTITY
      Σ'_v zed(K,n,v)·q^{−v} = q^{2n}               -- the q^n monics × shape box q^n:
                                                    -- full-box strata masses sum to 1
    theorem deepStratumDrain_all (h₁ : 0 < n₁) (h₂ : 0 < n₂) :  -- ★★★ THE DRAIN,
      DeepStratumDrain n₁ n₂                        -- EVERY split, Lean-core,
                                                    -- UNCONDITIONAL
    theorem visCensusLaw_of_clusterGeom_collisions :  -- ★★★ THE ROW, DRAIN-FREE
      VisEntryClusterGeom (all entries, both genres) + CollisionLaw +
      power-collision ZcURLim ⟹ ∀ g, VisCensusLaw g m σ   -- EVERY mass, EVERY type
    theorem decidedSliceAt_all_of_clusterGeom / capstoneHypotheses_of_clusterGeom :
      -- ★★★ BOTH MASTERS RECOMPUTED, the hDR premise GONE (other rows byte-identical)

## The four charge items, disposition

**(1) The genre-restricted per-depth cluster values — does NOT close; the charged
mechanism is unsound.**  The charge proposed the genre-restricted census as the
type-restricted sub-sum of GNA's assembly (filter `patternUniverse`).  The genre is
sector membership of the PRODUCT cell (`visGenreSet g` = `splitSectorVis` /
`powerSectorProperVis`) — a condition on the decided factorization type at the deep
level `M + m` — while GNA's assembly (`zed = Σ_g coeff(patRate(patternOf g))`) is
graded by the RESIDUAL (mod-π) pattern of the level-0 reduction only.  The two
gradings coincide only in order-0/tame situations; deriving type-restricted values
from pattern-restricted ones is classifier content (the deep tower), not a sub-sum.
`VisEntryClusterGeom` (the sector-membership × depth joint census + the geometric-in-v
structure) remains the named remainder EXACTLY as VA23 fenced.  Nothing was asserted.

**(2) The `min ≥ 2` drains — CLOSED, stronger than charged.**  Route (all landed):
* §1 `primo_succ` (the recursion with the attach-sum flattened), `sum_peel_telescope`
  (the ℕ-telescope `Σ_j (q^{E−δj} − q^{E−δj−δ}) + q^{E−δW} = q^E`, additive, no
  truncated subtraction), ★ `sum_primo_mul_le` (partial sums ≤ q^{δe}: the fixed-point
  INEQUALITY `P ≤ x^E·P + (q^E−1)` solved), `summable_primo_mul`, ★ `tsum_primo_mul`
  (the fixed-point EQUATION `S·(1−q^{−E}) = q^E − 1` solved; strong induction on `e`,
  tsum-shift instruments).  Cross-checks: e = 0 gives 1 = q^0; e = 1 gives
  `(q^δ−1)·Σ q^{−δk} = q^δ` (IGV's flat geometric law).
* §2 ★ `summable_tsum_patRate_mul`: multiset induction + mathlib's antidiagonal
  Cauchy instruments (`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`;
  nonneg coefficients make norm-summability free).
* §3 ★★ `tsum_zed_mul`: each monic contributes its shape box `q^{weight(patternOf g)}
  = q^n` (`patternWeight_patternOf`), and `#monicFinset = q^n` (`card_monicOfDeg`).
* §4 `card_depthPairSet_general` (NEW exact census, ℕ-multiplied form):
  `#depthPairSet(n₁,n₂,L,v)·q^{v+2n₁} = zed(K,n₁,v)·q^{(n₁+n₂)L}` for `0<n₁≤n₂, v<L`
  — IGV's `card_depthPairSet_reduce` composed with GNA's
  `card_redDepthPairSet_general`; the normalized stratum mass is the LEVEL-FREE
  `zed(K,min,v)·q^{−v−2·min}`.  Then the GE mass is `1 − (head masses)` (VA23's GE
  partition + VCL's box partition), the head masses tend to `Σ' = q^{2n}·q^{−2n} = 1`
  (§3 + `HasSum.tendsto_sum_nat`), and ★★★ `deepStratumDrain_all` fires at EVERY
  positive split (swap for `n₂ < n₁`).  The `min = 1` case reproves VA23's fires
  through the general stack — consistent, and VA23's exact `q^{−(V+1)}` envelope
  remains the sharper per-level statement there.

**(3) The two collision limits — do NOT close; the charged mechanism is unsound.**
The charged formula `collisions = Σ_v (q^v − 1)·(clusters at depth v)` (with RDC's
graded identities + CSL's `q^v` fiber law) is exact ONLY if every visible cell is hit
by exactly one cluster across the WHOLE convolution table.  False in general: a
visible cell admits multiple `(mass split, part)`-groupings — e.g. a fully split type
at `m = 4` is hit under `(1,3)/(2,2)/(3,1)` and multiple parts.  The discrepancy
`Σ clusters − #vis` is precisely the per-cell cluster-multiplicity (block-grouping)
census — VCL's fence axis (iii), B.42's genre — and is exactly what `CollisionLaw`
must still supply.  No dishonest identity was stated.

**(4) FIRE `VisCensusLaw` at every ramified multi-σ — does NOT close (needs (1) and
(3)); what lands is the row and BOTH masters with the drain axis eliminated.**

## THE CENSUS MASTER, RECOMPUTED EXACTLY (the charge's "state exactly")

After this file (`decidedSliceAt_all_of_clusterGeom`, census spine),
`∀ n, DecidedSliceAt n` rests on:
1. **The convolution row (rows 3/4), DRAIN-FREE**: at each ramified non-singleton
   `(e ≥ 5, σ)` under the `< e` value laws — (i) `VisEntryClusterGeom g n₁ n₂ σ part`
   for both genres at every admissible mass split/type part, (ii) `CollisionLaw e σ`
   + the power-collision `ZcURLim`.  **VA23's axis (ii) — the σ-free
   `DeepStratumDrain` at `2 ≤ min` — is GONE (this unit's theorem).**
2. `PowerFullSpanLaw` (row 2 leg), `LeafSubfaceLaw` at non-singleton σ (row 5), the
   `e = 4` remainder laws — byte-identical to VA23's master.
On the capstone spine (`capstoneHypotheses_of_clusterGeom`): {ladder/deepTwist
supply, FC_D (`FactorCorrespondenceAt`), `EisFullSpanRemainderLaw` (where the r ≥ 2
frames / h ≥ 2 carrier gap / MixedFaceLaws live, unchanged), the row-1 base} + item 1
above + `LeafSubfaceLaw`.  The charge's predicted post-unit master {FC_D, r ≥ 2
frames, h ≥ 2 gap, MixedFaceLaws} presupposed items (1)/(3); the honest recomputation
keeps {cluster values, collision limits} as the convolution row's exact residue.

## File map (`leanfinal/Uniformity/ChapI/IFCG73.lean`, 849 lines)

§1 `sum_peel_telescope` (private), `sum_ite_shift` (private), `primo_succ` (private),
★ `sum_primo_mul_le`, `summable_primo_mul`, `tsum_ite_shift` (private),
`sum_peel_cast` (private), ★ `tsum_primo_mul` ·
§2 `patternWeight_cons` (private), ★ `summable_tsum_patRate_mul` ·
§3 `card_monicFinset` (private), `zed_expand` (private), `summable_zed_mul`,
★★ `tsum_zed_mul` ·
§4 `card_depthPairSet_general` (private), `deepStratumDrain_of_le` (private),
★★★ `deepStratumDrain_all` ·
§5 `deepStratumDrain_min_two` (the masters' premise currency, now a theorem),
★★★ `visCensusLaw_of_clusterGeom_collisions`, ★★★ `decidedSliceAt_all_of_clusterGeom`,
★★★ `capstoneHypotheses_of_clusterGeom` · AxCheck footer (11 rows).
Imports: Mathlib + IFCG70 + IFCG71 (everything else transitive).  Aggregator: one
import line after IFCG71's (the sanctioned touch).

## Design decisions (recorded)

* **The value stack proved from the recursion, not the census**: summability and the
  partial-sum bound come from `primo`'s own fixed-point inequality (no DVR witness,
  no irreducible-of-degree-δ existence needed), so the whole stack is uniform in
  abstract `q ≥ 2` and Lean-core.
* **The fixed point solved additively**: the self-loop `x^E·S` is isolated by
  `mul_right_cancel₀` against `1 − x^E > 0`; the peel coefficients stay as opaque
  ℕ-subtraction casts until the single telescope evaluation (`sum_peel_cast`).
* **Cauchy product via mathlib's antidiagonal instruments** — the `PowerSeries ℕ`
  coefficients enter only through `coeff_mul`/`coeff_mk`/`coeff_one`; nonnegativity
  makes norm-summability a `congr`.
* **The exponent bookkeeping `zify`-discharged**: the one nonlinear ℕ-subtraction
  identity (`n₁(2L−1) + ((n₂−n₁)L + n₁) = (n₁+n₂)L`) goes to ℤ with the two ≤ side
  conditions and closes by `ring`.
* **`deepStratumDrain_min_two` stated in the masters' exact premise shape** so the
  re-based masters are one-line applications of VA23's.

## Repair log (2 rounds, both mechanical; every theorem landed as designed)

1. Pin names: bare `tsum_add`/`tsum_sum` are now the to_additive-generated
   `Summable.tsum_add`/`Summable.tsum_finsetSum`; an over-eager `rw [mul_sub]` hit
   the wrong side (replaced by `nlinarith [hmain, hqxE]`).
2. `Finset.card_image_of_injective` needs `DecidableEq K[X]` — `classical`.

## Cross-checks

* `tsum_primo_mul` at `e = 1`: `(q^δ − 1)·Σ_k q^{−δk} = q^δ` — IGV's flat geometric
  law; at `e = 0`: the unit mass.  The `(1,n₂)` drain instance now has two
  independent proofs (VA23's exact `q^{−(V+1)}` envelope; this stack) — consistent.
* The axiom split confirms the design: the drain never touches B.42 (it is a pure
  box statement); B.42 enters exactly where VA23's assembly consumes VCL's graded
  census, never earlier.
* Consistency with VA23's fence: remainder axes (i)/(iii) survive verbatim as
  `VisEntryClusterGeom`/collision hypotheses; axis (ii) is GONE (this unit).
