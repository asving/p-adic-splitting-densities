# UNIT CSL — VERDICT: THE q-POWER FIBER LAW AND THE HENSEL LEG BOTH LAND, PURE LEAN-CORE — `#fiber = q^v` is machine-checked EXACTLY (both directions at once, uniform in q, sizes, levels) via a new Smith-normal-form index-determinant engine over the DVR; RDC's `LiftsFactor` existence leg is DISCHARGED by a depth-`v` Newton iteration (for `2v+1 ≤ N`, the classical Hensel bound); RDC's decidedness-transfer criterion now FIRES with both legs proved and mixDepth-keyed — while `CollisionLaw`/`StrayLaw` honestly do NOT fire (the depth-stratum root counts + the drainage premise are the exact named remainder) (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG42.lean` (1541 lines, ZERO sorries, zero
warnings, zero errors; 13 AxCheck footer lines, ALL pure Lean core
`{propext, Classical.choice, Quot.sound}` — **no B.42, no C.33, no `AX_cellRecursion`;
the fiber law and the Hensel leg are unconditional Lean-core theorems**).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG42.lean`
(final run: only the 13 footprint infos); targeted
`lake build Uniformity.ChapI.IFCG42` GREEN (8955 jobs).  Sanctioned aggregator import
inserted in `Uniformity/ChapI.lean` between IFCG41's and IFCG43's.  No git ops.

## THE HEADLINES

1. **★★ THE q-POWER FIBER LAW** (`natCard_pairNbhd`, §3; mixDepth-keyed socket
   `natCard_pairNbhd_of_mixDepth`, §5): at EXACT resultant depth `v` (`π^v ∣ Res`,
   `π^{v+1} ∤ Res` — equivalently `mixDepth = v` via the §5 bridges) with
   `2v + 1 ≤ N` and either mass nonzero, the set of level-`N` class pairs with the
   same `mulClass` product as `(a₁, a₂)` and factors ≡ `(a₁, a₂)` mod `π^{v+1}` has
   EXACTLY `q^v` members.  This is RDC's named remainder (i) — the pair-map fiber
   over a product cell has exactly `q^{depth}` members per cluster — with the `≤`
   (separation) AND `≥` (construction) directions landed in one stroke: the
   neighborhood is in explicit bijection with the kernel of the Sylvester map mod
   `π^v`.  RDC's gap engine `mulClass_fiber_gap` runs the separation/exhaustion leg
   (`exists_phiMap_eq`); the perturbation parametrization
   `phiMap : (ε,η) ↦ (a₁ + π^{N-v}ε, a₂ + π^{N-v}η)` runs the construction leg
   (`phiMap_mem_pairNbhd`); coset-faithfulness (`phiMap_eq_iff`) transports the count.
   At `v = 0` the law says the neighborhood is a singleton — level-exact injectivity,
   coherent with IFCG41's unit-corner instance.
2. **★★ THE INDEX-DETERMINANT LAW over the DVR** (`natCard_quotient_range_smith`,
   §1): an injective endomorphism `φ` of a finite free `O`-module with
   `det φ ~ π^w` has cokernel of size EXACTLY `q^w`.  THE Smith-normal-form/Igusa
   counting engine, fully uniform, reusable for the census: mathlib's general-PID
   `Submodule.quotientEquivPiSpan` + `smithNormalForm*` data mirror the ℤ-only
   `Submodule.natAbs_det_equiv` proof, transposed to the DVR with the corpus's
   `card_res` counting each cyclic factor.  Specialized (§2) to mathlib's
   `sylvesterMap` (whose matrix IS the Sylvester matrix, `toMatrix_sylvesterMap'`,
   hence determinant = the pinned-size resultant): `sylvesterMap_injective`
   (adjugate cancellation), `natCard_quotient_range_sylvesterMap` (#coker = q^w),
   `smul_top_le_range_sylvesterMap` (π^v·M ⊆ range, adjugate + scaling, w ≤ v), and
   ★ `natCard_ker_sylvesterMap_quot` (#ker mod π^v = q^w EXACTLY — Lagrange + first
   iso on the finite level-`v` quotients + third iso `quotientQuotientEquivQuotientSup`
   to the cokernel).
3. **★★ THE HENSEL LEG DISCHARGED** (`liftsFactor_of_not_dvd_resultant`, §4): RDC's
   `LiftsFactor π v N a₁ a₂` — the polygon-block factor-lifting existence leg, RDC's
   named remainder (ii) — HOLDS VERBATIM for `2v + 1 ≤ N`, either mass nonzero, and
   `π^{v+1} ∤ Res`.  Mechanism (`exists_monic_factorization_of_bezout` +
   `newton_step`): a depth-`v` Newton iteration in which every stage re-derives a
   NORMALIZED Bezout witness from its own resultant (depth is congruence-stable mod
   `π^{v+1}` via `resultant_map_map`; mathlib's Sylvester-adjugate Bezout
   `exists_mul_add_mul_eq_C_resultant` carries the degree bounds), kills the linear
   term EXACTLY (`G·w₀ + H·u₀ = C(π^v)·E` by monic division), leaves the quadratic
   error at doubled level `2(k−v) ≥ k+1`, and converges through the corpus's
   `exists_adicLimit_of_degree_lt` with per-coefficient Hausdorff separation closing
   the exact factorization `F = g'·h'` with `C(π^{N-v}) ∣ g'−g, h'−h`.
4. **★ THE TRANSFER CRITERION FIRES** (`decidedAt_mulClass_of_not_dvd_resultant`,
   `decidedAt_mulClass_of_mixDepth`): RDC's `decidedAt_mulClass_of_liftsFactor` — the
   `hdec` discharge criterion for SDL's sector-converse gate — now fires from the
   resultant/mixDepth data alone: exact depth `v`, `2v+1 ≤ N`, factors decided at the
   shifted level `N−v` ⟹ product class `⟨σ₁.data + σ₂.data⟩`-decided at level `N`.
   BOTH legs (uniqueness = RDC's gap engine, existence = this file's Newton engine)
   machine-checked, Lean-core.

## Answer to the charge's XHS question

`LiftsFactor` needed NEITHER `exists_class_block_split` nor a shifted variant: XHS's
split lives in the NP-face/residual-factorization frame (coprime residual pieces,
`v = 0` genre after rescaling), while `LiftsFactor` demands lifting at arbitrary
depth `v`.  The general discharge came from a NEW depth-`v` Newton engine built on
the corpus's `HenselFactorization` limit machinery; it subsumes the `v = 0`/coprime
case (where `2·0+1 ≤ N` is just `N ≥ 1`), so no XHS import was consumed.

## THE HONEST FENCE (what remains of the census, exactly)

`CollisionLaw m σ`/`StrayLaw m σ` (hence `SplitSectorLaw` at `m ≥ 4`) do NOT fire in
this unit.  With the fiber law the remainder is now PRECISELY (§5 docstring):

1. **The depth-stratum ROOT COUNTS** — each depth-`v` cluster of a `pairDepthFiber`
   is a `pairNbhd` of size exactly `q^v`, so RDC's graded census
   `convCount = #vis + Σ_k (k−1)·#visStrata_k + Σ_k k·#strayStrata_k` reduces to
   counting CLUSTER ROOTS: a level-`(v+1)` digit-box quantity (N-free!) per depth —
   the `v(Res) = v` coefficient-box measure (DBL's instrument genre / the elementary
   route into the classical |Res| Igusa integral).  Their normalized limits are the
   one remaining engine.
2. **The DRAINAGE premise** — identifying `pairDepthFiber` as a disjoint union of
   `pairNbhd`s requires the fiber's member pairs to be decided at the SHIFTED level
   `N − v` (the same `hd₁/hd₂` genre the transfer criterion consumes): the
   level-stabilization of the decided census.  In the `M → ∞` limit with `v` fixed
   this is the natural regime (`N − v = M + m − v → ∞`), but it must be proved.
3. `LiftsFactor` below the classical bound (`N ≤ 2v`) is untouched (and is not
   expected to hold there).

Every uniqueness, existence, and counting MECHANISM those need is now landed
(§1–§4 here + RDC's graded identities); the remainder is census-side measure theory.

## File map (`IFCG42.lean`, 1541 lines, all Lean-core)

§0 `pow_eq_of_associated_pow`, `card_quot_span_associated_pow` · §1 ★★
`natCard_quotient_range_smith` · §2 torsion-free local instances,
`smul_id_injective`, `natCard_quotient_smul_id`, `sylvesterMap_injective`,
`natCard_quotient_range_sylvesterMap`, `smul_top_le_range_sylvesterMap`, ★
`natCard_ker_sylvesterMap_quot` · §3 `pairNbhd`, vecPoly instruments,
`monicPoly_sub_eq_C_mul`, `C_pow_dvd_mul_sub_of_mulClass_eq` (IFCG41 private,
copied) + converse `mulClass_eq_of_C_pow_dvd`, `mem_smul_range_of_C_dvd`,
`C_pow_dvd_cancel`, `phiMap`, `monicPoly_phi_eq`, `frame_prod_expand`,
`phiMap_eq_iff`, `phiMap_mem_pairNbhd`, `exists_phiMap_eq`, ★★ `natCard_pairNbhd` ·
§4 `mem_coeffIdeal_iff_C_dvd`, `newton_step`, ★★
`exists_monic_factorization_of_bezout`, ★★ `liftsFactor_of_not_dvd_resultant`, ★
`decidedAt_mulClass_of_not_dvd_resultant` · §5 `dvd_resultant_of_mixDepth`,
`not_dvd_resultant_of_mixDepth_lt`, ★★ `natCard_pairNbhd_of_mixDepth`, ★★
`decidedAt_mulClass_of_mixDepth` + the precise census fence · AxCheck footer (13
lines).  Imports: `Uniformity.ChapI.IFCG41` only (through it, SDL/RDC; the
`HenselFactorization` engine arrives via the existing import graph).

## Design decisions (recorded)

* **The mathlib jackpot**: this pin's resultant file carries `sylvesterMap` (the pair
  map as a linear map on `degreeLT` products), `toMatrix_sylvesterMap'` (its matrix
  IS the Sylvester matrix), `adjSylvester` with both `∘`-identities `= Res • id`, and
  the Bezout lemma WITH degree bounds — so the fiber law's linear algebra needed no
  hand-built Sylvester theory.  The counting side similarly: general-PID
  `Submodule.quotientEquivPiSpan`/`smithNormalForm*` — only the ℤ→DVR transposition
  of the determinant-index law was missing, and it is §1.
* **Statement shapes**: `pairNbhd` congruences are phrased on lifts
  (lift-independent for `v+1 ≤ N`), keeping the set `Coeff`-native;
  `natCard_ker_sylvesterMap_quot` takes the `mapQ` compatibility as a `≤ comap`
  hypothesis so the census can instantiate it with any presentation of the level-`v`
  reduction; `hpos : n₁ ≠ 0 ∨ n₂ ≠ 0` is carried honestly (mathlib's Bezout needs
  it; census consumers always have both masses positive).
* **No cite consumed**: the elementary route carried everything; the declared
  `AX_cellRecursion` family remains untouched and available for the census
  measure-side remainder.

## Repair log (≈10 error rounds, ALL mechanical; every theorem landed as designed)

1. Pin renames/moves: `Basis` → `Module.Basis`; `Ideal.quotEquivOfEq` takes only the
   equality; `NoZeroSMulDivisors.of_algebraMap_injective` absent (proved the three
   torsion-free instances — polynomial/submodule/prod — by hand, local instances);
   `Ideal.neg_mem` → `neg_mem`; `modByMonic_add_div (p q)` takes the divisor, no
   monicity argument; `push_neg` deprecated → `rw [not_le]`.
2. `Finsupp.single_eq_of_ne` in this pin wants the `i ≠ j` orientation (twice).
3. Under-specified coercions (`(e1 : _ →ₗ[O] _)`) stall elaboration → `.toLinearMap`;
   `(by omega)` args before implicit `N v` are pinned → name the implicits.
4. `rw [← hNvv]`-style rewrites of `N` loop into `N - v` occurrences → prove the
   `π^N = π^{N-v}·π^v` split as a standalone `have` (IFCG41's idiom).
5. `congr 2` on `C (π^a) = C (π^b)` splits unpredictably → same split-idiom.
6. One self-inflicted cut: an Edit anchored on a docstring's first line ate it;
   restored.  `dvd_add_right` wanted the divisible summand left → `add_comm` first.
