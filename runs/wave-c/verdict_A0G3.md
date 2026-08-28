# VERDICT — UNIT A0G3 (node A0G-PD, n-ary product assembly)

**Date:** 2026-08-28 · **File:** `leanfinal/Uniformity/ChapI/IFCG2.lean` (NEW, 553 lines)
**Status: PROVED — file green, zero `sorry`, all 31 AxCheck footprints Lean-core only
(`propext, Classical.choice, Quot.sound`).**
Verified per discipline: `timeout 580 lake env lean Uniformity/ChapI/IFCG2.lean` — clean
(no errors, no warnings), 31/31 `#print axioms` lines are Lean-core. No dissection cite
inherited (nothing in the file touches `C33Cite`/`fgmn_dvDissection_factor_eq`).

## Dedup finding (read this first — it changes the row's plan)

The blueprint's §6 row lists `typeOf_of_residual_coprime` and `C133mh3.dvResPoly_mul_gen` as
`A0G-PD0`'s landed inputs. Both were read. **Neither is the right tool**:
`typeOf_of_residual_coprime` only handles an already-exact factorization (no level-`N` class,
no "decided" quantifier), and `dvResPoly_mul_gen` is Theorem M clause 3 of the dv-graded
MacLane tower engine (`KeyFrame`/`dvResPoly`), not the `Coeff`/`DecidedAt` combinatorics this
row actually convolves.

**The right tool was already landed by an earlier phase of the same blueprint**: chapter H's
`N-1` "level-0 class transport" (`blueprint/CHAP-H_general_induction.md` §17.1, unit T-1/OM-2,
2026-08-16) — the *same* `leanfinal/` target and the *same* `Uniformity.Density`
`Coeff`/`proj`/`DecidedAt`/`typeOf` objects `DecidedSliceAt` is built from.
`Uniformity.Density.Induction.decidedAt_mulClass` (H.103) is **already** the fully
degree-generic two-block decided/type injection (arbitrary `n₁, n₂`, no `Fin 3` anywhere), with
`mulClass_mem_levelZeroStratum`/`mem_levelZeroStratum_iff` (H.102/H.100) as its supporting
bookkeeping. Per the standing dedup discipline (the `[A0G2]` precedent on `IFCG1`/H123a), this
file does **not** re-derive the binary injection — it reuses H.103/H.104 as the engine and adds
exactly the two things the row still needed: the bridge to H97r4's concrete "unit-derivative
root" presentation, and the n-ary fold.

## What landed, in `Uniformity.Density.IFCG2`

1. **§1–§2, `A0G-PD0` (the bridge + the generic two-block injection).**
   `isCoprime_X_sub_C_of_eval_ne_zero` (field-general: a linear factor is coprime to anything
   it doesn't vanish at, via `EuclideanDomain.dvd_or_coprime` + `dvd_iff_isRoot`);
   `exists_peel_of_root` (arbitrary-degree existence generalization of `H97r1.cubic_peel`'s
   closed form, via `divByMonic`); `eval_derivative_eq_eval_peel` (the product-rule identity
   generalizing `cubic_deriv_eval`'s role); and the payoff
   **`decidedAt_of_linearPeel_decided`** — peeling ANY unit-derivative root off a degree-`(1+n)`
   class with a decided cofactor decides the whole class, at every `n`, proved by handing the
   bridged data to `decidedAt_mulClass`.
2. **§3, the recovery corollary (THE GATE).** `decidedAt_of_peel_decided_recovered` has the
   EXACT statement of `Uniformity.Density.decidedAt_of_peel_decided` (`H97r4.lean:107`, the
   cubic linear×quadratic `DBL` peel), reproved as the `n = 2` instance of §2 fed through
   `H97r1.cubic_peel`. `1 + 2` reduces to `3` on the nose — no cast, no `Fin`-reindexing lemma
   anywhere in the recovery (`example : (1 + 2 : ℕ) = 3 := rfl` records this).
3. **§4–§5, `A0G-PD1` (the n-ary fold).** `PDBlock O N` bundles a coprime residual block
   (monic residue polynomial + degree + level-`N` class + stratum membership + decided type);
   `degSum`/`typeSum`/`gProd`/`combinedClass` fold a `List (PDBlock O N)` by plain structural
   recursion (not `List.sum`/`List.prod`, so the dependent type `Coeff O (degSum L) N` matches
   the recursive step by construction, no cast); full `@[simp]` equation-lemma API
   (`degSum_cons`, `typeSum_cons`, `gProd_cons`, `combinedClass_cons`, + `nil` forms).
   **`combinedClass_mem_and_decided`/`decidedAt_combinedClass`**: for any pairwise-coprime
   block list, the fold both lies in the combined stratum and is decided at the convolved type
   `typeSum L`, proved by structural induction feeding `decidedAt_mulClass` at every cons step.
   Plus `mulClass_unit_right` (the empty list is a two-sided unit for the fold),
   `decidedAt_combinedClass_singleton` (the `k = 1` sanity instance), and
   `pairwise_coprime_pair` (2-block convenience unfolding).
4. **§6, order-independence (the `A0G-PD1` gate).** `degSum_perm`/`typeSum_perm`/`gProd_perm`:
   the fold's degree, its convolved type, AND its underlying residue-polynomial product are all
   `List.Perm`-invariant (via `List.Perm.sum_eq`/`List.Perm.prod_eq` after an auxiliary
   `_eq_sum`/`_eq_prod` bridge to `List.map`, proved separately from the recursive definitions
   so no defeq is disturbed); `pairwiseCoprime_perm` shows the hypothesis itself transports
   along any reordering (`List.Perm.pairwise_iff`, `IsCoprime.symm`). Every ingredient
   `decidedAt_combinedClass` needs — hypothesis, degree, type, stratum witness — is therefore
   order-independent.

## GATE (both satisfied)

* **Recovers the landed cubic `DBL` use, degrees add exactly:** §3, byte-identical statement,
  `1 + 2 = 3` with no cast.
* **Order-independent:** §6, `degSum_perm`/`typeSum_perm` (+ the bonus `gProd_perm`).

## Size note

553 lines vs. the row's 550–950 estimate (binary 300–500 + n-ary 220–380 ≈ 520–880) — the
dedup against H.103/H.104 removed the from-scratch binary-injection cost the row budgeted for
`A0G-PD0`, so the file sits near the combined estimate's low end even with the added equation
lemmas, the unit-fold lemma, and the full `gProd`/hypothesis order-independence bonus content.

## Downstream (per the §6 critical path, `PD ──→ FP → CL → AS → DS → ALL`)

`PDBlock` is the exported unit for `A0G-HE`/`A0G-NP` to populate (their `g`, `c`, `strat`,
`dec` fields from the dv-graded engine's certified pure blocks) and for `A0G-CH`/`A0G-CL` to
fold via `decidedAt_combinedClass`. Nothing here constructs a `PDBlock` from scratch beyond
§2's linear-peel leaf — that is intentionally `A0G-HE`/`A0G-NP`'s job.

## Trust boundary

Every declaration in this file is NEW (flagged for the standing review) except where it
explicitly cites a landed theorem (`decidedAt_mulClass`, `mulClass_mem_levelZeroStratum`,
`mem_levelZeroStratum_iff` from H.100/H.102/H.103; `cubic_peel`, `peel` from H97r1, via H97r4).
No landed file touched; no new axiom; footprint Lean-core throughout.
