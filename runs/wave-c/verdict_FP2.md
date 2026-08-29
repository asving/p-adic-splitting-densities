# UNIT FP2 — VERDICT STUB (in progress)

Charge: the multi-residual-point genres' exact counts — per-genre census clause for the
multi-point genres of `nonloopDecidedSet`, + the reduction
`UniformRationalNonloopCensus ⟸ [FP2 theorem] ∧ [named single-point remainder]`.

File: `leanfinal/Uniformity/ChapI/IFCG17.lean` (NEW).

## Planned stages (updated as they land)

- [ ] S1 §1: `stratDecCount` (σ-decided count within a level-0 stratum), bank membership,
      fiberwise partition of `decidedCount` over the monic residuals.
- [ ] S2 §2–§3: ★ the decided-refinement (`exists_decided_factors`: a decided product class
      has decided factor classes at types summing to σ — pure `typeOf_mul` + multiset
      cancellation, NO Hensel) + ★ the binary convolution law `stratDecCount_mul`
      (`#dec_σ(strat(g₁g₂)) = Σ_{s ≤ σ.data} #dec_{⟨s⟩}(strat g₁)·#dec_{⟨σ.data−s⟩}(strat g₂)`).
- [ ] S3 §4: the type-indexed count as an element of `AddMonoidAlgebra ℚ (Multiset (ℕ×ℕ))`
      (`stratPoly`), the coefficient formula, and the ★ product law
      `stratPoly (g₁·g₂) = stratPoly g₁ * stratPoly g₂` — the n-ary fold becomes ring
      multiplication (commutativity/perm-invariance free).
- [ ] S4 §5: primary patterns of residuals via `normalizedFactors` (UFD layer):
      `patternOf`, cons law for coprime prime-power peel, fiber Finsets with avoidance.
- [ ] S5 §6: distinct-tuple aggregates `V` over super-block lists, the exact collision-peel
      `SP(b)·V(L) = V(b::L) + Σ_merge V(...)`, and the labelled double count
      `V(L_π) = mult(π)·Σ_{pattern g = π} stratPoly g`.
- [ ] S6 §7: the uniform-rational-limit calculus (`URseq` closure under +,×,−,Finset sums)
      + THE NAMED SINGLE-POINT REMAINDER (`SinglePointAggregateLaw`,
      `DeepLinearClusterLaw`) + `V_tendsto`.
- [ ] S7 §8: the assembly — pattern cells partition `nonloopDecidedSet`, the loop-corrected
      `{(1,m)}` cell, `RationalNonloopCensusAt m` from the two remainders, and the capstone
      reduction `decidedSliceAt_all_of_singlePoint`.

## Notes so far

- DEDUP FINDING: `Uniformity.Density.Induction.card_levelZeroStratum_mul` and
  `bijOn_mulClass` were ALREADY LANDED at H.102 (2026-08-16) — FP1's §7
  `IFCG16.card_levelZeroStratum_mul` is a re-derivation (verdict_FP1.md's "no prior product
  law exists" is incorrect as stated; the H.102 law is byte-equivalent up to binders).
  Harmless duplication; FP2 consumes the landed H.102/H.103 forms where possible.
- Charge's δ ≥ 5 question: ANSWER — pattern-level identities suffice; no separate I_δ
  (necklace) hypothesis is needed at any m. The irreducible-census rationality is folded
  into the single-point aggregate remainder (sums over irreducibles of degree δ are the
  remainder's own object; for e = 1 blocks its truth is Gauss's count, known math).
