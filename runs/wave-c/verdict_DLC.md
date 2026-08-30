# UNIT DLC — VERDICT: LANDED (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG20.lean` (636 lines, ZERO sorries,
axiom footprint Lean core `{propext, Classical.choice, Quot.sound}` on every footer
line; the C.33 cite does not occur; no landed file touched except the sanctioned
one-line aggregator import in `Uniformity/ChapI.lean`). Targeted
`lake build Uniformity.ChapI.IFCG20` green (8916 jobs); `lake env lean Uniformity/ChapI.lean`
green.

## ★★ THE RESULT — the kernel is EQUIVALENT to its fractional cell

`DeepLinearClusterLaw` does NOT fully close (see the answer below), but it is now
provably an IFF with a strictly smaller named remainder:

    def DeepFractionalCellLaw : Prop :=          -- kernel-verbatim shape
      ∀ m, 4 ≤ m → (smaller value laws below m) →
      ∀ σ, σ.degree = m → Witnessed m σ →
        ∃ n d : Polynomial ℚ, d ≠ 0 ∧ ∀ O [complete DVR, finite residue],
          d.eval q ≠ 0 ∧ ∀ π, Irreducible π →
            Tendsto (fun M => (fracCellCount O π m σ M : ℝ) / q^(m·(M+m)))
              atTop (nhds (n.eval q / d.eval q))

    theorem deepLinearClusterLaw_iff_fractionalCell :
      DeepLinearClusterLaw ↔ DeepFractionalCellLaw          -- an IFF: nothing weakened

    theorem decidedSliceAt_all_of_singlePoint_fractional :
      SinglePointAggregateLaw → DeepFractionalCellLaw → ∀ n, DecidedSliceAt n

where `fracCellCount O π m σ M = Nat.card ((nonloopDecidedSet ∩ {pattern = {(1,m)}})
\ range (fullLoopClassN π))` and `fullLoopClassN π (γ, d) = proj (loopMapN γ π d)` is
IFCG3's recentering extended to ALL mixed boxes (no decidedness constraint).

## KEY-QUESTION ANSWER (charge item 2): is the law derivable from the recursion?

**NO for the full law — and the file proves exactly what the recursion structure DOES
give.** The integer-recentering geometric series is already spent upstream (IFCG14's
fixed-point bridge sums `D = B + q^(1-T_m)·D`; IFCG15's loop subtraction removes the
once-recentred image of the level-M-DECIDED boxes). The loop-corrected cell `pcellCount`
splits exactly (proved, `pcell_partition`) as

    pcellCount + q^(1+κ_m)·decidedCount(M) = #decidedPairs + fracCellCount

with `decidedPairs` = recentrations decided at the TARGET level M+m. The mismatch
(#decidedPairs − loop image) — the "decides inside the window (M, M+m]" boundary — is
annihilated in the limit UNCONDITIONALLY and DRAINAGE-FREE:

* ★ `decided_of_mixedTruncN` (the lift correspondence, the unit's engine): if the
  recentring of a mixed box is decided at M+m, EVERY uniform-(M+m) refinement of the box
  is decided — the recentering `f ↦ π^m·g((X−γ̃)/π)` is a type-preserving bijection
  between uniform lifts of the class and mixed lifts of the box (assembled from IFCG3's
  `typeOf_scaleVecN`, IFCG1's `typeOf_shiftVecN`/`dvd_shiftVecN_sub`,
  `mkBoxN_eq_iff_dvd`; ~30 lines, no new hard math).
* `card_ker_pairTruncN`: the truncation `Coeff O m (M+m) →+ MBoxN O m M` (new
  `mixedTruncN`, mirroring `mtruncN`'s AddMonoidHom pattern) has fibre exactly `q^(T_m)`.
* `card_decidedPairs_mul_le`: hence `#decidedPairs · q^(T_m) ≤ q·decidedCount(M+m)`;
  with the landed lower bound (the loop image), the normalized boundary is squeezed into
  `q^(1-T)·[decidedSeq(M), decidedSeq(M+m)]`, whose width → 0 by the LANDED monotone
  convergence `decidedSeq_tendsto` ALONE (`tendsto_pcell_iff_frac`, via `squeeze_zero`).

**What remains — and why the recursion cannot reach it:** the fractional cell has, BY
CONSTRUCTION, no self-similarity under integer recentering (it is the complement of the
full recentering range at every centre), so no further geometric series exists in this
structure. Mathematically its members are the deep clusters whose recentred Newton
polygon dips below the slope-1 line at visible precision — some root valuation in (0,1),
necessarily FRACTIONAL. This is the same fractional-slope Okutsu–Montes cone census as
`SinglePointAggregateLaw`'s `e ≥ 2` blocks: ONE open heart, two entry points.

## Census front after this unit

Remaining gap = `SinglePointAggregateLaw` AND `DeepFractionalCellLaw` (which replaces
`DeepLinearClusterLaw` losslessly). Both are fractional-slope cone censuses; a future
unit that lands the deep-cone census machinery discharges both.

## Stages (all closed)

- [x] S1 `fullLoopClassN` + injectivity (= IFCG3.loopMapN_inj) + loop-range inclusion +
      deep-pattern confinement (IFCG18 §6's proof, verbatim at the full range).
- [x] S2 `mixedTruncN`/`pairTruncN` + `card_ker_pairTruncN = q^(T_m)`
      (via `card_preimage_of_surjective` at Set.univ + exponent arithmetic κ+T = m²).
- [x] S3 ★ `decided_of_mixedTruncN` (the lift correspondence).
- [x] S4 `card_decidedPairs_mul_le` + ★ `pcell_partition` (exact ℕ identity).
- [x] S5 ★ `tendsto_pcell_iff_frac` (the boundary annihilation squeeze).
- [x] S6 `DeepFractionalCellLaw` + ★★ `deepLinearClusterLaw_iff_fractionalCell` +
      `decidedSliceAt_all_of_singlePoint_fractional`. AxCheck footer: Lean core on all
      9 lines.

## Repair notes (3 compile passes to green)

- `stratumPoly`/`levelZeroStratum` live in `Uniformity.Density.Induction` (H124/H100) —
  open the namespace FULLY (IFCG18 did; a selective open misses them).
- `omega` cannot see `a·b = b·a` for opaque ℕ products (treats each order as a fresh
  atom) — commute with an explicit `Nat.mul_comm` calc step before feeding it counting
  identities.
- A single-step outer `calc A ≤ B := by …` wrapping the same statement as its `have`
  parses badly mid-block — drop the wrapper, keep the inner `refine …; calc`.
- Deprecations at this pin: `Set.diff_subset → Set.sdiff_subset`,
  `Set.ncard_inter_add_ncard_diff_eq_ncard → …_ncard_sdiff_…`, `Set.mem_diff → mem_sdiff`.
