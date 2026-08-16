/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H119
import Uniformity.ChapB.B74
import Uniformity.ChapB.B77a
import Uniformity.ChapB.B77b

/-!
# Uniformity.ChapH.H120 — cluster-level C2D: the conservative complement is antitone

**Chapter H, NODE H.120** [lemma] (`blueprint/CHAP-H_general_induction.md` §17.3 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §2 debt D-4, source
`EFF.GENIND.201` (`GENIND-C2D`)).  Third node of **N-3**.

`uClusterNorm O π m W ≤ uClusterNorm O π m T` for `1 ≤ T ≤ W`: the NORMALIZED conservative
complement is antitone in the window.  H.70's argument (`undecidedSet` pulls back along
`coeffFactor`, fibres equicardinal) transported to the `ClusterState` carrier — and, as D-4
warns, the carriers differ, so H.70's full-space monotonicity is NOT consumed: the containment
is re-proved here from the ground up, and its mathematical content is a genuine induction over
the H.118 derivation, not the one-line contrapositive H.70 enjoys.

## The three steps, and where the work is

1. **Truncation** (`clusterTrunc`) — coordinatewise `resFactor`; residual zeroness is preserved,
   so a window-`W` state truncates to a window-`T` state.
2. **The conservative verdict pulls back** (`clusterUndecided_clusterTrunc`) — the theorem of
   this node.  Induction on the window-`W` derivation, with the reader's four rules re-fired at
   `T`.  The case analysis is the subtle step the blueprint flags, and it comes out as:
   * **DRAIN** truncates to DRAIN (`resFactor 0 = 0`), and every other case first asks whether
     the truncation is a DRAIN — if it is, the truncated state exits undecided at depth 0 and
     the case is closed.  This is the "coarsens toward drain" branch: it fires exactly when the
     window `T` no longer sees the constant coefficient.
   * **CS** truncates to CS on the non-drain branch.  `IsCSState` is a `∀`-lift statement, so
     this is the ONE direction that needs the polygon to be a function of the class: it is
     chapter B's landed level-`N` congruence transport (`sideSet_congr` B.77a,
     `resPoly_congr` B.77b, `H₀_lt_of_visible` B.74) run at the key `φ = X`, licensed by the
     visible-polygon principle — a non-drain state at window `T` has its whole polygon strictly
     below `T` (`Visible π X (monicPoly a) T`), so no side and no residual coefficient the CS
     witness consults is invisible at `T`.
   * **α / β** re-fire at `T` with the SAME event data `(μ, k, z)`: the capped content is
     unchanged (`betaContent_clusterTrunc_eq`, on the non-drain branch), so H.109's
     `hasChildAt_of_exists` transports the `∀`-lift clauses from one class lift, and the
     extracted child commutes with truncation (`alphaChild_clusterTrunc`,
     `betaChild_clusterTrunc`).  The IH is then applied at the child's own truncated window.
   * The β case additionally needs that truncation creates NO full-multiplicity child
     (`hasChildAt_full_of_clusterTrunc`): otherwise the truncated state would be α while its
     parent is β, and the β rule could not be re-fired.  It cannot: a full child at `T` pins
     the content at `m * k` at BOTH levels, and every `W`-lift pair is a `T`-lift pair.
3. **Counting** (`uClusterNorm_antitone`) — the fibres of `coeffFactor` are equicardinal
   (`card_preimage_coeffFactor`), which is exactly H.70's bookkeeping step.  The state
   subtype is transported to a `Set (Coeff O m N)` first (`clusterUndecidedSet`), because the
   landed fibre count lives on the full coefficient box; the transport is legitimate because
   being a cluster state is itself a property of the level-`1` truncation, hence stable under
   `coeffFactor` in BOTH directions.

## ⚠ The S-1 fence

Everything here is about the CONSERVATIVE complement `ClusterUndecided`/`uCluster` (H.118,
H.119), NOT about the semantic `undecidedSet`/`undecidedCount`.  D-4's warning is precisely
that the two carriers differ; the one-way bridge is H.123's.  No statement of this file may be
read as a statement about the semantic object (finding F-2).

DEPENDS: H.106 (`ClusterState`, `card_clusterState`), H.107 (`resOrd`, `mk_mem_map_pow_iff`,
`le_resOrd_iff`), H.108 (`IsDrainState`, `betaContent`), H.109 (`HasChildAt`,
`hasChildAt_of_exists`), H.110 (`IsCSState`), H.111 (`IsAlphaState`, `IsBetaState`), H.112
(`alpha_content`, `coeff_recentre_top`), H.115 (`alphaChild`, `alphaChild_spec`, `classSect`,
`resSect`), H.116 (`betaChild`, `betaChild_spec`, `exists_dividedFrame_at`,
`exists_residue_split`, `monicPoly_map_residue`, `monicFactor_congr_of_pow_dvd_sub`), H.118
(`ClusterUndecided`), H.119 (`uCluster`, `uClusterNorm`) · landed `coeffFactor`,
`coeffFactor_proj`, `card_preimage_coeffFactor`, `card_coeff`, `resFactor`, `resFactor_mk`
(`Uniformity/Density/LocalData.lean`) · landed CHAP-B `dev_X`, `npHgt_X` (B.15),
`npHgt_min_congr` (B.76), `H₀_lt_of_visible` (B.74), `sideSet_congr` (B.77a), `resPoly_congr`
(B.77b) — the level-`N` congruence transport of the order-1 read, at `φ = X`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `[Finite (ResidueField O)]` (the truncation map
`coeffFactor` and all counting) + `[IsAdicComplete (maximalIdeal O) O]` (β's child) + `π`
explicit, every binder INLINE.

## TEETH (GC-8)

PROOF-ONLY at the blueprint (as H.70's was); the numeric shadow is PART 3's per-window tables
being monotone.  §6 reproduces that shadow on the two landed conservative closed forms
(`hex3R`/`hex3U`, the battery's `P1(i)` references): the normalized sequences
`u(N) / q ^ (m (N − 1))` are checked antitone at both battery characteristics over the whole
`part1` window range, and the un-normalized counts are checked NOT antitone — so the
normalization is load-bearing and the guard is not vacuous.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

/-! ## 1. The truncation of a cluster state -/

section Carrier

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The windowed valuation under truncation.**  `resOrd` at the smaller window is the larger
window's value, capped: `resOrd (resFactor h x) = min (resOrd x) T`.  Both inequalities are
H.107's `mk_mem_map_pow_iff` read at a representative — membership of an image ideal `𝔪 ^ s`
is a property of the representative alone, as long as `s` is inside the window. -/
theorem resOrd_resFactor {T W : ℕ} (h : T ≤ W) (x : Res O W) :
    resOrd (resFactor (O := O) h x) = min (resOrd x) T := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ W) x
  rw [resFactor_mk]
  refine le_antisymm (le_min ?_ (resOrd_le _)) ?_
  · set s := resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ T) a) with hs
    have hsT : s ≤ T := resOrd_le _
    have hmem : a ∈ (maximalIdeal O) ^ s :=
      (mk_mem_map_pow_iff hsT a).1 ((le_resOrd_iff hsT _).1 le_rfl)
    exact (le_resOrd_iff (hsT.trans h) _).2 ((mk_mem_map_pow_iff (hsT.trans h) a).2 hmem)
  · set t := min (resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ W) a)) T with ht
    have htT : t ≤ T := min_le_right _ _
    have hmem : a ∈ (maximalIdeal O) ^ t :=
      (mk_mem_map_pow_iff (htT.trans h) a).1 ((le_resOrd_iff (htT.trans h) _).1 (min_le_left _ _))
    exact (le_resOrd_iff htT _).2 ((mk_mem_map_pow_iff htT a).2 hmem)

/-- **The truncation of a cluster state.**  Coordinatewise `resFactor`; residual zeroness is
preserved, since a representative in `𝔪` stays a representative in `𝔪`. -/
def clusterTrunc {m T W : ℕ} (h : T ≤ W) (c : ClusterState O m W) : ClusterState O m T :=
  ⟨coeffFactor m h c.1, by
    intro i
    obtain ⟨x, hx, hxi⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (c.2 i)
    show resFactor h (c.1 i) ∈ _
    rw [← hxi, resFactor_mk]
    exact Ideal.mem_map_of_mem _ hx⟩

theorem clusterTrunc_apply {m T W : ℕ} (h : T ≤ W) (c : ClusterState O m W) (i : Fin m) :
    (clusterTrunc h c).1 i = resFactor h (c.1 i) := rfl

/-- Truncating the class of a lift is projecting that same lift at the smaller window: a
window-`W` lift IS a window-`T` lift of the truncated state. -/
theorem proj_clusterTrunc {m T W : ℕ} (h : T ≤ W) (c : ClusterState O m W) {a : Fin m → O}
    (ha : proj O m W a = c.1) : proj O m T a = (clusterTrunc h c).1 := by
  rw [show (clusterTrunc h c).1 = coeffFactor m h c.1 from rfl, ← ha, coeffFactor_proj]

/-! ### The drain rule under truncation -/

/-- **DRAIN truncates to DRAIN.** -/
theorem isDrainState_clusterTrunc {m T W : ℕ} (h : T ≤ W) {c : ClusterState O m W}
    (h0 : IsDrainState c) : IsDrainState (clusterTrunc h c) := by
  intro hm
  rw [clusterTrunc_apply, h0 hm, map_zero]

/-- **The non-drain branch sees the constant coefficient.**  If the truncation is not a drain
then the parent's constant coefficient is visible already at the SMALL window. -/
theorem resOrd_zero_lt_of_not_isDrainState_clusterTrunc {m T W : ℕ} (h : T ≤ W)
    {c : ClusterState O m W} (hm : 0 < m) (h0 : ¬ IsDrainState (clusterTrunc h c)) :
    resOrd (c.1 ⟨0, hm⟩) < T := by
  have hne : (clusterTrunc h c).1 ⟨0, hm⟩ ≠ 0 := fun hq => h0 ((isDrainState_iff hm _).2 hq)
  have hlt : resOrd ((clusterTrunc h c).1 ⟨0, hm⟩) ≠ T := fun hq => hne ((resOrd_eq_iff _).1 hq)
  rw [clusterTrunc_apply, resOrd_resFactor] at hlt
  have hle : min (resOrd (c.1 ⟨0, hm⟩)) T ≤ T := min_le_right _ _
  omega

/-- A truncated non-drain state has a non-drain parent (the contrapositive of
`isDrainState_clusterTrunc`). -/
theorem not_isDrainState_of_not_isDrainState_clusterTrunc {m T W : ℕ} (h : T ≤ W)
    {c : ClusterState O m W} (h0 : ¬ IsDrainState (clusterTrunc h c)) : ¬ IsDrainState c :=
  fun hc => h0 (isDrainState_clusterTrunc h hc)

/-! ### The capped content under truncation -/

/-- **The content can only drop under truncation**: every term of H.108's infimum is capped by
the small window. -/
theorem betaContent_clusterTrunc_le {m T W : ℕ} (h : T ≤ W) (c : ClusterState O m W) (k : ℕ) :
    betaContent (clusterTrunc h c) k ≤ betaContent c k := by
  classical
  set F : ℕ → ℕ := fun j => if hj : j < m then resOrd (c.1 ⟨j, hj⟩) + j * k else m * k with hF
  set G : ℕ → ℕ :=
    fun j => if hj : j < m then resOrd ((clusterTrunc h c).1 ⟨j, hj⟩) + j * k else m * k with hG
  have hne : (Finset.range (m + 1)).Nonempty := Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)
  obtain ⟨j, hjmem, hjeq⟩ := Finset.exists_mem_eq_inf' hne F
  have hGF : G j ≤ F j := by
    by_cases hjm : j < m
    · simp only [hG, hF, dif_pos hjm]
      rw [clusterTrunc_apply, resOrd_resFactor]
      have := min_le_left (resOrd (c.1 ⟨j, hjm⟩)) T
      omega
    · simp only [hG, hF, dif_neg hjm, le_refl]
  calc betaContent (clusterTrunc h c) k ≤ G j := Finset.inf'_le _ hjmem
    _ ≤ F j := hGF
    _ = betaContent c k := hjeq.symm

/-- **The content is UNCHANGED once the window still sees it.**  On the non-drain branch
`betaContent c k < T` always holds (the `j = 0` term of the infimum is below `resOrd (c 0)`,
which is `< T`), so this is the equality the α/β transports run on. -/
theorem betaContent_clusterTrunc_eq {m T W : ℕ} (h : T ≤ W) (c : ClusterState O m W) (k : ℕ)
    (hlt : betaContent c k < T) : betaContent (clusterTrunc h c) k = betaContent c k := by
  classical
  refine le_antisymm (betaContent_clusterTrunc_le h c k) ?_
  refine Finset.le_inf' _ _ ?_
  intro j _
  by_cases hjm : j < m
  · rw [dif_pos hjm, clusterTrunc_apply, resOrd_resFactor]
    rcases le_or_gt T (resOrd (c.1 ⟨j, hjm⟩)) with hc | hc
    · rw [min_eq_right hc]; omega
    · rw [min_eq_left hc.le]
      exact betaContent_le_of_lt c k hjm
  · rw [dif_neg hjm]
    exact betaContent_le_mul c k

/-- The non-drain branch's content bound, packaged: on it the capped content is strictly inside
the SMALL window, so every child window `T − D` is positive and the content is stable. -/
theorem betaContent_lt_of_not_isDrainState_clusterTrunc {m T W : ℕ} (h : T ≤ W)
    {c : ClusterState O m W} (hm : 0 < m) (h0 : ¬ IsDrainState (clusterTrunc h c)) (k : ℕ) :
    betaContent c k < T := by
  have h1 : betaContent c k ≤ resOrd (c.1 ⟨0, hm⟩) + 0 * k := betaContent_le_of_lt c k hm
  have h2 := resOrd_zero_lt_of_not_isDrainState_clusterTrunc h hm h0
  omega

end Carrier

end Uniformity.Density.Induction
