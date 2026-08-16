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

/-! ## 2. The CS rule under truncation

The one direction that needs the polygon to be a function of the CLASS.  `IsCSState` is a
`∀`-lift statement, and the small window has MORE lifts than the large one, so the transport
runs through chapter B's landed level-`N` congruence: at the key `φ = X` a non-drain state's
whole polygon is strictly below its own window (`Visible`), and then `sideSet_congr` (B.77a),
`H₀_lt_of_visible` (B.74), `npHgt_min_congr` (B.76) and `resPoly_congr` (B.77b) carry the CS
witness from the pinned `W`-lift to an arbitrary `T`-lift. -/

section CS

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

omit [Finite (ResidueField O)] in
/-- **The visible-polygon principle, in B.75's digit form.**  A non-drain state's constant
coefficient is a digit inside the window, so the order-1 read of every lift is `Visible` at that
window — which is the licence chapter B's congruence lemmas ask for. -/
theorem visible_of_not_isDrainState {π : O} (hπ : Irreducible π) {m T : ℕ} (hm : 0 < m)
    {c : ClusterState O m T} (h0 : ¬ IsDrainState c) {a : Fin m → O}
    (ha : proj O m T a = c.1) : Visible π X (monicPoly a) T := by
  have hmk : c.1 ⟨0, hm⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ T) (a ⟨0, hm⟩) :=
    (congrFun ha ⟨0, hm⟩).symm
  refine ⟨0, ?_⟩
  rw [dev_X, Polynomial.coeff_C_zero, monicPoly_coeff_lt a hm]
  intro hdvd
  have hge := (resOrd_ge_iff hπ (le_refl T) (a ⟨0, hm⟩)).2 hdvd
  rw [← hmk] at hge
  have heq : resOrd (c.1 ⟨0, hm⟩) = T := le_antisymm (resOrd_le _) hge
  exact h0 ((isDrainState_iff hm c).2 ((resOrd_eq_iff _).1 heq))

/-- **CS truncates to CS on the non-drain branch.**  DECISION D-H17.1's pessimistic exit is
stable under shrinking the window, as long as the window still sees the constant coefficient
(if it does not, the truncation is a DRAIN and exits undecided for that reason instead). -/
theorem isCSState_clusterTrunc {π : O} (hπ : Irreducible π) {m T W : ℕ} (h : T ≤ W) (hm : 0 < m)
    {c : ClusterState O m W} (h0 : ¬ IsDrainState (clusterTrunc h c)) (hcs : IsCSState π c) :
    IsCSState π (clusterTrunc h c) := by
  refine ⟨h0, ?_⟩
  intro a' ha'
  have hmin' : ∀ (s t : Finset ℕ) (hs : s.Nonempty) (ht : t.Nonempty), s = t →
      s.min' hs = t.min' ht := by
    rintro s t hs ht rfl; rfl
  -- the pinned `W`-lift; it is a `T`-lift of the truncation
  have haW : proj O m W (classSect O m W c.1) = c.1 := proj_classSect O m W c.1
  have haT : proj O m T (classSect O m W c.1) = (clusterTrunc h c).1 := proj_clusterTrunc h c haW
  obtain ⟨u, ℓ, hne, H₀, hℓ, hcop, hH₀, ψ, hψ, hψdeg, hψdvd⟩ := hcs.2 _ haW
  -- the two lifts agree at level `T`
  have hff' : ∀ i, π ^ T ∣ (monicPoly (classSect O m W c.1) - monicPoly a').coeff i := by
    intro i
    have hx := pow_dvd_coeff_comp_sub hπ (haT.trans ha'.symm) X i
    rwa [Polynomial.comp_X, Polynomial.comp_X] at hx
  have hdegX : (0 : ℕ) < (X : Polynomial O).natDegree := by simp
  have hvis : Visible π X (monicPoly (classSect O m W c.1)) T :=
    visible_of_not_isDrainState hπ hm h0 haT
  have hdeg : (monicPoly a').natDegree = (monicPoly (classSect O m W c.1)).natDegree := by
    rw [monicPoly_natDegree, monicPoly_natDegree]
  have hset : sideSet X (monicPoly a') u ℓ = sideSet X (monicPoly (classSect O m W c.1)) u ℓ :=
    sideSet_congr hπ monic_X hdegX hff' hdeg hvis u ℓ
  have hne' : (sideSet X (monicPoly a') u ℓ).Nonempty := by rw [hset]; exact hne
  have hH₀T : H₀ < T := H₀_lt_of_visible hπ hvis hℓ hne hH₀
  -- the pinned abscissa and its height transport
  have hminEq : sideMin X (monicPoly a') u ℓ hne'
      = sideMin X (monicPoly (classSect O m W c.1)) u ℓ hne := hmin' _ _ _ _ hset
  have hnp : npHgt X (monicPoly a') (sideMin X (monicPoly a') u ℓ hne') = (H₀ : ℕ∞) := by
    rw [hminEq]
    have hmc := npHgt_min_congr hπ monic_X hdegX hff'
      (sideMin X (monicPoly (classSect O m W c.1)) u ℓ hne)
    rw [hH₀] at hmc
    have hlt : ((H₀ : ℕ) : ℕ∞) < ((T : ℕ) : ℕ∞) := by exact_mod_cast hH₀T
    rw [min_eq_left hlt.le] at hmc
    rcases min_cases (npHgt X (monicPoly a')
      (sideMin X (monicPoly (classSect O m W c.1)) u ℓ hne)) ((T : ℕ) : ℕ∞) with
      ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hmc; exact hmc.symm
    · rw [he] at hmc; exact absurd hmc (by exact_mod_cast hlt.ne)
  refine ⟨u, ℓ, hne', H₀, hℓ, hcop, hnp, ψ, hψ, hψdeg, ?_⟩
  have hres : resPoly π X (monicPoly a') u ℓ hne' H₀
      = resPoly π X (monicPoly (classSect O m W c.1)) u ℓ hne H₀ :=
    resPoly_congr hπ monic_X hdegX hff' hdeg hvis hne hH₀T
  rw [hres]
  exact hψdvd

/-- **The easy direction.**  CS at the SMALL window forces CS at the large one: every `W`-lift
is a `T`-lift, so the `∀`-lift clause at `T` already covers the `W`-lift clause.  This is what
keeps `¬ IsCSState` — the second conjunct of α, β and DEC — alive under truncation. -/
theorem isCSState_of_isCSState_clusterTrunc {π : O} {m T W : ℕ} (h : T ≤ W)
    {c : ClusterState O m W} (h0 : ¬ IsDrainState c)
    (hcs : IsCSState π (clusterTrunc h c)) : IsCSState π c := by
  refine ⟨h0, ?_⟩
  intro a ha
  exact hcs.2 a (proj_clusterTrunc h c ha)

end CS

/-! ## 3. The child events under truncation

On the non-drain branch the capped content is unchanged, so the `∀`-lift clauses of H.109
transport from ONE class lift (H.109's `hasChildAt_of_exists`), in both directions.  The
backward direction is needed only at FULL multiplicity, and there the content equality is
automatic: a full child pins `D = m k` at whichever window it is read. -/

section Events

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **A child event re-fires at the smaller window** (non-drain branch): same `(μ, k, z)`, same
capped content, and the `∀`-lift clauses come from the pinned class lift. -/
theorem hasChildAt_clusterTrunc {π : O} (hπ : Irreducible π) {m T W μ k : ℕ}
    {z : ResidueField O} (h : T ≤ W) (hm : 0 < m) {c : ClusterState O m W}
    (h0 : ¬ IsDrainState (clusterTrunc h c)) (hch : HasChildAt π c μ k z) :
    HasChildAt π (clusterTrunc h c) μ k z := by
  obtain ⟨hμ, hk, hz, hall⟩ := hch
  have hT : 1 ≤ T := one_le_window_of_not_drain _ h0
  have hDeq : betaContent (clusterTrunc h c) k = betaContent c k :=
    betaContent_clusterTrunc_eq h c k (betaContent_lt_of_not_isDrainState_clusterTrunc h hm h0 k)
  have haW : proj O m W (classSect O m W c.1) = c.1 := proj_classSect O m W c.1
  have haT : proj O m T (classSect O m W c.1) = (clusterTrunc h c).1 := proj_clusterTrunc h c haW
  obtain ⟨c1, c2, c3⟩ := hall (classSect O m W c.1) (resSect O z) haW (residue_resSect O z)
  refine hasChildAt_of_exists hπ hT h0 hμ hk hz (classSect O m W c.1) (resSect O z) haT
    (residue_resSect O z) ?_ ?_ ?_ <;> rw [hDeq]
  · exact c1
  · exact c2
  · exact c3

/-- **Truncation creates no FULL-multiplicity child.**  A full child at the small window forces
the capped content to be `m * k` there, hence also at the large window (the content only drops
under truncation, and `m * k` is its monic-top bound), and then every `W`-lift pair is covered
by the small window's own `∀`-lift clause.  This is what keeps a β state β under truncation. -/
theorem hasChildAt_full_of_clusterTrunc {π : O} (hπ : Irreducible π) {m T W k : ℕ}
    {z : ResidueField O} (h : T ≤ W) {c : ClusterState O m W}
    (h0 : ¬ IsDrainState (clusterTrunc h c)) (hch : HasChildAt π (clusterTrunc h c) m k z) :
    HasChildAt π c m k z := by
  obtain ⟨hμ, hk, hz, hall⟩ := hch
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have h0W : ¬ IsDrainState c := not_isDrainState_of_not_isDrainState_clusterTrunc h h0
  have hW : 1 ≤ W := one_le_window_of_not_drain _ h0W
  have haW : proj O m W (classSect O m W c.1) = c.1 := proj_classSect O m W c.1
  have haT : proj O m T (classSect O m W c.1) = (clusterTrunc h c).1 := proj_clusterTrunc h c haW
  obtain ⟨c1, c2, c3⟩ := hall (classSect O m W c.1) (resSect O z) haT (residue_resSect O z)
  -- the content is `m * k` at BOTH windows
  have hge : m * k ≤ betaContent (clusterTrunc h c) k := by
    by_contra hlt
    refine c3 ?_
    rw [coeff_recentre_top hπ0 (classSect O m W c.1) k (resSect O z), ← pow_mul,
      Nat.mul_comm k m]
    exact pow_dvd_pow π (by omega)
  have hle := betaContent_clusterTrunc_le h c k
  have hmul := betaContent_le_mul c k
  have hDeq : betaContent (clusterTrunc h c) k = betaContent c k := by omega
  refine hasChildAt_of_exists hπ hW h0W hμ hk hz (classSect O m W c.1) (resSect O z) haW
    (residue_resSect O z) ?_ ?_ ?_ <;> rw [← hDeq]
  · exact c1
  · exact c2
  · exact c3

/-- **α re-fires at the smaller window** (non-drain branch). -/
theorem isAlphaState_clusterTrunc {π : O} (hπ : Irreducible π) {m T W k : ℕ}
    {z : ResidueField O} (h : T ≤ W) (hm : 0 < m) {c : ClusterState O m W}
    (h0 : ¬ IsDrainState (clusterTrunc h c)) (hα : IsAlphaState π c k z) :
    IsAlphaState π (clusterTrunc h c) k z :=
  ⟨h0, fun hcs => hα.2.1 (isCSState_of_isCSState_clusterTrunc h hα.1 hcs),
    hasChildAt_clusterTrunc hπ h hm h0 hα.2.2⟩

/-- **β re-fires at the smaller window** (non-drain branch): the witnessed child transports
forward, and no full-multiplicity child appears (`hasChildAt_full_of_clusterTrunc`). -/
theorem isBetaState_clusterTrunc {π : O} (hπ : Irreducible π) {m T W μ k : ℕ}
    {z : ResidueField O} (h : T ≤ W) (hm : 0 < m) {c : ClusterState O m W}
    (h0 : ¬ IsDrainState (clusterTrunc h c)) (hβ : IsBetaState π c)
    (hch : HasChildAt π c μ k z) : IsBetaState π (clusterTrunc h c) := by
  refine ⟨h0, fun hcs => hβ.2.1 (isCSState_of_isCSState_clusterTrunc h hβ.1 hcs),
    ⟨μ, k, z, hasChildAt_clusterTrunc hπ h hm h0 hch⟩, ?_⟩
  rintro ⟨k', z', hfull⟩
  exact hβ.2.2.2 ⟨k', z', hasChildAt_full_of_clusterTrunc hπ h h0 hfull⟩

/-! ### The extracted children commute with truncation -/

/-- **The α child commutes with truncation.**  Both children are the monic development of the
SAME divided frame — the α extraction is a division formula, so the two digit vectors are
equal on the nose and only their windows differ. -/
theorem alphaChild_clusterTrunc {π : O} (hπ : Irreducible π) {m T W k : ℕ}
    {z : ResidueField O} (h : T ≤ W) (hm : 2 ≤ m) {c : ClusterState O m W}
    (h0 : ¬ IsDrainState (clusterTrunc h c)) (hα : IsAlphaState π c k z)
    (hα' : IsAlphaState π (clusterTrunc h c) k z) (hMM : T - m * k ≤ W - m * k) :
    alphaChild π (clusterTrunc h c) hα' = clusterTrunc hMM (alphaChild π c hα) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hT : 1 ≤ T := one_le_window_of_not_drain _ h0
  have hW : 1 ≤ W := one_le_window_of_not_drain _ hα.1
  have haW : proj O m W (classSect O m W c.1) = c.1 := proj_classSect O m W c.1
  have haT : proj O m T (classSect O m W c.1) = (clusterTrunc h c).1 := proj_clusterTrunc h c haW
  obtain ⟨bW, -, hbWeq, hbWproj⟩ := alphaChild_spec hπ hm hW c hα _ haW
  obtain ⟨bT, -, hbTeq, hbTproj⟩ :=
    alphaChild_spec hπ hm hT (clusterTrunc h c) hα' _ haT
  -- the two monic developments factor the SAME frame, so they are equal
  have hCne : (Polynomial.C (π ^ (m * k)) : Polynomial O) ≠ 0 :=
    Polynomial.C_ne_zero.2 (pow_ne_zero _ hπ0)
  have hmono : monicPoly bW = monicPoly bT := mul_left_cancel₀ hCne (hbWeq.symm.trans hbTeq)
  have hb : bW = bT := by
    refine funext fun i => ?_
    rw [← monicPoly_coeff_lt bW i.isLt, hmono, monicPoly_coeff_lt bT i.isLt]
  refine Subtype.ext ?_
  rw [← hbTproj, ← hb,
    show (clusterTrunc hMM (alphaChild π c hα)).1
      = coeffFactor m hMM (alphaChild π c hα).1 from rfl, ← hbWproj, coeffFactor_proj]

/-- **The β child commutes with truncation.**  Both children are monic degree-`μ` left factors
of the SAME divided frame at the SAME pinned centre, so H.116's fixed-centre uniqueness
(`monicFactor_congr_of_pow_dvd_sub`) identifies them at the small child window. -/
theorem betaChild_clusterTrunc {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m T W μ k : ℕ} {z : ResidueField O} (h : T ≤ W) (hm : 2 ≤ m) {c : ClusterState O m W}
    (h0 : ¬ IsDrainState (clusterTrunc h c)) (hch : HasChildAt π c μ k z)
    (hch' : HasChildAt π (clusterTrunc h c) μ k z)
    (hMM : T - betaContent (clusterTrunc h c) k ≤ W - betaContent c k) :
    betaChild π (clusterTrunc h c) hch' (T - betaContent (clusterTrunc h c) k)
      = clusterTrunc hMM (betaChild π c hch (W - betaContent c k)) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hm0 : 0 < m := by omega
  have h0W : ¬ IsDrainState c := not_isDrainState_of_not_isDrainState_clusterTrunc h h0
  have hT : 1 ≤ T := one_le_window_of_not_drain _ h0
  have hW : 1 ≤ W := one_le_window_of_not_drain _ h0W
  have hDeq : betaContent (clusterTrunc h c) k = betaContent c k :=
    betaContent_clusterTrunc_eq h c k (betaContent_lt_of_not_isDrainState_clusterTrunc h hm0 h0 k)
  have haW : proj O m W (classSect O m W c.1) = c.1 := proj_classSect O m W c.1
  have haT : proj O m T (classSect O m W c.1) = (clusterTrunc h c).1 := proj_clusterTrunc h c haW
  obtain ⟨bW, HW, hbWmem, hbWeq, hbWproj⟩ := betaChild_spec hπ hm hW c hch h0W _ haW
  obtain ⟨bT, HT, hbTmem, hbTeq, hbTproj⟩ :=
    betaChild_spec hπ hm hT (clusterTrunc h c) hch' h0 _ haT
  rw [hDeq] at hbTeq
  -- the two factorizations are of the same divided frame
  have hCne : (Polynomial.C (π ^ betaContent c k) : Polynomial O) ≠ 0 :=
    Polynomial.C_ne_zero.2 (pow_ne_zero _ hπ0)
  have hprod : monicPoly bW * HW = monicPoly bT * HT :=
    mul_left_cancel₀ hCne (hbWeq.symm.trans hbTeq)
  -- the `W`-cofactor is residually coprime to `X ^ μ` (H.116's residue split, re-read)
  have hcop : IsCoprime (X ^ μ : Polynomial (ResidueField O)) (HW.map (residue O)) := by
    obtain ⟨G, hGeq, hGlt, hGtop⟩ :=
      exists_dividedFrame_at hπ c hch (classSect O m W c.1) haW
    obtain ⟨v, hv, -, hvcop⟩ := exists_residue_split hGlt hGtop
    have hGprod : G = monicPoly bW * HW := mul_left_cancel₀ hCne (hGeq.symm.trans hbWeq)
    have hXne : (X : Polynomial (ResidueField O)) ^ μ ≠ 0 := pow_ne_zero _ X_ne_zero
    have hmapv : (X : Polynomial (ResidueField O)) ^ μ * (HW.map (residue O))
        = (X : Polynomial (ResidueField O)) ^ μ * v := by
      rw [← hv, hGprod, Polynomial.map_mul, monicPoly_map_residue hbWmem]
    rw [mul_left_cancel₀ hXne hmapv]
    exact hvcop
  -- fixed-centre uniqueness at the SMALL child window
  have hs : ∀ j, π ^ (T - betaContent c k) ∣
      (monicPoly bW * HW - monicPoly bT * HT).coeff j := by
    intro j
    rw [hprod, sub_self, Polynomial.coeff_zero]
    exact dvd_zero _
  have huniq := monicFactor_congr_of_pow_dvd_sub hπ (monicPoly_monic bW) (monicPoly_monic bT)
    (monicPoly_natDegree bW) (monicPoly_natDegree bT) (monicPoly_map_residue hbTmem) hcop hs
  refine Subtype.ext ?_
  rw [← hbTproj,
    show (clusterTrunc hMM (betaChild π c hch (W - betaContent c k))).1
      = coeffFactor μ hMM (betaChild π c hch (W - betaContent c k)).1 from rfl,
    ← hbWproj, coeffFactor_proj, hDeq]
  refine funext fun i => ?_
  refine Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ _ _).2 ?_)
  have h3 := huniq (i : ℕ)
  rw [Polynomial.coeff_sub, monicPoly_coeff_lt bW i.isLt, monicPoly_coeff_lt bT i.isLt] at h3
  exact (dvd_sub_comm).1 (by simpa using h3)

end Events

end Uniformity.Density.Induction
