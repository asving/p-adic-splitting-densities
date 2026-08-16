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
   landed fibre count lives on the full coefficient box; `card_clusterUndecidedSet` proves the
   two presentations have the same count, and only the CONTAINMENT
   (`clusterUndecidedSet_subset`) is consumed after that, so no claim about the shape of the
   full fibre is needed.

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

/-! ## 4. The conservative verdict pulls back along truncation

The theorem of the node.  Induction on the H.118 derivation; at each rule the truncated state
is first tested for DRAIN (the "coarsens toward drain" branch — it fires exactly when the small
window no longer sees the constant coefficient, and closes the case at depth 0), and on the
non-drain branch the SAME rule re-fires at the small window. -/

section Pullback

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The conservative reader with fewer digits decides no more.**  A window-`W` conservatively
undecided state truncates to a window-`T` conservatively undecided state, for every
`1 ≤ T ≤ W`.  This is the mathematical content of cluster-level C2D (debt D-4); the counting
that turns it into the antitone statement is §5. -/
theorem clusterUndecided_clusterTrunc {π : O} (hπ : Irreducible π) :
    ∀ {m W : ℕ} {c : ClusterState O m W}, ClusterUndecided O π m W c → 2 ≤ m →
      ∀ {T : ℕ} (h : T ≤ W), 1 ≤ T → ClusterUndecided O π m T (clusterTrunc h c) := by
  intro m W c hu
  induction hu with
  | drain c hd =>
      intro _ _ h _
      exact ClusterUndecided.drain _ (isDrainState_clusterTrunc h hd)
  | cs c hcs =>
      intro hm T h hT
      by_cases h0 : IsDrainState (clusterTrunc h c)
      · exact ClusterUndecided.drain _ h0
      · exact ClusterUndecided.cs _ (isCSState_clusterTrunc hπ h (by omega) h0 hcs)
  | @alpha m N k z c hα hrec ih =>
      intro hm T h hT
      by_cases h0 : IsDrainState (clusterTrunc h c)
      · exact ClusterUndecided.drain _ h0
      · have hm0 : 0 < m := by omega
        have hN : 1 ≤ N := one_le_window_of_not_drain _ hα.1
        obtain ⟨hD, hk, hwin⟩ := alpha_content hπ hm hN hα
        have hDlt : m * k < T := by
          have hb := betaContent_lt_of_not_isDrainState_clusterTrunc h hm0 h0 k
          omega
        have hMM : T - m * k ≤ N - m * k := by omega
        have hα' : IsAlphaState π (clusterTrunc h c) k z :=
          isAlphaState_clusterTrunc hπ h hm0 h0 hα
        refine ClusterUndecided.alpha _ hα' ?_
        rw [alphaChild_clusterTrunc hπ h hm h0 hα hα' hMM]
        exact ih hm hMM (by omega)
  | @beta m N μ k z c hβ hch hrec ih =>
      intro hm T h hT
      by_cases h0 : IsDrainState (clusterTrunc h c)
      · exact ClusterUndecided.drain _ h0
      · have hm0 : 0 < m := by omega
        have hDlt : betaContent c k < T :=
          betaContent_lt_of_not_isDrainState_clusterTrunc h hm0 h0 k
        have hDeq : betaContent (clusterTrunc h c) k = betaContent c k :=
          betaContent_clusterTrunc_eq h c k hDlt
        have hMM : T - betaContent (clusterTrunc h c) k ≤ N - betaContent c k := by omega
        have hβ' : IsBetaState π (clusterTrunc h c) :=
          isBetaState_clusterTrunc hπ h hm0 h0 hβ hch
        have hch' : HasChildAt π (clusterTrunc h c) μ k z :=
          hasChildAt_clusterTrunc hπ h hm0 h0 hch
        refine ClusterUndecided.beta _ hβ' hch' ?_
        rw [betaChild_clusterTrunc hπ h hm h0 hch hch' hMM]
        exact ih hch.1 hMM (by omega)

end Pullback

/-! ## 5. The count: `GENIND-C2D` on the cluster carrier

H.70's bookkeeping step, on this node's carrier.  The undecided states are first presented as a
SUBSET of the coefficient box `Coeff O m N`, because the landed equicardinality of the
truncation fibres (`card_preimage_coeffFactor`) lives there; this costs nothing, because being
a cluster state is a property of the level-`1` truncation and is therefore preserved and
reflected by `coeffFactor`. -/

section Counting

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- The conservative-undecided locus, as a subset of the coefficient box. -/
def clusterUndecidedSet (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) (m N : ℕ) : Set (Coeff O m N) :=
  {x | ∃ hx : ∀ i, x i ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)),
    ClusterUndecided O π m N ⟨x, hx⟩}

omit [Finite (ResidueField O)] in
/-- The box-level presentation counts what H.119's subtype counts. -/
theorem card_clusterUndecidedSet (π : O) (m N : ℕ) :
    Nat.card (clusterUndecidedSet O π m N) = uCluster O π m N :=
  Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm

/-- **The containment** (`clusterUndecided_clusterTrunc`, read on the box). -/
theorem clusterUndecidedSet_subset {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m)
    {T W : ℕ} (h : T ≤ W) (hT : 1 ≤ T) :
    clusterUndecidedSet O π m W ⊆ (coeffFactor m h) ⁻¹' clusterUndecidedSet O π m T := by
  rintro x ⟨hx, hu⟩
  exact ⟨(clusterTrunc h ⟨x, hx⟩).2, clusterUndecided_clusterTrunc hπ hu hm h hT⟩

end Counting

/-! ## 5b. The signed statement -/

/-- **H.120 — cluster-level C2D (debt D-4), `GENIND-C2D` on the `ClusterState` carrier.**  The
NORMALIZED conservative complement is antitone in the window.

⚠ S-1: this is the CONSERVATIVE complement of H.118/H.119, not the semantic `undecidedSet`;
D-4's warning that the carriers differ is why H.70's full-space monotonicity is not consumed
here (only its argument template is).

The binder list is the frozen stub's, INLINE (`leanspec/Leanspec/ChapH.lean`, **H.120**). -/
theorem uClusterNorm_antitone {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) (m : ℕ) (hm : 2 ≤ m) :
    ∀ T W, 1 ≤ T → T ≤ W → uClusterNorm O π m W ≤ uClusterNorm O π m T := by
  intro T W hT hTW
  have hW : 1 ≤ W := le_trans hT hTW
  -- the containment, counted
  have hcard : uCluster O π m W
      ≤ Nat.card ((coeffFactor m hTW) ⁻¹' clusterUndecidedSet O π m T) := by
    rw [← card_clusterUndecidedSet, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (clusterUndecidedSet_subset hπ hm hTW hT) (Set.toFinite _)
  -- the fibres are equicardinal (the landed refinement count)
  have hkey := card_preimage_coeffFactor (O := O) m hTW (clusterUndecidedSet O π m T)
  rw [card_coeff, card_coeff, card_clusterUndecidedSet] at hkey
  have hnat : uCluster O π m W * residueCard O ^ (m * T)
      ≤ uCluster O π m T * residueCard O ^ (m * W) :=
    calc uCluster O π m W * residueCard O ^ (m * T)
        ≤ Nat.card ((coeffFactor m hTW) ⁻¹' clusterUndecidedSet O π m T)
            * residueCard O ^ (m * T) := Nat.mul_le_mul_right _ hcard
      _ = uCluster O π m T * residueCard O ^ (m * W) := hkey
  -- strip one census factor `q ^ m` from each side
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, W = w + 1 := ⟨W - 1, by omega⟩
  have hmT : m * (t + 1 - 1) + m = m * (t + 1) := by simp [Nat.mul_succ]
  have hmW : m * (w + 1 - 1) + m = m * (w + 1) := by simp [Nat.mul_succ]
  have hcancel : uCluster O π m (w + 1) * residueCard O ^ (m * (t + 1 - 1))
      ≤ uCluster O π m (t + 1) * residueCard O ^ (m * (w + 1 - 1)) := by
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (residueCard_pos O) m)
    calc uCluster O π m (w + 1) * residueCard O ^ (m * (t + 1 - 1)) * residueCard O ^ m
        = uCluster O π m (w + 1) * residueCard O ^ (m * (t + 1)) := by
          rw [mul_assoc, ← pow_add, hmT]
      _ ≤ uCluster O π m (t + 1) * residueCard O ^ (m * (w + 1)) := hnat
      _ = uCluster O π m (t + 1) * residueCard O ^ (m * (w + 1 - 1)) * residueCard O ^ m := by
          rw [mul_assoc, ← pow_add, hmW]
  have hq : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  rw [uClusterNorm, uClusterNorm, div_le_div_iff₀ (pow_pos hq _) (pow_pos hq _)]
  exact_mod_cast hcancel

end Uniformity.Density.Induction

/-! ## 6. TEETH — the numeric shadow: PART 3's per-window tables are monotone

The node is PROOF-ONLY at the blueprint, as H.70's was; what the battery shows is that the
per-window tables are monotone AFTER normalization.  `hexR`/`hexU` are
`verification/openmath/OM2_genindb_battery.py`'s `hex3R_ref`/`hex3U_ref` transcribed verbatim
(the `P1(i)` reference implementations of ChapG's landed `hex3R` at `m = 2` and `hex3U` at
`m = 3`) — the same transcription H.119 §4.2 carries, repeated here so a drift in either copy
breaks a build.

`normLe q m u T W` is the theorem's conclusion cleared of denominators, exactly as the Lean
proof clears it: `û(W) ≤ û(T)` is `u(W) · q ^ (m (T−1)) ≤ u(T) · q ^ (m (W−1))`.  The guards
run it over the battery's whole `part1` window range at both battery characteristics.

**The normalization is load-bearing, and the guard is not vacuous**: the un-normalized counts
are checked NOT antitone (they grow with the window), and the exercised population of
`(q, T, W)` pairs is pinned.

⚠ S-1: `hex3R`/`hex3U` are CONSERVATIVE-family closed forms; nothing here ties them to the
semantic `undecidedCount` (finding F-2). -/

section NumericGate

/-- The battery's `hex3R_ref` — ChapG `hex3R`, the `m = 2` conservative complement. -/
private def hexR (q M : ℕ) : ℕ :=
  if M = 0 then 0 else if M = 1 then 1
  else q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

/-- The battery's `hex3U_ref` — ChapG `hex3U`, the cubic per-centre conservative complement. -/
private def hexU (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ 3 * k ≤ N - 1)).map fun k =>
        (q - 1) * q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hexR q (N - 3 * k))).sum

/-- `uClusterNorm O π m W ≤ uClusterNorm O π m T`, cleared of denominators. -/
private def normLe (u : ℕ → ℕ → ℕ) (q m T W : ℕ) : Bool :=
  decide (u q W * q ^ (m * (T - 1)) ≤ u q T * q ^ (m * (W - 1)))

/-- The `(T, W)` pairs of the battery's window range: `1 ≤ T ≤ W ≤ cap`. -/
private def windowPairs (cap : ℕ) : List (ℕ × ℕ) :=
  ((List.range (cap + 1)).flatMap fun T =>
    (List.range (cap + 1)).map fun W => (T, W)).filter
    fun p => decide (1 ≤ p.1 ∧ p.1 ≤ p.2)

-- THE THEOREM's conclusion, re-run: `m = 2` on `hex3R`, both battery characteristics
#guard ([2, 3] : List ℕ).all fun q => (windowPairs 6).all fun p => normLe hexR q 2 p.1 p.2

-- and `m = 3` on `hex3U`
#guard ([2, 3] : List ℕ).all fun q => (windowPairs 6).all fun p => normLe hexU q 3 p.1 p.2

-- non-vacuity: the exercised population of `(T, W)` pairs, pinned
#guard (windowPairs 6).length == 21

-- the normalization is LOAD-BEARING: the un-normalized counts are NOT antitone
#guard !(decide (hexR 2 6 ≤ hexR 2 1))
#guard !(decide (hexU 3 4 ≤ hexU 3 1))

-- the transcription, pinned against H.119 §4.2's copy
#guard (hexR 2 6, hexR 3 5) == (64, 189)
#guard (hexU 2 4, hexU 3 4) == (72, 837)
#guard (hexR 2 1, hexU 2 1) == (1, 1)

-- the boundary is where antitonicity bites: `û(1) = 1` is the maximum of the normalized family
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 7).filter fun W => decide (1 ≤ W)).all fun W =>
    normLe hexR q 2 1 W && normLe hexU q 3 1 W

end NumericGate

/-! ## 7. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.resOrd_resFactor
#print axioms Uniformity.Density.Induction.clusterTrunc
#print axioms Uniformity.Density.Induction.clusterTrunc_apply
#print axioms Uniformity.Density.Induction.proj_clusterTrunc
#print axioms Uniformity.Density.Induction.isDrainState_clusterTrunc
#print axioms Uniformity.Density.Induction.resOrd_zero_lt_of_not_isDrainState_clusterTrunc
#print axioms Uniformity.Density.Induction.not_isDrainState_of_not_isDrainState_clusterTrunc
#print axioms Uniformity.Density.Induction.betaContent_clusterTrunc_le
#print axioms Uniformity.Density.Induction.betaContent_clusterTrunc_eq
#print axioms Uniformity.Density.Induction.betaContent_lt_of_not_isDrainState_clusterTrunc
#print axioms Uniformity.Density.Induction.visible_of_not_isDrainState
#print axioms Uniformity.Density.Induction.isCSState_clusterTrunc
#print axioms Uniformity.Density.Induction.isCSState_of_isCSState_clusterTrunc
#print axioms Uniformity.Density.Induction.hasChildAt_clusterTrunc
#print axioms Uniformity.Density.Induction.hasChildAt_full_of_clusterTrunc
#print axioms Uniformity.Density.Induction.isAlphaState_clusterTrunc
#print axioms Uniformity.Density.Induction.isBetaState_clusterTrunc
#print axioms Uniformity.Density.Induction.alphaChild_clusterTrunc
#print axioms Uniformity.Density.Induction.betaChild_clusterTrunc
#print axioms Uniformity.Density.Induction.clusterUndecided_clusterTrunc
#print axioms Uniformity.Density.Induction.clusterUndecidedSet
#print axioms Uniformity.Density.Induction.card_clusterUndecidedSet
#print axioms Uniformity.Density.Induction.clusterUndecidedSet_subset
#print axioms Uniformity.Density.Induction.uClusterNorm_antitone

end AxCheck
