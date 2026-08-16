/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H116b2

/-!
# Uniformity.ChapH.H116b1 — the multi-child peel

**Chapter H, NODE H.116b1** (`blueprint/CHAP-H_general_induction.md`, AMENDMENT A-H.7 §4).
The second sub-node of the H.116b re-split, in the DAG order A-H.7 §3 adjudicates
(**H.116b2 → H.116b1**: the degree-sum bound is a CONCLUSION of the peel induction, paid for
by the cofactor-inherits clause, whose mechanism is H.116b2's multiplicity-additivity).

* **clause (ii) `peel_cofactor_inherits`** — THE COFACTOR INHERITS THE REMAINING CHILDREN.
  After peeling the `(μ, k, z)`-child off a lift, the cofactor's class is again non-drain, its
  content at any OTHER slope is the parent's less the planted floor `μ · min (k, k')`, it
  carries the same child event at every foreign frame, and it READS the same child there at
  the parent's window.
* **clause (i) `exists_peel_finset`** — THE MULTI-CHILD PEEL.  Every monic lift of a non-drain
  state whose child set contains `L` factors EXACTLY in `O[X]` as a `Finset`-indexed product
  of planted factors at the pinned centres times a monic cofactor, and
  **`Σ_p μ_p ≤ m` is a CONCLUSION** — not a hypothesis, and not available from H.108
  (`mul_le_betaContent` + `betaContent_le_mul` give only `μ_p ≤ m` for EACH `p`, whose sum is
  the useless `|L| · m`).  The peel induction pays for it: each recursion consumes `μ_p` of
  the degree budget.

⚠ FENCE A-H.7/F1: nothing in this module builds a map between fibres.

## The window layer (§0), and why it is needed

`betaChild π c h M` is a description at an ARBITRARY window `M`, but H.116's landed
`betaChild_spec` pins it only at the GENUINE window `N − betaContent c k`.  Clause (ii) reads
the cofactor's child at the PARENT's window, which is strictly shallower than the cofactor's
own genuine window (`betaContent c' k' ≤ betaContent c k'`), and clause (i)'s induction has
the same shape.  §0 therefore lands `exists_betaChild_lift`: a single `𝔪`-valued presentation
`b` of the child, coming with the divided factorization of ONE chosen lift's frame, that
computes `betaChild π c h M` at EVERY window `M ≤ N − betaContent c k` at once.  Its engine is
H.116's `monicFactor_congr_of_pow_dvd_sub` (fixed-centre uniqueness), exactly as in
`betaChild_spec`'s own final step.

DEPENDS: H.102 (`monicFactor_congr_of_pow_dvd_sub`'s Bézout route), H.107
(`mem_maximalIdeal_pow_iff_dvd_of_irr`), H.108 (`betaContent`, `IsDrainState`,
`betaContent_le`, `betaContent_le_mul`, `isDrainState_iff`), H.109 (`HasChildAt`,
`hasChildAt_of_exists`, `pow_dvd_coeff_comp_sub`), H.115 (`resSect`, `classSect`, `recFrame`),
H.115b (`alphaParent` and its profiles), H.115c (`proj_eq_iff_pow_dvd`), H.116
(`betaChild`, `betaChild_spec`, `monicFactor_congr_of_pow_dvd_sub`, `monicPoly_map_residue`) ·
landed in `H116bR.lean`: `exists_peel`, `mul_le_betaContent`,
`pow_min_dvd_coeff_recentre_alphaParent`, `coeff_zero_recentre_alphaParent_not_dvd`,
`level_recentre_mul_alphaParent`, `pow_content_dvd_coeff_recentre`,
`not_pow_content_succ_dvd_coeff_recentre`, `betaContent_eq_of_recentre_exact` ·
landed in `H116b2.lean`: `coeff_level_mul_trailing`, `abscissa_unique`,
`residue_eq_zero_iff_dvd`, `mem_maximalIdeal_of_proj`, `monicPoly_coeff_self`,
`isCoprime_X_pow_of_coeff_zero_ne_zero` · mathlib `Finset.induction_on`,
`Finset.prod_insert`, `Polynomial.coeff_X_pow_mul`, `Polynomial.C_dvd_iff_dvd_coeff`.

**ENVIRONMENT — ENV-H17** + `[IsAdicComplete]` + `π` explicit, every binder INLINE.

## TEETH (GC-8)

`verification/openmath/OM2_h116b_replant_cert.py` check **B** (exact factorization, margin
`≥ N + 3` at every tested lift) and check **A** (per-`(L, D)`-with-`z` fibres, ONTO); the
degree-sum bound is exercised implicitly by every genre the batteries enumerate.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 0. The `betaChild` class at EVERY window at most the genuine one -/

section Witness

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Class equality truncates to a SHALLOWER window. -/
theorem proj_eq_of_window_le {π : O} (hπ : Irreducible π) {n M M' : ℕ} (hM : M ≤ M')
    {u v : Fin n → O} (h : proj O n M' u = proj O n M' v) :
    proj O n M u = proj O n M v :=
  (proj_eq_iff_pow_dvd (N := M) hπ u v).2 fun j =>
    (pow_dvd_pow π hM).trans ((proj_eq_iff_pow_dvd (N := M') hπ u v).1 h j)

/-- **The cofactor of a divided factorization has a UNIT residual constant term** as soon as
the frame's first unit sits at abscissa `μ`.  This is the residue-level datum
`monicFactor_congr_of_pow_dvd_sub` consumes (through
`isCoprime_X_pow_of_coeff_zero_ne_zero`), and the reason `betaChild_spec`'s output can be fed
back into fixed-centre uniqueness. -/
theorem cofactor_coeff_zero_ne_zero {π : O} (hπ : Irreducible π) {μ D : ℕ} {b : Fin μ → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) {H' F : Polynomial O}
    (hF : F = C (π ^ D) * (monicPoly b * H'))
    (habs : ¬ π ^ (D + 1) ∣ F.coeff μ) :
    (H'.map (residue O)).coeff 0 ≠ 0 := by
  intro hcon
  refine habs ?_
  have hmap : ((monicPoly b * H').map (residue O)).coeff μ = 0 := by
    rw [Polynomial.map_mul, monicPoly_map_residue hb]
    have hx := Polynomial.coeff_X_pow_mul (H'.map (residue O)) μ 0
    rw [Nat.zero_add] at hx
    rw [hx, hcon]
  have hdvd : π ∣ (monicPoly b * H').coeff μ := by
    refine (residue_eq_zero_iff_dvd hπ _).1 ?_
    rwa [coeff_map] at hmap
  rw [hF, coeff_C_mul, pow_succ]
  exact mul_dvd_mul_left _ hdvd

variable [IsAdicComplete (maximalIdeal O) O]

/-- **`betaChild` at a SHALLOWER window, from one divided factorization.**  Any `𝔪`-valued
presentation `b` occurring in a `π ^ D`-divided factorization of ONE lift's frame — with a
residually invertible cofactor — computes the child class at every window `M ≤ N − D`.

Mechanism: `betaChild`'s description branch is inhabited at every window (the pinned split of
`betaChild_spec` witnesses it), its chosen witness `b₁` factors the CANONICAL frame, the two
frames agree mod `π ^ N` (H.109's `pow_dvd_coeff_comp_sub`), and after dividing by `π ^ D` the
monic degree-`μ` factors agree mod `π ^ (N − D)` by fixed-centre uniqueness. -/
theorem betaChild_proj_eq_of_factor {π : O} (hπ : Irreducible π) {m N μ k : ℕ}
    {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N) {c : ClusterState O m N}
    (h : HasChildAt π c μ k z) (h0 : ¬ IsDrainState c)
    {a : Fin m → O} (ha : proj O m N a = c.1)
    {b : Fin μ → O} {H' : Polynomial O}
    (hfac : (monicPoly a).comp (C (π ^ k) * (X + C (resSect O z)))
      = C (π ^ betaContent c k) * (monicPoly b * H'))
    (hH0 : (H'.map (residue O)).coeff 0 ≠ 0)
    {M : ℕ} (hM : M ≤ N - betaContent c k) :
    (betaChild π c h M).1 = proj O μ M b := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hDN : betaContent c k ≤ N - 1 := betaContent_le hm1 hN c h0 k
  have hDsum : betaContent c k + (N - betaContent c k) = N := by omega
  -- the description's branch is inhabited at EVERY window: the pinned split witnesses it
  obtain ⟨b₀, H₀, hb₀mem, hb₀eq, -⟩ :=
    betaChild_spec hπ hm hN c h h0 (classSect O m N c.1) (proj_classSect O m N c.1)
  have hex : ∃ d : ClusterState O μ M, ∃ (b' : Fin μ → O) (H'' : Polynomial O),
      (∀ i, b' i ∈ maximalIdeal O) ∧
      recFrame π c.1 k z = C (π ^ betaContent c k) * (monicPoly b' * H'') ∧
      proj O μ M b' = d.1 :=
    ⟨⟨proj O μ M b₀, fun i => Ideal.mem_map_of_mem _ (hb₀mem i)⟩, b₀, H₀, hb₀mem, hb₀eq, rfl⟩
  have hval : betaChild π c h M = hex.choose := by
    simp only [betaChild, dif_pos hex]
  obtain ⟨b₁, H₁, hb₁mem, hb₁eq, hb₁proj⟩ := hex.choose_spec
  rw [hval, ← hb₁proj]
  -- the two divided factorizations agree to level `π ^ (N − D)`
  have hπN : π ^ N = π ^ betaContent c k * π ^ (N - betaContent c k) := by
    rw [← pow_add, hDsum]
  have hdiff : ∀ j, π ^ M ∣ (monicPoly b * H' - monicPoly b₁ * H₁).coeff j := by
    intro j
    refine (pow_dvd_pow π hM).trans ?_
    have h1 : π ^ N ∣ ((monicPoly a).comp (C (π ^ k) * (X + C (resSect O z)))
        - (monicPoly (classSect O m N c.1)).comp
            (C (π ^ k) * (X + C (resSect O z)))).coeff j :=
      pow_dvd_coeff_comp_sub hπ (ha.trans (proj_classSect O m N c.1).symm) _ j
    rw [hfac, show (monicPoly (classSect O m N c.1)).comp (C (π ^ k) * (X + C (resSect O z)))
        = C (π ^ betaContent c k) * (monicPoly b₁ * H₁) from hb₁eq, ← mul_sub, coeff_C_mul,
      hπN] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 h1
  have huniq := monicFactor_congr_of_pow_dvd_sub hπ (monicPoly_monic b) (monicPoly_monic b₁)
    (monicPoly_natDegree b) (monicPoly_natDegree b₁) (monicPoly_map_residue hb₁mem)
    (isCoprime_X_pow_of_coeff_zero_ne_zero hH0 μ) hdiff
  refine (funext fun i => ?_).symm
  refine Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ _ _).2 ?_)
  have h3 := huniq (i : ℕ)
  rwa [coeff_sub, monicPoly_coeff_lt b i.isLt, monicPoly_coeff_lt b₁ i.isLt] at h3

/-- **The child presentation of a lift, valid at every window at most the genuine one.**  This
is `betaChild_spec` upgraded from ONE window to the whole shallower tower, with the cofactor's
residual unit carried along (it is what makes the upgrade legal, and what clause (ii)'s
transport re-uses on the other side of the peel). -/
theorem exists_betaChild_lift {π : O} (hπ : Irreducible π) {m N μ k : ℕ}
    {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N) {c : ClusterState O m N}
    (h : HasChildAt π c μ k z) (h0 : ¬ IsDrainState c)
    {a : Fin m → O} (ha : proj O m N a = c.1) :
    ∃ (b : Fin μ → O) (H' : Polynomial O),
      (∀ i, b i ∈ maximalIdeal O) ∧
      (monicPoly a).comp (C (π ^ k) * (X + C (resSect O z)))
        = C (π ^ betaContent c k) * (monicPoly b * H') ∧
      (H'.map (residue O)).coeff 0 ≠ 0 ∧
      ∀ M, M ≤ N - betaContent c k → (betaChild π c h M).1 = proj O μ M b := by
  obtain ⟨b, H', hbmem, hbeq, -⟩ := betaChild_spec hπ hm hN c h h0 a ha
  obtain ⟨-, -, c3⟩ := h.2.2.2 a (resSect O z) ha (residue_resSect O z)
  have hH0 : (H'.map (residue O)).coeff 0 ≠ 0 :=
    cofactor_coeff_zero_ne_zero hπ hbmem hbeq c3
  exact ⟨b, H', hbmem, hbeq, hH0,
    fun M hM => betaChild_proj_eq_of_factor hπ hm hN h h0 ha hbeq hH0 hM⟩

end Witness

/-! ## 1. H.116b1 (clause ii) — THE COFACTOR INHERITS THE REMAINING CHILDREN -/

section Inherit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **H.116b1 (clause ii) [A-H.7 §4].  THE COFACTOR INHERITS THE REMAINING CHILDREN.**
After peeling the `(μ, k, z)`-child off a lift of a non-drain state, the cofactor's class is
again non-drain, its content at any OTHER slope `k'` is the parent's less the planted floor
`μ · min (k, k')`, it carries the same child event at every foreign frame, and it READS the
same child there at the PARENT's window.

This is the inductive step clause (i) runs on, and (A-H.7 §3) the reason the degree-sum bound
`Σ_p μ_p ≤ m` is a conclusion of the peel rather than a hypothesis.

PROOF.  1. **Non-drain**: constant coefficients multiply and the planted factor's is
`π ^ (kμ) · (unit)`, so `π ^ N ∤ (monicPoly a).coeff 0` forces `π ^ N ∤ Q.coeff 0`.
2. **Content**: H116bR's Gauss law `level_recentre_mul_alphaParent` gives the product's exact
frame level as `μ · min (k, k') + e` with `e` the cofactor's exact level, and
`betaContent_eq_of_recentre_exact` identifies both ends.  3. **Child event**: H.116b2's
`coeff_level_mul_trailing` at `μ₁ = 0` (the planted factor is a UNIT at a FOREIGN frame —
`coeff_zero_recentre_alphaParent_not_dvd`, which is where `hne` is spent) makes the product's
first-unit abscissa the cofactor's; `abscissa_unique` identifies it with `μ'` and
`hasChildAt_of_exists` upgrades from the one lift pair.  4. **Read**: §0's
`exists_betaChild_lift` presents both children by divided factorizations of the SAME frame —
the parent's is the cofactor's multiplied by the planted unit — and fixed-centre uniqueness
identifies the two presentations at the parent's (shallower) window. -/
theorem peel_cofactor_inherits {π : O} (hπ : Irreducible π) {m N μ k : ℕ}
    {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N)
    (c : ClusterState O m N) (h0 : ¬ IsDrainState c) (h : HasChildAt π c μ k z)
    {b : Fin μ → O} (hb : ∀ i, b i ∈ maximalIdeal O) {Q : Polynomial O}
    (hQ : Q.Monic) (hQdeg : Q.natDegree = m - μ)
    {a : Fin m → O} (ha : proj O m N a = c.1)
    (hfac : monicPoly a = alphaParent π b k (resSect O z) * Q)
    (c' : ClusterState O (m - μ) N)
    (hc' : proj O (m - μ) N (fun i : Fin (m - μ) => Q.coeff (i : ℕ)) = c'.1)
    {μ' k' : ℕ} {z' : ResidueField O} (hne : ¬ (k' = k ∧ z' = z))
    (h' : HasChildAt π c μ' k' z') :
    ¬ IsDrainState c' ∧ betaContent c k' = μ * min k k' + betaContent c' k' ∧
      ∃ h'' : HasChildAt π c' μ' k' z',
        betaChild π c' h'' (N - betaContent c k')
          = betaChild π c h' (N - betaContent c k') := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hz : z ≠ 0 := h.2.2.1
  have hz' : z' ≠ 0 := h'.2.2.1
  have hk' : 1 ≤ k' := h'.2.1
  have hμ'2 : 2 ≤ μ' := h'.1
  have ha'eq : monicPoly (fun i : Fin (m - μ) => Q.coeff (i : ℕ)) = Q :=
    monicPoly_coeff_self hQ hQdeg
  -- the planted factor's profile at the FOREIGN frame `(k', z')`
  have hPlow : ∀ j, π ^ (μ * min k k') ∣
      (((alphaParent π b k (resSect O z))).comp
        (C (π ^ k') * (X + C (resSect O z')))).coeff j :=
    pow_min_dvd_coeff_recentre_alphaParent b k (resSect O z) k' (resSect O z')
  have hP0 : ¬ π ^ (μ * min k k' + 1) ∣
      (((alphaParent π b k (resSect O z))).comp
        (C (π ^ k') * (X + C (resSect O z')))).coeff 0 :=
    coeff_zero_recentre_alphaParent_not_dvd hπ hb (residue_resSect O z) hz
      (residue_resSect O z') hz' hne
  have hFsplit : (monicPoly a).comp (C (π ^ k') * (X + C (resSect O z')))
      = (((alphaParent π b k (resSect O z))).comp (C (π ^ k') * (X + C (resSect O z'))))
        * (Q.comp (C (π ^ k') * (X + C (resSect O z')))) := by
    rw [hfac, mul_comp]
  -- STEP 0: the cofactor has POSITIVE degree (a full-multiplicity child leaves no foreign one)
  have hmμ : 0 < m - μ := by
    by_contra hcon
    have hQ1 : Q = 1 := hQ.natDegree_eq_zero.1 (by omega)
    have haP : monicPoly a = (alphaParent π b k (resSect O z)) := by rw [hfac, hQ1, mul_one]
    have hDeq : betaContent c k' = μ * min k k' := by
      refine betaContent_eq_of_recentre_exact hπ hm1 hN c h0 k' ha (resSect O z') ?_ ?_
      · rw [haP]; exact hPlow
      · intro hall; rw [haP] at hall; exact hP0 (hall 0)
    obtain ⟨-, c2, -⟩ := h'.2.2.2 a (resSect O z') ha (residue_resSect O z')
    have hc0 := c2 0 (by omega)
    rw [hDeq, haP] at hc0
    exact hP0 hc0
  -- STEP 1: the cofactor is NON-DRAIN
  have h0' : ¬ IsDrainState c' := by
    intro hd
    have hQ0 : c'.1 ⟨0, hmμ⟩ = 0 := (isDrainState_iff hmμ c').1 hd
    have h2 : Ideal.Quotient.mk ((maximalIdeal O) ^ N) (Q.coeff 0) = 0 := by
      have hq := congrFun hc' (⟨0, hmμ⟩ : Fin (m - μ))
      rw [hQ0] at hq
      exact hq
    have h3 : π ^ N ∣ Q.coeff 0 :=
      (mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    refine h0 ((isDrainState_iff (by omega) c).2 ?_)
    have h7 : c.1 ⟨0, by omega⟩
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨0, by omega⟩) :=
      (congrFun ha ⟨0, by omega⟩).symm
    rw [h7]
    refine Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).2 ?_)
    rw [show a ⟨0, by omega⟩ = (monicPoly a).coeff 0 from
      (monicPoly_coeff_lt a (by omega : 0 < m)).symm, hfac, Polynomial.mul_coeff_zero]
    exact Dvd.dvd.mul_left h3 _
  -- STEP 2: the CONTENT splits as the planted floor plus the cofactor's content
  have hQlow : ∀ j, π ^ betaContent c' k' ∣
      (Q.comp (C (π ^ k') * (X + C (resSect O z')))).coeff j := by
    have hx := pow_content_dvd_coeff_recentre hπ c' k' hc' (resSect O z')
    rwa [ha'eq] at hx
  have hQhigh : ¬ ∀ j, π ^ (betaContent c' k' + 1) ∣
      (Q.comp (C (π ^ k') * (X + C (resSect O z')))).coeff j := by
    have hx := not_pow_content_succ_dvd_coeff_recentre hπ hmμ hN c' h0' k' hc' (resSect O z')
    rwa [ha'eq] at hx
  obtain ⟨g1, g2⟩ := level_recentre_mul_alphaParent hπ hb (residue_resSect O z) hz
    (residue_resSect O z') hz' Q hQlow hQhigh
  have hD : betaContent c k' = μ * min k k' + betaContent c' k' := by
    refine betaContent_eq_of_recentre_exact hπ hm1 hN c h0 k' ha (resSect O z') ?_ ?_
    · rw [hfac]; exact g1
    · rw [hfac]; exact g2
  -- STEP 3: the CHILD EVENT is inherited at the foreign frame
  have hex : ∃ j, ¬ π ^ (betaContent c' k' + 1) ∣
      (Q.comp (C (π ^ k') * (X + C (resSect O z')))).coeff j := not_forall.1 hQhigh
  have hA1 : ∀ j < Nat.find hex, π ^ (betaContent c' k' + 1) ∣
      (Q.comp (C (π ^ k') * (X + C (resSect O z')))).coeff j :=
    fun j hj => not_not.1 (Nat.find_min hex hj)
  have hA2 : ¬ π ^ (betaContent c' k' + 1) ∣
      (Q.comp (C (π ^ k') * (X + C (resSect O z')))).coeff (Nat.find hex) := Nat.find_spec hex
  obtain ⟨-, f2, f3⟩ := coeff_level_mul_trailing hπ hPlow
    (fun j hj => absurd hj (by omega)) hP0 hQlow hA1 hA2
  rw [Nat.zero_add, ← hFsplit] at f2 f3
  obtain ⟨-, c2, c3⟩ := h'.2.2.2 a (resSect O z') ha (residue_resSect O z')
  rw [hD] at c2 c3
  have hμ'A : μ' = Nat.find hex := abscissa_unique c2 c3 f2 f3
  have hch' : HasChildAt π c' μ' k' z' :=
    hasChildAt_of_exists hπ hN h0' hμ'2 hk' hz'
      (fun i : Fin (m - μ) => Q.coeff (i : ℕ)) (resSect O z') hc' (residue_resSect O z')
      (by rw [ha'eq]; exact hQlow)
      (by rw [ha'eq, hμ'A]; exact hA1)
      (by rw [ha'eq, hμ'A]; exact hA2)
  refine ⟨h0', hD, hch', ?_⟩
  -- STEP 4: the READ at the parent's window
  have hSdeg : (C (π ^ k') * (X + C (resSect O z')) : Polynomial O).natDegree ≤ 1 := by
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_add_C]
  have hQfdeg : (Q.comp (C (π ^ k') * (X + C (resSect O z')))).natDegree ≤ m - μ := by
    refine le_trans natDegree_comp_le ?_
    calc Q.natDegree * (C (π ^ k') * (X + C (resSect O z')) : Polynomial O).natDegree
        ≤ Q.natDegree * 1 := Nat.mul_le_mul_left _ hSdeg
      _ = m - μ := by rw [Nat.mul_one, hQdeg]
  have hAle : Nat.find hex ≤ m - μ := by
    by_contra hcon
    exact hA2 (by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _)
  have hm2' : 2 ≤ m - μ := by omega
  obtain ⟨bc, Hc, hbcmem, hbceq, -, hbcwin⟩ := exists_betaChild_lift hπ hm hN h' h0 ha
  obtain ⟨bq, Hq, -, hbqeq, hHq0, hbqwin⟩ :=
    exists_betaChild_lift hπ hm2' hN hch' h0' hc'
  rw [ha'eq] at hbqeq
  -- the planted factor's frame, divided by its floor: a residual UNIT constant term
  obtain ⟨U, hU⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ (μ * min k k'))
    (((alphaParent π b k (resSect O z))).comp
      (C (π ^ k') * (X + C (resSect O z'))))).2 hPlow
  have hU0 : residue O (U.coeff 0) ≠ 0 := by
    intro hcon
    refine hP0 ?_
    rw [hU, coeff_C_mul, pow_succ]
    exact mul_dvd_mul_left _ ((residue_eq_zero_iff_dvd hπ _).1 hcon)
  have hUHq0 : ((U * Hq).map (residue O)).coeff 0 ≠ 0 := by
    rw [Polynomial.map_mul, Polynomial.mul_coeff_zero, coeff_map]
    exact mul_ne_zero hU0 hHq0
  -- the two presentations factor the SAME frame
  have hkey : monicPoly bc * Hc = monicPoly bq * (U * Hq) := by
    have hCne : (C (π ^ betaContent c k') : Polynomial O) ≠ 0 := by
      simpa using pow_ne_zero (betaContent c k') hπ.ne_zero
    refine mul_left_cancel₀ hCne ?_
    rw [← hbceq, hFsplit, hU, hbqeq, hD, pow_add, C_mul]
    ring
  have hcongr := monicFactor_congr_of_pow_dvd_sub hπ (monicPoly_monic bq) (monicPoly_monic bc)
    (monicPoly_natDegree bq) (monicPoly_natDegree bc) (monicPoly_map_residue hbcmem)
    (isCoprime_X_pow_of_coeff_zero_ne_zero hUHq0 μ')
    (s := N - betaContent c k') (fun j => by rw [← hkey, sub_self]; exact dvd_zero _)
  refine Subtype.ext ?_
  rw [hbqwin (N - betaContent c k') (by omega), hbcwin (N - betaContent c k') le_rfl]
  refine (proj_eq_iff_pow_dvd hπ bq bc).2 fun i => ?_
  have hj := hcongr (i : ℕ)
  rwa [coeff_sub, monicPoly_coeff_lt bq i.isLt, monicPoly_coeff_lt bc i.isLt] at hj

end Inherit

end Uniformity.Density.Induction
