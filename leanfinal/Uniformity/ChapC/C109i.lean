/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C108
import Uniformity.ChapB.B77a
import Uniformity.ChapB.B77b
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C109i — NODE C.109-i, class-invariance of the HT node cell

**Chapter C, NODE C.109-i** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md`, the A-C.5
amendment, ITEM 1 — the C.109 SPLIT), **ENV-C1**.
`[signed: A-C.5, 2026-08-16 — layer 1 of five under C.109's byte-unchanged assembly]`.

Under window-visibility (`hvis : ∀ j ≤ v.m, v.Pceil j < N`), membership of `monicPoly a` in
`htCell π Φ v` depends only on the level-`N` class `proj O (v.m * Φ.natDegree) N a`.  This is
`EFF.W12.23`'s closing sentence — *"Every pinned or priced slot sits at height ≤ P(0) ≤ N−1:
in-window, no truncation error"* — as a STATEMENT, and it is what makes C.109's left-hand side
a count OF CLASSES rather than a count of integral lifts.

## Why `hvis` cannot be dropped (the node's teeth)

The `hvis`-free statement is FALSE by inspection: take `b` differing from `a` only at digit
`N` at a slot whose `Pceil j ≥ N`.  The two lifts have the same level-`N` class, but the pin
`npHgt Φ · j = Pceil j` reads a digit the class does not see.  Every use of `hvis` below is at
exactly such a read: `npHgt_le_iff` needs `k ≤ N`, `npHgt_eq_iff` needs `k < N`, and the
residual read needs the side's left-endpoint height `< N`.

## Proof route (four moves)

1. **Congruence.** `proj a = proj b` says `π ^ N ∣ (monicPoly a − monicPoly b).coeff k` for
   every `k` (`dvd_coeff_sub_of_proj_eq`), and B.10's `dev_congr` propagates that to every
   development coefficient.
2. **Heights transport inside the window.**  `le_gaussVal_iff` (B.08) turns `k ≤ npHgt` into
   coefficientwise divisibility by `π ^ k`; for `k ≤ N` the congruence transports it both ways
   (`npHgt_le_iff`).  Equality at a pinned height `k < N` is the conjunction of `k ≤ npHgt` and
   `¬ (k+1 ≤ npHgt)`, so it transports too (`npHgt_eq_iff`).
3. **The cell member is window-visible, and so are its side endpoints.**  Abscissa `0` is a
   hull vertex vacuously, so the cell pins `npHgt Φ f 0 = Pceil 0 < N`: the member is
   `Visible π Φ f N`, the hypothesis B.77a/B.77b's congruences consume.  The same pin bounds
   the `(u,ℓ)`-support value, hence forces every side's left endpoint to sit strictly below
   `N` as well (`npHgt_sideMin_lt`) — the fact that lets the residual read transport verbatim.
4. **The residual clause.**  B.77a's `sideSet_congr` makes the two side sets equal (so the
   `sideMin`s agree), and B.77b's `resPoly_congr` makes the two residual polynomials equal at
   the shared in-window height; the prescribed type then reads the same on both sides.

Both directions are the same lemma (`mem_htCell_transfer`) applied to `hab` and `hab.symm`.

**DEPENDS.** C.108 (`HTNode`, `HTNode.IsVertex`, `htCell`) · B.08 (`le_gaussVal_iff`) ·
B.10 (`dev_congr`) · B.11 (`npHgt`) · B.16/B.20 (`OnSide`, `sideSet`, `suppVal`, `sideMin`) ·
B.77a (`sideSet_congr`, `Visible`) · B.77b (`resPoly_congr`) · landed `proj`/`monicPoly`
(`Uniformity/Density/LocalData.lean`).

**SOURCE.** `EFF.W12.23` (the in-window sentence, verbatim).

**NOTE on `hwf`.** The signed statement carries `hwf : v.WF`; the proof does not need it (the
transfer is purely a congruence argument on the cell's five clauses, none of which mentions
the node's coherence).  The binder is kept because the signature is signed and C.109's
assembly passes `hwf` through; `linter.unusedVariables` is silenced at the theorem only.

## Status

Sorry-free, axiom-free (Lean core only).  Every helper is `private`: the node's signed surface
is exactly `htCell_class_invariant`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. The level-`N` congruence read off `proj` -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem coeff_tail {n : ℕ} (a : Fin n → O) (k : ℕ) :
    (∑ i : Fin n, C (a i) * X ^ (i : ℕ)).coeff k = if h : k < n then a ⟨k, h⟩ else 0 := by
  classical
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨k, h⟩ : Fin n)]
    · simp
    · intro c _ hc
      exact if_neg fun hk => hc (Fin.ext hk.symm)
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i _ => if_neg fun hk => ?_
    exact h (hk ▸ i.isLt)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem monicPoly_sub_coeff {n : ℕ} (a b : Fin n → O) (k : ℕ) :
    (monicPoly a - monicPoly b).coeff k = if h : k < n then a ⟨k, h⟩ - b ⟨k, h⟩ else 0 := by
  rw [coeff_sub]
  change ((X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)).coeff k
    - (X ^ n + ∑ i : Fin n, C (b i) * X ^ (i : ℕ)).coeff k) = _
  rw [coeff_add, coeff_add, coeff_tail, coeff_tail]
  by_cases h : k < n
  · rw [dif_pos h, dif_pos h, dif_pos h]; ring
  · rw [dif_neg h, dif_neg h, dif_neg h]; ring

private theorem dvd_coeff_sub_of_proj_eq (hπ : Irreducible π) {n N : ℕ} {a b : Fin n → O}
    (hab : proj O n N a = proj O n N b) (k : ℕ) :
    π ^ N ∣ (monicPoly a - monicPoly b).coeff k := by
  rw [monicPoly_sub_coeff]
  by_cases h : k < n
  · rw [dif_pos h]
    have hk : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (a ⟨k, h⟩)
        = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (b ⟨k, h⟩) := congrFun hab ⟨k, h⟩
    have hmem : a ⟨k, h⟩ - b ⟨k, h⟩ ∈ (IsLocalRing.maximalIdeal O) ^ N :=
      (Ideal.Quotient.eq.1 hk)
    rwa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  · rw [dif_neg h]
    exact dvd_zero _

/-! ### 2. Height transport inside the window -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem dvd_of_dvd_sub {x y : O} {k N : ℕ} (hk : k ≤ N) (h : π ^ N ∣ x - y)
    (hx : π ^ k ∣ x) : π ^ k ∣ y := by
  have h' : π ^ k ∣ x - y := (pow_dvd_pow π hk).trans h
  have hy : y = x - (x - y) := by ring
  rw [hy]
  exact dvd_sub hx h'

private theorem npHgt_le_iff (hπ : Irreducible π) {Φ : Polynomial O} (hΦm : Φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) {k : ℕ} (hk : k ≤ N) (j : ℕ) :
    ((k : ℕ) : ℕ∞) ≤ npHgt Φ f j ↔ ((k : ℕ) : ℕ∞) ≤ npHgt Φ f' j := by
  have hdc := dev_congr hπ hΦm hff' j
  have hdc' : ∀ i, π ^ N ∣ ((dev Φ f j).coeff i - (dev Φ f' j).coeff i) := by
    intro i
    simpa only [coeff_sub] using hdc i
  rw [npHgt, npHgt, le_gaussVal_iff hπ, le_gaussVal_iff hπ]
  constructor
  · exact fun h i => dvd_of_dvd_sub hk (hdc' i) (h i)
  · refine fun h i => dvd_of_dvd_sub hk ?_ (h i)
    exact (dvd_neg).1 (by simpa only [neg_sub] using hdc' i)

private theorem enat_eq_cast_iff {x : ℕ∞} {c : ℕ} :
    x = ((c : ℕ) : ℕ∞) ↔ (((c : ℕ) : ℕ∞) ≤ x ∧ ¬ (((c + 1 : ℕ) : ℕ∞) ≤ x)) := by
  constructor
  · rintro rfl
    refine ⟨le_rfl, ?_⟩
    rw [not_le]
    exact_mod_cast Nat.lt_succ_self c
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ h1
    by_contra hcon
    refine h2 ?_
    have hlt : ((c : ℕ) : ℕ∞) < x := not_le.1 hcon
    have : ((c : ℕ) : ℕ∞) + 1 ≤ x := (ENat.add_one_le_iff (by simp)).2 hlt
    simpa only [Nat.cast_add, Nat.cast_one] using this

private theorem npHgt_eq_iff (hπ : Irreducible π) {Φ : Polynomial O} (hΦm : Φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) {k : ℕ} (hk : k < N) (j : ℕ) :
    npHgt Φ f j = ((k : ℕ) : ℕ∞) ↔ npHgt Φ f' j = ((k : ℕ) : ℕ∞) := by
  rw [enat_eq_cast_iff, enat_eq_cast_iff, npHgt_le_iff hπ hΦm hff' hk.le j,
    npHgt_le_iff hπ hΦm hff' (Nat.succ_le_of_lt hk) j]

/-! ### 3. A cell member is window-visible, and its side endpoints sit inside the window -/

/-- abscissa `0` is a hull vertex vacuously, so the cell pins the height there. -/
private theorem isVertex_zero (v : HTNode) : v.IsVertex 0 :=
  fun i _ hi _ _ => absurd hi (Nat.not_lt_zero i)

private theorem npHgt_zero_of_mem (v : HTNode) {Φ : Polynomial O} [IsDomain (resField Φ)]
    [UniqueFactorizationMonoid (resField Φ)] {f : Polynomial O} (hf : f ∈ htCell π Φ v) :
    npHgt Φ f 0 = ((v.Pceil 0 : ℕ) : ℕ∞) :=
  hf.2.2.2.1 0 (Nat.zero_le _) (isVertex_zero v)

private theorem visible_of_mem (hπ : Irreducible π) (v : HTNode) {Φ : Polynomial O}
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)] {N : ℕ}
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) {f : Polynomial O} (hf : f ∈ htCell π Φ v) :
    Visible π Φ f N := by
  by_contra hcon
  simp only [Visible, not_exists, not_not] at hcon
  have hle : ((N : ℕ) : ℕ∞) ≤ npHgt Φ f 0 := (le_gaussVal_iff hπ).2 hcon
  rw [npHgt_zero_of_mem v hf] at hle
  exact absurd (Nat.cast_le.1 hle) (not_le.2 (hvis 0 (Nat.zero_le _)))

/-- the left endpoint of any side of a cell member sits strictly inside the window: its height
is bounded by the height at abscissa `0`, which the vertex clause pins at `Pceil 0 < N`. -/
private theorem npHgt_sideMin_lt (v : HTNode) {Φ : Polynomial O} [IsDomain (resField Φ)]
    [UniqueFactorizationMonoid (resField Φ)] {N : ℕ}
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) {f : Polynomial O} (hf : f ∈ htCell π Φ v)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hne : (sideSet Φ f u ℓ).Nonempty) :
    npHgt Φ f (sideMin Φ f u ℓ hne) < ((N : ℕ) : ℕ∞) := by
  set j₀ := sideMin Φ f u ℓ hne with hj₀
  have hon : OnSide Φ f u ℓ j₀ := onSide_of_mem_sideSet (Finset.min'_mem _ hne)
  have h0 : npHgt Φ f 0 = ((v.Pceil 0 : ℕ) : ℕ∞) := npHgt_zero_of_mem v hf
  have hinf : suppVal Φ f u ℓ ≤ ℓ • npHgt Φ f 0 + ((u * 0 : ℕ) : ℕ∞) :=
    Finset.inf_le (f := fun j => ℓ • npHgt Φ f j + ((u * j : ℕ) : ℕ∞))
      (Finset.mem_range.2 (Nat.succ_pos _))
  have hupper : suppVal Φ f u ℓ ≤ ((ℓ * v.Pceil 0 : ℕ) : ℕ∞) := by
    refine hinf.trans ?_
    rw [h0]
    simp [nsmul_eq_mul]
  by_contra hcon
  have hN : ((N : ℕ) : ℕ∞) ≤ npHgt Φ f j₀ := not_lt.1 hcon
  have hlow : ((ℓ * N : ℕ) : ℕ∞) ≤ suppVal Φ f u ℓ := by
    rw [← hon]
    refine le_trans ?_ (le_add_right (le_refl (ℓ • npHgt Φ f j₀)))
    calc ((ℓ * N : ℕ) : ℕ∞) = (ℓ : ℕ∞) * ((N : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ (ℓ : ℕ∞) * npHgt Φ f j₀ := mul_le_mul_right hN _
      _ = ℓ • npHgt Φ f j₀ := (nsmul_eq_mul _ _).symm
  have : ((ℓ * N : ℕ) : ℕ∞) ≤ ((ℓ * v.Pceil 0 : ℕ) : ℕ∞) := hlow.trans hupper
  have hnat : ℓ * N ≤ ℓ * v.Pceil 0 := Nat.cast_le.1 this
  exact absurd (Nat.le_of_mul_le_mul_left hnat hℓ) (not_le.2 (hvis 0 (Nat.zero_le _)))

/-! ### 4. The one-directional transfer -/

/-- `Finset.min'` depends only on the set: the nonemptiness argument is a proof. -/
private theorem min'_congr {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst hst; rfl

private theorem exists_nat_of_lt_top {x : ℕ∞} {N : ℕ} (h : x < ((N : ℕ) : ℕ∞)) :
    ∃ c : ℕ, x = ((c : ℕ) : ℕ∞) := by
  rcases eq_or_ne x ⊤ with rfl | htop
  · exact absurd h (by simp)
  · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 htop
    exact ⟨c, hc⟩

private theorem mem_htCell_transfer (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    (v : HTNode) {N : ℕ} (hvis : ∀ j, j ≤ v.m → v.Pceil j < N)
    {a b : Fin (v.m * Φ.natDegree) → O}
    (hab : proj O (v.m * Φ.natDegree) N a = proj O (v.m * Φ.natDegree) N b)
    (ha : monicPoly a ∈ htCell π Φ v) : monicPoly b ∈ htCell π Φ v := by
  have hff' : ∀ i, π ^ N ∣ (monicPoly a - monicPoly b).coeff i :=
    dvd_coeff_sub_of_proj_eq hπ hab
  have hdeg' : (monicPoly b).natDegree = (monicPoly a).natDegree := by
    rw [monicPoly_natDegree, monicPoly_natDegree]
  have hvisible : Visible π Φ (monicPoly a) N := visible_of_mem hπ v hvis ha
  have hge := ha.2.2.1
  have hvert := ha.2.2.2.1
  have hres := ha.2.2.2.2
  refine ⟨monicPoly_monic b, monicPoly_natDegree b, ?_, ?_, ?_⟩
  · intro j hj
    exact (npHgt_le_iff hπ hΦ.monic hff' (hvis j hj).le j).1 (hge j hj)
  · intro j hj hjv
    exact (npHgt_eq_iff hπ hΦ.monic hff' (hvis j hj) j).1 (hvert j hj hjv)
  · intro u ℓ hℓ hcop hmem hne' H₀ hH
    have hset : sideSet Φ (monicPoly b) u ℓ = sideSet Φ (monicPoly a) u ℓ :=
      sideSet_congr hπ hΦ.monic hΦ.pos hff' hdeg' hvisible u ℓ
    have hne : (sideSet Φ (monicPoly a) u ℓ).Nonempty := hset ▸ hne'
    have hmin : sideMin Φ (monicPoly b) u ℓ hne' = sideMin Φ (monicPoly a) u ℓ hne :=
      min'_congr hset hne' hne
    -- the left endpoint's height is inside the window, so it transports verbatim
    obtain ⟨c, hc⟩ :=
      exists_nat_of_lt_top (npHgt_sideMin_lt v hvis ha hℓ hne)
    have hcN : c < N := by
      have hlt := npHgt_sideMin_lt v hvis ha hℓ hne
      rw [hc] at hlt
      exact_mod_cast hlt
    have hc' : npHgt Φ (monicPoly b) (sideMin Φ (monicPoly a) u ℓ hne) = ((c : ℕ) : ℕ∞) :=
      (npHgt_eq_iff hπ hΦ.monic hff' hcN _).1 hc
    have hH₀c : H₀ = c := by
      rw [hmin, hc'] at hH
      exact_mod_cast hH.symm
    subst hH₀c
    have heq : resPoly π Φ (monicPoly b) u ℓ hne' H₀ = resPoly π Φ (monicPoly a) u ℓ hne H₀ :=
      resPoly_congr hπ hΦ.monic hΦ.pos hff' hdeg' hvisible hne hcN
    rw [heq]
    exact hres u ℓ hℓ hcop hmem hne H₀ hc

/-! ### 5. NODE C.109-i -/

set_option linter.unusedVariables false in
/-- **NODE C.109-i — class-invariance of the cell under window-visibility.** -/
theorem htCell_class_invariant (hπ : Irreducible π)
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    (v : HTNode) (hwf : v.WF) (N : ℕ) (hvis : ∀ j, j ≤ v.m → v.Pceil j < N)
    {a b : Fin (v.m * Φ.natDegree) → O}
    (hab : proj O (v.m * Φ.natDegree) N a = proj O (v.m * Φ.natDegree) N b) :
    monicPoly a ∈ htCell π Φ v ↔ monicPoly b ∈ htCell π Φ v :=
  ⟨mem_htCell_transfer hπ hΦ v hvis hab, mem_htCell_transfer hπ hΦ v hvis hab.symm⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.htCell_class_invariant

end AxCheck
