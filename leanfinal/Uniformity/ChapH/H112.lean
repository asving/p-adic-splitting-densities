/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H111

/-!
# Uniformity.ChapH.H112 — event well-formedness (uniqueness, window, finiteness)

**Chapter H, NODE H.112** [theorem] (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §3.2 N-2a's realized
`1 ≤ k`, `m k ≤ N − 1` plus CC-3(i) *"the windowed form is forced, not optional"*; sources
`EFF.GENIND.08`, `EFF.GENIND.09`).  Seventh node of **N-2**, the cluster event grammar over
`O`: it makes the grammar's α event well-formed.

Three clauses, in the blueprint's numbering (the Lean order is the dependency order, so
clause (ii) is proved first and clause (i) reads it):

* **(ii) `alpha_content`** — the α content is EXACT and WINDOWED: `betaContent c k = m * k`,
  with `1 ≤ k` and `m * k ≤ N − 1`.  The window condition is AUTOMATIC on true events, never
  an extra hypothesis: this is the site of OM-2's CC-3(i) replay, where the unwindowed form
  would read the nonexistent `u(0)`.
* **(i) `alpha_event_unique`** — two full-multiplicity children coincide (`k = k'`, `z = z'`).
* **(iii) `childSet_finite`** — the child set of any state is finite.

## How the three are proved (the mechanisms, none of them a residual polynomial)

The whole node is run off three elementary facts about the recentring
`G_w = f (π ^ k (X + w))` of a lift `f = monicPoly a`, each proved here:

* **the top coefficient** `G_w.coeff m = (π ^ k) ^ m` (`coeff_recentre_top`) and
  `G_w.natDegree = m` (`natDegree_recentre`) — the recentring is a degree-`1` substitution with
  leading coefficient `π ^ k`.  Clause (ii) is immediate: the non-divisibility clause of
  `HasChildAt` at `μ = m` says `π ^ (D + 1) ∤ π ^ (km)`, i.e. `D ≥ mk`, while `D ≤ mk` is the
  monic top term of the infimum (H.108).  The window bound is then H.108's `betaContent_le`.
* **ghost divisibility** `(π ^ k) ^ j ∣ G_w.coeff j` (`pow_dvd_coeff_recentre`) — every
  coefficient above the constant one carries the full ghost power of the substitution.  This
  is what bounds the slope in clause (iii): a child at `(μ, k)` with `μ ≥ 1` forces `k ≤ D`,
  and `D ≤ resOrd (c 0) ≤ N`.
* **the Taylor shift** (H.109's `comp_recentre_add`, `C_dvd_comp`) — moving the centre from `w`
  to `w'` is precomposition with `X + (w' − w)`.  Clause (i)'s `z = z'` is exactly this: both
  recentrings are `π ^ (mk) X ^ m` modulo `π ^ (mk+1)`, so `(X + d̄) ^ m = X ^ m` in the residue
  field, and evaluating at `−d̄` gives `d̄ = 0`.  This is the blueprint's "unique degree-`m` root
  block" reading, obtained WITHOUT forming a residual polynomial.

Clause (i)'s `k = k'` goes through the **visible height** `resOrd_zero_of_isAlphaState`:
an α state has `resOrd (c 0) = m * k` on the nose (`≥` from the content, `≤` because
`a 0 = G_w (−w) = π ^ (mk) (−w) ^ m + π ^ (mk+1) (…)` with `w` a unit).  Two α slopes read the
same visible height, so `m k = m k'`.

## Clause (iii) over an infinite residue field

`childSet_finite` carries NO `[Finite (ResidueField O)]` and NO hypothesis on `π` — the
blueprint's instruction is that the PROOF carries the pinning of `z`, not a `Finite` instance.
It does, in three steps: `μ ≤ m` (a non-divisible coefficient is nonzero, hence within the
degree), `k ≤ N` (ghost divisibility, as above), and — the pinning — the chosen lifts of
distinct children at a fixed slope are **unit-separated roots** of the reduction of the
dilation `H = f (π ^ k X)` modulo `π ^ (D + 1)`; `card_le_natDegree_of_unitSep` (proved here,
valid over ANY commutative ring: the factor theorem plus cancellation of the unit differences)
caps their number by `deg H ≤ m`.  Nothing in that chain needs `π` to be a uniformizer, which
is what lets the bare-`π` signature stand.

DEPENDS: H.107 (`resOrd`, `resOrd_ge_iff`, `resOrd_le`), H.108 (`IsDrainState`, `betaContent`,
`betaContent_le`, `betaContent_le_mul`, `betaContent_le_of_lt`), H.109 (`HasChildAt`,
`comp_recentre_add`, `C_dvd_comp`), H.111 (`IsAlphaState`) · landed `monicPoly`,
`monicPoly_monic`, `monicPoly_natDegree`, `monicPoly_coeff_lt`, `proj` · mathlib
`coeff_comp_degree_mul_degree`, `natDegree_linear`, `dvd_iff_isRoot`, `C_dvd_iff_dvd_coeff`,
`Set.Infinite.exists_subset_card_eq`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `π` explicit where the blueprint says so, every
binder INLINE (the B.42 completeness-binder rule; §17 declares no section variables).  No
`[Finite (ResidueField O)]` anywhere in this node — including clause (iii), see above — and no
`[IsAdicComplete]`.

## TEETH (GC-8)

Battery `P1(c) alpha locus law + window` of `verification/openmath/OM2_genindb_battery.py`
(28 cells × 2 rings), whose window half is
`if not (1 <= k and m * k <= W - 1): ok_c = False` over the realized α slopes, together with
the ALPHA branch's own content assertion in `_read_cluster_work`,
`assert D == m * k and Dpred == m * k`.  Both halves have a cheap combinatorial content and
both are reproduced by `#guard` at the end of the file: the admissible-slope index set of a
cell is exactly the battery's scan range `range(1, (N-1)/m + 1)`, and the capped content model
returns `m * k` on every α-dominating digit vector of the grid.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open Polynomial IsLocalRing

/-! ## 1. Ghost divisibility of a linear substitution

Pure `CommRing` facts: `π` is an arbitrary ring element here, and only the caller knows it is a
uniformizer. -/

/-- The recentring `C t * (X + C w)`, written as the linear substitution `C t * X + C (t w)`. -/
theorem recentre_eq_linear {O : Type*} [CommRing O] (t w : O) :
    C t * (X + C w) = C t * X + C (t * w) := by
  rw [map_mul]; ring

/-- **Ghost divisibility, one power.**  Coefficient `j` of `(t X + u) ^ i` is divisible by
`t ^ j`: each of the `j` `X`-factors it collects drags a `t` with it. -/
theorem pow_dvd_coeff_pow_linear {O : Type*} [CommRing O] (t u : O) (i : ℕ) :
    ∀ j : ℕ, t ^ j ∣ ((C t * X + C u) ^ i).coeff j := by
  induction i with
  | zero =>
      intro j
      rcases j with _ | n
      · simp
      · simp [Polynomial.coeff_one]
  | succ i ih =>
      intro j
      have hsplit : ((C t * X + C u) ^ (i + 1))
          = C t * (((C t * X + C u) ^ i) * X) + ((C t * X + C u) ^ i) * C u := by
        ring
      rw [hsplit, coeff_add, coeff_C_mul, coeff_mul_C]
      rcases j with _ | n
      · rw [pow_zero]
        exact one_dvd _
      · refine dvd_add ?_ (Dvd.dvd.mul_right (ih (n + 1)) u)
        rw [coeff_mul_X]
        obtain ⟨s, hs⟩ := ih n
        exact ⟨s, by rw [hs]; ring⟩

/-- **Ghost divisibility, any polynomial.** -/
theorem pow_dvd_coeff_comp_linear {O : Type*} [CommRing O] (t u : O) (p : Polynomial O) (j : ℕ) :
    t ^ j ∣ (p.comp (C t * X + C u)).coeff j := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, finsetSum_coeff]
  refine Finset.dvd_sum fun i _ => ?_
  rw [coeff_C_mul]
  exact (pow_dvd_coeff_pow_linear t u i j).mul_left _

/-- **Ghost divisibility for the recentring** `p (t (X + w))`. -/
theorem pow_dvd_coeff_recentre {O : Type*} [CommRing O] (t w : O) (p : Polynomial O) (j : ℕ) :
    t ^ j ∣ (p.comp (C t * (X + C w))).coeff j := by
  rw [recentre_eq_linear]
  exact pow_dvd_coeff_comp_linear t (t * w) p j

/-! ## 2. Unit-separated roots

The pinning device of clause (iii).  Over a general commutative ring a nonzero polynomial can
have infinitely many roots, but not infinitely many roots whose differences are UNITS: the
factor theorem plus cancellation of the unit differences runs the classical induction. -/

/-- **At most `deg` unit-separated roots.**  Valid over any commutative ring: `Nontrivial` is
extracted from `f ≠ 0`, not assumed. -/
theorem card_le_natDegree_of_unitSep {A : Type*} [CommRing A] :
    ∀ (n : ℕ) (f : Polynomial A) (s : Finset A), f.natDegree ≤ n → f ≠ 0 →
      (∀ r ∈ s, f.eval r = 0) →
      (∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → IsUnit (r - r')) → s.card ≤ n := by
  classical
  intro n
  induction n with
  | zero =>
      intro f s hdeg hf hroot _
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨r, hr⟩
      · simp
      · exfalso
        have hC : f = C (f.coeff 0) := eq_C_of_natDegree_le_zero hdeg
        have h0 : f.coeff 0 = 0 := by
          have hev := hroot r hr
          rw [hC, eval_C] at hev
          exact hev
        exact hf (by rw [hC, h0, map_zero])
  | succ n ih =>
      intro f s hdeg hf hroot hsep
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨r, hr⟩
      · simp
      haveI : Nontrivial A := by
        rcases subsingleton_or_nontrivial A with hsub | hnt
        · exact absurd (by ext i; exact Subsingleton.elim _ _ : f = 0) hf
        · exact hnt
      obtain ⟨g, hg⟩ : (X - C r) ∣ f := dvd_iff_isRoot.2 (hroot r hr)
      have hgne : g ≠ 0 := by
        intro h
        exact hf (by rw [hg, h, mul_zero])
      have hdegg : f.natDegree = g.natDegree + 1 := by
        have hlc : (X - C r : Polynomial A).leadingCoeff * g.leadingCoeff ≠ 0 := by
          rw [Polynomial.monic_X_sub_C r]
          simpa using fun h => hgne (Polynomial.leadingCoeff_eq_zero.1 h)
        rw [hg, Polynomial.natDegree_mul' hlc, Polynomial.natDegree_X_sub_C]
        omega
      have hgroot : ∀ r' ∈ s.erase r, g.eval r' = 0 := by
        intro r' hr'
        have hne : r' ≠ r := Finset.ne_of_mem_erase hr'
        have hmem : r' ∈ s := Finset.mem_of_mem_erase hr'
        have h0 : (r' - r) * g.eval r' = 0 := by
          have hev := hroot r' hmem
          rw [hg, eval_mul, eval_sub, eval_X, eval_C] at hev
          exact hev
        exact (IsUnit.mul_right_eq_zero (hsep r' hmem r hr hne)).1 h0
      have hcard := ih g (s.erase r) (by omega) hgne hgroot
        (fun x hx y hy hxy =>
          hsep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy)
      have := Finset.card_erase_add_one hr
      omega

/-! ## 3. The recentring at the top: degree and leading coefficient -/

/-- The recentred polynomial has degree `m`: the substitution is linear with leading
coefficient `π ^ k ≠ 0`. -/
theorem natDegree_recentre {O : Type*} [CommRing O] [IsDomain O] {π : O} (hπ0 : π ≠ 0) {m : ℕ}
    (a : Fin m → O) (k : ℕ) (w : O) :
    ((monicPoly a).comp (C (π ^ k) * (X + C w))).natDegree = m := by
  have ht : (π : O) ^ k ≠ 0 := pow_ne_zero k hπ0
  rw [recentre_eq_linear, natDegree_comp, natDegree_linear ht, monicPoly_natDegree, mul_one]

/-- The top coefficient of the recentred polynomial is `(π ^ k) ^ m` — the α event's
non-divisibility clause is a statement about THIS number. -/
theorem coeff_recentre_top {O : Type*} [CommRing O] [IsDomain O] {π : O} (hπ0 : π ≠ 0) {m : ℕ}
    (a : Fin m → O) (k : ℕ) (w : O) :
    ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff m = (π ^ k) ^ m := by
  have ht : (π : O) ^ k ≠ 0 := pow_ne_zero k hπ0
  rw [recentre_eq_linear]
  have h := coeff_comp_degree_mul_degree (p := monicPoly a)
    (q := C (π ^ k) * X + C (π ^ k * w)) (by rw [natDegree_linear ht]; norm_num)
  rw [natDegree_linear ht, monicPoly_natDegree, mul_one, leadingCoeff_linear ht,
    (monicPoly_monic a).leadingCoeff, one_mul] at h
  exact h

/-- **The α error term.**  If the recentred polynomial's coefficients below `m` are all
divisible by `π ^ (m k + 1)`, the polynomial IS `π ^ (m k) X ^ m` up to a polynomial all of
whose coefficients are divisible by `π ^ (m k + 1)`: at `j = m` the top coefficient is exactly
`π ^ (m k)`, and above `m` there is nothing. -/
theorem C_dvd_recentre_sub {O : Type*} [CommRing O] [IsDomain O] {π : O} (hπ0 : π ≠ 0) {m : ℕ}
    (a : Fin m → O) (k : ℕ) (w : O)
    (h2 : ∀ j < m, π ^ (m * k + 1) ∣
      ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j) :
    C (π ^ (m * k + 1)) ∣
      ((monicPoly a).comp (C (π ^ k) * (X + C w)) - C (π ^ (m * k)) * X ^ m) := by
  refine (C_dvd_iff_dvd_coeff _ _).2 fun j => ?_
  rw [coeff_sub, coeff_C_mul, coeff_X_pow]
  rcases lt_trichotomy j m with hj | hj | hj
  · rw [if_neg (by omega), mul_zero, sub_zero]
    exact h2 j hj
  · subst hj
    rw [if_pos rfl, mul_one, coeff_recentre_top hπ0 a k w, ← pow_mul,
      show k * j = j * k from Nat.mul_comm _ _, sub_self]
    exact dvd_zero _
  · rw [if_neg (by omega), mul_zero, sub_zero]
    have hd : ((monicPoly a).comp (C (π ^ k) * (X + C w))).natDegree < j := by
      rw [natDegree_recentre hπ0]; omega
    rw [coeff_eq_zero_of_natDegree_lt hd]
    exact dvd_zero _

/-! ## 4. Lifts, and the window from non-drain -/

/-- The residue map is surjective (used to pick a centre lifting a given `z`). -/
theorem residue_surj {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Function.Surjective (residue O) := Ideal.Quotient.mk_surjective

/-- Every level-`N` coefficient class has an integral lift — the `[Finite]`-free half of the
landed `proj_surjective` (whose section carries `[Finite (ResidueField O)]`, outside ENV-H17). -/
theorem exists_proj_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (c : Coeff O m N) : ∃ a : Fin m → O, proj O m N a = c := by
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) (c i)
  exact ⟨a, funext ha⟩

/-- A non-drain state forces a positive window: at `N = 0` the truncation ring is trivial, so
every state is a drain. -/
theorem one_le_window_of_not_drain {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m N : ℕ} (c : ClusterState O m N) (h0 : ¬ IsDrainState c) :
    1 ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · exfalso
    apply h0
    intro hm
    haveI : Subsingleton (Res O 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact Subsingleton.elim _ _
  · exact h

/-! ## 5. Clause (ii): the α content is exact and windowed -/

/-- **H.112 (clause ii).**  The α content is exactly `m * k`, and the event sits in the
window: `1 ≤ k` and `m * k ≤ N − 1` (the A-H.2 window condition, AUTOMATIC on true events).

`D ≤ m k` is the monic top term of H.108's infimum; `D ≥ m k` is the event's own
non-divisibility clause read at the top coefficient `π ^ (km)`; and the window bound is
H.108's `betaContent_le` on the non-drain state. -/
theorem alpha_content {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 2 ≤ m) (hN : 1 ≤ N)
    {c : ClusterState O m N} {k : ℕ} {z : ResidueField O} (h : IsAlphaState π c k z) :
    betaContent c k = m * k ∧ 1 ≤ k ∧ m * k ≤ N - 1 := by
  obtain ⟨h0, -, hchild⟩ := h
  obtain ⟨-, hk, -, hall⟩ := hchild
  obtain ⟨a, ha⟩ := exists_proj_eq c.1
  obtain ⟨w, hw⟩ := residue_surj (O := O) z
  obtain ⟨-, -, h3⟩ := hall a w ha hw
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have htop := coeff_recentre_top hπ0 a k w
  have hge : m * k ≤ betaContent c k := by
    by_contra hlt
    apply h3
    rw [htop, ← pow_mul, Nat.mul_comm k m]
    exact pow_dvd_pow π (by omega)
  have heq : betaContent c k = m * k := le_antisymm (betaContent_le_mul c k) hge
  refine ⟨heq, hk, ?_⟩
  have hle := betaContent_le (by omega : 1 ≤ m) hN c h0 k
  omega

/-! ## 6. The visible height, and clause (i): the α event is unique -/

/-- **The visible height of an α state.**  `resOrd (c 0) = m * k` on the nose.  `≥` is the
content bound; `≤` is the evaluation `a 0 = G (−w) = π ^ (mk) (−w) ^ m + π ^ (mk+1) (…)` with
`w` a unit (its residue `z` is nonzero), which is the α residual's `(−z) ^ m ≠ 0`. -/
theorem resOrd_zero_of_isAlphaState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 2 ≤ m)
    {c : ClusterState O m N} {k : ℕ} {z : ResidueField O} (h : IsAlphaState π c k z)
    (h0m : 0 < m) : resOrd (c.1 ⟨0, h0m⟩) = m * k := by
  have hN : 1 ≤ N := one_le_window_of_not_drain c h.1
  obtain ⟨hD, hk, hwin⟩ := alpha_content hπ hm hN h
  obtain ⟨h0, -, hchild⟩ := h
  obtain ⟨-, -, hz, hall⟩ := hchild
  obtain ⟨a, ha⟩ := exists_proj_eq c.1
  obtain ⟨w, hw⟩ := residue_surj (O := O) z
  obtain ⟨-, h2, -⟩ := hall a w ha hw
  have hπ0 : π ≠ 0 := hπ.ne_zero
  obtain ⟨E, hEeq⟩ := C_dvd_recentre_sub hπ0 a k w
    (fun j hj => by have hj2 := h2 j hj; rwa [hD] at hj2)
  -- evaluate the recentring at `−w`: it returns the constant coefficient of the lift
  have hval : (monicPoly a).coeff 0
      = π ^ (m * k) * (-w) ^ m + π ^ (m * k + 1) * E.eval (-w) := by
    have h1 : ((monicPoly a).comp (C (π ^ k) * (X + C w))).eval (-w)
        = (monicPoly a).eval 0 := by
      rw [eval_comp]
      simp
    have h2' : (monicPoly a).comp (C (π ^ k) * (X + C w))
        = C (π ^ (m * k)) * X ^ m + C (π ^ (m * k + 1)) * E := by
      rw [← hEeq]; ring
    rw [coeff_zero_eq_eval_zero, ← h1, h2']
    simp
  have ha0 : c.1 ⟨0, h0m⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨0, h0m⟩) := by
    rw [← ha]; rfl
  have hcoeff : (monicPoly a).coeff 0 = a ⟨0, h0m⟩ := monicPoly_coeff_lt a h0m
  rw [hcoeff] at hval
  have hlow : π ^ (m * k) ∣ a ⟨0, h0m⟩ := by
    rw [hval]
    exact dvd_add (Dvd.intro _ rfl) ⟨π * E.eval (-w), by rw [pow_succ]; ring⟩
  have hhigh : ¬ π ^ (m * k + 1) ∣ a ⟨0, h0m⟩ := by
    intro hcon
    have hsub : π ^ (m * k + 1) ∣ π ^ (m * k) * (-w) ^ m := by
      have hrw : π ^ (m * k) * (-w) ^ m
          = a ⟨0, h0m⟩ - π ^ (m * k + 1) * E.eval (-w) := by rw [hval]; ring
      rw [hrw]
      exact dvd_sub hcon (Dvd.intro _ rfl)
    rw [pow_succ] at hsub
    have hne : (π : O) ^ (m * k) ≠ 0 := pow_ne_zero _ hπ0
    have hdvd : π ∣ (-w) ^ m := (mul_dvd_mul_iff_left hne).1 hsub
    have hw' : π ∣ w := (dvd_neg).1 (hπ.prime.dvd_of_dvd_pow hdvd)
    apply hz
    rw [← hw]
    obtain ⟨u, rfl⟩ := hw'
    have hπm : π ∈ maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact hπ.not_isUnit
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ hπm)
  rw [ha0]
  have hle1 : m * k ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨0, h0m⟩)) :=
    (resOrd_ge_iff hπ (by omega) _).2 hlow
  have hle2 : ¬ (m * k + 1 ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨0, h0m⟩))) :=
    fun hcon => hhigh ((resOrd_ge_iff hπ (by omega) _).1 hcon)
  omega

/-- **The α centre is unique modulo `𝔪`.**  If two recentrings of the SAME lift both reduce to
`π ^ (m k) X ^ m` modulo `π ^ (m k + 1)`, their centres have the same residue: the shift
between them satisfies `(X + d̄) ^ m = X ^ m` in the residue field, and evaluating at `−d̄`
gives `d̄ = 0`.  This is the blueprint's "unique degree-`m` root block" reading — two distinct
roots of multiplicity `m` would need degree `≥ 2m` — obtained without forming a residual. -/
theorem residue_centre_unique {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 1 ≤ m) (a : Fin m → O) (k : ℕ) (w w' : O)
    (h2 : ∀ j < m, π ^ (m * k + 1) ∣
      ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j)
    (h2' : ∀ j < m, π ^ (m * k + 1) ∣
      ((monicPoly a).comp (C (π ^ k) * (X + C w'))).coeff j) :
    residue O w = residue O w' := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hA := C_dvd_recentre_sub hπ0 a k w h2
  have hA' := C_dvd_recentre_sub hπ0 a k w' h2'
  -- the two recentrings differ by the Taylor shift by `d = w' − w`
  have hshift : (monicPoly a).comp (C (π ^ k) * (X + C w'))
      = ((monicPoly a).comp (C (π ^ k) * (X + C w))).comp (X + C (w' - w)) := by
    have hww : w + (w' - w) = w' := by ring
    calc (monicPoly a).comp (C (π ^ k) * (X + C w'))
        = (monicPoly a).comp (C (π ^ k) * (X + C (w + (w' - w)))) := by rw [hww]
      _ = ((monicPoly a).comp (C (π ^ k) * (X + C w))).comp (X + C (w' - w)) :=
          comp_recentre_add (monicPoly a) (π ^ k) w (w' - w)
  have hkey : C (π ^ (m * k)) * ((X + C (w' - w)) ^ m - X ^ m)
      = ((monicPoly a).comp (C (π ^ k) * (X + C w')) - C (π ^ (m * k)) * X ^ m)
        - ((monicPoly a).comp (C (π ^ k) * (X + C w)) - C (π ^ (m * k)) * X ^ m).comp
            (X + C (w' - w)) := by
    rw [sub_comp, mul_comp, C_comp, pow_comp, X_comp, ← hshift]
    ring
  have hdvdB : C (π ^ (m * k + 1)) ∣ C (π ^ (m * k)) * ((X + C (w' - w)) ^ m - X ^ m) := by
    rw [hkey]
    exact dvd_sub hA' (C_dvd_comp hA _)
  obtain ⟨R, hR⟩ := hdvdB
  have hCne : (C (π ^ (m * k)) : Polynomial O) ≠ 0 := by
    simpa using pow_ne_zero (m * k) hπ0
  have hB : C π ∣ ((X + C (w' - w)) ^ m - X ^ m) := by
    refine ⟨R, mul_left_cancel₀ hCne ?_⟩
    rw [hR, pow_succ, map_mul]
    ring
  have hπm : π ∈ maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hπ.not_isUnit
  have hmapzero : ((X + C (w' - w)) ^ m - X ^ m).map (residue O) = 0 := by
    ext j
    rw [coeff_map, coeff_zero]
    obtain ⟨u, hu⟩ := (C_dvd_iff_dvd_coeff _ _).1 hB j
    rw [hu]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ hπm)
  have hpoly : ((X + C (residue O w' - residue O w)) ^ m - X ^ m
      : Polynomial (ResidueField O)) = 0 := by
    rw [← hmapzero]
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, map_sub]
  have heval : (-(residue O w' - residue O w)) ^ m = 0 := by
    have h := congrArg (Polynomial.eval (-(residue O w' - residue O w))) hpoly
    rw [eval_sub, eval_pow, eval_pow, eval_add, eval_X, eval_C, eval_zero,
      neg_add_cancel, zero_pow (by omega : m ≠ 0), zero_sub, neg_eq_zero] at h
    exact h
  have hzero : residue O w' - residue O w = 0 := by
    have hneg := (pow_eq_zero_iff (by omega : m ≠ 0)).1 heval
    rwa [neg_eq_zero] at hneg
  exact (sub_eq_zero.1 hzero).symm

/-- **H.112 (clause i).**  The α event is UNIQUE: two full-multiplicity children of the same
state coincide, both in slope and in centre.

The slope: a full child at slope `k` pins the visible height `resOrd (c 0) = m k`, so
`m k = m k'`.  The centre: with the slope fixed, `residue_centre_unique`. -/
theorem alpha_event_unique {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 2 ≤ m) {c : ClusterState O m N}
    {k k' : ℕ} {z z' : ResidueField O} :
    IsAlphaState π c k z → IsAlphaState π c k' z' → k = k' ∧ z = z' := by
  intro hα hα'
  have h0m : 0 < m := by omega
  have hkk : k = k' := by
    have h1 := resOrd_zero_of_isAlphaState hπ hm hα h0m
    have h2 := resOrd_zero_of_isAlphaState hπ hm hα' h0m
    exact Nat.eq_of_mul_eq_mul_left h0m (h1.symm.trans h2)
  subst hkk
  refine ⟨rfl, ?_⟩
  have hN : 1 ≤ N := one_le_window_of_not_drain c hα.1
  obtain ⟨hD, -, -⟩ := alpha_content hπ hm hN hα
  obtain ⟨a, ha⟩ := exists_proj_eq c.1
  obtain ⟨w, hw⟩ := residue_surj (O := O) z
  obtain ⟨w', hw'⟩ := residue_surj (O := O) z'
  obtain ⟨-, h2, -⟩ := hα.2.2.2.2.2 a w ha hw
  obtain ⟨-, h2', -⟩ := hα'.2.2.2.2.2 a w' ha hw'
  rw [← hw, ← hw']
  exact residue_centre_unique hπ (by omega) a k w w'
    (fun j hj => by have hj2 := h2 j hj; rwa [hD] at hj2)
    (fun j hj => by have hj2 := h2' j hj; rwa [hD] at hj2)

/-! ## 7. Clause (iii): the child set is finite

No `[Finite (ResidueField O)]` and no hypothesis on `π`: the multiplicity is capped by the
degree, the slope by the window, and the centre by the unit-separated root count. -/

/-- Every child multiplicity is at most the cluster degree: the event's non-divisible
coefficient is in particular NONZERO, hence within the degree of the recentring. -/
theorem mult_le_of_hasChildAt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N : ℕ} {c : ClusterState O m N} {μ k : ℕ} {z : ResidueField O}
    (h : HasChildAt π c μ k z) : μ ≤ m := by
  obtain ⟨-, -, -, hall⟩ := h
  obtain ⟨a, ha⟩ := exists_proj_eq c.1
  obtain ⟨w, hw⟩ := residue_surj (O := O) z
  obtain ⟨-, -, h3⟩ := hall a w ha hw
  have hne : ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff μ ≠ 0 := by
    intro hzero
    exact h3 (by rw [hzero]; exact dvd_zero _)
  have hdeg : ((monicPoly a).comp (C (π ^ k) * (X + C w))).natDegree ≤ m := by
    refine le_trans natDegree_comp_le ?_
    have hq : ((C (π ^ k) * (X + C w)) : Polynomial O).natDegree ≤ 1 := by
      refine le_trans (natDegree_C_mul_le _ _) ?_
      rw [natDegree_X_add_C]
    calc (monicPoly a).natDegree * ((C (π ^ k) * (X + C w)) : Polynomial O).natDegree
        ≤ (monicPoly a).natDegree * 1 := Nat.mul_le_mul_left _ hq
      _ = m := by rw [mul_one, monicPoly_natDegree]
  exact le_trans (le_natDegree_of_ne_zero hne) hdeg

/-- Every child slope sits inside the window.  Ghost divisibility gives `π ^ k ∣ G.coeff μ` at
`μ ≥ 1`, so the event's non-divisibility clause forces `k ≤ D`, and `D ≤ resOrd (c 0) ≤ N`. -/
theorem slope_le_of_hasChildAt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N : ℕ} {c : ClusterState O m N} {μ k : ℕ} {z : ResidueField O}
    (h : HasChildAt π c μ k z) : k ≤ N := by
  have hμm : μ ≤ m := mult_le_of_hasChildAt h
  obtain ⟨hμ, -, -, hall⟩ := h
  obtain ⟨a, ha⟩ := exists_proj_eq c.1
  obtain ⟨w, hw⟩ := residue_surj (O := O) z
  obtain ⟨-, -, h3⟩ := hall a w ha hw
  have hdvd : π ^ k ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff μ :=
    dvd_trans (dvd_pow_self (π ^ k) (by omega : μ ≠ 0))
      (pow_dvd_coeff_recentre (π ^ k) w (monicPoly a) μ)
  have hkD : k ≤ betaContent c k := by
    by_contra hcon
    exact h3 (dvd_trans (pow_dvd_pow π (by omega)) hdvd)
  have h0m : 0 < m := by omega
  have hb : betaContent c k ≤ resOrd (c.1 ⟨0, h0m⟩) := by
    simpa using betaContent_le_of_lt c k h0m
  have hr : resOrd (c.1 ⟨0, h0m⟩) ≤ N := resOrd_le _
  omega

/-- **The `z`-slice of the child set is finite**, at every slope and over an arbitrary
(possibly infinite) residue field.  The chosen lifts of distinct children are unit-separated
roots of the reduction, modulo `π ^ (D + 1)`, of the slope-`k` dilation `H = f (π ^ k X)`;
that reduction is nonzero (else the event's non-divisibility clause fails), so
`card_le_natDegree_of_unitSep` caps their number by `deg H ≤ m`. -/
theorem childZ_finite {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) (k : ℕ) :
    {z : ResidueField O | ∃ μ, HasChildAt π c μ k z}.Finite := by
  classical
  rw [← Set.not_infinite]
  intro hinf
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq (m + 1)
  obtain ⟨a, ha⟩ := exists_proj_eq c.1
  -- a section of the residue map, and the slope-`k` dilation
  set lft : ResidueField O → O := Function.surjInv (residue_surj (O := O)) with hlftdef
  have hlft : ∀ z, residue O (lft z) = z := fun z => Function.surjInv_eq _ z
  set J : Ideal O := Ideal.span {π ^ (betaContent c k + 1)} with hJ
  set φ := Ideal.Quotient.mk J with hφ
  set H := (monicPoly a).comp (C (π ^ k) * X) with hH
  have hHcomp : ∀ v : O, H.comp (X + C v) = (monicPoly a).comp (C (π ^ k) * (X + C v)) := by
    intro v
    rw [hH, Polynomial.comp_assoc]
    congr 1
    simp
  have hEval : ∀ v : O, ((monicPoly a).comp (C (π ^ k) * (X + C v))).coeff 0 = H.eval v := by
    intro v
    rw [← hHcomp v, coeff_zero_eq_eval_zero, eval_comp]
    simp
  -- (1) every chosen lift is a root modulo `π ^ (D + 1)`
  have hzdata : ∀ z ∈ s, π ^ (betaContent c k + 1) ∣ H.eval (lft z) := by
    intro z hz
    obtain ⟨μ, hμ, -, -, hall⟩ := hs hz
    obtain ⟨-, h2, -⟩ := hall a (lft z) ha (hlft z)
    have h0 := h2 0 (by omega)
    rwa [hEval (lft z)] at h0
  -- (2) the reduction is nonzero
  obtain ⟨z₀, hz₀⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have hHbar : H.map φ ≠ 0 := by
    intro hzero
    obtain ⟨μ, -, -, -, hall⟩ := hs hz₀
    obtain ⟨-, -, h3⟩ := hall a (lft z₀) ha (hlft z₀)
    refine h3 ?_
    have hHd : C (π ^ (betaContent c k + 1)) ∣ H := by
      refine (C_dvd_iff_dvd_coeff _ _).2 fun i => ?_
      have hi : φ (H.coeff i) = 0 := by rw [← coeff_map, hzero, coeff_zero]
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem, hJ, Ideal.mem_span_singleton] at hi
      exact hi
    have hcomp := (C_dvd_iff_dvd_coeff _ _).1 (C_dvd_comp hHd (X + C (lft z₀))) μ
    rwa [hHcomp (lft z₀)] at hcomp
  haveI hnt : Nontrivial (O ⧸ J) := by
    rcases subsingleton_or_nontrivial (O ⧸ J) with hsub | hnt
    · exact absurd (by ext i; exact Subsingleton.elim _ _ : H.map φ = 0) hHbar
    · exact hnt
  -- (3) unit separation, and injectivity of the chosen lifts
  have hunit : ∀ z ∈ s, ∀ z' ∈ s, z ≠ z' → IsUnit (φ (lft z) - φ (lft z')) := by
    intro z hz z' hz' hne
    have hdiff : residue O (lft z - lft z') ≠ 0 := by
      rw [map_sub, hlft, hlft]
      exact sub_ne_zero.2 hne
    have hu : IsUnit (lft z - lft z') := by
      by_contra hcon
      exact hdiff (Ideal.Quotient.eq_zero_iff_mem.2
        ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcon)))
    have hmap := IsUnit.map φ hu
    rwa [map_sub] at hmap
  have hinj : Set.InjOn (fun z => φ (lft z)) s := by
    intro z hz z' hz' heq
    by_contra hne
    have hu := hunit z hz z' hz' hne
    have heq' : φ (lft z) = φ (lft z') := heq
    rw [heq', sub_self] at hu
    exact not_isUnit_zero hu
  -- (4) the root count
  have hroot : ∀ r ∈ s.image (fun z => φ (lft z)), (H.map φ).eval r = 0 := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hr
    have hz0 : φ (H.eval (lft z)) = 0 := by
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem, hJ, Ideal.mem_span_singleton]
      exact hzdata z hz
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hz0]
  have hsep : ∀ r ∈ s.image (fun z => φ (lft z)), ∀ r' ∈ s.image (fun z => φ (lft z)),
      r ≠ r' → IsUnit (r - r') := by
    intro r hr r' hr' hne
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hr'
    exact hunit z hz z' hz' (fun h => hne (by rw [h]))
  have hbound := card_le_natDegree_of_unitSep (H.map φ).natDegree (H.map φ)
    (s.image (fun z => φ (lft z))) le_rfl hHbar hroot hsep
  have hcardimg : (s.image (fun z => φ (lft z))).card = m + 1 := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have hdegH : H.natDegree ≤ m := by
    rw [hH]
    refine le_trans natDegree_comp_le ?_
    have hq : ((C (π ^ k) * X) : Polynomial O).natDegree ≤ 1 := by
      refine le_trans (natDegree_C_mul_le _ _) ?_
      rw [natDegree_X]
    calc (monicPoly a).natDegree * ((C (π ^ k) * X) : Polynomial O).natDegree
        ≤ (monicPoly a).natDegree * 1 := Nat.mul_le_mul_left _ hq
      _ = m := by rw [mul_one, monicPoly_natDegree]
  have hmapdeg := natDegree_map_le (f := φ) (p := H)
  omega

/-- **H.112 (clause iii).**  The child set of any state is FINITE.  It sits inside
`Iic m ×ˢ ⋃ (k ≤ N), {k} ×ˢ (the finite `z`-slice at `k`)`. -/
theorem childSet_finite {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) :
    {p : ℕ × ℕ × ResidueField O | HasChildAt π c p.1 p.2.1 p.2.2}.Finite := by
  refine Set.Finite.subset
    ((Set.finite_Iic m).prod ((Set.finite_Iic N).biUnion
      (fun k _ => (Set.finite_singleton k).prod (childZ_finite π c k)))) ?_
  rintro ⟨μ, k, z⟩ hp
  exact ⟨mult_le_of_hasChildAt hp, Set.mem_biUnion (slope_le_of_hasChildAt hp) ⟨rfl, ⟨μ, hp⟩⟩⟩

end Uniformity.Density.Induction

/-! ## 8. TEETH — the battery's window scan and ALPHA content assertion, reproduced

`P1(c) alpha locus law + window` scans the realized α slopes of a cell and asserts
`1 <= k and m * k <= W - 1`, then re-scans `for k in range(1, (W - 1) // m + 1)` to demand that
every admissible slope IS realized.  The window predicate and its index range are pure
arithmetic, and `windowedSlopes` below reproduces them: the admissible slopes of a cell are
exactly the battery's scan range.

The ALPHA branch of `_read_cluster_work` additionally asserts `Dpred == m * k` at every α
state, where `Dpred` is the capped content model of H.108.  `contentModel` is that model
transcribed; the guard runs it over the α-dominating digit vectors (`v j ≥ (m − j) k`, the
one-sided polygon condition) of a grid, where the theorem `alpha_content` says the answer must
be `m * k`. -/

section NumericGate

/-- The window predicate of the battery's α scan: `1 ≤ k` and `m * k ≤ N − 1`. -/
def alphaWindow (m N k : ℕ) : Bool := decide (1 ≤ k ∧ m * k ≤ N - 1)

/-- The admissible slopes of a cell, filtered out of `0, …, N`. -/
def windowedSlopes (m N : ℕ) : List ℕ := (List.range (N + 1)).filter (alphaWindow m N)

-- the admissible-slope set IS the battery's scan range `range(1, (N-1)//m + 1)`,
-- at every cell of the battery's `part1` plan (its largest window per `(q, m)` row)
#guard [(2, 6), (3, 6), (4, 4), (2, 5), (3, 4), (4, 3)].all
  fun p => windowedSlopes p.1 p.2 == List.range' 1 ((p.2 - 1) / p.1)

#guard windowedSlopes 2 6 == [1, 2]
#guard windowedSlopes 3 6 == [1]
#guard windowedSlopes 4 3 == []

/-- The capped content model `Dpred = min_{j ≤ m} (min (v j) N + j k)`, with the monic top
`j = m` contributing `m * k` (H.108's `betaContent`, transcribed for numerals). -/
def contentModel (v : List ℕ) (N k : ℕ) : ℕ :=
  let m := v.length
  ((v.zipIdx.map fun p => min p.1 N + p.2 * k) ++ [m * k]).foldr min (m * k)

/-- The α-dominating (one-sided polygon) condition `v j ≥ (m − j) k`. -/
def alphaDominates (v : List ℕ) (k : ℕ) : Bool :=
  v.zipIdx.all fun p => decide ((v.length - p.2) * k ≤ p.1)

-- ALPHA branch, `assert Dpred == m * k`: on every α-dominating digit vector of the grid
-- (`m = 2`, digits `≤ 4`, slopes `k ≤ 2`, window wide enough to see the whole side) the capped
-- content is exactly `m * k`
#guard ((List.range 5).flatMap fun v0 => (List.range 5).map fun v1 => [v0, v1]).all
  fun v => (List.range 3).all fun k =>
    !(alphaDominates v k) || contentModel v 8 k == v.length * k

-- the same at `m = 3`
#guard ((List.range 4).flatMap fun v0 => (List.range 4).flatMap fun v1 =>
    (List.range 4).map fun v2 => [v0, v1, v2]).all
  fun v => (List.range 2).all fun k =>
    !(alphaDominates v k) || contentModel v 9 k == v.length * k

-- DEFEAT 1 (domination is load-bearing): a non-dominating vector has content BELOW `m * k`
#guard alphaDominates [1, 0] 1 == false
#guard contentModel [1, 0] 8 1 == 1

-- DEFEAT 2 (the window is load-bearing, and it is a CONCLUSION, not a hypothesis): at
-- `m = 2, k = 2, N = 3` the slope is out of window, and there the capped content drops to `3`,
-- below `m * k = 4` — so `alpha_content`'s `betaContent c k = m * k` could not hold, which is
-- exactly why no α event is realized at an out-of-window slope
#guard alphaWindow 2 3 2 == false
#guard alphaDominates [4, 2] 2 == true
#guard contentModel [4, 2] 3 2 == 3
#guard contentModel [4, 2] 8 2 == 4

-- non-vacuity: the α-dominating populations actually exercised above
#guard (((List.range 5).flatMap fun v0 => (List.range 5).map fun v1 => [v0, v1]).filter
  fun v => alphaDominates v 1).length == 12
#guard (((List.range 5).flatMap fun v0 => (List.range 5).map fun v1 => [v0, v1]).filter
  fun v => alphaDominates v 2).length == 3
#guard (((List.range 4).flatMap fun v0 => (List.range 4).flatMap fun v1 =>
    (List.range 4).map fun v2 => [v0, v1, v2]).filter
  fun v => alphaDominates v 1).length == 6

end NumericGate

/-! ## 9. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.pow_dvd_coeff_recentre
#print axioms Uniformity.Density.Induction.card_le_natDegree_of_unitSep
#print axioms Uniformity.Density.Induction.coeff_recentre_top
#print axioms Uniformity.Density.Induction.alpha_content
#print axioms Uniformity.Density.Induction.resOrd_zero_of_isAlphaState
#print axioms Uniformity.Density.Induction.residue_centre_unique
#print axioms Uniformity.Density.Induction.alpha_event_unique
#print axioms Uniformity.Density.Induction.childZ_finite
#print axioms Uniformity.Density.Induction.childSet_finite

end AxCheck
