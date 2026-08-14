/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.StrongHensel — Hensel's lemma with a NON-UNIT derivative

**What this file proves.** Over a complete discrete valuation ring `O` with uniformizer `π`, for an
arbitrary polynomial `F ∈ O[X]` (no monicity, no degree bound) and a point `x₀` with

    F'(x₀) = π ^ w * u   (u a unit, i.e. `v(F'(x₀)) = w` exactly)      and
    π ^ k ∣ F(x₀)        (i.e. `v(F(x₀)) ≥ k`)      with      2 * w < k

there is a root `r` of `F` with `π ^ (k - w) ∣ r - x₀`, and it is the *unique* root in the open
disc `π ^ (w + 1) ∣ s - x₀` (`strongHensel`).  The `addVal` phrasing
(`v(F(x₀)) > 2 v(F'(x₀)) = 2w ⟹ ∃! root at distance > w`) is `strongHensel_addVal`.

This is `HYP.04` of `spec/HYPOTHESIS_LEDGER.md`, whose consumer is the `n = 3` triple-root
recursion of `leancheck/notes/N3_CHECK_2026-08-13.md` §9.4.

## Provenance (checked 2026-08-14)

Mathlib has the `w = 0` case for a general complete local ring (`HenselianLocalRing`,
`IsAdicComplete.henselianRing` in `Mathlib/RingTheory/Henselian.lean`) and the `w ≥ 0` case only
for `ℤ_[p]` (`hensels_lemma` in `Mathlib/NumberTheory/Padics/Hensel.lean`, which is proved with the
`ℤ_[p]`-specific archimedean-style norm estimates and does not generalise verbatim). The
general-DVR statement below is not in mathlib. The coprime-factorization form of Hensel (this
repo's `Uniformity.HenselFactorization`) does **not** supply it: after recentring, the residual
factorization is `X · X²`, which is not coprime (`N3_CHECK` §9.4).

## Method

The classical Newton iteration with the quadratic-convergence bookkeeping, run on the divisibility
filtration rather than a norm. The invariant carried by `NState` is

    F'(xₙ) = π ^ w * uₙ  (uₙ a unit)      and      π ^ (2 * w + jₙ) ∣ F(xₙ) ,   jₙ ≥ 1 ,

and one step doubles `jₙ` (`newton_step`) while moving the point by `π ^ (w + jₙ)`. The `w` never
moves: that is the whole content of the "strong" form. Completeness enters exactly twice, through
`IsPrecomplete` (the limit exists) and `IsHausdorff` (the limit is a root); both come from the
standing bundle's `IsAdicComplete (maximalIdeal O) O`.

Compare `Mathlib/RingTheory/Henselian.lean`'s proof of `IsAdicComplete.henselianRing`, which is the
`w = 0` specialisation of the same argument written with `Ring.inverse`; here the derivative is not
invertible, so the correction is built from the unit part `u` of `F'(x)` explicitly and the excess
`π ^ w` is paid for out of the surplus `k - 2w`.

## Status

Zero `sorry`; no axiom is declared here; every theorem's `#print axioms` footprint is the Lean core
triple `propext, Classical.choice, Quot.sound` (printed by the `AxCheck` block at the foot of the
file). Informal proofs and faithfulness paragraphs: `notes/P5_INFRA_2026-08-14.md` §1.
-/

set_option linter.style.longLine false

namespace Uniformity

namespace Hensel

open Polynomial IsLocalRing

section Step

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- In a local ring, a unit plus an element of the maximal ideal is a unit. -/
theorem isUnit_add_of_mem_maximalIdeal {u m : O} (hu : IsUnit u) (hm : m ∈ maximalIdeal O) :
    IsUnit (u + m) := by
  by_contra h
  rw [← notMem_maximalIdeal, not_not] at h
  refine (notMem_maximalIdeal.2 hu) ?_
  have h2 : u + m - m ∈ maximalIdeal O := Ideal.sub_mem _ h hm
  simpa using h2

/-- **The Newton step, with the derivative's valuation held fixed.**

If `v(F'(x)) = w` exactly (written `F'(x) = π ^ w * u` with `u` a unit) and
`π ^ (2w + j) ∣ F(x)` with `j ≥ 1`, then the Newton correction `δ = -F(x) / F'(x)` — which lies in
`O` because `π ^ (w + j)` divides it — produces a point `y = x + δ` at which the *same* invariant
holds with `j` replaced by `2j`. The doubling of `j` is the quadratic convergence; the invariance
of `w` is what makes the iteration run at all. -/
theorem newton_step {π : O} (hπ : Irreducible π) {F : Polynomial O} {x : O} {w j : ℕ}
    (hj : 1 ≤ j) (hd : ∃ u : Oˣ, F.derivative.eval x = π ^ w * u)
    (hv : π ^ (2 * w + j) ∣ F.eval x) :
    ∃ y : O, π ^ (w + j) ∣ y - x ∧ (∃ u' : Oˣ, F.derivative.eval y = π ^ w * u') ∧
      π ^ (2 * w + 2 * j) ∣ F.eval y := by
  obtain ⟨u, hu⟩ := hd
  obtain ⟨a, ha⟩ := hv
  have huu : (u : O) * (↑u⁻¹ : O) = 1 := u.mul_inv
  set δ : O := -(π ^ (w + j) * a * (↑u⁻¹ : O)) with hδ
  refine ⟨x + δ, ⟨-(a * (↑u⁻¹ : O)), by rw [hδ]; ring⟩, ?_, ?_⟩
  · -- the derivative keeps valuation exactly `w`
    obtain ⟨t, ht⟩ := sub_dvd_eval_sub (x + δ) x F.derivative
    have hmem : (-(π ^ j * a * (↑u⁻¹ : O) * t)) ∈ maximalIdeal O := by
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton, dvd_neg]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (dvd_pow_self π (by omega : j ≠ 0)) a) _) t
    have hunit : IsUnit ((u : O) + -(π ^ j * a * (↑u⁻¹ : O) * t)) :=
      isUnit_add_of_mem_maximalIdeal u.isUnit hmem
    refine ⟨hunit.unit, ?_⟩
    rw [hunit.unit_spec]
    have hstep : F.derivative.eval (x + δ) = F.derivative.eval x + δ * t := by
      have h2 := ht
      rw [add_sub_cancel_left] at h2
      linear_combination h2
    rw [hstep, hu, hδ]
    ring
  · -- the value's surplus doubles
    obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add F x δ
    have hcancel : F.derivative.eval x * δ + F.eval x = 0 := by
      rw [hu, ha, hδ]
      linear_combination (-(π ^ (2 * w + j) * a)) * huu
    have hFy : F.eval (x + δ) = c * δ ^ 2 := by
      rw [← hc]; linear_combination hcancel
    exact ⟨c * (a * (↑u⁻¹ : O)) ^ 2, by rw [hFy, hδ]; ring⟩

end Step

/-! ## The iteration -/

section Iterate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The state of the strong Newton iteration.** `pt` is the current approximation, `lvl` the
current surplus `j`: the value `F(pt)` is divisible by `π ^ (2w + lvl)` while the derivative still
has valuation exactly `w`. -/
structure NState (π : O) (F : Polynomial O) (w : ℕ) where
  /-- The current approximation. -/
  pt : O
  /-- The current surplus `j` (a lower bound for `v(F(pt)) - 2w`). -/
  lvl : ℕ
  /-- The surplus is positive — this is the strict inequality `v(F(x₀)) > 2 v(F'(x₀))`. -/
  lvl_pos : 1 ≤ lvl
  /-- The derivative has valuation exactly `w` at the current point. -/
  der : ∃ u : Oˣ, F.derivative.eval pt = π ^ w * u
  /-- The value has valuation at least `2w + lvl` at the current point. -/
  vdvd : π ^ (2 * w + lvl) ∣ F.eval pt

variable {π : O} {F : Polynomial O} {w : ℕ}

/-- One Newton step on states. -/
noncomputable def NState.next (hπ : Irreducible π) (s : NState π F w) : NState π F w where
  pt := (newton_step hπ s.lvl_pos s.der s.vdvd).choose
  lvl := 2 * s.lvl
  lvl_pos := by have := s.lvl_pos; omega
  der := (newton_step hπ s.lvl_pos s.der s.vdvd).choose_spec.2.1
  vdvd := (newton_step hπ s.lvl_pos s.der s.vdvd).choose_spec.2.2

theorem NState.next_lvl (hπ : Irreducible π) (s : NState π F w) :
    (s.next hπ).lvl = 2 * s.lvl := rfl

theorem NState.next_dist (hπ : Irreducible π) (s : NState π F w) :
    π ^ (w + s.lvl) ∣ (s.next hπ).pt - s.pt :=
  (newton_step hπ s.lvl_pos s.der s.vdvd).choose_spec.1

/-- The iterated state. -/
noncomputable def NState.iter (hπ : Irreducible π) (s : NState π F w) : ℕ → NState π F w
  | 0 => s
  | n + 1 => (s.iter hπ n).next hπ

theorem NState.iter_zero (hπ : Irreducible π) (s : NState π F w) : s.iter hπ 0 = s := rfl

theorem NState.iter_lvl (hπ : Irreducible π) (s : NState π F w) (n : ℕ) :
    (s.iter hπ n).lvl = 2 ^ n * s.lvl := by
  induction n with
  | zero => simp [NState.iter]
  | succ n ih => rw [NState.iter, NState.next_lvl, ih, pow_succ]; ring

/-- The surplus grows past every level: `jₙ = 2ⁿ j₀ ≥ n + 1`. -/
theorem NState.lt_iter_lvl (hπ : Irreducible π) (s : NState π F w) (n : ℕ) :
    n < (s.iter hπ n).lvl := by
  rw [NState.iter_lvl]
  calc n < 2 ^ n := Nat.lt_two_pow_self
    _ = 2 ^ n * 1 := (mul_one _).symm
    _ ≤ 2 ^ n * s.lvl := Nat.mul_le_mul_left _ s.lvl_pos

theorem NState.iter_lvl_mono (hπ : Irreducible π) (s : NState π F w) {m n : ℕ} (h : m ≤ n) :
    (s.iter hπ m).lvl ≤ (s.iter hπ n).lvl := by
  rw [NState.iter_lvl, NState.iter_lvl]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) h)

/-- **The Cauchy estimate.** All later points agree with the `m`-th one to `π ^ (w + jₘ)`. -/
theorem NState.iter_dist (hπ : Irreducible π) (s : NState π F w) {m n : ℕ} (h : m ≤ n) :
    π ^ (w + (s.iter hπ m).lvl) ∣ (s.iter hπ n).pt - (s.iter hπ m).pt := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hsplit : (s.iter hπ (n + 1)).pt - (s.iter hπ m).pt
        = ((s.iter hπ (n + 1)).pt - (s.iter hπ n).pt) + ((s.iter hπ n).pt - (s.iter hπ m).pt) := by
      ring
    rw [hsplit]
    refine dvd_add ?_ ih
    refine dvd_trans (pow_dvd_pow π ?_) ((s.iter hπ n).next_dist hπ)
    have := NState.iter_lvl_mono hπ s hmn
    omega

end Iterate

/-! ## Valuation dictionary -/

section Dictionary

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open IsDiscreteValuationRing hiding maximalIdeal

/-- `𝔪 ^ n = (π ^ n)` for a uniformizer `π`. -/
theorem maximalIdeal_pow_eq_span {π : O} (hπ : Irreducible π) (n : ℕ) :
    (maximalIdeal O) ^ n = Ideal.span {π ^ n} := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- The `SModEq` form of `π ^ n ∣ x - y`, in the shape `IsAdicComplete` wants. -/
theorem smodEq_of_dvd {π : O} (hπ : Irreducible π) {x y : O} {n : ℕ} (h : π ^ n ∣ x - y) :
    x ≡ y [SMOD ((maximalIdeal O) ^ n • ⊤ : Ideal O)] := by
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem,
    maximalIdeal_pow_eq_span hπ, Ideal.mem_span_singleton]
  exact h

/-- The converse of `smodEq_of_dvd`. -/
theorem dvd_of_smodEq {π : O} (hπ : Irreducible π) {x y : O} {n : ℕ}
    (h : x ≡ y [SMOD ((maximalIdeal O) ^ n • ⊤ : Ideal O)]) : π ^ n ∣ x - y := by
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem,
    maximalIdeal_pow_eq_span hπ, Ideal.mem_span_singleton] at h
  exact h

/-- `v(a) = n` in the `addVal` sense is the same as `a = π ^ n · unit`. -/
theorem exists_unit_mul_pow_of_addVal_eq {π : O} (hπ : Irreducible π) {a : O} {n : ℕ}
    (h : addVal O a = (n : ℕ∞)) : ∃ u : Oˣ, a = π ^ n * u := by
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, addVal_zero] at h
    exact (ENat.top_ne_coe n) h
  obtain ⟨m, v, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  have hm : (m : ℕ∞) = (n : ℕ∞) := by rw [← addVal_def' v hπ m]; exact h
  have hmn : m = n := by exact_mod_cast hm
  exact ⟨v, by rw [hmn]; ring⟩

/-- `π ^ n ∣ a` is the same as `v(a) ≥ n`. -/
theorem pow_dvd_iff_le_addVal {π : O} (hπ : Irreducible π) {a : O} {n : ℕ} :
    π ^ n ∣ a ↔ (n : ℕ∞) ≤ addVal O a := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]

end Dictionary

/-! ## The theorem -/

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open IsDiscreteValuationRing hiding maximalIdeal

/-- **STRONG HENSEL, uniqueness.** In the open disc `v(s - x₀) > w = v(F'(x₀))` a root is unique.
No completeness is needed for this half, and no monicity. -/
theorem root_unique_of_strongHensel {π : O} (hπ : Irreducible π) {F : Polynomial O} {x₀ : O}
    {w : ℕ} (hd : ∃ u : Oˣ, F.derivative.eval x₀ = π ^ w * u) {r s : O}
    (hr : F.eval r = 0) (hs : F.eval s = 0)
    (hdr : π ^ (w + 1) ∣ r - x₀) (hds : π ^ (w + 1) ∣ s - x₀) : s = r := by
  obtain ⟨u, hu⟩ := hd
  obtain ⟨t, ht⟩ := sub_dvd_eval_sub r x₀ F.derivative
  obtain ⟨e, he⟩ : π ^ (w + 1) ∣ s - r := by
    have hsr : s - r = (s - x₀) - (r - x₀) := by ring
    rw [hsr]; exact dvd_sub hds hdr
  obtain ⟨b, hb⟩ := hdr
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add F r (s - r)
  rw [show r + (s - r) = s by ring] at hc
  -- the derivative at `r` still has valuation exactly `w`
  have hder : F.derivative.eval r = π ^ w * (u : O) + π ^ (w + 1) * b * t := by
    linear_combination ht + hu + t * hb
  have hkey : F.derivative.eval r + c * (s - r) = π ^ w * ((u : O) + π * (b * t + c * e)) := by
    rw [hder, he]; ring
  have hunit : IsUnit ((u : O) + π * (b * t + c * e)) := by
    refine isUnit_add_of_mem_maximalIdeal u.isUnit ?_
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact Dvd.intro _ rfl
  have hzero : (s - r) * (F.derivative.eval r + c * (s - r)) = 0 := by
    linear_combination hc - hr + hs
  rw [hkey] at hzero
  have hne : π ^ w * ((u : O) + π * (b * t + c * e)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hunit.ne_zero
  rcases mul_eq_zero.1 hzero with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne

variable [IsAdicComplete (maximalIdeal O) O]

/-- **STRONG HENSEL, existence.** `F'(x₀)` of valuation exactly `w`, `F(x₀)` of valuation at least
`k > 2w` ⟹ a root at distance at least `k - w`. No monicity, no degree hypothesis, no restriction
on the residue characteristic; `w = 0` is ordinary Hensel. -/
theorem exists_root_of_strongHensel {π : O} (hπ : Irreducible π) {F : Polynomial O} {x₀ : O}
    {w k : ℕ} (hd : ∃ u : Oˣ, F.derivative.eval x₀ = π ^ w * u) (hv : π ^ k ∣ F.eval x₀)
    (hk : 2 * w < k) :
    ∃ r : O, F.eval r = 0 ∧ π ^ (k - w) ∣ r - x₀ := by
  classical
  have hj₀ : 1 ≤ k - 2 * w := by omega
  have hkj : 2 * w + (k - 2 * w) = k := by omega
  let s₀ : NState π F w := ⟨x₀, k - 2 * w, hj₀, hd, by rw [hkj]; exact hv⟩
  set c : ℕ → O := fun n => (s₀.iter hπ n).pt with hcdef
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → c m ≡ c n [SMOD ((maximalIdeal O) ^ m • ⊤ : Ideal O)] := by
    intro m n hmn
    refine smodEq_of_dvd hπ (dvd_sub_comm.mp ?_)
    have hle : m ≤ w + (s₀.iter hπ m).lvl := by
      have := NState.lt_iter_lvl hπ s₀ m; omega
    exact dvd_trans (pow_dvd_pow π hle) (NState.iter_dist hπ s₀ hmn)
  obtain ⟨r, hr⟩ := IsPrecomplete.prec' c hcauchy
  have hrd : ∀ n : ℕ, π ^ n ∣ c n - r := fun n => dvd_of_smodEq hπ (hr n)
  have hroot : F.eval r = 0 := by
    refine IsHausdorff.haus' (I := maximalIdeal O) _ ?_
    intro n
    refine smodEq_of_dvd hπ ?_
    have h1 : π ^ n ∣ F.eval (c n) - F.eval r :=
      dvd_trans (hrd n) (sub_dvd_eval_sub (c n) r F)
    have h2 : π ^ n ∣ F.eval (c n) := by
      refine dvd_trans (pow_dvd_pow π ?_) (s₀.iter hπ n).vdvd
      have := NState.lt_iter_lvl hπ s₀ n; omega
    have h3 : π ^ n ∣ F.eval r := by
      have h4 := dvd_sub h2 h1
      rwa [show F.eval (c n) - (F.eval (c n) - F.eval r) = F.eval r by ring] at h4
    simpa using h3
  refine ⟨r, hroot, ?_⟩
  set N := k - w with hN
  have hNeq : w + (s₀.iter hπ 0).lvl = N := by
    show w + (k - 2 * w) = N
    omega
  have hfar : π ^ N ∣ c N - x₀ := by
    have h5 := NState.iter_dist hπ s₀ (Nat.zero_le N)
    rw [hNeq] at h5
    exact h5
  have hsplit : r - x₀ = -(c N - r) + (c N - x₀) := by ring
  rw [hsplit]
  exact dvd_add (dvd_neg.2 (hrd N)) hfar

/-- **STRONG HENSEL** (divisibility form): existence at distance `k - w`, uniqueness in the disc
of radius `> w`. -/
theorem strongHensel {π : O} (hπ : Irreducible π) {F : Polynomial O} {x₀ : O} {w k : ℕ}
    (hd : ∃ u : Oˣ, F.derivative.eval x₀ = π ^ w * u) (hv : π ^ k ∣ F.eval x₀) (hk : 2 * w < k) :
    ∃ r : O, F.eval r = 0 ∧ π ^ (k - w) ∣ r - x₀ ∧
      ∀ s : O, F.eval s = 0 → π ^ (w + 1) ∣ s - x₀ → s = r := by
  obtain ⟨r, hroot, hdist⟩ := exists_root_of_strongHensel hπ hd hv hk
  have hdr : π ^ (w + 1) ∣ r - x₀ := dvd_trans (pow_dvd_pow π (by omega)) hdist
  exact ⟨r, hroot, hdist, fun s hs hds => root_unique_of_strongHensel hπ hd hroot hs hdr hds⟩

/-- **STRONG HENSEL** in the ledger's `addVal` phrasing (`HYP.04`): if
`v(F(x₀)) > 2 · v(F'(x₀)) = 2w` then `F` has a root `r` with `v(r - x₀) > w`, and `r` is the only
root at distance `> w` from `x₀`. -/
theorem strongHensel_addVal {π : O} (hπ : Irreducible π) {F : Polynomial O} {x₀ : O} {w : ℕ}
    (hw : addVal O (F.derivative.eval x₀) = (w : ℕ∞))
    (hgt : ((2 * w : ℕ) : ℕ∞) < addVal O (F.eval x₀)) :
    ∃ r : O, F.eval r = 0 ∧ (w : ℕ∞) < addVal O (r - x₀) ∧
      ∀ s : O, F.eval s = 0 → (w : ℕ∞) < addVal O (s - x₀) → s = r := by
  have hd : ∃ u : Oˣ, F.derivative.eval x₀ = π ^ w * u := exists_unit_mul_pow_of_addVal_eq hπ hw
  -- the divisibility form of "distance `> w`"
  have hdisc : ∀ s : O, ((w : ℕ∞) < addVal O (s - x₀)) ↔ π ^ (w + 1) ∣ s - x₀ := by
    intro s
    rw [pow_dvd_iff_le_addVal hπ]
    constructor
    · intro h; exact Order.add_one_le_of_lt (by exact_mod_cast h)
    · intro h
      refine lt_of_lt_of_le ?_ (by exact_mod_cast h)
      exact_mod_cast Nat.lt_succ_self w
  by_cases h0 : F.eval x₀ = 0
  · refine ⟨x₀, h0, ?_, ?_⟩
    · simp
    · intro s hs hsd
      exact root_unique_of_strongHensel hπ hd h0 hs (by simp) ((hdisc s).1 hsd)
  · have hne : addVal O (F.eval x₀) ≠ ⊤ := by
      rw [Ne, addVal_eq_top_iff]; exact h0
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    have hvk : π ^ k ∣ F.eval x₀ := (pow_dvd_iff_le_addVal hπ).2 (le_of_eq hk)
    have hkk : 2 * w < k := by
      rw [← hk] at hgt; exact_mod_cast hgt
    obtain ⟨r, hroot, hdist, huniq⟩ := strongHensel hπ hd hvk hkk
    refine ⟨r, hroot, ?_, fun s hs hsd => huniq s hs ((hdisc s).1 hsd)⟩
    refine (hdisc r).2 (dvd_trans (pow_dvd_pow π (by omega)) hdist)

end Main

/-! ## Non-vacuity gate

The hypotheses of `strongHensel` are satisfiable for **every** `w`, over **every** base in the
bundle, with `F(x₀) ≠ 0` — so the theorem is not a statement about an empty situation, and the
`w ≥ 1` regime that mathlib's general-DVR Hensel cannot reach is genuinely occupied. The witness is
characteristic-free (no `2` is inverted):

    F = (X - π^(2w+1)) * (X + π^w) ,     x₀ = 0 ,
    F'(0) = π^w * (1 - π^(w+1))          (valuation exactly w) ,
    F(0)  = -π^(3w+1) ≠ 0                (valuation 3w+1 > 2w) ,

and the theorem returns the *deep* root `π^(2w+1)`, rejecting the shallow root `-π^w` (which sits
at distance exactly `w`, outside the uniqueness disc). -/
section Gate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The gate polynomial `(X - π^(2w+1))·(X + π^w)`. -/
noncomputable def gatePoly (π : O) (w : ℕ) : Polynomial O :=
  (X - C (π ^ (2 * w + 1))) * (X + C (π ^ w))

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem gatePoly_derivative_eval_zero (π : O) (w : ℕ) :
    (gatePoly π w).derivative.eval 0 = π ^ w - π ^ (2 * w + 1) := by
  simp only [gatePoly, derivative_mul, derivative_sub, derivative_add, derivative_X,
    derivative_C, eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_one, eval_zero,
    zero_sub, zero_add, one_mul, sub_zero]
  ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem gatePoly_eval_zero (π : O) (w : ℕ) :
    (gatePoly π w).eval 0 = -(π ^ (3 * w + 1)) := by
  simp only [gatePoly, eval_mul, eval_sub, eval_add, eval_X, eval_C, zero_sub, zero_add]
  ring

theorem gate_der {π : O} (hπ : Irreducible π) (w : ℕ) :
    ∃ u : Oˣ, (gatePoly π w).derivative.eval 0 = π ^ w * u := by
  have hunit : IsUnit ((1 : O) + -(π ^ (w + 1))) := by
    refine isUnit_add_of_mem_maximalIdeal isUnit_one ?_
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton, dvd_neg]
    exact dvd_pow_self π (by omega)
  refine ⟨hunit.unit, ?_⟩
  rw [hunit.unit_spec, gatePoly_derivative_eval_zero]
  ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem gate_val {π : O} (w : ℕ) : π ^ (3 * w + 1) ∣ (gatePoly π w).eval 0 :=
  ⟨-1, by rw [gatePoly_eval_zero]; ring⟩

omit [IsDiscreteValuationRing O] in
theorem gate_eval_ne_zero {π : O} (hπ : Irreducible π) (w : ℕ) : (gatePoly π w).eval 0 ≠ 0 := by
  rw [gatePoly_eval_zero, neg_ne_zero]
  exact pow_ne_zero _ hπ.ne_zero

/-- **The gate fires**: `strongHensel` applied to `gatePoly` returns exactly the deep root
`π ^ (2w+1)`, at the predicted distance `k - w = 2w + 1`. -/
theorem gate_fires {π : O} (hπ : Irreducible π) [IsAdicComplete (maximalIdeal O) O] (w : ℕ) :
    -- (the completeness instance is used through `strongHensel`)
    ∃ r : O, (gatePoly π w).eval r = 0 ∧ π ^ (2 * w + 1) ∣ r - 0 ∧ r = π ^ (2 * w + 1) := by
  obtain ⟨r, hroot, hdist, huniq⟩ :=
    strongHensel hπ (gate_der hπ w) (gate_val (π := π) w) (by omega : 2 * w < 3 * w + 1)
  have hkw : 3 * w + 1 - w = 2 * w + 1 := by omega
  rw [hkw] at hdist
  refine ⟨r, hroot, hdist, ?_⟩
  have hs : (gatePoly π w).eval (π ^ (2 * w + 1)) = 0 := by simp [gatePoly]
  have hsd : π ^ (w + 1) ∣ π ^ (2 * w + 1) - 0 := by
    simpa using pow_dvd_pow π (by omega : w + 1 ≤ 2 * w + 1)
  exact (huniq _ hs hsd).symm

end Gate

/-! ## Axiom census -/

section AxCheck

open IsDiscreteValuationRing hiding maximalIdeal

#print axioms Uniformity.Hensel.newton_step
#print axioms Uniformity.Hensel.exists_root_of_strongHensel
#print axioms Uniformity.Hensel.root_unique_of_strongHensel
#print axioms Uniformity.Hensel.strongHensel
#print axioms Uniformity.Hensel.strongHensel_addVal
#print axioms Uniformity.Hensel.gate_fires

end AxCheck

end Hensel

end Uniformity
