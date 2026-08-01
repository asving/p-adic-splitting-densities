/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Core
import LeanUrat.MovesU.Defs

/-!
# Scaffold/O12/Bookings — the four bookings, Theorem 1, (SL≥2) [BP_II units II-B1..B12]

Movement II bookings (blueprint `lean/blueprints/BP_II.md` §1.2; source of
mathematical truth: the verified leaf `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§2.2, §2.4).

This file carries **unit II-B1**: the transcribed definitions `Booking`,
`Booking.kernel` (with the e ≤ 1 guard = 0), `Booking.Phi`, `Booking.solveU`.
Units II-B2..B12 (the kernel/Φ lemmas, the four `Phi_*_eq` landed-det forms, the
Theorem 1 solves, and the (SL≥2) statements) extend this module.

The `BookingSystem` structure (the §1.2 display consumed by II-B11/B12 and by the
𝔅_n coordinates of unit II-R12) is transcribed verbatim below as a prerequisite of
the wave-0c statement layer.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc detO1 detO2 detO3)

/-- The four kernel organizations (brief §2.4). `O2r` = (O2′). -/
inductive Booking | O1 | O2 | O2r | O3
  deriving DecidableEq, Fintype

/-- The 1×1 kernel scalar `K_e` per booking; block 1 (and the degenerate e = 0)
carries `K = 0` (brief §2.2: block 1 terminates immediately). -/
noncomputable def Booking.kernel (b : Booking) (e : ℕ) : Qq :=
  if e ≤ 1 then 0 else
  match b with
  | .O1  => qX * (qX ^ blockE e)⁻¹              -- κ₀ + κ₁ = q^{1−E}
  | .O2  => (qX ^ blockE e)⁻¹                   -- κ₀
  | .O2r => (qX ^ blockE e)⁻¹                   -- κ₀ (κ₁ re-fed as exit legs)
  | .O3  => (qX - 1) * (qX ^ blockE e - 1)⁻¹    -- κ₁/(1−κ₀)

noncomputable def Booking.Phi (b : Booking) (e : ℕ) : Qq := 1 - b.kernel e

/-- The booking's solve denominator `u` (Theorem 1(3)): `1 − q^{1−E}` for the three
re-entrant bookings, `1 − q^{−E}` for (O2). -/
noncomputable def Booking.solveU (b : Booking) (e : ℕ) : Qq :=
  match b with
  | .O2 => 1 - (qX ^ blockE e)⁻¹
  | _   => 1 - qX * (qX ^ blockE e)⁻¹

theorem Booking.kernel_one (b : Booking) : b.kernel 1 = 0 := by        -- K₁ = 0
  simp [Booking.kernel]

theorem Booking.Phi_one (b : Booking) : b.Phi 1 = 1 := by              -- Φ₁ = 1
  simp [Booking.Phi, Booking.kernel_one]

/-! Unit II-B3: Theorem 1(2), displayed forms — the four Φ's are the landed dets.
Mechanism: `1 − q^{1−E} = (q^{E−1} − 1)/q^{E−1}`, `1 − q^{−E} = (q^E − 1)/q^E`,
`1 − (q−1)/(q^E−1) = (q^E − q)/(q^E − 1) = q(q^{E−1}−1)/(q^E−1)`. -/

/-- Theorem 1(2), (O1): `Φ^{(O1)} = 1 − q^{1−E} = (q^{E−1} − 1)/q^{E−1}`. -/
theorem Phi_O1_eq {e : ℕ} (he : 2 ≤ e) : Booking.O1.Phi e = detO1 (blockE e - 1) := by
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  have hpow1 : qX ^ (blockE e - 1) ≠ 0 := qX_pow_ne_zero _
  -- split off one factor of q: `q^E = q · q^{E−1}`.
  have hsplit : qX ^ blockE e = qX * qX ^ (blockE e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hker : Booking.O1.kernel e = qX * (qX ^ blockE e)⁻¹ := by
    unfold Booking.kernel
    rw [if_neg (show ¬ e ≤ 1 by omega)]
  have hdet : detO1 (blockE e - 1)
      = (qX ^ (blockE e - 1) - 1) * (qX ^ (blockE e - 1))⁻¹ := by
    rw [detO1, div_eq_mul_inv]
    simp only [map_sub, map_pow, map_one]
    rfl
  rw [Booking.Phi, hker, hdet, hsplit, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ qX_ne_zero, one_mul, sub_mul, mul_inv_cancel₀ hpow1, one_mul]

/-- Theorem 1(2), (O2): `Φ^{(O2)} = 1 − q^{−E} = (q^E − 1)/q^E`. -/
theorem Phi_O2_eq {e : ℕ} (he : 2 ≤ e) : Booking.O2.Phi e = detO2 (blockE e) := by
  have hpow : qX ^ blockE e ≠ 0 := qX_pow_ne_zero _
  have hker : Booking.O2.kernel e = (qX ^ blockE e)⁻¹ := by
    unfold Booking.kernel
    rw [if_neg (show ¬ e ≤ 1 by omega)]
  have hdet : detO2 (blockE e) = (qX ^ blockE e - 1) * (qX ^ blockE e)⁻¹ := by
    rw [detO2, detO1, div_eq_mul_inv]
    simp only [map_sub, map_pow, map_one]
    rfl
  rw [Booking.Phi, hker, hdet, sub_mul, mul_inv_cancel₀ hpow, one_mul]

/-- Theorem 1(2), (O2′): same kernel as (O2), same landed det. -/
theorem Phi_O2r_eq {e : ℕ} (he : 2 ≤ e) : Booking.O2r.Phi e = detO2 (blockE e) := by
  have hpow : qX ^ blockE e ≠ 0 := qX_pow_ne_zero _
  have hker : Booking.O2r.kernel e = (qX ^ blockE e)⁻¹ := by
    unfold Booking.kernel
    rw [if_neg (show ¬ e ≤ 1 by omega)]
  have hdet : detO2 (blockE e) = (qX ^ blockE e - 1) * (qX ^ blockE e)⁻¹ := by
    rw [detO2, detO1, div_eq_mul_inv]
    simp only [map_sub, map_pow, map_one]
    rfl
  rw [Booking.Phi, hker, hdet, sub_mul, mul_inv_cancel₀ hpow, one_mul]

/-- Theorem 1(2), (O3): `Φ^{(O3)} = 1 − (q−1)/(q^E−1) = (q^E − q)/(q^E − 1)`. -/
theorem Phi_O3_eq {e : ℕ} (he : 2 ≤ e) : Booking.O3.Phi e = detO3 (blockE e) := by
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  -- `q^E − 1 ≠ 0`: it is the image of the 𝒮-member `X^E − 1` (E ≥ 1).
  have hsubne : qX ^ blockE e - 1 ≠ 0 := by
    have himg : qX ^ blockE e - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e - 1) := by
      simp [qX, map_sub, map_pow]
    rw [himg]
    exact RatFunc.algebraMap_ne_zero
      (MovesU.cycS_ne_zero (MovesU.Xpow_sub_one_mem_cycS (by omega)))
  -- split off one factor of q: `q^E = q · q^{E−1}`.
  have hsplit : qX ^ blockE e = qX * qX ^ (blockE e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hker : Booking.O3.kernel e = (qX - 1) * (qX ^ blockE e - 1)⁻¹ := by
    unfold Booking.kernel
    rw [if_neg (show ¬ e ≤ 1 by omega)]
  have hdet : detO3 (blockE e)
      = qX * (qX ^ (blockE e - 1) - 1) * (qX ^ blockE e - 1)⁻¹ := by
    rw [detO3, div_eq_mul_inv]
    simp only [map_mul, map_sub, map_pow, map_one]
    rfl
  -- the reduced numerator: `q·(q^{E−1} − 1) = q^E − q`.
  have hnum : qX * (qX ^ (blockE e - 1) - 1) = qX ^ blockE e - qX := by
    rw [hsplit]
    ring
  -- fold `1 − (q−1)·(q^E−1)⁻¹` into a single ratio over `q^E − 1`.
  have key : (1 : Qq) - (qX - 1) * (qX ^ blockE e - 1)⁻¹
      = (qX ^ blockE e - qX) * (qX ^ blockE e - 1)⁻¹ := by
    have hc : (qX ^ blockE e - 1) * (qX ^ blockE e - 1)⁻¹ = 1 := mul_inv_cancel₀ hsubne
    linear_combination -hc
  rw [Booking.Phi, hker, key, hdet, hnum]

/-! Unit II-B4: gcd(X^a − 1, X^b − 1) = X^gcd(a,b) − 1 in ℚ[X]. Euclidean
induction on (a, b): the division step is exact — for a > 0,
`(X^b − 1) % (X^a − 1) = X^(b % a) − 1` with quotient `Σ_{i < b/a} X^(a·i + b%a)`
(telescoping), so the polynomial Euclidean algorithm tracks `Nat.gcd`'s recursion
literally and the stated equality holds on the nose (the representative
`EuclideanDomain.gcd` computes IS `X^gcd(a,b) − 1`; both sides are monic-or-zero,
so no unit fudge survives). -/

/-- Division step: for `a > 0`, the Euclidean remainder of `X^b − 1` by `X^a − 1`
in ℚ[X] is exactly `X^(b % a) − 1`. -/
private lemma X_pow_sub_one_mod (a b : ℕ) (ha : 0 < a) :
    (Polynomial.X ^ b - 1 : Polynomial ℚ) % (Polynomial.X ^ a - 1)
      = Polynomial.X ^ (b % a) - 1 := by
  have hmonic : (Polynomial.X ^ a - 1 : Polynomial ℚ).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : ℚ) ha.ne'
  rw [← Polynomial.modByMonic_eq_mod _ hmonic]
  have hdega : (Polynomial.X ^ a - 1 : Polynomial ℚ).degree = a := by
    simpa using Polynomial.degree_X_pow_sub_C ha (1 : ℚ)
  have hdeg : (Polynomial.X ^ (b % a) - 1 : Polynomial ℚ).degree
      < (Polynomial.X ^ a - 1 : Polynomial ℚ).degree := by
    rw [hdega]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
    rw [Polynomial.degree_X_pow, Polynomial.degree_one]
    exact max_lt (by exact_mod_cast Nat.mod_lt b ha) (by exact_mod_cast ha)
  -- telescoping: (X^a − 1) · Σ_{i<b/a} X^(a·i + b%a) = X^b − X^(b%a)
  have key : (Polynomial.X ^ a - 1 : Polynomial ℚ)
        * ∑ i ∈ Finset.range (b / a), Polynomial.X ^ (a * i + b % a)
      = Polynomial.X ^ b - Polynomial.X ^ (b % a) := by
    rw [Finset.mul_sum]
    have htele := Finset.sum_range_sub
      (fun i => (Polynomial.X : Polynomial ℚ) ^ (a * i + b % a)) (b / a)
    calc ∑ i ∈ Finset.range (b / a),
            (Polynomial.X ^ a - 1 : Polynomial ℚ) * Polynomial.X ^ (a * i + b % a)
        = ∑ i ∈ Finset.range (b / a),
            ((Polynomial.X : Polynomial ℚ) ^ (a * (i + 1) + b % a)
              - Polynomial.X ^ (a * i + b % a)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sub_mul, one_mul, ← pow_add]
          ring_nf
      _ = Polynomial.X ^ (a * (b / a) + b % a) - Polynomial.X ^ (a * 0 + b % a) := htele
      _ = Polynomial.X ^ b - Polynomial.X ^ (b % a) := by
          rw [Nat.mul_zero, Nat.zero_add, Nat.div_add_mod b a]
  have hsum : (Polynomial.X ^ (b % a) - 1 : Polynomial ℚ)
      + (Polynomial.X ^ a - 1)
        * ∑ i ∈ Finset.range (b / a), Polynomial.X ^ (a * i + b % a)
      = Polynomial.X ^ b - 1 := by
    rw [key]; ring
  exact (Polynomial.div_modByMonic_unique _ _ hmonic ⟨hsum, hdeg⟩).2

/-- gcd(X^a − 1, X^b − 1) = X^gcd(a,b) − 1 in ℚ[X] (Theorem 1(2)'s gcd input).
[BP_II unit II-B4] -/
theorem gcd_X_pow_sub_one (a b : ℕ) :
    EuclideanDomain.gcd (Polynomial.X ^ a - 1) (Polynomial.X ^ b - 1)
      = (Polynomial.X ^ Nat.gcd a b - 1 : Polynomial ℚ)  -- up to unit normalization
    := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · rw [EuclideanDomain.gcd_val, X_pow_sub_one_mod a b ha,
        ih (b % a) (Nat.mod_lt b ha) a, ← Nat.gcd_rec]

/-- Theorem 1(2), (O3) reduced numerator: q^E − q = q(q^{E−1}−1), and after the
gcd = q−1 division the numerator is q·(1 + q + ⋯ + q^{E−2}). [BP_II unit II-B5] -/
theorem detO3_reduced {E : ℕ} (hE : 2 ≤ E) :
    (Polynomial.X ^ E - Polynomial.X : Polynomial ℚ)
      = (Polynomial.X - 1) * (Polynomial.X * ∑ i ∈ Finset.range (E - 1), Polynomial.X ^ i) := by
  obtain ⟨n, rfl⟩ : ∃ n, E = n + 1 := ⟨E - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h := geom_sum_mul (Polynomial.X : Polynomial ℚ) n
  linear_combination (-Polynomial.X : Polynomial ℚ) * h

/-! Unit II-B9: Theorem 1(1)'s scalar determinant identity + separated zero set. -/

/-- Theorem 1(1)'s scalar determinant identity. -/
theorem det_one_sub_scalar_id {k : ℕ} (κ : Qq) :
    ((1 : Matrix (Fin k) (Fin k) Qq) - κ • 1).det = (1 - κ) ^ k := by
  have h : (1 : Matrix (Fin k) (Fin k) Qq) - κ • 1 = (1 - κ) • 1 := by
    rw [sub_smul, one_smul]
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

/-- Presentation independence of the zero set requires a nonempty state type. -/
theorem det_one_sub_scalar_id_eq_zero_iff {k : ℕ} (hk : 0 < k) (κ : Qq) :
    ((1 : Matrix (Fin k) (Fin k) Qq) - κ • 1).det = 0 ↔ 1 - κ = 0 := by
  rw [det_one_sub_scalar_id]
  exact pow_eq_zero_iff hk.ne'

/-- A concrete transition presentation for one booking. `step e σ e' σ'` is an
actual system transition; kernel support is equivalent to existence of a same-block
transition, rather than being the definition of “self-loop”. -/
structure BookingSystem (n : ℕ) where
  booking : Booking
  step : ℕ → MovesU.SplittingType n → ℕ → MovesU.SplittingType n → Prop
  kernel_support :
    ∀ e, booking.kernel e ≠ 0 ↔
      ∃ σ σ', step e σ e σ'
  handoff_descent :
    ∀ {e σ e' σ'}, step e σ e' σ' → e' ≠ e → e' < e

/-! Unit II-B11: (SL≥2)(b)(c) — actual self-loops force block size ≥ 2, and every
block of size ≥ 2 has a genuinely nonzero kernel (e ≤ 1 gives kernel = 0 by the
definitional guard; for e ≥ 2 each booking's kernel is a nonzero q-power/quotient). -/

/-- (SL≥2)(b,c): every actual same-block transition lies in a block of size ≥ 2. -/
theorem selfloop_ge_two {n : ℕ} (S : BookingSystem n) {e : ℕ}
    (hloop : ∃ σ σ', S.step e σ e σ') : 2 ≤ e := by
  have hker : S.booking.kernel e ≠ 0 := (S.kernel_support e).mpr hloop
  by_contra h
  exact hker (by simp [Booking.kernel, show e ≤ 1 by omega])

theorem kernel_ne_zero (b : Booking) {e : ℕ} (he : 2 ≤ e) : b.kernel e ≠ 0 := by
  have hqX : qX ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hpow : qX ^ blockE e ≠ 0 := pow_ne_zero _ hqX
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  have hqX1 : qX - 1 ≠ 0 := by
    have h : qX - 1 = algebraMap (Polynomial ℚ) Qq (Polynomial.X - 1) := by
      simp [qX]
    rw [h]
    exact RatFunc.algebraMap_ne_zero (by simpa using Polynomial.X_sub_C_ne_zero (1 : ℚ))
  have hpow1 : qX ^ blockE e - 1 ≠ 0 := by
    have hX : (Polynomial.X ^ blockE e - 1 : Polynomial ℚ) ≠ 0 := by
      intro h0
      have h1 := congrArg (Polynomial.eval 0) h0
      simp [zero_pow (show blockE e ≠ 0 by omega)] at h1
    have h : qX ^ blockE e - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e - 1) := by
      simp [qX]
    rw [h]
    exact RatFunc.algebraMap_ne_zero hX
  unfold Booking.kernel
  rw [if_neg (show ¬ e ≤ 1 by omega)]
  cases b with
  | O1 => exact mul_ne_zero hqX (inv_ne_zero hpow)
  | O2 => exact inv_ne_zero hpow
  | O2r => exact inv_ne_zero hpow
  | O3 => exact mul_ne_zero hqX1 (inv_ne_zero hpow1)

/-- (SL≥2)(a): the concrete inter-block projection of `step` has no directed cycle. -/
theorem no_interblock_cycle {n : ℕ} (S : BookingSystem n) :
    ∀ e, ¬ Relation.TransGen
      (fun a b => ∃ σ σ', S.step a σ b σ' ∧ b ≠ a) e e := by
  intro e h
  -- Every inter-block edge strictly descends the block index.
  have hmono : ∀ a b : ℕ, (∃ σ σ', S.step a σ b σ' ∧ b ≠ a) → b < a := by
    rintro a b ⟨σ, σ', hstep, hne⟩
    exact S.handoff_descent hstep hne
  -- Hence the cycle transports to `TransGen (· > ·) e e`, which collapses to `e < e`.
  have h' : Relation.TransGen (fun a b : ℕ => b < a) e e :=
    Relation.TransGen.mono hmono h
  have hlt : ∀ a b : ℕ, Relation.TransGen (fun a b : ℕ => b < a) a b → b < a := by
    intro a b hab
    induction hab with
    | single hr => exact hr
    | tail _ hr ih => exact lt_trans hr ih
  exact lt_irrefl e (hlt e e h')

/-- Theorem 1(3), O1/O2′ solve: the balance equation has the displayed unique
solution. [BP_II unit II-B6] -/
theorem solve_O1_O2r {e : ℕ} (he : 2 ≤ e) (s x : Qq)
    (hbal : x = (kappa0 e + kappa1 e) * x + s) :
    x = s * (1 - qX * (qX ^ blockE e)⁻¹)⁻¹ := by
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  have hE1 : 1 ≤ blockE e - 1 := by omega
  have hqX : qX ≠ 0 := qX_ne_zero
  have hpow1 : qX ^ (blockE e - 1) ≠ 0 := qX_pow_ne_zero _
  -- `q^{E−1} − 1 ≠ 0`: it is the image of the 𝒮-member `X^{E−1} − 1` (E − 1 ≥ 1).
  have hsubne : qX ^ (blockE e - 1) - 1 ≠ 0 := by
    have himg : qX ^ (blockE e - 1) - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ (blockE e - 1) - 1) := by
      simp [qX, map_sub, map_pow]
    rw [himg]
    exact RatFunc.algebraMap_ne_zero
      (MovesU.cycS_ne_zero (MovesU.Xpow_sub_one_mem_cycS hE1))
  -- split off one factor of q: `q^E = q · q^{E−1}`.
  have hsplit : qX ^ blockE e = qX * qX ^ (blockE e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  -- hence the solve denominator `1 − q·q^{−E} = (q^{E−1} − 1)·(q^{E−1})⁻¹` is nonzero
  have hu : (1 : Qq) - qX * (qX ^ blockE e)⁻¹
      = (qX ^ (blockE e - 1) - 1) * (qX ^ (blockE e - 1))⁻¹ := by
    rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ hqX, one_mul, sub_mul,
      mul_inv_cancel₀ hpow1, one_mul]
  have hune : (1 : Qq) - qX * (qX ^ blockE e)⁻¹ ≠ 0 := by
    rw [hu]
    exact mul_ne_zero hsubne (inv_ne_zero hpow1)
  -- the balance gives x(1 − κ₀ − κ₁) = s; divide.
  rw [eq_mul_inv_iff_mul_eq₀ hune]
  rw [kappa_add] at hbal
  linear_combination hbal

/-- Theorem 1(3), O3 solve: multiplying through by 1 − κ₀ ≠ 0 gives the SAME
equation. [BP_II unit II-B7] -/
theorem solve_O3 {e : ℕ} (he : 2 ≤ e) (s x : Qq)
    (hbal : (1 - kappa1 e * (1 - kappa0 e)⁻¹) * x = s * (1 - kappa0 e)⁻¹) :
    x = s * (1 - qX * (qX ^ blockE e)⁻¹)⁻¹ := by
  have hE : 1 ≤ blockE e := by have := blockE_ge_three he; omega
  have hpow : qX ^ blockE e ≠ 0 := qX_pow_ne_zero _
  -- `q^E − 1 ≠ 0`: it is the image of the 𝒮-member `X^E − 1` (E ≥ 1).
  have hsubne : qX ^ blockE e - 1 ≠ 0 := by
    have himg : qX ^ blockE e - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e - 1) := by
      simp [qX, map_sub, map_pow]
    rw [himg]
    exact RatFunc.algebraMap_ne_zero
      (MovesU.cycS_ne_zero (MovesU.Xpow_sub_one_mem_cycS hE))
  -- `1 − κ₀ = (q^E − 1)·q^{−E} ≠ 0`
  have h1k : (1 : Qq) - kappa0 e ≠ 0 := by
    rw [kappa0]
    have hu : (qX ^ blockE e - 1) * (qX ^ blockE e)⁻¹
        = (1 : Qq) - (qX ^ blockE e)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hpow, one_mul]
    rw [← hu]
    exact mul_ne_zero hsubne (inv_ne_zero hpow)
  -- multiply the balance through by 1 − κ₀: recover II-B6's equation
  have h : (1 - kappa1 e * (1 - kappa0 e)⁻¹) * x * (1 - kappa0 e)
      = s * (1 - kappa0 e)⁻¹ * (1 - kappa0 e) := by rw [hbal]
  have hinv : (1 - kappa0 e)⁻¹ * (1 - kappa0 e) = 1 := inv_mul_cancel₀ h1k
  have hbal' : x = (kappa0 e + kappa1 e) * x + s := by
    linear_combination h + (kappa1 e * x + s) * hinv
  exact solve_O1_O2r he s x hbal'

/-- Theorem 1(3), O2 solve: no feedback, genuine division by 1 − κ₀. -/
theorem solve_O2 {e : ℕ} (he : 2 ≤ e) (t x : Qq) (hbal : x = kappa0 e * x + t) :
    x = t * (1 - (qX ^ blockE e)⁻¹)⁻¹ := by
  -- `E_e ≥ 1` for `e ≥ 2` (unit II-C1's `blockE`).
  have hE : 1 ≤ blockE e := by
    have h6 : 2 * 3 ≤ e * (e + 1) := Nat.mul_le_mul he (by omega)
    have h2 : 1 * 2 ≤ e * (e + 1) := by omega
    exact (Nat.le_div_iff_mul_le (by omega)).mpr h2
  have hqX : qX ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hpow : qX ^ blockE e ≠ 0 := pow_ne_zero _ hqX
  -- `q^E − 1 ≠ 0`: it is the image of the 𝒮-member `X^E − 1` (E ≥ 1).
  have hsubne : qX ^ blockE e - 1 ≠ 0 := by
    have himg : qX ^ blockE e - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e - 1) := by
      simp [qX, map_sub, map_pow]
    rw [himg]
    exact RatFunc.algebraMap_ne_zero
      (MovesU.cycS_ne_zero (MovesU.Xpow_sub_one_mem_cycS hE))
  -- hence the solve denominator `1 − κ₀ = (q^E − 1)·q^{−E}` is nonzero
  have hune : (1 : Qq) - (qX ^ blockE e)⁻¹ ≠ 0 := by
    have hu : (qX ^ blockE e - 1) * (qX ^ blockE e)⁻¹
        = (1 : Qq) - (qX ^ blockE e)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hpow, one_mul]
    rw [← hu]
    exact mul_ne_zero hsubne (inv_ne_zero hpow)
  -- the balance gives x(1 − κ₀) = t; divide.
  rw [eq_mul_inv_iff_mul_eq₀ hune]
  simp only [kappa0] at hbal
  linear_combination hbal

/-! Unit II-B10: (SL≥2) unit half. Mechanism: rewrite the solve denominator via the
II-B3 landed-det forms (`1 − q^{1−E} = detO1 (E−1)`, `1 − q^{−E} = detO2 E = detO1 E`),
then invoke the corpus `unit_of_cycS_ratio` through `detO1_unit`. -/

/-- (SL≥2), unit half: for 2 ≤ e the solve denominator is a nonzero ℛ-unit (L7(iii)).
[BP_II unit II-B10] -/
theorem solveU_unit (b : Booking) {e : ℕ} (he : 2 ≤ e) :
    b.solveU e ≠ 0 ∧ MemRcyc (b.solveU e) ∧ MemRcyc (b.solveU e)⁻¹ := by
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  -- the re-entrant denominator is the landed det `detO1 (E − 1)` (II-B3, O1 form)
  have hO1 : (1 : Qq) - qX * (qX ^ blockE e)⁻¹ = detO1 (blockE e - 1) := by
    have hker : Booking.O1.kernel e = qX * (qX ^ blockE e)⁻¹ := by
      unfold Booking.kernel
      rw [if_neg (show ¬ e ≤ 1 by omega)]
    rw [← Phi_O1_eq he, Booking.Phi, hker]
  -- the (O2) denominator is the landed det `detO2 E = detO1 E` (II-B3, O2 form)
  have hO2 : (1 : Qq) - (qX ^ blockE e)⁻¹ = detO2 (blockE e) := by
    have hker : Booking.O2.kernel e = (qX ^ blockE e)⁻¹ := by
      unfold Booking.kernel
      rw [if_neg (show ¬ e ≤ 1 by omega)]
    rw [← Phi_O2_eq he, Booking.Phi, hker]
  cases b with
  | O1 =>
      have h : Booking.O1.solveU e = detO1 (blockE e - 1) := hO1
      rw [h]; exact MovesU.detO1_unit (by omega)
  | O2 =>
      have h : Booking.O2.solveU e = detO2 (blockE e) := hO2
      rw [h]; exact MovesU.detO1_unit (by omega)
  | O2r =>
      have h : Booking.O2r.solveU e = detO1 (blockE e - 1) := hO1
      rw [h]; exact MovesU.detO1_unit (by omega)
  | O3 =>
      have h : Booking.O3.solveU e = detO1 (blockE e - 1) := hO1
      rw [h]; exact MovesU.detO1_unit (by omega)

end LeanUrat.Scaffold
