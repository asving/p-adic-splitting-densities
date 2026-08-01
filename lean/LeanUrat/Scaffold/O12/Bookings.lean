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

end LeanUrat.Scaffold
