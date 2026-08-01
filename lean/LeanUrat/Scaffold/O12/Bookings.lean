/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Core

/-!
# Scaffold/O12/Bookings — the four bookings, Theorem 1, (SL≥2) [BP_II units II-B1..B12]

Movement II bookings (blueprint `lean/blueprints/BP_II.md` §1.2; source of
mathematical truth: the verified leaf `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§2.2, §2.4).

This file carries **unit II-B1**: the transcribed definitions `Booking`,
`Booking.kernel` (with the e ≤ 1 guard = 0), `Booking.Phi`, `Booking.solveU`.
Units II-B2..B12 (the kernel/Φ lemmas, the four `Phi_*_eq` landed-det forms, the
Theorem 1 solves, and the (SL≥2) statements) extend this module.
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

end LeanUrat.Scaffold
