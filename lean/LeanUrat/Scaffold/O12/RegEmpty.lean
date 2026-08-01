/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Family

/-!
# Scaffold/O12/RegEmpty — Theorem 3, Corollary D at 𝔅_n, InstancePin seam [BP_II units II-G1..G7]

Movement II (REG-p)-emptiness layer (blueprint `lean/blueprints/BP_II.md` §1.4;
source of mathematical truth: the verified leaf
`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`).

This file carries **unit II-G1**: `BnMember.toAbs`, packaging a 𝔅_n member as the
landed abstract solve table (`AbsSolveTable`, `MovesU/O12PoleFree.lean` §1), against
which the landed pole-free theorem `AbsSolveTable.regAt_primePow` fires.
Units II-G2..G7 extend this module.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)

/-- Package a 𝔅_n member as the landed abstract solve table (O12PoleFree.lean §1). -/
noncomputable def BnMember.toAbs {n : ℕ} (T : BnMember n) : AbsSolveTable where
  nBlocks := n + 1
  Phi     := fun e => T.booking.Phi e
  entries := fun e => T.entries e

/-! ## Unit II-G2: the ℛ-discipline at every member

Dets: at e ≤ 1 the guarded kernel vanishes, so Φ = 1 — trivially a nonzero
ℛ-unit; at e ≥ 2 the II-B3 forms `Phi_O1_eq`/`Phi_O2_eq`/`Phi_O2r_eq`/`Phi_O3_eq`
(Bookings.lean) rewrite Φ to the landed determinants, and the landed L7(iii)
units `detO1_unit`/`detO3_unit` (MovesU/O12PoleFree.lean) close the triple
(`detO2 = detO1` definitionally). Entries: Theorem 2
(`BnMember.entries_memRcyc`, unit II-R13). -/

/-- The ℛ-discipline holds at every member: dets are ℛ-units (II-B10 + landed
`detO1_unit`/`detO3_unit` + `Phi_one`), entries in ℛ (Theorem 2). -/
theorem BnMember.discipline {n : ℕ} (T : BnMember n) : T.toAbs.RcycDiscipline := by
  refine ⟨fun e => ?_, fun e g hg => T.entries_memRcyc e g hg⟩
  change T.booking.Phi (e : ℕ) ≠ 0 ∧ MemRcyc (T.booking.Phi (e : ℕ)) ∧
    MemRcyc (T.booking.Phi (e : ℕ))⁻¹
  by_cases he : (e : ℕ) ≤ 1
  · -- e ≤ 1: the guarded kernel is 0, Φ = 1
    have h1 : T.booking.Phi (e : ℕ) = 1 := by
      simp [Booking.Phi, Booking.kernel, he]
    rw [h1, inv_one]
    exact ⟨one_ne_zero, LeanUrat.MovesU.memRcyc_one, LeanUrat.MovesU.memRcyc_one⟩
  · -- e ≥ 2: rewrite to the landed dets, fire the landed units
    have he2 : 2 ≤ (e : ℕ) := by omega
    have hE3 : 3 ≤ blockE (e : ℕ) := blockE_ge_three he2
    cases hb : T.booking with
    | O1 => rw [Phi_O1_eq he2]; exact LeanUrat.MovesU.detO1_unit (by omega)
    | O2 => rw [Phi_O2_eq he2]; exact LeanUrat.MovesU.detO1_unit (by omega)
    | O2r => rw [Phi_O2r_eq he2]; exact LeanUrat.MovesU.detO1_unit (by omega)
    | O3 => rw [Phi_O3_eq he2]; exact LeanUrat.MovesU.detO3_unit (by omega)

/-! ## Unit II-G4: Corollary D at 𝔅_n (the Step-17 (r1) margin numbers)

Route (per the blueprint's II-G4 dependency row): rewrite each booking's Φ_e as
the landed determinant (`detO1`/`detO2`/`detO3`, MovesU/O12PoleFree.lean) — the
II-B3 `Phi_*_eq` forms, carried here as `private` helpers pending their landing
in Bookings.lean — then fire the landed margins `detO1_margin`/`detO2_margin`/
`detO3_margin` with the II-C2 arithmetic (`blockE_ge_three`,
`two_le_blockE_sub_one`). -/

/-- `q^E − 1 ≠ 0` in `Qq` for `E ≥ 1` (evaluate at 0). -/
private theorem qX_pow_sub_one_ne_zero {E : ℕ} (hE : 1 ≤ E) : qX ^ E - 1 ≠ 0 := by
  have hX : (Polynomial.X ^ E - 1 : Polynomial ℚ) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval 0) h0
    simp [zero_pow (show E ≠ 0 by omega)] at h1
  have h : qX ^ E - 1 = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ E - 1) := by
    simp [qX]
  rw [h]
  exact RatFunc.algebraMap_ne_zero hX

/-- (O1): Φ = 1 − q·q^{−E} = (q^{E−1} − 1)/q^{E−1} = `detO1 (E − 1)`. -/
private theorem phi_O1_eq {e : ℕ} (he : 2 ≤ e) :
    Booking.O1.Phi e = detO1 (blockE e - 1) := by
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  have hdet : detO1 (blockE e - 1)
      = (qX ^ (blockE e - 1) - 1) / qX ^ (blockE e - 1) := by
    simp only [detO1, map_sub, map_pow, map_one, qX]
  rw [Booking.Phi, hdet]
  simp only [Booking.kernel, if_neg (show ¬ e ≤ 1 by omega)]
  set m := blockE e - 1 with hm
  rw [show blockE e = m + 1 by omega]
  have hq : qX ≠ 0 := qX_ne_zero
  have hpm : qX ^ m ≠ 0 := qX_pow_ne_zero m
  field_simp
  ring

/-- (O2): Φ = 1 − q^{−E} = (q^E − 1)/q^E = `detO2 E`. -/
private theorem phi_O2_eq {e : ℕ} (he : 2 ≤ e) :
    Booking.O2.Phi e = detO2 (blockE e) := by
  have hdet : detO2 (blockE e) = (qX ^ blockE e - 1) / qX ^ blockE e := by
    simp only [detO2, detO1, map_sub, map_pow, map_one, qX]
  rw [Booking.Phi, hdet]
  simp only [Booking.kernel, if_neg (show ¬ e ≤ 1 by omega)]
  have hp : qX ^ blockE e ≠ 0 := qX_pow_ne_zero _
  field_simp

/-- (O2′): same kernel as (O2), same determinant. -/
private theorem phi_O2r_eq {e : ℕ} (he : 2 ≤ e) :
    Booking.O2r.Phi e = detO2 (blockE e) := by
  have hdet : detO2 (blockE e) = (qX ^ blockE e - 1) / qX ^ blockE e := by
    simp only [detO2, detO1, map_sub, map_pow, map_one, qX]
  rw [Booking.Phi, hdet]
  simp only [Booking.kernel, if_neg (show ¬ e ≤ 1 by omega)]
  have hp : qX ^ blockE e ≠ 0 := qX_pow_ne_zero _
  field_simp

/-- (O3): Φ = 1 − (q−1)/(q^E−1) = q(q^{E−1} − 1)/(q^E − 1) = `detO3 E`. -/
private theorem phi_O3_eq {e : ℕ} (he : 2 ≤ e) :
    Booking.O3.Phi e = detO3 (blockE e) := by
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  have hdet : detO3 (blockE e)
      = (qX * (qX ^ (blockE e - 1) - 1)) / (qX ^ blockE e - 1) := by
    simp only [detO3, map_mul, map_sub, map_pow, map_one, qX]
  rw [Booking.Phi, hdet]
  simp only [Booking.kernel, if_neg (show ¬ e ≤ 1 by omega)]
  set m := blockE e - 1 with hm
  rw [show blockE e = m + 1 by omega]
  have h1 : qX ^ (m + 1) - 1 ≠ 0 := qX_pow_sub_one_ne_zero (by omega)
  field_simp
  ring

/-- **Corollary D at 𝔅_n** (the Step-17 (r1) margin numbers): per booking the det
values at every prime power obey the displayed lower bounds Φ ≥ 3/4 [O1],
7/8 [O2/O2′], 6/7 [O3] (and Φ₁ = 1). Reuses the landed `detO*_margin`. -/
theorem BnMember.detMargin {n : ℕ} (T : BnMember n) {e : ℕ} (he : 2 ≤ e)
    {x : ℚ} (hx : 2 ≤ x) :
    (match T.booking with
     | .O1 => (3:ℚ)/4 | .O2 => 7/8 | .O2r => 7/8 | .O3 => 6/7)
      ≤ (T.booking.Phi e).eval (RingHom.id ℚ) x := by
  cases hb : T.booking with
  | O1 =>
    rw [phi_O1_eq he]
    exact LeanUrat.MovesU.detO1_margin hx (two_le_blockE_sub_one he)
  | O2 =>
    rw [phi_O2_eq he]
    exact LeanUrat.MovesU.detO2_margin hx (blockE_ge_three he)
  | O2r =>
    rw [phi_O2r_eq he]
    exact LeanUrat.MovesU.detO2_margin hx (blockE_ge_three he)
  | O3 =>
    rw [phi_O3_eq he]
    exact LeanUrat.MovesU.detO3_margin hx (blockE_ge_three he)

end LeanUrat.Scaffold
