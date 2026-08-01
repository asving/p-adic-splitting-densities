/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H5.Kernels
import LeanUrat.Scaffold.O12.Substochastic

/-!
# Scaffold/HDischarge/H5/PackI — (PACK-i) block form [HDISCHARGE_H5 units P0, P1]

Statements VERBATIM from `lean/blueprints/HDISCHARGE_H5.md` §4.6, rows P0/P1
(REVISION 2: P0 moved to Wave 1 and split at the r2 probe — B1 consumes the
pivot positivity; kernel-independent, deps W0 only. P1 probed at r2, the r1
PROBE-OWED tag cleared; redundant `hui` binder dropped).

Unit P0 (both halves):
* `solveU_mem_OKat` — the solve denominator `u` is evaluation-regular at every
  q₀ ≥ 2: `u ∈ ℛ = ℚ[q][𝒮⁻¹]` by closure (`1`, `qX`, `(qX^E)⁻¹` are all ℛ
  members), then the K1 bridge `memRcyc_mem_OKat`.
* `solveU_eval_pos` — the Corollary-D scalar margin: for the re-entrant
  bookings `u = 1 − q·q^{−E}`, so eval = 1 − q₀^{1−E} ≥ 3/4 > 0 via
  `blockE_ge_three` arithmetic, fired through the landed
  `bn_substochastic_margin` at the (O1) kernel shape.

Unit P1: `beta_eval_solve` — solve-evaluation commutation at the 𝔅_n rows (the
(PACK-i) BLOCK form): the member's solve `β = u⁻¹·t` commutes with `evalAt`.
Route: rewrite `hsolve`, `map_mul` of `evalAt`, K3 (`evalAt_inv`); the u⁻¹
membership K3 needs is supplied inside the proof from `hu.2.2` + K1. SEAM NOTE
(blueprint §2.2): the K2 chain-vocabulary form (`RS4Chain.rsh_interp` at the
real instance) rides the chain-instance seam — NEVER claimed here.
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType memRcyc_one memRcyc_algebraMap
  memRcyc_inv_cycS Xpow_mem_cycS)
open LeanUrat.MovesS (OKat evalAt)

set_option linter.unusedVariables false in
/-- **Unit P0, first half**: the booking's solve denominator `u` lies in the
evaluation-regular subring `OKat q₀` at every rational q₀ ≥ 2 — `u` is an
ℛ-member (`1 − q·q^{−E}`, resp. `1 − q^{−E}` at (O2)), so the K1 bridge
`memRcyc_mem_OKat` applies. (`he` is carried by the VERBATIM blueprint
statement; membership needs no lower bound on e, so it is unused here.)
[HDISCHARGE_H5 unit P0] -/
theorem solveU_mem_OKat {e : ℕ} (he : 2 ≤ e) (b : Booking) {q₀ : ℚ}
    (hq : 2 ≤ q₀) : b.solveU e ∈ OKat q₀ := by
  have hqX : MemRcyc qX := by
    simpa [qX] using memRcyc_algebraMap Polynomial.X
  have hinv : MemRcyc (qX ^ blockE e)⁻¹ := by
    have h := memRcyc_inv_cycS (Xpow_mem_cycS (blockE e))
    simpa [qX, map_pow] using h
  have hrc : MemRcyc (b.solveU e) := by
    cases b with
    | O1 => exact memRcyc_one.sub (hqX.mul hinv)
    | O2 => exact memRcyc_one.sub hinv
    | O2r => exact memRcyc_one.sub (hqX.mul hinv)
    | O3 => exact memRcyc_one.sub (hqX.mul hinv)
  exact memRcyc_mem_OKat hrc hq

/-- **Unit P0, second half** (the pivot positivity B1 consumes): at every
re-entrant booking the solve denominator evaluates positively at q₀ ≥ 2 —
`u = 1 − q·q^{−E}` evaluates to `1 − q₀^{1−E} ≥ 3/4` (the Corollary-D scalar
margin via `bn_substochastic_margin` at the (O1) kernel shape, E ≥ 3 by
`blockE_ge_three`). [HDISCHARGE_H5 unit P0] -/
theorem solveU_eval_pos {e : ℕ} (he : 2 ≤ e) (b : Booking)
    (hb : b ≠ Booking.O2) {q₀ : ℚ} (hq : 2 ≤ q₀)
    (h : b.solveU e ∈ OKat q₀) : 0 < evalAt q₀ ⟨b.solveU e, h⟩ := by
  have hne : ¬ e ≤ 1 := by omega
  -- the (O1) kernel at e ≥ 2 is exactly the re-entrant `q·q^{−E}` scalar
  have hker : Booking.O1.kernel e = qX * (qX ^ blockE e)⁻¹ := by
    unfold Booking.kernel
    rw [if_neg hne]
  -- for b ≠ O2, `u = 1 − K_e^{(O1)}`
  have hsolve : b.solveU e = 1 - Booking.O1.kernel e := by
    rw [hker]
    cases b with
    | O1 => rfl
    | O2 => exact absurd rfl hb
    | O2r => rfl
    | O3 => rfl
  -- kernel membership from `u`'s: K = 1 − u
  have hkmem : Booking.O1.kernel e ∈ OKat q₀ := by
    have hmem := (OKat q₀).sub_mem ((OKat q₀).one_mem) h
    rw [hsolve, sub_sub_cancel] at hmem
    exact hmem
  -- transport the subtype element through the identity `u = 1 − K`
  have hcast : (⟨b.solveU e, h⟩ : OKat q₀)
      = 1 - ⟨Booking.O1.kernel e, hkmem⟩ := by
    apply Subtype.ext
    simpa using hsolve
  -- the Corollary-D margin: eval K ≤ 1/4 at q₀ ≥ 2, E ≥ 3
  have hmargin : (Booking.O1.kernel e).eval (RingHom.id ℚ) q₀ ≤ 1 / 4 := by
    have hm := bn_substochastic_margin Booking.O1 he hq
    norm_num at hm
    exact hm
  have hkev : evalAt q₀ (⟨Booking.O1.kernel e, hkmem⟩ : OKat q₀)
      = (Booking.O1.kernel e).eval (RingHom.id ℚ) q₀ := rfl
  rw [hcast, map_sub, map_one, hkev]
  linarith

/-- **Unit P1** (the (PACK-i) block form): solve-evaluation commutation at the
𝔅_n rows — the member's solve `β_e(σ) = u⁻¹ · t_σ` commutes with the `evalAt`
ring hom at every rational q₀ ≥ 2 with nonvanishing pivot. Route: rewrite
`hsolve` through the subtype (`Subtype.ext`), `map_mul` of `evalAt`, then K3
(`evalAt_inv`); the u⁻¹ membership K3 needs is supplied inside from `hu.2.2`
(the block's `MemRcyc u⁻¹` datum) + K1 (`memRcyc_mem_OKat`). The chain-vocabulary
form (`RS4Chain.rsh_interp`) is a NAMED SEAM (blueprint §2.2), not claimed here.
[HDISCHARGE_H5 unit P1] -/
theorem beta_eval_solve {n : ℕ} (T : BnMember n) {e : ℕ} (he : 2 ≤ e)
    {q₀ : ℚ} (hq : 2 ≤ q₀) (σ : SplittingType n)
    (hβ : T.β e σ ∈ OKat q₀) (ht : (T.blocks e he).trow σ ∈ OKat q₀)
    (hu : (T.blocks e he).u ∈ OKat q₀)
    (hne : evalAt q₀ ⟨(T.blocks e he).u, hu⟩ ≠ 0) :
    evalAt q₀ ⟨T.β e σ, hβ⟩
      = (evalAt q₀ ⟨(T.blocks e he).u, hu⟩)⁻¹
        * evalAt q₀ ⟨(T.blocks e he).trow σ, ht⟩ := by
  -- the u⁻¹ membership K3 needs, from the block's `hu.2.2` through K1
  have hui : (T.blocks e he).u⁻¹ ∈ OKat q₀ :=
    memRcyc_mem_OKat (T.blocks e he).hu.2.2 hq
  -- transport the solve identity `β = u⁻¹ · t` to the subtype carrier
  have hcast : (⟨T.β e σ, hβ⟩ : OKat q₀)
      = ⟨(T.blocks e he).u⁻¹, hui⟩ * ⟨(T.blocks e he).trow σ, ht⟩ := by
    apply Subtype.ext
    simpa using (T.blocks e he).hsolve σ
  -- `map_mul` of the `evalAt` ring hom, then K3 at the inverse leg
  rw [hcast, map_mul, evalAt_inv hu hui hne]

end LeanUrat.Scaffold.HDischarge.H5
