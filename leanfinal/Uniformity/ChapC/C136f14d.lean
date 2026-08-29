/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136f14c

/-!
# Uniformity.ChapC.C136f14d — UNIT A24C: the SOURCE-faithful twisted carrier and the
constant-scalar transfer [A-C.24″ mechanism, 2026-08-28]

The third C.39 adjudication round's Lean leg.  SOURCE ARCHAEOLOGY (recorded in
`runs/wave-c/verdict_A24C.md`): EFF.HE6R1.39's constant per-side scalar is asserted
between the source's OWN level-2 residual polynomials, which CARRY the per-slot
normalizer twist — spec/EFF-HE7.md DEFINITION HE7-3's exponents, verbatim closed form
`c_t := (s(m₁ − t·u₂) + t·s(u₂) − s(m₁))/ℓ` at the side pin `m₁` (EFF.HE7.08's
convention "changing the choice multiplies its coefficients by explicit powers of β";
EFF.HE7.30 Step 2's `τ_t with res(τ_t) = β^{c_t} the explicit twist of §S1`; tooth
HE7-T-BADTWIST: dropping the twist mispredicts σ).  The enacted A-C.24′ row transcribed
the source conclusion onto the UNTWISTED anchored carrier, where the honest law is
F14C's slot-indexed family — the "missing stationarity" of F14C §2.2 is not a missing
hypothesis but the missing twist, and it is supplied IDENTICALLY by cocycle arithmetic.

## This file

* `twistExp L u₂ M₂ t` — DEFINITION HE7-3's twist exponents at the generic pin `M₂`,
  in the Lean-native cocycle-sum form
  `c₁(M₂ − t·u₂, t·u₂) + Σ_{i<t} c₁(u₂, i·u₂)`;
  `ell_mul_twistExp`-style closed form recovered by `twistExp` + `ell_mul_twistSum`.
* ★ `twistExp_cocycle_transfer` (ID1) — the SCALAR-TRANSFER identity
  `c₁(M₂,c) + ε_t(M₂) = c₁(M₂−t·u₂,c) + ε_t(M₂+c)`: converts F14C's slot-varying
  family over `dv2ResPolyAnch` into the source's CONSTANT pin-height scalar over the
  twisted carrier.  Pure cocycle arithmetic; no `ℓ ∣ u₂`, no stationarity premise.
* ★ `twistExp_cocycle_mul` (ID2) — the PRODUCT identity
  `c₁(Mg,Mz) + ε_{t₁}(Mg) + ε_{t₂}(Mz) = c₁(Mg−t₁u₂, Mz−t₂u₂) + ε_{t₁+t₂}(Mg+Mz)`:
  turns F14C's weighted convolution into the classical theorem-of-the-product shape
  over the twisted carrier.
* `dv2ResPolyTw` — the twisted carrier (the source's classical residual polynomial):
  coefficient `t` is `root^{twistExp} ·` the anchored coefficient.
* ★★ `dv2ResPolyTw_scalar_of_anch_family` — THE A-C.24″ MECHANISM: from the honest
  slot-indexed family over the anchored carrier (F14C's shape), the source display
  `R̃(f) = C(root^{c₁(M₂′, c)} · γ̂) · R̃(f_S)` — constant, pin-height exponent,
  byte-shaped as EFF.HE6R1.39's TERMINAL identification.
* ★★ `dv2ResPolyTw_mul_of_weightedConv` — the classical product law
  `R̃(g·z) = C(root^{c₁(Mg,Mz)}) · R̃(g) · R̃(z)` from F14C's weighted-convolution
  premise: the twisted carrier is THE multiplicative object.
* `dv2ResPolyTw_radical_eq_of_scalar`, `dv2ResPolyTw_coeff_eq_zero_iff`,
  `natDegree_dv2ResPolyTw_eq` — the F1.5 adapter and the Tw ↔ Anch degree/vanishing
  bridge (`root ≠ 0` in the stage field tower).

Numeric cross-check: `verification/a24b_anchor_battery.py` Part D (the F4 frame,
β of order 3): ID1/ID2/HE7-3-closed-form grids exact; the family holds 127/127 at the
unreduced slot level, the enacted constant fails at all 15 odd-`c_z` complements, the
source law over the twisted reads holds 127/127.

No landed or leanspec file is edited; `dv2ResPolyAnch` and all its consumers are
untouched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136f14d

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0 Uniformity.Density.Tower.C136l2e1
open Uniformity.Density.Tower.C136l2e2 Uniformity.Density.Tower.C136l2e3
open Uniformity.Density.Tower.C136f14b Uniformity.Density.Tower.C136f14c

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 0 — private plumbing (the standing local-twin convention: `shift_spec` /
`shift_unique` re-derived as in C136f14c; `s(0) = 0`) -/

private theorem shift_spec (L : LevelDatum F H₀ hpin) (m : ℕ) :
    L.shift m < L.ℓ ∧ L.shift m * L.u ≡ m [MOD L.ℓ] := by
  have hex : ∃ b ∈ (↑(Finset.range L.ℓ) : Set ℕ), b * L.u % L.ℓ = m % L.ℓ :=
    (Uniformity.Density.Induction.class_sep_bij L.hcop).surjOn (by
      simpa only [Finset.coe_range, Set.mem_Iio] using Nat.mod_lt m L.hℓ)
  have hnone : (List.range L.ℓ).find? (fun b => (b * L.u) % L.ℓ == m % L.ℓ) ≠ none := by
    intro hn
    obtain ⟨b, hb, hcong⟩ := hex
    simp only [Finset.coe_range, Set.mem_Iio] at hb
    exact (List.find?_eq_none.mp hn b (List.mem_range.mpr hb)) (by simpa using hcong)
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hnone
  have hval : L.shift m = c := by rw [LevelDatum.shift, hc]; rfl
  refine ⟨hval ▸ List.mem_range.mp (List.mem_of_find?_eq_some hc), ?_⟩
  have hp := List.find?_some hc
  simp only [beq_iff_eq] at hp
  rw [hval]
  exact hp

private theorem shift_unique (L : LevelDatum F H₀ hpin) {m b : ℕ}
    (hb : b < L.ℓ) (hcong : b * L.u ≡ m [MOD L.ℓ]) : b = L.shift m := by
  obtain ⟨hlt, hsp⟩ := shift_spec L m
  exact Uniformity.Density.Induction.class_sep L.hcop hb hlt (hcong.trans hsp.symm)

private theorem shift_zero (L : LevelDatum F H₀ hpin) : L.shift 0 = 0 :=
  (shift_unique L L.hℓ (by simp [Nat.ModEq])).symm

/-- Subadditivity of the shift (C.28's `hsum` step, exposed): the truncated
subtraction in `cocycle_mem`'s display is exact. -/
private theorem shift_add_le (L : LevelDatum F H₀ hpin) (a b : ℕ) :
    L.shift (a + b) ≤ L.shift a + L.shift b := by
  obtain ⟨hal, hac⟩ := shift_spec L a
  obtain ⟨hbl, hbc⟩ := shift_spec L b
  have hsum : (L.shift a + L.shift b) % L.ℓ = L.shift (a + b) := by
    refine shift_unique L (Nat.mod_lt _ L.hℓ) ?_
    calc ((L.shift a + L.shift b) % L.ℓ) * L.u
        ≡ (L.shift a + L.shift b) * L.u [MOD L.ℓ] := (Nat.mod_modEq _ L.ℓ).mul_right L.u
      _ = L.shift a * L.u + L.shift b * L.u := by ring
      _ ≡ a + b [MOD L.ℓ] := hac.add hbc
  calc L.shift (a + b) = (L.shift a + L.shift b) % L.ℓ := hsum.symm
    _ ≤ L.shift a + L.shift b := Nat.mod_le _ _

/-! ## Part 1 — the source's twist exponents (DEFINITION HE7-3 at the generic pin) -/

/-- **The twist exponents of the level-2 residual assembly** (SOURCE:
spec/EFF-HE7.md DEFINITION HE7-3, verbatim "let c_t := (s(d₂u₂ − tu₂) + t·s(u₂) −
s(d₂u₂))/ℓ be the twist exponents of §S1 at m₁ := d₂u₂" — here at the generic pin
`M₂`), in the exact cocycle-sum form.  `ell_mul_twistSum` + `cocycle_mem` recover the
closed form; the two are grid-identical in the battery's Part D oracle. -/
def twistExp (L : LevelDatum F H₀ hpin) (u₂ M₂ t : ℕ) : ℕ :=
  L.cocycle (M₂ - t * u₂) (t * u₂) + ∑ i ∈ Finset.range t, L.cocycle u₂ (i * u₂)

/-- The anchor slot is twist-free: `ε_0 = 0` (so the twisted and anchored carriers
share the well-definedness clause `coeff 0 = the exact pin read`). -/
theorem twistExp_zero (L : LevelDatum F H₀ hpin) (u₂ M₂ : ℕ) :
    twistExp L u₂ M₂ 0 = 0 := by
  unfold twistExp
  simp only [zero_mul, Nat.sub_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  have hc := (L.cocycle_mem M₂ 0).1
  simp only [add_zero] at hc
  have hs0 := shift_zero L
  refine Nat.eq_of_mul_eq_mul_left L.hℓ ?_
  omega

/-- The telescoped `Σ`-leg of the twist exponent:
`ℓ·Σ_{i<t} c₁(u₂, i·u₂) + s(t·u₂) = t·s(u₂) + s(0)`. -/
private theorem ell_mul_twistSum (L : LevelDatum F H₀ hpin) (u₂ t : ℕ) :
    L.ℓ * (∑ i ∈ Finset.range t, L.cocycle u₂ (i * u₂)) + L.shift (t * u₂)
      = t * L.shift u₂ + L.shift 0 := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hc := (L.cocycle_mem u₂ (n * u₂)).1
    have hsub := shift_add_le L u₂ (n * u₂)
    have he : u₂ + n * u₂ = (n + 1) * u₂ := by ring
    rw [he] at hc
    rw [he] at hsub
    have hr : (n + 1) * L.shift u₂ = n * L.shift u₂ + L.shift u₂ := by ring
    rw [Finset.sum_range_succ, mul_add]
    omega

/-- ★ **ID1 — the scalar-transfer identity** (machine cross-check: battery Part D
oracle, grid-exact).  `c₁(M₂, c) + ε_t(M₂) = c₁(M₂ − t·u₂, c) + ε_t(M₂ + c)`.
This is what F14C §2.2's "stationarity" actually is: not a new hypothesis but the
2-cocycle identity of `c₁` — the twist difference between the two pins absorbs the
slot-variation of the family weight EXACTLY. -/
theorem twistExp_cocycle_transfer (L : LevelDatum F H₀ hpin) {u₂ M₂ c t : ℕ}
    (htu : t * u₂ ≤ M₂) :
    L.cocycle M₂ c + twistExp L u₂ M₂ t
      = L.cocycle (M₂ - t * u₂) c + twistExp L u₂ (M₂ + c) t := by
  have key : L.cocycle M₂ c + L.cocycle (M₂ - t * u₂) (t * u₂)
      = L.cocycle (M₂ - t * u₂) c + L.cocycle (M₂ + c - t * u₂) (t * u₂) := by
    have h1 := (L.cocycle_mem M₂ c).1
    have h2 := (L.cocycle_mem (M₂ - t * u₂) (t * u₂)).1
    have h3 := (L.cocycle_mem (M₂ - t * u₂) c).1
    have h4 := (L.cocycle_mem (M₂ + c - t * u₂) (t * u₂)).1
    have s1 := shift_add_le L M₂ c
    have s2 := shift_add_le L (M₂ - t * u₂) (t * u₂)
    have s3 := shift_add_le L (M₂ - t * u₂) c
    have s4 := shift_add_le L (M₂ + c - t * u₂) (t * u₂)
    have e2 : M₂ - t * u₂ + t * u₂ = M₂ := by omega
    have e3 : M₂ - t * u₂ + c = M₂ + c - t * u₂ := by omega
    have e4 : M₂ + c - t * u₂ + t * u₂ = M₂ + c := by omega
    rw [e2] at h2 s2
    rw [e3] at h3 s3
    rw [e4] at h4 s4
    refine Nat.eq_of_mul_eq_mul_left L.hℓ ?_
    rw [mul_add, mul_add]
    omega
  unfold twistExp
  omega

/-- ★ **ID2 — the product identity** (machine cross-check: battery Part D oracle,
grid-exact).  `c₁(Mg, Mz) + ε_{t₁}(Mg) + ε_{t₂}(Mz) = c₁(Mg − t₁·u₂, Mz − t₂·u₂) +
ε_{t₁+t₂}(Mg + Mz)`: the antidiagonal weight of F14C's honest convolution equals the
single pin cocycle after passing to the twisted carrier. -/
theorem twistExp_cocycle_mul (L : LevelDatum F H₀ hpin) {u₂ Mg Mz t₁ t₂ : ℕ}
    (h1 : t₁ * u₂ ≤ Mg) (h2 : t₂ * u₂ ≤ Mz) :
    L.cocycle Mg Mz + twistExp L u₂ Mg t₁ + twistExp L u₂ Mz t₂
      = L.cocycle (Mg - t₁ * u₂) (Mz - t₂ * u₂)
        + twistExp L u₂ (Mg + Mz) (t₁ + t₂) := by
  have hs0 := shift_zero L
  have hS1 := ell_mul_twistSum L u₂ t₁
  have hS2 := ell_mul_twistSum L u₂ t₂
  have hS12 := ell_mul_twistSum L u₂ (t₁ + t₂)
  have c0 := (L.cocycle_mem Mg Mz).1
  have c1 := (L.cocycle_mem (Mg - t₁ * u₂) (t₁ * u₂)).1
  have c2 := (L.cocycle_mem (Mz - t₂ * u₂) (t₂ * u₂)).1
  have c3 := (L.cocycle_mem (Mg - t₁ * u₂) (Mz - t₂ * u₂)).1
  have c4 := (L.cocycle_mem (Mg + Mz - (t₁ + t₂) * u₂) ((t₁ + t₂) * u₂)).1
  have s0 := shift_add_le L Mg Mz
  have s1 := shift_add_le L (Mg - t₁ * u₂) (t₁ * u₂)
  have s2 := shift_add_le L (Mz - t₂ * u₂) (t₂ * u₂)
  have s3 := shift_add_le L (Mg - t₁ * u₂) (Mz - t₂ * u₂)
  have s4 := shift_add_le L (Mg + Mz - (t₁ + t₂) * u₂) ((t₁ + t₂) * u₂)
  have er : (t₁ + t₂) * u₂ = t₁ * u₂ + t₂ * u₂ := by ring
  have e1 : Mg - t₁ * u₂ + t₁ * u₂ = Mg := by omega
  have e2 : Mz - t₂ * u₂ + t₂ * u₂ = Mz := by omega
  have e3 : Mg - t₁ * u₂ + (Mz - t₂ * u₂) = Mg + Mz - (t₁ + t₂) * u₂ := by omega
  have e4 : Mg + Mz - (t₁ + t₂) * u₂ + (t₁ + t₂) * u₂ = Mg + Mz := by omega
  rw [e1] at c1 s1
  rw [e2] at c2 s2
  rw [e3] at c3 s3
  rw [e4] at c4 s4
  have hr : (t₁ + t₂) * L.shift u₂ = t₁ * L.shift u₂ + t₂ * L.shift u₂ := by ring
  refine Nat.eq_of_mul_eq_mul_left L.hℓ ?_
  unfold twistExp
  simp only [mul_add]
  omega

/-! ## Part 2 — the twisted carrier (the source's classical residual polynomial) -/

/-- ★ **The SOURCE-faithful twisted level-2 residual polynomial**: coefficient `t` is
`root^{ε_t} ·` the guarded/anchored coefficient — DEFINITION HE7-3's twist carried in
the object, exactly as the source's residual assembly does (EFF.HE7.30 Step 2).  Over
THIS carrier EFF.HE6R1.39's constant per-side scalar display is the faithful
transcription; over the untwisted `dv2ResPolyAnch` the same content is F14C's
slot-indexed family (`dv2ResPolyTw_scalar_of_anch_family` below is the exact bridge). -/
noncomputable def dv2ResPolyTw (L : LevelDatum F H₀ hpin) (Ψ f : Polynomial O)
    (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) (M₂ : ℕ)
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    Polynomial (AdjoinRoot L.r) :=
  (Finset.range (dv2SideDeg L Ψ f u₂ ℓ₂ hne + 1)).sum fun t =>
    Polynomial.C (AdjoinRoot.root L.r ^ twistExp L u₂ M₂ t
        * (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t)
      * Polynomial.X ^ t

/-- Unconditional coefficient extraction: the twisted coefficient is `root^{ε_t} ·` the
anchored one at EVERY `t` (beyond the side degree both vanish). -/
theorem dv2ResPolyTw_coeff (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) (t : ℕ) :
    (dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t
      = AdjoinRoot.root L.r ^ twistExp L u₂ M₂ t
        * (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t := by
  rw [dv2ResPolyTw, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  by_cases ht : t < dv2SideDeg L Ψ f u₂ ℓ₂ hne + 1
  · rw [if_pos ht]
  · rw [if_neg ht, dv2ResPolyAnch_coeff_of_gt L hne hp₂ (by omega), mul_zero]

/-- The anchor clause survives the twist verbatim (`ε_0 = 0`): the constant coefficient
is the exact pin read of the side-min digit — the same well-definedness clause as the
anchored carrier's. -/
theorem dv2ResPolyTw_coeff_zero (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    (dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff 0
      = dv2FullRead L M₂ (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne)) := by
  rw [dv2ResPolyTw_coeff, twistExp_zero, pow_zero, one_mul,
    dv2ResPolyAnch_coeff_zero]

/-! ## Part 3 — ★★ the A-C.24″ mechanism: the constant scalar over the twisted
carrier, FROM the slot-indexed family over the anchored carrier -/

/-- ★★ **THE SCALAR TRANSFER** (the A-C.24″ conclusion shape, source-faithful).  If the
anchored carriers satisfy F14C's honest slot-indexed family
`coeff t (f) = root^{c₁(M₂′ − t·u₂, c)} · γ̂ · coeff t (f_S)` (the block/complement
specialization of the weighted convolution, with the complement's constant `c` and pin
addition `M₂ = M₂′ + c`), then the TWISTED carriers satisfy EFF.HE6R1.39's display:
one CONSTANT scalar per side, with the PIN-HEIGHT exponent `c₁(M₂′, c)` —
`R̃(f) = C(root^{c₁(M₂′,c)} · γ̂) · R̃(f_S)`.  No stationarity premise: ID1 is the
whole mechanism. -/
theorem dv2ResPolyTw_scalar_of_anch_family (L : LevelDatum F H₀ hpin)
    {Ψ f fS : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ fS u₂ ℓ₂).Nonempty)
    {M₂ M₂' c : ℕ} {γ : AdjoinRoot L.r}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ fS (dv2SideMin L Ψ fS u₂ ℓ₂ hne') = (M₂' : ℕ∞))
    (hdeg : dv2SideDeg L Ψ f u₂ ℓ₂ hne = dv2SideDeg L Ψ fS u₂ ℓ₂ hne')
    (hM : M₂ = M₂' + c)
    (hfloor : dv2SideDeg L Ψ fS u₂ ℓ₂ hne' * u₂ ≤ M₂')
    (hfam : ∀ t, t ≤ dv2SideDeg L Ψ fS u₂ ℓ₂ hne' →
      (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t
        = AdjoinRoot.root L.r ^ L.cocycle (M₂' - t * u₂) c
          * (γ * (dv2ResPolyAnch L Ψ fS u₂ ℓ₂ hne' M₂' hp₂').coeff t)) :
    dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂
      = Polynomial.C (AdjoinRoot.root L.r ^ L.cocycle M₂' c * γ)
        * dv2ResPolyTw L Ψ fS u₂ ℓ₂ hne' M₂' hp₂' := by
  subst hM
  apply Polynomial.ext
  intro t
  rw [Polynomial.coeff_C_mul, dv2ResPolyTw_coeff, dv2ResPolyTw_coeff]
  by_cases ht : t ≤ dv2SideDeg L Ψ fS u₂ ℓ₂ hne'
  · rw [hfam t ht]
    have htu : t * u₂ ≤ M₂' := le_trans (Nat.mul_le_mul_right u₂ ht) hfloor
    have hid := twistExp_cocycle_transfer L (u₂ := u₂) (M₂ := M₂') (c := c)
      (t := t) htu
    have hpow : AdjoinRoot.root L.r ^ twistExp L u₂ (M₂' + c) t
          * AdjoinRoot.root L.r ^ L.cocycle (M₂' - t * u₂) c
        = AdjoinRoot.root L.r ^ L.cocycle M₂' c
          * AdjoinRoot.root L.r ^ twistExp L u₂ M₂' t := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    calc AdjoinRoot.root L.r ^ twistExp L u₂ (M₂' + c) t
          * (AdjoinRoot.root L.r ^ L.cocycle (M₂' - t * u₂) c
            * (γ * (dv2ResPolyAnch L Ψ fS u₂ ℓ₂ hne' M₂' hp₂').coeff t))
        = AdjoinRoot.root L.r ^ twistExp L u₂ (M₂' + c) t
            * AdjoinRoot.root L.r ^ L.cocycle (M₂' - t * u₂) c
          * (γ * (dv2ResPolyAnch L Ψ fS u₂ ℓ₂ hne' M₂' hp₂').coeff t) := by
          ring
      _ = AdjoinRoot.root L.r ^ L.cocycle M₂' c
            * AdjoinRoot.root L.r ^ twistExp L u₂ M₂' t
          * (γ * (dv2ResPolyAnch L Ψ fS u₂ ℓ₂ hne' M₂' hp₂').coeff t) := by
          rw [hpow]
      _ = AdjoinRoot.root L.r ^ L.cocycle M₂' c * γ
          * (AdjoinRoot.root L.r ^ twistExp L u₂ M₂' t
            * (dv2ResPolyAnch L Ψ fS u₂ ℓ₂ hne' M₂' hp₂').coeff t) := by
          ring
  · rw [dv2ResPolyAnch_coeff_of_gt L hne hp₂ (by omega),
      dv2ResPolyAnch_coeff_of_gt L hne' hp₂' (by omega),
      mul_zero, mul_zero, mul_zero]

/-! ## Part 4 — ★★ the classical product law over the twisted carrier -/

/-- ★★ **The theorem-of-the-product shape** (the classical vindication): from F14C's
honest weighted convolution (`hw`, the conclusion of
`dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution`), the TWISTED carriers multiply
with a SINGLE pin cocycle — `R̃(g·z) = C(root^{c₁(Mg,Mz)}) · R̃(g) · R̃(z)`.  ID2 is
the whole mechanism; the slot-varying antidiagonal weights are absorbed exactly. -/
theorem dv2ResPolyTw_mul_of_weightedConv (L : LevelDatum F H₀ hpin)
    {Ψ g z : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty)
    {Mg Mz Mgz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞))
    (hpgz : dv2Pin L Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz) = (Mgz : ℕ∞))
    (hM : Mgz = Mg + Mz)
    (hfg : dv2SideDeg L Ψ g u₂ ℓ₂ hng * u₂ ≤ Mg)
    (hfz : dv2SideDeg L Ψ z u₂ ℓ₂ hnz * u₂ ≤ Mz)
    (hw : dv2ResPolyAnch L Ψ (g * z) u₂ ℓ₂ hngz Mgz hpgz
      = dv2ResPolyAnchWeightedConv L Ψ g z u₂ ℓ₂ hng hnz Mg Mz hpg hpz) :
    dv2ResPolyTw L Ψ (g * z) u₂ ℓ₂ hngz Mgz hpgz
      = Polynomial.C (AdjoinRoot.root L.r ^ L.cocycle Mg Mz)
        * (dv2ResPolyTw L Ψ g u₂ ℓ₂ hng Mg hpg
          * dv2ResPolyTw L Ψ z u₂ ℓ₂ hnz Mz hpz) := by
  classical
  subst hM
  apply Polynomial.ext
  intro J
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    dv2ResPolyTw_coeff L hngz hpgz J, hw,
    dv2ResPolyAnchWeightedConv, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  by_cases hJ : J < dv2SideDeg L Ψ g u₂ ℓ₂ hng + dv2SideDeg L Ψ z u₂ ℓ₂ hnz + 1
  · rw [if_pos hJ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₁ ht₁ => ?_
    have ht₁J : t₁ ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁)
    by_cases hg₁ : t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng
    · by_cases hz₁ : J - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz
      · rw [if_pos ⟨hg₁, hz₁⟩, dv2ResPolyTw_coeff L hng hpg t₁,
          dv2ResPolyTw_coeff L hnz hpz (J - t₁)]
        have h1t : t₁ * u₂ ≤ Mg := le_trans (Nat.mul_le_mul_right u₂ hg₁) hfg
        have h2t : (J - t₁) * u₂ ≤ Mz := le_trans (Nat.mul_le_mul_right u₂ hz₁) hfz
        have hid := twistExp_cocycle_mul L (u₂ := u₂) (Mg := Mg) (Mz := Mz)
          (t₁ := t₁) (t₂ := J - t₁) h1t h2t
        have hJt : t₁ + (J - t₁) = J := by omega
        rw [hJt] at hid
        have hpow : AdjoinRoot.root L.r ^ twistExp L u₂ (Mg + Mz) J
              * AdjoinRoot.root L.r
                  ^ L.cocycle (Mg - t₁ * u₂) (Mz - (J - t₁) * u₂)
            = AdjoinRoot.root L.r ^ L.cocycle Mg Mz
              * (AdjoinRoot.root L.r ^ twistExp L u₂ Mg t₁
                * AdjoinRoot.root L.r ^ twistExp L u₂ Mz (J - t₁)) := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1
          omega
        calc AdjoinRoot.root L.r ^ twistExp L u₂ (Mg + Mz) J
              * (AdjoinRoot.root L.r
                    ^ L.cocycle (Mg - t₁ * u₂) (Mz - (J - t₁) * u₂)
                * ((dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg).coeff t₁
                  * (dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz).coeff (J - t₁)))
            = AdjoinRoot.root L.r ^ twistExp L u₂ (Mg + Mz) J
                * AdjoinRoot.root L.r
                    ^ L.cocycle (Mg - t₁ * u₂) (Mz - (J - t₁) * u₂)
              * ((dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg).coeff t₁
                * (dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz).coeff (J - t₁)) := by
              ring
          _ = AdjoinRoot.root L.r ^ L.cocycle Mg Mz
                * (AdjoinRoot.root L.r ^ twistExp L u₂ Mg t₁
                  * AdjoinRoot.root L.r ^ twistExp L u₂ Mz (J - t₁))
              * ((dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg).coeff t₁
                * (dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz).coeff (J - t₁)) := by
              rw [hpow]
          _ = AdjoinRoot.root L.r ^ L.cocycle Mg Mz
              * (AdjoinRoot.root L.r ^ twistExp L u₂ Mg t₁
                  * (dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg).coeff t₁
                * (AdjoinRoot.root L.r ^ twistExp L u₂ Mz (J - t₁)
                  * (dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz).coeff (J - t₁))) := by
              ring
      · rw [if_neg (fun h => hz₁ h.2), mul_zero, dv2ResPolyTw_coeff L hnz hpz,
          dv2ResPolyAnch_coeff_of_gt L hnz hpz (by omega),
          mul_zero, mul_zero, mul_zero]
    · rw [if_neg (fun h => hg₁ h.1), mul_zero, dv2ResPolyTw_coeff L hng hpg,
        dv2ResPolyAnch_coeff_of_gt L hng hpg (by omega),
        mul_zero, zero_mul, mul_zero]
  · rw [if_neg hJ, mul_zero]
    symm
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun t₁ ht₁ => ?_
    rcases Nat.lt_or_ge (dv2SideDeg L Ψ g u₂ ℓ₂ hng) t₁ with hg₁ | hg₁
    · rw [dv2ResPolyTw_coeff L hng hpg, dv2ResPolyAnch_coeff_of_gt L hng hpg hg₁,
        mul_zero, zero_mul, mul_zero]
    · have hz₁ : dv2SideDeg L Ψ z u₂ ℓ₂ hnz < J - t₁ := by omega
      rw [dv2ResPolyTw_coeff L hnz hpz, dv2ResPolyAnch_coeff_of_gt L hnz hpz hz₁,
        mul_zero, mul_zero, mul_zero]

/-! ## Part 5 — the Tw ↔ Anch bridge and the F1.5 adapter -/

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField
    (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- `root ≠ 0` in the stage tower: `L.r ∣ X` would force `L.r = c·X`, contradicting
`L.r.coeff 0 ≠ 0` (the datum's `r(0) ≠ 0` clause, DEFINITION HE7-1). -/
private theorem root_ne_zero (L : LevelDatum F H₀ hpin) :
    (AdjoinRoot.root L.r : AdjoinRoot L.r) ≠ 0 := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  intro h0
  have hdvd : L.r ∣ Polynomial.X := by
    rw [← AdjoinRoot.mk_X (f := L.r)] at h0
    exact AdjoinRoot.mk_eq_zero.mp h0
  obtain ⟨q, hq⟩ := hdvd
  have hr0 : L.r ≠ 0 := L.hrmonic.ne_zero
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact Polynomial.X_ne_zero hq
  have hdeg1 : (Polynomial.X : Polynomial (F.stageField H₀ hpin)).natDegree
      = L.r.natDegree + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul hr0 hq0]
  rw [Polynomial.natDegree_X] at hdeg1
  have h00 : L.r.coeff 0 * q.coeff 0 = 0 := by
    rw [← Polynomial.mul_coeff_zero, ← hq, Polynomial.coeff_X_zero]
  have hqdeg : q.natDegree = 0 := by
    have := L.hrdeg
    omega
  obtain ⟨cq, hcq⟩ := Polynomial.natDegree_eq_zero.mp hqdeg
  have hqc : q.coeff 0 ≠ 0 := by
    rw [← hcq, Polynomial.coeff_C_zero]
    intro h
    rw [h, map_zero] at hcq
    exact hq0 hcq.symm
  rcases mul_eq_zero.mp h00 with h | h
  · exact L.hr0 h
  · exact hqc h

/-- The twist is coefficient-vanishing-invariant (root powers are units in the stage
tower): the twisted and anchored carriers vanish at the same slots — in particular the
GUARD (`dv2ResPolyAnch_coeff_eq_zero_of_not_onSide`) transfers to the twisted carrier
verbatim. -/
theorem dv2ResPolyTw_coeff_eq_zero_iff (L : LevelDatum F H₀ hpin)
    {Ψ f : Polynomial O} {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    {M₂ : ℕ} (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) (t : ℕ) :
    (dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t = 0
      ↔ (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t = 0 := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  haveI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  rw [dv2ResPolyTw_coeff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (pow_ne_zero _ (root_ne_zero L))
    · exact h
  · intro h
    rw [h, mul_zero]

/-- The twist is degree-invariant. -/
theorem natDegree_dv2ResPolyTw_eq (L : LevelDatum F H₀ hpin)
    {Ψ f : Polynomial O} {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    {M₂ : ℕ} (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    (dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree
      = (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree := by
  apply le_antisymm
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    exact (dv2ResPolyTw_coeff_eq_zero_iff L hne hp₂ m).mpr
      (Polynomial.coeff_eq_zero_of_natDegree_lt hm)
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    exact (dv2ResPolyTw_coeff_eq_zero_iff L hne hp₂ m).mp
      (Polynomial.coeff_eq_zero_of_natDegree_lt hm)

/-- The F1.5 adapter over the twisted carrier (C136f14c's
`dv2ResPolyAnch_radical_eq_of_scalar`, transposed): a nonzero constant scalar identity
gives equal degree and identical monic irreducible divisors. -/
theorem dv2ResPolyTw_radical_eq_of_scalar (L : LevelDatum F H₀ hpin)
    {Ψ f fS : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ fS u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ fS (dv2SideMin L Ψ fS u₂ ℓ₂ hne') = (M₂' : ℕ∞))
    {c : AdjoinRoot L.r} (hc : c ≠ 0)
    (hscalar : dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂ =
      Polynomial.C c * dv2ResPolyTw L Ψ fS u₂ ℓ₂ hne' M₂' hp₂') :
    (dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree
        = (dv2ResPolyTw L Ψ fS u₂ ℓ₂ hne' M₂' hp₂').natDegree ∧
    ∀ q : Polynomial (AdjoinRoot L.r), q.Monic → Irreducible q →
      (q ∣ dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂ ↔
        q ∣ dv2ResPolyTw L Ψ fS u₂ ℓ₂ hne' M₂' hp₂') := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  haveI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  have hunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr ((isUnit_iff_ne_zero).mpr hc)
  constructor
  · by_cases hQ : dv2ResPolyTw L Ψ fS u₂ ℓ₂ hne' M₂' hp₂' = 0
    · rw [hQ, mul_zero] at hscalar
      rw [hscalar, hQ]
    · rw [hscalar, Polynomial.natDegree_mul hunit.ne_zero hQ,
        Polynomial.natDegree_C, zero_add]
  · intro q _hqmonic _hqirr
    rw [hscalar, hunit.dvd_mul_left]

end Uniformity.Density.Tower.C136f14d

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136f14d.twistExp
#print axioms Uniformity.Density.Tower.C136f14d.twistExp_zero
#print axioms Uniformity.Density.Tower.C136f14d.twistExp_cocycle_transfer
#print axioms Uniformity.Density.Tower.C136f14d.twistExp_cocycle_mul
#print axioms Uniformity.Density.Tower.C136f14d.dv2ResPolyTw
#print axioms Uniformity.Density.Tower.C136f14d.dv2ResPolyTw_coeff
#print axioms Uniformity.Density.Tower.C136f14d.dv2ResPolyTw_coeff_zero
#print axioms Uniformity.Density.Tower.C136f14d.dv2ResPolyTw_scalar_of_anch_family
#print axioms Uniformity.Density.Tower.C136f14d.dv2ResPolyTw_mul_of_weightedConv
#print axioms Uniformity.Density.Tower.C136f14d.dv2ResPolyTw_coeff_eq_zero_iff
#print axioms Uniformity.Density.Tower.C136f14d.natDegree_dv2ResPolyTw_eq
#print axioms Uniformity.Density.Tower.C136f14d.dv2ResPolyTw_radical_eq_of_scalar

end AxCheck
