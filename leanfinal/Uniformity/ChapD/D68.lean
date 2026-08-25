/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D07
import Uniformity.ChapD.D08
import Uniformity.ChapD.D37
import Uniformity.ChapD.D46
import Uniformity.ChapD.D48

/-!
# Uniformity.ChapD.D68 — the non-vacuity witnesses gate (`portWitness`, `certWitness`)

**Chapter D, NODE D.68** [gate] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §10; the
chapter-D census gate). ENV n/a. No signed theorem: a gate file, carrying the two
non-vacuity witnesses D.37 and D.46 each explicitly DECLINE to duplicate in their own
files — "that witness … is gate content owned by D.68" (D.37's TEETH note; D.46's TEETH
note repeats the same routing for `CertFrame`).

*Why this file, and why now.* D.37's `BoundaryReadPort` and D.46's `CertFrame` are both
hypothesis-carrying structures whose emptiness would make their consumers' theorems
vacuous. Non-vacuity is *not* scored at those nodes themselves (by design, to avoid two
copies of a gate row in the chapter); it is scored here, exactly once, per A-D.1 item (v).

## The two witnesses

1. **`portWitness`** — `BoundaryReadPort A q s` is inhabited for EVERY arena `A`, ladder
   step `q`, exponent `s` and unit `w : Kˣ`. The witness's `U` field is FORCED to
   `w^s · ϑ⁻¹ = Θ·w^s` (D.38's own conclusion), derived from the port axioms (BR1–BR5)
   alone — not supplied as a shortcut, since the fence at D.37 forbids a port carrying the
   endpoint as data.
2. **`certWitness`** (with its support layer `gradWitness`) — `CertFrame ℤ Unit ℚ` is
   inhabited with (FLOOR) satisfied, and its coordinate `j = 0` is `Touched`
   (`certWitness_touched`), so D.48's `Touched` and D.49's equivalence are both
   non-trivially satisfiable, not vacuously so.

DEPENDS: D.07 (`GaugeArena`) · D.08 (`GaugeArena.vartheta`) · D.37 (`BoundaryReadPort`) ·
D.46 (`CertFrame`) · D.48 (`CertFrame.omega`, `CertFrame.Touched`) · mathlib `Units`,
`Finsupp`, `AddMonoidHom`.

**PROOF.** `portWitness`/`certWitness` are structure literals whose obligation fields
discharge by `rfl`/`simp`/`decide`-shaped calculation; `certWitness_touched` unfolds the
witness and reduces to a `Finsupp.single`/evaluation fact.

SOURCE: `EFF.T3.06`–`.11` (the port, non-vacuity leg) · `EFF.T4.01`–`.13` (the certificate
frame, non-vacuity leg).

**TEETH.** A-D.1 item (v): the landed census must carry a non-vacuity witness for both
hypothesis-carrying structures the chapter signs. This file is that witness.

ENVIRONMENT: no `variable` block; all binders inline (B.42 binder rule).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.68** `BoundaryReadPort` is INHABITED for every arena, ladder step, exponent and
unit, so D.37/D.38 are not vacuous. The witness's `U` is forced to `w^s·ϑ⁻¹ = Θ·w^s` —
D.38's conclusion, arrived at from the port axioms alone. -/
noncomputable def portWitness {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) (w : Kˣ) : BoundaryReadPort A q s where
  w := w
  ctR := (w : K) ^ s
  ctRQ := fun j => if j = 0 then (w : K) ^ s else 0
  expSupport := {0}
  br1 := rfl
  br2 := by simp
  br3 := by intro j hj; simp [hj]
  U := (w : K) ^ s * ((A.vartheta q s)⁻¹ : Kˣ)
  digit := (A.vartheta q s : K)
  br4 := by
    simp only [if_pos]
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  br5 := rfl

/-- **D.68** gate-local data: an additive `grΔ` layer over `ℤ` with a single canonical
slot, used only to inhabit `certWitness` below. -/
noncomputable def gradWitness (m : ℕ) : ℤ →+ (Unit →₀ ℚ) :=
  if m = 0 then AddMonoidHom.mk' (fun n => Finsupp.single () (n : ℚ))
    (by intro a b; simp [Finsupp.single_add]) else 0

/-- **D.68** `CertFrame` is INHABITED, with (FLOOR) satisfied, so D.46–D.52 are not
vacuous. -/
noncomputable def certWitness : CertFrame ℤ Unit ℚ where
  μ₂ := 1
  Θ := fun _ => 0
  M := Set.univ
  fkey := 1
  fkey_mem := Set.mem_univ 1
  grΔ := fun m _ => gradWitness m
  floor := by intro f _ j _ m hm; exact absurd hm (Nat.not_lt_zero m)

/-- **D.68** …and `certWitness`'s coordinate `j = 0` is TOUCHED, so D.48's `Touched` and
D.49's equivalence are both non-trivially satisfiable. -/
theorem certWitness_touched : certWitness.Touched 0 := by
  simp only [CertFrame.Touched, CertFrame.omega, certWitness, gradWitness]
  intro h
  have := congrArg (fun f => f ()) h
  simp at this

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.portWitness
#print axioms Uniformity.Density.Gauge.gradWitness
#print axioms Uniformity.Density.Gauge.certWitness
#print axioms Uniformity.Density.Gauge.certWitness_touched

end AxCheck
