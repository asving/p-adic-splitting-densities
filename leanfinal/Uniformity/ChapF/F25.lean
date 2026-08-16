/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F25 — the gauge-torsor lemma (the `H¹ = 0` uniqueness claim, killed)

**Chapter F, NODE F.25** [lemma] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1. From
`EFF.WELDMASTER.23` (the C6 F-2 annex): for gauges `F, G : ZMod E → Kˣ` the coboundaries
agree (`∂F = ∂G`, where `(∂F) a b = F a * F b * (F (a + b))⁻¹`) **exactly when** the ratio
`η := F * G⁻¹` is multiplicative — i.e. a group homomorphism `ZMod E → Kˣ`. The RHS below
is literally that character condition, pointwise; the converse direction is the statement
that `∂(F · η) = ∂F` for every homomorphism `η`.

**What the lemma is for.** Gauges with a FIXED coboundary form a torsor under
`Hom(ZMod E, Kˣ) ≅ μ_E(K)` — "rather than being unique". Since `H¹(ℤ/E, Kˣ) = Hom = μ_E(K)`
need not vanish, no downstream argument may canonicalize a gauge by an `H¹ = 0` appeal;
this node gives the counterexample machinery its name. Minimal witness (gate F.30 leg 5):
`E = 2`, `K = F₅`, `η ν = (−1)^ν`, nontrivial because `−1 = 4 ∈ F₅ˣ` has order 2.
CONDITIONALITY of the source finding, carried: it "affects only the certification
narrative, not WM-CLASS's proved existence/class identity". The withdrawn PE10 gloss is
NOT transcribed.

`gaugeBdry` is the signed `def`; `gaugeBdry_eq_iff` was an `axiom` stub at stage 0e and is
PROVED here, at the byte-identical signature — commutative-unit algebra in `Kˣ`
(`mul_inv_eq_mul_inv_iff_mul_eq_mul` twice, with the middle regrouping).
-/

namespace Uniformity.Density.Weld

/-- The 1-coboundary of a gauge (`EFF.WELDMASTER.23`). -/
def gaugeBdry {E : ℕ} [NeZero E] {K : Type*} [Field K] (F : ZMod E → Kˣ) :
    ZMod E → ZMod E → Kˣ := fun a b => F a * F b * (F (a + b))⁻¹

/-- The gauge-torsor lemma (`EFF.WELDMASTER.23`): two gauges have the same coboundary
exactly when their ratio is a character of `ZMod E` into `Kˣ`. Hence the fibres of
`gaugeBdry` are `Hom(ZMod E, Kˣ) ≅ μ_E(K)`-torsors — NOT singletons: any claim of a
canonical gauge via `H¹ = 0` is refuted by an `η ≠ 1`. -/
theorem gaugeBdry_eq_iff {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (F G : ZMod E → Kˣ) :
    gaugeBdry F = gaugeBdry G ↔
      ∀ a b, (F a * (G a)⁻¹) * (F b * (G b)⁻¹) = F (a + b) * (G (a + b))⁻¹ := by
  have key : ∀ a b : ZMod E,
      (gaugeBdry F a b = gaugeBdry G a b) ↔
        ((F a * (G a)⁻¹) * (F b * (G b)⁻¹) = F (a + b) * (G (a + b))⁻¹) := by
    intro a b
    simp only [gaugeBdry]
    rw [mul_inv_eq_mul_inv_iff_mul_eq_mul, mul_mul_mul_comm, ← mul_inv,
      mul_inv_eq_mul_inv_iff_mul_eq_mul, mul_comm (G a * G b) (F (a + b))]
  constructor
  · intro h a b
    exact (key a b).mp (by rw [h])
  · intro h
    funext a b
    exact (key a b).mpr (h a b)

end Uniformity.Density.Weld
