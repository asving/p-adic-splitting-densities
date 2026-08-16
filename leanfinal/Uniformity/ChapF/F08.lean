/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F07
import Mathlib.Algebra.Module.Pi

/-!
# Uniformity.ChapF.F08 — `TwistedAlgebra`, `single`: the twisted group algebra `K^c[ℤ/E]`

**Chapter F, NODE F.08** [def] (`blueprint/CHAP-F_weld_layer.md` §5, as repaired at
A-W.1/F-D3), ENV-F1. W-9 clause (iii)'s object (`EFF.GRTJC.89`): carrier `ZMod E → K`,
multiplication the `c`-twisted convolution `(f ⋆ g) t = ∑_{a+b=t} c a b · f a · g b`.
`Type _`-level `def` (not `abbrev`) so the twisted `Mul` cannot leak onto plain
`ZMod E → K`. The corpus object `𝒜(T)` is a subquotient of the harness chain; W-9(iii)
says it IS this twisted algebra — F declares the abstract right-hand side only; the
identification is inside F.11's carried face.

Six below-the-line instances/helpers per the signed list + A-W.1/F-D3 (`One`/`Pow`, with
**the inverse taken in `Kˣ`, never in `K`** — the executed `q = 3` gate leg's wall), plus
the helper lemmas the blueprint's F.09/F.10 prose pre-authorizes below this contract line
(`mul_apply`/`single_apply` unfolding lemmas, `single_mul_single`, and the two-sided unit
laws `TwistedAlgebra.one_mul`/`mul_one` — F.09's STATEMENT half "single 0 (cc.c 0 0)⁻¹ is a
two-sided unit", in theorem form via F.07's `c_zero_left`/`c_zero_right`) [A-W.2, unit
OM-9; certified by om9_weld_cert.py LEG C before proving].

Signatures byte-identical to the stage-0e gate. Landed by unit OM-9 (2026-08-16).
-/

namespace Uniformity.Density.Weld

open Finset

-- `cc` is phantom in the body by design (the signed signature keys the TYPE by the cocycle
-- so the twisted `Mul` cannot leak onto plain `ZMod E → K`); linter silenced, not respelled.
set_option linter.unusedVariables false in
/-- The twisted group algebra `K^c[ℤ/E]` of the abscissa-coset group over the carry cocycle
(`EFF.GRTJC.89` clause (iii)). Carrier: `ZMod E → K`; multiplication: `c`-twisted
convolution. -/
def TwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Type _ := ZMod E → K

/-- `(f ⋆ g) t = ∑ a, c a (t − a) * f a * g (t − a)`. -/
instance instMulTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Mul (TwistedAlgebra cc) :=
  ⟨fun f g t => ∑ a : ZMod E, (cc.c a (t - a) : K) * f a * g (t - a)⟩

/-- The `single` basis vectors of `TwistedAlgebra cc`. -/
def single {E : ℕ} [NeZero E] {K : Type*} [Field K] {cc : CarryCocycle E K}
    (a : ZMod E) (x : K) : TwistedAlgebra cc :=
  fun t => if t = a then x else 0

instance instAddCommGroupTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : AddCommGroup (TwistedAlgebra cc) := Pi.addCommGroup

instance instModuleTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Module K (TwistedAlgebra cc) := Pi.module _ _ _

/-- A-W.1/F-D3's `One`, following F.09's own prose (`single 0 (cc.c 0 0)⁻¹` is the
two-sided unit); **the inverse is taken in `Kˣ` and coerced afterwards**. -/
instance instOneTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : One (TwistedAlgebra cc) :=
  ⟨single 0 (((cc.c 0 0)⁻¹ : Kˣ) : K)⟩

instance instPowTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Pow (TwistedAlgebra cc) ℕ := ⟨fun f n => npowRec n f⟩

namespace TwistedAlgebra

variable {E : ℕ} [NeZero E] {K : Type*} [Field K] {cc : CarryCocycle E K}

/-- [A-W.2, below the contract line] Unfolding lemma for the twisted convolution. -/
theorem mul_apply (f g : TwistedAlgebra cc) (t : ZMod E) :
    (f * g) t = ∑ a : ZMod E, (cc.c a (t - a) : K) * f a * g (t - a) := rfl

/-- [A-W.2, below the contract line] Unfolding lemma for `single`. -/
theorem single_apply (a : ZMod E) (x : K) (t : ZMod E) :
    (single a x : TwistedAlgebra cc) t = if t = a then x else 0 := rfl

/-- [A-W.2, below the contract line] Unfolding lemma for the F-D3 unit. -/
theorem one_def : (1 : TwistedAlgebra cc) = single 0 (((cc.c 0 0)⁻¹ : Kˣ) : K) := rfl

/-- [A-W.2, below the contract line] Unfolding lemma for the module action (the carrier is
opaque, so `Pi.smul_apply` cannot fire on it). -/
theorem smul_apply (r : K) (f : TwistedAlgebra cc) (t : ZMod E) : (r • f) t = r * f t := rfl

/-- [A-W.2, below the contract line] `single` is injective in its coefficient. -/
theorem single_injective (i : ZMod E) {x y : K}
    (h : (single i x : TwistedAlgebra cc) = single i y) : x = y := by
  have h2 := congrArg (fun f : TwistedAlgebra cc => f i) h
  simpa [single] using h2

/-- [A-W.2, below the contract line; blueprint F.10 PROOF step 2's helper] The convolution
of two `single`s: `single a x ⋆ single b y = single (a+b) (c a b · x · y)`. -/
theorem single_mul_single (a b : ZMod E) (x y : K) :
    (single a x : TwistedAlgebra cc) * single b y
      = single (a + b) ((cc.c a b : K) * x * y) := by
  funext t
  rw [mul_apply, Finset.sum_eq_single a]
  · by_cases h : t = a + b
    · subst h
      simp [single, add_sub_cancel_left]
    · have h2 : t - a ≠ b := fun hh => h (by rw [sub_eq_iff_eq_add] at hh; rw [hh, add_comm])
      simp [single, h, h2]
  · intro s _ hs
    simp [single, hs]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- [A-W.2, below the contract line; F.09's STATEMENT half in theorem form, left leg]
`single 0 (cc.c 0 0)⁻¹` is a left unit — via `CarryCocycle.c_zero_left`. -/
protected theorem one_mul (f : TwistedAlgebra cc) : 1 * f = f := by
  funext t
  rw [one_def, mul_apply, Finset.sum_eq_single 0]
  · rw [sub_zero, cc.c_zero_left t, single_apply, if_pos rfl, Units.mul_inv, one_mul]
  · intro s _ hs
    simp [single, hs]
  · intro h
    exact absurd (Finset.mem_univ 0) h

/-- [A-W.2, below the contract line; F.09's STATEMENT half in theorem form, right leg]
`single 0 (cc.c 0 0)⁻¹` is a right unit — via `CarryCocycle.c_zero_right`. -/
protected theorem mul_one (f : TwistedAlgebra cc) : f * 1 = f := by
  funext t
  rw [one_def, mul_apply, Finset.sum_eq_single t]
  · rw [sub_self, cc.c_zero_right t, single_apply, if_pos rfl, mul_right_comm,
      Units.mul_inv, one_mul]
  · intro s _ hs
    have h2 : t - s ≠ 0 := fun hh => hs (sub_eq_zero.mp hh).symm
    simp [single, h2]
  · intro h
    exact absurd (Finset.mem_univ t) h

end TwistedAlgebra

end Uniformity.Density.Weld
