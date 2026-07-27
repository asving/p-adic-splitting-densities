/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# HC1/DefsD — the carry algebra 𝒟 = F[u]/(u^e − z̄) (blueprint §2.1)

**Provenance.** `HC1_LEAN_BLUEPRINT_2026-07-28.md` (rev 2, ACCEPTED) §2.1; pass-7
carry-algebra spec MOVES 1508–1514. The carry algebra is the PORTABLE digit-arithmetic
object (design decision D1): the concrete graded function object `ZMod e → F` with the
cocycle product; `zbar` enters through the multiplication only. Definitions only —
no theorems, no `sorry`. The `CommRing` instance is unit D1's construction (packaged
here as the interface `CarryRingPack`, mirroring MovesGr's `GradedRingStr` pattern),
NOT a Defs field.

Falsifiability: `carryExp` is FORCED (⌊(ρ.val+σ.val)/e⌋ for representatives < e is
exactly this indicator); a wrong cocycle breaks unit D1's associativity.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

/-- **The carry algebra 𝒟 = F[u]/(u^e − z̄)** (pass-7 spec, MOVES 1508–1514), as the
concrete graded function object `ZMod e → F` with the cocycle product. `zbar` enters
through the multiplication only. Requires `NeZero e` wherever sums over `ZMod e` are
taken (e ≥ 1; e = 0 is note-rejected — no read has denominator 0). -/
def CarryAlg (F : Type u) (e : ℕ) : Type u := ZMod e → F

/-- Pointwise addition (the additive group of 𝒟 is the function space's). -/
instance {F : Type u} [Field F] {e : ℕ} : AddCommGroup (CarryAlg F e) :=
  Pi.addCommGroup

instance {F : Type u} [Field F] {e : ℕ} : Inhabited (CarryAlg F e) := ⟨0⟩

variable {F : Type u} [Field F] {e : ℕ}

/-- the 2-cocycle: 1 iff adding the canonical representatives overflows `e`. -/
def carryExp (ρ σ : ZMod e) : ℕ := if e ≤ ρ.val + σ.val then 1 else 0

/-- twisted convolution: `(x * y) τ = Σ_{ρ+σ=τ} x ρ · y σ · z̄^{carryExp ρ σ}`. -/
noncomputable def cmul [NeZero e] (zbar : Fˣ) (x y : CarryAlg F e) : CarryAlg F e :=
  fun τ => ∑ ρ : ZMod e, x ρ * y (τ - ρ) * (zbar : F) ^ carryExp ρ (τ - ρ)

/-- homogeneous generator `u_ρ` with scalar `c`: `Pi.single ρ c`. -/
noncomputable def dOf (ρ : ZMod e) (c : F) : CarryAlg F e := Pi.single ρ c

/-- homogeneity: supported on one coset. -/
def IsHomog (x : CarryAlg F e) (ρ : ZMod e) : Prop := ∀ σ, σ ≠ ρ → x σ = 0

/-- **The carry-ring interface** (unit D1's deliverable; the MovesGr `GradedRingStr`
pattern): a `CommRing` on `CarryAlg F e` whose product IS the twisted convolution
`cmul zbar`, whose addition is pointwise (stated componentwise against the ambient
`Pi` addition — the non-tautological form, per the MovesGr §8.4 machine-check), and
whose unit is `dOf 0 1`. The ring depends on `zbar` (MOVES 1508–1511: 𝒟 is a strongly
graded twisted algebra). -/
structure CarryRingPack (F : Type u) [Field F] (e : ℕ) [NeZero e] (zbar : Fˣ) where
  ring : CommRing (CarryAlg F e)
  mul_def : ∀ x y : CarryAlg F e, (letI := ring; x * y) = cmul zbar x y
  add_def : ∀ (x y : CarryAlg F e) (τ : ZMod e), (letI := ring; x + y) τ = x τ + y τ
  one_def : (letI := ring; (1 : CarryAlg F e)) = dOf 0 1

/-- **The DIG map** of a stage's coefficient digit into 𝒟 at the BIRTH index (design
decision D6 threading): an (S5)-shaped residual `R B = c·z^k` (a monomial unit) is sent
to the `u_{k mod e_b}`-homogeneous element whose scalar is the ALIGNED residual class
`c·z̄^{(k − (k mod e_b))/e_b}` evaluated at `zbar`. Total on `A`: 0 off the (S5)
monomial-unit shape (E-phase note: the position is the monomial's OWN position,
choice-extracted; the (S5) law `k = −t·wPrev B` identifies it on the parent
coefficient space — Deviation D-2 in the blueprint's DEVIATIONS appendix). -/
noncomputable def _root_.LeanUrat.Moves.Stage.digD {p : ℕ} [Fact p.Prime]
    {F : Type u} [Field F] [Finite F] (σ : Stage p F) (zbar : Fˣ) (e_b : ℕ) [NeZero e_b]
    (B : Polynomial ℤ_[p]) : CarryAlg F e_b :=
  open scoped Classical in
  if h : IsMonomialUnit (σ.R B) then
    dOf ((h.choose_spec.choose : ℤ) : ZMod e_b)
      (((h.choose : ↥σ.K) : F) *
        ((zbar ^ ((h.choose_spec.choose -
            (((h.choose_spec.choose : ℤ) : ZMod e_b)).val) / (e_b : ℤ)) : Fˣ) : F))
  else 0

end LeanUrat.HC1
