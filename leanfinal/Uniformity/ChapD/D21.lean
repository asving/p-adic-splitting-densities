/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D13
import Uniformity.ChapD.D15
import Uniformity.ChapD.D17
import Uniformity.ChapD.D19
import Uniformity.ChapD.D20

/-!
# Uniformity.ChapD.D21 — `(C1-level-2)`: the level-2 letter in level-1 letters

**Chapter D, NODE D.21** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1, A-D.1, A-D.2 govern — A-D.1 SPELLED this node's elided membership
hole through D.19's proved sibling `chi_varpi_mem_ker`, added the undeclared DEPENDS edge
`BP.D.21 → BP.D.17`, and recorded defect **D-D13**). ENV-D1 + ENV-D3. One signed declaration.

*`(C1-level-2)`.* Put `π₂ := x^{ℓ₁}π^{ℓ′₁}` with `ℓ₁h + ℓ′₁e₁ = 1`, `0 ≤ ℓ₁ < e₁` — that is,
`ℓ₁ = iexp e₁ h 1` and `ℓ′₁ = aexp e₁ h 1`, D.13 at `k = 1`, so `π₂ = n̂₁(1) = ϖ` is exactly
D.19's height-1 normalizer avatar. Then the level-1 ratio

* `ρ₁ = res(n̂₁(u₂)·π₂^{−u₂}) = η^{−⌊ℓ₁u₂/e₁⌋}`,

and, fed into D.20's letter factorization at the stage triple, this is the corpus's
`z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}` with `z₁ = η` (`(C1-base-letter)`).

## What the node actually is, once `π₂ = ϖ` is seen

`π₂^{u₂}` is the `u₂`-th power of the height-1 normalizer, so the left-hand side IS D.19's
`chi (levelOneSection e₁ h) (varpiSection e₁ h)` at `k = u₂` — `varpiSection` is REUSED here
with `ϖ := π₂`, exactly as the A-D.1 SIGNATURE rider says. D.19 already evaluates that residue
as `η^{−q(u₂)}`. So the whole content left to D.21 is the arithmetic identity

* `qexp e₁ h u₂ = ⌊ℓ₁u₂/e₁⌋` (with `ℓ₁ = i₀ = iexp e₁ h 1`),

i.e. `q(k) = ⌊i₀k/e₁⌋`, which is `EFF.T1.06`'s derivation step `i(u) = ℓ₁u − e₁⌊ℓ₁u/e₁⌋`
read backwards. That step is the private helper `iexp_eq_emod` below: `i(k)` is the
`ZMod e₁`-representative of `i₀k`, hence literally `(i₀k) % e₁`, and subtracting a remainder
before an exact division is `Int.ediv_add_emod`.

## A-D.1 / D-D13 — the dead-weight hypothesis, signed as given

`hu : 0 ≤ u₂` is **unnecessary**: Lean's `Int./` and `Int.%` are `ediv`/`emod` at the v4.31.0
pin, so `iexp e₁ h k = (i₀k) % e₁` and `qexp e₁ h k = (i₀k)/e₁` hold at EVERY sign of `k` —
`iexp_eq_emod` and `qexp_eq_ediv` below are proved with no sign hypothesis at all, and the
`k < 0` rows are executed in the §10 gate tables. The blueprint signs `hu` anyway because it is
FAITHFUL to `EFF.T1.06`'s display, and this transcription keeps the signature byte-exact; the
file therefore carries `set_option linter.unusedVariables false in` on the one declaration
whose binder is dead. A consumer blocked only by `hu` may drop it in a re-sign (A-D.1's own
wording), which is a statement change and needs the usual sign-off.

## The `z₂` display (the STATEMENT's "hence" clause)

D.21's SIGNATURE block signs ONE declaration (`levelOne_rho`) and the A-D.1 stub recount agrees
(`leanspec/Leanspec/ChapD.lean` carries exactly one D.21 row), so the `z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}`
display — PROOF step 4, "D.20 applied at the stage triple" — is landed as the unnamed, EXECUTED
`example` in the `StageTriple` section at the foot of this file, the same device D.19 used for
its own unnamed "moreover" clause (GC-6.5). It is machine-checked, and it invents no public
name the blueprint did not sign.

## Faithfulness

No new definition. The one trust-boundary reading is the identification `π₂ = n̂₁(1)`, which is
the blueprint's own (D.13 at `k = 1` IS the exact-height spec at height 1) and is discharged by
REUSING `varpiSection` rather than by introducing a second section — so nothing about `π₂`
beyond "the height-1 normalizer" can enter.

DEPENDS: D.13 (`iexp`) · D.15 (`qexp`) · D.17 (`levelOneArena`, `levelOneSection`; the A-D.1
edge `BP.D.21 → BP.D.17` — the conclusion applies `(levelOneArena …).res`) · D.19
(`varpiSection`, `chi_varpi_mem_ker`, `res_chi_varpi`) · D.20 (`GaugeArena.res_ratio_factor`,
for the `z₂` display only) · mathlib `ZMod.val_intCast`, `ZMod.natCast_val`, `ZMod.cast_id`,
`Int.ediv_add_emod`, `Int.mul_ediv_cancel_left` — all name-verified at the v4.31.0 pin.

**PROOF.** 1. `π₂ = n̂₁(1)` (D.13 at `k = 1`), so the LHS is D.19's `chi` at `k = u₂`.
2. D.19's `res_chi_varpi` gives `η^{−q(u₂)}`. 3. `q(u₂) = ⌊i₀u₂/e₁⌋`: `i(k) = (i₀k) % e₁`
because `(k)·(h)⁻¹ = (i₀k)` in `ZMod e₁` and `ZMod.val_intCast` reads `val` as `%`; then
`i₀k − (i₀k)%e₁ = e₁·((i₀k)/e₁)` and the outer division cancels. 4. The `z₂` display is D.20 at
`(Φ, n̂₁(u₂), π₂^{u₂})`, all of height `u₂` — the `StageTriple` `example`.

SOURCE: `EFF.T1.06` (the boxed `(C1-level-2)` `z₂ = η₂z₁^{−⌊ℓ₁u₂/e₁⌋}` and its derivation);
`EFF.T1.31` SPAN PIN 1 (the A7 GENTOW2 pin is this display verbatim — chapter C's GENTOW2 layer
consumes this node BY NAME, so `levelOne_rho` is an OUT-interface name).

**TEETH.** T1 §7 attacks 1 and 8 → §12 signed rows; the GENTOW2 `S5.1` consumer pin → the
statement-level edge recorded at §11. Nothing numeric is scored here (`K` is an abstract field);
the `η`-power tables run at gates D.65/D.66, and `iexp_eq_emod`'s no-sign-hypothesis form is
what makes the `k < 0` rows there legitimate.

ENVIRONMENT: ENV-D1 + ENV-D3 (`{K : Type*} [Field K]`, `η : Kˣ` and the lattice arena, written
inline per the B.42 binder rule — this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- `i(k)` IS the `Int`-remainder of `i₀k`: `i(k) = (i₀k) % e₁`, `i₀ = iexp e₁ h 1`
(`EFF.T1.06`'s derivation step `i(u) = ℓ₁u − e₁⌊ℓ₁u/e₁⌋`, read as a remainder).  Private —
D.21 is the only consumer, and the shared `iexp` API is D.13's.  ⚠ NO sign hypothesis on `k`:
`ZMod.val` is the nonnegative representative and `Int.%` is `emod` at the pin (A-D.1/D-D13). -/
private theorem iexp_eq_emod (e₁ h : ℕ) (he : 0 < e₁) (k : ℤ) :
    (iexp e₁ h k : ℤ) = (iexp e₁ h 1 * k) % e₁ := by
  haveI : NeZero e₁ := ⟨he.ne'⟩
  have hz : ((iexp e₁ h 1 * k : ℤ) : ZMod e₁) = (k : ZMod e₁) * (h : ZMod e₁)⁻¹ := by
    push_cast
    rw [iexp, ZMod.natCast_val, ZMod.cast_id]
    push_cast
    ring
  rw [← ZMod.val_intCast (n := e₁) (iexp e₁ h 1 * k), hz, iexp]

/-- `(C5-carry)`'s exponent in closed form: `q(k) = ⌊i₀k/e₁⌋`.  Private, same reason as
`iexp_eq_emod`; also with no sign hypothesis (A-D.1/D-D13). -/
private theorem qexp_eq_ediv (e₁ h : ℕ) (he : 0 < e₁) (k : ℤ) :
    qexp e₁ h k = (iexp e₁ h 1 * k) / e₁ := by
  have hne : (e₁ : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  have hkey : (iexp e₁ h 1 : ℤ) * k - (iexp e₁ h k : ℤ)
      = (e₁ : ℤ) * (((iexp e₁ h 1 : ℤ) * k) / (e₁ : ℤ)) := by
    rw [iexp_eq_emod e₁ h he k]
    linarith [Int.mul_ediv_add_emod ((iexp e₁ h 1 : ℤ) * k) (e₁ : ℤ)]
  change ((iexp e₁ h 1 : ℤ) * k - (iexp e₁ h k : ℤ)) / (e₁ : ℤ) = _
  rw [hkey, Int.mul_ediv_cancel_left _ hne]

set_option linter.unusedVariables false in
/-- **D.21 — `(C1-level-2)`** (`EFF.T1.06`): with `π₂ = x^{ℓ₁}π^{ℓ′₁} = n̂₁(1) = ϖ`, the level-1
ratio is `ρ₁ = res(n̂₁(u₂)·π₂^{−u₂}) = η^{−⌊ℓ₁u₂/e₁⌋}`, `ℓ₁ = iexp e₁ h 1`.  Combined with D.20
this is `z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}` (the `StageTriple` `example` below).

⚠ **A-D.1/D-D13**: `hu : 0 ≤ u₂` is dead weight — the identity holds at every sign, since
`Int./` and `Int.%` are `ediv`/`emod` at the pin.  It is signed as given (faithful to
`EFF.T1.06`'s display), hence the `unusedVariables` suppression. -/
theorem levelOne_rho (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (u₂ : ℤ) (hu : 0 ≤ u₂) :
    (levelOneArena e₁ h he hcop η).res
        ⟨NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) u₂,
          chi_varpi_mem_ker e₁ h he hcop η u₂⟩
      = η ^ (-((iexp e₁ h 1 * u₂) / e₁)) := by
  rw [res_chi_varpi e₁ h he hcop η u₂, qexp_eq_ediv e₁ h he u₂]

end Uniformity.Density.Gauge

/-! ## The `z₂` display, EXECUTED (the STATEMENT's "hence" clause)

PROOF step 4: D.20's letter factorization `z = η'·ρ` at the stage triple
`(Φ, n̂₁(u₂), π₂^{u₂})` — three elements of height `u₂` — with `ρ₁` evaluated by `levelOne_rho`
gives the corpus's `z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}`, `z₁ = η`.  Unnamed by design: D.21's SIGNATURE
block signs `levelOne_rho` and no second name (GC-6.5), so this closure is scored as an
`example`.  `Φ` stands for the stage element `Φ_1^{e_2}`, constrained only by its height —
which is all `EFF.T1.02`'s stage typing supplies. -/

section StageTriple

open Uniformity.Density.Gauge

/-- Gate-local: `ϖ^k` has height `k` (`v` is a hom and `ϖ = n̂₁(1)` has height `1`).  This is
D.19's `chi_varpi_mem_ker` proof step `h2`, which is local to that proof. -/
private theorem varpiSection_height (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (k : ℤ) :
    (levelOneArena e₁ h he hcop η).v ((varpiSection e₁ h).n k) = Multiplicative.ofAdd k := by
  change (levelOneArena e₁ h he hcop η).v ((levelOneSection e₁ h).n 1 ^ k) = _
  rw [map_zpow, (levelOneArena e₁ h he hcop η).exact_height]
  simp [← ofAdd_zsmul]

/-- EXECUTED: `z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}` with `z₁ = η` — D.20 at the stage triple, with D.21
evaluating the `ρ₁` factor. -/
example (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) {K : Type*} [Field K] (η : Kˣ)
    (u₂ : ℤ) (hu : 0 ≤ u₂) (Φ : Multiplicative (ℤ × ℤ))
    (hΦ : (levelOneArena e₁ h he hcop η).v Φ = Multiplicative.ofAdd u₂) :
    (levelOneArena e₁ h he hcop η).res
        ⟨Φ * ((varpiSection e₁ h).n u₂)⁻¹,
          (levelOneArena e₁ h he hcop η).mem_ker_div
            (hΦ.trans (varpiSection_height e₁ h he hcop η u₂).symm)⟩
      = (levelOneArena e₁ h he hcop η).res
            ⟨Φ * ((levelOneSection e₁ h).n u₂)⁻¹,
              (levelOneArena e₁ h he hcop η).mem_ker_div
                (hΦ.trans ((levelOneArena e₁ h he hcop η).exact_height u₂).symm)⟩
          * η ^ (-((iexp e₁ h 1 * u₂) / e₁)) := by
  rw [← levelOne_rho e₁ h he hcop η u₂ hu]
  exact GaugeArena.res_ratio_factor (levelOneArena e₁ h he hcop η) Φ
    ((levelOneSection e₁ h).n u₂) ((varpiSection e₁ h).n u₂)
    (hΦ.trans ((levelOneArena e₁ h he hcop η).exact_height u₂).symm)
    (((levelOneArena e₁ h he hcop η).exact_height u₂).trans
      (varpiSection_height e₁ h he hcop η u₂).symm)

end StageTriple

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.levelOne_rho

end AxCheck
