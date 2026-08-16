/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapD.D13 — `iexp`/`aexp`, the level-1 exponent pair

**Chapter D, NODE D.13** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1, A-D.1 govern — the SIGNATURE is A-D.1-re-signed at five public
declarations). ENV-D1.

*The level-1 exponent pair.* For `e₁ h : ℕ` with `0 < e₁` and `Nat.Coprime h e₁`, and a height
`k : ℤ`: `iexp e₁ h k` is the unique `i` with `0 ≤ i < e₁` and `i·h ≡ k (mod e₁)`, and
`aexp e₁ h k := (k − iexp·h)/e₁ : ℤ`, so that the **exact-height identity**
`(iexp e₁ h k)·h + (aexp e₁ h k)·e₁ = k` holds — `EFF.T1.01`'s displayed
`n̂₁(k) = x^{i(k)}π^{a(k)}`, `0 ≤ i(k) < e₁`, `i(k)h + a(k)e₁ = k`.

**Five public declarations**, permitted on the B.15 precedent against GC-6.5 (the pair and its
spec are one interface; every §4 node consumes all three of `iexp`/`aexp`/`iexp_aexp_spec`, and
every §10 gate row consumes one of the last two reducers). `ZMod e₁` needs `NeZero e₁`, supplied
from `he` at use sites (`haveI`); the definitions themselves are total — garbage at `e₁ = 0`,
spec'd only under `he`.

## The two reducers, and DEFECT D-D1 (A-D.1, recorded at its source)

`iexp` **is not `decide`-reducible**: `(h : ZMod e₁)⁻¹` unfolds to `ZMod.inv`, which routes
through `Nat.gcdA`/`Nat.xgcd`; even `((1 : ℕ) : ZMod 2)⁻¹ = 1` fails `decide` at the v4.31.0
pin. The definition is signed AS IS — it is the faithful transcription of `EFF.T1.01`, and
`ZMod.inv` is the right mathematical content — and the gate programme is repaired instead.
Hence the two reducers landed here as PROVED theorems (never axioms):

* `iexp_one` (A-D.1/D-D1): the reduction at `h = 1`, load-bearing for the WHOLE §10 gate
  programme, since all three original gate frames have `h = 1`, where the `ZMod`-inverse
  disappears and the reduced form IS `decide`-able.
* `iexp_eq_of_inv` (A-D.1/D-F1): the general reduction, needed by the `h > 1` frame FRAME-H2
  that finding D-F1 makes mandatory (§10 leg 5). The inverse `c` of `h` is supplied as DATA and
  its defining equation `hc` is `decide`-able at any concrete frame; this is what makes `iexp`
  computable when `h ≠ 1`.

⚠ **The GC-11 gate-writing rider binds every downstream gate row**: `iexp` is NOT
`decide`-reducible, so a §10 gate line written as a bare `by decide` does not compile. Every
gate row goes `simp only [<local defs>, iexp_one]` (or `iexp_eq_of_inv`) **then** `decide`,
with `Θ`/`U` carried as literal data plus involution certificates — never `native_decide`.

## Negative heights (A-D.1's answer to §14 item 5)

`ZMod.val` is always the nonnegative representative, and Lean's `Int./`, `Int.%` are
`ediv`/`emod` at the pin (`(-3)/2 = -2`, `(-3) % 2 = 1`), so `iexp`/`aexp`/`qexp` behave at
every sign with **no hypothesis**: the stage-0e gate executed `iexp 2 1` on `k = −3…5` (D.65)
and `iexp`/`aexp`/`qexp` on `k = −2…6` plus the `(C2-wrap)`/`(C5-carry)`/D.27 grids INCLUDING
negative heights (D.66). Consequence downstream: D.21's `hu : 0 ≤ u₂` is dead weight (defect
D-D13, signed as given).

## Landing order (A-D.1/D-D2, recorded)

`BP.D.17 → BP.D.13` is a **DEFINITIONAL** dependency, not a lemma dependency: D.17's
`levelOneArena.exact_height` field can only be discharged from `iexp_aexp_spec`, so the arena's
axiom footprint carries whatever `iexp_aexp_spec` carries. This node therefore lands BEFORE
D.17, and with `iexp_aexp_spec` PROVED (Lean core only, verified below), so that D.17's
footprint is clean.

## Faithfulness

**⚠ Mandatory, trust-boundary definitions.** Flagged for the chapter cross-read:

* `iexp` is the `ZMod`-normalized representative `((k : ZMod e₁) * (h : ZMod e₁)⁻¹).val`, not a
  `Nat.find`. Uniqueness of `EFF.T1.01`'s `i(k)` is not asserted as a separate clause: it is
  implied by `0 ≤ i < e₁` together with the congruence, both of which `iexp_aexp_spec` carries.
* `aexp` is typed `ℤ`, per T1 §4.2 check 10 (the grade-data value group) and `EFF.T1.02`'s
  integrality clause. It is defined by `Int` division, which is EXACT here — the divisibility
  `e₁ ∣ k − iexp·h` is proved inside `iexp_aexp_spec`, so no truncation occurs on the specified
  domain.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

DEPENDS: none landed; mathlib `ZMod.val`, `ZMod.inv`, `ZMod.val_lt`,
`ZMod.intCast_zmod_eq_zero_iff_dvd`, `ZMod.natCast_val`, `ZMod.cast_id`, `ZMod.inv_mul_of_unit`,
`ZMod.unitOfCoprime`, `ZMod.inv_eq_of_mul_eq_one`, `Int.ediv_mul_cancel` — all name-verified at
the v4.31.0 pin.

**PROOF.** The two `def` bodies are the gate-verified `leanspec/Leanspec/ChapD.lean` stub bodies
verbatim, as is `iexp_one`'s. `iexp_aexp_spec` follows the blueprint's three-step recipe:
(1) `iexp < e₁` is `ZMod.val_lt` under `NeZero e₁` from `he`; (2) the congruence `iexp·h ≡ k`
holds because `(h : ZMod e₁)` is a unit by `hcop` (`ZMod.unitOfCoprime`), so multiplying the
definition back by `h` cancels the inverse (`ZMod.inv_mul_of_unit`); (3) the divisibility
`e₁ ∣ k − iexp·h` comes from the congruence via `ZMod.intCast_zmod_eq_zero_iff_dvd`, and the
identity from `Int.ediv_mul_cancel` plus `omega`. `iexp_eq_of_inv` rewrites the `ZMod` inverse
by `ZMod.inv_eq_of_mul_eq_one` against the supplied `hc`.

SOURCE: `EFF.T1.01` (the displayed `n̂₁(k) = x^{i(k)}π^{a(k)}`, `0 ≤ i(k) < e₁`,
`i(k)h + a(k)e₁ = k`).

**TEETH.** T1 §4.2 check 1 (live-domain boundary) → gates D.65/D.66 evaluate the
`iexp`/`aexp` tables through `iexp_one`; check 10 (grade-data value group) → the `ℤ`-typing of
`aexp`.

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only) — including `iexp_aexp_spec`, which is a PROVED theorem
here and not the leanspec `axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- `i(k)`: the reduced x-exponent of the level-1 normalizer `n̂₁(k) = x^{i(k)}π^{a(k)}`
(`EFF.T1.01`).  Total; specified only under `0 < e₁` and `Nat.Coprime h e₁`. -/
def iexp (e₁ h : ℕ) (k : ℤ) : ℕ := ((k : ZMod e₁) * (h : ZMod e₁)⁻¹).val

/-- `a(k)`: the π-exponent, fixed by the exact-height identity (`EFF.T1.01`).  The `Int`
division is exact on the specified domain — see `iexp_aexp_spec`. -/
def aexp (e₁ h : ℕ) (k : ℤ) : ℤ := (k - iexp e₁ h k * h) / e₁

/-- The exact-height identity `i(k)h + a(k)e₁ = k` together with the range bound
`0 ≤ i(k) < e₁` (`EFF.T1.01`). -/
theorem iexp_aexp_spec (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (k : ℤ) :
    iexp e₁ h k < e₁ ∧ (iexp e₁ h k : ℤ) * h + aexp e₁ h k * e₁ = k := by
  haveI : NeZero e₁ := ⟨he.ne'⟩
  refine ⟨ZMod.val_lt _, ?_⟩
  have hdvd : (e₁ : ℤ) ∣ (k - (iexp e₁ h k : ℤ) * h) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [iexp, ZMod.natCast_val, ZMod.cast_id, mul_assoc, ZMod.inv_mul_of_unit]
    · ring
    · exact (ZMod.unitOfCoprime h hcop).isUnit
  have hcancel := Int.ediv_mul_cancel hdvd
  rw [aexp]
  omega

/-- [A-D.1/D-D1] `iexp` at `h = 1`.  PROVED, and load-bearing for the whole §10 gate
programme: `ZMod.inv` routes through `Nat.gcdA` and does NOT kernel-reduce, so no `decide` can
evaluate `iexp` as defined (defect D-D1).  Every original gate frame of this chapter has
`h = 1`, where the `ZMod`-inverse disappears and the reduced form IS `decide`-able. -/
theorem iexp_one (e₁ : ℕ) (k : ℤ) : iexp e₁ 1 k = ((k : ZMod e₁)).val := by simp [iexp]

/-- [A-D.1/D-F1] The general reduction, needed by the `h > 1` frame FRAME-H2 (§10 leg 5).
The inverse `c` of `h` is supplied as DATA, its defining equation `hc` being `decide`-able at
any concrete frame; this is what makes `iexp` computable when `h ≠ 1`. -/
theorem iexp_eq_of_inv (e₁ h : ℕ) (c : ZMod e₁) (hc : (h : ZMod e₁) * c = 1) (k : ℤ) :
    iexp e₁ h k = ((k : ZMod e₁) * c).val := by
  simp [iexp, ZMod.inv_eq_of_mul_eq_one _ _ _ hc]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.iexp
#print axioms Uniformity.Density.Gauge.aexp
#print axioms Uniformity.Density.Gauge.iexp_aexp_spec
#print axioms Uniformity.Density.Gauge.iexp_one
#print axioms Uniformity.Density.Gauge.iexp_eq_of_inv

end AxCheck
