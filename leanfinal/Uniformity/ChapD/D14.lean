/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D13

/-!
# Uniformity.ChapD.D14 — the wrap bit and `(C2-wrap)`

**Chapter D, NODE D.14** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1 and A-D.1 govern — neither re-signs this node, so the SIGNATURE
below is the one signed at composition and re-stubbed at stage 0e in
`leanspec/Leanspec/ChapD.lean`, whose `wrap` body is reused here byte-for-byte). ENV-D1 — the
arithmetic arena: pure `ℕ`/`ℤ`, no `O`, no polynomials. Two signed declarations (the definition
and its one lemma, whose two clauses are conjoined exactly as signed).

*The wrap bit and `(C2-wrap)`.* `wrap e₁ h a b := (iexp a + iexp b) / e₁` (`ℕ`-division). Then
(i) the **wrap identity** `iexp a + iexp b = iexp (a+b) + e₁ * wrap a b`, and (ii)
`wrap ∈ {0,1}` — the exponent form of `(C2-wrap)`'s monomial display
`n̂₁(a)n̂₁(b) = n̂₁(a+b)·(x^{e₁}/π^h)^{wrap(a,b)}`. The monomial form itself is NOT proved here:
it is a D.17-arena corollary, proved there as the `tau` computation.

## The sign convention, and the wrong-sign tooth

T1 §4.2 check 2 (the "positive-wrap" and "wrong-sign" teeth) is scored by the placement of the
correction term: it is `+ e₁ * wrap a b` on the RIGHT of `iexp (a + b)`, i.e. the reduced
exponents of `a` and `b` OVERSHOOT the reduced exponent of `a + b` by exactly one full period
`e₁` whenever the reduction wraps. A transcription with the term on the left, or with a minus
sign, is a different (and false) statement; the executed frame below is what makes that
mechanical rather than editorial.

## The route (the blueprint's own, executed)

The corpus derivation is "the reduced exponent satisfies `i(a)+i(b) = i(a+b) + e₁ wrap(a,b)`"
(`EFF.T1.07`). Its Lean form is the `ZMod`-additivity of `iexp` composed with `Nat.mod_add_div`:

1. **`iexp` is `%`-additive.** `iexp e₁ h (a + b) = (iexp e₁ h a + iexp e₁ h b) % e₁`. Both sides
   are `ZMod.val` of the same element: `(↑(a+b) * (h : ZMod e₁)⁻¹) = ↑a * (h : ZMod e₁)⁻¹
   + ↑b * (h : ZMod e₁)⁻¹` (`Int.cast_add` + `add_mul`), and `ZMod.val_add` turns the `val` of a
   sum into the `%`-reduced sum of the `val`s. Note this step needs NEITHER `he` nor `hcop` — it
   is pure `ZMod` arithmetic, valid for whatever element `(h : ZMod e₁)⁻¹` happens to be. The two
   hypotheses are consumed only in clause (ii), through D.13's range bound.
2. **The identity is then `Nat.mod_add_div`.** With `n := iexp a + iexp b`, clause (i) reads
   `n = n % e₁ + e₁ * (n / e₁)`, which is `(Nat.mod_add_div n e₁).symm` on the nose — `wrap` was
   defined to be that quotient.
3. **`wrap ≤ 1`** from `n < 2 * e₁` (two applications of D.13's `iexp < e₁`, which is where `he`
   and `hcop` enter) via `Nat.div_lt_iff_lt_mul`.

## The A-D.1 gate-writing rider, honoured in the executed frame below

`iexp` is NOT `decide`-reducible (defect D-D1, recorded at its source in D.13: `(h : ZMod e₁)⁻¹`
unfolds to `ZMod.inv`, which routes through `Nat.gcdA`/`Nat.xgcd` and does not kernel-reduce).
So the local frame at the end of this file — the F4-JOINT/X-frame `e₁ = 2, h = 1` live-wrap
table, executed on a grid that INCLUDES negative heights — goes
`simp only [wrap, iexp_one]; decide` and never a bare `decide`. `iexp_one` is D.13's PROVED
reduction at `h = 1`. No `native_decide` anywhere.

DEPENDS: D.13 (`iexp`, `iexp_aexp_spec`, `iexp_one`) · mathlib `ZMod.val_add`,
`Nat.mod_add_div`, `Nat.div_lt_iff_lt_mul` — all name-verified at the v4.31.0 pin.

SOURCE: `EFF.T1.07` (the boxed `(C2-wrap)` and `wrap(a,b) = ⌊(i(a)+i(b))/e₁⌋ ∈ {0,1}`).

**TEETH.** T1 §4.2 check 2 + the "positive-wrap" and "wrong-sign" teeth → this Lean theorem (the
sign convention above) + gates D.65/D.66 (wrap tables at both primes; the frame below is the
D.66 leg-1 grid).

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only): `iexp_add_wrap` is a PROVED theorem here, not the
leanspec `axiom` stub. `wrap` is a plain `ℕ`-valued definition — **flagged for human review**
only insofar as `ℕ`-division is the intended `⌊·⌋` of the corpus display (it is: both `iexp`s are
nonnegative, so no truncation subtlety arises).
-/

namespace Uniformity.Density.Gauge

/-- **D.14 (def) — the wrap bit.** `wrap(a,b) = ⌊(i(a)+i(b))/e₁⌋` (`EFF.T1.07`).  Total; the
`{0,1}` clause of `iexp_add_wrap` is what pins it to a bit, and needs `0 < e₁`. -/
def wrap (e₁ h : ℕ) (a b : ℤ) : ℕ := (iexp e₁ h a + iexp e₁ h b) / e₁

/-- **D.14 (lemma) — `(C2-wrap)`.** The wrap identity
`i(a) + i(b) = i(a+b) + e₁·wrap(a,b)` — correction term POSITIVE and on the right — together
with `wrap(a,b) ≤ 1` (`EFF.T1.07`).  The exponent form of the monomial display
`n̂₁(a)n̂₁(b) = n̂₁(a+b)·(x^{e₁}/π^h)^{wrap(a,b)}`; the monomial form is D.17's `tau`
computation. -/
theorem iexp_add_wrap (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (a b : ℤ) :
    iexp e₁ h a + iexp e₁ h b = iexp e₁ h (a + b) + e₁ * wrap e₁ h a b
    ∧ wrap e₁ h a b ≤ 1 := by
  haveI : NeZero e₁ := ⟨he.ne'⟩
  -- (1) `iexp` is `%`-additive: pure `ZMod` arithmetic, no hypothesis on `h` needed.
  have hsplit : ((a + b : ℤ) : ZMod e₁) * (h : ZMod e₁)⁻¹
      = ((a : ℤ) : ZMod e₁) * (h : ZMod e₁)⁻¹ + ((b : ℤ) : ZMod e₁) * (h : ZMod e₁)⁻¹ := by
    push_cast
    ring
  have hmod : iexp e₁ h (a + b) = (iexp e₁ h a + iexp e₁ h b) % e₁ := by
    simp only [iexp, hsplit, ZMod.val_add]
  -- (3) the bit clause, from D.13's range bound at `a` and at `b`.
  have hsum : iexp e₁ h a + iexp e₁ h b < 2 * e₁ := by
    have h1 : iexp e₁ h a < e₁ := (iexp_aexp_spec e₁ h he hcop a).1
    have h2 : iexp e₁ h b < e₁ := (iexp_aexp_spec e₁ h he hcop b).1
    omega
  have hle : wrap e₁ h a b ≤ 1 := by
    have hlt : (iexp e₁ h a + iexp e₁ h b) / e₁ < 2 :=
      (Nat.div_lt_iff_lt_mul he).2 (by omega)
    simpa [wrap] using Nat.lt_succ_iff.mp hlt
  -- (2) the identity is `Nat.mod_add_div` once `iexp (a+b)` is the remainder.
  refine ⟨?_, hle⟩
  rw [hmod, wrap]
  exact (Nat.mod_add_div _ _).symm

end Uniformity.Density.Gauge

/-! ## The executed frame (A-D.1 gate-writing rider: `simp only [...]; decide`, never bare)

The X-frame `e₁ = 2, h = 1` of D.66 leg 1, run here at its source so that the sign convention of
`iexp_add_wrap` is scored by a machine and not by a reader: `(C2-wrap)` on a grid that INCLUDES
negative heights, and the "live wrap" characterisation `wrap = 1` exactly on odd/odd.  Both rows
reduce through D.13's `iexp_one` BEFORE deciding — a bare `decide` on any row mentioning `iexp`
or `wrap` does not compile (defect D-D1). -/

section Frame

open Uniformity.Density.Gauge

/-- `(C2-wrap)` EXECUTED at `e₁ = 2, h = 1` on `a, b ∈ {−2,…,3}` — negative heights included. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    iexp 2 1 a + iexp 2 1 b = iexp 2 1 (a + b) + 2 * wrap 2 1 a b
      ∧ wrap 2 1 a b ≤ 1 := by
  simp only [wrap, iexp_one]; decide

/-- The live wrap: at `e₁ = 2, h = 1` the bit fires exactly on odd/odd. -/
example : ∀ a ∈ ([0, 1, 2, 3] : List ℤ), ∀ b ∈ ([0, 1, 2, 3] : List ℤ),
    (wrap 2 1 a b = 1 ↔ (iexp 2 1 a = 1 ∧ iexp 2 1 b = 1)) := by
  simp only [wrap, iexp_one]; decide

end Frame

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.wrap
#print axioms Uniformity.Density.Gauge.iexp_add_wrap

end AxCheck
