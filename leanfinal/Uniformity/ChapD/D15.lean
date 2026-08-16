/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D14

/-!
# Uniformity.ChapD.D15 — `qexp`, the carry exponent and `(C5-carry)`

**Chapter D, NODE D.15** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1 and A-D.1 govern — A-D.1 does not re-sign the SIGNATURE but DOES
amend the TEETH row, which is what the executed frame at the foot of this file discharges).
ENV-D1 — the arithmetic arena: pure `ℕ`/`ℤ`, no `O`, no polynomials. Two signed declarations (the
definition and its one lemma), the `qexp` body reused byte-for-byte from the gate-verified stub
`leanspec/Leanspec/ChapD.lean`.

*The carry exponent `q(k)` and `(C5-carry)`.* With `i₀ := iexp e₁ h 1`,

  `qexp e₁ h k := (i₀·k − iexp e₁ h k)/e₁ : ℤ`,   `q(a+b) = q(a) + q(b) + wrap(a,b)`.

This is `EFF.T1.19`'s boxed `(C5-carry)`. The `wrap` on the right is D.14's bit, so the carry law
says exactly that `q` is additive up to the level-1 wrap — `q` is the deviation of `k ↦ i₀·k` from
the reduced exponent, measured in units of `e₁`.

## Integrality of the defining division (why `/` is exact here)

`qexp` is written with `Int` division, which would silently truncate if `e₁ ∤ i₀k − i(k)`. It does
divide, and the proof is inside `qexp_add` as its first step: from D.13's exact-height identity at
`k = 1` and at `k`,

  `(i₀·k − i(k))·h = e₁·(a(k) − a(1)·k)`,

so `e₁ ∣ (i₀k − i(k))·h`, and `Nat.Coprime h e₁` upgrades that to `e₁ ∣ i₀k − i(k)`
(`IsCoprime.dvd_of_dvd_mul_right` after `Nat.isCoprime_iff_coprime`). The coprimality hypothesis
is therefore NOT decoration: without it the definition's division is not exact and the carry law
is false. The one-line identity above is `linear_combination k * (spec 1) - (spec k)` — the corpus
instruction "multiply the difference by `e₁` and use `i(a)+i(b)−i(a+b) = e₁ wrap(a,b)`"
(`EFF.T1.19`) run in the only order Lean will accept.

## The route (the blueprint's own, executed)

1. **`key`:** `(e₁ : ℤ) * qexp e₁ h k = i₀·k − i(k)` for every `k`, by `Int.mul_ediv_cancel'` on
   the divisibility just described. This is the "clear the exact division" step.
2. **`hwz`:** D.14's wrap identity `i(a) + i(b) = i(a+b) + e₁·wrap(a,b)`, cast from `ℕ` to `ℤ`.
3. **cancel `e₁`:** the goal is multiplied through by `e₁` (`mul_left_cancel₀`, legitimate since
   `0 < e₁`) and closed by `linear_combination key (a+b) - key a - key b + hwz` — the four facts
   combine to the law with all cross terms `i₀·(a+b) = i₀·a + i₀·b` handled by `ring` inside
   `linear_combination`.

## ⚠ FINDING D-F1, and why the frame at the foot of this file is MANDATORY

`(A-D.1)` **No `h = 1` frame can score this node.** At `h = 1` we have `i₀ = iexp e₁ 1 1 = 1`, so

  `qexp e₁ 1 k = (k − i(k))/e₁ = aexp e₁ 1 k`  identically,

and the X frame's leg-1 tables (D.66 leg 1, `e₁ = 2, h = 1`) score the SAME function twice — both
come out `[-1,-1,0,0,1,1,2,2,3]` on `k = −2…6`. An `aexp`/`qexp` confusion survives that gate
untouched. This is a coverage hole in the frame, not a defect in D.13/D.15, and A-D.1 closes it by
ADDING a frame: **FRAME-H2**, `e₁ = 3, h = 2` (coprime), where `2⁻¹ = 2` in `ZMod 3` and hence
`i₀ = iexp 3 2 1 = 2 ≠ 1`. It is signed as D.66 leg 5, and it is executed below at this node's own
source so that D.15 is scored independently wherever it is read.

The separation FRAME-H2 buys, in one line: `aexp 3 2 k ≠ qexp 3 2 k` for every `k ∈ {1,…,6}` (they
agree only at `k ∈ {−2,−1,0}`) — in particular at `k = 1`, where `aexp = −1` and `qexp = 0`. An
`aexp`/`qexp` swap now fails a `decide`.

## The A-D.1 gate-writing rider, honoured below

`iexp` is NOT `decide`-reducible (defect D-D1, recorded at its source in D.13). At `h = 2` even
D.13's `iexp_one` does not apply, so every executed row here reduces through D.13's OTHER proved
reducer, `iexp_eq_of_inv`, with the inverse `c = 2` of `h = 2` in `ZMod 3` supplied as DATA and its
defining equation `((2 : ℕ) : ZMod 3) * 2 = 1` discharged by `decide`. The pattern is
`simp only [<local defs>, frameH2_iexp]` **then** `decide`, never a bare `decide`, and never
`native_decide`.

## Faithfulness

**⚠ Trust-boundary definition.** `qexp` is typed `ℤ` (heights and carries are integers,
`EFF.T1.02`'s integrality clause), and `i₀` is spelled `iexp e₁ h 1` inside the body rather than
carried as a parameter — that is `EFF.T1.19`'s own `q(k) = (i₀k − i(k))/e₁` with `i₀ = i(1)`. The
sign convention is the displayed one: `i₀·k` MINUS `i(k)`, and `+ wrap(a,b)` on the right of the
carry law. Negative heights need no hypothesis (`Int./` is `ediv` at the pin; A-D.1's
negative-height answer, recorded at D.13), and the frame below runs `k = −3…6` to score that.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

DEPENDS: D.13 (`iexp`, `aexp`, `iexp_aexp_spec`, `iexp_eq_of_inv`), D.14 (`wrap`,
`iexp_add_wrap`) — both landed at `Uniformity.ChapD.D13`/`D14`; mathlib
`Nat.isCoprime_iff_coprime`, `IsCoprime.dvd_of_dvd_mul_right`, `Int.mul_ediv_cancel'`,
`mul_left_cancel₀`, `linear_combination` — all name-verified at the v4.31.0 pin.

SOURCE: `EFF.T1.19` (the boxed `(C5-carry)` `q(a+b) = q(a)+q(b)+wrap(a,b)`, and
`q(k) = (i₀k − i(k))/e₁`).

**TEETH** *[amended: A-D.1/D-F1]*. T1's A2 consumption regression + §4.2 check 4 (the `−q(k)`
sign) → THIS Lean theorem (and D.19); gate D.66 legs 1 **and 5**. Leg 5 — FRAME-H2, the `h > 1`
separator — is executed at the foot of this file, which is the only place in chapter D where
`qexp` is scored as a function distinct from `aexp`.

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only): `qexp_add` is a PROVED theorem here, not the leanspec
`axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.15 (def) — the carry exponent.** `q(k) = (i₀k − i(k))/e₁` with `i₀ = i(1)`
(`EFF.T1.19`).  The `Int` division is EXACT under `0 < e₁` and `Nat.Coprime h e₁` — the
divisibility is proved inside `qexp_add`. -/
def qexp (e₁ h : ℕ) (k : ℤ) : ℤ := (iexp e₁ h 1 * k - iexp e₁ h k) / e₁

/-- **D.15 (lemma) — `(C5-carry)`.** `q(a+b) = q(a) + q(b) + wrap(a,b)` (`EFF.T1.19`): the carry
exponent is additive up to D.14's wrap bit.  Both hypotheses are load-bearing — `hcop` is what
makes the defining division of `qexp` exact. -/
theorem qexp_add (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (a b : ℤ) :
    qexp e₁ h (a + b) = qexp e₁ h a + qexp e₁ h b + wrap e₁ h a b := by
  have hcopZ : IsCoprime (e₁ : ℤ) (h : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  -- (1) clear the exact division: `e₁ * q(k) = i₀·k − i(k)`, for every `k`.
  have key : ∀ k : ℤ, (e₁ : ℤ) * qexp e₁ h k
      = (iexp e₁ h 1 : ℤ) * k - (iexp e₁ h k : ℤ) := by
    intro k
    have h1 := (iexp_aexp_spec e₁ h he hcop 1).2
    have hk := (iexp_aexp_spec e₁ h he hcop k).2
    have hmul : ((iexp e₁ h 1 : ℤ) * k - (iexp e₁ h k : ℤ)) * (h : ℤ)
        = (e₁ : ℤ) * (aexp e₁ h k - aexp e₁ h 1 * k) := by
      linear_combination k * h1 - hk
    have hdvd : (e₁ : ℤ) ∣ ((iexp e₁ h 1 : ℤ) * k - (iexp e₁ h k : ℤ)) :=
      hcopZ.dvd_of_dvd_mul_right ⟨_, hmul⟩
    exact Int.mul_ediv_cancel' hdvd
  -- (2) D.14's wrap identity, in `ℤ`.
  have hwz : (iexp e₁ h a : ℤ) + (iexp e₁ h b : ℤ)
      = (iexp e₁ h (a + b) : ℤ) + (e₁ : ℤ) * (wrap e₁ h a b : ℤ) := by
    exact_mod_cast (iexp_add_wrap e₁ h he hcop a b).1
  -- (3) multiply the goal by `e₁` and combine.
  refine mul_left_cancel₀ (a := (e₁ : ℤ)) (by exact_mod_cast he.ne') ?_
  linear_combination key (a + b) - key a - key b + hwz

end Uniformity.Density.Gauge

/-! ## FRAME-H2, EXECUTED (D.66 leg 5; the A-D.1/D-F1 repair)

`e₁ = 3, h = 2`, coprime, so `2⁻¹ = 2` in `ZMod 3` and `i₀ = iexp 3 2 1 = 2 ≠ 1`.  This is the
ONLY frame of chapter D at which `qexp` is a different function from `aexp`, so it is the only
frame that scores D.15 independently (finding D-F1).  Every row reduces through D.13's
`iexp_eq_of_inv` BEFORE deciding — at `h = 2` even `iexp_one` does not apply, and a bare `decide`
on any row mentioning `iexp`, `aexp`, `qexp` or `wrap` does not compile (defect D-D1). -/

section FrameH2

open Uniformity.Density.Gauge

/-- FRAME-H2's inverse datum, `decide`-able: `2 · 2 = 1` in `ZMod 3`. -/
private theorem frameH2_inv : ((2 : ℕ) : ZMod 3) * 2 = 1 := by decide

/-- The GC-11 reducer at FRAME-H2: `iexp 3 2 k = (2k mod 3)`, from D.13's `iexp_eq_of_inv`. -/
private theorem frameH2_iexp (k : ℤ) : iexp 3 2 k = ((k : ZMod 3) * 2).val :=
  iexp_eq_of_inv 3 2 2 frameH2_inv k

/-- The frame is live: `i₀ = iexp 3 2 1 = 2 ≠ 1`.  At `h = 1` this number is `1`, which is exactly
why the `h = 1` frames collapse `qexp` onto `aexp`. -/
example : iexp 3 2 1 = 2 ∧ iexp 3 2 1 ≠ 1 := by
  simp only [frameH2_iexp]; decide

/-- `iexp 3 2` on `k = −3 … 6` — negative heights included. -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => iexp 3 2 k)
    = [0, 2, 1, 0, 2, 1, 0, 2, 1, 0] := by
  simp only [frameH2_iexp]; decide

/-- `aexp 3 2` on `k = −3 … 6`. -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => aexp 3 2 k)
    = [-1, -2, -1, 0, -1, 0, 1, 0, 1, 2] := by
  simp only [aexp, frameH2_iexp]; decide

/-- `qexp 3 2` on `k = −3 … 6`. -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => qexp 3 2 k)
    = [-2, -2, -1, 0, 0, 1, 2, 2, 3, 4] := by
  simp only [qexp, frameH2_iexp]; decide

/-- **THE SEPARATION (finding D-F1's repair).** `aexp 3 2 k ≠ qexp 3 2 k` for every
`k ∈ {1,…,6}` — at `k = 1`, `aexp = −1` while `qexp = 0`.  An `aexp`/`qexp` swap fails here. -/
example : ∀ k ∈ ([1, 2, 3, 4, 5, 6] : List ℤ), aexp 3 2 k ≠ qexp 3 2 k := by
  simp only [aexp, qexp, frameH2_iexp]; decide

/-- The complementary half of the separation: the two functions AGREE exactly on
`k ∈ {−2, −1, 0}` inside the tabulated range, so the frame's discriminating power is a fact about
the range and not an accident of one point. -/
example : ∀ k ∈ ([-2, -1, 0] : List ℤ), aexp 3 2 k = qexp 3 2 k := by
  simp only [aexp, qexp, frameH2_iexp]; decide

/-- `(C5-carry)` EXECUTED at FRAME-H2 on `a, b ∈ {−2,…,3}` — this node's law, at `h > 1`. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    qexp 3 2 (a + b) = qexp 3 2 a + qexp 3 2 b + wrap 3 2 a b := by
  simp only [qexp, wrap, frameH2_iexp]; decide

/-- D.14's `(C2-wrap)` on the same grid at `h = 2`, where `iexp` is genuinely three-valued
(`{0,1,2}`) while the wrap bit is still `{0,1}` — the `h = 1` frames cannot show that gap. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    iexp 3 2 a + iexp 3 2 b = iexp 3 2 (a + b) + 3 * wrap 3 2 a b ∧ wrap 3 2 a b ≤ 1 := by
  simp only [wrap, frameH2_iexp]; decide

end FrameH2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.qexp
#print axioms Uniformity.Density.Gauge.qexp_add

end AxCheck
