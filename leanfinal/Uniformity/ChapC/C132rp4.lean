/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp1

/-!
# Uniformity.ChapC.C132rp4 — the μ₃ grade-sum arithmetic: parity, endpoint sums, carry (μ₃ campaign, node M3-RP4)

**[M3-RP4, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP4):
the pure `s_r`/`u_r` grade-ADDITION arithmetic (published Definition 3.12, p. 16) at the μ₃
numerals `(e₃, h₃) = (2, 21)`, completing C132rp1's Part 0 uniqueness pins
(`s2Mu3_def312_level3`, a SINGLE grade) to the TWO-grade sum case that M3-RP5's (future)
convolution proof will need — mirroring exactly the shape of the old μ₂ arithmetic used
inside `C130rp4.lean`'s coefficient convolution (`s2GradedCoeff_mul_aux`'s `hcpar` premise,
`C130rp4.lean:479-485`, and its four-way-parity instantiation at `C130rp4.lean:635-637`) and
U14's adjudicated carry formula (`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §5):

```text
s = s₃(α), t = s₃(β), c = ⌊(s+t)/e₃⌋ ∈ {0,1};
s₃(α+β) = s+t-c·e₃,  u₃(α+β) = u₃(α)+u₃(β)+c·h₃;
at S2, e₃ = 2, so c = ((β%2)+(β'%2))/2 = (β%2)·(β'%2).
```

Since `e₃ = e₂ = 2` (the SAME abscissa modulus at every S2 level), the carry-exponent
identity itself carries VERBATIM from the μ₂ occurrence — no numeral changes at all — while
the `u`-level sum law is the μ₃ numeral instance (`h₃ = 21` in place of `h₂ = 5`), REUSED by
directly invoking C132rp1's already-landed single-grade uniqueness pin
`s2Mu3_def312_level3` rather than re-deriving it.

## What lands

* **the carry exponent** `s2Mu3Carry β β' := (β % 2) * (β' % 2)` and **U14's carry formula**
  `s2Mu3Carry_parity : β % 2 + β' % 2 = (β + β') % 2 + 2 * s2Mu3Carry β β'` — the four-way
  parity check, named and reusable (the inline proof `C130rp4.lean:635-637` generalizes to a
  standalone lemma; it does not mention `h₂`/`h₃`, so it is IDENTICAL at every S2 level).
* **the abscissa endpoint sum** `s2Mu3_abscissa_sum` — published eq (11)'s two abscissae
  `β%2+2t` (grade `β`, index `t`) and `β'%2+2(T-t)` (grade `β'`, index `T-t`) sum to the
  grade-`(β+β')` abscissa at index `T + s2Mu3Carry β β'` — the pure `ℕ` identity M3-RP5's
  convolution reindexing will consume (the μ₃ analogue of `C130rp4.lean`'s `himg` step,
  `C130rp4.lean:574-582`).
* **the gate-level endpoint sum** `s2Mu3SlotOnGrade_abscissa_sum` — BUILDS ON (does not
  re-prove) C132rp1's landed `s2Mu3SlotOnGrade_parity`: for on-line slots `s` of `g` at grade
  `β` and `s'` of `z` at grade `β'`, `s + s' = (β+β')%2 + 2*(s/2 + s'/2 + s2Mu3Carry β β')` —
  the abscissa sum re-expressed against the actual gate `S2Mu3SlotOnGrade`, not just its raw
  numerals.
* **the `u`-value endpoint sum** `s2Mu3_def312_add` — Definition 3.12's second coordinate
  addition law `u₃(α+β) = u₃(α)+u₃(β)+c·h₃` at `h₃ = 21`, stated in the same
  solved-linear-equation idiom as `s2Mu3_def312_level3` (no bespoke division-based
  definition) and proved by REUSING that lemma's two instances (at `β` and at `β'`) plus the
  carry formula — not a fresh derivation of the line arithmetic.
* two numeral teeth (`tooth_carry_Φ₂Φ₂`, `tooth_def312_add_Φ₂Φ₂`) at the odd×odd pair
  `β = β' = 21` (both on `Φ₂`'s own grade), the carry genre COR412 §5 flags as the
  non-vacuous tooth.

## What this node does NOT claim (honesty scope)

* No convolution, no polynomial-level product law, no `s2Mu3GradedRes` assembly: M3-RP5/RP6.
  In particular `s2Mu3SlotOnGrade_abscissa_sum` is NOT the (false in general) claim that
  on-line slots of `g` and `z` combine into an on-line slot of `g*z` — the μ₂ precedent
  (`C130rp4.lean`'s heavy `s2GradedCoeff_mul_aux`, using `dev_mul_conv_split`, `carry_floor`,
  and `twistRead` additivity) shows that step needs the actual convolution machinery, not
  slot arithmetic alone. This node supplies only the numeral bookkeeping that machinery will
  index by.
* No use of M3-NV4's conditional minimizer apparatus (`Dv2OnSide`/`dv2SideMin`,
  `s2_dv2OnSide_mul_endpoint_at_21`): the numeral `h₃ = 21` this file uses everywhere is
  already pinned by C132rp1 (which itself inherits it from NV4/NV1's `(u₃,ℓ₃) = (21,2)`
  fixing), so no additional NV4 theorem is consumed to validate it.
* `s2Mu3Carry_parity` restates the general COR412 §5 formula only at `e₃ = 2`; no claim about
  a general `e_r`.

**DEPENDS.** C132rp1 (`S2Mu3SlotOnGrade`, `s2Mu3SlotOnGrade_iff`, `s2Mu3SlotOnGrade_parity`,
`s2Mu3_def312_level3`, `tooth_mu3_gate_Φ₂`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch and U14's adjudicated formula.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2Mu3Carry_parity`, `s2Mu3_abscissa_sum`, `s2Mu3SlotOnGrade_abscissa_sum`,
`s2Mu3_def312_add`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132rp1

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — ★ the μ₃ carry exponent, and U14's carry formula

Published Definition 3.12's carry `c = ⌊(s_r(α)+s_r(β))/e_r⌋` at `e₃ = 2`: since
`s₃(α), s₃(β) ∈ {0,1}`, the floor collapses to the PRODUCT of the two parities
(`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §5). This identity mentions no `h`,
so it is the same fact at every S2 level (μ₂ or μ₃); it is stated once here, named, for
M3-RP5 to reuse without re-deriving. -/

/-- ★ **the μ₃ carry exponent** (U14's `c`, COR412 §5): `(β%2)·(β'%2)`. -/
def s2Mu3Carry (β β' : ℕ) : ℕ := β % 2 * (β' % 2)

/-- the carry is Boolean-valued: `0` (mixed/even-even parity) or `1` (odd×odd). -/
theorem s2Mu3Carry_eq_zero_or_one (β β' : ℕ) :
    s2Mu3Carry β β' = 0 ∨ s2Mu3Carry β β' = 1 := by
  unfold s2Mu3Carry
  rcases Nat.mod_two_eq_zero_or_one β with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one β' with h' | h' <;> rw [h, h'] <;> omega

/-- ★ **U14's carry formula** (`COR412_ADJUDICATION_2026-08-25.md` §5, the four-way parity
check): `β%2 + β'%2 = (β+β')%2 + 2·s2Mu3Carry β β'` — the exact linear relation
`s2GradedCoeff_mul_aux`'s `hcpar` premise instantiates at μ₂ (`C130rp4.lean:635-637`); named
here so M3-RP5 reuses it rather than re-deriving the case split. -/
theorem s2Mu3Carry_parity (β β' : ℕ) :
    β % 2 + β' % 2 = (β + β') % 2 + 2 * s2Mu3Carry β β' := by
  unfold s2Mu3Carry
  rcases Nat.mod_two_eq_zero_or_one β with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one β' with h' | h' <;> rw [h, h'] <;> omega

/-! ## Part 2 — ★ the abscissa endpoint sum (published eq (11)'s index arithmetic)

The `t`-th abscissa of the grade-`β` line is `β%2+2t` (C132rp1's `s2Mu3Coeff_slot`
indexing); the endpoint sum is the statement that the abscissae of grade `β` at index `t`
and of grade `β'` at index `T-t` add EXACTLY to the abscissa of the combined grade `β+β'`
at index `T` shifted by the carry. -/

/-- ★ **the abscissa endpoint sum**: `(β%2+2t) + (β'%2+2(T-t)) = (β+β')%2 + 2(T+c)` for
`t ≤ T` — the μ₃ analogue of `C130rp4.lean`'s reindexing step (`himg`, lines 574-582),
isolated as a pure `ℕ` fact so M3-RP5 need not re-derive it inside the convolution proof. -/
theorem s2Mu3_abscissa_sum (β β' T t : ℕ) (ht : t ≤ T) :
    (β % 2 + 2 * t) + (β' % 2 + 2 * (T - t)) = (β + β') % 2 + 2 * (T + s2Mu3Carry β β') := by
  have hc := s2Mu3Carry_parity β β'
  omega

/-! ## Part 3 — ★ the gate-level endpoint sum, BUILDING ON the landed parity pin

`s2Mu3SlotOnGrade_parity` (C132rp1, already landed — NOT re-proved here) pins that every
on-line slot has the grade's own parity; combined with Part 1's carry formula this reads the
abscissa endpoint sum directly against the gate `S2Mu3SlotOnGrade`, without unfolding to raw
numerals at the call site. -/

/-- ★ **the gate-level endpoint sum**: for `S2Mu3SlotOnGrade`-on-line slots `s` of `g` (at
grade `β`) and `s'` of `z` (at grade `β'`), `s + s' = (β+β')%2 + 2·(s/2 + s'/2 + c)` — the
abscissa sum read against the actual on-line slots rather than the abstract index arithmetic
of Part 2. (Does NOT assert `s+s'` is itself on-line for `g*z` at `β+β'` — see the honesty
scope above.) -/
theorem s2Mu3SlotOnGrade_abscissa_sum {β s β' s' : ℕ} {g z : Polynomial O}
    (h : S2Mu3SlotOnGrade h2 hq β g s) (h' : S2Mu3SlotOnGrade h2 hq β' z s') :
    s + s' = (β + β') % 2 + 2 * (s / 2 + s' / 2 + s2Mu3Carry β β') := by
  have hpar : s % 2 = β % 2 := s2Mu3SlotOnGrade_parity h2 hq h
  have hpar' : s' % 2 = β' % 2 := s2Mu3SlotOnGrade_parity h2 hq h'
  have hc := s2Mu3Carry_parity β β'
  omega

/-! ## Part 4 — ★ the `u`-value endpoint sum, REUSING `s2Mu3_def312_level3`

Published Definition 3.12's other coordinate: `u₃(α+β) = u₃(α)+u₃(β)+c·h₃` at `h₃ = 21`.
Stated in the same solved-linear-equation idiom as C132rp1's `s2Mu3_def312_level3` (no
bespoke division-based `u₃` definition is introduced), and proved by invoking that lemma at
`β` and at `β'` to pin `s = β%2`, `s' = β'%2`, then closing the resulting linear identity —
a REUSE, not a fresh derivation of the line arithmetic. -/

/-- ★ **the `u`-value endpoint sum** (Definition 3.12's `u₃(α+β) = u₃(α)+u₃(β)+c·h₃` at
`h₃ = 21`): if `u,s` solve the grade-`β` line equation and `u',s'` solve the grade-`β'` line
equation (both with `0 ≤ s,s' < 2`, `s2Mu3_def312_level3`'s hypotheses), then
`u+u'+21·c` solves the grade-`(β+β')` line equation against the NATURAL abscissa
`(β+β')%2`. -/
theorem s2Mu3_def312_add (β β' : ℕ) (u s u' s' : ℤ)
    (h : u * 2 + s * 21 = (β : ℤ)) (hs0 : 0 ≤ s) (hs2 : s < 2)
    (h' : u' * 2 + s' * 21 = (β' : ℤ)) (hs0' : 0 ≤ s') (hs2' : s' < 2) :
    (u + u' + 21 * (s2Mu3Carry β β' : ℤ)) * 2 + ((((β + β') % 2 : ℕ) : ℤ)) * 21
      = ((β + β' : ℕ) : ℤ) := by
  have hβs : s = ((β % 2 : ℕ) : ℤ) := (s2Mu3_def312_level3 β u s h hs0 hs2).1
  have hβ's' : s' = ((β' % 2 : ℕ) : ℤ) := (s2Mu3_def312_level3 β' u' s' h' hs0' hs2').1
  have hc : ((β % 2 : ℕ) : ℤ) + ((β' % 2 : ℕ) : ℤ)
      = (((β + β') % 2 : ℕ) : ℤ) + 2 * ((s2Mu3Carry β β' : ℕ) : ℤ) := by
    exact_mod_cast s2Mu3Carry_parity β β'
  have hβadd : ((β + β' : ℕ) : ℤ) = (β : ℤ) + (β' : ℤ) := by push_cast; ring
  omega

/-! ## Part 5 — teeth at the odd×odd pair `(21,21)` (COR412 §5's non-vacuous carry genre) -/

/-- **tooth (carry fires)**: at the odd×odd pair `β = β' = 21` (`Φ₂`'s own grade, twice),
the carry is `1`, not `0` — the genre COR412 §5 flags as non-vacuous. -/
theorem tooth_carry_Φ₂Φ₂ : s2Mu3Carry 21 21 = 1 := by decide

/-- **tooth (the `u`-sum fires at the carry pair)**: at `β = β' = 21`, `Φ₂`'s own on-line
solution `u = 0, s = 1` (`tooth_mu3_gate_Φ₂`'s data) combines to `u+u'+21·1 = 21` solving the
grade-`42` line at abscissa `42 % 2 = 0`. -/
theorem tooth_def312_add_Φ₂Φ₂ :
    ((0 : ℤ) + 0 + 21 * (s2Mu3Carry 21 21 : ℤ)) * 2 + (((42 % 2 : ℕ) : ℤ)) * 21
      = ((42 : ℕ) : ℤ) :=
  s2Mu3_def312_add 21 21 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end S2

end Uniformity.Density.Tower.C132rp4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp4.s2Mu3Carry
#print axioms Uniformity.Density.Tower.C132rp4.s2Mu3Carry_eq_zero_or_one
#print axioms Uniformity.Density.Tower.C132rp4.s2Mu3Carry_parity
#print axioms Uniformity.Density.Tower.C132rp4.s2Mu3_abscissa_sum
#print axioms Uniformity.Density.Tower.C132rp4.s2Mu3SlotOnGrade_abscissa_sum
#print axioms Uniformity.Density.Tower.C132rp4.s2Mu3_def312_add
#print axioms Uniformity.Density.Tower.C132rp4.tooth_carry_Φ₂Φ₂
#print axioms Uniformity.Density.Tower.C132rp4.tooth_def312_add_Φ₂Φ₂

end AxCheck
