/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C42

/-!
# Uniformity.ChapC.C50 — `slotOffset`, `gridWeight`, `E₂_gt_xfloor`: the composed grid and the SPLIT

**Chapter C, NODE C.50** [def+lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed
keys and the tower bridges — the GENTOW1 half; the A-C.1 amendment set governs).
**ENV-C5/C1**. Three signed declarations: two definitions and the one inequality that makes
`E₂` worth naming.

* `slotOffset T a b` — GENTOW1's **slot offset** `w(a,b) = a·e₂h + b·u₂`, the `dv₂`-cost of the
  composed slot `x^a Φ′^b`: `a` steps of the x-carry at `e₂h` apiece (level 1's `h`, rescaled by
  the inner ramification `e₂`), `b` steps of the `Φ′`-carry at the inner slope numerator `u₂`.
* `gridWeight T v a b j` — the **weight** of a monomial datum `(v, a, b, j)`:
  `wt = e₁e₂·v + w(a,b) + j·E₂`. Three graded contributions: `v` units of the composed
  uniformizer (priced `e₁e₂`, the composed ramification), the slot offset, and `j` powers of the
  composed key (priced `E₂`).
* `E₂_gt_xfloor T` — the **SPLIT**: `D₂·(e₂·h) < E₂`, i.e. `dv₂(x^{D₂}) < E₂`.

## The SPLIT, and why the node has to state it

At level 1 the key's side height and `dv(x^{D′})` are the same number, both `D′h`; the level-1
budget arithmetic quietly uses that coincidence. At level 2 the two separate, and `E₂ = e₂f₂u₂`
— *not* `dv₂(x^{D₂}) = D₂e₂h` — is the true floor. `EFF.GENTOW1.07` states the gap and its cause
verbatim: *"here they SPLIT: `E₂ > dv₂(x^{D₂}) = D₂e₂h = e₂f₂·(e₂D′h)`, by `u₂ > e₂D′h`"*. This
is the structural novelty COR GENTOW-1.1 turns on, and it is the reason C.42 recorded the node
floor `hfloor : e₂·(e₁f₁)·h < u₂` as a *field* of `TowerDatum` rather than deriving it: the SPLIT
is exactly that field, multiplied through by `e₂f₂`.

The whole proof, in one line: `E₂ = e₂f₂·u₂ > e₂f₂·(e₂·e₁f₁·h) = (e₁f₁·e₂f₂)·e₂h = D₂·e₂h`,
using `hfloor` once and `0 < e₂f₂` once. The positivity comes from `hcomp : 2 ≤ e₂ * f₂` (C.42's
chapter-added nondegeneracy fence), not from `he₂`/`hf₂` separately, and it is genuinely needed:
multiplying a strict ℕ-inequality through by `0` would collapse it.

**The degenerate frame is covered.** `KeyFrame` admits `h = 0` (C.01's docstring: the degenerate
frame, kept so that C.05's level-1 reconciliation is definitional). At `h = 0` the statement reads
`0 < E₂`, and the argument still delivers it — `hfloor` becomes `0 < u₂`, and `e₂f₂·u₂ > 0`. No
case split is needed, and none is made. (The gate's `c50_grid` in `leanspec/Leanspec/ChapC.lean`
ranges `h` from `0`, precisely to exercise this.)

## What is signed here, and what is not

The blueprint STATEMENT's lemma half lists **three** items: the SPLIT, and the *two term-family
verifications* — `Φ′^{e₂f₂}` sits at `e₂f₂·u₂ = E₂`, and the `t`-th lift term at
`e₂u₂(f₂−t) + e₂t·u₂ = E₂`, the same value for every `t`. Only the SPLIT is signed. The two
verifications are not declarations here (signatures are frozen; a node may not grow one) and
they are in any case identities about a key this node does not yet have — `Φ₂` is C.43's — so
they land as arithmetic, mirrored in the `#guard` section below. Note their own ℕ-caveat: the
lift-term identity is `e₂u₂(f₂−t) + e₂tu₂ = e₂u₂f₂` only for `t ≤ f₂`; at `t > f₂` the truncated
`f₂ − t` is `0` and the left side overshoots. The scope `t < f₂` is the summation range of
C.43's key, so nothing is lost, but a consumer must carry it.

Also unsigned: the **grid ranges**. The STATEMENT says the composed grid indexes `(j, a, b)` with
`a < D′`, `b < e₂f₂`, `j < μ₂`. `slotOffset` and `gridWeight` are total functions of `ℕ`
arguments and enforce none of that — the ranges are the consumers' (`towerLocus_iff_budget`,
C.52, quantifies them explicitly). Nothing below is false off-range; it is merely uninterpreted.

**A scope note transcribed from `EFF.GENTOW1.08`, because it is easy to lose.** The weight is a
**lower bound** statement on the locus, not an equality: *"wt = dv₂ of the evaluated monomial …
on the actual locus a LOWER bound with the `j`-graded part strict"*. Every "weight ≥ W" claim
downstream is to be read that way. `gridWeight` itself is just the number; it asserts nothing,
and in particular this node proves no relation between `gridWeight` and any valuation.

## Divergence from the blueprint SIGNATURE (twin authoritative)

Two, both cosmetic, both from the leanspec gate:

* **D2** — the blueprint writes `def slotOffset {F : KeyFrame O π} {H₀ hpin} (T : …) (a b : ℕ)`
  in full but `def gridWeight … (v a b j : ℕ) : ℕ` with a literal ellipsis for the binder list.
  C.50 is one of the four nodes the gate classifies as *"the surrounding prose forces a unique
  reading of the omitted binders"*, and the twin completes it as
  `{F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin)` — the only reading under which the
  signed body typechecks. Same completion C.42 already carries for `D₂`/`E₂`.
* The blueprint display writes the slot offset as `a * e₂ * h + b * u₂`; the twin writes
  `a * (T.e₂ * F.h) + b * T.u₂`. Identical by associativity of `*`; the twin's parenthesization
  is what lands, and it is the readable one (`e₂h` is the rescaled x-carry price, one quantity).

**DEPENDS.** C.42 (`TowerDatum` and its `e₂`, `f₂`, `u₂`, `hcomp`, `hfloor`; `TowerDatum.D₂`,
`TowerDatum.E₂`) · C.01 (`KeyFrame.e₁`, `KeyFrame.f₁`, `KeyFrame.h`) — by committed node ID
(GC-13(b)). The single import is `Uniformity.ChapC.C42`, which pulls C.03, C.01 and the B chain.
Nothing from the HETOW half of §6 is needed: C.50 does not mention the composed key, the wrap, or
the stage letter, and deliberately does not import C.41 or C.43.

**PROOF.** The blueprint's PROOF field verbatim (`E₂ = e₂f₂u₂ > e₂f₂·e₂D′h = D₂e₂h` from
`T.hfloor`), with the strict-monotonicity step spelled as `Nat.mul_lt_mul_left hpos |>.mpr`,
left multiplication by `e₂f₂ > 0`.  The blueprint's cited `Nat.mul_lt_mul_left` is in Mathlib at
this pin an *iff*, so it is consumed through `.mpr`; same lemma, same direction.

SOURCE: `EFF.GENTOW1.07` (`E₂` + the SPLIT, verbatim, with the five-family audit);
`EFF.GENTOW1.08` (the weight and its lower-bound scope note, transcribed above).

**TEETH.** `EFF.GENTOW1.07`'s five-family audit — `E₂ = 10/14/6/21/6` against
`dv₂(x^{D₂}) = D₂e₂h = 8/8/4/18/4` — → **§13 regression rows** (two of the five are `q = 2`,
FAM-D is `q = 3`; GC-11's two-prime rule is served there, not here — this node's binders are an
abstract `TowerDatum` over an abstract `KeyFrame O π` and supply no numeral). The five
inequalities are numerals, though, so they are mirrored as bare `#guard`s at the bottom of this
file, together with the three families whose `(e₂, f₂, u₂)` the audit text displays (A5, B, C,
recovered in C.42's docstring table, all three with `D′h = 2` read back off the companion
`D₂e₂h` value) and with both term-family verifications on family B. Those rows check the
arithmetic of the audit; they are **not** statements about the abstract declarations above.

ENVIRONMENT: ENV-C5/C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- GENTOW1's **slot offset** `w(a,b) = a·e₂h + b·u₂`: the `dv₂`-cost of the composed slot
`x^a Φ′^b`.  Total in `a` and `b`; the grid ranges `a < D′`, `b < e₂f₂` are the consumers'
(C.52), not this definition's. -/
def slotOffset {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) (a b : ℕ) : ℕ :=
  a * (T.e₂ * F.h) + b * T.u₂

/-- GENTOW1's **weight** of a monomial datum `(v, a, b, j)`: `wt = e₁e₂·v + w(a,b) + j·E₂`.

Scope note (`EFF.GENTOW1.08`, transcribed): on the actual locus this is a **lower bound** for the
`dv₂` of the evaluated monomial, with the `j`-graded part strict — every downstream
"weight ≥ W" reads that way.  This definition asserts no relation to any valuation.
[A-C.1/D2: the blueprint's `def gridWeight … (v a b j : ℕ) : ℕ` ellipsis is completed by the
twin's binder list, the only one under which the signed body typechecks.] -/
def gridWeight {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) (v a b j : ℕ) : ℕ :=
  (F.e₁ * T.e₂) * v + slotOffset T a b + j * T.E₂

/-- **C.50, the SPLIT** (`EFF.GENTOW1.07`): `dv₂(x^{D₂}) = D₂·e₂h < E₂`.  At level 1 the key's
side height and `dv(x^{D′})` coincide; at level 2 they separate, and `E₂` is the true floor.

`T.hfloor` (C.42's `[r1]` node floor `u₂ > e₂D′h`) multiplied through by `e₂f₂ > 0`, the
positivity coming from `T.hcomp`.  Covers the degenerate `F.h = 0` frame without a case split:
there the claim is `0 < E₂` and `hfloor` reads `0 < u₂`. -/
theorem E₂_gt_xfloor {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) :
    T.D₂ * (T.e₂ * F.h) < T.E₂ := by
  have hpos : 0 < T.e₂ * T.f₂ := Nat.lt_of_lt_of_le Nat.zero_lt_two T.hcomp
  calc T.D₂ * (T.e₂ * F.h)
      = (T.e₂ * T.f₂) * (T.e₂ * (F.e₁ * F.f₁) * F.h) := by
        simp only [TowerDatum.D₂]; ring
    _ < (T.e₂ * T.f₂) * T.u₂ := (Nat.mul_lt_mul_left hpos).mpr T.hfloor
    _ = T.E₂ := by simp only [TowerDatum.E₂]

end Uniformity.Density.Tower

/-! ## `EFF.GENTOW1.07`'s five-family audit, as `#guard`s

Numeral mirrors of the audit rows — **not** statements about the abstract declarations above (an
abstract `TowerDatum` over an abstract `KeyFrame O π` supplies no numeral to `#guard`). The
first block is the SPLIT `E₂ > D₂e₂h` on all five families as the audit displays the two columns;
the second recomputes `E₂` and the node floor from the three families whose `(e₂, f₂, u₂)` the
audit text gives (C.42's docstring table, `D′h = 2` throughout); the third is the pair of
term-family verifications, unsigned here, on family B. -/

section FiveFamilyAudit

/-! The SPLIT column by column: `E₂ = 10/14/6/21/6` against `dv₂(x^{D₂}) = 8/8/4/18/4`. -/
#guard (8 : ℕ) < 10
#guard (8 : ℕ) < 14
#guard (4 : ℕ) < 6
#guard (18 : ℕ) < 21
#guard (4 : ℕ) < 6

/-! Family A5, `(e₂, f₂, u₂) = (2, 1, 5)`, `D′h = 2`: `E₂ = 10`, `D₂e₂h = 8`, floor `4 < 5`. -/
#guard (2 * 1 * 5 : ℕ) = 10
#guard (2 * 2 : ℕ) < 5

/-! Family B, `(e₂, f₂, u₂) = (1, 2, 3)`, `D′h = 2`: `E₂ = 6`, `D₂e₂h = 4`, floor `2 < 3`. -/
#guard (1 * 2 * 3 : ℕ) = 6
#guard (1 * 2 : ℕ) < 3

/-! Family C, `(e₂, f₂, u₂) = (3, 1, 7)`, `D′h = 2`: `E₂ = 21`, `D₂e₂h = 18`, floor `6 < 7`. -/
#guard (3 * 1 * 7 : ℕ) = 21
#guard (3 * 2 : ℕ) < 7

/-! The two term-family verifications on family B (`e₂ = 1`, `f₂ = 2`, `u₂ = 3`, `E₂ = 6`), both
unsigned at this node: the `Φ′^{e₂f₂}` term sits at `e₂f₂·u₂ = E₂`, and the `t`-th lift term at
`e₂u₂(f₂−t) + e₂t·u₂ = E₂` for every `t < f₂` — the same value, `t`-independent. -/
#guard (1 * 2 * 3 : ℕ) = 6
#guard (1 * 3 * (2 - 0) + 1 * 0 * 3 : ℕ) = 6
#guard (1 * 3 * (2 - 1) + 1 * 1 * 3 : ℕ) = 6

end FiveFamilyAudit

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.slotOffset
#print axioms Uniformity.Density.Tower.gridWeight
#print axioms Uniformity.Density.Tower.E₂_gt_xfloor

end AxCheck
