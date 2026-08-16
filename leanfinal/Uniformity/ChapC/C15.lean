/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C01

/-!
# Uniformity.ChapC.C15 — `slotIdx`, `twistExp`: the normalizer exponents

**Chapter C, NODE C.15** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge layer;
the A-C.1 amendment set governs). **ENV-C1** *[A-C.1 re-tag per defect **D7**: ENV-C5 → ENV-C1,
stated over `KeyFrame`, which binds the DVR telescope; the pure-arithmetic content is carried by
the numeric-gate mirrors (`slotIdxN` etc.) at §13]*. Two signed declarations, both definitional,
both COMPUTABLE. **This is a TERMINAL SUPPLY node** (the normalizer/twist layer C.15/C.18/C.21/
C.24 is what CHAP-B H-1's out-of-scope consumers and chapter E's `.13`/`.14` pin anchors read).

* `KeyFrame.slotIdx F k` — the **slot index** `i(k)`: the unique `0 ≤ i < e₁` with
  `i·h ≡ k (mod e₁)`. Existence and uniqueness are `F.hcop : Nat.Coprime F.h F.e₁` (C.01)
  through H.51's mod-`e₁` bijection `i ↦ ih`; the SPEC is C.16's `slotIdx_spec` /
  `slotIdx_unique`, not this body.
* `KeyFrame.twistExp F k` — the **twist exponent** `q(k)` of `EFF.HE6.13`-RIDER, defined by
  `i₀·k = i(k) + q(k)·e₁` with `i₀ = slotIdx F 1` (ϖ's `x`-exponent: `i₀h + e₁a₀ = 1` forces
  `i₀h ≡ 1 (mod e₁)`). Its defining identity is C.16's `twistExp_spec`.

## The D6 cure, and what the body does and does not promise

The blueprint's original SIGNATURE read
`noncomputable def KeyFrame.slotIdx F k := Nat.find (F.slotIdx_exists k)`. **`slotIdx_exists` is
declared in no node of the chapter** — this is stub-gate defect **D6**, and the signature was
therefore UNDECLARABLE as written (`Nat.find` additionally needs the decidable predicate, which
the missing lemma was to have supplied). A-C.1(m) adopts the gate's cure: the total, COMPUTABLE,
junk-`0`-defaulting body below, with `noncomputable` dropped. It is transcribed verbatim from
the gate-verified twin `leanspec/Leanspec/ChapC.lean`.

What the body promises: `slotIdx F k` is the FIRST `i` in `[0, e₁)` with `i·h ≡ k (mod e₁)`, and
`0` if there is none. What it does not promise, at this node: that such an `i` exists. It always
does — `F.hcop` makes `i ↦ ih mod e₁` a bijection of `range e₁` — but that argument is C.16's,
and until C.16 lands, `slotIdx`'s value carries no proved property. Consumers must cite C.16,
never the body. (The blueprint's own PROOF field says as much: *"the `Nat.find` packaging may
become `(h⁻¹·k) % e₁` … the SPEC is the defining congruence + range, C.16, not the
implementation"* — so the body is explicitly a non-contract.)

The junk value `0` is the honest reading and not a hidden falsehood: at the degenerate frame
`e₁ = 1` (where `List.range 1 = [0]` and every congruence holds mod 1) the intended value IS
`0`, so the default agrees with the intent on the one instance where the search could look
degenerate. `twistExp` inherits the same discipline: it is `ℕ`-truncated subtraction and
`ℕ`-division, both junk-valued off the intended range, and C.16(iii) is what pins
`i₀k = i(k) + q(k)·e₁` exactly.

## The `a₀ < 0` phenomenon is designed out (C-H14)

`EFF.HE6.11` presents ϖ's exponents as the Bézout pair `(i₀, a₀)` with `i₀h + e₁a₀ = 1`, and
`a₀` is genuinely negative in the corpus's own witness audit (`(e₁, h) = (2, 3) ⟹ i₀ = 1,
a₀ = −1`). **No `a₀` is ever computed in this chapter.** Every exponent that reaches Lean is a
`ℕ`, obtained from `i₀ = slotIdx F 1` and the division `q(k) = (i₀k − i(k))/e₁`, so the
`WithTop ℤ` fallback flagged at C-H14 is never reached. That witness audit is this node's
TEETH and it executes as a `slotIdx`-table regression at §13's gate frames (C.123/C.124), NOT
here: over an abstract `KeyFrame` there is no numeral to `#guard`, which is precisely why the
D7 re-tag routes the arithmetic content to the §13 numeric mirrors.

**DEPENDS.** C.01 (`KeyFrame`) · H.51 (`class_sep_bij` — the mod-`e₁` bijection `i ↦ ih`; a
DEPENDS of the SPEC at C.16, not of this body) — by committed node ID (GC-13(b)). The single
import is `Uniformity.ChapC.C01`.

**PROOF.** Definitional.

SOURCE: `EFF.HE6.11` (ϖ's exponents: `i₀h + e₁a₀ = 1`, `0 ≤ i₀ < e₁`); `EFF.HE6.13` (RIDER:
`i₀k = i + qe₁`, `a₀k − a = −qh`); `EFF.HE6.58` (`i(k)` as re-displayed).

**TEETH.** `EFF.HE6.11`'s witness audit → executable regression at §13 (see above); not
dischargeable at this node's binders.

ENVIRONMENT: ENV-C1 (post-D7).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `i(k)`: the unique `0 ≤ i < e₁` with `ih ≡ k (mod e₁)` (`EFF.HE6.58`'s `i(k)`;
`EFF.HE6.13`'s `i₀(k)`). Total: at the degenerate `e₁ = 1` it is `0`.
[A-C.1/D6: the `Nat.find (F.slotIdx_exists k)` body was UNDECLARABLE (`slotIdx_exists`
exists in no node, and `Nat.find` needs the predicate); the gate's total, COMPUTABLE,
junk-`0`-defaulting body is adopted — it agrees with the intended value exactly when it
exists, which `F.hcop` guarantees (C.16's spec pins it).] -/
def KeyFrame.slotIdx (F : KeyFrame O π) (k : ℕ) : ℕ :=
  ((List.range F.e₁).find? (fun i => (i * F.h) % F.e₁ == k % F.e₁)).getD 0

/-- `q(k)`: the ϖ-vs-`n(k)` twist exponent, `i₀·k = i(k) + q(k)·e₁` (`EFF.HE6.13` RIDER). -/
def KeyFrame.twistExp (F : KeyFrame O π) (k : ℕ) : ℕ :=
  (F.slotIdx 1 * k - F.slotIdx k) / F.e₁

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx
#print axioms Uniformity.Density.Tower.KeyFrame.twistExp

end AxCheck
