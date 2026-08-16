/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C15

/-!
# Uniformity.ChapC.C17 — `slotWindow`: the slot window `T(k)`

**Chapter C, NODE C.17** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge layer;
the A-C.1 amendment set governs). **ENV-C1** *[A-C.1 re-tag per defect **D7**: ENV-C5 → ENV-C1,
stated over `KeyFrame`, which binds the DVR telescope; see C.15's rider]*. One signed
declaration, definitional, COMPUTABLE.

* `KeyFrame.slotWindow F k` — `EFF.HE6.13`'s
  `T(k) = {t < f₁ : k ≥ (i₀(k) + e₁t)·h}`, the set of **slots available at height `k`**: the
  `t`-th slot of the `f₁`-element power basis costs `(i(k) + e₁t)·h` in `dv`, and it is in the
  window exactly when the budget `k` covers that cost. The slot index `i(k)` is C.15's
  `slotIdx`, whose defining congruence is C.16's, not C.15's body.

## What the definition does and does not promise

Everything: it is a `Finset.filter` on `Finset.range F.f₁` with a decidable arithmetic
predicate, so `t ∈ slotWindow F k ↔ t < F.f₁ ∧ (slotIdx F k + F.e₁ * t) * F.h ≤ k` is
`Finset.mem_filter` and needs no lemma. What is deliberately NOT here is the threshold layer —
fullness (`slotWindow F k = range F.f₁` iff the top slot is affordable), the uniform sufficiency
bound `(e₁f₁ − 1)h ≤ k`, and downward closure in `t` — all of which are **C.18**, and all of
which need C.16's `slotIdx F k < F.e₁`. Consumers wanting a *full* window must cite C.18.

One inherited caveat, worth naming because the object looks self-contained: `slotWindow` is
built on C.15's `slotIdx`, whose body is a total, junk-`0`-defaulting search (defect **D6**'s
cure). At an arbitrary `(e₁, h, k)` with `h` and `e₁` not coprime the junk value would make the
window's threshold meaningless — but at a `KeyFrame` this cannot happen: `F.hcop` is a structure
field and C.16 discharges the search. So the window is honest here for the same reason C.15's
`slotIdx` is, and for no other reason; the frame hypothesis is doing the work.

## Divergence from the blueprint SIGNATURE (twin authoritative)

The blueprint signs `noncomputable def KeyFrame.slotWindow`. The gate-verified twin
`leanspec/Leanspec/ChapC.lean` signs a plain `def`, and the twin is authoritative on divergence.
The twin is also right on the merits: the `noncomputable` is inherited from the blueprint's
original `Nat.find`-based `slotIdx` body, which defect **D6** replaced with the computable
`List.find?` search that C.15 landed, and the filter's predicate
`(F.slotIdx k + F.e₁ * t) * F.h ≤ k` is `Nat.decLe`-decidable. Dropping the modifier is a
strictly weaker claim about the declaration, not a statement change: the type and the body are
byte-identical to the signed ones. (This is the same D6/D7 correction C.15 already carries.)

**DEPENDS.** C.15 (`slotIdx`) · C.01 (`KeyFrame.f₁`, `KeyFrame.e₁`, `KeyFrame.h`) — by committed
node ID (GC-13(b)). The single import is `Uniformity.ChapC.C15`, which pulls C.01 and the whole
B chain. C.16 is deliberately NOT imported: nothing here consumes a `slotIdx` property, and the
first node that does is C.18.

**PROOF.** Definitional. The body is the gate-verified twin's verbatim.

SOURCE: `EFF.HE6.13` (the `T(k)` display, verbatim: `T(k) = {t : 0 ≤ t < f₁, k ≥ (i₀ + e₁t)h}`).

**TEETH.** The `.12` audit's two window rows → **executable regression at §13** (C.123/C.124's
numeric mirrors); not dischargeable at this node's binders, since an abstract `KeyFrame O π`
offers no numeral to `#guard` (the D7 consequence recorded at C.15). For the record, both rows
are reproduced by the body that lands here:
* `(e₁, f₁, h) = (3, 1, 2)`, `k = 1`: `slotIdx 1 = 2` (as `2·2 % 3 = 1`), the only candidate
  `t = 0` costs `(2 + 0)·2 = 4 > 1`, so `T(1) = ∅` — the audit's empty window.
* `(e₁, f₁, h) = (1, 2, 1)`, `k = 0`: `slotIdx 0 = 0`, `t = 0` costs `0 ≤ 0` and `t = 1` costs
  `1 > 0`, so `T(0) = {0} ⊊ range 2` — the audit's proper window.

ENVIRONMENT: ENV-C1 (post-D7).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `T(k) := {t < f₁ : k ≥ (i₀(k) + e₁t)h}` (`EFF.HE6.13`) — the slots affordable at height `k`.
[A-C.1/D6+D7: the blueprint's `noncomputable` is inherited from the withdrawn `Nat.find` body of
C.15's `slotIdx`; the predicate is `Nat.decLe`-decidable and the twin signs a plain `def`.]
The threshold laws (fullness, uniform sufficiency, downward closure) are C.18, not this node. -/
def KeyFrame.slotWindow (F : KeyFrame O π) (k : ℕ) : Finset ℕ :=
  (Finset.range F.f₁).filter (fun t => (F.slotIdx k + F.e₁ * t) * F.h ≤ k)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotWindow

end AxCheck
