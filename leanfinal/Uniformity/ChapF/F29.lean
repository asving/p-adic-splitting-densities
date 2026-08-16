/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.GateFields
import Uniformity.ChapF.F07
import Uniformity.ChapF.F08
import Uniformity.ChapF.F09
import Uniformity.ChapF.F10a
import Uniformity.ChapF.F10b
import Uniformity.ChapF.F13
import Mathlib.Algebra.Field.ZMod

/-!
# Uniformity.ChapF.F29 — the twisted-algebra gate, EXECUTED at `q = 2` AND `q = 3`

**Chapter F, NODE F.29** [gate] [fresh] (`blueprint/CHAP-F_weld_layer.md` §10; GC-11's
both-primes + `e > 1 ∧ f > 1` discipline). ENV-F1. The node signs **no blueprint declaration** —
its contract IS the executed check list. What the file declares are gate carriers only: the
standard nontrivial 2-cocycle table on `ZMod 2` (`gateC`, `gateDelta`), its two instances
(`gateCocycleF4`, `gateCocycleF3`), and the odd-`E` carry shadow `gateDelta3`. The two
table-built fields `F4`/`F9` are §10's shared construction block
(`Uniformity.ChapF.GateFields`, landed separately, shared with F.30).

**The cocycle under test.** On the abscissa-coset group `ZMod 2`: `c 1 1 = ζ` and `c = 1`
elsewhere, with integer shadow `δ 1 1 = 1`, `δ = 0` elsewhere. It is nontrivial exactly when
`ζ ≠ 1`, so the gate runs it at `ζ = ω` of order 3 over `F₄` (`q = 2`) and at `ζ = 2 = −1` of
order 2 over `F₃` (`q = 3`). `e > 1 ∧ f > 1` witness: the `F₄` leg — `E = 2` (coset group,
e-side) with `F₄/F₂` (f = 2).

## The six checks (blueprint §10 NODE F.29)

1. **the `CarryCocycle` fields hold** — all 8 triples of the `Kˣ`-cocycle identity and all 8 of
   the integer identity, at both primes. These are not separate `example`s: they ARE the proof
   fields of the two instances below (`cocycle := by decide`, `δ_le_one := by decide`,
   `δ_cocycle := by decide` — 3 fields × 2 primes = 6 in-instance `decide`s), which is the
   sharpest form, since a failure makes the instance itself not exist;
2. **F.13's cardinality identity at instance level:** `Nat.card (TwistedAlgebra cc)` is 16 at
   `F₄` (`= 4²`) and 9 at `F₃` (`= 3²`);
3. **F.10(a)'s `Module.finrank K (TwistedAlgebra cc) = 2`** at both primes;
4. **F.10(b) at `E = 2`:** `(single 1 1)² = ζ • single 0 1` with the orbit product
   `∏_{k=1}^{1} c(1,k) = c(1,1) = ζ` — expected `ω` at `F₄`, `2` at `F₃`;
5. **the `E = 3` integer-carry instance:** the `{0,1}` table `δ a b = if 3 ≤ a.val + b.val then
   1 else 0` on `ZMod 3` satisfies the integer cocycle identity (27 triples) — the carry shadow
   at odd `E`;
6. **NEGATIVE control:** at `K = F₂` the unit group is trivial, so every gate cocycle collapses
   to `c ≡ 1` (F.06's regime) — a character check run at `q = 2` on `F₂` alone is vacuous, which
   is why the arena is `F₄`.

## ⚠ GATE-FORM RIDER (A-W.1/F-D5), in force here

Three displayed spellings do not kernel-reduce; §10's rider pre-authorises the substituted
forms, **and every expected VALUE of the blueprint display is reproduced** — what moved is the
spelling, not the arithmetic. A gate-form substitution is NOT a value mismatch.

* **(i), check 2:** `Nat.card` is not directly decidable, so the leg runs `show` through the
  carrier `ZMod E → K`, then `Nat.card_eq_fintype_card`, then `decide` on `Fintype.card`.
* **(i), check 3:** `Module.finrank` is noncomputable, so this leg is a `show`-through-the-
  carrier `simp`, never a `decide`.
* **(i) + F-D3, check 4:** the equality of algebra elements runs POINTWISE
  (`∀ t : ZMod 2, (…) t = (…) t`) so `decide` applies without `funext`. This is the leg that
  forces F.08's `One` to invert inside `Kˣ` (F-D3): `1 = single 0 ((c 0 0)⁻¹ : Kˣ)` reduces,
  while a `K`-side inverse would not.
* **(F-D6)** the `AdjoinRoot` field spellings carry no `DecidableEq`/`Fintype`, so no `decide`
  can fire on them at all; §10's pre-authorised table fallback is `GateFields`.

**`native_decide` appears nowhere** in this file (axiom census: Lean core only).

**DEPENDS.** F.07 (`CarryCocycle`), F.08 (`TwistedAlgebra`, `single`), F.09 (the algebra's
`Monoid` layer, so `^` means the twisted power), F.10(a) (`TwistedAlgebra.finrank_eq`), F.10(b)
(`TwistedAlgebra.pow_card_single`), F.13 (`TwistedAlgebra.nat_card`), and §10's `GateFields`.
`Mathlib.Algebra.Field.ZMod` is imported for the `Field (ZMod p)` instance the `F₃`/`F₂` legs
need.

**SOURCE.** GC-11; `EFF.GRTJC.89`'s JC7 battery shape (cocycle + carry + E-fold chain, "two
ways") — these are its smallest Lean-executable instances.

**TEETH.** Lean-executed gate; mirrored as `verification/chapF_gate_twisted.py` (§13).

**ENVIRONMENT.** ENV-F1 (concrete instances).

## Status

Sorry-free, `native_decide`-free. The five gate carriers print
`[propext, Classical.choice, Quot.sound]`; every other check is an anonymous `example` closed
by `decide`, `simp`, or an application of a landed F-node theorem (F.10(a)'s `finrank_eq`,
F.10(b)'s `pow_card_single`, F.13's `nat_card`), so nothing here can enter the trusted base.
Checks 2, 3 and 4 are each fired TWICE — once as the decided/simped value, once through the
landed theorem — so the computed numbers and the proved laws are checked against each other.
-/

namespace Uniformity.Density.Weld

section GateF29

/-! ## Gate-local carriers (NOT blueprint declarations)

The standard nontrivial 2-cocycle on `ZMod 2` and its integer shadow. -/

/-- The gate cocycle table (`c 1 1 = ζ`, else `1`). Gate-local. -/
def gateC {K : Type*} [Field K] (ζ : Kˣ) : ZMod 2 → ZMod 2 → Kˣ :=
  fun a b => if a = 1 ∧ b = 1 then ζ else 1

/-- The gate carry shadow (`δ 1 1 = 1`, else `0`). Gate-local. -/
def gateDelta : ZMod 2 → ZMod 2 → ℕ :=
  fun a b => if a = 1 ∧ b = 1 then 1 else 0

/-! ## CHECK 1 — the `CarryCocycle` fields, at both primes

All 8 triples of the `Kˣ`-cocycle identity and all 8 of the integer identity are the PROOF
FIELDS of the two instances: if a triple failed, the instance would not exist. -/

/-- `q = 2`: the gate cocycle at `(K, ζ) = (F₄, ω)`, `ω` of order 3 — a genuinely nontrivial
cocycle. This is the `e > 1 ∧ f > 1` witness (`E = 2`, `F₄/F₂`). -/
def gateCocycleF4 : CarryCocycle 2 F4 where
  c := gateC F4.omega
  δ := gateDelta
  cocycle := by decide
  δ_le_one := by decide
  δ_cocycle := by decide

/-- `q = 3`: the same table at `(K, ζ) = (F₃, 2 = −1)`. -/
def gateCocycleF3 : CarryCocycle 2 (ZMod 3) where
  c := gateC (-1)
  δ := gateDelta
  cocycle := by decide
  δ_le_one := by decide
  δ_cocycle := by decide

-- the cocycle is nontrivial at both primes (otherwise checks 2–4 would be testing the
-- untwisted group algebra and could not see a twist bug at all)
example : gateC F4.omega 1 1 ≠ 1 := by decide
example : gateC (-1 : (ZMod 3)ˣ) 1 1 ≠ 1 := by decide

/-! ## CHECK 2 — F.13's cardinality identity, `card K ^ E` = 16 resp. 9, form (i) -/

example : Fintype.card (ZMod 2 → F4) = 16 := by decide
example : Fintype.card (ZMod 2 → ZMod 3) = 9 := by decide

example : Nat.card (TwistedAlgebra gateCocycleF4) = 16 := by
  show Nat.card (ZMod 2 → F4) = 16
  rw [Nat.card_eq_fintype_card]; decide

example : Nat.card (TwistedAlgebra gateCocycleF3) = 9 := by
  show Nat.card (ZMod 2 → ZMod 3) = 9
  rw [Nat.card_eq_fintype_card]; decide

-- the same two numbers PREDICTED by F.13's theorem rather than counted
example : Nat.card (TwistedAlgebra gateCocycleF4) = Nat.card F4 ^ 2 :=
  TwistedAlgebra.nat_card gateCocycleF4
example : Nat.card (TwistedAlgebra gateCocycleF3) = Nat.card (ZMod 3) ^ 2 :=
  TwistedAlgebra.nat_card gateCocycleF3
example : Nat.card F4 ^ 2 = 16 := by
  rw [Nat.card_eq_fintype_card]; decide
example : Nat.card (ZMod 3) ^ 2 = 9 := by
  rw [Nat.card_eq_fintype_card]; decide

/-! ## CHECK 3 — F.10(a)'s `finrank = E = 2` at both primes, form (i) (`simp`, not `decide`) -/

example : Module.finrank F4 (TwistedAlgebra gateCocycleF4) = 2 := by
  show Module.finrank F4 (ZMod 2 → F4) = 2
  simp

example : Module.finrank (ZMod 3) (TwistedAlgebra gateCocycleF3) = 2 := by
  show Module.finrank (ZMod 3) (ZMod 2 → ZMod 3) = 2
  simp

-- the same value through F.10(a)'s theorem (the carrier route and the proved law agree)
example : Module.finrank F4 (TwistedAlgebra gateCocycleF4) = 2 :=
  TwistedAlgebra.finrank_eq gateCocycleF4
example : Module.finrank (ZMod 3) (TwistedAlgebra gateCocycleF3) = 2 :=
  TwistedAlgebra.finrank_eq gateCocycleF3

/-! ## CHECK 4 — F.10(b) at `E = 2`: `(single 1 1)² = ζ • single 0 1`, pointwise, form (i)

The orbit product is `∏_{k=1}^{1} c(1,k) = c(1,1) = ζ`: expected `ω` at `F₄` and `2` at `F₃`. -/

example : ∀ t : ZMod 2,
    ((single 1 1 : TwistedAlgebra gateCocycleF4) ^ 2) t
      = (((F4.omega : F4) • (single 0 1 : TwistedAlgebra gateCocycleF4)) t) := by decide

example : ∀ t : ZMod 2,
    ((single 1 1 : TwistedAlgebra gateCocycleF3) ^ 2) t
      = ((((2 : ZMod 3)) • (single 0 1 : TwistedAlgebra gateCocycleF3)) t) := by decide

-- the same identity through F.10(b)'s theorem, with the orbit product left symbolic …
example : (single 1 1 : TwistedAlgebra gateCocycleF4) ^ 2
    = (∏ k ∈ Finset.Ico (1 : ℕ) 2, (gateCocycleF4.c 1 ((k : ℕ) : ZMod 2) : F4)) • single 0 1 :=
  TwistedAlgebra.pow_card_single gateCocycleF4
example : (single 1 1 : TwistedAlgebra gateCocycleF3) ^ 2
    = (∏ k ∈ Finset.Ico (1 : ℕ) 2, (gateCocycleF3.c 1 ((k : ℕ) : ZMod 2) : ZMod 3)) • single 0 1 :=
  TwistedAlgebra.pow_card_single gateCocycleF3
-- … and the orbit product's VALUE, decided: `ω` at `F₄`, `2` at `F₃`
example : (∏ k ∈ Finset.Ico (1 : ℕ) 2, (gateCocycleF4.c 1 ((k : ℕ) : ZMod 2) : F4))
    = (F4.omega : F4) := by decide
example : (∏ k ∈ Finset.Ico (1 : ℕ) 2, (gateCocycleF3.c 1 ((k : ℕ) : ZMod 2) : ZMod 3))
    = (2 : ZMod 3) := by decide

/-! ## CHECK 5 — the `E = 3` integer-carry instance (27 triples) -/

/-- The odd-`E` carry shadow: `δ a b = 1` exactly when `a.val + b.val` wraps. Gate-local. -/
def gateDelta3 : ZMod 3 → ZMod 3 → ℕ :=
  fun a b => if 3 ≤ a.val + b.val then 1 else 0

example : ∀ a b : ZMod 3, gateDelta3 a b ≤ 1 := by decide
example : ∀ a b d : ZMod 3,
    gateDelta3 a b + gateDelta3 (a + b) d = gateDelta3 b d + gateDelta3 a (b + d) := by decide
-- it really does wrap somewhere (a shadow that is identically 0 would pass check 5 vacuously)
example : gateDelta3 2 2 = 1 := by decide

/-! ## CHECK 6 — NEGATIVE control at `K = F₂`: the unit group is trivial

F.06's regime, made concrete: over `F₂` every gate cocycle collapses to `c ≡ 1`, so a
character check run at `q = 2` on `F₂` alone is vacuous — the reason the arena is `F₄`. -/

example : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
example : ∀ a b : ZMod 2, gateC (1 : (ZMod 2)ˣ) a b = 1 := by decide

end GateF29

end Uniformity.Density.Weld
