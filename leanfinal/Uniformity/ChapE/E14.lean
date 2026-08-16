/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E12

/-!
# Uniformity.ChapE.E14 — `(DEG-SUM)`: the separable side's forced class sizes fill its root count

**Chapter E, NODE E.14** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §4), ENV-E2 (the carrier
arena: a slot carrier `C : SlotCarrier O K` from E.10, a block `B : BlockData C` from E.11 and a
rung interface `I : RungInterface C B` from E.12).

`EFF.T2.12`'s `(RES-DEG)` says of every side `λ` of the block's polygon that
`e′ · Σ_{r′} m_{λ,r′} · deg r′ = L_λ`: the side length is the slope denominator times the
multiplicity-weighted degree of the residual polynomial's factorization. `EFF.T2.29` specializes
it to the **separable** case — every residual multiplicity `= 1` — where it becomes `(DEG-SUM)`,
`e′ Σ_{r′} deg r′ = L_λ`. This node lands that specialization in the form the counting argument
actually consumes:

> at a separable side, the **forced** class sizes sum EXACTLY to the side's root count:
> `Σ_{linear} D·e′ + Σ_{higher} D·e′·deg r′ = rootCount λ`.

The two summands are the lower bounds `hforce` imposes on each residual factor's class
(E.12: `D·p.2 ≤ classCount`, `D·p.2·q.1 ≤ classCountHi`). Their total meeting `rootCount` on the
nose is what makes E.15's multiset sandwich bite: `hexhaust` says the ACTUAL class sizes sum to
`rootCount`, this node says the FORCED lower bounds already do, and termwise equality follows.
So E.14 supplies the "`Σ lower = Σ count`" half of that sandwich and nothing else — it asserts
no equality of individual classes, which is E.15/E.16's conclusion, not this node's hypothesis.

## What `SepSide` is, and what it is not

`RungInterface.SepSide I p` is the **numerical shadow** of separability: every pair in `linFac p`
and in `hiFac p` carries multiplicity `1`. It is a statement about E.12's residual bookkeeping
multisets, NOT about a polynomial being squarefree. The corpus's separability lives one layer
down (the residual polynomial `R_λ` is separable over the stage field); D-E2 records that E's
carrier keeps only the numerical shadow of it, and any instance discharging `RungInterface`
must derive `SepSide` from real separability at that point. Read `SepSide` as a hypothesis
SHAPE, not as a proof that any side is separable.

## Where the hypotheses are spent (nothing is decorative)

* `hsep` — twice, and only to erase multiplicities: on `linFac` it turns the constant summand
  `D·e′` into `D·e′·q.2`, on `hiFac` it turns `D·e′·q.1` into `D·e′·(q.1·q.2)`. Those are exactly
  the two shapes `hresdeg` sums over. The gate below shows the hypothesis is load-bearing: with a
  single residual factor of multiplicity `m`, the multiplicity-blind total matches the root count
  **iff** `m = 1`.
* `hp : p ∈ I.sides` — to invoke `hresdeg` and `haccount`, both of which are quantified over
  sides. Off the side set the interface says nothing and the identity is not claimed.
* `hresdeg` — `(RES-DEG)` itself, and `haccount` — `(SIDE-COUNT)`, `rootCount λ = D · len λ`.

## Conditionality (read before citing this as unconditional)

This is a theorem ABOUT a `RungInterface C B`; it does not assert that one exists. `RungInterface`
carries `EFF.T2.39`'s five hypothesis families as FIELDS (source obligations, not conclusions),
so every consumer inherits the instance obligation of E.22/E.23. Nothing here derives `(RES-DEG)`
or `(ACCOUNT)`; the node's content is precisely that those two, plus multiplicity-freeness, force
the forced-size total.

DEPENDS: E.12 (`RungInterface`, its `linFac`/`hiFac`/`len`/`rootCount` and the fields `hresdeg`,
`haccount`) · mathlib `Multiset.sum_map_mul_left`, `Multiset.map_congr`.

SOURCE: `EFF.T2.29` (`(DEG-SUM)`: "For separable `R_λ`, `(RES-DEG)` specializes to `(DEG-SUM)`");
`EFF.T2.12` (`(RES-DEG)`); `EFF.HE7.13`'s proof (`Σ_{r₂}|S_{λ₂,r₂}| = n_{λ₂} = D″L_{λ₂} =
Σ_{r₂}D″ℓ₂ deg r₂` — this identity one level down).

TEETH: S7 Pass 2 missing-`(RES-DEG)` refusal → **Lean theorem** (a consumer that drops `hresdeg`
cannot elaborate: the field is what the proof rewrites with).

ENVIRONMENT: ENV-E2.

## Status

Sorry-free. Both declarations report at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}` — these arrive through mathlib's `Multiset` quotient
API, not through any project axiom. Types checked against the signed SIGNATURE declaration by
declaration (binder names, order and explicitness unchanged).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.14** [def] A side `p = (u_λ, ℓ_λ)` is **separable in the numerical shadow** when every
residual factor recorded at it — linear (`linFac`) or of degree `≥ 2` (`hiFac`) — carries
multiplicity `1`. The shadow of `EFF.T2.29`'s "separable `R_λ`"; the polynomial statement lives
one layer down (D-E2). -/
def RungInterface.SepSide {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B) (p : ℕ × ℕ) : Prop :=
  (∀ q ∈ I.linFac p, q.2 = 1) ∧ (∀ q ∈ I.hiFac p, q.2 = 1)

/-- **E.14** [lemma] `(DEG-SUM)` in consumed form: at a separable side the FORCED class sizes
(`D·e′` per linear residual factor, `D·e′·deg r′` per higher one — `hforce`'s lower bounds) sum
exactly to the side's root count `D·L_λ`. This is the "`Σ lower = Σ count`" half of E.15's
sandwich; it claims nothing about any individual class. -/
theorem RungInterface.forced_sum_eq {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    {p : ℕ × ℕ} (hp : p ∈ I.sides) (hsep : I.SepSide p) :
    ((I.linFac p).map fun _ => C.D * p.2).sum
      + ((I.hiFac p).map fun q => C.D * p.2 * q.1).sum = I.rootCount p := by
  obtain ⟨hlin, hhi⟩ := hsep
  -- the linear part: `D·e′ = D·e′·q.2` because `q.2 = 1`, so the sum is `D·e′ · Σ q.2`
  have h1 : ((I.linFac p).map fun _ => C.D * p.2).sum
      = C.D * p.2 * ((I.linFac p).map Prod.snd).sum := by
    rw [← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro q hq
    rw [hlin q hq, mul_one]
  -- the higher part: `D·e′·q.1 = D·e′·(q.1·q.2)` for the same reason
  have h2 : ((I.hiFac p).map fun q => C.D * p.2 * q.1).sum
      = C.D * p.2 * ((I.hiFac p).map fun q => q.1 * q.2).sum := by
    rw [← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro q hq
    rw [hhi q hq, mul_one]
  -- collect, then read `(RES-DEG)` and `(SIDE-COUNT)` off the interface
  rw [h1, h2, ← Nat.mul_add, mul_assoc, I.hresdeg p hp, I.haccount p hp]

/-! ## Gate (executed `example`s, not blueprint declarations)

An identity between two sums is easy to state and easy to state VACUOUSLY, and `hsep` is easy to
mistake for a technical convenience. Both are checked here in the arithmetic shadow — the same
device E.12's gate uses, since a full `SlotCarrier`/`BlockData` instance is E.22/E.23's
obligation and is deliberately not attempted below §4. -/

section Gate

-- (a) a separable side with one linear and one degree-2 residual factor, `D = 2`, `e′ = 3`:
-- `(RES-DEG)` gives `len = 3·(1 + 2) = 9`, `(SIDE-COUNT)` gives `rootCount = 2·9 = 18`, and the
-- forced total is `D·e′ + D·e′·2 = 6 + 12 = 18`. The identity is not vacuous.
example : 2 * 3 + 2 * 3 * 2 = 2 * (3 * (1 + 2 * 1)) := by decide

-- (b) `hsep` is load-bearing, sharply: with ONE linear residual factor of multiplicity `m`,
-- `(RES-DEG)` reads `len = e′·m` and the root count is `D·e′·m`, while the multiplicity-blind
-- forced total of this node is `D·e′`. They agree exactly when `m = 1` — so dropping `hsep`
-- does not merely lose the proof, it makes the conclusion false at every `m ≥ 2`.
example (D e' m : ℕ) (hD : 0 < D) (he : 0 < e') (h : D * e' = D * (e' * m)) : m = 1 := by
  have h1 : e' = e' * m := Nat.eq_of_mul_eq_mul_left hD h
  have h2 : e' * 1 = e' * m := by rwa [mul_one]
  exact (Nat.eq_of_mul_eq_mul_left he h2).symm

-- (b′) the failure instance itself, at `D = 2`, `e′ = 3`, `m = 2`.
example : 2 * 3 ≠ 2 * (3 * 2) := by decide

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.RungInterface.SepSide
#print axioms Uniformity.Density.Ladder.RungInterface.forced_sum_eq

end AxCheck
