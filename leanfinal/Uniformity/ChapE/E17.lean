/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E07

/-!
# Uniformity.ChapE.E17 — the continuation trichotomy (`ContCase`, the WIDENED four-case split)

**Chapter E, NODE E.17** (`blueprint/CHAP-E_sigma_ladder.md` §4, THEOREM HE7.A clauses (3)–(4)).
The read's per-block continuation decision, on the *numerical shadow* of the block: the side
denominator `ℓ`, the residual-factor degree `d`, and the `(LABEL-OWN)` block multiplicity
`k = deg F_{λ,r′} / (D·ℓ·d)`.

* `ContCase` — the three continuation cases: `terminal`, `refine`, `child`.
* `contCaseOf ℓ d k` — the decision function: `terminal` at `k = 1`, else `refine` at
  `ℓ * d = 1`, else `child`.
* `contCase_complete` — the classification is exhaustive and each branch carries its
  numerical certificate (`k = 1` / `2 ≤ k ∧ ℓ*d = 1` / `2 ≤ k ∧ 2 ≤ ℓ*d`). Since
  `contCaseOf` is a function, "exactly one holds" is the disjunction plus functionality;
  the three case tags are pairwise distinct by `ContCase`'s `DecidableEq`, so the signed
  disjunction IS the trichotomy.
* `child_mass` — `(MASS)` at a child: `μ_child * (ℓ*d) ≤ μ` with `2 ≤ ℓ*d` gives
  `2 * μ_child ≤ μ`. This is E.07(ii) (`jump_halving`) at `p := ℓ * d`, re-exported under the
  clause's own name because the consumer (E.19's `rank_decreases_of_mass_lt`, E.20's engine)
  cites the child jump, not the abstract halving.

## The split is on the PRODUCT, not on `ℓ` alone

`EFF.HE7.14`'s `[r1]` rider: *"split on the product `ℓ₂·deg r₂` (NOT on `ℓ₂` alone)"*. The
pre-`r1` split (`refine` iff `ℓ = 1`) is REFUTED — FINDING HE6R1-F1, *"β₂ ∈ K₂(β₂)∖K₂ is not a
value of (LIFT₂)"*: at `ℓ = 1, d ≥ 2` the recentering has nothing to recenter *by* inside the
current field, and the continuation must open a child carrier. The `NumericGate` section below
exhibits the disagreement as an executed check at `(ℓ, d, k) = (1, 2, 2)`, so the widening is
machine-visible and not a comment.

## What this node does NOT say (the two corpus fences, both signature-visible)

1. **The parent-multiplicity NON-IMPORT** (`EFF.T2.17`, S1.7A): *"No equality between
   `k_{λ,r′}` and `m_{λ,r′}` from the parent residual factorization is assumed"* — the
   multiplicities living in `RungInterface`'s `linFac`/`hiFac` are absent from every signature
   here. `k` enters as a bare `ℕ` argument; nothing relates it to a parent datum.
2. **STATEMENT clause (iii)** — the `(LABEL-OWN)` integrality `k * (D * ℓ * d) = deg F_{λ,r′}`
   with `k ≥ 1` — has **no conjunct in the SIGNATURE** and none is added (the same convention
   E.18's SIGNATURE NOTE records for its clause (iii)). It is the *definition* of the block
   multiplicity datum, i.e. the way a consumer manufactures the `k` it passes in, not a
   consequence this node proves. Recorded so the missing conjunct does not read as a
   transcription loss.

## `(LB1)` SCOPE (blueprint's ⚠, transcribed)

Constructing the label BLOCKS at a level-one multi-side/mixed state is `(LB1)` (E.39, OPEN);
this node classifies *given* the block data. Consumers at level one must thread E.39's
hypothesis; at level ≥ 2 the blocks come from ANNEX-LEMMA HE7-13′(a) = E.57. The corpus's own
scoping (`EFF.T2.18`): *"Clauses 1 and 2 are not [conditional]; … the clause-4 route [is], on
`(LB1)`."* Nothing in this file is conditional — the conditionality is the *supplier's*.

DEPENDS: E.01 (the rung vocabulary — `ℓ`, `d`; no `RungDatum` argument is signed, the node is
pure `ℕ`-arithmetic), E.07 (`jump_halving`) · mathlib `Nat.mul_eq_one` (used through `omega`
after the `ℓ*d` case split).

SOURCE: `EFF.T2.31` clauses 3–4 (*"the continuation is decided by the product `e′deg r′`.
Product 1 gives the certified linear recentering; product at least 2 gives the certified child
carrier and the mass bound `(MASS)`"*); `EFF.T2.17` (S1.7A, `k_{λ,r′} = ν/(e′deg r′) ∈ ℤ_{≥1}`
and the parent-multiplicity NON-IMPORT); `EFF.T2.21` (`(MASS)`: `μ_child ≤ μ/(e′deg r′) ≤ μ/2`);
`EFF.T2.22` (the processing order); `EFF.HE7.14` (the widened trichotomy and the refutation of
the pre-`r1` branch).

TEETH: S7 Pass 2's mixed-residual/two-repeated-classes tooth; `he7r2_supp.py` B1–B5 (the refine
branch, 42/42); `he7_pe3_probe12.py` (144/144 at the first mixed node) → the *classification*
becomes a Lean theorem here; the *block construction* stays a carried hypothesis at level 1.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free. Footprint Lean-core only: `ContCase`, `contCaseOf` and `child_mass` depend on no
axioms at all; `contCase_complete` reports `[propext, Quot.sound]` (the `simp`/`omega` route
through the `if`-branches). No chapter axiom, in particular not B.42.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.17** [def] The three continuation cases of HE7.A(3)–(4), on the numerical shadow of a
label block: `terminal` (the block is finished), `refine` (a linear recentering inside the
current carrier), `child` (a new carrier one level up). -/
inductive ContCase | terminal | refine | child
  deriving DecidableEq

/-- **E.17** [def] The continuation case of a factor with side denominator `ℓ`, residual-factor
degree `d` and block multiplicity `k`. The second test is on the **product** `ℓ * d`
(`EFF.HE7.14` `[r1]`), never on `ℓ` alone. -/
def contCaseOf (ℓ d k : ℕ) : ContCase :=
  if k = 1 then .terminal else if ℓ * d = 1 then .refine else .child

/-- **E.17(i)** The continuation trichotomy is complete: at legal block data
(`1 ≤ ℓ`, `1 ≤ d`, `1 ≤ k`) the decision lands in one of the three cases together with that
case's numerical certificate. -/
theorem contCase_complete (ℓ d k : ℕ) (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (contCaseOf ℓ d k = .terminal ∧ k = 1) ∨
    (contCaseOf ℓ d k = .refine ∧ 2 ≤ k ∧ ℓ * d = 1) ∨
    (contCaseOf ℓ d k = .child ∧ 2 ≤ k ∧ 2 ≤ ℓ * d) := by
  unfold contCaseOf
  -- `1 ≤ ℓ` and `1 ≤ d` give `1 ≤ ℓ * d`, so the `ℓ * d ≠ 1` branch really is `2 ≤ ℓ * d`.
  have hprod : 1 ≤ ℓ * d := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.1 hℓ) (Nat.one_le_iff_ne_zero.1 hd))
  by_cases hk1 : k = 1
  · exact Or.inl ⟨by simp [hk1], hk1⟩
  · by_cases hℓd : ℓ * d = 1
    · exact Or.inr (Or.inl ⟨by simp [hk1, hℓd], by omega, hℓd⟩)
    · exact Or.inr (Or.inr ⟨by simp [hk1, hℓd], by omega, by omega⟩)

/-- **E.17(ii)** `(MASS)` at a child: a child jump with product `ℓ * d ≥ 2` at least halves the
mass. E.07(ii) (`jump_halving`) at `p := ℓ * d`, under the clause's own name. -/
theorem child_mass {μ μc ℓ d : ℕ} (h2 : 2 ≤ ℓ * d) (h : μc * (ℓ * d) ≤ μ) :
    2 * μc ≤ μ :=
  jump_halving h2 h

end Uniformity.Density.Ladder

/-! ## Numeric gate

The classification is decidable, so the trichotomy is re-fired as an executed sweep, and the
`[r1]` widening is exhibited as a *disagreement* with the refuted pre-`r1` split. -/

section NumericGate

open Uniformity.Density.Ladder

/-- The certificate attached to each branch of `contCase_complete`, as a `Bool`. -/
private def contCaseCert (l d k : ℕ) : Bool :=
  match contCaseOf l d k with
  | .terminal => k == 1
  | .refine => decide (2 ≤ k) && (l * d == 1)
  | .child => decide (2 ≤ k) && decide (2 ≤ l * d)

-- The trichotomy, executed over all legal `(ℓ, d, k)` with each entry in `1..8`.
#guard (List.range 8).all fun i => (List.range 8).all fun j => (List.range 8).all fun m =>
  contCaseCert (i + 1) (j + 1) (m + 1)

-- All three cases actually occur inside the swept range (the theorem is not vacuously about
-- one branch).
#guard contCaseOf 2 1 1 == ContCase.terminal
#guard contCaseOf 1 1 3 == ContCase.refine
#guard contCaseOf 2 1 3 == ContCase.child

/-- The REFUTED pre-`r1` split: `refine` decided by `ℓ = 1` alone. -/
private def preR1CaseOf (l _d k : ℕ) : ContCase :=
  if k = 1 then .terminal else if l = 1 then .refine else .child

-- The two splits DISAGREE at `(ℓ, d, k) = (1, 2, 2)`: the widened rule opens a child carrier
-- (`ℓ*d = 2 ≥ 2`), the refuted rule would recenter. FINDING HE6R1-F1's shape, machine-visible.
#guard contCaseOf 1 2 2 == ContCase.child
#guard preR1CaseOf 1 2 2 == ContCase.refine

-- …and they agree wherever `d = 1`, which is why the pre-`r1` reading survived as long as it
-- did (every `d = 1` block is classified identically by both rules).
#guard (List.range 8).all fun i => (List.range 8).all fun m =>
  contCaseOf (i + 1) 1 (m + 1) == preR1CaseOf (i + 1) 1 (m + 1)

-- `(MASS)`: the halving really needs `2 ≤ ℓ*d`. At `ℓ*d = 1` the child bound fails —
-- `μc = μ = 3` satisfies `μc * 1 ≤ μ` but not `2*μc ≤ μ`.
#guard decide (3 * (1 * 1) ≤ 3) && !decide (2 * 3 ≤ 3)

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.ContCase
#print axioms Uniformity.Density.Ladder.contCaseOf
#print axioms Uniformity.Density.Ladder.contCase_complete
#print axioms Uniformity.Density.Ladder.child_mass

end AxCheck
