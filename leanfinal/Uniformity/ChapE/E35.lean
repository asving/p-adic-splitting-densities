/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E10
import Mathlib.Data.ZMod.Basic

/-!
# Uniformity.ChapE.E35 — `(REF-HT)`: the refinement height AND digit are forced by `(RISE)`

**Chapter E, NODE E.35** (`blueprint/CHAP-E_sigma_ladder.md` §6), ENV-E2. The forcing step of
the refinement branch, in carrier form: over a slot carrier `C` (E.10), let `a` be the class
value and `b` the increment, with exact heights `C.hgt a = λ` and `C.hgt b = k`. If the
**ultrametric rise** `(RISE)` holds — `λ < C.hgt (a - b)`, the difference sits strictly higher
than the class value — then BOTH the height and the digit of the increment are pinned:

* `(HT)`: `k = λ`. If `k ≠ λ` the heights of `a` and `-b` differ, so `hgt_add_eq` computes the
  height of the difference exactly as `min λ k ≤ λ`, contradicting the rise. `EFF.T2.19`'s
  master implication, verbatim mechanism.
* `(DIG)`: `C.dig b = C.dig a`. At the now-equal height `λ`, if `dig a + dig (-b) ≠ 0` then
  `dig_add` says the difference STAYS at height `λ` — again contradicting the rise. So
  `dig a - dig b = 0`. `EFF.T2.71`'s boxed digit equivalence, carrier form.

## The negation law is a HYPOTHESIS here, deliberately

`hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A` is a carrier law the corpus uses
silently (residues are additive and `d(−x) = d(x)`), and E.10 does **not** carry it as a field.
The blueprint's SIGNATURE NOTE takes it as an explicit hypothesis pending the stub stage, with
the RE-PLAN rule attached: *if three or more consumers thread it, RE-PLAN promotes it to an
E.10 field* (GC-5; a field addition to E.10 is amendment-level and dated). This node is the
first consumer. The hypothesis is threaded, not promoted — promoting it here would be an
unsigned change to E.10's landed structure.

Both halves of `hneg` are used, and each in exactly one place: the height half converts
`C.hgt b = k` into `C.hgt (-b) = k` for the `hgt_add_eq` step, and the digit half converts the
`dig_add` premise `dig a + dig (-b) ≠ 0` into `dig a - dig b ≠ 0`. A consumer supplying only
the height half cannot get clause (ii).

## `(RISE)` STAYS STIPULATED

`hrise` **is** `(RISE)` — carrier-supplied at instances (`EFF.T2.19`'s X02/X10–X11/X24 pins →
the E.22/E.23 instance rows). This node is the FORCING, not a discharge of `(RISE)`. A fleet
agent asked to prove `hrise` has left the chapter.

## Note on the shape of the conclusion

The signed conclusion is `k = lam ∧ C.dig b = C.dig a` — an equality of ℤ heights (not of
`WithTop ℤ` values) and an equality of digits in `K`. Both `a` and `b` are assumed to have
FINITE height (`ha`, `hb` are equalities with coercions of integers), so neither is the zero
polynomial as far as the height law is concerned; no `⊤` case arises and none is signed.

DEPENDS: E.10 (`SlotCarrier`: `hgt_add_eq`, `dig_add`; `hgt_add_ge` is not needed by this
route — the `hgt_add_eq` branch closes clause (i) outright).

SOURCE: `EFF.T2.19` (`(REF-HT)` boxed; the derivation *"If `k ≠ λ`, the ultrametric equality
yields `d(Φ − L_k(s)) = min(λ, k) ≤ λ`, contradicting `(RISE)`; hence `(HT)`"*, and *"`(RISE)`
is a carrier hypothesis, not an open ledger obligation"*); `EFF.T2.71` (the boxed digit
equivalence `d((Φ−Λ)(ρ)) > λ ⟺ ι_ρ(s − dig(Λ)) = 0 ⟺ dig(Λ) = s`, with its `K^×`-membership
and lift-freedom riders, all reproduced by this carrier-level proof); `EFF.T2.59` (the
`(REF-HT)` derivation record: *"(HT) is forced by (RISE), and that forcing uses master data
only"*).

TEETH: the S7 print/coherent index mutant and the lift-choice mutant (`EFF.T2.19`) → a Lean
theorem here. Clause (ii) is what kills the print mutant: the print label `s·η^{−q}` does not
satisfy `dig b = dig a` unless `q = 0`, so the coherent-frame read is the only one that can
elaborate.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free. Footprint `[propext, Classical.choice, Quot.sound]` — Lean core only. No chapter
axiom, in particular not B.42.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.35 `(REF-HT)`.** Over a slot carrier, the ultrametric rise `λ < hgt (a - b)` at
`hgt a = λ`, `hgt b = k` forces BOTH `k = λ` (the height) and `dig b = dig a` (the digit). -/
theorem refht_forced {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)
    {a b : Polynomial O} {lam k : ℤ}
    (ha : C.hgt a = (lam : WithTop ℤ)) (hb : C.hgt b = (k : WithTop ℤ))
    (hrise : (lam : WithTop ℤ) < C.hgt (a - b)) :
    k = lam ∧ C.dig b = C.dig a := by
  -- Work with `a - b` as `a + (-b)`, so the carrier's additive laws apply directly.
  have hsub : a - b = a + (-b) := sub_eq_add_neg a b
  have hnegb : C.hgt (-b) = (k : WithTop ℤ) := by rw [(hneg b).1, hb]
  -- (i) `(HT)`: if the two heights differed, `hgt_add_eq` would pin the difference at
  -- `min lam k ≤ lam`, contradicting the strict rise above `lam`.
  have hk : k = lam := by
    by_contra hne
    have hne' : C.hgt a ≠ C.hgt (-b) := by
      rw [ha, hnegb]
      exact fun h => hne (WithTop.coe_eq_coe.1 h).symm
    have hcalc : C.hgt (a - b) = min ((lam : WithTop ℤ)) ((k : WithTop ℤ)) := by
      rw [hsub, C.hgt_add_eq a (-b) hne', ha, hnegb]
    rw [hcalc] at hrise
    exact absurd (lt_of_lt_of_le hrise (min_le_left _ _)) (lt_irrefl _)
  refine ⟨hk, ?_⟩
  -- (ii) `(DIG)`: at the now-shared height `lam`, a nonzero digit sum would keep the difference
  -- at height `lam` (`dig_add`), again contradicting the rise. So the digits agree.
  by_contra hdig
  have hbl : C.hgt (-b) = ((lam : ℤ) : WithTop ℤ) := by rw [hnegb, hk]
  have hsum : C.dig a + C.dig (-b) ≠ 0 := by
    rw [(hneg b).2]
    intro h
    exact hdig (add_neg_eq_zero.1 h).symm
  have hstay : C.hgt (a + (-b)) = ((lam : ℤ) : WithTop ℤ) :=
    (C.dig_add a (-b) lam ha hbl hsum).1
  rw [hsub, hstay] at hrise
  exact absurd hrise (lt_irrefl _)

end Uniformity.Density.Ladder

/-! ## Gate

`(REF-HT)` is a statement about an abstract carrier, so the gate is a **carrier witness**: a
concrete `SlotCarrier` over `O = ℤ`, `K = ZMod 5` — heights read off a `ZMod 5`-valued
"leading coefficient at degree 0" model — is out of reach at this file's import surface without
re-deriving E.10's five laws. What IS checkable, and what the mutants actually attack, is the
ARITHMETIC of the two contradictions. Both are executed below.

The teeth attack the *forcing*, i.e. the claim that `min lam k ≤ lam` cannot exceed `lam` and
that a same-height sum cannot rise. Their `ℤ`/`WithTop ℤ` shadows are decidable. -/

section Gate

-- (i)'s arithmetic: `min lam k ≤ lam` always, so `lam < min lam k` is impossible — the
-- height-forcing contradiction, over a spot range of `(lam, k)` including `k < lam`, `k = lam`
-- and `k > lam`.
#guard ((List.range 9).map (fun i => (i : ℤ) - 4)).all fun lam =>
  ((List.range 9).map (fun i => (i : ℤ) - 4)).all fun k =>
    decide (min lam k ≤ lam) && !decide (lam < min lam k)

-- The same step in `WithTop ℤ`, where the proof actually runs — proved rather than decided
-- (the lattice structure on `WithTop` is not a `decide` target).
example (x y : WithTop ℤ) : ¬ x < min x y := fun h => absurd (lt_of_lt_of_le h (min_le_left _ _)) (lt_irrefl _)

-- (ii)'s arithmetic, the print-mutant's shape: clause (ii) is an EQUALITY of digits, and the
-- print label multiplies the digit by a unit `η^{-q}`. Over `ZMod 5` at `η = 3` (order 4 in the
-- unit group), the twisted digit `s * 3^q` equals `s` for every nonzero `s` EXACTLY at `q = 0`
-- — the mutant's signature, executed.
#guard (List.range 4).all fun q =>
  ((List.range 4).map (fun i => ((i : ZMod 5) + 1))).all fun s =>
    decide (s * (3 : ZMod 5) ^ q = s) == (q == 0)

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.refht_forced

end AxCheck
