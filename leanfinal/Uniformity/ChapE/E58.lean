/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E56

/-!
# Uniformity.ChapE.E58 — the per-class refine quartet (ANNEX-LEMMA HE7-13′(b)–(e))

**Chapter E, NODE E.58** [lemma] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §8 —
root-continuation and exhaust), ENV-E2. One signed declaration, `refine_quartet`.

Subtracting a single increment `w` of height `λ` and digit `s := dig w` from the read of a value
`a` does exactly four different things, according to where `a` sits relative to `(λ, s)`:

| where `a` sits | what `a − w` does | clause |
|---|---|---|
| `hgt a = λ`, `dig a = s` | height RISES strictly above `λ` | (b) |
| `hgt a = λ`, `dig a ≠ s` | height stays `λ`, digit translates to `dig a − s` | (c) |
| `hgt a = μ < λ` | untouched: height `μ`, digit `dig a` | (d) |
| `hgt a = ν > λ` | COLLAPSES onto `λ` with digit `−s` | (e) |

Clause (b) is the refined class jumping (E.56(i) under its own name). Clause (c) is what protects
the companion classes: they keep the same height and are separated by their RESIDUES, not by any
slot disjointness — the corpus's own answer to the PE3 charge (`EFF.HE7.96`, *"the mechanism is
NOT slot disjointness … What protects the companion classes on-disk is RESIDUE SEPARATION, clause
(c)'s calculation: same value, different residue"*). Clause (e) is the negative result of the
quartet: every steeper side collapses onto height `λ` with the SAME digit `−s`, independent of
which `a` it came from — which is exactly why the naive "continue the whole `f_S`" move fails.
That independence is fired at data in the gate below.

## How the four clauses are proved (and what does the work)

Three carrier laws, all HYPOTHESES (see the protocol note below): `hneg` (negation), `hsame` (the
same-residue kill) and `hhigh` (a fixed-height sum with a strictly higher partner keeps the lower
summand's height AND digit). Plus one `SlotCarrier` FIELD, `C.dig_add` (digit additivity at a
shared height, `EFF.HE7.96`(c)'s mechanism).

* (b) is `same_digit_rises` (E.56) verbatim — `a` and `w` at the same height with equal digits.
* (c) is `C.dig_add a (−w)`: `hneg` puts `−w` at height `λ` too, and `dig a + dig (−w) =
  dig a − s ≠ 0` is exactly the hypothesis `dig a ≠ s`. Additivity then returns BOTH clauses at
  once (height stays, digit adds), and `a + (−w) = a − w` by `sub_eq_add_neg`.
* (d) and (e) are the SAME instance of `hhigh` with the roles swapped. `hhigh` always takes the
  strictly LOWER summand first: (d) is `hhigh a (−w)` (`a` at `μ`, `−w` at `λ > μ`), (e) is
  `hhigh (−w) a` (`−w` at `λ`, `a` at `ν > λ`). The blueprint PROOF's parenthetical *"careful:
  here `−w` is the LOWER one"* is resolved that way and no other; in (e) the surviving digit is
  therefore `dig (−w) = −s`, with no dependence on `a`.

## The three carrier laws are hypotheses, deliberately (the promotion protocol)

`hneg`, `hsame`, `hhigh` are laws the corpus uses silently and `SlotCarrier` (E.10) does not carry
as fields. The standing protocol (E.35's note, followed by E.56) is to THREAD them and count
consumers; GC-5's RE-PLAN rule promotes to an E.10 field only at three or more, and a field
addition to a landed structure is amendment-level. The blueprint flags these three as ONE
promotion cluster — *"if E.10 grows fields, all three go together (one dated amendment)"* — so
this node threads all three rather than promoting any.

Consumer count after this node: `hneg` — E.35, E.58; `hsame` — E.56, E.58; `hhigh` — E.58.

## Faithfulness

**⚠ Four recasts to check on the chapter cross-read.**

* *the quartet is stated at the CARRIER level, not per root.* The corpus states HE7-13′(b)–(e)
  for the read of `Ψ̃` at a root of the class; `hgt`/`dig` are the ξ-independent transports of
  those reads (E.10's DECISION D-E1), and `a` is any polynomial with the stated height and digit.
  No root, no algebraic closure, no completion appears — the same recast E.56 makes.
* *clause (c)'s `≠ 0` is derived, not dropped.* The corpus display is
  `dig (a − w) = dig a − s ≠ 0`; the signature carries the equation only. The nonvanishing is
  `sub_ne_zero.mpr` applied to the clause's own hypothesis `dig a ≠ dig w`, and it is FIRED in the
  gate below (`residue_separation`) so that the residue-separation reading is machine-checked
  rather than asserted in prose.
* *`μ` and `ν` are `ℤ`, and the comparisons are `ℤ` comparisons cast into `WithTop ℤ`.* A value at
  height `⊤` (i.e. `a = 0`, by `hgt_zero`) is therefore OUT of scope of clauses (d)/(e) by the
  shape of the hypothesis `C.hgt a = (μ : WithTop ℤ)`, not by an omission: the corpus's sides all
  sit at finite heights, and the `⊤` case has no side to collapse.
* *nothing here is a chain statement.* Each clause subtracts ONE increment. Iterating is E.55/E.56's
  business (finiteness, monotonicity); reading the quartet as a statement about a refine chain is
  the error the §14 cross-read entry warns about at E.56.

**DEPENDS.** E.10 (`SlotCarrier`, the `dig_add` field), E.56 (`same_digit_rises` — clause (b) is
consumed by name, not re-proved), E.35 (the `hneg` protocol; cited, not imported — the import of
E.56 already carries E.10).

**SOURCE.** `EFF.HE7.96` clauses (b)–(e) + proof, verbatim (incl. the PE3-charge answer quoted
above; the translation law `r₂^τ(Z) = r₂(Z + s₂)` is the shadow's label move, carried by the
instances' factor bookkeeping and NOT restated here); `EFF.HE7.44`(a) (clause (d)/(e)'s off-disk
sibling).

**TEETH.** `he7annex_supp.py` P2 (clause (c) verified as polynomial EQUALITY, 128/128), P3 (clause
(b), 148 refines), P4 (clause (e)'s cycle tooth, 48/48), P5 (16/16) → **Lean theorem** (this node).

**ENVIRONMENT.** ENV-E2.

## Status

Sorry-free, axiom-free (Lean core only: `propext`, `Classical.choice`, `Quot.sound`).
-/

-- The committed stub spells the negation law's right-hand side `- C.dig A`, with the space
-- (`leanspec/Leanspec/ChapE.lean:1176`, and the landed sibling `E35.lean:85`). The whitespace
-- linter prefers `-C.dig A`; the signature is transcribed byte-for-byte instead, so the linter is
-- turned off here rather than the transcription edited. No other spelling is affected.
set_option linter.style.whitespace false

namespace Uniformity.Density.Ladder

/-- **NODE E.58 — the per-class refine quartet** (ANNEX-LEMMA HE7-13′(b)–(e)). Subtracting one
increment `w` of height `lam` and digit `dig w`:

* **(b)** at height `lam` with the same digit, the difference RISES strictly above `lam`;
* **(c)** at height `lam` with a different digit, the height is UNCHANGED and the digit
  translates by `−dig w` (residue separation — the companion classes persist, distinguished by
  residue and not by slot);
* **(d)** strictly below `lam`, nothing moves (height and digit both unchanged);
* **(e)** strictly above `lam`, everything COLLAPSES to height `lam` with digit `−dig w`,
  independently of `a`.

`hneg`, `hsame`, `hhigh` are the three threaded carrier laws (promotion cluster; see the module
docstring). -/
theorem refine_quartet {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    (hhigh : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      (k : WithTop ℤ) < C.hgt b → C.hgt (a + b) = (k : WithTop ℤ) ∧
        C.dig (a + b) = C.dig a)
    {w : Polynomial O} {lam : ℤ} (hw : C.hgt w = (lam : WithTop ℤ)) :
    (∀ a, C.hgt a = (lam : WithTop ℤ) → C.dig a = C.dig w →
      (lam : WithTop ℤ) < C.hgt (a - w)) ∧
    (∀ a, C.hgt a = (lam : WithTop ℤ) → C.dig a ≠ C.dig w →
      C.hgt (a - w) = (lam : WithTop ℤ) ∧ C.dig (a - w) = C.dig a - C.dig w) ∧
    (∀ a (μ : ℤ), μ < lam → C.hgt a = (μ : WithTop ℤ) →
      C.hgt (a - w) = (μ : WithTop ℤ) ∧ C.dig (a - w) = C.dig a) ∧
    (∀ a (ν : ℤ), lam < ν → C.hgt a = (ν : WithTop ℤ) →
      C.hgt (a - w) = (lam : WithTop ℤ) ∧ C.dig (a - w) = - C.dig w) := by
  -- `−w` sits at the same height as `w`; every clause below is an additive law read at `a + (−w)`.
  have hnw : C.hgt (-w) = (lam : WithTop ℤ) := by rw [(hneg w).1, hw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (b) the refined class jumps: E.56(i) at `(a, w)`.
    intro a ha hd
    exact same_digit_rises C hsame ha hw hd
  · -- (c) companions persist, labels translate: digit additivity at the shared height `lam`,
    -- whose nonvanishing side condition IS the clause's hypothesis `dig a ≠ dig w`.
    intro a ha hd
    have hsum : C.dig a + C.dig (-w) ≠ 0 := by
      rw [(hneg w).2, ← sub_eq_add_neg, sub_ne_zero]
      exact hd
    have hadd := C.dig_add a (-w) lam ha hnw hsum
    rw [← sub_eq_add_neg] at hadd
    refine ⟨hadd.1, ?_⟩
    rw [hadd.2, (hneg w).2, ← sub_eq_add_neg]
  · -- (d) lower sides untouched: `hhigh` with `a` (at `μ`) as the lower summand.
    intro a mu hmu ha
    have hlt : (mu : WithTop ℤ) < C.hgt (-w) := by
      rw [hnw]; exact_mod_cast hmu
    have hres := hhigh a (-w) mu ha hlt
    rw [← sub_eq_add_neg] at hres
    exact hres
  · -- (e) steeper sides collapse: the SAME law with the roles swapped — `−w` (at `lam`) is now
    -- the lower summand, so its digit `−dig w` is what survives, with no dependence on `a`.
    intro a nu hnu ha
    have hlt : (lam : WithTop ℤ) < C.hgt a := by
      rw [ha]; exact_mod_cast hnu
    have hres := hhigh (-w) a lam hnw hlt
    have hcomm : -w + a = a - w := by ring
    rw [hcomm] at hres
    exact ⟨hres.1, by rw [hres.2, (hneg w).2]⟩

end Uniformity.Density.Ladder

/-! ## Gate: the two readings the corpus draws from the quartet, fired as theorems

Not blueprint declarations — executed `example`s, so that an edit which silently changes a clause's
shape breaks the build here rather than four nodes downstream.

`residue_separation` is the PE3-charge answer: clause (c)'s difference has a NONZERO digit, so the
companion class is still a live class after the refine (this is the `≠ 0` of the corpus display,
which the signature leaves implicit). `collapse_is_blind` is clause (e)'s tooth: two values on two
DIFFERENT steeper sides land at the same height with the same digit, so the refine cannot tell
them apart — the precise failure of the naive whole-`f_S` continuation. -/

section Gate

open Uniformity.Density.Ladder

variable {O : Type} [CommRing O] {K : Type} [Field K]

/-- Clause (c)'s nonvanishing, recovered: a companion at the same height keeps a nonzero digit. -/
example (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    (hhigh : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      (k : WithTop ℤ) < C.hgt b → C.hgt (a + b) = (k : WithTop ℤ) ∧
        C.dig (a + b) = C.dig a)
    {w : Polynomial O} {lam : ℤ} (hw : C.hgt w = (lam : WithTop ℤ))
    (a : Polynomial O) (ha : C.hgt a = (lam : WithTop ℤ)) (hd : C.dig a ≠ C.dig w) :
    C.dig (a - w) ≠ 0 := by
  rw [((refine_quartet C hneg hsame hhigh hw).2.1 a ha hd).2, sub_ne_zero]
  exact hd

/-- Clause (e) is blind: any two values strictly above `lam` — at different heights, with
different digits — are sent to the SAME height and the SAME digit. -/
example (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    (hhigh : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      (k : WithTop ℤ) < C.hgt b → C.hgt (a + b) = (k : WithTop ℤ) ∧
        C.dig (a + b) = C.dig a)
    {w : Polynomial O} {lam : ℤ} (hw : C.hgt w = (lam : WithTop ℤ))
    (a b : Polynomial O) (ν₁ ν₂ : ℤ) (h₁ : lam < ν₁) (h₂ : lam < ν₂)
    (ha : C.hgt a = (ν₁ : WithTop ℤ)) (hb : C.hgt b = (ν₂ : WithTop ℤ)) :
    C.hgt (a - w) = C.hgt (b - w) ∧ C.dig (a - w) = C.dig (b - w) := by
  have qa := (refine_quartet C hneg hsame hhigh hw).2.2.2 a ν₁ h₁ ha
  have qb := (refine_quartet C hneg hsame hhigh hw).2.2.2 b ν₂ h₂ hb
  exact ⟨by rw [qa.1, qb.1], by rw [qa.2, qb.2]⟩

/-- Clauses (b) and (c) are exhaustive at height `lam`: every value there either rises or keeps
its height. (The dichotomy the refine loop reads.) -/
example (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    (hhigh : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      (k : WithTop ℤ) < C.hgt b → C.hgt (a + b) = (k : WithTop ℤ) ∧
        C.dig (a + b) = C.dig a)
    {w : Polynomial O} {lam : ℤ} (hw : C.hgt w = (lam : WithTop ℤ))
    (a : Polynomial O) (ha : C.hgt a = (lam : WithTop ℤ)) :
    (lam : WithTop ℤ) < C.hgt (a - w) ∨ C.hgt (a - w) = (lam : WithTop ℤ) := by
  by_cases hd : C.dig a = C.dig w
  · exact Or.inl ((refine_quartet C hneg hsame hhigh hw).1 a ha hd)
  · exact Or.inr ((refine_quartet C hneg hsame hhigh hw).2.1 a ha hd).1

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.refine_quartet

end AxCheck
