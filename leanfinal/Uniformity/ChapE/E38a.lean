/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Uniformity.ChapE.E38a — slot domination, the off-disk positivity arithmetic (HE7-12 (a))

**Chapter E, NODE E.38** [theorem], **second of the SPLIT-MANDATED pair**
(`blueprint/CHAP-E_sigma_ladder.md` §5: *"`slot_fold` and `offdisk_positivity` as two files
(`E38`, `E38a`) — independent consumers (E.42 needs the fold; E.23's HE7-12(a) row needs the
arithmetic)"*). The fold clause is `leanfinal/Uniformity/ChapE/E38.lean`; this file lands
`offdisk_positivity`. ENV-E1 (the arithmetic clause's environment: nothing but `ℤ`).

## What the node says

`EFF.HE7.44` clause (a)'s displayed bound, transcribed as a standalone arithmetic lemma:

> `(ν − T₂) + ε₁ − ℓ(D′−1)ε₀ > 0`

under the source's case data. This is the whole content — pure `ℤ` arithmetic, no carrier, no
polynomial, no slot. The case data is what carries the geometry, and it enters as the hypothesis
`hcase`; everything the source's proof does with it is the substitution in the `ε₀ > 0` branch,
made machine-visible as gate (b) below.

## The two branches

* **`ε₀ > 0`.** Substitute the source's `ε₁ = ℓ(λ − D′h) + ℓD′ε₀`. The `ε₀` terms collapse —
  `ℓD′ε₀ − ℓ(D′−1)ε₀ = ℓε₀` — leaving `(ν − T₂) + ℓ(λ − D′h) + ℓε₀`, a sum of a strictly positive
  term (`hν`) and two nonnegative-and-here-strictly-positive products (`hℓ` with `hlam`; `hℓ` with
  `ε₀ > 0`). The two products are where the only nonlinearity lives, so they are supplied as
  explicit `mul_pos` facts and the rest is linear.
* **`ε₀ = 0`.** The subtracted term vanishes identically and the bound is `(ν − T₂) + ε₁ > 0`,
  from `hν` and `hε₁` alone (gate (d)).

## ⚠ TWO HONEST DISCLOSURES

1. **`hD : 1 ≤ D′` is CARRIED BUT UNCONSUMED.** The signed hypothesis is kept — the SIGNATURE is
   frozen and this file does not touch it — but the proof never needs it, because in the `ε₀ > 0`
   branch `D′` cancels out of the substituted expression entirely and in the `ε₀ = 0` branch it is
   multiplied by zero. Gate (a) proves the identical conclusion with `hD` DELETED, so the
   disclosure is machine-checked rather than asserted. (Same posture as E.18's signed-but-unused
   `hD`, which that file also flags in-place.) The `linter.unusedVariables` warning this produces
   is silenced locally, with this note as the reason.
2. **The signed `hcase` is WEAKER than the source's case list, hence the theorem is STRONGER.**
   `EFF.HE7.44`(a) splits three ways — `ε₀ > 0` (substitute), `ε₀ = 0 < ε₁`, `ε₀ = ε₁ = 0` — while
   the signed second disjunct is the bare `ε₀ = 0`, merging the source's last two. Gate (c) maps
   the source's three cases onto the two signed disjuncts, so the transcription is checked to
   COVER the source rather than merely to resemble it. Nothing is assumed that the source does not
   supply.

DEPENDS: nothing in the project — this is the ENV-E1 arithmetic leaf. E.10's carrier does not
appear, and neither does E.38's fold: the two halves of NODE E.38 share a source clause, not a
statement. mathlib `mul_pos`, `linarith`, `ring`.

SOURCE: `EFF.HE7.44` (LEMMA HE7-12, the clause-(a) proof's three-case positivity computation, and
the displayed bound transcribed above); `EFF.HE7.43` (the slot-domination mechanism this bound
serves: key slots AT `T₂`, increment slots strictly above, the off-disk estimate separating them).

TEETH: `he7r2_supp.py` B2 — the off-disk inequality in resultant-sum form, 210/210 machine members
→ **Lean theorem**, landed here. B2 carries the `[r3]` vacuity disclosure (the `δ = ∞` half is
vacuous on 41 of 42 members); that disclosure is a property of the numeric battery's coverage, not
of this arithmetic statement, and is recorded in the blueprint §13 honesty census.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free: `offdisk_positivity` reports at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}`. Transcribed byte-for-byte against the signed SIGNATURE
(`leanspec/Leanspec/ChapE.lean` §5), INCLUDING the A-E.1/E-D3 repair — the hypothesis is `hlam`,
not `hλ`, because `hλ` is not a legal Lean identifier (hard parse error at the gate, *"unexpected
token 'λ'"*). Variable names, binder order and the conclusion are otherwise unchanged.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- Disclosure 1 (see the header): the signed `hD : 1 ≤ D'` is frozen into the SIGNATURE and kept
-- verbatim, but the proof does not consume it — `D'` cancels in the `ε₀ > 0` branch and is
-- multiplied by zero in the other. Gate (a) proves the conclusion with `hD` deleted.
set_option linter.unusedVariables false in
/-- **E.38 — the off-disk positivity arithmetic** (LEMMA HE7-12 clause (a), `EFF.HE7.44`). The
displayed bound `(ν − T₂) + ε₁ − ℓ(D′−1)ε₀ > 0`, under the source's case data. Pure `ℤ`
arithmetic: the `[repaired: A-E.1/E-D3]` hypothesis name is `hlam` (`hλ` does not parse). -/
theorem offdisk_positivity {ν T₂ ℓ D' h lam ε₀ ε₁ : ℤ}
    (hν : T₂ < ν) (hlam : D' * h < lam) (hℓ : 1 ≤ ℓ) (hD : 1 ≤ D')
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hcase : (0 < ε₀ ∧ ε₁ = ℓ * (lam - D' * h) + ℓ * D' * ε₀) ∨ ε₀ = 0) :
    0 < (ν - T₂) + ε₁ - ℓ * (D' - 1) * ε₀ := by
  rcases hcase with ⟨hpos, heq⟩ | h0
  · -- `ε₀ > 0`: substitute; `ℓD′ε₀ − ℓ(D′−1)ε₀ = ℓε₀`, so the bound is a sum of positives
    subst heq
    have h2 : 0 < ℓ * (lam - D' * h) := mul_pos (by linarith) (by linarith)
    have h3 : 0 < ℓ * ε₀ := mul_pos (by linarith) hpos
    linarith
  · -- `ε₀ = 0` (the source's last two cases): the subtracted term vanishes
    subst h0
    linarith

/-! ## Gates (executed `example`s, not blueprint declarations)

**(a) `hD` is unconsumed — proved, not asserted.** The identical conclusion under the identical
hypotheses MINUS `hD : 1 ≤ D′`. Disclosure 1 of the header, machine-checked. A future reader who
sees `hD` in the SIGNATURE and wonders whether the bound secretly needs `D′ ≥ 1` gets the answer
here.

**(b) The substitution the source performs, as a `ring` identity.** In the `ε₀ > 0` branch the
whole content is that `ℓD′ε₀ − ℓ(D′−1)ε₀` collapses to `ℓε₀`. Displayed as an equation so that
the step is checkable independently of the inequality reasoning.

**(c) The source's THREE cases collapse into the signed TWO disjuncts.** Disclosure 2, machine-
checked: `EFF.HE7.44`(a)'s `ε₀ > 0` / `ε₀ = 0 < ε₁` / `ε₀ = ε₁ = 0` all imply the signed `hcase`,
so the transcription covers the source. The converse direction is deliberately not claimed — the
signed form is the weaker hypothesis, i.e. the stronger theorem.

**(d) The `ε₀ = 0` branch needs only `hν` and `hε₁`.** No case data, no `ℓ`, no `D′`. -/

section Gate

-- (a) the conclusion holds with `hD` DELETED: the signed hypothesis is not load-bearing.
example {ν T₂ ℓ D' h lam ε₀ ε₁ : ℤ}
    (hν : T₂ < ν) (hlam : D' * h < lam) (hℓ : 1 ≤ ℓ)
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hcase : (0 < ε₀ ∧ ε₁ = ℓ * (lam - D' * h) + ℓ * D' * ε₀) ∨ ε₀ = 0) :
    0 < (ν - T₂) + ε₁ - ℓ * (D' - 1) * ε₀ := by
  rcases hcase with ⟨hpos, heq⟩ | h0
  · subst heq
    have h2 : 0 < ℓ * (lam - D' * h) := mul_pos (by linarith) (by linarith)
    have h3 : 0 < ℓ * ε₀ := mul_pos (by linarith) hpos
    linarith
  · subst h0; linarith

-- (b) the substitution identity: the `ε₀` terms collapse to `ℓ ε₀`.
example {ν T₂ ℓ D' h lam ε₀ : ℤ} :
    (ν - T₂) + (ℓ * (lam - D' * h) + ℓ * D' * ε₀) - ℓ * (D' - 1) * ε₀
      = (ν - T₂) + ℓ * (lam - D' * h) + ℓ * ε₀ := by
  ring

-- (c) the source's three-case split implies the signed two-disjunct `hcase`.
example {ℓ D' h lam ε₀ ε₁ : ℤ}
    (hsrc : (0 < ε₀ ∧ ε₁ = ℓ * (lam - D' * h) + ℓ * D' * ε₀) ∨ (ε₀ = 0 ∧ 0 < ε₁) ∨
      (ε₀ = 0 ∧ ε₁ = 0)) :
    (0 < ε₀ ∧ ε₁ = ℓ * (lam - D' * h) + ℓ * D' * ε₀) ∨ ε₀ = 0 := by
  rcases hsrc with hgt | ⟨h0, _⟩ | ⟨h0, _⟩
  · exact Or.inl hgt
  · exact Or.inr h0
  · exact Or.inr h0

-- (d) at `ε₀ = 0` the bound is `(ν − T₂) + ε₁ > 0`, from the threshold gap and `hε₁` alone.
example {ν T₂ ℓ D' ε₁ : ℤ} (hν : T₂ < ν) (hε₁ : 0 ≤ ε₁) :
    0 < (ν - T₂) + ε₁ - ℓ * (D' - 1) * 0 := by
  linarith

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.offdisk_positivity

end AxCheck
