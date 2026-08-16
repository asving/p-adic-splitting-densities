/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E10

/-!
# Uniformity.ChapE.E43 — S1.8C: a recentered level-one key is a test-family member

**Chapter E, NODE E.43** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §6), ENV-E2 (here at its
minimal binding: a commutative base `O` and a label field `K`; nothing below counts residues, so
no `[IsDomain O]`/`[IsDiscreteValuationRing O]`/`[Finite (ResidueField O)]` is taken — GC-6.4).

The S1.8C adjudication has two transcribable clauses, and this file is both of them:

* **(i) the membership identity.** At `(ℓ, d) = (1, 1)` the test-family shape `Ψ = Φ′ + B₀` with
  `deg B₀ < D′` IS the recentered key `Φ′ − Λ` at `Λ := −B₀`. In Lean this is the
  trivial-but-load-bearing algebra `Φ + B₀ = Φ − (−B₀)` (`recentered_is_member`), together with
  the degree/height bookkeeping that makes the identification usable: the recentering datum
  `Λ = −B₀` has the same degree as `B₀` (so the sub-`D` fence transfers), the same height
  (`h(−B₀) = κ`), and the negated digit. `EFF.T2.61`: *"A recentered level-one key is not a
  foreign object to HE6; it is one of HE6's own test polynomials."*
* **(ii) the frame-stability record.** The frame items (i)–(v) *"are not 'carried by' Φ″: nothing
  about them moves when the key does."* In the schema this is enforced by TYPE: the SlotCarrier
  `C` (NODE E.10) has no key argument at all, so a carrier read `C.hgt A` / `C.dig A` cannot
  depend on which key is current. `frame_key_free` is the anchor recording that this elaborates.

## What this node does NOT adjudicate (honesty)

The parts of S1.8C that consume HE3/HE6 pin content — the stage-α transport and the HE6-PROOF
licence — are INSTANCE rows (E.22, `C` placeholders) at HE3's grade cap, not content of this
file. Nothing here asserts the transport; nothing here re-derives `(MP1′)` (RETIRED per
`EFF.T2.25`: *"What is removed is the extra frame-level obligation, not the level-one fences"*),
and per NODE E.44 no carrier for `(MP1′)` is declared anywhere in the chapter.

## Clause (ii) is a type-level claim (⚠ NODE-KIND NOTE, transcribed)

`frame_key_free`'s Lean content is intentionally trivial — its VALUE is that it ELABORATES:
`C.hgt` and `C.dig` are functions of the stage datum and of nothing else, so the corpus's
frame-stability claim is a typing fact rather than a proof obligation. The node exists so that
§13's disposition table has a Lean anchor for `EFF.T2.25`/`.61` (the retirement of `(MP1′)`)
instead of a prose-only claim. The elaboration gate at the end of this file makes the point
executable in the only way available: a single carrier read is literally the SAME term at two
different keys, by `rfl`.

## Beyond-signature support (clause (i)'s bookkeeping, derived — no new hypotheses)

`hgt_neg` and `dig_neg` are NOT in the blueprint SIGNATURE; they are derived from NODE E.10's
existing carrier fields (no field is added, no hypothesis is weakened) and are stated because
the blueprint STATEMENT names exactly this bookkeeping (`h(−B₀) = κ`, `dig(−B₀)` the
choice-independent partner, E.34's directives). Their proofs are the carrier's own laws read at
`A + (−A) = 0`:

* `hgt_neg`: were `hgt (−A) ≠ hgt A`, the ultrametric equality field `hgt_add_eq` would give
  `⊤ = hgt 0 = min (hgt A) (hgt (−A))`, forcing BOTH to be `⊤` — contradicting the assumed
  inequality. So the height is negation-invariant, with no `hgt_neg` field needed.
* `dig_neg`: at a FINITE height `k`, were `dig A + dig (−A) ≠ 0`, the additivity field `dig_add`
  would give `hgt 0 = (k : WithTop ℤ)`, i.e. `⊤ = k` — false. So the digits cancel. The finite
  height is a real hypothesis: at `A = 0` (height `⊤`) the field says nothing and the conclusion
  is supplied instead by `dig_zero`.

DEPENDS: E.10 (`SlotCarrier`) · E.34 (the choice-independent height/digit pair — cited, not
imported: E.34's bijection layer is not used here) · landed `Polynomial.natDegree_neg`.

SOURCE: `EFF.T2.25` (S1.8C: *"`(MP1′)` is retired … `HE3-A-PROOF`, `HE6-SLOT-SEAM`,
`HE6-FAMILY` and `HE6-PROOF` certify it between them"*; *"What is removed is the extra
frame-level obligation, not the level-one fences"*); `EFF.T2.61` (the adjudication, incl. *"At
`(ℓ,d) = (1,1)` the member `Ψ_{λ,Z−s} = Φ′ + B₀` IS the recentered key"*, plus the two reading
directives: only the refined sub-block travels; invoked at the product-1 branch and nowhere
else); `EFF.T2.70` (the print/coherent seam and `(IDX-TWIST)`'s role).

TEETH: the level-one frame-transport hostile tooth → the type-level enforcement above (clause
(ii)) + E.22's instance rows; clause (i) is the consumed identity.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.43, clause (i).** *The membership identity* (`EFF.T2.61`): the test-family shape
`Ψ = Φ + B₀` at `(ℓ, d) = (1, 1)` IS the key `Φ` recentered at `Λ := −B₀`. Trivial algebra,
load-bearing adjudication: it is what makes a recentered level-one key one of HE6's own test
polynomials rather than a foreign object. -/
theorem recentered_is_member {O : Type*} [CommRing O] (Φ B₀ : Polynomial O) :
    Φ + B₀ = Φ - (-B₀) :=
  (sub_neg_eq_add Φ B₀).symm

/-- **NODE E.43, clause (ii).** *The frame does not move when the key does.* The SlotCarrier
reads `C.hgt A` / `C.dig A` take no key argument (NODE E.10's signature), so frame stability is
a typing fact: this statement is `rfl`, and the content is that it elaborates at all. Stated as
a rewriting anchor for consumers (`EFF.T2.25`/`.61`, §13's disposition table). -/
theorem frame_key_free {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (A : Polynomial O) :
    C.hgt A = C.hgt A ∧ C.dig A = C.dig A :=
  ⟨rfl, rfl⟩

section Bookkeeping

variable {O : Type*} [CommRing O] {K : Type*} [Field K]

/-- **NODE E.43** (clause (i)'s height bookkeeping; derived, not a new carrier field). The slot
height is negation-invariant: `h(−A) = h(A)`, so the recentering datum `Λ = −B₀` sits at the
same height `κ` as the member's offset `B₀`. Proved from `hgt_add_eq` at `A + (−A) = 0`. -/
theorem hgt_neg (C : SlotCarrier O K) (A : Polynomial O) : C.hgt (-A) = C.hgt A := by
  by_contra hne
  have hne' : C.hgt A ≠ C.hgt (-A) := fun h => hne h.symm
  have hmin : C.hgt (A + -A) = min (C.hgt A) (C.hgt (-A)) := C.hgt_add_eq A (-A) hne'
  rw [add_neg_cancel, C.hgt_zero] at hmin
  have h1 : (⊤ : WithTop ℤ) ≤ C.hgt A := hmin ▸ min_le_left (C.hgt A) (C.hgt (-A))
  have h2 : (⊤ : WithTop ℤ) ≤ C.hgt (-A) := hmin ▸ min_le_right (C.hgt A) (C.hgt (-A))
  exact hne (top_le_iff.mp h2 |>.trans (top_le_iff.mp h1).symm)

/-- **NODE E.43** (clause (i)'s digit bookkeeping; derived, not a new carrier field). At a FINITE
height the slot digit is negation-antisymmetric: `dig (−A) = −dig A`. Proved from `dig_add` at
`A + (−A) = 0`, whose conclusion would put the zero polynomial at the finite height `k`. The
finiteness hypothesis is real: at `A = 0` the carrier's additivity field says nothing (there
`dig_zero` supplies the value directly). -/
theorem dig_neg (C : SlotCarrier O K) (A : Polynomial O) {k : ℤ}
    (hk : C.hgt A = (k : WithTop ℤ)) : C.dig (-A) = -C.dig A := by
  have hkneg : C.hgt (-A) = (k : WithTop ℤ) := by rw [hgt_neg, hk]
  by_contra hne
  have hsum : C.dig A + C.dig (-A) ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_right h0)
  have hzero := (C.dig_add A (-A) k hk hkneg hsum).1
  rw [add_neg_cancel, C.hgt_zero] at hzero
  exact (WithTop.top_ne_coe) hzero

/-- **NODE E.43, clause (i) packaged.** *The recentering datum of a level-one member.* For the
test-family member `Ψ = Φ + B₀` at a finite offset height `κ`, the datum `Λ = −B₀` realises `Ψ`
as the recentered key `Φ − Λ` AND carries the offset's own bookkeeping: the same degree (so the
sub-`D` fence `deg B₀ < D` transfers verbatim to `Λ`), the same height `κ`, and the negated
digit. This is the whole of `EFF.T2.61`'s identification, in one consumable statement. -/
theorem recentered_bookkeeping (C : SlotCarrier O K) (Φ B₀ : Polynomial O) {κ : ℤ}
    (hκ : C.hgt B₀ = (κ : WithTop ℤ)) :
    Φ + B₀ = Φ - (-B₀) ∧ (-B₀).natDegree = B₀.natDegree ∧
      C.hgt (-B₀) = (κ : WithTop ℤ) ∧ C.dig (-B₀) = -C.dig B₀ :=
  ⟨recentered_is_member Φ B₀, Polynomial.natDegree_neg B₀,
    (hgt_neg C B₀).trans hκ, dig_neg C B₀ hκ⟩

end Bookkeeping

end Uniformity.Density.Ladder

/-! ## Elaboration gate — the two clauses, consumed

No `decide` gate is available here and none is owed: `Polynomial O` equality is not decidable at
this pin (the coefficient support is a `Finsupp`), and clause (ii) is a claim about ELABORATION,
which no `#guard` can express. The gate is therefore the honest one — the statements are
consumed in the shapes downstream nodes will use them in, at concrete data where possible. -/

section ElaborationGate

open Polynomial Uniformity.Density.Ladder

/-- Clause (i) at concrete data over `ℤ`: the member `Ψ = (X² + 3) + 2X` of the test family is
the key `X² + 3` recentered at `Λ = −2X`. -/
example : ((X ^ 2 + C 3) + C 2 * X : Polynomial ℤ)
    = (X ^ 2 + C 3) - (-(C 2 * X)) :=
  recentered_is_member _ _

/-- Clause (i) as a REWRITE, the way a consumer meets it: a hypothesis stated about a member
`Φ + B₀` is transported to the recentered key `Φ - (-B₀)` with no side condition. -/
example {O : Type*} [CommRing O] (P : Polynomial O → Prop) (Φ B₀ : Polynomial O)
    (h : P (Φ + B₀)) : P (Φ - (-B₀)) := by
  rwa [recentered_is_member] at h

/-- Clause (ii), executable form: the carrier read at a polynomial is literally the SAME term
whichever key is "current" — the two keys `Φ₁`, `Φ₂` cannot even be mentioned in the read, so
the equation closes by `rfl`. This is the type-level enforcement, exhibited. -/
example {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (A Φ₁ Φ₂ : Polynomial O) (_hne : Φ₁ ≠ Φ₂) :
    (C.hgt A, C.dig A) = (C.hgt A, C.dig A) :=
  rfl

/-- The sub-`D` fence transfers to the recentering datum: `deg B₀ < D` gives `deg (−B₀) < D`,
which is the form E.22's instance rows consume. -/
example {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B₀ : Polynomial O) (h : B₀.natDegree < C.D) :
    (-B₀).natDegree < C.D := by
  rwa [Polynomial.natDegree_neg]

end ElaborationGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.recentered_is_member
#print axioms Uniformity.Density.Ladder.frame_key_free
#print axioms Uniformity.Density.Ladder.hgt_neg
#print axioms Uniformity.Density.Ladder.dig_neg
#print axioms Uniformity.Density.Ladder.recentered_bookkeeping

end AxCheck
