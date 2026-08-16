/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D02

/-!
# Uniformity.ChapD.D03 — `NormSection.tau_cocycle`, the cocycle law `(C2-cocycle)`

**Chapter D, NODE D.03** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern — this node's signature is unamended).
ENV-D2. One public declaration, the signed theorem.

*The cocycle law `(C2-cocycle)`.* For all `a b c : ℤ`:

  `τ(a,b)·τ(a+b,c) = τ(b,c)·τ(a,b+c)`,

with `τ` D.02's normalizer cocycle `τ(a,b) = n(a)·n(b)·n(a+b)⁻¹` of a normalizer section
(D.01). This is the second half of `EFF.T1.08`'s boxed content: D.02 landed the ENDPOINTS
(`τ(0,a) = τ(a,0) = 1`, the half that consumes `n_zero`), and this node lands the
associativity half, which consumes nothing but the group axioms.

## Faithfulness

**⚠ Trust-boundary transcription.** Three points, flagged for the chapter cross-read:

* *the τ is D.02's τ, and there is no other.* T3 §8.1 check (3)'s "no competing frame"
  obligation binds here: the `τ` of this law is `NormSection.tau` verbatim, not a re-declared
  cocycle, and the law is stated about an arbitrary section `N`, so no consumer can satisfy it
  with a different two-argument cocycle. The near-miss name is T3's one-argument `χ` (D.39),
  which is a different arity and a different Lean name (blueprint §0.3(ii)).
* *the ARGUMENT SPELLING is the whole tooth.* T1's "misindexed telescope tooth"
  (`EFF.T1.08` TEETH) is a mutation that shifts one argument — e.g. `τ(a+b,c)` written
  `τ(a,b+c)` on the left. The statement as landed pins the two parenthesizations against each
  other in the exact order `(a,b),(a+b,c)` versus `(b,c),(a,b+c)`; the sides are NOT symmetric
  under a naive swap, which is what makes the mutant a failing `rfl` rather than a re-proof.
  Its executable partner is gate D.67's numeric leg.
* *heights are integers and every sum is total.* `EFF.T1.08`'s CONDITIONALITY ("all displayed
  heights and sums must be defined") is discharged by D.01's typing `n : ℤ → G`: `a + b`,
  `b + c` and `a + b + c` are total on `ℤ`, so the law needs no side condition. Nothing here
  is `K`-valued and no residue is taken — that layer is D.07/D.08.

DEPENDS: D.02 (`NormSection.tau`, landed at `Uniformity.ChapD.D02`; transitively D.01's
`NormSection`). Note what is NOT consumed: `n_zero` plays no part in this law — unfolding `τ`
leaves a pure `CommGroup` identity — which is exactly why `EFF.T1.08`'s own derivation splits
the endpoints off from the associativity ("Associativity compares the two parenthesizations of
three normalizers. `n̂_i(0) = 1` gives both endpoints").

**PROOF.** The blueprint's, executed. 1. Unfold `tau`: both sides are products of `n a`, `n b`,
`n c` and one inverse `(n (a+b+c))⁻¹` — the middle terms `n (a+b)` / `n (b+c)` each meet their
own inverse. 2. Rewrite the two argument spellings against each other by `add_assoc a b c`
(`(a+b)+c = a+(b+c)`; the instance is given explicitly so the rewrite cannot pick another
sum). 3. Close by commutative-group normalization. One deviation from the blueprint's letter,
recorded: the blueprint says "then `group`", but mathlib's `group` tactic normalizes *without*
assuming commutativity (its own docstring), and after step 2 the two sides differ by the
reordering `n a·n b·n c` versus `n b·n c·n a`. The landed closer is therefore the standard
commutative-group normalization `simp [mul_comm, mul_left_comm, mul_assoc]`, which performs
the inverse cancellations of step 1 and the reordering in one pass. No statement changed.

SOURCE: `EFF.T1.08` (the boxed `(C2-cocycle)` `τ_i(a,b)τ_i(a+b,c) = τ_i(b,c)τ_i(a,b+c)`, and
its DERIVATION "Associativity compares the two parenthesizations of three normalizers");
`EFF.T3.02` (the same law re-imported as `(T1-C2)`).

**TEETH.** T1's "misindexed telescope tooth" (`EFF.T1.08` TEETH) → the mutation this statement
kills is a shifted argument; Lean theorem (this node) + gate D.67's numeric leg. ORIENTATION is
not at stake in this node (τ is orientation-free: it is symmetric in `a`,`b` on a commutative
`G`), so it carries no `ORIENTATION:` field beyond D.02's.

ENVIRONMENT: ENV-D2 (`{G : Type*} [CommGroup G]`, written inline per the B.42 binder rule —
this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only). A PROVED theorem here, not the leanspec `axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- `(C2-cocycle)`: the normalizer cocycle law `τ(a,b)·τ(a+b,c) = τ(b,c)·τ(a,b+c)`
(`EFF.T1.08`, `EFF.T3.02` `(T1-C2)`).  Both sides collapse to `n(a)n(b)n(c)/n(a+b+c)`; the
content is that the two parenthesizations of three normalizers agree. -/
theorem NormSection.tau_cocycle {G : Type*} [CommGroup G] (N : NormSection G) (a b c : ℤ) :
    N.tau a b * N.tau (a + b) c = N.tau b c * N.tau a (b + c) := by
  simp only [NormSection.tau, add_assoc a b c]
  simp [mul_comm, mul_left_comm, mul_assoc]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection.tau_cocycle

end AxCheck
