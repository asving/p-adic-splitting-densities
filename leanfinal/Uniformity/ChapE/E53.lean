/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E46

/-!
# Uniformity.ChapE.E53 — the GC-3 bridge FENCE: `e · f` is conserved, and identified with nothing

**Chapter E, NODE E.53** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws), ENV-E1. A **statement-shaped fence node**: deliberately thin in Lean
content, and existing so that GC-3's prohibition has a machine-readable anchor in the corpus
rather than living only in a blueprint paragraph.

## The fence (this is the node; read it before using anything in this file)

Chapter E's dictionary emits pairs `(e, f)` of natural numbers. The ideal-theoretic pair —
`Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` of the maximal ideal of the local ring `S`
over the base — is a *different* object, living in a different theory. **This repo does not
identify them.** The identification is ledger rows `HYP.01` + `HYP.12`, both **[CORE-SET]**
(human-review), and GC-3's ruling is verbatim: the two are *"KEPT APART, on pain of HYP.01"*.

Operationally, for any consumer:

> If your argument needs "the dictionary's `e` **is** `ramificationIdx'`" (or the same for `f`
> and `inertiaDeg'`), you must either take that as an **explicit hypothesis in your own
> signature**, or return `BLOCKED: HYP.01`. You may not derive it, and nothing in chapter E
> supplies it.

This is the `inertiaDegOf`-lesson class of defect: a silent identification of a combinatorial
shadow with an ideal-theoretic invariant, which type-checks (both are `ℕ`) and is unprovable.

## What Lean actually carries here

`leaf_ef_finrank` is the **conservation composition**, and nothing more: `e · f = n` transported
across an anchor `hrank`. The mathematics is already proved — it is E.46's
`ladderSigma_degree` (`(FUND)` `|Ω| = ef`, summed over the emission) — and this node's job is to
be the place where an instance *substitutes* `Module.finrank K₀ L` for `n`, at which point the
substitution is the instance's declared content, visible in its signature.

`hrank : n = n` is the anchor binder. It is trivially true and it is **deliberately trivial**:
it marks the slot where the quarry identity would be plugged in, WITHOUT this file asserting
that it may be. Landing anything stronger here — e.g. binding `n` to `finrank` by hypothesis and
concluding about `ramificationIdx'` — would be exactly the defect the fence exists to prevent.

## The quarry identity — cited, NOT consumed

`Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`
(`leanfinal/Uniformity/Quarry/RamificationInertiaLocal.lean`, the GC-3 primed generation) proves
`ramificationIdx' * inertiaDeg' = Module.finrank R S` for `S` local, finite over a Dedekind
domain. That is the rank-form fundamental identity on the *ideal-theoretic* side. It is cited
here as the object an instance would compose against; **this file does not import it**, so no
consumer of E.53 can accidentally acquire the bridge by transitivity of imports. The
non-importing is part of the fence, not an oversight.

DEPENDS: E.46 (`ladderSigma_degree` — the conservation this node transports) · [quarry:
`Uniformity/Quarry/RamificationInertiaLocal.lean` — cited, not consumed].

SOURCE: GC-3 ("KEPT APART, on pain of HYP.01"); `EFF.T2.30` (`(FUND)` `|Ω| = ef`); ledger rows
HYP.01 / HYP.12 (CORE-SET, human-review).

TEETH: none — this is a fence, not an empirical claim.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, Lean-core axioms only. Thin by design; the FENCE TEXT above is the contract.
-/

set_option linter.style.longLine false
-- `hrank : n = n` is the fence's anchor binder and is deliberately unused (see the module
-- docstring): it marks the substitution slot without asserting the substitution.
set_option linter.unusedVariables false

namespace Uniformity.Density.Ladder

/-- **NODE E.53** — the GC-3 bridge fence. The dictionary's leaf invariants satisfy
`e · f = n` (E.46's conservation), transported across the anchor `hrank`, at which an instance
substitutes `Module.finrank K₀ L` for `n` via the quarry identity. The identification of
`(e, f)` with `(ramificationIdx', inertiaDeg')` is **HYP.01 + HYP.12 [CORE-SET] and is NOT
made here**: a consumer needing it states it as an explicit hypothesis or returns
`BLOCKED: HYP.01`. -/
theorem leaf_ef_finrank {e f n : ℕ} (hef : e * f = n)
    (hrank : n = n) :  -- anchor: instances substitute `finrank K₀ L` here via the
                       -- quarry identity; the fence forbids more
    e * f = n :=
  hef

end Uniformity.Density.Ladder

/-! ## Gate — the conservation the fence transports, and the fence's own scope

Two things are checked. First, that the node genuinely composes with E.46: a single-leaf
emission's `.degree` *is* its `e · f`, so `leaf_ef_finrank` fires on real dictionary output
rather than on an abstract `ℕ`. Second, the **scope** of the fence: the `#guard`s exhibit
distinct `(e, f)` pairs with the same product, which is precisely why `e · f = n` cannot be
inverted to recover `(e, f)` — and hence why an identification of the pair with
`(ramificationIdx', inertiaDeg')` is extra information, never a consequence of conservation. -/

section Gate

open Uniformity Uniformity.Density.Ladder

/-- The node fires on genuine dictionary output: for a single leaf, E.46's conservation gives
`.degree = e · f`, and `leaf_ef_finrank` transports it across the anchor. -/
example (e₀ f₀ : ℕ) (l : LadderLeaf) :
    (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2 = (ladderSigma e₀ f₀ {l}).degree := by
  refine leaf_ef_finrank ?_ rfl
  rw [ladderSigma_degree]
  simp

/-- The three-letter alphabet of E.49/E.50, read through the fence: each letter's blocks account
for degree `8`, and that is *all* conservation says about them. -/
example : (8 : ℕ) * 1 = 8 := leaf_ef_finrank rfl rfl

-- Conservation at the μ₂ = 2 alphabet: `8·1 = 8`, `4·2 = 8`, `4·1 + 4·1 = 8`.
#guard 8 * 1 == 8
#guard 4 * 2 == 8
#guard 4 * 1 + 4 * 1 == 8

-- THE FENCE'S SCOPE, executed: `e · f = 8` is satisfied by FOUR distinct ordered pairs. So the
-- product determines neither `e` nor `f`; a fortiori it cannot determine that they equal
-- `(ramificationIdx', inertiaDeg')`. This is the arithmetic reason HYP.01 is a hypothesis and
-- not a lemma.
private def factorPairs (n : ℕ) : List (ℕ × ℕ) :=
  ((List.range (n + 1)).flatMap fun e => (List.range (n + 1)).map fun f => (e, f)).filter
    (fun p => p.1 * p.2 == n)

#guard (factorPairs 8).length == 4
#guard (factorPairs 8) == [(1, 8), (2, 4), (4, 2), (8, 1)]

-- Two DIFFERENT letters of the alphabet, `(8,1)` and `(4,2)`, share the product 8 — the
-- collision is inside the dictionary's own image, not a contrived example.
#guard (8 * 1 : ℕ) == (4 * 2 : ℕ)
#guard ((8, 1) : ℕ × ℕ) != ((4, 2) : ℕ × ℕ)

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.leaf_ef_finrank

end AxCheck
