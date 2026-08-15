/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02

/-!
# Uniformity.ChapB.B75 — `Visible`, window visibility of the order-1 read

**Chapter B, NODE B.75** [def] (`blueprint/CHAP-B_leaf_layer.md` §9, the level-`N` decidedness
certificates), ENV-A.

For `π : O`, polynomials `φ, f` and a level `N : ℕ`, the order-1 read of `f` at the key `φ` is
**visible at level `N`** when some coefficient of the constant development coefficient `dev φ f 0`
is not divisible by `π ^ N`. Since the `φ`-adic polygon of `f` runs from `(0, npHgt φ f 0)` down to
`(μ, 0)` and is convex, `npHgt φ f 0` bounds *every* height the order-1 read consults — every vertex
height, every on-side line height `H₀ − u·k`, and every "strictly above the line" ceiling — so
`Visible π φ f N` says exactly: *all data the read consumes sit at heights `≤ N − 1`.*

DEPENDS: B.02 (`dev`).

**PROOF.** Definitional. Two choices are deliberate, and both are the blueprint's.

1. **The digit form is primary.** `∃ i, ¬ π ^ N ∣ (dev φ f 0).coeff i` rather than the valuation
   form `npHgt φ f 0 < N`: it is literally a statement about the window, it mentions no `ℕ∞`, and it
   is the form a certificate checker evaluates on a level-`N` class. The two are equated at B.76
   (`visible_iff_npHgt_lt`), which needs `Irreducible π` — and that is why `π` is an argument of the
   definition even though nothing here uses its irreducibility. ENV-A is therefore the right
   environment: `π` enters as *data*, not as a hypothesis.
2. **Visibility is pinned at abscissa `0`, not per side.** B.76's calculus derives every per-side
   bound from the abscissa-`0` read (for `0 < ℓ`, `suppVal φ f u ℓ ≤ ℓ • npHgt φ f 0`, so every
   on-side height is `≤ npHgt φ f 0`); a per-side definition would multiply the transport lemmas by
   the number of sides for no gain.

**FAITHFULNESS.** Three sources, and the definition must be read against all three.

* `EFF.HE3.67` (R8-1, the *rewritten* certificate — the chapter's line-221 commitment) clause 2:
  "at every nonterminal node ν, every recentered value consulted there is either read exactly below
  `c_ν`, or is known only to be `≥ c_ν` but satisfies `c_ν > b_{ν,j}`, so that the required strict
  inequality above the supporting line is nevertheless certified." At chapter B's single order-1
  node with cap `c = N` (DECISION D-4(c)): values on the hull are read exactly below `N` (their
  heights are `≤ npHgt φ f 0 < N`), and values off the hull need only "`≥ hull ceiling`", certified
  since `N > npHgt φ f 0 ≥ b_j` for every supporting-line height `b_j`. **The superseded
  `LEMMA HE3-5` display (`EFF.HE3.37`) is not transcribed, and no "one more window unit" clause
  exists here.**
* `EFF.W12.23`: "Every pinned or priced slot sits at height `≤ P(0) ≤ N−1`: in-window, no truncation
  error" — `P(0)` is `npHgt φ f 0` and "`≤ N−1`" is `< N`. Also `EFF.W12.28`'s per-family visibility
  clause "`u₀ ≤ N−1`" (there `u₀ = v(b₀) = P(0)` at the TRP center).
* The **junk direction is meaningful**: `Visible` is *false* exactly when every digit of `dev φ f 0`
  vanishes in-window. `EFF.HE3.55`'s never-decided residue — "the 25 / 49 with vanishing residual
  constant (no full side: outside the genre)" — is precisely the `¬ Visible` locus, and it is
  correct that no certificate below fires there.

**Flagged for human review as a new definition** (parent CLAUDE.md trust boundary), and the
faithfulness reading above is flagged with it.

**SOURCE.** `EFF.HE3.67` (R8-1 clause 2, the rewritten certificate — transcribed per H-4);
`EFF.W12.23` (the in-window slot-height law); `EFF.W12.28` (the `u₀ ≤ N−1` instances);
`EFF.HE3.55` (the `¬ Visible` residue, read through its R8-1 re-scoping).

**TEETH.** `HE-BND` (`EFF.HE3.55`, 3,744 boundary reads, RE-SCOPED by R8-1) → executable regression
retained with the re-scoping carried (D-4(c)): the battery's zero-decided row at `cap < μλ` is
instance evidence that invisibility blocks certification; no general `N`-law is scored.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `Visible π φ f N` : the order-1 read of `f` at the key `φ` is contained in the height-`N`
window — some digit of `dev φ f 0` sits strictly below height `N`. Equivalently (given
`Irreducible π`): `npHgt φ f 0 < N`. -/
def Visible (π : O) (φ f : Polynomial O) (N : ℕ) : Prop :=
  ∃ i, ¬ π ^ N ∣ (dev φ f 0).coeff i

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.Visible
end AxCheck
