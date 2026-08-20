/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapB.B38 — the graded Bézout solve over the residual field

**Chapter B, NODE B.38** `exists_solve_resField` (`blueprint/CHAP-B_leaf_layer.md` §6), ENV-D.

*The graded Bézout solve over the residual field.*  Let `K` be a field and `G, H ∈ K[Y]` coprime
monic with `G.natDegree = a`, `H.natDegree = b`.  Every `W ∈ K[Y]` with `W.degree < a + b`
splits as `W = H * U + G * V` with `U.degree < a` and `V.degree < b`.

This node exists **only to record that the landed lemma is stated at the right generality.**  The
blueprint's SIZE field spells out the check it wanted done first: `HenselFactorization.lean:131`
reads `variable {k : Type*} [Field k]` (not `ResidueField O`), so the graded engine inherits the
solve verbatim and no re-proof is needed.  Confirmed at transcription time — the landed
`Uniformity.Hensel.exists_solve_field` (`HenselFactorization.lean:133`) binds an arbitrary field
and the node is the one-liner the blueprint predicted.

The node is stated in `degree`/`WithBot ℕ` rather than `natDegree`/`ℕ`, and that shape is
load-bearing downstream: it is exactly the shape B.39 needed after `B39_REFUTATION_2` killed the
`natDegree` form (`U.natDegree < 0` is `False` in `ℕ`, so a degenerate divisor could not be served;
`U = 0` has `degree = ⊥ < 0` and serves it).

**GC-1 (`sideMin` height pin) is not engaged.** This node mentions neither `resPoly` nor `H₀` — it
is a pure field-level Bézout statement with no polygon in sight.  Its consumer B.39 does the
residual reads and carries the pin.

DEPENDS: landed `Uniformity.Hensel.exists_solve_field` (`HenselFactorization.lean:133`).

## Binder-vacuity audit (MANDATORY, per `blueprint/CHAP-C_tower_grammar.md` §A-C.8.4)

Verdict: **no vacuous binder; the hypothesis set is satisfiable and two of the three guards are
sharp at explicit counterexamples.**  Registry, one row per hypothesis:

| binder | verdict | witness / counterexample |
| --- | --- | --- |
| `[Field K]` | non-vacuous | `K = ℚ`; every instance below lives there. |
| `hG : G.Monic` | satisfiable, **NOT sharp** (convenience) | `G = Y` satisfies it. The conclusion does **not** need it: over a field a coprime pair `(G, H)` may be scaled monic without changing `IsCoprime`, the degrees, or the solvability of `W = H*U + G*V`. `G = C 2`, `H = Y`, `W = C 1` over `ℚ` violates `hG` and still solves (`U = 0`, `V = C (1/2)`). Retained because the landed template asks for it (it drives `degree_modByMonic_lt`). Restricts the instance set but is not load-bearing for truth. |
| `hH : H.Monic` | satisfiable, **NOT sharp** (convenience) | symmetric: `G = Y`, `H = C 2`, `W = Y`, solved by `U = C (1/2) * Y`… i.e. `V = 0`, `U = C (1/2) * W`. |
| `hcop : IsCoprime G H` | **SHARP — load-bearing** | `K = ℚ`, `G = H = Y` (both monic, `a + b = 2`), `W = 1` (`degree 0 < 2`). Then `H*U + G*V = Y*(U+V)` has zero constant coefficient for every `U, V`, so `W = 1` is unreachable. Dropping `hcop` makes the statement FALSE. |
| `hW : W.degree < ↑(a+b)` | **SHARP — load-bearing** | `K = ℚ`, `G = Y`, `H = Y + 1`, so `a + b = 2`; take `W = Y ^ 2`. The conclusion's own bounds force `U, V` constant, so `H*U + G*V` has degree `≤ 1 < 2`. Dropping `hW` makes the statement FALSE. |

Refutation attempts against my own guards: the two monicity guards were attacked successfully (the
statement survives without them, so they are recorded as non-sharp rather than sharp); `hcop` and
`hW` were attacked and both attacks produced the counterexamples above, which is the *ideal*
outcome — each guard is exactly the boundary of the truth.  Nothing here is unestablished: every
row's witness is elementary and exhibited.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

/-! ## The node -/

/-- **B.38** (`exists_solve_resField`), ENV-D.  *The graded Bézout solve over the residual field.*
For coprime monic `G, H` over a field `K` and any `W` of degree `< G.natDegree + H.natDegree`
there are `U, V` with `U.degree < G.natDegree`, `V.degree < H.natDegree` and `W = H * U + G * V`.

Note the pairing (inherited from the landed template, and the one the Newton correction of B.39
needs): the bound on `U` is against `G`'s degree while `U` multiplies `H`. -/
theorem exists_solve_resField {K : Type*} [Field K] {G H : Polynomial K}
    (hG : G.Monic) (hH : H.Monic) (hcop : IsCoprime G H) {W : Polynomial K}
    (hW : W.degree < ((G.natDegree + H.natDegree : ℕ) : WithBot ℕ)) :
    ∃ U V : Polynomial K, U.degree < (G.natDegree : WithBot ℕ) ∧
      V.degree < (H.natDegree : WithBot ℕ) ∧ W = H * U + G * V :=
  Uniformity.Hensel.exists_solve_field hG hH hcop hW

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_solve_resField
end AxCheck
