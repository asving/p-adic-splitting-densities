/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G19
import Uniformity.ChapG.G21

/-!
# Uniformity.ChapG.G22 — `resStratum`, classes of depth exactly `2k` with a given residual pair

**Chapter G, NODE G.22** (`blueprint/CHAP-G_base_cases_menus.md` §5). `resStratum π N k p` = the
classes of depth exactly `2k` whose residual pair at a depth-`2k` centre reduces to `p`.

DEPENDS: G.19, G.21.

**Cross-read note (AMENDMENT §A-1, 2026-08-15).** This definition is unchanged by A-1: the
finding there is that `resStratum` is not the right *counting* unit at a single pair `p` (the
residual pair is only a translation-orbit invariant, not a class invariant), not that the
`resStratum` predicate itself is mis-defined. G.23a (`card_resStratum`) is withdrawn; this node
(`resStratum` itself) and G.23b (`depthSet_eq_iUnion_resStratum`) both survive as stated.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- Classes of depth exactly `2k` carrying the residual pair `p`. -/
def resStratum (π : O) (N k : ℕ) (p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O) :
    Set (Coeff O 2 N) :=
  {c | c ∈ depthSet π N (2 * k) ∧
    ∃ (a : Fin 2 → O) (γ : O), proj O 2 N a = c ∧ Tang π a (2 * k) γ ∧
      ∃ (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ), residualPair h0 h1 = p}

end Uniformity.Density.Menu
