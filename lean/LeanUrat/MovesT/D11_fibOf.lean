/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E9_fiberDisjoint
import LeanUrat.MovesT.F1_oneF

/-! # T-D11 `fibOf_keying` — the class-tree → VTree keying (S-7), REV 3/5/6: `fibOf`'s
body displayed with the explicit premises `hrep : PrefixCoherentRepr` and
`hri : ReprInj` (Codex-5 gap #10); `fibOf_partition` consumes `hcov : ClassCover`
(REV 5, Codex-4 #9). [E-DEV, MANIFEST: `fibOf` lives HERE, not in Defs.lean — its
`hclosed`/`hleaf`/`hns_leaf` proof fields genuinely require `hrep`/`hri` content and
carry the unit's E-phase sorries; the zero-sorry Defs rule forces the carrier into
its consuming unit. Only T-D11's own theorems consume it.] -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

open Classical in
/-- the per-address representative tree of a class tree. -/
noncomputable def fibOf (hrep : PrefixCoherentRepr n pol)
    (hri : ReprInj n pol)
    (ct : ClassTree n (F := F) pol) : VTree p F where
  chains := (fun a : Σ P : Shape n, PrefIdx n pol P => reprOf a.2) '' ↑ct.addrs
  hfin := ct.addrs.finite_toSet.image _
  hne_nodes := fun H _ => H.nonempty
  hclosed := by sorry
  henV := ct.rootV
  hhen := ct.hroot
  leafV := fun H =>
    if h : ∃ av, av ∈ ct.leafV ∧ reprOf av.1.2 = H then some h.choose.2 else none
  hleaf := by sorry
  nsLeaf := fun H => ∃ a ∈ ct.nsMark, reprOf a.2 = H
  hns_leaf := by sorry

theorem fibOf_fiber_disjoint (hrep : PrefixCoherentRepr n pol)
    (hri : ReprInj n pol) {P : Shape n}
    (hwd : ClassFiberWelldef p F n N m pol P)
    (ct ct' : ClassTree n (F := F) pol) (h : ct ≠ ct')
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) :
    ¬ VTree.ext (fibOf hrep hri ct) (fibOf hrep hri ct') ∧
    Disjoint {x | (fibOf hrep hri ct).fiberAt T χ x}
      {x | (fibOf hrep hri ct').fiberAt T χ x} := by
  sorry

theorem fibOf_partition (hrep : PrefixCoherentRepr n pol)
    (hri : ReprInj n pol)
    (T : TreeModel p F n N m pol)
    (hcov : ClassCover T)
    (χ : Fin n → Fin m) (x : Box p m)
    (hx : Decided T χ x) :
    ∃ ct : ClassTree n (F := F) pol, (fibOf hrep hri ct).fiberAt T χ x := by
  sorry

end LeanUrat.MovesT
