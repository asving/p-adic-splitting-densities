/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniformity.ChapH.H64 — `prod_sub_antitone`, monotonicity of the composed undecided mass

**Chapter H, NODE H.64** (`blueprint/CHAP-H_general_induction.md` §10, sources `EFF.GENIND.168`
(`R6.0`) and `EFF.GENIND.25` (`R6.1`)). With `0 ≤ u i ≤ v i ≤ T i` on `s`,
`∏_{i∈s} (T i − v i) ≤ ∏_{i∈s} (T i − u i)`; equivalently
`∏_{s} T − ∏_{s}(T − u) ≤ ∏_{s} T − ∏_{s}(T − v)`, i.e. the composed undecided mass is
coordinatewise NONDECREASING in the child `u`'s (`∂/∂u_i [∏_j T_j − ∏_j (T_j − u_j)] =
∏_{j≠i} (T_j − u_j) ≥ 0`).

**What was false.** `R6.0` records that PE8 §4.1's necessity rationale — a claim of
non-monotonicity — is wrong; this node lands the true monotonicity and does not reproduce the
false rationale. `EFF.GENIND.25`'s supersession kind is `none received`: `GENIND-C1(ii)` and
`R6.1` are *consumers* of the drain-composition clause, not supersessions of it.

DEPENDS: none · mathlib `Finset.prod_le_prod`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

-- `h0` (`0 ≤ u i` on `s`) is carried because the frozen signature declares it; the proof does not
-- consume it — `0 ≤ T i − v i` comes from `hvT`, and `T i − v i ≤ T i − u i` from `huv` alone. The
-- `unusedVariables` linter is therefore switched off for this declaration only.
set_option linter.unusedVariables false in
/-- **Monotonicity of the composed undecided mass** (`R6.1`): raising each child's undecided mass
`u i` to `v i` (still inside `[0, T i]`) can only shrink the product of complements, hence can only
raise `∏ T − ∏ (T − ·)`. -/
theorem prod_sub_antitone {ι : Type*} (s : Finset ι) (u v T : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (huv : ∀ i ∈ s, u i ≤ v i) (hvT : ∀ i ∈ s, v i ≤ T i) :
    ∏ i ∈ s, (T i - v i) ≤ ∏ i ∈ s, (T i - u i) :=
  Finset.prod_le_prod (fun i hi => sub_nonneg.2 (hvT i hi))
    (fun i hi => sub_le_sub_left (huv i hi) (T i))

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.prod_sub_antitone

end AxCheck
