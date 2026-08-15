/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H02

/-!
# Uniformity.ChapH.H08 — the node floor sits strictly above `D′h`

**Chapter H, NODE H.08** (`blueprint/CHAP-H_general_induction.md` §3). Two clauses on the
stage-initial node floor `nodeHeight G j = (μ − j)·D′h + 1` of H.02, where `D′ = keyDeg G = e₁f₁`:

* `keyDeg_mul_h_lt_nodeHeight` — for every `j < μ`, `D′h < nodeHeight G j`. This is exactly why
  the TERMINAL `D′h < m` scope of the occupied-height clause suffices for every consumer: every
  pin the `GENHN` laws consume sits in that domain.
* `nodeHeight_of_f_one` — at `f₁ = 1` the floor collapses to the sealed `S = e₁h` form
  `(μ − j)·e₁h + 1`.

DEPENDS: H.01, H.02.

**⚠ WHY CLAUSE (ii) IS STATED AT ALL** (blueprint). Because it is the *coincidence* that hid the
defect. Every machine row of `EFF.GENHN` has `f₁ = 1`, so no run could distinguish the sealed
`S = e₁h`-node from the `[r1]`-corrected `D′h = e₁f₁h`-node; landing the specialization as a
**theorem** makes the coincidence explicit and prevents a future node from "simplifying"
`keyDeg * h` to `e₁ * h` in the definition. Same discipline as H.02's transcription-fidelity note;
same trap as the G.23 refutation (checks at `q = 2` only) and as HE6's F-1.

SOURCE: `EFF.GENHN.09`'s protection sentence, verbatim: *"every pin the note's laws consume sits
in that domain (the stage-initial node floor `{dv(A_j) ≥ (μ−j)D′h + 1}` and the refine floors)"*;
`EFF.GENHN.08`'s `[r1]` bracket for clause (ii): *"the two agree exactly at `f₁ = 1`, which is
every battery row and every first-live case"*.

TEETH: `GN-T-NODE` (`EFF.GENHN.08`, planted mutant, fired 1/1: "E3 construction `a₀₀` floor
off-by-one must break the volume") — discharged for clause (i) as **Lean theorem**.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.08(i).** The stage-initial node floor at any coordinate `j < μ` lies strictly above
the key-degree height `D′h = keyDeg · h`. Consequently every node floor is inside the terminal
`D′h < m` domain of the occupied-height clause (H.07/H.10). -/
theorem GenreDatum.keyDeg_mul_h_lt_nodeHeight (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.keyDeg * G.h < G.nodeHeight j := by
  have hpos : 0 < G.μ - j := Nat.sub_pos_of_lt hj
  calc G.keyDeg * G.h ≤ (G.μ - j) * (G.keyDeg * G.h) := Nat.le_mul_of_pos_left _ hpos
    _ = (G.μ - j) * G.keyDeg * G.h := (Nat.mul_assoc _ _ _).symm
    _ < (G.μ - j) * G.keyDeg * G.h + 1 := Nat.lt_succ_self _
    _ = G.nodeHeight j := rfl

/-- **NODE H.08(ii).** At `f₁ = 1` the `[r1]`-corrected `D′h`-node coincides with the sealed
`S = e₁h`-node: `nodeHeight G j = (μ − j)·e₁·h + 1`. This is *every* battery row and every
first-live case — hence the coincidence that hid the pre-`[r1]` defect. -/
theorem GenreDatum.nodeHeight_of_f_one (G : GenreDatum) (hf : G.f₁ = 1) (j : ℕ) :
    G.nodeHeight j = (G.μ - j) * G.e₁ * G.h + 1 := by
  simp only [GenreDatum.nodeHeight, GenreDatum.keyDeg, hf, Nat.mul_one]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.GenreDatum.keyDeg_mul_h_lt_nodeHeight
#print axioms Uniformity.Density.Induction.GenreDatum.nodeHeight_of_f_one

end AxCheck
