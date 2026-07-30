/-
Kernels/KC5 — BP4-c5 E-phase skeleton for unit KC5: the HMC reduction
assembly `hmc_of_domProj_markCompose`
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.C + §4 KC5; F9 disposition
binding; adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

HONEST STATUS (REV 2, F9 — quoted from the blueprint, binding): with KC3's
bare-implication `MarkCompose` and KC2b's `DomProj`, this theorem is
DEFINITIONAL ASSEMBLY (Iff.intro of the two named directions), NOT a depth
reduction.  Its value is (i) the NAMING of the two directions as separately
attackable laws, (ii) the typing (retained-state matching + Hpt append via
the V4 cast toolkit, carried inside the two defs), and (iii) the instance
checks that give the pair content.  Per R5 it SHIPS ONLY together with its
two content guards: KC4 `markCompose_fails_at_toy` (Kernels/HmcReduction.lean
— the pair is not True-everywhere) and KC6's Order0Sys instances
(Kernels/KC6.lean — the pair is not False-everywhere).  NOTHING here asserts
HMC unconditionally (risk R9).

GATE SEQUENCING (REV 2, F5): KC4 is the CM gate of this unit and is
SEQUENCED FIRST; it lives in the imported Kernels/HmcReduction.lean.

deps: KC3 (`MarkCompose`, imported), KC4 (CM gate, same import), KC2b
(`DomProj`, imported).  difficulty: routine-opus given the defs, ~30 ln.

Build: cd lean && lake build LeanUrat.Kernels.KC5
-/
import LeanUrat.Kernels.HmcReduction
import LeanUrat.Kernels.KC2b

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesV

/-- KC5 — `hmc_of_domProj_markCompose`: DomProj ∧ MarkCompose ⟹ HMC.
The two named directional laws assemble to the open kernel's iff: for every
step/template/height instance, `Iff.intro` of the DomProj instance (the ⊆/
projection leg) and the MarkCompose instance (the ⊇/composition leg).
Sketch: intro the HMC quantifiers; exact ⟨fun h => hproj … h, fun h =>
hcomp … h⟩ (modulo the implicit-binder instantiations).  Ships only with
the KC4/KC6 content guards — see the file header. -/
theorem hmc_of_domProj_markCompose {n : ℕ} {S : StepSys n}
    (TE : TmplEvents n S) (D : XHDd n S TE)
    (hproj : DomProj TE D) (hcomp : MarkCompose TE D) :
    HMC TE D := by
  sorry

end LeanUrat.Kernels
