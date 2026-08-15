/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G47

/-!
# Uniformity.ChapG.G48 — `genuineDensity_two_exact`, the `n = 2` density function

**Chapter G, NODE G.48** (`blueprint/CHAP-G_base_cases_menus.md` §7). The three exact values of
G.46 and G.47, re-keyed from the CERTIFIED density `decidedDensity` (the limit of the proportion
of level-`N` classes on which the type is already forced) to **THE** density `genuineDensity`
(the limit of the proportion of level-`N` classes merely *consistent with* the type), plus the
statement that every other type carries density `0`.

The re-keying is unconditional: the `n = 2` tie `genuineDensity_eq_decidedDensity_two` is a landed
theorem, not a hypothesis, because `drainage_two` is proved outright at `n = 2`.

DEPENDS: G.46 (`decidedDensity_two_ram_eq`), G.47 (`decidedDensity_two_inert_eq`,
`decidedDensity_two_split_eq`) · landed `genuineDensity_eq_decidedDensity_two`
(`Drainage.lean:858`), `genuineDensity_two_eq_zero` (`Drainage.lean:1037`),
`sum_three_densities_eq_one` (`Drainage.lean:1080`).

**PROOF.** Each of the first three conjuncts is `rw [genuineDensity_eq_decidedDensity_two]`
followed by the matching G.47 / G.46 value. The fourth is the landed `genuineDensity_two_eq_zero`
verbatim.

**⚠ ARITHMETIC CROSS-CHECK.** `2·q/(2(q+1)) + 1/(q+1) = q/(q+1) + 1/(q+1) = (q+1)/(q+1) = 1` ✓,
consistent with the landed `sum_three_densities_eq_one` (`genuineDensity split + inert + ram = 1`,
`Drainage.lean:1080`) — a real, if weak, check that these three values are not a transcription
slip: any single-value error would break the identity.

**TEETH.** `W11-EXHAUST` → Lean theorem; `W11-ORACLE` → executable regression
(`verification/quartic_oracle.py`, mixed characteristic only).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **THE `n = 2` DENSITY FUNCTION, EXACTLY.** Over every complete DVR with finite residue field,
both characteristics, wild residue characteristic included. -/
theorem genuineDensity_two_exact [IsAdicComplete (maximalIdeal O) O] :
    genuineDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
    ∧ (∀ σ : FactorizationType, σ ≠ splitType → σ ≠ inertType → σ ≠ ramType →
        genuineDensity O 2 σ = 0) := by
  refine ⟨?_, ?_, ?_, fun _ hs hi hr => genuineDensity_two_eq_zero hs hi hr⟩
  · rw [genuineDensity_eq_decidedDensity_two]; exact decidedDensity_two_split_eq
  · rw [genuineDensity_eq_decidedDensity_two]; exact decidedDensity_two_inert_eq
  · rw [genuineDensity_eq_decidedDensity_two]; exact decidedDensity_two_ram_eq

section AxCheck

#print axioms Uniformity.Density.genuineDensity_two_exact

end AxCheck

end Uniformity.Density
