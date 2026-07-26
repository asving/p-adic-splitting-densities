import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **Generic localization-existence lemma** (MANIFEST `L2_loc_exists`). For any submonoid `M` of
the graded ring `S.Gr` (under the `GradedRingStr` ring structure), a commutative-ring localization
of `S.Gr` at `M` exists — the canonical mathlib witness `Localization M`.

SCOPE / AUDIT NOTE: this is ONLY the generic existence of *some* localization at an arbitrary
submonoid. It must **NOT** be cited as the full §B2-DEF D.1(d) homogeneous faithful-localization
theorem (the genuine homogeneous localization at `⟨U ∪ {Y}⟩` with its degree-0 / degree-1 and
faithfulness content). Those are separate MANIFEST units (`L2_degZero_subring`, `L2_homMon_homogeneous`,
`L2_coeffLoc`, and the L3 iso units). -/
theorem L2_loc_exists (S : SideVal p) (Rg : GradedRingStr S) (M : letI := Rg.ring; Submonoid S.Gr) : letI := Rg.ring; ∃ (L : Type) (_ : CommRing L) (_ : Algebra S.Gr L), IsLocalization M L := by
  letI := Rg.ring
  exact ⟨Localization M, inferInstance, inferInstance, Localization.isLocalization⟩
