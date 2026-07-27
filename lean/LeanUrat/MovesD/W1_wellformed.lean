/-
Unit W1′.wellformed_of_wf  (MovesD campaign, E-phase)  [REV 6: shape-internal — no member
needed; the rev-5 member-transport version is SUPERSEDED]
moves_ref: "COARSE CHAIN … deg R_anch,r ≤ n always" (L11) — over the note's shape
universe BY TYPE, unconditional.
deps: Defs.
sketch: induction down the reads on the CERTIFICATE P.2: root — ℓ₀ ≤ s0+wSide ≤ n
(root_box); step — ℓ_{r+1} ≤ s0'+wSide' ≤ μ_r (window) ≤ ℓ_r (gmu, g ≥ 1).
difficulty: easy-medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {n : ℕ}

/-- Wellformedness holds unconditionally over the subtype (ℓ_r ≤ n at every read).

Downward chain on the certificate `P.2`: at the root `ℓ₀ ≤ s0₀+wSide₀ ≤ n` (`root_box`);
at a step `ℓ_{r+1} ≤ s0'+wSide' ≤ μ_r ≤ g_r·μ_r ≤ ℓ_r` (`window`, `gmu`, `g ≥ 1`), so
`ℓ_{r+1} ≤ ℓ_r`, and the bound `ℓ_r ≤ n` propagates by induction on `r`. Throughout,
`ℓ_r = wSide_r / e_r ≤ wSide_r` (`Nat.div_le_self`). -/
theorem wellformed_of_wf (P : Shape n) : (P : ShapePrefix).Wellformed n := by
  intro r
  induction r with
  | zero =>
    intro hr
    have h1 : ((P : ShapePrefix).reads[0]'hr).len ≤ ((P : ShapePrefix).reads[0]'hr).wSide :=
      Nat.div_le_self _ _
    have h2 := P.2.root_box hr
    omega
  | succ k ih =>
    intro hr
    have hk : k < (P : ShapePrefix).reads.length := by omega
    have hlen_k := ih hk
    have hwin : ((P : ShapePrefix).reads[k+1]'hr).s0 + ((P : ShapePrefix).reads[k+1]'hr).wSide
        ≤ ((P : ShapePrefix).reads[k]'hk).μ := P.2.window k hr
    have hgmu := P.2.gmu k hk
    have hg : 1 ≤ ((P : ShapePrefix).reads[k]'hk).g := ((P : ShapePrefix).reads[k]'hk).hg
    have hmul : ((P : ShapePrefix).reads[k]'hk).μ
        ≤ ((P : ShapePrefix).reads[k]'hk).g * ((P : ShapePrefix).reads[k]'hk).μ :=
      Nat.le_mul_of_pos_left _ hg
    have h1 : ((P : ShapePrefix).reads[k+1]'hr).len ≤ ((P : ShapePrefix).reads[k+1]'hr).wSide :=
      Nat.div_le_self _ _
    omega

end LeanUrat.MovesD
