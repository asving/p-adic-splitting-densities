/- TSTK probe (2026-08-28) — the depth-three keyAt `rfl` kernel trap.

FINDING (recorded in C136t.lean at `s2DepthThreeKeyAt_two`): for
`k i := if i ≤ 2 then s2DepthTwoKeyAt h2 hq i else g8 h2 hq` (and likewise for an
`if i = 3` guard), the pin `k 2 = s2DepthTwoKeyAt h2 hq 2 := rfl` elaborates but the
KERNEL check hits a deterministic timeout: lazy-delta unfolds both sides to `ite`s with
UNEQUAL branch arguments (`g8` vs the landed key definitions) and compares those
argument-wise — descending into `composedKey`/`Polynomial` internals — before falling
back to proper whnf.  The `k 1 = frame key` and `k 3 = g8` pins (whose RHS never exposes
a competing `ite`) are fine as `rfl`.

FIX (production, C136t.lean): prove the level-2 pin by `show`-normalizing to the `ite`
and rewriting with `if_pos` — kernel-cheap, no cross-branch defeq. -/
import Uniformity.ChapC.C130pk
import Uniformity.ChapC.C132rp10b
import Uniformity.ChapC.C132kp3

namespace TSTKProbe

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132rp10b

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

noncomputable def kA (i : ℕ) : Polynomial O :=
  if i ≤ 2 then s2DepthTwoKeyAt h2 hq i else g8 h2 hq

-- the production fix: `show` + `if_pos`, kernel-cheap
example : kA h2 hq 2 = s2DepthTwoKeyAt h2 hq 2 := by
  show (if (2 : ℕ) ≤ 2 then s2DepthTwoKeyAt h2 hq 2 else g8 h2 hq) = s2DepthTwoKeyAt h2 hq 2
  rw [if_pos (by norm_num)]

-- the safe rfl shapes
example : kA h2 hq 1 = (s2Frame h2 hq).key := rfl
example : kA h2 hq 3 = g8 h2 hq := rfl

-- KERNEL-TIMEOUT witness, kept as a comment (do not re-enable):
-- example : kA h2 hq 2 = s2DepthTwoKeyAt h2 hq 2 := rfl

end TSTKProbe
