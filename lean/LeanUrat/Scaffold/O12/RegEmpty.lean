/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Family

/-!
# Scaffold/O12/RegEmpty — Theorem 3, Corollary D at 𝔅_n, InstancePin seam [BP_II units II-G1..G7]

Movement II (REG-p)-emptiness layer (blueprint `lean/blueprints/BP_II.md` §1.4;
source of mathematical truth: the verified leaf
`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`).

This file carries **unit II-G1**: `BnMember.toAbs`, packaging a 𝔅_n member as the
landed abstract solve table (`AbsSolveTable`, `MovesU/O12PoleFree.lean` §1), against
which the landed pole-free theorem `AbsSolveTable.regAt_primePow` fires.
Units II-G2..G7 extend this module.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)

/-- Package a 𝔅_n member as the landed abstract solve table (O12PoleFree.lean §1). -/
noncomputable def BnMember.toAbs {n : ℕ} (T : BnMember n) : AbsSolveTable where
  nBlocks := n + 1
  Phi     := fun e => T.booking.Phi e
  entries := fun e => T.entries e

end LeanUrat.Scaffold
