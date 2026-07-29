/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D6 `cfw_canonical` [hard] — `ClassFiberWelldef` from RUN-KEY + ETA-LOC
(W4-3(c)): hkey equates every jet's top stratum with the representative's membership
event; heta equates the membership events across one class. PROVED. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem cfw_canonical {P : Shape n} (T : TreeModel p F n N m pol)
    (hkey : RunKey T P) (heta : EtaLoc T P) :
    ClassFiberWelldef p F n N m pol P := by
  intro H H' hH hH' heq J J'
  -- the shared class index: H's η-datum, witnessed by H itself
  set i : PrefIdx n pol P := ⟨etaData (P : ShapePrefix) H, ⟨H, hH, rfl⟩⟩ with hidef
  have hsc : SameClass i H := rfl
  have hsc' : SameClass i H' := by
    show etaData (P : ShapePrefix) H' = i.1
    rw [hidef]
    exact heq.symm
  ext x
  constructor
  · intro hx
    have h1 : T.mem (some H) x := (hkey H hH x J).mp hx
    have h2 : T.mem (some (reprOf i)) x := (heta i H hH hsc x).mp h1
    have h3 : T.mem (some H') x := (heta i H' hH' hsc' x).mpr h2
    exact (hkey H' hH' x J').mpr h3
  · intro hx
    have h1 : T.mem (some H') x := (hkey H' hH' x J').mp hx
    have h2 : T.mem (some (reprOf i)) x := (heta i H' hH' hsc' x).mp h1
    have h3 : T.mem (some H) x := (heta i H hH hsc x).mpr h2
    exact (hkey H hH x J).mpr h3

end LeanUrat.MovesT
