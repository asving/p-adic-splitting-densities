/-
BP_IV §1.4 — Step 17, the D-11 M1 unconditional layer + M3 glue (`MassId.lean`).
Units landed in this file so far: M0a (`BlockStrata` carrier).
-/
import Mathlib

/-!
# The one-step block carrier [BP_IV division, unit M0a]

**PROVENANCE (unit M0a; BP_IV §1.4).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.4 (statement transcribed VERBATIM).
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §1.
* Counts and indices only — NO mathematical laws. The counting content lives in
  the named `BlockCountLaws` row (unit M0b), never as data smuggled into this
  carrier.
-/

namespace LeanUrat.Scaffold.ValueSide

/-- The one-step block carrier contains objects and counts only. -/
structure BlockStrata (E e : ℕ) (q₀ : ℕ) where
  hq : 2 ≤ q₀
  hEe : e ≤ E
  descentCount : ℕ
  cellCount : ℕ
  centerCount : ℕ
  o1Count : ℕ

end LeanUrat.Scaffold.ValueSide
