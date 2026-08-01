/-
BP_IV §1.4 — Step 17, the D-11 M1 unconditional layer + M3 glue (`MassId.lean`).
Units landed in this file so far: M0a (`BlockStrata` carrier), M0b
(`BlockCountLaws` named row).
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

/-!
# The named count-law row [BP_IV division, unit M0b]

**PROVENANCE (unit M0b; BP_IV §1.4).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.4 (statement transcribed VERBATIM).
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §1.
* [M]-hypothesis discipline: this is a NAMED `Prop` row — explicit count
  hypotheses, no axiom, and no claim of unconditionality. Downstream M1
  specializations bind it as `(hB : BlockCountLaws B)`.
-/

/-- The hard counting content is an explicit named row, not data smuggled into
`BlockStrata`. Constructors for this row must be derived from the imported O-12
base before any M1 specialization is called unconditional. -/
structure BlockCountLaws {E e q₀ : ℕ} (B : BlockStrata E e q₀) : Prop where
  cell_pos : 0 < B.cellCount
  descent_law : B.descentCount * q₀ ^ E = B.cellCount
  center_law : B.centerCount = q₀
  o1_law : B.o1Count * q₀ ^ E = B.cellCount * q₀

end LeanUrat.Scaffold.ValueSide
