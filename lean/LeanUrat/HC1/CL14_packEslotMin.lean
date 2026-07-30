/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL14_packEslotMin — the repaired LST leg (i-b) at `packE`, unfolded (BP5 CL-14)

**Unit CL-14** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4 —
"repaired (i-b) at packE (the transport)", THE RISK STEP of the R6 closure).

**Informal statement.** Leg (i-b) of the CL-06-ratified `LSTStmt'` (VARIANT A of
display (6): the reinstated T4/C1 hypothesis row `hfin` + `hsupp`), instantiated at
the graded-expansion pack `packE T rl` (display (8)): for a block-b-supported,
finitely supported digit assignment `y` whose expansion slot coefficient is nonzero,
some coordinate `c₀` attains the expansion's weight — `y c₀ ≠ 0`,
`wE (packE.slotCoeff b y) = ht c₀`, and `∀ c, y c ≠ 0 → ht c₀ ≤ ht c`.

**Proof sketch (blueprint §3.2, the two-level argument).** Let γ̂ := wE(E) be the
least populated level of `E := packE.slotCoeff b y`. `inγ_detects` gives the
component at γ̂ nonzero, i.e. `T.inGr γ̂ (T.slotCoeff b (y↾lvl b γ̂)) ≠ 0`, so the
restricted polynomial is ≠ 0; `T4_slotMinHt` on the restriction (finitely supported —
`levelSet_finite'`; all support at height γ̂) yields `c₀` with `y c₀ ≠ 0` and
`ht c₀ = γ̂`. Minimality: for `y c ≠ 0` with `γ := ht c < γ̂`, the component at γ is 0
(below the least populated level); but LVL-DET (display (9), unit CL-13; `c` sits in
`levelSet b (ht c)` via `hsupp`) would force it nonzero — contradiction; hence no
support below γ̂. NCL gate: the countermodel-first unit CL-10 MUST complete before
the CL-11/CL-12/CL-13 spine this proof consumes (risk R-1).

**Deps.** CL-06 (Q-3 ADJUDICATED: VARIANT A — the ratified hypothesis row is baked
into this statement as `hfin` + `hsupp`, so this unit does NOT wait on the R1 file
edit); CL-13 (LVL-DET) → CL-12 (NCL) → CL-11/CL-27 → CL-10 (proof-side spine);
`T4_slotMinHt`, `T7_alphabetSpan.levelSet_finite'` (PROVED Lean-core at HEAD);
CL-08/CL-09 enter only at the CL-19 fold-back, not here. Per the blueprint's
bookkeeping note: with VARIANT A ratified, `hfin` is available and may go UNUSED in
this instance's proof (per-level restrictions are automatically finite).

**E-PHASE RESOLUTIONS RECORDED (statement-fence discipline).**
* CL-09's `packE` (blueprint display (8)) has NOT landed at HEAD (sibling cluster),
  and this writer may not create it (collision risk) nor edit existing files. The
  unit is therefore stated as the DEFINITIONAL UNFOLDING of the leg at `packE T rl`
  in tower vocabulary, per the display-(8) field values:
  `packE.slotCoeff _ b y`'s γ-component ↦
  `T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then y c else 0))`;
  `packE.ht _ ↦ T.ht`; `packE.blk _ ↦ T.blk`; `packE.window _ _ ↦ True` (the leg's
  window hypothesis is trivially discharged and hence dropped).
* `packE.slotCoeff b y ≠ 0` (a `LatticeExp` subtype element) unfolds to the
  ∃-component form `hne` (Subtype.ext + funext — mechanical).
* The conclusion `packE.G.w (packE.slotCoeff b y) = (T.ht c₀ : WithTop ℚ)` — `wE` is
  CL-08's least-populated-level weight — unfolds to its spec characterization: the
  component at `T.ht c₀` is nonzero AND every component strictly below vanishes.
  This pins `wE = ht c₀` for ANY implementation of the least populated level
  (`Nat.find` or the R-8 `sInf` fallback), given CL-07's LAT (`ht c₀` lies on the
  nonneg `(1/strTop)·ℕ` lattice). Fold-back to the literal pack leg = CL-19 glue via
  CL-08's `wE` spec; `rl` does not occur in the unfolded leg and is omitted.

difficulty: hard-fable. Size: ~100. PERMITTED OUTCOME: BLOCKED-with-artifact
(never a forced proof); an NCL countermodel at CL-10 escalates R6 per risk R-1.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped Classical

/-- **CL-14** — the repaired (i-b) at `packE T rl`, unfolded to tower vocabulary
(see the module docstring's E-phase resolutions): block-b-supported `y` (the
CL-06-ratified VARIANT-A row `hfin` + `hsupp`) with a nonzero graded expansion
(`hne`, the ∃-component form of `packE.slotCoeff b y ≠ 0`) attains its expansion
weight at a support coordinate `c₀` of minimal height — the middle conjunct is
`wE (packE.slotCoeff b y) = ht c₀` unfolded through the least-populated-level
characterization (nonzero component AT `ht c₀`, zero components strictly BELOW). -/
theorem CL14_packE_ib {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hfin : (Function.support y).Finite)
    (hsupp : ∀ c : T.Coord, y c ≠ 0 → T.blk c = b)
    (hne : ∃ γ : ℚ,
      T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then y c else 0)) ≠ 0) :
    ∃ c₀ : T.Coord, y c₀ ≠ 0 ∧
      (T.inGr (T.ht c₀) (T.slotCoeff b
          (fun c => if c ∈ T.levelSet b (T.ht c₀) then y c else 0)) ≠ 0 ∧
        ∀ γ : ℚ, γ < T.ht c₀ →
          T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then y c else 0)) = 0) ∧
      ∀ c : T.Coord, y c ≠ 0 → T.ht c₀ ≤ T.ht c := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL14_packE_ib
