/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.CL13_lvlDet

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

open Polynomial LeanUrat.Moves in
/-- `digLift 0 = 0` (C2_TYPa's private `digLift_zero`, copied). -/
private lemma cl14_digLift_zero {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) : T.digLift 0 = 0 := by
  rw [Tower.digLift, dif_neg]
  rintro ⟨B, hB0, -, -, hR⟩
  apply (T.stg 0).hRne B hB0
  rw [hR]
  have h0 : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ :
      ↥(T.stg 0).K) = 0 := Subtype.ext (by simp)
  rw [h0, map_zero, zero_mul]

/-- The slot coefficient of an everywhere-zero digit assignment vanishes. -/
private lemma cl14_slotCoeff_zero {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (z : T.Coord → ↥(T.stg 0).FQ)
    (hz : ∀ c, z c = 0) : T.slotCoeff b z = 0 := by
  rw [Tower.slotCoeff]
  apply finsum_mem_of_eqOn_zero
  intro c _
  show T.digLift (z c) * T.mono c = (0 : Polynomial ℤ_[p])
  rw [hz c, cl14_digLift_zero T, zero_mul]

/-- The class `[f]` in the degree-`m` piece vanishes iff `f` has strictly higher weight
(T6's private `mk_eq_zero_iff`, copied). -/
private lemma cl14_mk_eq_zero_iff {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (m : ℤ) (f : Polynomial ℤ_[p]) (hf : f ∈ T.side.ge m) :
    (Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge m) : T.side.grPiece m) = 0
      ↔ (↑m : WithTop ℤ) < T.side.w f := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- `inGr γ 0 = 0` (both branches of the class map send `0` to `0`). -/
private lemma cl14_inGr_zero {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (γ : ℚ) : T.inGr γ (0 : Polynomial ℤ_[p]) = 0 := by
  by_cases h : T.onLattice γ ∧ ((⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) ≤ T.side.w 0)
  · rw [Tower.inGr, dif_pos h]
    exact (cl14_mk_eq_zero_iff T _ 0 h.2).mpr
      (by rw [T.side.w_zero]; exact WithTop.coe_lt_top _)
  · rw [Tower.inGr, dif_neg h]

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
  classical
  -- 1. the support is nonempty (a nonzero component forces a support coordinate)
  have hsuppne : ∃ c : T.Coord, y c ≠ 0 := by
    obtain ⟨γ₁, hγ₁⟩ := hne
    by_contra hall
    have hall' : ∀ c : T.Coord, y c = 0 := fun c => by
      by_contra hyc
      exact hall ⟨c, hyc⟩
    apply hγ₁
    have hz : ∀ c : T.Coord, (if c ∈ T.levelSet b γ₁ then y c else 0) = 0 := by
      intro c
      by_cases hc : c ∈ T.levelSet b γ₁
      · simp [hc, hall' c]
      · simp [hc]
    rw [cl14_slotCoeff_zero T b _ hz, cl14_inGr_zero T γ₁]
  obtain ⟨c₁, hc₁⟩ := hsuppne
  -- 2. pick a support coordinate of minimal height (VARIANT A's hfin is consumed here)
  set S : Finset T.Coord := hfin.toFinset with hSdef
  have hmemS : ∀ c, c ∈ S ↔ y c ≠ 0 := by
    intro c
    rw [hSdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hSne : S.Nonempty := ⟨c₁, (hmemS c₁).mpr hc₁⟩
  obtain ⟨c₀, hc₀S, hmin⟩ := S.exists_min_image (fun c => T.ht c) hSne
  have hc₀ne : y c₀ ≠ 0 := (hmemS c₀).mp hc₀S
  have hminS : ∀ c : T.Coord, y c ≠ 0 → T.ht c₀ ≤ T.ht c :=
    fun c hc => hmin c ((hmemS c).mpr hc)
  refine ⟨c₀, hc₀ne, ⟨?_, ?_⟩, hminS⟩
  -- 3a. the component AT ht c₀ is detected: LVL-DET (CL-13) on the γ̂-restriction
  · apply CL13_lvlDet T b (T.ht c₀)
    · refine ⟨c₀, ?_⟩
      have hmem : c₀ ∈ T.levelSet b (T.ht c₀) := ⟨hsupp c₀ hc₀ne, rfl⟩
      simpa [hmem] using hc₀ne
    · intro c hc
      by_cases hcl : c ∈ T.levelSet b (T.ht c₀)
      · exact hcl
      · simp [hcl] at hc
  -- 3b. every component STRICTLY BELOW vanishes: no support below the minimal height
  · intro γ hγ
    have hz : ∀ c : T.Coord, (if c ∈ T.levelSet b γ then y c else 0) = 0 := by
      intro c
      by_cases hcl : c ∈ T.levelSet b γ
      · have hy0 : y c = 0 := by
          by_contra hyc
          have hge := hminS c hyc
          rw [hcl.2] at hge
          exact absurd (lt_of_lt_of_le hγ hge) (lt_irrefl _)
        simp [hcl, hy0]
      · simp [hcl]
    rw [cl14_slotCoeff_zero T b _ hz, cl14_inGr_zero T γ]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL14_packE_ib
