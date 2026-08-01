/-
BP_IV §1.4 — Step 17, the D-11 M1 unconditional layer + M3 glue (`MassId.lean`).
Units landed in this file so far: M0a (`BlockStrata` carrier), M0b
(`BlockCountLaws` named row), M1a (`kernel_O1_mass`, conditional on the M0b
row), M3' (`perVisit_margin` + `perBlock_exit`), M1c (`kernel_O3_resummed`).
-/
import Mathlib

open Filter Topology
open scoped NNReal

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

/-!
# (O1) kernel value IS the continuation mass [BP_IV division, unit M1a]

**PROVENANCE (unit M1a; BP_IV §1.4).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.4 (statement transcribed VERBATIM).
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2 (a) (O1).
* CONDITIONAL on the named `BlockCountLaws` row (unit M0b), bound as
  `(hB : BlockCountLaws B)` — never call this unconditional until O-12-derived
  constructors for that row have landed. Field algebra from the row only.
-/

/-- M1a ((O1) kernel value IS the continuation mass): K_e(q₀) = q₀^{1−E} as the
    exact count ratio of the displayed event. -/
theorem kernel_O1_mass {E e q₀ : ℕ} (B : BlockStrata E e q₀)
    (hB : BlockCountLaws B) :
    (B.o1Count : ℚ) / B.cellCount = (q₀ : ℚ) ^ (1 - (E : ℤ)) := by
  have hq2 : 2 ≤ q₀ := B.hq
  have hq0 : (q₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcell : (B.cellCount : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.cell_pos.ne'
  have hqE : ((q₀ : ℚ) ^ E) ≠ 0 := pow_ne_zero _ hq0
  have hlaw : (B.o1Count : ℚ) * (q₀ : ℚ) ^ E = (B.cellCount : ℚ) * q₀ := by
    exact_mod_cast hB.o1_law
  rw [zpow_sub₀ hq0, zpow_one, zpow_natCast, div_eq_div_iff hcell hqE, hlaw]
  ring

/-!
# The per-visit termination margin [BP_IV division, unit M3']

**PROVENANCE (unit M3'; BP_IV §1.4).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.4 (statements transcribed VERBATIM).
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2 (c), the
  per-block half.
* Unconditional (no [M]-rows): pure inequalities/limits in `ℝ≥0` from
  `2 ≤ q₀` and `2 ≤ E`; geometric `Tendsto` per the corpus pattern
  `tendsto_envBound_zero` (`OM/SeriesAssembly.lean`).
-/

/-- M3' (per-visit termination margin, M1(c)'s per-block half): the continuation
    mass is κ₀ + κ₁ = q₀^{1−E} ≤ 1/2, and k-step survival ≤ 2^{−k} → 0. -/
theorem perVisit_margin {E q₀ : ℕ} (hq : 2 ≤ q₀) (hE : 2 ≤ E) :
    ((q₀ : ℝ≥0) ^ (E - 1))⁻¹ ≤ 1 / 2 := by
  have hq' : (2 : ℝ≥0) ≤ (q₀ : ℝ≥0) := by exact_mod_cast hq
  have h2 : (2 : ℝ≥0) ≤ (q₀ : ℝ≥0) ^ (E - 1) := by
    calc (2 : ℝ≥0) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ≥0) ^ (E - 1) := pow_le_pow_right₀ one_le_two (by omega)
      _ ≤ (q₀ : ℝ≥0) ^ (E - 1) := pow_le_pow_left₀ (by positivity) hq' _
  rw [one_div]
  exact inv_anti₀ (by norm_num) h2

/-- M3' second half: k-step survival at the ≤ 1/2 margin is geometric, so it
    tends to 0 (pattern: `tendsto_envBound_zero`). -/
theorem perBlock_exit {E q₀ : ℕ} (hq : 2 ≤ q₀) (hE : 2 ≤ E) :
    Tendsto (fun k => (((q₀ : ℝ≥0) ^ (E - 1))⁻¹) ^ k) atTop (nhds 0) := by
  have h2 : (2 : ℝ≥0) ≤ (q₀ : ℝ≥0) ^ (E - 1) := by
    calc (2 : ℝ≥0) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ≥0) ^ (E - 1) := pow_le_pow_right₀ one_le_two (by omega)
      _ ≤ (q₀ : ℝ≥0) ^ (E - 1) := pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast hq) _
  have hlt : (((q₀ : ℝ≥0) ^ (E - 1))⁻¹) < 1 :=
    inv_lt_one_of_one_lt₀ (lt_of_lt_of_le one_lt_two h2)
  exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt

/-!
# (O3) resummation [BP_IV division, unit M1c]

**PROVENANCE (unit M1c; BP_IV §1.4).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.4 (statement transcribed VERBATIM).
* Math source of record: D11 §2 (a) (O3).
* Proof note: the geometric resummation over ℝ≥0 is Mathlib's NNReal-native
  `NNReal.tsum_geometric` (the ℝ≥0 form of the blueprint's
  `tsum_geometric_of_lt_one`), with κ₀ = q₀^{−E} < 1 from q₀ ≥ 2, E ≥ 1.
  No `sorry`; no dependencies on the M0 rows.
-/

/-- M1c ((O3) resummation): Σ_{L≥1} κ₀^{L−1}·κ₁ = κ₁/(1−κ₀) = (q₀−1)/(q₀^E−1),
    κ₀ = q₀^{−E}, κ₁ = (q₀−1)q₀^{−E} — `tsum_geometric_of_lt_one` over ℝ≥0,
    with κ₀ < 1 from q₀ ≥ 2. -/
theorem kernel_O3_resummed {E q₀ : ℕ} (hq : 2 ≤ q₀) (hE : 1 ≤ E) :
    ∑' L : ℕ, ((q₀ : ℝ≥0) ^ E)⁻¹ ^ L * ((q₀ - 1) * ((q₀ : ℝ≥0) ^ E)⁻¹)
      = ((q₀ : ℝ≥0) - 1) / ((q₀ : ℝ≥0) ^ E - 1) := by
  have hq1 : (1 : ℝ≥0) < (q₀ : ℝ≥0) := by
    have h2 : (1 : ℝ≥0) < 2 := one_lt_two
    exact h2.trans_le (by exact_mod_cast hq)
  have hqE : (1 : ℝ≥0) < (q₀ : ℝ≥0) ^ E := one_lt_pow₀ hq1 (by omega)
  have hq0 : ((q₀ : ℝ≥0) ^ E) ≠ 0 := (zero_lt_one.trans hqE).ne'
  have hr : ((q₀ : ℝ≥0) ^ E)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact hqE
  have hsum : Summable fun L : ℕ => ((q₀ : ℝ≥0) ^ E)⁻¹ ^ L :=
    NNReal.summable_geometric hr
  rw [hsum.tsum_mul_right, NNReal.tsum_geometric hr]
  have h1 : (1 : ℝ≥0) - ((q₀ : ℝ≥0) ^ E)⁻¹
      = ((q₀ : ℝ≥0) ^ E - 1) / (q₀ : ℝ≥0) ^ E := by
    rw [div_eq_mul_inv, tsub_mul, mul_inv_cancel₀ hq0, one_mul]
  rw [h1, inv_div, div_eq_mul_inv, div_eq_mul_inv,
    mul_comm ((q₀ : ℝ≥0) - 1) (((q₀ : ℝ≥0) ^ E)⁻¹),
    mul_mul_mul_comm, mul_inv_cancel₀ hq0, one_mul,
    mul_comm (((q₀ : ℝ≥0) ^ E - 1))⁻¹ ((q₀ : ℝ≥0) - 1)]

end LeanUrat.Scaffold.ValueSide
