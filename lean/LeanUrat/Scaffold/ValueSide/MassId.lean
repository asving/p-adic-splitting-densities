/-
BP_IV §1.4 — Step 17, the D-11 M1 unconditional layer + M3 glue (`MassId.lean`).
Units landed in this file so far: M0a (`BlockStrata` carrier), M0b
(`BlockCountLaws` named row), M1a (`kernel_O1_mass`, conditional on the M0b
row), M1b (`kernel_O2_mass`, conditional on the M0b row), M3'
(`perVisit_margin` + `perBlock_exit`), M1c (`kernel_O3_resummed`), M2
(`RowPartition` named row + `row_sum_one`), M5 (`PattStrata` carrier +
`PattCountLaws` named row + `divisorPattern_mass`, conditional on M0b + the
F(ii) row), M8 (`alpha2` datum + `alpha2StrataMass` + `alpha2Row_gate`, the
M1′ gate object — OPTIONAL unit, unconditional value-level arithmetic), M6a
(`PolyCellStrata` carrier + `PolyCellCountLaws` named row +
`polygonCell_mass`, conditional on M0b + the L6a row; the affine-cone
geometric sum is unit M6b, serial after this one), M6b (`tsum_pi_fin_prod`
Fubini engine + `coneSum_eq_prod_geometric`, unconditional).

M4 (`r1_margin_of_regP`) LANDED at REVISION 3: the §1.4 display's
`RatFunc.eval (q₀ : ℚ) (D.detFull e)` was ILL-TYPED (Mathlib's `RatFunc.eval`
takes the coefficient ring hom FIRST: `eval (f : K →+* L) (a : L)`); the
repaired statement inserts `(RingHom.id ℚ)` — the exact corpus spelling of
`RegP.detFull_clause` (`MovesU/RegPFinite.lean`), of which the unit is now
the (r1)-projection.  See the M4 section at the end of this file + BP_IV
REVISION 3.

BLOCKED(M7), REVISION-3 disposition: `trueType_const_on_cylinder` (§1.4 M3
glue) STILL does not land here.  Its BP_IV-owned event carriers `CylEvent` /
`IsContinuationEvent` are now landed (`ValueSide/Hyps.lean`, REVISION 3), but
the two BP_III-owned rows `ThmERow`/`D15Row` remain undeclared corpus-wide
(BP_III.md never charters them — cross-blueprint seam failure recorded in
BP_IV REVISION 3), and M7's PROOF consumes their CONTENT (the two-row
transport), so the opaque-parameter pattern that unblocked S5b/D4/K11 does
NOT apply — an opaque-row M7 would be unprovable, not honest.  M7 stays
owner-blocked; it elaborates the moment BP_III lands the rows.  Per the §4
failure protocol; no prover-side restatement.
-/
import Mathlib
-- M4 (BP_IV §3 reuse rows "RegP.detFull_ne_zero …" / "cycS_eval_pos …"):
-- the O-12/(REG-p) corpus layer, used AS IS.
import LeanUrat.MovesU.RegPFinite

open Filter Topology
open scoped NNReal ENNReal

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
# (O2)/(O2′) kernel value at c = 0 [BP_IV division, unit M1b]

**PROVENANCE (unit M1b; BP_IV §1.4 + §2 M-table).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.4 gives M1b as its docstring comment
  only (transcribed VERBATIM below); the M-table row fixes the content —
  statement "(O2) value q₀^{−E}", proof "same, c = 0", deps M0. The signature
  therefore follows unit M1a's displayed pattern with the c = 0 count: the
  (O2)/(O2′) loop-0 event ratio is `descentCount / cellCount`, whose value
  q₀^{−E} is exactly the `descent_law` field (D11 rev3 §2 (a) (O2):
  K_e(q₀) = q₀^{−E} = κ₀ = P(loop-0 | C_e), same cites as (O1), c = 0).
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2 (a) (O2).
* CONDITIONAL on the named `BlockCountLaws` row (unit M0b), bound as
  `(hB : BlockCountLaws B)` — never call this unconditional until O-12-derived
  constructors for that row have landed. Field algebra from the row only.
-/

/-- M1b ((O2)/(O2′), c = 0): K_e(q₀) = q₀^{−E}.  MECH from the same laws. -/
theorem kernel_O2_mass {E e q₀ : ℕ} (B : BlockStrata E e q₀)
    (hB : BlockCountLaws B) :
    (B.descentCount : ℚ) / B.cellCount = (q₀ : ℚ) ^ (-(E : ℤ)) := by
  have hq2 : 2 ≤ q₀ := B.hq
  have hq0 : (q₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcell : (B.cellCount : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.cell_pos.ne'
  have hqE : ((q₀ : ℚ) ^ E) ≠ 0 := pow_ne_zero _ hq0
  have hlaw : (B.descentCount : ℚ) * (q₀ : ℚ) ^ E = (B.cellCount : ℚ) := by
    exact_mod_cast hB.descent_law
  rw [zpow_neg, zpow_natCast, inv_eq_one_div, div_eq_div_iff hcell hqE, hlaw,
    one_mul]

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

/-!
# Row-sum-one over the M1(b) partition row [BP_IV division, unit M2]

**PROVENANCE (unit M2; BP_IV §1.4).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.4 (`row_sum_one` statement transcribed
  VERBATIM). The blueprint does NOT display `RowPartition` itself — it specifies
  it as "a hypothesis structure whose fields are M1(b)'s disjointness/exhaustion
  clauses (the D-11 (b) content)"; the structure below is this unit's
  transcription of that spec and is FLAGGED FOR REVIEW as a new definition.
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2 (b) (strata
  pairwise disjoint, exhausting C_e up to the displayed null set Z_e) and (d)
  (Σ = 1 from (b)'s partition + Z_e null).
* Layer convention: counting only, per the file header — the cell space of the
  one-step read of C_e is `Fin B.cellCount`, strata are their cell sets, and
  mass is count/cellCount (the corpus `TreeSeam.count_tie` convention). "Null at
  the read level" = the padding set contributes zero cells.
* [M]-hypothesis discipline: `RowPartition` is a NAMED row bound as
  `(P : RowPartition B)` — no axiom, no claim that any concrete pack's rows form
  such a partition (that is D-11's clause-4/data-pass content, OPEN; scope
  sentence of D-11 §2 (b), pass-2 P6).
-/

/-- M2's hypothesis row: a displayed one-step strata family for the block read,
    carrying M1(b)'s disjointness/exhaustion clauses (D-11 §2 (b)) at the
    counting layer. `strata` are the strata's cell sets in the level-read cell
    space `Fin B.cellCount`; `padding` is the displayed null/padding set (D-11's
    Z_e at the read level); the clauses say the strata are pairwise disjoint and
    exhaust the cell space up to `padding`, which is null (zero cells) at this
    layer; `cell_pos` is the nondegeneracy of the read (M0b's `cell_pos`,
    carried on the row so that the mass convention divides by a nonzero count). -/
structure RowPartition {E e q₀ : ℕ} (B : BlockStrata E e q₀) where
  /-- the displayed one-step strata, as their cell sets in the level-read cell
      space of C_e. -/
  strata : Finset (Finset (Fin B.cellCount))
  /-- the displayed null/padding set (D-11's Z_e read at this level). -/
  padding : Finset (Fin B.cellCount)
  /-- M1(b), disjointness clause: the displayed strata are pairwise disjoint. -/
  strata_disjoint : ∀ s ∈ strata, ∀ t ∈ strata, s ≠ t → Disjoint s t
  /-- M1(b), exhaustion clause: the strata exhaust C_e up to the padding set. -/
  strata_exhaust : strata.biUnion id ∪ padding = Finset.univ
  /-- the padding set is null at the read level (zero cells). -/
  padding_null : padding.card = 0
  /-- nondegeneracy of the read: the block cell count is positive. -/
  cell_pos : 0 < B.cellCount

/-- The row's mass column at the counting layer: count/cellCount (the corpus
    `TreeSeam.count_tie` convention — no measure theory at this layer). -/
def RowPartition.mass {E e q₀ : ℕ} {B : BlockStrata E e q₀}
    (_P : RowPartition B) (s : Finset (Fin B.cellCount)) : ℚ :=
  (s.card : ℚ) / B.cellCount

/-- M2 (row-sum-one — "Σ = 1 across each row now a THEOREM"): the one-step strata
    partition C_e up to the displayed null/padding set, so the row's mass column
    sums to 1.  Stated over a `RowPartition` hypothesis structure whose fields
    are M1(b)'s disjointness/exhaustion clauses (the D-11 (b) content). -/
theorem row_sum_one {E e q₀ : ℕ} {B : BlockStrata E e q₀} (P : RowPartition B) :
    ∑ s ∈ P.strata, P.mass s = 1 := by
  have hpad : P.padding = ∅ := Finset.card_eq_zero.mp P.padding_null
  have hunion : P.strata.biUnion id = Finset.univ := by
    have h := P.strata_exhaust
    rwa [hpad, Finset.union_empty] at h
  have hcard : ∑ s ∈ P.strata, s.card = B.cellCount := by
    calc ∑ s ∈ P.strata, s.card
        = (P.strata.biUnion id).card :=
          (Finset.card_biUnion P.strata_disjoint).symm
      _ = B.cellCount := by rw [hunion, Finset.card_univ, Fintype.card_fin]
  have hcell : (B.cellCount : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr P.cell_pos.ne'
  calc ∑ s ∈ P.strata, P.mass s
      = (∑ s ∈ P.strata, (s.card : ℚ)) / B.cellCount := by
        simp [RowPartition.mass, Finset.sum_div]
    _ = 1 := by rw [← Nat.cast_sum, hcard, div_self hcell]

/-!
# The divisor-pattern mass row, family (ii) [BP_IV division, unit M5]

**PROVENANCE (unit M5; BP_IV §2 M-table).**

* Blueprint: `lean/blueprints/BP_IV.md` §2 M-table row M5 — statement
  "divisor-pattern mass row (family (ii)): m(π)(q₀) = q₀^{−(E−e)}·N_π(q₀)·q₀^{−e}",
  proof sketch "field algebra over M0 + a `pattCount` field (Fact F(ii) as a
  law)", deps M0.  §1.4 displays no Lean signature for M5 (as for unit M1b),
  so the signature follows unit M1a's displayed count-ratio pattern with the
  M-table's factored value, transcribed with ℤ-exponents: q₀^{−(E−e)} as
  `(q₀ : ℚ) ^ (-((E : ℤ) - e))`, q₀^{−e} as `(q₀ : ℚ) ^ (-(e : ℤ))`.
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2 (a), the
  divisor-pattern bullet: m(π)(q₀) = q₀^{−(E−e)}·N_π(q₀)·q₀^{−e} =
  P(patt-π | C_e) [L2 + L3's uniform reduction + Fact F(ii): N_π(q₀) counts
  the monic h̄ of pattern π].
* [M]-hypothesis discipline: `PattStrata` carries counts only (`pattCount` =
  the Fact-F(ii) value N_π(q₀); `pattEventCount` = the patt-π continuation
  event count inside the cell).  The counting content — Fact F(ii) as a law,
  composed with L2 + L3's uniform reduction, in the count-ratio convention of
  this file — is the NAMED `Prop` row `PattCountLaws`, never data smuggled
  into the carrier and never an axiom.
* CONDITIONAL on the named rows M0b (`BlockCountLaws`, for `cell_pos`) and
  `PattCountLaws` — never call this unconditional until O-12-derived
  constructors for those rows have landed. Field algebra from the rows only.
-/

/-- M5 carrier: the divisor-pattern counts over a block carrier — objects and
counts only.  `pattCount` is the Fact-F(ii) count field N_π(q₀) (the number of
monic h̄ of pattern π); `pattEventCount` counts the displayed patt-π
continuation event inside the cell. -/
structure PattStrata {E e q₀ : ℕ} (B : BlockStrata E e q₀) where
  pattCount : ℕ
  pattEventCount : ℕ

/-- The Fact-F(ii) counting content as an explicit named row (M0b discipline):
the patt-π event count factorizes through the (E−e)-descent times the
`pattCount` monic residuals at q₀^{−e} each, in this file's count-ratio
convention.  Constructors must be derived from the imported O-12 base before
any M5 specialization is called unconditional. -/
structure PattCountLaws {E e q₀ : ℕ} {B : BlockStrata E e q₀}
    (P : PattStrata B) : Prop where
  patt_law : P.pattEventCount * q₀ ^ E = B.cellCount * P.pattCount

/-- M5 (divisor-pattern mass row, family (ii)):
m(π)(q₀) = q₀^{−(E−e)}·N_π(q₀)·q₀^{−e} as the exact count ratio of the
displayed patt-π continuation event. -/
theorem divisorPattern_mass {E e q₀ : ℕ} {B : BlockStrata E e q₀}
    (P : PattStrata B) (hB : BlockCountLaws B) (hP : PattCountLaws P) :
    (P.pattEventCount : ℚ) / B.cellCount
      = (q₀ : ℚ) ^ (-((E : ℤ) - e)) * P.pattCount * (q₀ : ℚ) ^ (-(e : ℤ)) := by
  have hq2 : 2 ≤ q₀ := B.hq
  have hq0 : (q₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcell : (B.cellCount : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.cell_pos.ne'
  have hqE : ((q₀ : ℚ) ^ E) ≠ 0 := pow_ne_zero _ hq0
  have hlaw : (P.pattEventCount : ℚ) * (q₀ : ℚ) ^ E
      = (B.cellCount : ℚ) * P.pattCount := by
    exact_mod_cast hP.patt_law
  have hcomb : (q₀ : ℚ) ^ (-((E : ℤ) - e)) * (P.pattCount : ℚ)
        * (q₀ : ℚ) ^ (-(e : ℤ))
      = (P.pattCount : ℚ) * ((q₀ : ℚ) ^ (E : ℤ))⁻¹ := by
    rw [mul_comm ((q₀ : ℚ) ^ (-((E : ℤ) - e))) (P.pattCount : ℚ), mul_assoc,
      ← zpow_add₀ hq0,
      show -((E : ℤ) - e) + -(e : ℤ) = -(E : ℤ) by ring, zpow_neg]
  rw [hcomb, zpow_natCast, ← div_eq_mul_inv, div_eq_div_iff hcell hqE, hlaw]
  ring

/-!
# The M1′ gate object — the recorded concrete α₂ row at n = 2
[BP_IV division, unit M8 — OPTIONAL]

**PROVENANCE (unit M8; BP_IV §2 M-table).**

* Blueprint: `lean/blueprints/BP_IV.md` §2 M-table row M8 — statement "M1′
  gate object (the recorded concrete α₂ row at n = 2) — OPTIONAL", proof
  sketch "one concrete Finset computation", deps M0, MECH.  §1.4 displays no
  Lean signature for M8 (as for units M1b and M5), so the signatures below
  transcribe the SOURCE displays directly (D11 rev3 §2 Proposition M1′ +
  O-12 rev4's α-identity display "1/q − q^{−3} = (q^{−1} − q^{−2}) +
  (q−1)·q^{−3}, i.e. α₂ = (0, q−1)").
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2, Proposition
  M1′: under the (O2) booking with the concrete allocation datum
  α₂ = (0, q−1) (the machine-checked degree-2 table), at e = 2 the
  α-adjusted verdict row 1/q − q^{−3} evaluates to q₀^{−1} − q₀^{−3} =
  P(descend and not (loop-0) | C_2) — the disjoint union of the two pattern
  strata (π = {(1,1),(1,1)} and {(2,1)}, TOTAL mass q₀^{−1} − q₀^{−2} by
  Fact F; the individual pattern masses are NOT recorded there and are NOT
  stated here) with the recentering stratum (κ₁ = q₀^{−2} − q₀^{−3}, the
  E = 3 block value (q₀ − 1)·q₀^{−E} of unit M1c's κ₁).
* Dep M0 reading: the gate rides the block vocabulary at the recorded
  degree-2 member (E, e) = (3, 2) — the (O2) kernel exponent is E = 3
  (κ₀ = q₀^{−3}); the `BlockStrata 3 2 q₀` binder keys the gate to that
  carrier (only its `hq` field is consumed; no count law is used or needed —
  the recorded row is value-level).
* SCOPE FENCE (D11 M1′ verbatim): this is "a gate object, not a density
  carrier" — the booked event is NOT verdict-constant (the recentering
  stratum re-enters the full state law and realizes every verdict), so the
  solved values differ from the true conditional densities.  Nothing below
  states or implies verdict-constancy or any density semantics; the unit is
  the recorded value-level arithmetic only.  For arbitrary allocation data
  the adjusted rows need not be masses at all — ONLY the recorded concrete
  choice α₂ = (0, q−1) is formalized.
-/

/-- M8 datum: the recorded concrete allocation α₂ = (0, q−1) (the
machine-checked degree-2 table's member), as the two verdict-slot values at
q.  Recorded choice only — no other allocation is formalized. -/
def alpha2 (q : ℚ) : Fin 2 → ℚ := ![0, q - 1]

/-- The allocation constraint on the recorded datum: Σ_σ α₂(σ) = q − 1
(O-12's total-added-mass display: the α-adjustments across the verdict row
add up to κ₁'s numerator q − 1). -/
theorem alpha2_sum (q : ℚ) : ∑ σ : Fin 2, alpha2 q σ = q - 1 := by
  simp [alpha2, Fin.sum_univ_two]

/-- M8 strata masses: the two RECORDED mass values of Proposition M1′'s
displayed disjoint union — slot 0 the two pattern strata's TOTAL mass
q₀^{−1} − q₀^{−2} (Fact F), slot 1 the recentering stratum
κ₁ = q₀^{−2} − q₀^{−3}. -/
def alpha2StrataMass (q₀ : ℕ) : Fin 2 → ℚ :=
  ![(q₀ : ℚ)⁻¹ - ((q₀ : ℚ) ^ 2)⁻¹, ((q₀ : ℚ) ^ 2)⁻¹ - ((q₀ : ℚ) ^ 3)⁻¹]

/-- M8 α-identity leg: the recentering stratum mass is exactly the
α₂-allocated mass at the (O2) kernel exponent E = 3 —
κ₁ = (q₀ − 1)·q₀^{−3} (O-12 rev4's display, second summand). -/
theorem alpha2_recentering {q₀ : ℕ} (B : BlockStrata 3 2 q₀) :
    alpha2StrataMass q₀ 1 = alpha2 (q₀ : ℚ) 1 * ((q₀ : ℚ) ^ 3)⁻¹ := by
  have hq0 : (q₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := B.hq; omega)
  simp only [alpha2StrataMass, alpha2]
  norm_num
  field_simp

/-- M8 (the M1′ gate object, the one concrete Finset computation): the
recorded strata masses sum to the α₂-adjusted verdict-row value
1/q − q^{−3} evaluated at q₀ — Proposition M1′'s displayed identity
q₀^{−1} − q₀^{−3} = (q₀^{−1} − q₀^{−2}) + (q₀^{−2} − q₀^{−3}). -/
theorem alpha2Row_gate {q₀ : ℕ} (_B : BlockStrata 3 2 q₀) :
    ∑ i : Fin 2, alpha2StrataMass q₀ i = (q₀ : ℚ)⁻¹ - ((q₀ : ℚ) ^ 3)⁻¹ := by
  simp only [alpha2StrataMass, Fin.sum_univ_two]
  norm_num

/-!
# The polygon-family per-cell mass leg, family (iii)
[BP_IV division, unit M6a — first half of the M6 split]

**PROVENANCE (unit M6a; BP_IV §2 M-table + §4 wave 2 split M6a → M6b).**

* Blueprint: `lean/blueprints/BP_IV.md` §2 M-table row M6 — statement
  "polygon-family cell mass (family (iii)): per-cell (1−q₀^{−1})^k·q₀^{−N(P)}
  + affine-cone geometric sum", deps M1c, src "D11 §2 (a) polygon bullet
  (L6a/L6b/L6e)".  §4 wave 2 splits M6 into the serial pair M6a → M6b:
  M6a = THIS unit, the per-cell (1−q₀^{−1})^k·q₀^{−N(P)} leg [L6a];
  M6b = the affine-cone geometric sum (L6b's exponents c_j ≥ 1, per-axis
  `tsum_geometric` + Fubini, the L6′ closed-form algebra) — NOT here.
* §1.4 displays no Lean signature for M6 (as for units M1b, M5, M8), so the
  signature follows unit M1a's displayed count-ratio pattern with the
  M-table's per-cell value, transcribed with the ℤ-exponent q₀^{−N(P)} as
  `(q₀ : ℚ) ^ (-(P.polyVol : ℤ))` and (1−q₀^{−1})^k as
  `(1 - (q₀ : ℚ)⁻¹) ^ P.unitDigits`.
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2 (a), the
  polygon bullet: "Per cell: P(cell) = (1−q₀^{−1})^k·q₀^{−N(P)} [L6a,
  exact]".  The shape-conditional factor [L6d (JC)], the cone disjointness
  [L6e(i)], and the D-11 conditional normalization q₀^{+e} all ride the M6b
  assembly, not this leg.
* [M]-hypothesis discipline: `PolyCellStrata` carries counts and indices only
  (`unitDigits` = L6a's unit-digit count k; `polyVol` = the polygon volume
  exponent N(P), left as a free index so that M6b can instantiate it along
  the affine cone N_min + Σ c_j·w_j; `polyCellCount` = the displayed polygon
  cell's count in the block read).  The counting content — L6a's exact cell
  enumeration (O-12 §8 rev 2/4), in the count-ratio convention of this file —
  is the NAMED `Prop` row `PolyCellCountLaws`, never data smuggled into the
  carrier and never an axiom.
* CONDITIONAL on the named rows M0b (`BlockCountLaws`, for `cell_pos`) and
  `PolyCellCountLaws` — never call this unconditional until O-12-derived
  constructors for those rows have landed. Field algebra from the rows only.
-/

/-- M6a carrier: the polygon-cell counts over a block carrier — objects and
counts only.  `unitDigits` is L6a's unit-digit count k (the exponent of the
(1−q₀^{−1}) factor); `polyVol` is the polygon volume exponent N(P) (a free
index here; unit M6b instantiates it along L6b's affine cone
N_min + Σ c_j·w_j); `polyCellCount` counts the displayed polygon cell in the
block read. -/
structure PolyCellStrata {E e q₀ : ℕ} (B : BlockStrata E e q₀) where
  unitDigits : ℕ
  polyVol : ℕ
  polyCellCount : ℕ

/-- The L6a counting content as an explicit named row (M0b discipline): the
displayed polygon cell counts (q₀−1)^k parts in q₀^{N(P)+k} of the block
read, in this file's count-ratio convention.  Constructors must be derived
from the imported O-12 base (§8 rev 2/4 exact enumerations) before any M6
specialization is called unconditional. -/
structure PolyCellCountLaws {E e q₀ : ℕ} {B : BlockStrata E e q₀}
    (P : PolyCellStrata B) : Prop where
  polyCell_law : P.polyCellCount * q₀ ^ (P.polyVol + P.unitDigits)
    = B.cellCount * (q₀ - 1) ^ P.unitDigits

/-- M6a (polygon-family cell mass, family (iii), per-cell leg):
P(cell) = (1−q₀^{−1})^k·q₀^{−N(P)} as the exact count ratio of the displayed
polygon cell [L6a, exact].  The affine-cone resummation over the depth cone
is unit M6b. -/
theorem polygonCell_mass {E e q₀ : ℕ} {B : BlockStrata E e q₀}
    (P : PolyCellStrata B) (hB : BlockCountLaws B) (hP : PolyCellCountLaws P) :
    (P.polyCellCount : ℚ) / B.cellCount
      = (1 - (q₀ : ℚ)⁻¹) ^ P.unitDigits * (q₀ : ℚ) ^ (-(P.polyVol : ℤ)) := by
  have hq2 : 2 ≤ q₀ := B.hq
  have hq0 : (q₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcell : (B.cellCount : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.cell_pos.ne'
  have hcast : ((q₀ - 1 : ℕ) : ℚ) = (q₀ : ℚ) - 1 :=
    Nat.cast_pred (by omega)
  have hlaw : (P.polyCellCount : ℚ) * (q₀ : ℚ) ^ (P.polyVol + P.unitDigits)
      = (B.cellCount : ℚ) * ((q₀ : ℚ) - 1) ^ P.unitDigits := by
    calc (P.polyCellCount : ℚ) * (q₀ : ℚ) ^ (P.polyVol + P.unitDigits)
        = ((P.polyCellCount * q₀ ^ (P.polyVol + P.unitDigits) : ℕ) : ℚ) := by
          push_cast; ring
      _ = ((B.cellCount * (q₀ - 1) ^ P.unitDigits : ℕ) : ℚ) := by
          rw [hP.polyCell_law]
      _ = (B.cellCount : ℚ) * ((q₀ : ℚ) - 1) ^ P.unitDigits := by
          push_cast [hcast]; ring
  have hone : (1 : ℚ) - (q₀ : ℚ)⁻¹ = ((q₀ : ℚ) - 1) / q₀ := by
    rw [sub_div, div_self hq0, one_div]
  rw [hone, div_pow, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_div,
    ← pow_add, div_eq_div_iff hcell (pow_ne_zero _ hq0),
    add_comm P.unitDigits P.polyVol, hlaw]
  ring

/-!
# The affine-cone geometric sum, family (iii)
[BP_IV division, unit M6b — second half of the M6 split]

**PROVENANCE (unit M6b; BP_IV §2 M-table + §4 wave 2 split M6a → M6b).**

* Blueprint: `lean/blueprints/BP_IV.md` §2 M-table row M6 — proof sketch
  "cone sum = product of geometric series (c_j ≥ 1); `tsum_geometric` per
  axis + Fubini for finitely many axes", deps M1c, src "D11 §2 (a) polygon
  bullet (L6a/L6b/L6e)".  §4 wave 2 splits M6 into the serial pair
  M6a → M6b: M6a = the per-cell (1−q₀^{−1})^k·q₀^{−N(P)} leg (above);
  M6b = THIS unit, the affine-cone resummation.
* §1.4 displays no Lean signature for M6 (as for units M1b, M5, M8), so the
  statement transcribes the D-11 display directly: the summand is the
  convergent geometric term q₀^{−N_min−Σ_j c_j·w_j} of the polygon bullet
  ("countable additivity along L6b's affine cone (exponents c_j ≥ 1 give
  convergent geometric sums Σ_w q₀^{−N_min−Σc_jw_j})"), i.e. M6a's free
  volume index `polyVol` instantiated along the cone as N_min + Σ c_j·w_j;
  the value is the product of the per-axis geometric series.  Carried over
  ℝ≥0 (the M1c pattern), where the equality genuinely encodes convergence
  (a non-summable ℝ≥0 `tsum` is 0, never the displayed positive product).
* Math source of record: `D11_massid_phaseB_attempt_rev3.md` §2 (a), the
  polygon bullet [L6b affine cone].  The per-cell L6a factor is unit M6a
  (above); the shape-conditional L6d factor, the L6e(i) disjointness read,
  and the q₀^{+e} normalization ride the downstream family-(iii) assembly,
  not this unit.
* Unconditional (no [M]-rows): pure geometric-series analysis from 2 ≤ q₀
  and c_j ≥ 1.  Engine: `tsum_pi_fin_prod`, the ℝ≥0∞ Fubini for finitely
  many axes (checked absent from Mathlib: loogle `∑' _ : (_ → _), ∏ _, _`
  and local search 2026-08-01 find no pi-type `tsum` factorization) —
  `ENNReal.tsum_prod'`/`ENNReal.tsum_mul_left/right` along `Fin.consEquiv`,
  per the §3 reuse row "Mathlib: `tsum_geometric_of_lt_one` (ℝ≥0),
  `ENNReal.tsum_*` | geometric resummation | M1c, M6, S1a, S4a".
-/

/-- M6b engine (Fubini for finitely many axes): over ℝ≥0∞ the `tsum` of a
product of per-axis factors over the finite-axis lattice `Fin k → ℕ`
factorizes as the product of the per-axis `tsum`s.  Unconditional in ℝ≥0∞;
induction on the axes along `Fin.consEquiv`. -/
theorem tsum_pi_fin_prod {k : ℕ} (f : Fin k → ℕ → ℝ≥0∞) :
    ∑' w : Fin k → ℕ, ∏ j, f j (w j) = ∏ j, ∑' n, f j n := by
  induction k with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact tsum_eq_single (fun i => i.elim0) fun b hb =>
        absurd (Subsingleton.elim b _) hb
  | succ k ih =>
      calc ∑' w : Fin (k + 1) → ℕ, ∏ j, f j (w j)
          = ∑' p : ℕ × (Fin k → ℕ), ∏ j, f j ((Fin.consEquiv fun _ => ℕ) p j) :=
            ((Fin.consEquiv fun _ => ℕ).tsum_eq fun w => ∏ j, f j (w j)).symm
        _ = ∑' p : ℕ × (Fin k → ℕ),
              f 0 p.1 * ∏ j : Fin k, f j.succ (p.2 j) := by
            simp [Fin.consEquiv, Fin.prod_univ_succ]
        _ = (∑' n, f 0 n) * ∑' v : Fin k → ℕ, ∏ j : Fin k, f j.succ (v j) := by
            rw [ENNReal.tsum_prod']
            simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
        _ = (∑' n, f 0 n) * ∏ j : Fin k, ∑' n, f j.succ n := by
            rw [ih]
        _ = ∏ j, ∑' n, f j n := (Fin.prod_univ_succ fun j => ∑' n, f j n).symm

/-- M6b (affine-cone geometric sum, family (iii)'s cone leg): summing the
per-cell weight q₀^{−N(P)} along L6b's affine cone N(P) = N_min + Σ_j c_j·w_j
(finitely many axes, exponents c_j ≥ 1) gives
Σ_w q₀^{−N_min−Σ_j c_j·w_j} = q₀^{−N_min}·∏_j (1 − q₀^{−c_j})^{−1} —
`tsum_geometric` per axis + Fubini (`tsum_pi_fin_prod`), convergent over ℝ≥0
since q₀ ≥ 2 and c_j ≥ 1. -/
theorem coneSum_eq_prod_geometric {k : ℕ} {q₀ : ℕ} (hq : 2 ≤ q₀)
    (Nmin : ℕ) (c : Fin k → ℕ) (hc : ∀ j, 1 ≤ c j) :
    ∑' w : Fin k → ℕ, ((q₀ : ℝ≥0) ^ (Nmin + ∑ j, c j * w j))⁻¹
      = ((q₀ : ℝ≥0) ^ Nmin)⁻¹ * ∏ j, (1 - ((q₀ : ℝ≥0) ^ c j)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ≥0) < (q₀ : ℝ≥0) := by
    have h : (1 : ℕ) < q₀ := by omega
    exact_mod_cast h
  have hpow : ∀ j : Fin k, (1 : ℝ≥0) < (q₀ : ℝ≥0) ^ c j := fun j =>
    one_lt_pow₀ hq1 (by have := hc j; omega)
  have hne : ∀ j : Fin k, ((q₀ : ℝ≥0) ^ c j) ≠ 0 := fun j =>
    (zero_lt_one.trans (hpow j)).ne'
  have hr1 : ∀ j : Fin k, ((q₀ : ℝ≥0) ^ c j)⁻¹ < 1 := fun j => by
    rw [inv_lt_one_iff₀]; right; exact hpow j
  have h1r : ∀ j : Fin k, (1 : ℝ≥0) - ((q₀ : ℝ≥0) ^ c j)⁻¹ ≠ 0 := fun j =>
    (tsub_pos_iff_lt.mpr (hr1 j)).ne'
  have hcoe : ∀ j : Fin k, ((((q₀ : ℝ≥0) ^ c j)⁻¹ : ℝ≥0) : ℝ≥0∞)
      = ((q₀ : ℝ≥0∞) ^ c j)⁻¹ := fun j => by
    rw [ENNReal.coe_inv (hne j), ENNReal.coe_pow, ENNReal.coe_natCast]
  -- split the cone exponent into the apex factor and the per-axis factors
  have hsplit : ∀ w : Fin k → ℕ,
      ((q₀ : ℝ≥0) ^ (Nmin + ∑ j, c j * w j))⁻¹
        = ((q₀ : ℝ≥0) ^ Nmin)⁻¹ * ∏ j, (((q₀ : ℝ≥0) ^ c j)⁻¹) ^ w j := by
    intro w
    rw [pow_add, mul_inv, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun j _ => by
      rw [pow_mul, inv_pow])
  rw [tsum_congr hsplit, NNReal.tsum_mul_left]
  congr 1
  -- the core cone sum, lifted to ℝ≥0∞ where Fubini is unconditional
  rw [NNReal.tsum_eq_toNNReal_tsum]
  have hlift : (∑' w : Fin k → ℕ,
        ((∏ j, (((q₀ : ℝ≥0) ^ c j)⁻¹) ^ w j : ℝ≥0) : ℝ≥0∞))
      = ∏ j, ((1 : ℝ≥0∞) - ((q₀ : ℝ≥0∞) ^ c j)⁻¹)⁻¹ := by
    calc ∑' w : Fin k → ℕ, ((∏ j, (((q₀ : ℝ≥0) ^ c j)⁻¹) ^ w j : ℝ≥0) : ℝ≥0∞)
        = ∑' w : Fin k → ℕ, ∏ j, (((q₀ : ℝ≥0∞) ^ c j)⁻¹) ^ w j := by
          refine tsum_congr fun w => ?_
          rw [ENNReal.ofNNReal_finsetProd]
          exact Finset.prod_congr rfl fun j _ => by rw [ENNReal.coe_pow, hcoe j]
      _ = ∏ j, ∑' n, (((q₀ : ℝ≥0∞) ^ c j)⁻¹) ^ n :=
          tsum_pi_fin_prod fun j n => (((q₀ : ℝ≥0∞) ^ c j)⁻¹) ^ n
      _ = ∏ j, ((1 : ℝ≥0∞) - ((q₀ : ℝ≥0∞) ^ c j)⁻¹)⁻¹ :=
          Finset.prod_congr rfl fun j _ => ENNReal.tsum_geometric _
  rw [hlift]
  -- read the finite ℝ≥0∞ product back in ℝ≥0 (each ratio < 1 by c_j ≥ 1)
  have hfac : ∀ j : Fin k, ((1 : ℝ≥0∞) - ((q₀ : ℝ≥0∞) ^ c j)⁻¹)⁻¹
      = (((1 - ((q₀ : ℝ≥0) ^ c j)⁻¹)⁻¹ : ℝ≥0) : ℝ≥0∞) := fun j => by
    rw [ENNReal.coe_inv (h1r j), ENNReal.coe_sub, ENNReal.coe_one, hcoe j]
  rw [Finset.prod_congr rfl fun j _ => hfac j, ← ENNReal.ofNNReal_finsetProd,
    ENNReal.toNNReal_coe]

/-!
# (r1) margins over the VERIFIED O-12 lemma base [BP_IV division, unit M4;
REPAIRED and PROVED at REVISION 3]

**PROVENANCE (unit M4; BP_IV §1.4 + §2 M-table row M4; REVISION 3).**

* Blueprint: §1.4's M4 display concluded
  `RatFunc.eval (q₀ : ℚ) (D.detFull e) ≠ 0` — ILL-TYPED as written: Mathlib's
  `RatFunc.eval` signature is `eval (f : K →+* L) (a : L) (p : RatFunc K)`,
  so the ring hom argument is missing (the division run's "application
  mismatch").  REVISION-3 repair: insert `(RingHom.id ℚ)` — exactly the
  corpus spelling of `RegP.detFull_clause`'s second conjunct
  (`MovesU/RegPFinite.lean`: `(D.detFull e).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0`).
* Math source of record: D11 §2 (c) (r1); the O-12 lemma base.  The corpus
  already packages M17 Lemma 0's (r1) clause per pool value (`RegP` is the
  ∀-form; `detFull_clause` its named read), so the repaired unit is the
  (r1)-projection: RegP transports the margin to every pool member — the
  §1.4 docstring's own phrase.  `cycS_eval_pos` (the §3 reuse row) lives
  UNDER `RegP` at the real instance and is not re-consumed here.
* Statement fence: repair confined to the ill-typed application; binder list
  and conclusion shape otherwise verbatim (recorded in BP_IV REVISION 3).
-/

open LeanUrat.MovesU in
/-- M4 ((r1) margins over the VERIFIED O-12 lemma base; REVISION-3 typing):
    the block determinant does not vanish at any pool value q₀ = p^δ ≥ 2 —
    packaged as: RegP transports the margin to every pool member. -/
theorem r1_margin_of_regP {p : ℕ} {D : RegData p} (h : RegP D) (e : D.Block) :
    ∀ q₀ ∈ D.Pool, (D.detFull e).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0 :=
  fun _ hq => (h.detFull_clause hq e).2

end LeanUrat.Scaffold.ValueSide
