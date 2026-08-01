/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.UniformCapstone
import LeanUrat.OM.SeriesAssembly
import LeanUrat.OM.RealInstanceV2Gates

/-!
# Scaffold/AnchorN2 — the numerics/instance anchors [wave VI-2]

Transcription of `lean/blueprints/BP_VI.md` §1.4 at REVISION 3. Anchors are
FLAGS, never substitutes (tree §0 discipline): each anchor names the EXACT
proposition its corpus gate proves and re-fires the gate's proof, so a
regression anywhere in the spine's import cone breaks a visible gate here.

REVISION-3 STATEMENT REPAIR OF RECORD (VI-N1/VI-N2/VI-N3, compile-gated): the
§1.4 Revision-2 displays wrapped proof TERMS in `Nonempty`
(`Nonempty (montes_uniform_n2 σ hσ)`, `Nonempty hExhaust_n2`,
`Nonempty gate_v2_…`) — a category error (`Nonempty : Sort u → Prop` cannot
consume a proof term), COMPILER-REFUTED at 2026-08-01 HEAD; VI-N1 additionally
omitted the capstone's explicit leading `(p : ℕ) [Fact p.Prime]` binders
(section variable, OM/UniformCapstone.lean:295). The repaired pattern (BP_VI.md
REVISION 3) states each anchor as THE ACTUAL PROPOSITION the gate proves
(`def AnchorX : Prop := <the proposition>`) plus a consumption theorem whose
proof is the corpus gate term verbatim — same intent (exact-proposition
preservation, no retyped denominator or coercion), now well-typed. For VI-N1
a definitional-equality pin (`AnchorN2 p σ hσ = type_of% (montes_uniform_n2
p σ hσ) := rfl`) certifies the transcription is exact.
-/

set_option linter.style.longLine false
set_option linter.dupNamespace false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold.AnchorN2

open LeanUrat LeanUrat.OM LeanUrat.OM.UniformCapstone Polynomial Filter Topology

set_option linter.unusedVariables false in
/-- VI-N1: the exact capstone proposition of `montes_uniform_n2`
    (OM/UniformCapstone.lean:1850), not a hand-reconstructed partial record.
    This preserves pole-freeness, the common rational family, the value tie,
    and bracket uniqueness together, with the prime instance explicit.
    (`hσ` is carried unused, mirroring the capstone's own degree-2 scope pin.) -/
def AnchorN2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : Prop :=
  (uniformDen σ ≠ 0 ∧
    (∀ q' : ℕ, 1 < q' → (uniformDen σ).eval (q' : ℚ) ≠ 0 ∧
      (∑ T ∈ shapesOfU σ, CU T q')
        = (uniformNum σ).eval (q' : ℚ) / (uniformDen σ).eval (q' : ℚ)) ∧
    ((M7 p).countingDensity σ
        = (uniformNum σ).eval ((p : ℕ) : ℚ) / (uniformDen σ).eval ((p : ℕ) : ℚ)
      ∧ (uniformDen σ).eval ((p : ℕ) : ℚ) ≠ 0)) ∧
  ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
      (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N) ≤ d ∧
      d ≤ (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N)
            + (M7 p).undecidedCount N / (p : ℚ) ^ (2 * N)) →
    d = (M7 p).countingDensity σ

/-- VI-N1 consumption: the anchor is discharged by the capstone itself. -/
theorem anchor_n2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : AnchorN2 p σ hσ :=
  montes_uniform_n2 p σ hσ

/-- VI-N1 transcription pin: `AnchorN2` is DEFINITIONALLY the capstone's exact
    proposition — no coercion or denominator was retyped in the scaffold. -/
example (p : ℕ) [Fact p.Prime] (σ : FactorizationType) (hσ : σ.degree = 2) :
    AnchorN2 p σ hσ = type_of% (montes_uniform_n2 p σ hσ) := rfl

section Drainage
open LeanUrat.OM.SeriesAssembly

/-- VI-N2: the exact `hExhaust_n2` proposition (OM/SeriesAssembly.lean:1745) is
    preserved by a named wrapper; no denominator or coercion is retyped. -/
def AnchorN2Drainage : Prop :=
  Tendsto (fun N => undecidedCount6 N / (M9.realP : ℚ) ^ (2 * N)) atTop (nhds 0)

/-- VI-N2 consumption: discharged by `hExhaust_n2` verbatim. -/
theorem anchor_n2_drainage : AnchorN2Drainage := hExhaust_n2

end Drainage

section Gates
open LeanUrat.OM.RealInstanceV2Gates

/-- VI-N3: stable named declaration preserving the complete proposition and all
    coercions of `gate_v2_value_inert2` (OM/RealInstanceV2Gates.lean:90). -/
def AnchorV2ValueInert2 : Prop :=
  (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
      OMCountV2.omCount T M9.realP) = 1 / 4

theorem anchor_v2_value_inert2 : AnchorV2ValueInert2 :=
  gate_v2_value_inert2

/-- VI-N3: the exact proposition of `gate_v2_split_q3`. -/
def AnchorV2SplitQ3 : Prop :=
  (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11),
      OMCountV2.omCount T 3) = 1 / 9

theorem anchor_v2_split_q3 : AnchorV2SplitQ3 := gate_v2_split_q3

/-- VI-N3: the exact proposition of `gate_v2_inert_q3`. -/
def AnchorV2InertQ3 : Prop :=
  (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
      OMCountV2.omCount T 3) = 1 / 3

theorem anchor_v2_inert_q3 : AnchorV2InertQ3 := gate_v2_inert_q3

/-- VI-N3: the exact proposition of `gate_v2_sigma_separation`. -/
def AnchorV2SigmaSeparation : Prop :=
  Order0.unramType 2 OMCountV2.lam11 ≠ Order0.unramType 2 OMCountV2.lam2
    ∧ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11),
          OMCountV2.omCount T 3)
      ≠ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
          OMCountV2.omCount T 3)

theorem anchor_v2_sigma_separation : AnchorV2SigmaSeparation :=
  gate_v2_sigma_separation

end Gates

end LeanUrat.Scaffold.AnchorN2
