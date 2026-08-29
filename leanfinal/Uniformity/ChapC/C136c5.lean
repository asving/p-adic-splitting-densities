/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136c0
import Uniformity.ChapC.C136e2
import Uniformity.ChapI.I10RecenterDirect

/-!
# Uniformity.ChapC.C136c5 — the deep-witness rows C5r + C6r: THE FIRST HONEST
`RecenterStepDirect` OCCURRENCE / `MidPeelEmission`, and the same-X deepTwist tooth
[C56R 2026-08-29]

**Rows C5r + C6r** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.5, as
revised by §11 ([DWR]) and enacted through §12 ([A8D]/[AI8E]): the GN payload is retired,
the live surface is `IFC5.RecenterStepDirect` (`I10RecenterDirect.lean`), and the MP1
occurrence is the DIRECT-key nonvacuity tooth C5d, carrying **every DWR provenance
binding** (`step.quot.F = B'.F`, `B'.T = B.T`, `step.quot.T = B.T`, `B.F = B'.Φ * B'.F`).

## What lands

* Part 1 — **R8r**: the distinct-factor mass-two input `s2C5F0 := s2Mu5Leaf * (g16 + 1)`
  (`= leaf * (keyAt 4 + 1)`), its monicity/degree-32 ledger, and the PARENT key-freeness
  leg `IsCoprime (F0, g16)` over `FractionRing O` (the two landed C136e2 legs multiplied).
* Part 2 — the realized witness at the payload: the first CONCRETE (non-parametric)
  instantiation of the keystone's `s2FourArisingCoreOf`/`s2FourRealizedInputOf` (μ = 2,
  n = 32), and the canonical carrier/block views at `eK = RingEquiv.refl`.
* Part 3 — the quotient block `s2C5QuotBlock` (`Φ = s2Mu5Leaf`, `F = g16 + 1`, `μ = 1`):
  **the G7 gate fires here** — its `hkeyfree` field is the landed quotient key-freeness
  leg, and the falsifier control (`F = leaf` in place of `g16 + 1`) is REFUTED below.
* Part 4 — the `DirectKeyPayload` at `B'.Φ = s2Mu5Leaf` from the μ₅ key bank
  (`s2SourceDataFour`, `S2Mu5KeyPoly_leaf`, `s2Mu5_key_irreducible`), and the
  `MP1StepCore` with `quot := B'` (all four DWR bindings definitional) + the E.12
  arithmetic-shadow `RungInterface` at the μ = 1 quotient (single side, saturated counts —
  the E.57 instance pattern).
* Part 5 — ★ **the C5d occurrence**: `IFC5.RecenterStepDirect` at
  `Λ = s2Mu5Lambda = chainNormBelow 4 171`, `B'.Φ = s2Mu5Leaf = keyAt 4 − Λ`, under the
  ONE existential owner (`core`/`A`/`X` = Part 2's witness, `eK`/`eG` = refl, views = the
  canonical CC-12 producing equalities).
* Part 6 — ★★ **the first honest `MidPeelEmission`**: the generic A-I.8 compiler
  `midPeelEmission_of_recenterStepDirect` fired at the occurrence — the mp1 leg's
  nonvacuity tooth.
* Part 7 — the G7 record: the quotient key-freeness restated at the literal input + the
  CONTROL: the DWV-refuted `leaf²` candidate's quotient (`quot.F = leaf`) FAILS
  key-freeness (`IsCoprime (leaf, leaf)` is false — `leaf` is not a unit).
* Part 8 — **C6r, the same-X deepTwist tooth**: at the unique deep-live level
  (`DeepLive 4 3`), the CONCRETE-payload `DeepLevelExport` nonvacuity, the wired `GentowW`
  projection of C2's demand, and `Ladder.DeepTwistConjunctLive 4` at the witness's own
  exports — C3's `VarthetaRes` paired with C2's `GentowW` under one `X`.

## Honesty scope (the [DWR] fences, kept)

* Conditionality: exactly the keystone's — the four open threshold datums `w₁ w₂ w₃ w₄`
  and `IsAdicComplete` (all Lean-nonempty; their openness is WHICH numeral the inherited
  `T_i` is).  Everything else is discharged at the witness.
* **NO `LadderSupplyLive₂`/`LadderSupplyLive₃` field is claimed.**  The occurrence and the
  tooth are NONVACUITY results for one explicit witness `X` (§11.4): `package`/`lb1` are
  separate HE7A/LB1 campaigns, and the universal deep-level/vartheta exporter is G10's.
  The generic `mp1` field is already discharged by `mp1CarrierLiveDirect_of_steps`
  (A-I.8); what this file adds is that its premise type is INHABITED at an honest witness.
* The `RungInterface` instance is E.12's arithmetic-shadow shape (single side, saturated
  counts, at the REAL polynomial block) — the E.57 precedent; no analytic polygon is
  claimed for it.
* Λ-provenance: `s2Mu5Lambda` IS the landed μ₅ calculus' `chainNormBelow 4 171`
  (`C136t`/`C136e1`); `s2Mu5Leaf = keyAt 4 − Λ` is the recenter equality BY DEFINITION,
  so `B'.Φ = B.Φ − Λ` is definitional at the witness — no equation is bent.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2C5F0`, `s2C5QuotBlock`, `s2C5Iface`, `s2C5DirectKeyPayload`, `s2C5StepCore`,
`s2C5_recenterStepDirect`, `s2C5_midPeelEmission_nonempty`, `s2C6_deepTwistTooth`.

Cite ledger: **empty** — every declaration rests on Lean/mathlib + the Lean-core landed
corpus; `#print axioms` footer is the audit.

Verdict: `runs/wave-c/verdict_C56R.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Uniformity.Density.Tower.C136c5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Gauge
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136e1 Uniformity.Density.Tower.C136e2
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0
open Uniformity.Density.DeepExport

universe uG uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — R8r: the distinct-factor mass-two input `F0 = leaf · (keyAt 4 + 1)` -/

/-- **R8r's input**: `F0 := s2Mu5Leaf * (g16 + 1)` — the mass-two distinct-factor
candidate (`g16 = keyAt 4`, so the cofactor is the row's `keyAt 4 + 1`). -/
def s2C5F0 : Polynomial O := s2Mu5Leaf h2 hq * ((g16 h2 hq : Polynomial O) + 1)

theorem s2C5F0_monic : (s2C5F0 h2 hq).Monic :=
  (s2Mu5Leaf_monic h2 hq).mul (s2_g16_add_one_monic h2 hq)

theorem s2C5F0_natDegree : (s2C5F0 h2 hq).natDegree = 32 := by
  show (s2Mu5Leaf h2 hq * ((g16 h2 hq : Polynomial O) + 1)).natDegree = 32
  rw [(s2Mu5Leaf_monic h2 hq).natDegree_mul (s2_g16_add_one_monic h2 hq),
    s2Mu5Leaf_natDegree h2 hq, s2_g16_add_one_natDegree h2 hq]

/-- **R8r's PARENT key-freeness leg** (the mass-two input against the carried key
`g16 = keyAt 4`, over the fraction field): the two landed C136e2 legs multiplied. -/
theorem s2C5F0_keyfree :
    IsCoprime ((s2C5F0 h2 hq).map (algebraMap O (FractionRing O)))
      ((g16 h2 hq : Polynomial O).map (algebraMap O (FractionRing O))) := by
  have hleaf : IsCoprime ((s2Mu5Leaf h2 hq).map (algebraMap O (FractionRing O)))
      ((g16 h2 hq : Polynomial O).map (algebraMap O (FractionRing O))) :=
    s2Mu5_leaf_keyAt4_coprime_fractionMap (K := FractionRing O) h2 hq
  have hcof : IsCoprime
      (((g16 h2 hq : Polynomial O) + 1).map (algebraMap O (FractionRing O)))
      ((g16 h2 hq : Polynomial O).map (algebraMap O (FractionRing O))) := by
    have h := (s2_g16_add_one_coprime_g16 h2 hq).map
      (Polynomial.mapRingHom (algebraMap O (FractionRing O)))
    simpa [Polynomial.coe_mapRingHom] using h
  show IsCoprime
    ((s2Mu5Leaf h2 hq * ((g16 h2 hq : Polynomial O) + 1)).map
      (algebraMap O (FractionRing O)))
    ((g16 h2 hq : Polynomial O).map (algebraMap O (FractionRing O)))
  rw [Polynomial.map_mul]
  exact hleaf.mul_left hcof

variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)

/-! ## Part 2 — the realized witness at the R8r payload (the first concrete payload) -/

/-- The depth-four `ArisingCore` at the R8r payload: `μ = 2`, `n = 32`. -/
abbrev s2C5Core : ArisingCore (O := O) ((s2DepthFour h2 hq).fld 4) L 32 :=
  s2FourArisingCoreOf h2 hq L (s2C5F0 h2 hq) (s2C5F0_monic h2 hq) 2 one_le_two
    (s2C5F0_natDegree h2 hq) (by norm_num) (s2C5F0_keyfree h2 hq)

/-- The realized input at the R8r payload — THE witness `X` of every theorem below
(the same-`X` discipline of §11.4). -/
abbrev s2C5X :
    RealizedInput (s2C5Core h2 hq L) (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) :=
  s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ (s2C5F0 h2 hq) (s2C5F0_monic h2 hq) 2
    one_le_two (s2C5F0_natDegree h2 hq) (by norm_num) (s2C5F0_keyfree h2 hq)

/-- The exported slot carrier at `eK = RingEquiv.refl` (CC-12's transport). -/
abbrev s2C5Carrier : Ladder.SlotCarrier O ((s2DepthFour h2 hq).fld 4) :=
  (s2C5X h2 hq L w₁ w₂ w₃ w₄).stageCarrierTransport
    (RingEquiv.refl ((s2DepthFour h2 hq).fld 4))

/-- The exported input block `B` (`Φ = g16`, `F = F0`, `μ = 2` — all definitional). -/
abbrev s2C5Block : Ladder.BlockData (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄) :=
  (s2C5X h2 hq L w₁ w₂ w₃ w₄).inputBlockTransport
    (RingEquiv.refl ((s2DepthFour h2 hq).fld 4))

/-! ## Part 3 — the quotient block `B'` (`Φ = leaf`, `F = g16 + 1`, `μ = 1`); G7 fires -/

/-- **The successor/quotient block `B'`** — `Φ := s2Mu5Leaf` (the recentered key
`keyAt 4 − Λ`), `F := g16 + 1` (the distinct cofactor), development `F = Φ + (1 + Λ)`.
Its `hkeyfree` field IS the G7 quotient gate at the literal input (the landed
`s2Mu5_leaf_g16_add_one_coprime_fractionMap`). -/
def s2C5QuotBlock : Ladder.BlockData (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄) where
  Φ := s2Mu5Leaf h2 hq
  F := (g16 h2 hq : Polynomial O) + 1
  μ := 1
  hμ := le_refl 1
  hΦ := s2Mu5Leaf_monic h2 hq
  hΦdeg := (s2Mu5Leaf_natDegree h2 hq).trans (s2DepthFour_Dcum_four h2 hq).symm
  A := fun j => if j = 0 then 1 + s2Mu5Lambda h2 hq else 0
  hdev := by
    have h : ∑ j ∈ Finset.range 1,
        (if j = 0 then 1 + s2Mu5Lambda h2 hq else 0) * s2Mu5Leaf h2 hq ^ j
        = 1 + s2Mu5Lambda h2 hq := by
      rw [Finset.sum_range_one]
      simp
    rw [h, pow_one]
    show (g16 h2 hq : Polynomial O) + 1
      = ((g16 h2 hq : Polynomial O) - s2Mu5Lambda h2 hq) + (1 + s2Mu5Lambda h2 hq)
    ring
  hdegA := fun j hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    rw [if_pos rfl]
    have h15 : (1 + s2Mu5Lambda h2 hq).natDegree ≤ 15 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_one, s2Mu5Lambda_natDegree h2 hq]
      omega
    have hD : (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄).D = 16 := s2DepthFour_Dcum_four h2 hq
    omega
  hkeyfree := (s2Mu5_leaf_g16_add_one_coprime_fractionMap h2 hq).symm
  hA0 := by
    rw [if_pos rfl]
    intro h0
    have hΛ : s2Mu5Lambda h2 hq = -1 := eq_neg_of_add_eq_zero_right h0
    have h15 := s2Mu5Lambda_natDegree h2 hq
    rw [hΛ] at h15
    simp at h15
  T := (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdNat 4

/-! ## Part 4 — the direct payload, the rung interface, and the step core -/

/-- **The `DirectKeyPayload` at `B'.Φ = s2Mu5Leaf`** — the μ₅ key bank plugged into the
A-I.8 surface: `source := s2SourceDataFour` (the landed depth-four `FGMNSourceData` at
`(e', f', u') = (1, 1, 171)`), key-hood `S2Mu5KeyPoly_leaf`, and the DIRECT
irreducibility law `s2Mu5_key_irreducible` (no citation, no axiom — A-I.8's demand). -/
def s2C5DirectKeyPayload :
    IFC5.DirectKeyPayload (core := s2C5Core h2 hq L)
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) (s2Mu5Leaf h2 hq) where
  e' := 1
  f' := 1
  u' := 171
  source := s2SourceDataFour h2 hq
  keyPolynomial := S2Mu5KeyPoly_leaf h2 hq
  key_irreducible := fun _ hkey _ => s2Mu5_key_irreducible h2 hq hkey

/-- The E.12 arithmetic-shadow `RungInterface` at the μ = 1 quotient block: single side
`(T + 1, 1)` (λ > T is `T < T + 1`), one linear residual factor of multiplicity one,
saturated counts `classCount = rootCount = D·1` (E.12's gate arithmetic; the E.57
instance pattern at a REAL polynomial block). -/
def s2C5Iface :
    Ladder.RungInterface.{0, 0, 0} (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄)
      (s2C5QuotBlock h2 hq L w₁ w₂ w₃ w₄) where
  sides := {((s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdNat 4 + 1, 1)}
  hside_cop := fun p hp => by
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨Nat.coprime_one_right _, le_refl 1⟩
  hside_node := fun p hp => by
    rw [Finset.mem_singleton] at hp
    subst hp
    show 1 * (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdNat 4
      < (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdNat 4 + 1
    omega
  len := fun _ => 1
  hlen_pos := fun _ _ => le_refl 1
  hlen_sum := by
    rw [Finset.sum_singleton]
    rfl
  linFac := fun _ => {((1 : (s2DepthFour h2 hq).fld 4), 1)}
  hiFac := fun _ => 0
  hresdeg := fun p hp => by
    rw [Finset.mem_singleton] at hp
    subst hp
    simp
  rootCount := fun _ => (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄).D * 1
  haccount := fun _ _ => rfl
  classCount := fun _ _ => (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄).D * 1
  classCountHi := fun _ _ => 0
  hnonempty := fun p _ => by
    refine ⟨fun q _ => ?_, fun q hq' => absurd hq' (Multiset.notMem_zero q)⟩
    have hD := (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄).hD
    omega
  hforce := fun p hp => by
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨fun q _ => le_refl _, fun q hq' => absurd hq' (Multiset.notMem_zero q)⟩
  hexhaust := fun p _ => by simp
  W := ℕ
  wf := Nat.lt_wfRel
  σRank := 0

/-- **The `MP1StepCore` with `quot := B'`** — the DWR anti-splicing bindings
`hkey`/`hpeel`/`hthr` are DEFINITIONAL at this choice (`B.F = leaf·(g16+1) = B'.Φ·B'.F`
is `s2C5F0`'s definition), and `hmass` is the degree ledger `16 + 16 = 32`. -/
def s2C5StepCore :
    IFC5.MP1StepCore.{0} (s2C5Block h2 hq L w₁ w₂ w₃ w₄)
      (s2C5QuotBlock h2 hq L w₁ w₂ w₃ w₄) where
  quot := s2C5QuotBlock h2 hq L w₁ w₂ w₃ w₄
  hkey := rfl
  hpeel := rfl
  hmass := by
    show ((g16 h2 hq : Polynomial O) + 1).natDegree
        + (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄).D
      = (s2C5F0 h2 hq).natDegree
    have hD : (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄).D = 16 := s2DepthFour_Dcum_four h2 hq
    rw [s2_g16_add_one_natDegree h2 hq, hD, s2C5F0_natDegree h2 hq]
  hthr := rfl
  iface := s2C5Iface h2 hq L w₁ w₂ w₃ w₄

/-! ## Part 5 — ★ the C5d occurrence: `RecenterStepDirect` at the witness -/

/-- ★ **[C5r/C5d] THE FIRST `RecenterStepDirect` OCCURRENCE** — the depth-four witness
fires the A-I.8 live surface at `Λ = s2Mu5Lambda` (the μ₅ calculus'
`chainNormBelow 4 171`, degree 15 < 16), `B'.Φ = s2Mu5Leaf = keyAt 4 − Λ`: one
existential owner (`core`/`A`/`X` = the R8r witness), `eK`/`eG` = refl, the three
CC-12 producing views, the direct μ₅ key payload, and the fully-bound step core.
NEW STATEMENT (review). -/
theorem s2C5_recenterStepDirect :
    IFC5.RecenterStepDirect.{0, uG, 0, uL}
      (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄)
      (s2C5Block h2 hq L w₁ w₂ w₃ w₄)
      (s2C5QuotBlock h2 hq L w₁ w₂ w₃ w₄)
      (GaugeLattice.{uG} 4) ((s2DepthFour h2 hq).fld 4) L
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 4).symm)
      (gaugeHeightFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄))
      (canonicalResFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄))
      (useHeightFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄))
      32 (s2Mu5Lambda h2 hq) := by
  refine ⟨inferInstance, inferInstance, FractionRing (Polynomial O), inferInstance,
    s2C5Core h2 hq L, s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄,
    s2C5X h2 hq L w₁ w₂ w₃ w₄, RingEquiv.refl _, MulEquiv.refl _,
    (s2C5X h2 hq L w₁ w₂ w₃ w₄).slotViewEq _,
    ⟨rfl, (s2C5X h2 hq L w₁ w₂ w₃ w₄).blockViewEq _⟩,
    ?_, s2Mu5Lambda_ne_zero h2 hq, ?_, rfl,
    ⟨(g16 h2 hq : Polynomial O) + 1, rfl⟩, rfl,
    ⟨s2C5DirectKeyPayload h2 hq L w₁ w₂ w₃ w₄⟩,
    s2C5StepCore h2 hq L w₁ w₂ w₃ w₄, rfl, rfl, rfl⟩
  · -- the canonical gauge view at `eG = MulEquiv.refl` (all transports definitional)
    exact (s2C5X h2 hq L w₁ w₂ w₃ w₄).gaugeFamilyViewEq
  · -- `deg Λ = 15 < 16 = C.D`
    have hD : (s2C5Carrier h2 hq L w₁ w₂ w₃ w₄).D = 16 := s2DepthFour_Dcum_four h2 hq
    have h15 := s2Mu5Lambda_natDegree h2 hq
    omega

/-! ## Part 6 — ★★ the first honest `MidPeelEmission` (the mp1 nonvacuity tooth) -/

/-- ★★ **THE FIRST HONEST `MidPeelEmission`** — the generic A-I.8 compiler fired at the
C5d occurrence: E.40's exact record is INHABITED at the honest depth-four witness
(`B = (g16, F0)`, `B' = (leaf, g16+1)`).  The mp1 leg's nonvacuity tooth: the premise
type of the discharged `mp1CarrierLiveDirect_of_steps` is nonempty at a real input.
NEW STATEMENT (review). -/
theorem s2C5_midPeelEmission_nonempty :
    Nonempty (Ladder.MidPeelEmission.{0, 0, 0}
      (s2C5Block h2 hq L w₁ w₂ w₃ w₄) (s2C5QuotBlock h2 hq L w₁ w₂ w₃ w₄)) :=
  IFC5.midPeelEmission_of_recenterStepDirect
    (s2C5_recenterStepDirect.{0, uL} h2 hq L w₁ w₂ w₃ w₄)

/-! ## Part 7 — the G7 record: gate + falsifier control -/

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- **G7, the quotient key-freeness gate at the literal input** (restated as the row's
record; it is `s2C5QuotBlock`'s `hkeyfree` field): `gcd(g16 + 1, leaf) = 1` over the
fraction field. -/
theorem s2C5_g7_quot_keyfree :
    IsCoprime (((g16 h2 hq : Polynomial O) + 1).map (algebraMap O (FractionRing O)))
      ((s2Mu5Leaf h2 hq).map (algebraMap O (FractionRing O))) :=
  (s2Mu5_leaf_g16_add_one_coprime_fractionMap h2 hq).symm

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- **G7's falsifier control, REFUTED as demanded** ([DWR] §11.2: "Replacing `h` by
`leaf` must fail"): the DWV `leaf²` candidate's quotient block would need
`IsCoprime (leaf, leaf)`, which is FALSE — `leaf` maps to a non-unit (it is irreducible
of degree 16). -/
theorem s2C5_g7_control_fails :
    ¬ IsCoprime ((s2Mu5Leaf h2 hq).map (algebraMap O (FractionRing O)))
      ((s2Mu5Leaf h2 hq).map (algebraMap O (FractionRing O))) := by
  intro hcop
  have hirr : Irreducible ((s2Mu5Leaf h2 hq).map (algebraMap O (FractionRing O))) :=
    s2Mu5Leaf_map_irreducible h2 hq
  exact hirr.1 (hcop.isUnit_of_dvd' dvd_rfl dvd_rfl)

/-! ## Part 8 — C6r: the same-X deepTwist tooth at the unique `DeepLive 4 3` -/

/-- **[C6r] the concrete-payload `DeepLevelExport` nonvacuity** — §11.4's FIRST honest
result, now at the CONCRETE R8r payload (C136c0's inhabitant was payload-parametric;
this is the first instantiation with a landed `F₀`). -/
theorem s2C6_deepLevelExport_nonempty (hj : DeepLive 4 3) :
    Nonempty (DeepLevelExport.{0, 0, uL} (s2C5X h2 hq L w₁ w₂ w₃ w₄) 3 hj) :=
  s2Four_deepLevelExport_nonempty h2 hq L w₁ w₂ w₃ w₄ (s2C5F0 h2 hq)
    (s2C5F0_monic h2 hq) 2 one_le_two (s2C5F0_natDegree h2 hq) (by norm_num)
    (s2C5F0_keyfree h2 hq) hj

/-- **[C6r] C2's wired `GentowW`, projected at the concrete payload**: the raw D.44
identity at the witness's own arena/use-height/read/peel-unit exports, `j = 3`. -/
theorem s2C6_gentowW (hj : DeepLive 4 3) :
    GentowW
      (arenaFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄)
        (s2FourCore_one_lt_r h2 hq L (s2C5F0 h2 hq) (s2C5F0_monic h2 hq) 2 one_le_two
          (s2C5F0_natDegree h2 hq) (by norm_num) (s2C5F0_keyfree h2 hq)) 3)
      (useHeightFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄) 3)
      (towerReadFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄) 3)
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).node.peelUnitFamily 3) :=
  (s2Four_wiredGentowDemand h2 hq L w₁ w₂ w₃ w₄ (s2C5F0 h2 hq) (s2C5F0_monic h2 hq) 2
    one_le_two (s2C5F0_natDegree h2 hq) (by norm_num) (s2C5F0_keyfree h2 hq) hj).gentowW

/-- ★ **[C6r] THE SAME-X DEEPTWIST TOOTH** — `Ladder.DeepTwistConjunctLive 4` at the
witness's own exports: at the unique deep-live level `i = 3`, C3's `VarthetaRes`
(`s2Four_varthetaRes`) is paired with C2's wired `GentowW` (the `WFrame` leg) under ONE
witness `X` (the R8r payload).  **FENCE ([DWR] C6r row)**: this is a nonvacuity tooth for
one explicit witness — NO `LadderSupplyLive₂`/`₃` field is claimed; `package`/`lb1` and
G10's universal exporters remain separate obligations.  NEW STATEMENT (review). -/
theorem s2C6_deepTwistTooth :
    Ladder.DeepTwistConjunctLive 4
      (gaugeHeightFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄))
      (canonicalResFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄))
      (useHeightFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄))
      (arenaFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄)
        (s2FourCore_one_lt_r h2 hq L (s2C5F0 h2 hq) (s2C5F0_monic h2 hq) 2 one_le_two
          (s2C5F0_natDegree h2 hq) (by norm_num) (s2C5F0_keyfree h2 hq)))
      (towerReadFamily (s2C5X h2 hq L w₁ w₂ w₃ w₄))
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).node.peelUnitFamily) := by
  intro i hi
  have h3 : 3 ≤ i := hi.1
  have h4 : i < 4 := hi.2
  have hi3 : i = 3 := by omega
  subst hi3
  refine ⟨s2Four_varthetaRes h2 hq L w₁ w₂ w₃ w₄ (s2C5F0 h2 hq) (s2C5F0_monic h2 hq) 2
      one_le_two (s2C5F0_natDegree h2 hq) (by norm_num) (s2C5F0_keyfree h2 hq)
      hi.gaugeLive, ⟨?_⟩⟩
  intro j hj3 hji
  have hj : j = 3 := by omega
  subst hj
  exact s2C6_gentowW h2 hq L w₁ w₂ w₃ w₄ hi

end Uniformity.Density.Tower.C136c5

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none. -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136c5.s2C5F0
#print axioms Uniformity.Density.Tower.C136c5.s2C5F0_monic
#print axioms Uniformity.Density.Tower.C136c5.s2C5F0_natDegree
#print axioms Uniformity.Density.Tower.C136c5.s2C5F0_keyfree
#print axioms Uniformity.Density.Tower.C136c5.s2C5QuotBlock
#print axioms Uniformity.Density.Tower.C136c5.s2C5DirectKeyPayload
#print axioms Uniformity.Density.Tower.C136c5.s2C5Iface
#print axioms Uniformity.Density.Tower.C136c5.s2C5StepCore
#print axioms Uniformity.Density.Tower.C136c5.s2C5_recenterStepDirect
#print axioms Uniformity.Density.Tower.C136c5.s2C5_midPeelEmission_nonempty
#print axioms Uniformity.Density.Tower.C136c5.s2C5_g7_quot_keyfree
#print axioms Uniformity.Density.Tower.C136c5.s2C5_g7_control_fails
#print axioms Uniformity.Density.Tower.C136c5.s2C6_deepLevelExport_nonempty
#print axioms Uniformity.Density.Tower.C136c5.s2C6_gentowW
#print axioms Uniformity.Density.Tower.C136c5.s2C6_deepTwistTooth

end AxCheck
