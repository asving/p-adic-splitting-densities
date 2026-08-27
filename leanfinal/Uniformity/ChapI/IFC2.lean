/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC1
import Uniformity.ChapC.C130sg

/-!
# Uniformity.ChapI.IFC2 — GC-13 wiring at the realized S2 exports: `htheta` DISCHARGED,
`hread` REFUTED at the landed witness, and the underdetermination pin

**[FGCW, 2026-08-27]** — FDTB's blocker (`runs/wave-b/verdict_FDTB.md` gap 2: "discharging
hread/htheta at the realized S2 export data") evaluated at the concrete instance.  The two
IFC1 identifications are NOT a symmetric pair of open equations:

* **`htheta` FALLS at the μ₃ point** (§1): `A.theta q 1 = 1` for EVERY arena
  (`theta_one` — `Θ_N(1;q) = res(n̂(q)/n̂(q)¹) = 1`, a THEOREM of D.04/D.08, no
  dictionary), and the μ₃ calculus's `thetaRatioCleared 1 = x·x⁻¹ = 1` because at `t = 1`
  numerator and denominator are the SAME read, nonzero by A-C.21's landed `d = 1`
  supplies.  So IFC1's `htheta` holds for every arena and every receiver — including the
  witness's OWN exported arena family (§2): universal, hence D-D12-clean.  The μ₃ tooth
  is re-landed conditional on `hread` ALONE (`s2Mu3_gentowWWindow_of_hread`).
* **`hread` at S2 collapses to a read normalization, and the landed witness REFUTES it**
  (§2): the μ₃-side read is the UNIT `1` of the 2-element terminal field
  (`s2Mu3_read_eq_one`), every receiver preserves it (`s2Mu3_hread_iff`:
  `hread ↔ R(ladder point) = 1`); but the landed `s2SplitNode` exports NP-8's explicitly
  FREE convenience choice `towerRead ≡ 0`, so at the landed witness's OWN exports `hread`
  is FALSE at every level, receiver, and lattice point
  (`s2_hread_refuted_at_landed_exports`) — and the full D.44 `GentowW` fails there too
  (`s2_gentowW_false_at_landed_exports`); at depth 2 only the supplier's vacuity
  (`IFC1.deepGentow_demand_vacuous_of_shallow`) shields the deepTwist route.
* **The underdetermination pin** (§3): the equally admissible read constant `1` satisfies
  the FULL `GentowW` over the S2 terminal field (`s2_gentowW_of_read_one`).  ⚠ D-D12
  FENCE, HARD: §3 is the freedom HALF of an adjudication (both truth values of the wiring
  are realized by admissible node data), NOT supply — no witness is constructed and none
  may be presented as teeth.

## The adjudication (the honest BLOCKED-BECAUSE for the remaining `hread`)

`hread` at honest data is **OPEN-DICT-3/4 content**
(`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` §8 items 3–4: the
scalar-coordinate specialization of `R_{r,α}` through `W.fld i ≃ F_i`, and the
normalizer/letter compatibility): D.44's GC-13 note `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))`
was never a provable identification over the landed structures, because `towerRead` is a
FREE node field (NP-8: "nothing in the carrier reads this field") — §2/§3 realize BOTH
truth values, so the wiring is UNDERDETERMINED and needs a NEW source-faithful node LAW,
not a proof.  Decomposer blueprint: `docs/in-progress/GC13_WIRING_2026-08-27.md`.

Zero `sorry`, zero new axiom; AxChk footer expects Lean core only.  All statements below
are NEW (review-flagged, standing queue); nothing binds into leanspec; no existing file is
touched.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC2

open Uniformity.Density Uniformity.Density.Tower Uniformity.Density.Gauge

universe uT uG uL

/-! ## §0 General wiring lemmas (any arena, any calculus) -/

/-- ★ **the `s = 1` theta collapse, EVERY arena**: `Θ_N(1;q) = res(n̂(1·q)·(n̂(q)¹)⁻¹) =
res(1) = 1`.  The `θ`-half of D.44's GC-13 note at the window's single μ₃ exponent is a
THEOREM of D.04/D.08 — no FGMN dictionary enters.  (NEW STATEMENT, review.) -/
theorem theta_one {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) : A.theta q 1 = 1 := by
  have h1 : N.thetaEl q 1 = 1 := by
    rw [NormSection.thetaEl]
    simp
  show A.res ⟨N.thetaEl q 1, A.thetaEl_mem_ker q 1⟩ = 1
  rw [show (⟨N.thetaEl q 1, A.thetaEl_mem_ker q 1⟩ : MonoidHom.ker A.v) = 1 from
    Subtype.ext h1, map_one]

/-- the `s = 0` companion: `Θ_N(0;q) = res(n̂(0)) = 1` — D.44's zero clause (IFC1 gap 1)
therefore reduces to the read normalization `R (N.n 0) = 1`.  (NEW STATEMENT, review.) -/
theorem theta_zero {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) : A.theta q 0 = 1 := by
  have h1 : N.thetaEl q 0 = 1 := by
    rw [NormSection.thetaEl]
    simp [N.n_zero]
  show A.res ⟨N.thetaEl q 0, A.thetaEl_mem_ker q 0⟩ = 1
  rw [show (⟨N.thetaEl q 0, A.thetaEl_mem_ker q 0⟩ : MonoidHom.ker A.v) = 1 from
    Subtype.ext h1, map_one]

/-- ★ **the `t = 1` cleared-ratio collapse, ANY calculus**: at `t = 1` the A-C.21 ratio's
numerator and denominator are the same read (`n̂(u')¹ = n̂(1·u')`), so the ratio is `1`
whenever that read is nonzero.  (NEW STATEMENT, review.) -/
theorem thetaRatioCleared_one {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u')
    (h : I.Rgr (e' * u') (I.chainNormBelow r u') ≠ 0) :
    I.thetaRatioCleared 1 = 1 := by
  rw [FGMNCalculus.thetaRatioCleared]
  simp only [one_mul, pow_one]
  exact mul_inv_cancel₀ h

/-- ★ **D.44 is FALSE at an identically-zero read**: the `s = 1` clause forces
`0 = θ(q,1)·w¹ = w`, impossible for a unit of a field.  The anti-cook tooth §2 fires at
the landed S2 export read.  (NEW STATEMENT, review.) -/
theorem gentowW_false_of_read_zero {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) {R : G → Kt}
    (hR : ∀ g, R g = 0) (u : Ktˣ) : ¬ GentowW A q R u := by
  intro h
  have h1 := h 1
  rw [hR, theta_one A q, Units.val_one, one_mul, pow_one] at h1
  exact u.ne_zero h1.symm

/-! ## §1 The μ₃ point `(2,1,21)`: `htheta` discharged, the tooth on `hread` alone -/

section S2

open IsLocalRing Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C132sg2
open Uniformity.Density.Tower.C132fd1 Uniformity.Density.Tower.C132sg3
open Uniformity.Density.Tower.C130np8 Uniformity.Density.Tower.C130sg

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- the `d = 1` normalizer read is nonzero: `Rgr_ne_zero` at A-C.21's three landed supply
rows — the same derivation as `gentow5w_two_cleared`'s witness leg. -/
theorem s2Mu3_read_ne_zero :
    (s2Mu3Calculus h2 hq).Rgr (2 * (1 * 21))
      ((s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21)) ≠ 0 :=
  (s2Mu3Calculus h2 hq).Rgr_ne_zero (2 * (1 * 21)) _
    (s2Mu3_B1_exact_grade_supply_cleared h2 hq 1 one_pos le_rfl)
    (s2Mu3_B1_degree_supply h2 hq (s2Mu3Calculus h2 hq) rfl 1 one_pos le_rfl)
    (s2Mu3_B1_nonzero_supply h2 hq (s2Mu3Calculus h2 hq) rfl 1 one_pos le_rfl)

/-- ★ **the μ₃ read is the UNIT `1`** of the 2-element terminal field (nonzero + NP-8's
field collapse `s2Kt_eq_zero_or_one`) — so every receiver sends it to `1`, and IFC1's
`hread` is exactly a read normalization (`s2Mu3_hread_iff` below). -/
theorem s2Mu3_read_eq_one :
    (s2Mu3Calculus h2 hq).Rgr (2 * (1 * 21))
      ((s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21)) = 1 :=
  (s2Kt_eq_zero_or_one h2 hq _).resolve_left (s2Mu3_read_ne_zero h2 hq)

/-- the μ₃ cleared ratio at the window's one exponent is `1`. -/
theorem s2Mu3_thetaRatioCleared_one :
    (s2Mu3Calculus h2 hq).thetaRatioCleared 1 = 1 :=
  thetaRatioCleared_one (s2Mu3Calculus h2 hq) (by simpa using s2Mu3_read_ne_zero h2 hq)

/-- ★★ **`htheta` DISCHARGED at the μ₃ point — for EVERY arena and EVERY receiver**:
IFC1's second GC-13 identification, byte-shape, now a theorem.  Universal in `(A, q, φ)`,
so it holds in particular at the witness's OWN exported arena (§2) — D-D12-clean, nothing
cooked. -/
theorem s2Mu3_htheta_discharged {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* Kt) :
    (A.theta q 1 : Kt) * φ ((s2Mu3Calculus h2 hq).thetaRatioCleared 1) = 1 := by
  rw [s2Mu3_thetaRatioCleared_one h2 hq, map_one, mul_one, theta_one A q, Units.val_one]

/-- ★★ **the μ₃ tooth on `hread` ALONE**: IFC1's `s2Mu3_gentowWWindow` with its `htheta`
leg discharged — the deepTwist-ward residue of the μ₃ campaign is now exactly ONE
equation, the GC-13 read identification. -/
theorem s2Mu3_gentowWWindow_of_hread {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* Kt)
    (hread : R (N.n ((1 : ℕ) * q)) =
      φ ((s2Mu3Calculus h2 hq).Rgr (2 * (1 * 21))
          ((s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21)))) :
    ∃ w : Ktˣ, IFC1.GentowWWindow A q R w 1 :=
  IFC1.s2Mu3_gentowWWindow h2 hq A q R φ hread (s2Mu3_htheta_discharged h2 hq A q φ)

/-- ★ **what `hread` IS at S2**: through any receiver the μ₃-side read is `1`, so the
GC-13 read identification is precisely the normalization `R(ladder point) = 1` — the
exact residual equation the wiring campaign must source. -/
theorem s2Mu3_hread_iff {Kt : Type*} [Field Kt]
    (φ : (s2DepthTwo h2 hq).fld 2 →+* Kt) (x : Kt) :
    (x = φ ((s2Mu3Calculus h2 hq).Rgr (2 * (1 * 21))
        ((s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21)))) ↔ x = 1 := by
  rw [s2Mu3_read_eq_one h2 hq, map_one]

/-! ## §2 The realized S2 exports (the D-D12-fenced data): both sides computed -/

variable (L : Type uL) [Field L] [Algebra ((s2DepthTwo h2 hq).fld 2) L]

/-- ★ **the landed witness's export read is identically ZERO**: `towerReadFamily` at the
SG-1 realized input is NP-8's free convenience choice `s2TowerRead ≡ 0` on the gauge-live
range and the CC-11 junk `0` off it. -/
theorem s2_towerReadFamily_zero [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) (j : ℕ) (g : GaugeLattice.{uG} 2) :
    towerReadFamily (s2FrontierRealizedInput h2 hq L wT) j g = 0 := by
  show (s2Frontier h2 hq L wT).toCarrier.node.towerReadFamily0 j
    (gaugeLatticeEquiv 2 g) = 0
  by_cases hj : GaugeLive 2 j
  · rw [SplitNodePointSource.towerReadFamily0_live _ hj]
    rfl
  · exact SplitNodePointSource.towerReadFamily0_junk _ hj _

/-- ★ `htheta` at the witness's OWN exported arena family (the literal data of
`s2Frontier_deepTwist_socket`): §1's universal discharge, instantiated — the `θ`-half of
GC-13 holds at the realized S2 export data. -/
theorem s2_htheta_discharged_at_realized_arena
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (wT : S2LevelOneThreshold)
    (j : ℕ) (q : ℤ)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* (s2DepthTwo h2 hq).fld 2) :
    ((arenaFamily (s2FrontierRealizedInput h2 hq L wT) Nat.one_lt_two j).theta q 1 :
        (s2DepthTwo h2 hq).fld 2)
      * φ ((s2Mu3Calculus h2 hq).thetaRatioCleared 1) = 1 :=
  s2Mu3_htheta_discharged h2 hq _ q φ

/-- ★★ **`hread` is FALSE at the landed witness's OWN exports** — every level `j`, every
receiver `φ`, every lattice point: the exported read is `0` (NP-8's convenience choice),
the μ₃ read is the unit `1`, and receivers preserve `1`.  The GC-13 wiring CANNOT be
discharged at the landed S2 witness; per the module adjudication the missing content is a
source-faithful read law (OPEN-DICT-3/4), not a proof. -/
theorem s2_hread_refuted_at_landed_exports
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (wT : S2LevelOneThreshold)
    (j : ℕ) (g : GaugeLattice.{uG} 2)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* (s2DepthTwo h2 hq).fld 2) :
    towerReadFamily (s2FrontierRealizedInput h2 hq L wT) j g ≠
      φ ((s2Mu3Calculus h2 hq).Rgr (2 * (1 * 21))
          ((s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21))) := by
  rw [s2_towerReadFamily_zero h2 hq L wT j g, s2Mu3_read_eq_one h2 hq, map_one]
  exact zero_ne_one

/-- ★★ the stronger export-level refutation: the FULL D.44 `GentowW` fails at the landed
witness's exported read — every arena, height, and peel unit.  At depth 2 only the
supplier's vacuity (`IFC1.deepGentow_demand_vacuous_of_shallow`) shields the deepTwist
route from this witness; a depth-`≥ 4` witness assembled with the same free read would
REFUTE `DeepGentowSupplier` outright (the blueprint's tension record). -/
theorem s2_gentowW_false_at_landed_exports
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (wT : S2LevelOneThreshold) (j : ℕ)
    {N : NormSection (GaugeLattice.{uG} 2)}
    (A : GaugeArena (GaugeLattice.{uG} 2) ((s2DepthTwo h2 hq).fld 2) N) (q : ℤ)
    (u : ((s2DepthTwo h2 hq).fld 2)ˣ) :
    ¬ GentowW A q (towerReadFamily (s2FrontierRealizedInput h2 hq L wT) j) u :=
  gentowW_false_of_read_zero A q (s2_towerReadFamily_zero h2 hq L wT j) u

/-! ## §3 The underdetermination pin — ⚠ D-D12 FENCE, HARD

`towerRead` is a FREE node field (NP-8: "a FREE choice … never forced; nothing in the
carrier reads this field except through the ladder-point evaluations D.44 licenses").
§2 shows the landed choice `0` refutes the wiring; the pin below shows the equally
admissible choice `1` satisfies the FULL D.44 identity over the S2 terminal field.  Both
truth values are realized by admissible node data, so the landed laws UNDERDETERMINE
GC-13: the wiring is a missing source-faithful LAW, not a missing proof.  This theorem is
the adjudication's freedom half ONLY — it constructs NO witness, supplies NO socket, and
may never be presented as teeth. -/

/-- ⚠ freedom half (see the section fence — NOT supply): over the S2 terminal field every
`Ktˣ`-value is `1` (NP-8's `s2Unit_eq_one`), so a constant-`1` read satisfies `GentowW`
at every exponent, for every arena and peel unit. -/
theorem s2_gentowW_of_read_one {G : Type*} [CommGroup G] {N : NormSection G}
    (A : GaugeArena G ((s2DepthTwo h2 hq).fld 2) N) (q : ℤ)
    {R : G → (s2DepthTwo h2 hq).fld 2} (hR : ∀ g, R g = 1)
    (u : ((s2DepthTwo h2 hq).fld 2)ˣ) :
    GentowW A q R u := by
  intro s
  rw [hR, s2Unit_eq_one h2 hq (A.theta q s), s2Unit_eq_one h2 hq u, Units.val_one,
    one_pow, mul_one]

end S2

end Uniformity.Density.IFC2

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Consumes the UNCONDITIONAL μ₃ package (`C132sg2`/`C132sg3`, cite-free) and the SG-0/SG-1
realized S2 funnel (`C130sg`, cite-free); nothing here may add to the trusted base. -/

#print axioms Uniformity.Density.IFC2.theta_one
#print axioms Uniformity.Density.IFC2.theta_zero
#print axioms Uniformity.Density.IFC2.thetaRatioCleared_one
#print axioms Uniformity.Density.IFC2.gentowW_false_of_read_zero
#print axioms Uniformity.Density.IFC2.s2Mu3_read_ne_zero
#print axioms Uniformity.Density.IFC2.s2Mu3_read_eq_one
#print axioms Uniformity.Density.IFC2.s2Mu3_thetaRatioCleared_one
#print axioms Uniformity.Density.IFC2.s2Mu3_htheta_discharged
#print axioms Uniformity.Density.IFC2.s2Mu3_gentowWWindow_of_hread
#print axioms Uniformity.Density.IFC2.s2Mu3_hread_iff
#print axioms Uniformity.Density.IFC2.s2_towerReadFamily_zero
#print axioms Uniformity.Density.IFC2.s2_htheta_discharged_at_realized_arena
#print axioms Uniformity.Density.IFC2.s2_hread_refuted_at_landed_exports
#print axioms Uniformity.Density.IFC2.s2_gentowW_false_at_landed_exports
#print axioms Uniformity.Density.IFC2.s2_gentowW_of_read_one
