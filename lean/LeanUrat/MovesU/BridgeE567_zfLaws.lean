/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeZp
import LeanUrat.SerreLocalFields

/-!
# BridgeE567 — the zf LAWS at the re-pointed invariants (bridge campaign BP1, Group E)

Units **IB-E5** (`zf_pos`), **IB-E6** (pointwise e·f = deg), **IB-E7** (`zf_factor`
assembly), per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §4 Group E and the
IB-E6 re-plan through `OM/QpType`'s convention (SYNTHESIS PASS 1 findings C3/N1;
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` Q2/C3/N1 adjudication).

GATE STATUS (why this file may exist): the Q2 repair LANDED 2026-07-31 (sign-off
queue item 2) — `MovesT.ramIdx`/`resDeg` are re-pointed at THE INTEGRAL CLOSURE of
ℤ_p in the factor field `AdjoinRoot (h.map (algebraMap ℤ_[p] ℚ_[p]))` (Defs.lean
§2.7), and the Group-E gate (the Codex guardian audit of
`LeanUrat.SerreLocalFields.AX_integralClosure_dvr`) PASSED 2026-07-31 (recorded in
`docs/AXIOM_FAITHFULNESS.md` AX-SERRE-DVR + the campaign ledger).

CONDITIONALITY (visible, per the M16 faithfulness analysis
`lean/notes/openmath/M16-zf-serre_fable.md` §0/§5): every theorem below whose census
prints `AX_integralClosure_dvr` rides EXACTLY the one literature axiom (Serre,
*Local Fields* GTM 67, Ch. II §2, Prop. 3 — the DVR clause); all remaining content
is the pinned-Mathlib derivation inventory of M16 §5 (L1/L2/L3 are Mathlib-derivable
from L0), machine-checked here:
* (L2) = IB-E6 `ramIdx_mul_resDeg_of_irreducible` — the POINTWISE fundamental
  identity e·f = deg at the repaired defs, via
  `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` (Mathlib's Σeᵢfᵢ = n
  specialized to the local integral closure) + the §5 instance chain.
* (L1) = IB-E5 `bridge_zf_pos` — DERIVED from (L2): e·f = deg ≥ 1 forces both ≥ 1
  (the M16 "alternatively" route; no separate ne-zero lemmas needed).
* (L3) = IB-E7 `bridge_zf_factor` — witnesses := `monicFactors g` (IB-E1/E2/E3,
  BridgeZp.lean); conjunct 4 is the AGGREGATE identity derived from conjunct 3 +
  (L2) pointwise + `Multiset.map_congr` (M16 §4.2: pointwise ⟹ aggregate, never
  the converse).

TRANSCRIPTION RESOLUTIONS (statement fence; E-phase rule):
1. IB-E5/E7 are stated in the EXACT `ZpBridge.zf_pos`/`zf_factor` field shapes
   (DefsLedger.lean:742–750) at `zfType := bridgeZfType`, so IB-E9 consumes them
   verbatim.  The unused `g.natDegree = n` binder is kept — it is the field's.
2. IB-E6 is stated on the monic ℚ_p-irreducible locus with the guard at
   `algebraMap ℤ_[p] ℚ_[p]` (the repaired defs' own map); the `PadicInt.Coe.ringHom`
   spelling used by `zf_factor`'s conjunct 2 converts by `padicCoe_eq_algebraMap`
   (rfl, BridgeZp.lean).
3. W1 (M16 §4.3, cross-bundle invariance) is NOT needed: the repaired defs read ONE
   canonical carrier (`integralClosure ℤ_[p] L` itself), so no two-bundle agreement
   arises anywhere below.

Census: the AxCheck block at the bottom.  Expected footprints —
`maximalIdeal_padicInt_ne_bot` CORE ONLY; the three law theorems
`AX_integralClosure_dvr` + core (the M16 conditionality, nothing else).
Build: `lake env lean LeanUrat/MovesU/BridgeE567_zfLaws.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ## Proof-internal groundwork (NOT fenced statements) -/

/-- Proof-internal (IB-E6, NOT a fenced statement): the maximal ideal of ℤ_p is
    not ⊥ — it is `span {p}` and `p ≠ 0` (`PadicInt.prime_p`).  Supplies the
    `hp0` argument of Mathlib's fundamental-identity lemma.  Footprint: CORE. -/
theorem maximalIdeal_padicInt_ne_bot :
    (IsLocalRing.maximalIdeal ℤ_[p]) ≠ ⊥ := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  intro hbot
  rw [Ideal.span_singleton_eq_bot] at hbot
  exact (PadicInt.prime_p (p := p)).ne_zero hbot

/-! ## IB-E6 — the POINTWISE fundamental identity e·f = deg (†11g at the repaired defs)

Informal statement: for h monic over ℤ_p with ℚ_p-irreducible image,
`MovesT.ramIdx h * MovesT.resDeg h = h.natDegree` — the invariants read at the
integral closure `O = integralClosure ℤ_[p] L`, `L = AdjoinRoot (h.map …)`,
multiply to the field degree.  Deps: the Serre axiom (fires the dispatch +
DVR-ness of O), then Mathlib's `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
over the M16 §5 instance chain (finite-dimensionality via the power basis;
separability from char 0; `Module.Finite ℤ_[p] O` via `IsIntegralClosure.isNoetherian`;
`IsFractionRing O L` via `isFractionRing_of_finite_extension`; Dedekind on both
sides from PIR). -/

/-- IB-E6 (†11g, REPAIRED READING) — THE POINTWISE LAW: e·f = deg at the
    integral-closure invariants.  [Footprint: `AX_integralClosure_dvr` + core —
    the M16 (L2)-from-(L0) derivation, machine-checked.] -/
theorem ramIdx_mul_resDeg_of_irreducible (h : Polynomial ℤ_[p]) (hm : h.Monic)
    (hirr : Irreducible (h.map (algebraMap ℤ_[p] ℚ_[p]))) :
    MovesT.ramIdx h * MovesT.resDeg h = h.natDegree := by
  classical
  haveI hfact : Fact (Irreducible (h.map (algebraMap ℤ_[p] ℚ_[p]))) := ⟨hirr⟩
  have hne : h.map (algebraMap ℤ_[p] ℚ_[p]) ≠ 0 :=
    (hm.map (algebraMap ℤ_[p] ℚ_[p])).ne_zero
  -- the factor field L and its finite-dimensionality (M16 §5 item 1)
  set L := AdjoinRoot (h.map (algebraMap ℤ_[p] ℚ_[p])) with hLdef
  haveI : FiniteDimensional ℚ_[p] L := PowerBasis.finite (AdjoinRoot.powerBasis hne)
  -- the axiom fires: O := integralClosure ℤ_[p] L is a DVR, hence local (dispatch)
  haveI hdvr : IsDiscreteValuationRing (integralClosure ℤ_[p] L) :=
    LeanUrat.SerreLocalFields.AX_integralClosure_dvr p L
  have hloc : IsLocalRing (integralClosure ℤ_[p] L) := inferInstance
  -- unfold the junk-total dispatch on its firing locus
  unfold MovesT.ramIdx MovesT.resDeg
  rw [dif_pos hloc, dif_pos hloc]
  -- M16 §5 instance chain items 3–6
  haveI : IsNoetherian ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.isNoetherian ℤ_[p] ℚ_[p] L (integralClosure ℤ_[p] L)
  haveI : IsFractionRing (integralClosure ℤ_[p] L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] L
      (integralClosure ℤ_[p] L)
  -- the fundamental identity, local (DVR) case, then finrank = deg
  have key := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (R := ℤ_[p]) (S := integralClosure ℤ_[p] L) (K := ℚ_[p]) (L := L)
    (p := IsLocalRing.maximalIdeal ℤ_[p]) maximalIdeal_padicInt_ne_bot
  rw [key, PowerBasis.finrank (AdjoinRoot.powerBasis hne), AdjoinRoot.powerBasis_dim hne]
  exact hm.natDegree_map (algebraMap ℤ_[p] ℚ_[p])

/-! ## IB-E5 — `zf_pos` (†11e)

Informal statement: every pair read by `bridgeZfType` on a monic degree-n input has
both coordinates ≥ 1.  Deps: IB-E1/E2/E3 (the factor roster laws, BridgeZp.lean) +
IB-E6.  Sketch (the M16 (L1)-from-(L2) route): each read pair is
`(ramIdx h, resDeg h)` at a monic irreducible factor h of positive degree; IB-E6
gives `ramIdx h * resDeg h = h.natDegree ≥ 1`, and a ℕ-product is ≥ 1 only if both
factors are. -/

/-- IB-E5 (†11e) — `zf_pos` in the exact `ZpBridge.zf_pos` field shape
    (DefsLedger.lean:742–743) at `zfType := bridgeZfType`.  [Footprint:
    `AX_integralClosure_dvr` + core.] -/
theorem bridge_zf_pos (n : ℕ) : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∀ ef ∈ bridgeZfType g, 1 ≤ ef.1 ∧ 1 ≤ ef.2 := by
  intro g hg _ ef hef
  unfold bridgeZfType at hef
  rw [Multiset.mem_map] at hef
  obtain ⟨h, hmem, rfl⟩ := hef
  have hm := monicFactors_monic g hg h hmem
  have hdpos := monicFactors_natDegree_pos g hg h hmem
  have hirrZ := monicFactors_irreducible g hg h hmem
  have hirrQ : Irreducible (h.map (algebraMap ℤ_[p] ℚ_[p])) := by
    rw [← padicCoe_eq_algebraMap]
    exact monic_irreducible_map_coe h hm hdpos hirrZ
  have hef := ramIdx_mul_resDeg_of_irreducible h hm hirrQ
  constructor
  · rcases Nat.eq_zero_or_pos (MovesT.ramIdx h) with h0 | h1
    · rw [h0, zero_mul] at hef; omega
    · exact h1
  · rcases Nat.eq_zero_or_pos (MovesT.resDeg h) with h0 | h1
    · rw [h0, mul_zero] at hef; omega
    · exact h1

/-! ## IB-E7 — `zf_factor` assembly

Informal statement: for monic degree-n g, the roster `monicFactors g` witnesses the
four `zf_factor` conjuncts — the ℚ_p-side product law, monicity + ℚ_p-irreducibility
per factor, the definitional `bridgeZfType` read, and the AGGREGATE degree identity.
Deps: IB-E1 (`monicFactors_prod`), IB-E2 (irreducible + degree-positive), IB-E3
(Gauss transfer), IB-E11 (`bridgeZfType` def), IB-E6 (pointwise, for conjunct 4). -/

/-- IB-E7 — `zf_factor` in the exact `ZpBridge.zf_factor` field shape
    (DefsLedger.lean:744–750) at `zfType := bridgeZfType`.  [Footprint:
    `AX_integralClosure_dvr` + core.] -/
theorem bridge_zf_factor (n : ℕ) : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∃ factors : Multiset (Polynomial ℤ_[p]),
      g.map (PadicInt.Coe.ringHom)
          = (factors.map (Polynomial.map PadicInt.Coe.ringHom)).prod ∧
      (∀ h ∈ factors, h.Monic ∧ Irreducible (h.map PadicInt.Coe.ringHom)) ∧
      bridgeZfType g = factors.map (fun h => (MovesT.ramIdx h, MovesT.resDeg h)) ∧
      (bridgeZfType g).map (fun ef => ef.1 * ef.2) = factors.map Polynomial.natDegree := by
  intro g hg _
  refine ⟨monicFactors g, ?_, ?_, rfl, ?_⟩
  · -- conjunct 1: the ℚ_p-side product law from `monicFactors_prod` + hom-of-prod
    have hhom := map_multiset_prod (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := p)))
      (monicFactors g)
    simp only [Polynomial.coe_mapRingHom] at hhom
    conv_lhs => rw [← monicFactors_prod g hg]
    exact hhom
  · -- conjunct 2: monic + ℚ_p-irreducible per factor (IB-E2 + IB-E3)
    intro h hmem
    have hm := monicFactors_monic g hg h hmem
    exact ⟨hm, monic_irreducible_map_coe h hm
      (monicFactors_natDegree_pos g hg h hmem)
      (monicFactors_irreducible g hg h hmem)⟩
  · -- conjunct 4: the aggregate identity from conjunct 3 + IB-E6 pointwise
    unfold bridgeZfType
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun h hmem => ?_
    have hm := monicFactors_monic g hg h hmem
    have hirrQ : Irreducible (h.map (algebraMap ℤ_[p] ℚ_[p])) := by
      rw [← padicCoe_eq_algebraMap]
      exact monic_irreducible_map_coe h hm
        (monicFactors_natDegree_pos g hg h hmem)
        (monicFactors_irreducible g hg h hmem)
    simpa using ramIdx_mul_resDeg_of_irreducible h hm hirrQ

/-! ## Census (expected: `maximalIdeal_padicInt_ne_bot` CORE ONLY; the three laws
`AX_integralClosure_dvr` + core — the M16 single-axiom conditionality) -/

section AxCheck

#print axioms LeanUrat.MovesU.maximalIdeal_padicInt_ne_bot
#print axioms LeanUrat.MovesU.ramIdx_mul_resDeg_of_irreducible
#print axioms LeanUrat.MovesU.bridge_zf_pos
#print axioms LeanUrat.MovesU.bridge_zf_factor

end AxCheck

end LeanUrat.MovesU
