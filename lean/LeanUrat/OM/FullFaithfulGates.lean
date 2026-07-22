/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.FullFaithful

/-!
# FullFaithfulGates — witnesses, type-consequence gates, and probe anchors for the
scope-#5 faithfulness theorem
(Wild Wave 6c task D, `notes/WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §2-W6c-d, §3 anti-vacuity;
blueprint Codex-verified)

`OM/FullFaithful.lean` assembled `fullFiber_hasType`: every genuine monic quadratic over
`ℤ_[2]` whose coefficient box pair lies in ANY decided fiber of the full `n = 2` model
(`decidedCount6 σ N`) has a genuine ℚ_2-factorization certificate of the keyed type. THIS
module supplies the W6c-d evidence layer — the theorem (and the re-scoped axiom behind its
ram/inert legs) genuinely FIRES:

**Witness nonemptiness** (all four externally cross-checked against the 2-adic disc
square-class criterion, calibrated on the banked anchors `X² + 12` / `X² + 28` / `X² + 4`):
* `w6cInertPoly = x² + 2x + 4` — the DEPTH-0 inert fiber `LeafPair (inert 1)` at `(5, 5)`
  (disc `−12 = 4·(−3)`, `−3 ≡ 5 mod 8` ⟹ unramified quadratic: genuinely inert ✓);
* `w6cSplitPoly = x² + 2x + 8` — the depth-0 split fiber `LeafPair (split 1)` at `(5, 5)`
  (disc `−28 = 4·(−7)`, `−7 ≡ 1 mod 8` a 2-adic square: genuinely split ✓);
* `w6cTransPoly = x² − 2x + 5` — the `c = 1` TRANSLATE chain fiber
  `TransChain 1 [1] (ram 1)` at `N = 4`: its genuine translate `f(x+1) = x² + 4` is EXACTLY
  the banked chain-gate witness `QpTypeChain.chainGatePoly` (disc of `x²+4` is `−16`,
  totally ramified ✓ — `ℚ_2(2i)` with `i² = −1`... precisely `v(root) = 1/2`);
* `w6cDeepPoly = x² + 16` — a GENERAL-`m` chain fiber (`m = 2`): `ChainPair [2] (ram 1)` at
  `(6, 6)` (budget `2·2 + 2 = 6 ≤ 6`; the `m = 2` step at `ĉ = 1` descends
  `(16, 0) ↦ (16/16 + 0 + 1, 0/4 + 2) = (2, 2)` — the `ram 1` leaf read `v(b₀) = 1` exact).

**Type-consequence gates** (each witness exercises a landed W6c payload):
* `gate_w6c_inert_forced` — every bundle on the depth-0 inert witness carries `(1, 2)`
  (the (I) master through `leafFiber_inert_forced`; AXIOM-FREE);
* `gate_w6c_split_hasType_axfree` — the depth-0 split witness has a genuine certificate of
  type `{(1,1),(1,1)}` THROUGH the assembled `fullFiber_split_hasType_axfree` (AXIOM-FREE);
* `gate_w6c_trans_hasType` — **the assembled theorem end-to-end at a witness**:
  `fullFiber_hasType` at the family `chain 1 [1] (ram 1)` hands the `c = 1` translate
  witness a certificate of type `{(2,1)}` (footprint core + `om_leaf_faithful` — the single
  most valuable gate: menu + fiber + axiom + translate transport all fire);
* `gate_w6c_deep_forced` — irreducibility + every-bundle `(2, 1)` on the `m = 2` witness
  (the unwind + (R) master through `chainFiber_ram_forced`; AXIOM-FREE);
* `gate_w6c_axiom_coherent` — POSITIVE probe leg: the REAL axiom at the depth-0 inert
  witness through its `omMenu6` membership (the NEW scope-#5 menu leg) yields a certificate
  of type `{(1,2)}` COEXISTING with the proved irreducibility (core + `om_leaf_faithful`).

**Mutation probes** (the house scratch-derive-`False` pattern; scratch NOT committed,
recorded in the evidence block below): wrong-keying mutations at the two NEW fiber families
— split keying at the depth-0 inert leg, fine-`(e,f)`-swap keying at the `c = 1` translate
ram leg — each derive `False` against the AXIOM-FREE forcing anchors; the real
`om_leaf_faithful` appears in NEITHER refutation cone.

**Capstone companion** (`montes_n2_full_faithful`): the W6 capstone's full conclusion
(`SeriesAssembly.montes_unconditional_n2_full` — untouched) packaged in one statement with
the scope-#5 faithfulness clause. Footprint: core + `om_leaf_faithful` (the faithfulness
clause consumes the axiom; the capstone conjunct alone remains core-only at its own name).

Discipline: purely ADDITIVE module; no `sorry`, no new axiom; AxCheck census at bottom —
`gate_w6c_trans_hasType` / `gate_w6c_axiom_coherent` / `montes_n2_full_faithful` = Lean core
+ `om_leaf_faithful` exactly; EVERYTHING else core-only.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.FullFaithfulGates

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu LeanUrat.OM.CellCard
open LeanUrat.OM.QpTypeChain LeanUrat.OM.QpTypeChainLeaves LeanUrat.OM.QpTypeLeafMasters
open LeanUrat.OM.QpTypeChainAll

/-! ## Block 1 — the four witness polynomials and their fiber memberships -/

section Witnesses

/-- The depth-0 INERT witness `x² + 2x + 4` over `ℤ_[2]` (disc `−12`; `−3 ≡ 5 mod 8` ⟹
unramified quadratic). -/
noncomputable def w6cInertPoly : Polynomial ℤ_[M9.realP] := X ^ 2 + C 2 * X + C 4

theorem w6cInertPoly_monic : w6cInertPoly.Monic := by
  unfold w6cInertPoly
  monicity!

theorem w6cInertPoly_natDegree : w6cInertPoly.natDegree = 2 := by
  unfold w6cInertPoly
  compute_degree!

/-- **Depth-0 inert fiber nonemptiness** (`N = 5`): the box pair `(4, 2)` of the inert
witness satisfies the `LeafPair (inert 1)` digit conditions at frame `(5, 5)` —
`v(4) = 2` exact (residual digit 1), `v(2) = 1` (residual digit 1),
`(1, 1) ∈ noRootPairs 2` (the root-free residual `z² + z + 1`). -/
theorem w6cInertPair_mem :
    ChainMenu.LeafPair M9.realP (ChainMenu.ChainLeaf.inert 1) 5 5
      (PadicInt.toZModPow 5 (w6cInertPoly.coeff 0),
        PadicInt.toZModPow 5 (w6cInertPoly.coeff 1)) := by
  have hc0 : w6cInertPoly.coeff 0 = 4 := by
    unfold w6cInertPoly
    simp
  have hc1 : w6cInertPoly.coeff 1 = 2 := by
    unfold w6cInertPoly
    simp
  rw [hc0, hc1, map_ofNat, map_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · rw [ChainMenu.mem_noRootPairs]
    decide

/-- The depth-0 SPLIT witness `x² + 2x + 8` over `ℤ_[2]` (disc `−28`; `−7 ≡ 1 mod 8` a
2-adic square). -/
noncomputable def w6cSplitPoly : Polynomial ℤ_[M9.realP] := X ^ 2 + C 2 * X + C 8

theorem w6cSplitPoly_monic : w6cSplitPoly.Monic := by
  unfold w6cSplitPoly
  monicity!

theorem w6cSplitPoly_natDegree : w6cSplitPoly.natDegree = 2 := by
  unfold w6cSplitPoly
  compute_degree!

/-- **Depth-0 split fiber nonemptiness** (`N = 5`): the box pair `(8, 2)` of the split
witness satisfies `LeafPair (split 1)` at `(5, 5)` — readability gate `3 ≤ 5` ✓,
`v(8) = 3 ≥ 3` ✓, `v(2) = 1` exact ✓. -/
theorem w6cSplitPair_mem :
    ChainMenu.LeafPair M9.realP (ChainMenu.ChainLeaf.split 1) 5 5
      (PadicInt.toZModPow 5 (w6cSplitPoly.coeff 0),
        PadicInt.toZModPow 5 (w6cSplitPoly.coeff 1)) := by
  have hc0 : w6cSplitPoly.coeff 0 = 8 := by
    unfold w6cSplitPoly
    simp
  have hc1 : w6cSplitPoly.coeff 1 = 2 := by
    unfold w6cSplitPoly
    simp
  rw [hc0, hc1, map_ofNat, map_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The `c = 1` TRANSLATE witness `x² − 2x + 5` over `ℤ_[2]`: its genuine translate
`f(x + 1) = x² + 4` is the banked chain-gate witness. -/
noncomputable def w6cTransPoly : Polynomial ℤ_[M9.realP] := X ^ 2 - C 2 * X + C 5

theorem w6cTransPoly_monic : w6cTransPoly.Monic := by
  unfold w6cTransPoly
  monicity!

theorem w6cTransPoly_natDegree : w6cTransPoly.natDegree = 2 := by
  unfold w6cTransPoly
  compute_degree!

/-- The genuine translate of the `c = 1` witness IS the banked chain-gate polynomial:
`(x² − 2x + 5)(x + 1) = x² + 4`. -/
theorem w6cTransPoly_comp :
    w6cTransPoly.comp (X + C ((1 : ℕ) : ℤ_[M9.realP])) = X ^ 2 + C 4 := by
  unfold w6cTransPoly
  rw [Nat.cast_one]
  simp only [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp only [Polynomial.C_1, map_ofNat]
  ring

/-- **`c = 1` translate chain fiber nonemptiness** (`N = 4`): the box pair `(5, −2)` of the
translate witness lies in the `TransChain 1 [1] (ram 1)` fiber — via the PROVED translate
reduction `transChain_fiber_iff`, this is the `ChainPair [1] (ram 1)` fiber of the translate
`x² + 4` at box pair `(4, 0)`: stratum digits `v(4) = 2` exact (digit `1 = ĉ²`),
`v(0) ≥ 1`; leaf digits `v(b₀) = 1` exact, `v(b₁) ≥ 1` (the banked chain-gate read). -/
theorem w6cTransFiber_nonempty :
    SeriesAssembly.TransChain 1 [1] (ChainMenu.ChainLeaf.ram 1) 4
      (PadicInt.toZModPow 4 (w6cTransPoly.coeff 0),
        PadicInt.toZModPow 4 (w6cTransPoly.coeff 1)) := by
  refine (transChain_fiber_iff [1] (ChainMenu.ChainLeaf.ram 1)
    w6cTransPoly_monic w6cTransPoly_natDegree 1 4).mpr ?_
  rw [w6cTransPoly_comp]
  have hc0 : (X ^ 2 + C (4 : ℤ_[M9.realP])).coeff 0 = 4 := by simp
  have hc1 : (X ^ 2 + C (4 : ℤ_[M9.realP])).coeff 1 = 0 := by simp
  rw [hc0, hc1, map_ofNat, map_zero]
  show ChainMenu.ChainPair M9.realP [1] (ChainMenu.ChainLeaf.ram 1) 4 4
    ((4 : ZMod (M9.realP ^ 4)), 0)
  refine ⟨1, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  · show ChainMenu.LeafPair M9.realP (ChainMenu.ChainLeaf.ram 1) (4 - 2 * 1) (4 - 1)
      (ChainMenu.descendPair M9.realP 1 (((1 : (ZMod M9.realP)ˣ) : ZMod M9.realP)).val
        ((4 : ZMod (M9.realP ^ 4)), 0))
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide

/-- The GENERAL-`m` (`m = 2`) DEEP witness `x² + 16` over `ℤ_[2]`. -/
noncomputable def w6cDeepPoly : Polynomial ℤ_[M9.realP] := X ^ 2 + C 16

theorem w6cDeepPoly_monic : w6cDeepPoly.Monic := by
  unfold w6cDeepPoly
  monicity!

theorem w6cDeepPoly_natDegree : w6cDeepPoly.natDegree = 2 := by
  unfold w6cDeepPoly
  compute_degree!

/-- **General-`m` chain fiber nonemptiness** (`m = 2`, `N = 6`, budget `2·2 + 2 = 6 ≤ 6`):
the box pair `(16, 0)` of the deep witness lies in `ChainPair [2] (ram 1)` at `(6, 6)` —
stratum digits at head `m = 2`: `v(16) = 4` exact (digit `1 = ĉ²`), `v(0) ≥ 2`; the `ĉ = 1`
descent sends `(16, 0) ↦ (16/16 + 1·(0/4) + 1², 0/4 + 2·1) = (2, 2)` in frame `(2, 4)`,
where the `ram 1` leaf reads `v(2) = 1` exact (digit 1) and `v(2) ≥ 1`. -/
theorem w6cDeepFiber_nonempty :
    ChainMenu.ChainPair M9.realP [2] (ChainMenu.ChainLeaf.ram 1) 6 6
      (PadicInt.toZModPow 6 (w6cDeepPoly.coeff 0),
        PadicInt.toZModPow 6 (w6cDeepPoly.coeff 1)) := by
  have hc0 : w6cDeepPoly.coeff 0 = 16 := by
    unfold w6cDeepPoly
    simp
  have hc1 : w6cDeepPoly.coeff 1 = 0 := by
    unfold w6cDeepPoly
    simp
  rw [hc0, hc1, map_ofNat, map_zero]
  refine ⟨1, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  · show ChainMenu.LeafPair M9.realP (ChainMenu.ChainLeaf.ram 1) (6 - 2 * 2) (6 - 2)
      (ChainMenu.descendPair M9.realP 2 (((1 : (ZMod M9.realP)ˣ) : ZMod M9.realP)).val
        ((16 : ZMod (M9.realP ^ 6)), 0))
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide

end Witnesses

/-! ## Block 2 — index-set and menu memberships (the summation indices the witnesses sit
under, and the scope-#5 menu leg the coherence gate fires through) -/

section Membership

/-- The `c = 1` translate family `chain 1 [1] (ram 1)` is a well-formed summand of the
type-`{(2,1)}` count at `N = 4`. -/
theorem w6cTrans_index_ok :
    FullFaithful.W6FiberOK
      (FullFaithful.W6Fiber.chain 1 [1] (ChainMenu.ChainLeaf.ram 1)) 4 ChainMenu.ramType2 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [ChainMenu.mem_msMenu]
    refine ⟨by simp, ?_⟩
    intro m hm
    rw [List.mem_singleton] at hm
    omega
  · rw [ChainMenu.chainLeaves, if_pos rfl, Finset.mem_image]
    exact ⟨1, by rw [Finset.mem_Icc]; omega, by norm_num⟩

/-- The depth-0 split family `chain 0 [] (split 1)` is a well-formed summand of the
type-`{(1,1),(1,1)}` count at `N = 5`. -/
theorem w6cSplit_index_ok :
    FullFaithful.W6FiberOK
      (FullFaithful.W6Fiber.chain 0 [] (ChainMenu.ChainLeaf.split 1)) 5
      ChainMenu.splitType2 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [ChainMenu.mem_msMenu]
    exact ⟨by simp, fun m hm => absurd hm List.not_mem_nil⟩
  · rw [ChainMenu.chainLeaves,
      if_neg (fun hcon => absurd (congrArg FactorizationType.data hcon) (by decide)),
      if_neg (fun hcon => absurd (congrArg FactorizationType.data hcon) (by decide)),
      if_pos rfl, Finset.mem_image]
    exact ⟨1, by rw [Finset.mem_Icc]; omega, rfl⟩

/-- The depth-0 inert literal `chainLit [] (inert 1)` is on the scope-#5 menu
`omMenu6 2 1 1 inertType2` — via the NEW `chainShapes0` leg (it is on NO earlier menu:
`chainShapes` filters `ms ≠ []`). -/
theorem w6cInert_mem_omMenu6 :
    ChainMenu.chainLit [] (ChainMenu.ChainLeaf.inert 1)
      ∈ ChainMenu6.omMenu6 2 1 1 ChainMenu.inertType2 := by
  refine ChainMenu6.mem_omMenu6_cases.mpr
    (Or.inr ⟨rfl, ChainMenu.ChainLeaf.inert 1, ?_, rfl⟩)
  rw [ChainMenu.chainLeaves,
    if_neg (fun hcon => absurd (congrArg FactorizationType.data hcon) (by decide)),
    if_pos rfl, Finset.mem_image]
  exact ⟨1, by rw [Finset.mem_Icc]; omega, rfl⟩

/-- The depth-0 inert witness inhabits the `fiberOf5` fiber of the NEW depth-0 literal —
the scope-#5 menu instance of the axiom is NOT vacuous (the anti-vacuity leg of blueprint
§3 at the new emission). -/
theorem w6cInertFiber5_nonempty :
    OmLeafFaithful.fiberOf5 M9.realP 2 5 (by norm_num)
      (ChainMenu.chainLit [] (ChainMenu.ChainLeaf.inert 1))
      w6cInertPoly w6cInertPoly_monic w6cInertPoly_natDegree := by
  rw [OmLeafFaithful.fiberOf5_chain M9.realP 2 5 (by norm_num)
      (ChainMenu.headOrd_chainLit _ _) _ _ _,
    ChainMenu.decodeMs_chainLit, ChainMenu.decodeLeaf_chainLit]
  unfold ChainMenu.ChainCell
  have hcoeff : ∀ i, ((PadicLift.toBox M9.realP 2 5 (by norm_num) w6cInertPoly
      w6cInertPoly_monic w6cInertPoly_natDegree).1).coeff i
      = PadicInt.toZModPow 5 (w6cInertPoly.coeff i) := by
    intro i
    rw [PadicLift.toBox_val, Polynomial.coeff_map]
  rw [hcoeff 0, hcoeff 1]
  exact w6cInertPair_mem

/-- The depth-0 split witness lies in the model's counted fiber `TransChain 0 [] (split 1)`
(the `c = 0` translate is the identity — `transMap_zero`). -/
theorem w6cSplitTransFiber_nonempty :
    SeriesAssembly.TransChain 0 [] (ChainMenu.ChainLeaf.split 1) 5
      (PadicInt.toZModPow 5 (w6cSplitPoly.coeff 0),
        PadicInt.toZModPow 5 (w6cSplitPoly.coeff 1)) := by
  show ChainMenu.ChainPair M9.realP [] (ChainMenu.ChainLeaf.split 1) 5 5
    (SeriesAssembly.transMap 0 5 _)
  rw [SeriesAssembly.transMap_zero]
  exact w6cSplitPair_mem

end Membership

/-! ## Block 3 — the type-consequence gates (each witness fires a landed W6c payload) -/

section Gates

/-- **Gate (depth-0 inert, AXIOM-FREE forcing)**: the inert witness is irreducible over ℚ_2
and EVERY `LocalFactorData` bundle on it carries `(e, f) = (1, 2)` — the (I) master at the
witness's `LeafPair` fiber (`leafFiber_inert_forced`). This is the machine guard behind the
axiom's keying at the NEW depth-0 inert menu leg. -/
theorem gate_w6c_inert_forced :
    Irreducible (w6cInertPoly.map (algebraMap ℤ_[M9.realP] ℚ_[M9.realP]))
      ∧ ∀ D : QpType.LocalFactorData M9.realP w6cInertPoly,
          QpType.eOf M9.realP D = 1 ∧ QpType.fOf M9.realP D = 2 :=
  leafFiber_inert_forced M9.realP (by decide) le_rfl
    w6cInertPoly_monic w6cInertPoly_natDegree w6cInertPair_mem

/-- **Gate (depth-0 split, AXIOM-FREE certificate through the assembled corollary)**: the
split witness has a genuine certificate of type `{(1,1),(1,1)}`, obtained from
`fullFiber_split_hasType_axfree` at the model family `chain 0 [] (split 1)` — the split-keyed
legs of the scope-#5 theorem are PROVED, no axiom. -/
theorem gate_w6c_split_hasType_axfree :
    ∃ Fc : QpType.QpFactorization M9.realP w6cSplitPoly,
      QpType.qpType M9.realP Fc = ChainMenu.splitType2 :=
  FullFaithful.fullFiber_split_hasType_axfree (by norm_num) w6cSplit_index_ok
    (Or.inr ⟨0, [], 1, rfl⟩) w6cSplitPoly_monic w6cSplitPoly_natDegree
    w6cSplitTransFiber_nonempty

/-- **Gate (`c = 1` translate ram — THE assembled theorem end-to-end at a witness)**:
`fullFiber_hasType` at the family `chain 1 [1] (ram 1)` hands the translate witness a
genuine certificate of type `{(2,1)}`. This exercises, in one firing: the `W6FiberOK`
index, the `TransChain` fiber, the derived translate reduction, the scope-#5 menu, the
re-scoped axiom, and the proved transport. Footprint: core + `om_leaf_faithful` EXACTLY. -/
theorem gate_w6c_trans_hasType :
    ∃ Fc : QpType.QpFactorization M9.realP w6cTransPoly,
      QpType.qpType M9.realP Fc = ChainMenu.ramType2 :=
  FullFaithful.fullFiber_hasType (by norm_num) w6cTrans_index_ok
    w6cTransPoly_monic w6cTransPoly_natDegree w6cTransFiber_nonempty

/-- **Gate (general-`m` deep chain, AXIOM-FREE forcing)**: the `m = 2` witness is
irreducible over ℚ_2 and every bundle carries `(2, 1)` — the unwind + (R) master at depth
`[2]` (`chainFiber_ram_forced`), exercising the general-`m` step decode beyond the banked
`m = 1` anchors. -/
theorem gate_w6c_deep_forced :
    Irreducible (w6cDeepPoly.map (algebraMap ℤ_[M9.realP] ℚ_[M9.realP]))
      ∧ ∀ D : QpType.LocalFactorData M9.realP w6cDeepPoly,
          QpType.eOf M9.realP D = 2 ∧ QpType.fOf M9.realP D = 1 :=
  chainFiber_ram_forced M9.realP
    (fun m hm => by rw [List.mem_singleton] at hm; omega)
    ⟨0, by norm_num⟩ (by decide) le_rfl
    w6cDeepPoly_monic w6cDeepPoly_natDegree w6cDeepFiber_nonempty

/-- **Positive coherence gate (probe leg 3 at the NEW depth-0 menu leg)**: the REAL axiom
`om_leaf_faithful`, fired at the depth-0 inert witness THROUGH its `omMenu6` membership
(the scope-#5 emission `chainShapes0` — on no earlier menu), yields a certificate of type
`{(1,2)}` COEXISTING with the proved irreducibility. Where the recorded split-keying
mutation derives `False` (evidence block below), the real conclusion is consistent — the
two legs together pin the axiom's keying at the new leg. Footprint: core +
`om_leaf_faithful` EXACTLY (mirrors `chainGate_axiom_coherent`). -/
theorem gate_w6c_axiom_coherent :
    ∃ (f0 : Polynomial ℤ_[M9.realP]) (F : QpType.QpFactorization M9.realP f0),
      QpType.qpType M9.realP F = ChainMenu.inertType2 ∧
      Irreducible (f0.map (algebraMap ℤ_[M9.realP] ℚ_[M9.realP])) := by
  obtain ⟨F, hF⟩ := OmLeafFaithful.om_leaf_faithful M9.realP 2 5 (by norm_num)
    ChainMenu.inertType2 (ChainMenu.chainLit [] (ChainMenu.ChainLeaf.inert 1)) 1 1
    w6cInert_mem_omMenu6 w6cInertPoly w6cInertPoly_monic w6cInertPoly_natDegree
    w6cInertFiber5_nonempty
  exact ⟨w6cInertPoly, F, hF, gate_w6c_inert_forced.1⟩

end Gates

/-! ## Block 4 — the capstone companion (packaging, NOT a capstone change) -/

section Companion

/-- **`montes_n2_full_faithful` — the W6 capstone paired with scope-#5 faithfulness.** The
FIRST conjunct is VERBATIM the conclusion of `SeriesAssembly.montes_unconditional_n2_full`
(the Wave-6 capstone, untouched, still core-only at its own name): uniform rationality,
the unconditional full-density tie, conditional palindromy (`htameFE`), and unconditional
bracket uniqueness (`hExhaust` proved) for the full `n = 2` model. The SECOND conjunct is
`FullFaithful.fullFiber_hasType`: every fiber the model counts carries Montes-faithful
σ-keying. Footprint of THIS pairing: Lean core + `om_leaf_faithful` (the faithfulness
clause's honest cost; the counting clause contributes no axiom). -/
theorem montes_n2_full_faithful (σ : FactorizationType) (hσ : σ.degree = 2)
    (htameFE : TameFunctionalEquation SeriesAssembly.realFW6 2 σ) :
    ((∃ (num den : Polynomial ℚ), den ≠ 0 ∧
        (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
          (∑ T ∈ SeriesAssembly.shapesOf6 σ, SeriesAssembly.C6 T q')
            = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
        (SeriesAssembly.realMW6.countingDensity σ
          = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
        IsPalindromic num den) ∧
      ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
          SeriesAssembly.realMW6.decidedCount σ N / (M9.realP : ℚ) ^ (2 * N) ≤ d ∧
          d ≤ SeriesAssembly.realMW6.decidedCount σ N / (M9.realP : ℚ) ^ (2 * N)
                + SeriesAssembly.realMW6.undecidedCount N / (M9.realP : ℚ) ^ (2 * N)) →
        d = SeriesAssembly.realMW6.countingDensity σ) ∧
    (∀ (N : ℕ), 0 < N → ∀ (F : FullFaithful.W6Fiber),
      FullFaithful.W6FiberOK F N σ →
      ∀ (f : Polynomial ℤ_[M9.realP]), f.Monic → f.natDegree = 2 →
        FullFaithful.fiberPred F N
          (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1)) →
        ∃ Fc : QpType.QpFactorization M9.realP f, QpType.qpType M9.realP Fc = σ) :=
  ⟨SeriesAssembly.montes_unconditional_n2_full σ hσ htameFE,
    fun _N hN _F hOK _f hf hdeg hfib =>
      FullFaithful.fullFiber_hasType hN hOK hf hdeg hfib⟩

end Companion

/-! ## Block 5 — W6c-d mutation probe evidence (machine-checked 2026-07-22, scratch NOT
committed)

**The two wrong-keying mutations at the NEW scope-#5 fiber families** — (A) the re-scoped
axiom's hypotheses VERBATIM (over `ChainMenu6.omMenu6` with `fiberOf5`), conclusion replaced
by the SPLIT type `{(1,1),(1,1)}`, fired at the DEPTH-0 INERT leg; (B) the assembled
theorem's hypotheses VERBATIM (`W6FiberOK` + `fiberPred`, the `fullFiber_hasType` shape),
conclusion replaced by the fine-`(e,f)`-swapped singleton `{(1,2)}`, fired at the `c = 1`
TRANSLATE ram leg — were compiled against this module, `OM/FullFaithful.lean` and
`OM/OmLeafFaithful.lean`, and `lake env lean` accepted the following scratch with zero
errors: `False` DERIVES from each mutated statement + the inhabited fibers
(`w6cInertFiber5_nonempty` / `w6cTransFiber_nonempty`) + the AXIOM-FREE forcing anchors
(`gate_w6c_inert_forced`'s irreducibility + `not_irreducible_of_two_factors` for (A);
`QpTypeChainAll.transChainFiber_ram_forced` — `(2,1)` forced on EVERY bundle — +
`QpTypeEisenstein.qpType_singleton_forces` for (B)). The real `om_leaf_faithful` appears in
NEITHER refutation cone (footprints below: core + the mutated axiom ONLY); the positive
check `gate_w6c_axiom_coherent` (Block 3) consumes exactly core + the real axiom. With the
recorded W5c probes (`OM/QpTypeChain.lean` Block 7b, `OM/QpTypeChainLeaves.lean` Block 7),
every n = 2 fiber family of the FULL model — order-0, depth-1 chains, depth-0 leaf
literals, and the c = 1 translates — is now pinned against wrong-type keyings.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.FullFaithful
import LeanUrat.OM.FullFaithfulGates

namespace LeanUrat.OM.FullFaithfulGatesScratch

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.FullFaithfulGates

axiom om_leaf_faithful_MUTATED_leafinertsplit (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu6.omMenu6 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

theorem mutation_leafinertsplit_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_leafinertsplit M9.realP 2 5 (by norm_num)
    ChainMenu.inertType2 (ChainMenu.chainLit [] (ChainMenu.ChainLeaf.inert 1)) 1 1
    w6cInert_mem_omMenu6 w6cInertPoly w6cInertPoly_monic w6cInertPoly_natDegree
    w6cInertFiber5_nonempty
  have hirr := gate_w6c_inert_forced.1
  have hlen : F.factors.length = 2 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  exact QpTypeChainLeaves.not_irreducible_of_two_factors M9.realP F hlen hirr

axiom fullFiber_MUTATED_transinert (N : ℕ) (hN : 0 < N) (σ : FactorizationType)
    (F : FullFaithful.W6Fiber) (hOK : FullFaithful.W6FiberOK F N σ)
    (f : Polynomial ℤ_[M9.realP]) (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : FullFaithful.fiberPred F N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    ∃ Fc : QpType.QpFactorization M9.realP f,
      QpType.qpType M9.realP Fc = (⟨{((1 : ℕ), (2 : ℕ))}⟩ : FactorizationType)

theorem mutation_transinert_refuted : False := by
  obtain ⟨Fc, hFc⟩ := fullFiber_MUTATED_transinert 4 (by norm_num) ChainMenu.ramType2
    (FullFaithful.W6Fiber.chain 1 [1] (ChainMenu.ChainLeaf.ram 1)) w6cTrans_index_ok
    w6cTransPoly w6cTransPoly_monic w6cTransPoly_natDegree w6cTransFiber_nonempty
  obtain ⟨hmem, hef⟩ := QpTypeEisenstein.qpType_singleton_forces M9.realP Fc
    ((1 : ℕ), (2 : ℕ)) hFc
  obtain ⟨-, hforce⟩ := QpTypeChainAll.transChainFiber_ram_forced
    (fun m hm => by rw [List.mem_singleton] at hm; omega) ⟨0, by norm_num⟩ (by decide)
    w6cTransPoly_monic w6cTransPoly_natDegree w6cTransFiber_nonempty
  have h21 := hforce (Fc.data w6cTransPoly hmem)
  have hef2 : QpType.efOf M9.realP (Fc.data w6cTransPoly hmem) = (2, 1) := by
    unfold QpType.efOf
    rw [h21.1, h21.2]
  rw [hef] at hef2
  exact absurd hef2 (by decide)

end LeanUrat.OM.FullFaithfulGatesScratch

#print axioms LeanUrat.OM.FullFaithfulGatesScratch.mutation_leafinertsplit_refuted
#print axioms LeanUrat.OM.FullFaithfulGatesScratch.mutation_transinert_refuted
```

`lake env lean` output on the scratch (2026-07-22): NO errors; exactly the two info lines

```
'LeanUrat.OM.FullFaithfulGatesScratch.mutation_leafinertsplit_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.FullFaithfulGatesScratch.om_leaf_faithful_MUTATED_leafinertsplit]
'LeanUrat.OM.FullFaithfulGatesScratch.mutation_transinert_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.FullFaithfulGatesScratch.fullFiber_MUTATED_transinert]
```

i.e. `False` follows from each MUTATED statement + Lean core + PROVED theorems alone — the
real `om_leaf_faithful` appears in neither cone. -/

/-! ## Block 6 — axiom census

Expected footprints: `gate_w6c_trans_hasType` / `gate_w6c_axiom_coherent` /
`montes_n2_full_faithful` = Lean core + `LeanUrat.OM.OmLeafFaithful.om_leaf_faithful`
EXACTLY; EVERYTHING ELSE (witnesses, fiber memberships, index/menu memberships, the
axiom-free gates) = Lean core only. Any OTHER axiom appearing anywhere is a FAILURE. -/

section AxCheck

#print axioms LeanUrat.OM.FullFaithfulGates.w6cInertPoly
#print axioms LeanUrat.OM.FullFaithfulGates.w6cInertPoly_monic
#print axioms LeanUrat.OM.FullFaithfulGates.w6cInertPoly_natDegree
#print axioms LeanUrat.OM.FullFaithfulGates.w6cInertPair_mem
#print axioms LeanUrat.OM.FullFaithfulGates.w6cSplitPoly
#print axioms LeanUrat.OM.FullFaithfulGates.w6cSplitPair_mem
#print axioms LeanUrat.OM.FullFaithfulGates.w6cTransPoly
#print axioms LeanUrat.OM.FullFaithfulGates.w6cTransPoly_comp
#print axioms LeanUrat.OM.FullFaithfulGates.w6cTransFiber_nonempty
#print axioms LeanUrat.OM.FullFaithfulGates.w6cDeepPoly
#print axioms LeanUrat.OM.FullFaithfulGates.w6cDeepFiber_nonempty
#print axioms LeanUrat.OM.FullFaithfulGates.w6cTrans_index_ok
#print axioms LeanUrat.OM.FullFaithfulGates.w6cSplit_index_ok
#print axioms LeanUrat.OM.FullFaithfulGates.w6cInert_mem_omMenu6
#print axioms LeanUrat.OM.FullFaithfulGates.w6cInertFiber5_nonempty
#print axioms LeanUrat.OM.FullFaithfulGates.w6cSplitTransFiber_nonempty
#print axioms LeanUrat.OM.FullFaithfulGates.gate_w6c_inert_forced
#print axioms LeanUrat.OM.FullFaithfulGates.gate_w6c_split_hasType_axfree
#print axioms LeanUrat.OM.FullFaithfulGates.gate_w6c_trans_hasType
#print axioms LeanUrat.OM.FullFaithfulGates.gate_w6c_deep_forced
#print axioms LeanUrat.OM.FullFaithfulGates.gate_w6c_axiom_coherent
#print axioms LeanUrat.OM.FullFaithfulGates.montes_n2_full_faithful

end AxCheck

end LeanUrat.OM.FullFaithfulGates
