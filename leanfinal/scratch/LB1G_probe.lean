/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC0
import Uniformity.ChapC.C130sg
import Uniformity.ChapE.E57p

/-!
# LB1G probes: the landed S2 mass-one obstruction and the honest restricted carrier shape

This file does not refute `LB1Carrier` at the landed S2 pair.  It records the obstruction
encountered by the malicious-interface attempt: the landed block has mass `1`, and every
`RungInterface` on a mass-one block has exactly one side.  It also checks the generic
restriction/supersession shape, parameterized by the (currently missing) C-to-E interface-export
predicate.

There is no `sorry` and no new axiom.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.LB1GProbe

open Polynomial IsLocalRing
open Uniformity.Density

universe uO uK uW uL

/-! ## 1. The landed S2 block has mass one -/

section S2

open Tower

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {L : Type uL} [Field L] [Algebra ((C130s17.S2DepthTwo h2 hq).fld 2) L]

/-- The block exported by the landed S2 realization has mass `1`. -/
theorem s2_exported_block_mu_one [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : C130sg.S2LevelOneThreshold) :
    ((C130sg.s2Frontier h2 hq L w).s2RealizedInput.inputBlockTransport
      (RingEquiv.refl ((C130s17.S2DepthTwo h2 hq).fld 2))).μ = 1 := rfl

end S2

/-! ## 2. Mass one rules out the multi-side trigger -/

/-- Every legal rung interface over a mass-one block has exactly one side.  Thus the two-side
malicious interface used by the abstract A-E.2 non-triviality certificate cannot be transported
to the landed S2 block. -/
theorem rungInterface_card_eq_one_of_mu_eq_one
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C} (hmu : B.μ = 1)
    (I : Ladder.RungInterface.{uO, uK, uW} C B) : I.sides.card = 1 := by
  have hcard_le : I.sides.card ≤ ∑ p ∈ I.sides, I.len p := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun p hp => I.hlen_pos p hp
  have hnonempty : I.sides.Nonempty := by
    by_contra h
    have hsum := I.hlen_sum
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    have := B.hμ
    omega
  have hpos : 0 < I.sides.card := Finset.card_pos.mpr hnonempty
  rw [I.hlen_sum, hmu] at hcard_le
  omega

/-- In particular, the multi-side half of the LB1 trigger is false on every mass-one block. -/
theorem not_multi_of_mu_eq_one
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C} (hmu : B.μ = 1)
    (I : Ladder.RungInterface.{uO, uK, uW} C B) : ¬ 1 < I.sides.card := by
  rw [rungInterface_card_eq_one_of_mu_eq_one hmu I]
  omega

/-- Every side of a mass-one interface is separable.  This uses all three load-bearing
arithmetic groups: residual degree, forced class-count lower bounds, and exhaustion. -/
theorem rungInterface_sep_of_mu_eq_one
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C} (hmu : B.μ = 1)
    (I : Ladder.RungInterface.{uO, uK, uW} C B) :
    ∀ p ∈ I.sides, I.SepSide p := by
  letI := Classical.decEq K
  intro p hp
  have hlen_le : I.len p ≤ ∑ r ∈ I.sides, I.len r :=
    Finset.single_le_sum (fun r _ => Nat.zero_le (I.len r)) hp
  have hsum := I.hlen_sum
  rw [hmu] at hsum
  have hlen_upper : I.len p ≤ 1 := hlen_le.trans_eq hsum
  have hlen : I.len p = 1 := le_antisymm hlen_upper (I.hlen_pos p hp)
  have hres := I.hresdeg p hp
  rw [hlen] at hres
  have hpden : p.2 = 1 :=
    Nat.eq_one_of_dvd_one ⟨_, hres.symm⟩
  have hresTotal :
      Multiset.sum ((I.linFac p).map Prod.snd) +
        Multiset.sum ((I.hiFac p).map fun q => q.1 * q.2) = 1 := by
    simpa [hpden] using hres
  have hcountTotal := I.hexhaust p hp
  rw [I.haccount p hp, hlen] at hcountTotal
  simp at hcountTotal
  have hnonempty := I.hnonempty p hp
  have hforce := I.hforce p hp
  have hD := C.hD
  constructor
  · intro q hq
    have hq_le_lin : q.2 ≤ Multiset.sum ((I.linFac p).map Prod.snd) :=
      Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.snd hq)
    have hq_le_one : q.2 ≤ 1 := by omega
    by_contra hq_ne
    have hq_zero : q.2 = 0 := by omega
    have hcons := Multiset.cons_erase hq
    have hrest : (I.linFac p).erase q ≠ 0 ∨ I.hiFac p ≠ 0 := by
      by_contra hn
      push Not at hn
      obtain ⟨hlin, hhi⟩ := hn
      have ht := hresTotal
      rw [← hcons, hlin, hhi] at ht
      simp [hq_zero] at ht
    have hc := hcountTotal
    rw [← hcons] at hc
    simp only [Multiset.map_cons, Multiset.sum_cons] at hc
    have hq_force : C.D ≤ I.classCount p q := by simpa [hpden] using hforce.1 q hq
    rcases hrest with hlin | hhi
    · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hlin
      have hr0 : r ∈ I.linFac p := Multiset.mem_of_mem_erase hr
      have hr_pos : 1 ≤ I.classCount p r := hnonempty.1 r hr0
      have hr_le : I.classCount p r ≤
          Multiset.sum (((I.linFac p).erase q).map (I.classCount p)) :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (I.classCount p) hr)
      omega
    · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hhi
      have hr_pos : 1 ≤ I.classCountHi p r := hnonempty.2 r hr
      have hr_le : I.classCountHi p r ≤
          Multiset.sum ((I.hiFac p).map (I.classCountHi p)) :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (I.classCountHi p) hr)
      omega
  · intro q hq
    have hqprod_le_hi : q.1 * q.2 ≤
        Multiset.sum ((I.hiFac p).map fun r => r.1 * r.2) :=
      Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun r => r.1 * r.2) hq)
    have hqprod_le_one : q.1 * q.2 ≤ 1 := by omega
    have hcons := Multiset.cons_erase hq
    have hc := hcountTotal
    rw [← hcons] at hc
    simp only [Multiset.map_cons, Multiset.sum_cons] at hc
    have hqfirst_pos : 0 < q.1 := by
      by_contra hqfirst
      have hqfirst_zero : q.1 = 0 := Nat.eq_zero_of_not_pos hqfirst
      have ht := hresTotal
      rw [← hcons] at ht
      simp only [Multiset.map_cons, Multiset.sum_cons] at ht
      have hpositive :
          Multiset.sum ((I.linFac p).map Prod.snd) ≠ 0 ∨
            Multiset.sum (((I.hiFac p).erase q).map fun r => r.1 * r.2) ≠ 0 := by
        simp [hqfirst_zero] at ht
        omega
      have hq_pos : 1 ≤ I.classCountHi p q := hnonempty.2 q hq
      rcases hpositive with hlin | hhi
      · have hex : ∃ r ∈ I.linFac p, r.2 ≠ 0 := by
          by_contra hn
          push Not at hn
          apply hlin
          rw [Multiset.sum_eq_zero_iff]
          intro x hx
          obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
          exact hn r hr
        obtain ⟨r, hr, -⟩ := hex
        have hr_force : C.D ≤ I.classCount p r := by simpa [hpden] using hforce.1 r hr
        have hr_le : I.classCount p r ≤
            Multiset.sum ((I.linFac p).map (I.classCount p)) :=
          Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (I.classCount p) hr)
        omega
      · have hex : ∃ r ∈ (I.hiFac p).erase q, r.1 * r.2 ≠ 0 := by
          by_contra hn
          push Not at hn
          apply hhi
          rw [Multiset.sum_eq_zero_iff]
          intro x hx
          obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
          exact hn r hr
        obtain ⟨r, hr, hrnz⟩ := hex
        have hr0 : r ∈ I.hiFac p := Multiset.mem_of_mem_erase hr
        have hrfirst : 0 < r.1 := Nat.pos_of_ne_zero (fun hz => hrnz (by simp [hz]))
        have hr_force0 := hforce.2 r hr0
        have hr_force : C.D ≤ I.classCountHi p r := by
          rw [hpden, mul_one] at hr_force0
          exact le_trans (Nat.le_mul_of_pos_right C.D hrfirst) hr_force0
        have hr_le : I.classCountHi p r ≤
            Multiset.sum (((I.hiFac p).erase q).map (I.classCountHi p)) :=
          Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (I.classCountHi p) hr)
        omega
    have hqsecond_le_prod : q.2 ≤ q.1 * q.2 := by
      simpa using Nat.mul_le_mul_right q.2 hqfirst_pos
    have hqsecond_le_one : q.2 ≤ 1 := hqsecond_le_prod.trans hqprod_le_one
    by_contra hqsecond_ne
    have hqsecond_zero : q.2 = 0 := by omega
    have ht := hresTotal
    rw [← hcons] at ht
    simp only [Multiset.map_cons, Multiset.sum_cons] at ht
    have hpositive :
        Multiset.sum ((I.linFac p).map Prod.snd) ≠ 0 ∨
          Multiset.sum (((I.hiFac p).erase q).map fun r => r.1 * r.2) ≠ 0 := by
      simp [hqsecond_zero] at ht
      omega
    have hq_force0 := hforce.2 q hq
    have hq_force : C.D ≤ I.classCountHi p q := by
      rw [hpden, mul_one] at hq_force0
      exact le_trans (Nat.le_mul_of_pos_right C.D hqfirst_pos) hq_force0
    rcases hpositive with hlin | hhi
    · have hex : ∃ r ∈ I.linFac p, r.2 ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hlin
        rw [Multiset.sum_eq_zero_iff]
        intro x hx
        obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
        exact hn r hr
      obtain ⟨r, hr, -⟩ := hex
      have hr_force : C.D ≤ I.classCount p r := by simpa [hpden] using hforce.1 r hr
      have hr_le : I.classCount p r ≤
          Multiset.sum ((I.linFac p).map (I.classCount p)) :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (I.classCount p) hr)
      omega
    · have hex : ∃ r ∈ (I.hiFac p).erase q, r.1 * r.2 ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hhi
        rw [Multiset.sum_eq_zero_iff]
        intro x hx
        obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
        exact hn r hr
      obtain ⟨r, hr, hrnz⟩ := hex
      have hr0 : r ∈ I.hiFac p := Multiset.mem_of_mem_erase hr
      have hrfirst : 0 < r.1 := Nat.pos_of_ne_zero (fun hz => hrnz (by simp [hz]))
      have hr_force0 := hforce.2 r hr0
      have hr_force : C.D ≤ I.classCountHi p r := by
        rw [hpden, mul_one] at hr_force0
        exact le_trans (Nat.le_mul_of_pos_right C.D hrfirst) hr_force0
      have hr_le : I.classCountHi p r ≤
          Multiset.sum (((I.hiFac p).erase q).map (I.classCountHi p)) :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (I.classCountHi p) hr)
      omega

/-- Therefore the full LB1 trigger is false on every mass-one block. -/
theorem not_lb1_trigger_of_mu_eq_one
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C} (hmu : B.μ = 1)
    (I : Ladder.RungInterface.{uO, uK, uW} C B) :
    ¬ (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) := by
  rintro (hmulti | ⟨p, hp, hnsep⟩)
  · exact not_multi_of_mu_eq_one hmu I hmulti
  · exact hnsep (rungInterface_sep_of_mu_eq_one hmu I p hp)

/-- On a mass-one block the unrestricted `LB1Carrier` is true, but only vacuously: no legal
interface reaches its trigger. -/
theorem lb1Carrier_of_mu_eq_one
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C} (hmu : B.μ = 1) :
    Ladder.LB1Carrier.{uO, uK, uW} C B :=
  fun I htrigger => (not_lb1_trigger_of_mu_eq_one hmu I htrigger).elim

section S2Conclusion

open Tower

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {L : Type uL} [Field L] [Algebra ((C130s17.S2DepthTwo h2 hq).fld 2) L]

/-- The unrestricted LB1 carrier actually holds at the landed S2 pair, but only because its
mass-one exported block admits no triggering interface.  Hence this occurrence cannot refute the
arbitrary-interface quantifier. -/
theorem s2_unrestricted_lb1_vacuous [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : C130sg.S2LevelOneThreshold) :
    Ladder.LB1Carrier.{0, 0, uW}
      ((C130sg.s2Frontier h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((C130s17.S2DepthTwo h2 hq).fld 2)))
      ((C130sg.s2Frontier h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((C130s17.S2DepthTwo h2 hq).fld 2))) :=
  lb1Carrier_of_mu_eq_one (s2_exported_block_mu_one h2 hq w)

end S2Conclusion

/-! ## 3. Exact restricted carrier shape -/

/-- The honest E-layer restriction: `Exported I` is the C-to-E relation saying that `I` is the
rung interface exported by a realization witnessing the same external socket data.  That
relation is deliberately an explicit parameter here because no such exporter/relation is landed.
Instantiating it with `fun _ => True` recovers the unrestricted carrier. -/
def LB1CarrierLive {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop) : Prop :=
  ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, Exported I →
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    Nonempty (Ladder.BlockSuite I)

/-- Supersession direction: the old arbitrary-interface carrier implies every restricted twin. -/
theorem lb1CarrierLive_of_unrestricted
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop}
    (h : Ladder.LB1Carrier.{uO, uK, uW} C B) :
    LB1CarrierLive.{uO, uK, uW} C B Exported :=
  fun I _ htrigger => h I htrigger

/-- The landed E.57 funnel needs no arbitrary-interface strength: partition legs only for
exported triggering interfaces assemble the restricted carrier. -/
theorem lb1CarrierLive_of_exported_partitionLegs
    {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop}
    (hpart : ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, Exported I →
      (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
      Nonempty (Ladder.PartitionLeg I)) :
    LB1CarrierLive.{uO, uK, uW} C B Exported :=
  fun I hI htrigger => (hpart I hI htrigger).map Ladder.PartitionLeg.toBlockSuite

end Uniformity.Density.LB1GProbe

end

/-! ## Axiom footprint -/

#print axioms Uniformity.Density.LB1GProbe.s2_exported_block_mu_one
#print axioms Uniformity.Density.LB1GProbe.rungInterface_card_eq_one_of_mu_eq_one
#print axioms Uniformity.Density.LB1GProbe.not_multi_of_mu_eq_one
#print axioms Uniformity.Density.LB1GProbe.rungInterface_sep_of_mu_eq_one
#print axioms Uniformity.Density.LB1GProbe.not_lb1_trigger_of_mu_eq_one
#print axioms Uniformity.Density.LB1GProbe.lb1Carrier_of_mu_eq_one
#print axioms Uniformity.Density.LB1GProbe.s2_unrestricted_lb1_vacuous
#print axioms Uniformity.Density.LB1GProbe.LB1CarrierLive
#print axioms Uniformity.Density.LB1GProbe.lb1CarrierLive_of_unrestricted
#print axioms Uniformity.Density.LB1GProbe.lb1CarrierLive_of_exported_partitionLegs
