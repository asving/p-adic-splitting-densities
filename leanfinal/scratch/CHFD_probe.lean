import Uniformity.ChapI.I10_I15_I18
import Uniformity.ChapC.C130sg
import Uniformity.ChapH.H97b

/-!
CHFD load-bearing probes.  No declaration of an axiom and no `sorry`.
-/

namespace CHFDProbe

open Polynomial IsLocalRing
open Uniformity Uniformity.Density

universe uW uG uKt uL

-- The current landed I.01 supply has exactly the field's landed type.
#check ns7Termination_of_cite

-- These are socket-antecedent teeth at input degree 4 (and depth 2), not degree 2 capstone
-- suppliers and not proofs of either field's conclusion.
#check @Uniformity.Density.Tower.C130sg.s2Frontier_ladder_socket
#check @Uniformity.Density.Tower.C130sg.s2Frontier_deepTwist_socket

-- Public-name candidate for the anonymous I.02 degree-two gate.
theorem decidedSliceAt_two : DecidedSliceAt 2 := by
  intro σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := uniformityStatement_two σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨h1, h2⟩ := hlaw O
  exact ⟨h1, by rw [← genuineDensity_eq_decidedDensity_two]; exact h2⟩

private def a1LabelCell (σ : FactorizationType) : Induction.A1Cell 0 where
  offset := fun i => i.elim0
  stride := fun i => i.elim0
  stride_pos := fun i => i.elim0
  expCoeff := fun i => i.elim0
  expCoeff_pos := fun i => i.elim0
  expConst := 0
  visCoeff := fun i => i.elim0
  visConst := 0
  coeff := 1
  σ := σ

-- Public-name candidate for the anonymous I.03 degree-two gate.
theorem menuLawAt_two : MenuLawAt 2 := by
  refine ⟨0, [a1LabelCell splitType, a1LabelCell inertType, a1LabelCell ramType],
    {splitType, inertType, ramType}, ?_, ?_, ?_, ?_⟩
  · intro C hC
    simp only [id_eq, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with h | h | h <;> subst h <;> simp [a1LabelCell]
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    · exact ⟨a1LabelCell splitType, by simp, rfl⟩
    · exact ⟨a1LabelCell inertType, by simp, rfl⟩
    · exact ⟨a1LabelCell ramType, by simp, rfl⟩
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    exacts [splitType_degree, inertType_degree, ramType_degree]
  · intro O _ _ _ _ _
    exact coveringMenu_two

-- The cubic menu half is already landed.  This probe supplies only the mechanical A1 label
-- family which `MenuLawAt` additionally requests.
theorem menuLawAt_three : MenuLawAt 3 := by
  refine ⟨0,
    [a1LabelCell c3split, a1LabelCell c3linInert, a1LabelCell c3inert,
      a1LabelCell c3linRam, a1LabelCell c3ram],
    {c3split, c3linInert, c3inert, c3linRam, c3ram}, ?_, ?_, ?_, ?_⟩
  · intro C hC
    simp only [id_eq, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with h | h | h | h | h <;> subst h <;> simp [a1LabelCell]
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h | h | h <;> subst h
    · exact ⟨a1LabelCell c3split, by simp, rfl⟩
    · exact ⟨a1LabelCell c3linInert, by simp, rfl⟩
    · exact ⟨a1LabelCell c3inert, by simp, rfl⟩
    · exact ⟨a1LabelCell c3linRam, by simp, rfl⟩
    · exact ⟨a1LabelCell c3ram, by simp, rfl⟩
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h | h | h <;> subst h
    exacts [c3_degrees.1, c3_degrees.2.1, c3_degrees.2.2.1,
      c3_degrees.2.2.2.1, c3_degrees.2.2.2.2]
  · intro O _ _ _ _ _
    exact coveringMenu_three

theorem drainageAt_two : DrainageAt 2 := by
  intro O _ _ _ _ _ σ
  exact drainage_two σ

-- All current stub/guard fields at n=2 are mechanical.
example : True := True.intro
example : 6 ≤ 2 → True := fun _ => True.intro
example : WindowPinningAt 2 := True.intro
example : 6 ≤ 2 → GenhnHEAt 2 := by omega
example : 8 ≤ 2 → GenhnTow1At 2 := by omega

-- The depth-two S2 deep-twist conclusion is empty.  This does not prove the universal
-- Capstone field, whose guard may contain witnesses at other depths.
theorem deepTwistConjunctLive_two
    {G : Type*} [CommGroup G] {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] {N : Gauge.NormSection G}
    (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G K N) (R : ℕ → G → K) (w : ℕ → Kˣ) :
    Ladder.DeepTwistConjunctLive 2 v ρ q A R w := by
  intro i hi
  rcases hi with ⟨hi3, hi2⟩
  omega

-- The exact current n=2 assembly boundary: after the three easy fields above, only ns7 and
-- the two universal socket-to-supply functions remain inputs.  Keeping ns7 explicit makes
-- this constructor Lean-core; callers may separately use the declared C.94 cite.
theorem capstoneHypotheses_two_of_core
    (hns : NS7Termination)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q 2 →
      -- [A-I.6, 2026-08-28] rebound with the capstone field: the live-range record.
      -- [A-I.7, 2026-08-28] rebound again with the capstone field: the live-MP1 record.
      -- [A-I.8, 2026-08-28] rebound again with the capstone field: the direct-MP1 record.
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q 2)
    (hdeep : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r 2 →
      Ladder.DeepTwistConjunctLive r v ρ q A R w) :
    CapstoneHypotheses.{uW, uG, uKt, uL} 2 where
  ns7 := hns
  ladder := hladder
  deepTwist := hdeep
  a0 := decidedSliceAt_two
  a1 := menuLawAt_two
  a2 := drainageAt_two
  jd0 := True.intro
  genhnBox2 := fun _ => True.intro
  windowPinning := True.intro
  genhnHE := by omega
  genhnTow1 := by omega

#print axioms CHFDProbe.decidedSliceAt_two
#print axioms CHFDProbe.menuLawAt_two
#print axioms CHFDProbe.menuLawAt_three
#print axioms CHFDProbe.drainageAt_two
#print axioms CHFDProbe.deepTwistConjunctLive_two
#print axioms CHFDProbe.capstoneHypotheses_two_of_core
#print axioms Uniformity.Density.ns7Termination_of_cite

end CHFDProbe
