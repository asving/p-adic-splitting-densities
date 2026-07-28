import Mathlib
import LeanUrat.HC2.Defs

set_option linter.all false
set_option maxHeartbeats 1000000

open LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD Polynomial

namespace LeanUrat.MovesJ

/-- GENERAL OBSTRUCTION at N = 2: ANY `JetSetup` on ANY length-1 history whose only node is a
`g = 2, μ = 1` read has `totalPins = 4`, never 2. The `root_height` field (required) forces
`line.at b ≥ 1` for `b < μ·childWidth = 2e ≥ 2`, i.e. at both base indices 0,1; coherence
forces `Dwidth = 1`; so the frame-0 fresh band `{c : level ≤ line.at(base)}` swallows both
level-0 AND level-1 coordinates at both bases — the whole 4-coordinate box. -/
theorem obstruction_N2 (H : History 2 F4) (hlen : H.nodes.length = 1)
    (J : JetSetup H 2 2 4)
    (hg : ∀ h0 : 0 < H.nodes.length, (H.nodes[0]'h0).g = 2)
    (hμ : ∀ h0 : 0 < H.nodes.length, (H.nodes[0]'h0).μ = 1) :
    totalPins J (topLocus 2 4) = 4 := by
  have hlen0 : 0 < H.nodes.length := by rw [hlen]; norm_num
  set ν := H.nodes[0]'hlen0 with hν
  -- Dwidth = 1 from coherence (root frame deg Φ = 1) + hDwidth.
  have hΦ1 : ν.σ.Φ.natDegree = 1 := J.coherent.1 hlen0
  have hDw : ν.Dwidth = 1 := by rw [ν.hDwidth, hΦ1]
  -- childWidth = e·g·Dwidth = 2e ; μ·childWidth = 2e ≥ 2.
  have hg2 : ν.g = 2 := hg hlen0
  have hμ1 : ν.μ = 1 := hμ hlen0
  have hcw : ν.μ * ν.childWidth = 2 * ν.e := by
    rw [Node.childWidth, hDw, hg2, hμ1]; ring
  have he1 : 1 ≤ ν.e := ν.he
  have hcov : ∀ b : ℕ, b < 2 → b < ν.μ * ν.childWidth := by
    intro b hb; rw [hcw]; omega
  -- root_height: line.at b ≥ 1 for b < 2.
  have hrh : ∀ b : ℕ, b < 2 → (1 : ℚ) ≤ ν.line.at b := fun b hb =>
    J.root_height hlen0 b (hcov b hb)
  -- Every box coordinate is in the frame-0 fresh band.
  have hband : ∀ c : Fin 4, inFreshBand H 2 J.coordOf 0 ν c := by
    intro c
    obtain ⟨hℓ, hb⟩ := J.coordOf_lt c
    -- coordOf_lt gives level < N = 2, base < n = 2
    have hℓ2 : (J.coordOf c).1 < 2 := hℓ
    have hb2 : (J.coordOf c).2 < 2 := hb
    refine ⟨?_, ?_, ?_⟩
    · -- base < prevRim 2 0 = 2
      show (J.coordOf c).2 < H.prevRim 2 0
      exact hb2
    · -- floorH 0 = ⊥ < htH 0
      have hfl : H.floorH 0 (J.coordOf c).2 = ⊥ := by rw [History.floorH]; rfl
      rw [hfl]; exact WithBot.bot_lt_coe _
    · -- htH 0 c = level ≤ slotVal(fineSlot base) = line.at(base)
      have hht : H.htH 0 (J.coordOf c) = ((J.coordOf c).1 : ℚ) := by
        rw [History.htH, Finset.range_zero, Finset.sum_empty, add_zero]
      have hsv : ν.slotVal (ν.fineSlot (J.coordOf c).2) = ν.line.at (J.coordOf c).2 := by
        rw [Node.slotVal, Node.fineSlot, hDw, Nat.div_one, Nat.mul_one]
      rw [hht, hsv]
      have hlev1 : ((J.coordOf c).1 : ℚ) ≤ 1 := by
        have : (J.coordOf c).1 ≤ 1 := by omega
        exact_mod_cast this
      exact le_trans hlev1 (hrh _ hb2)
  -- mstar_eq at read 0: mstar = card of band = card univ = 4.
  have hcard : Nat.card {c : Fin 4 // inFreshBand H 2 J.coordOf 0 ν c} = 4 := by
    have huniv : {c : Fin 4 // inFreshBand H 2 J.coordOf 0 ν c} ≃ Fin 4 :=
      (Equiv.subtypeUnivEquiv hband)
    rw [Nat.card_congr huniv, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hmstar : (J.fresh 0).mstar = 4 := by
    have := J.mstar_eq 0 hlen0
    rw [hν] at hcard
    rw [this, hcard]
  -- totalPins ⊤ = Σ_{i<len} mstar + 0 = mstar 0.
  have hnp : (topLocus 2 4).numPinned = 0 := by
    unfold DigitSystem.numPinned
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _; simp [topLocus]
  rw [totalPins, hnp, Nat.add_zero, hlen, Finset.sum_range_one, hmstar]

/-- Corollary: `totalPins = 2` (U27's demand) is impossible at N = 2 for any such JetSetup. -/
theorem obstruction_ne2 (H : History 2 F4) (hlen : H.nodes.length = 1)
    (J : JetSetup H 2 2 4)
    (hg : ∀ h0 : 0 < H.nodes.length, (H.nodes[0]'h0).g = 2)
    (hμ : ∀ h0 : 0 < H.nodes.length, (H.nodes[0]'h0).μ = 1) :
    totalPins J (topLocus 2 4) ≠ 2 := by
  rw [obstruction_N2 H hlen J hg hμ]; norm_num

end LeanUrat.MovesJ

