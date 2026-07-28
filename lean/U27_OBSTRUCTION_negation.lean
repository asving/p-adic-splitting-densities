/-
ESCALATION WITNESS for HC2.U27_gateInert (2026-07-28, Fable escalation round).

Route 2 (independent of `U27_OBSTRUCTION_witness.lean`, which proves the totalPins-core
obstruction under extracted node hypotheses): refute the EXACT ∃-sentence of
`gate_order0_inert` at `N := 2` — every conjunct verbatim, including `KeysLawful`, the
species clause, the seed, and the second (mass-tie) equation — and conclude the falsity of
the full ∀-statement. This closes any residual doubt that some other conjunct or quantifier
nuance could rescue the unit as stated.

Mechanism (all forced by REQUIRED JetSetup fields, no freedom anywhere):
  coherent.1 (root deg Φ = 1) + hDwidth   ⇒ Dwidth = 1
  g = 2, μ = 1, e ≥ 1                      ⇒ μ·childWidth = 2e ≥ 2
  root_height                              ⇒ line.at b ≥ 1 at BOTH bases b = 0, 1
  floorH 0 = ⊥, htH 0 = level, fineSlot=id ⇒ frame-0 band = {level ≤ line.at base}
  N = 2 ⇒ levels ∈ {0,1}, both ≤ 1 ≤ line  ⇒ band = the WHOLE 2×2 box
  mstar_eq                                 ⇒ (fresh 0).mstar = 4
  topLocus pins nothing                    ⇒ totalPins = 4 ≠ 2.
The defect is a CONFLICT OF TWO JetSetup FIELDS at g·N ≥ 4: `root_height` (line ≥ 1 on the
factor interior) versus `inFreshBand`'s INCLUSIVE upper edge `htH ≤ slotVal` counted by
`mstar_eq` — together they swallow level 1 whenever it exists. Only N = 1 escapes.

ADJUDICATED + RESOLVED (2026-07-28, U27 restate+prove round): this artifact is now the
HISTORICAL witness against the PRE-RESTATEMENT `∀ N ≥ 1` form. The adjudication read the
defect through the DC-1 lesson: the recorded gate equations (totalPins = 2, the 1/4 tie)
are BOX-SIZE-DEPENDENT and belong to the (ZC-c)/C.2 coverage floor
`N(H₀,⊤) = 1 + the largest constrained level = 1` — exactly the "Only N = 1 escapes" of
the mechanism above (at N = 1 the forced band count is 2, MATCHING the recorded value, so
the mechanism produces no contradiction there). The unit was RESTATED at N := 1
(`LeanUrat/HC2/U27_gateInert.lean`) and PROVED sorry-free; `U27_restated_body_true` at the
bottom of this file re-exports that proof against the restated body VERBATIM — the
machine-checked demonstration that this refutation FAILS against (and by consistency can
never be adapted to) the restated form.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U27_gateInert

set_option linter.all false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace LeanUrat.MovesJ

/-- The VERBATIM body of `gate_order0_inert` at `N := 2` (so `2 * N = 2 * 2`). -/
def U27BodyAtN2 : Prop :=
  ∃ (H₀ : History 2 F4) (keys : ℕ → Polynomial ℤ_[2]),
    KeysLawful H₀ keys ∧
    H₀.nodes.length = 1 ∧
    (∀ h0 : 0 < H₀.nodes.length,
      (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
      (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
    ∃ (S : PresentSeed 2 F4 H₀ 2 2 keys) (J : JetSetup H₀ 2 2 (2 * 2)),
      totalPins J (topLocus 2 (2 * 2)) = 2 ∧
      Nat.card (J.SHZ (topLocus 2 (2 * 2))) * 2 ^ 2 = 2 ^ (2 * 2)

/-- **The exact U27 sentence is FALSE at N = 2.** No history, seed, or jet setup satisfying
all the listed conjuncts exists: `totalPins` is forced to 4. -/
theorem U27_false_at_N2 : ¬ U27BodyAtN2 := by
  rintro ⟨H, keys, -, hlen, hnode, -, J, hpins, -⟩
  have hlen0 : 0 < H.nodes.length := by omega
  obtain ⟨-, hg2, hμ1⟩ := hnode hlen0
  -- Dwidth = 1: coherence root clause (deg Φ₀ = 1) through the node's hDwidth frame link.
  have hDw : (H.nodes[0]'hlen0).Dwidth = 1 := by
    rw [(H.nodes[0]'hlen0).hDwidth, J.coherent.1 hlen0]
  -- The factor interior μ·childWidth = 1·(e·2·1) = 2e covers both bases 0, 1.
  have hcov : ∀ b : ℕ, b < 2 →
      b < (H.nodes[0]'hlen0).μ * (H.nodes[0]'hlen0).childWidth := by
    intro b hb
    have he1 : 1 ≤ (H.nodes[0]'hlen0).e := (H.nodes[0]'hlen0).he
    rw [Node.childWidth, hDw, hg2, hμ1]
    omega
  -- root_height (REQUIRED field): the line is ≥ 1 at both bases.
  have hrh : ∀ b : ℕ, b < 2 → (1 : ℚ) ≤ (H.nodes[0]'hlen0).line.at b :=
    fun b hb => J.root_height hlen0 b (hcov b hb)
  -- Every coordinate of the 2×2 box lies in the frame-0 fresh band.
  have hband : ∀ c : Fin (2 * 2), inFreshBand H 2 J.coordOf 0 (H.nodes[0]'hlen0) c := by
    intro c
    obtain ⟨hlev, hbase⟩ := J.coordOf_lt c
    refine ⟨hbase, ?_, ?_⟩
    · -- floorH 0 = ⊥ (empty prefix) sits strictly below every height.
      have hfl : H.floorH 0 (J.coordOf c).2 = ⊥ := rfl
      rw [hfl]; exact WithBot.bot_lt_coe _
    · -- htH 0 = the level; slotVal ∘ fineSlot = line.at base (Dwidth = 1); level ≤ 1 ≤ line.
      have hht : H.htH 0 (J.coordOf c) = ((J.coordOf c).1 : ℚ) := by
        rw [History.htH, Finset.range_zero, Finset.sum_empty, add_zero]
      have hsv : (H.nodes[0]'hlen0).slotVal ((H.nodes[0]'hlen0).fineSlot (J.coordOf c).2)
          = (H.nodes[0]'hlen0).line.at (J.coordOf c).2 := by
        rw [Node.slotVal, Node.fineSlot, hDw, Nat.div_one, Nat.mul_one]
      rw [hht, hsv]
      refine le_trans ?_ (hrh _ hbase)
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hlev)
  -- mstar_eq (REQUIRED field): the fresh pin count is the band count = the full box = 4.
  have hmstar : (J.fresh 0).mstar = 4 := by
    rw [J.mstar_eq 0 hlen0, Nat.card_congr (Equiv.subtypeUnivEquiv (hband)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  -- topLocus pins nothing.
  have hnp : (topLocus 2 (2 * 2)).numPinned = 0 := by
    unfold DigitSystem.numPinned
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _; simp [topLocus]
  -- totalPins = mstar(read 0) + 0 = 4, contradicting the demanded 2.
  rw [totalPins, hnp, Nat.add_zero, hlen, Finset.sum_range_one, hmstar] at hpins
  exact absurd hpins (by norm_num)

/-- **The full U27 statement (∀ N ≥ 1) is FALSE**: specialize the verbatim `gate_order0_inert`
sentence to N = 2. -/
theorem gate_order0_inert_statement_false :
    ¬ (∀ (N : ℕ), 1 ≤ N →
        ∃ (H₀ : History 2 F4) (keys : ℕ → Polynomial ℤ_[2]),
          KeysLawful H₀ keys ∧
          H₀.nodes.length = 1 ∧
          (∀ h0 : 0 < H₀.nodes.length,
            (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
            (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
          ∃ (S : PresentSeed 2 F4 H₀ 2 N keys) (J : JetSetup H₀ 2 N (2 * N)),
            totalPins J (topLocus 2 (2 * N)) = 2 ∧
            Nat.card (J.SHZ (topLocus 2 (2 * N))) * 2 ^ 2 = 2 ^ (2 * N)) := by
  intro h
  exact U27_false_at_N2 (h 2 (by norm_num))

#print axioms U27_false_at_N2
#print axioms gate_order0_inert_statement_false

/-- VERIFICATION THAT THE REFUTATION FAILS AGAINST THE RESTATED FORM (2026-07-28): the
restated unit's ∃-body — `N := 1` at the coverage floor, every other conjunct verbatim —
is TRUE, by the constructive proof of the restated `gate_order0_inert`. By consistency,
no adaptation of `U27_false_at_N2`'s mechanism refutes it: at N = 1 the forced band count
is 2 (only level 0 exists), which IS the recorded `totalPins`. -/
theorem U27_restated_body_true :
    ∃ (H₀ : History 2 F4) (keys : ℕ → Polynomial ℤ_[2]),
      KeysLawful H₀ keys ∧
      H₀.nodes.length = 1 ∧
      (∀ h0 : 0 < H₀.nodes.length,
        (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
        (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
      ∃ (S : PresentSeed 2 F4 H₀ 2 1 keys) (J : JetSetup H₀ 2 1 (2 * 1)),
        totalPins J (topLocus 2 (2 * 1)) = 2 ∧
        Nat.card (J.SHZ (topLocus 2 (2 * 1))) * 2 ^ 2 = 2 ^ (2 * 1) :=
  gate_order0_inert

#print axioms U27_restated_body_true

end LeanUrat.MovesJ
