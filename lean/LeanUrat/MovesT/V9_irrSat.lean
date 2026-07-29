/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V9 `irr_saturation` — the note's own parenthetical stated ON `IrrHalts`:
saturation ⟺ μ = 1 under lawfulness (MOVES 7078–7080). Together with T-V3's species
leg this displays BOTH equalities of the note line. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- the Dwidth chain telescopes the latest read's key degree to accE·accF. -/
theorem acc_childWidth (H : History p F) (n : ℕ) (hlaw : HistLawful p n H)
    (hne : H.nodes ≠ []) :
    accE H * accF H = (H.nodes.getLast?).elim 1 (fun ν => ν.childWidth) := by
  have hlen : 0 < H.nodes.length := List.length_pos_of_ne_nil hne
  -- Telescoping the Dwidth chain: for every prefix ending at index k, the product of the
  -- e's and g's up to k equals that node's childWidth.
  have key : ∀ k, (hk : k < H.nodes.length) →
      ((H.nodes.map fun ν => ν.e).take (k + 1)).prod
          * ((H.nodes.map fun ν => ν.g).take (k + 1)).prod
        = (H.nodes[k]'hk).childWidth := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [List.prod_take_succ _ 0 (by simpa using hk),
          List.prod_take_succ _ 0 (by simpa using hk)]
      simp only [List.take_zero, List.prod_nil, one_mul, List.getElem_map]
      -- goal: (H.nodes[0]).e * (H.nodes[0]).g = childWidth (H.nodes[0])
      have hDw0 : (H.nodes[0]'hk).Dwidth = 1 := by
        rw [(H.nodes[0]'hk).hDwidth]; exact hlaw.2.1 hk
      simp only [Node.childWidth, hDw0]; ring
    | succ k ih =>
      intro hk
      have hk' : k < H.nodes.length := by omega
      rw [List.prod_take_succ _ (k + 1) (by simpa using hk),
          List.prod_take_succ _ (k + 1) (by simpa using hk)]
      simp only [List.getElem_map]
      have hih := ih hk'
      -- chain clause: Dwidth_{k+1} = childWidth_k
      have hchain : (H.nodes[k + 1]'hk).Dwidth = (H.nodes[k]'hk').childWidth :=
        (hlaw.2.2.2.2.2.2.1 k hk).2.1
      simp only [Node.childWidth] at hchain ⊢
      -- goal: (Pe * e_{k+1}) * (Pg * g_{k+1}) = e_{k+1} * g_{k+1} * Dwidth_{k+1}
      rw [hchain, ← Node.childWidth, ← hih]
      ring
  -- Instantiate at the last index.
  have hk0 : H.nodes.length - 1 < H.nodes.length := by omega
  have hmain := key (H.nodes.length - 1) hk0
  rw [Nat.sub_add_cancel (show 1 ≤ H.nodes.length by omega),
      List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at hmain
  simp only [accE, accF]
  rw [List.getLast?_eq_some_getLast hne, Option.elim_some,
      List.getLast_eq_getElem]
  exact hmain

theorem irr_iff_mu_one (H : History p F) (n : ℕ) (hlaw : HistLawful p n H)
    (ν : Node p F) (hν : H.nodes.getLast? = some ν) :
    IrrHalts H ↔ ν.μ = 1 := by
  have hne : H.nodes ≠ [] := by
    intro h; rw [h] at hν; simp at hν
  -- accE·accF telescopes to ν.childWidth at the latest read.
  have hcw : accE H * accF H = ν.childWidth := by
    have h := acc_childWidth H n hlaw hne
    rw [hν, Option.elim_some] at h; exact h
  -- childWidth is positive (product of e's and g's, each ≥ 1).
  have hpos : 0 < ν.childWidth := by
    rw [← hcw]
    refine Nat.mul_pos (List.prod_pos ?_) (List.prod_pos ?_) <;>
      · intro x hx
        rw [List.mem_map] at hx
        obtain ⟨ν', _, rfl⟩ := hx
        first | exact ν'.he | exact ν'.hg
  simp only [IrrHalts, hν, Option.elim_some, hcw, ne_eq, hne, not_false_eq_true, true_and]
  -- goal: ν.childWidth = ν.childWidth * ν.μ ↔ ν.μ = 1
  constructor
  · intro heq
    have h1 : ν.childWidth * 1 = ν.childWidth * ν.μ := by rw [mul_one]; exact heq
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  · intro hmu; rw [hmu, mul_one]

end LeanUrat.MovesT
