/-  MovesV unit V0-2 `linset_mem_iff` — ROSTER (3): (a) normal form; (b) base
    membership; (c) closure under adding one period.
    moves_ref: "L(h₀; P) := {h₀ + Σ n_v·v}". -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem linset_mem_iff {D : ℕ} (L : LinSet D) (h : Hpt D) :
    L.Mem h ↔ ∃ c : Fin L.periods.length → ℕ,
      h = fun i => L.base i + ∑ j, c j * (L.periods.get j) i :=
  Iff.rfl

theorem linset_base_mem {D : ℕ} (L : LinSet D) : L.Mem L.base :=
  ⟨0, by funext i; simp⟩

theorem linset_add_period {D : ℕ} (L : LinSet D) (h : Hpt D)
    (j : Fin L.periods.length) (hm : L.Mem h) :
    L.Mem (fun i => h i + (L.periods.get j) i) := by
  obtain ⟨c, hc⟩ := hm
  refine ⟨fun k => c k + (if k = j then 1 else 0), ?_⟩
  funext i
  rw [hc]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq' Finset.univ j, Finset.mem_univ, if_pos]
  ring

end LeanUrat.MovesV
