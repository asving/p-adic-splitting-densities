/-
Unit W2.Mfac_le  (MovesD campaign, E-phase)  [REV 6, Codex#4 f.3: UNCONDITIONAL over the
subtype — the "smuggled" rider is GONE with the domain ruling]
moves_ref: "M(P̂) := ∏_r m̄_r ≤ ∏_r ⌊n/(g_rμ_r)⌋ ≤ n^{|P̂|} (m̄_r as above … coarse chain
displayed)" — for every shape-prefix of the degree-n classifier, verbatim.
deps: W1′.
sketch: m̄_r ≤ ℓ_r ≤ n (W1′); List.prod ≤ pow.  difficulty: easy.
hypothesis_fields: NONE.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {n : ℕ}

/-- [W1′ content, inlined helper] `ℓ_r ≤ n` at every read, read off the certificate `P.2`:
root — ℓ₀ ≤ s0+wSide ≤ n (`root_box`); step — ℓ_{r+1} ≤ s0'+wSide' ≤ μ_r (`window`)
≤ g_r·μ_r ≤ ℓ_r (`gmu`, g ≥ 1) ≤ n (IH). Inlined rather than imported from `W1_wellformed`
so this unit's axiom footprint stays Lean-core clean. -/
private theorem reads_len_le (P : Shape n) :
    ∀ (r : ℕ) (hr : r < (P : ShapePrefix).reads.length),
      ((P : ShapePrefix).reads[r]'hr).len ≤ n := by
  intro r
  induction r with
  | zero =>
    intro hr
    have hb := P.2.root_box hr
    calc ((P : ShapePrefix).reads[0]'hr).len
        ≤ ((P : ShapePrefix).reads[0]'hr).wSide := Nat.div_le_self _ _
      _ ≤ ((P : ShapePrefix).reads[0]'hr).s0 + ((P : ShapePrefix).reads[0]'hr).wSide := by omega
      _ ≤ n := hb
  | succ r ih =>
    intro hr
    have hr' : r < (P : ShapePrefix).reads.length := by omega
    have hih := ih hr'
    have hwin := P.2.window r hr
    have hgmu := P.2.gmu r hr'
    have hg := ((P : ShapePrefix).reads[r]'hr').hg
    calc ((P : ShapePrefix).reads[r+1]'hr).len
        ≤ ((P : ShapePrefix).reads[r+1]'hr).wSide := Nat.div_le_self _ _
      _ ≤ ((P : ShapePrefix).reads[r+1]'hr).s0 + ((P : ShapePrefix).reads[r+1]'hr).wSide := by omega
      _ ≤ ((P : ShapePrefix).reads[r]'hr').μ := hwin
      _ ≤ ((P : ShapePrefix).reads[r]'hr').g * ((P : ShapePrefix).reads[r]'hr').μ :=
          Nat.le_mul_of_pos_left _ hg
      _ ≤ ((P : ShapePrefix).reads[r]'hr').len := hgmu
      _ ≤ n := hih

/-- M(P̂) ≤ n^{|P̂|}, unconditional over the note's shapes. -/
theorem Mfac_le (P : Shape n) :
    (P : ShapePrefix).Mfac ≤ n ^ (P : ShapePrefix).reads.length := by
  simp only [ShapePrefix.Mfac]
  calc ((P : ShapePrefix).reads.map ShapeRead.mbar).prod
      ≤ n ^ ((P : ShapePrefix).reads.map ShapeRead.mbar).length := by
        apply List.prod_le_pow_card
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨R, hR, rfl⟩ := hx
        calc R.mbar ≤ R.len := Nat.div_le_self _ _
          _ ≤ n := by
              rw [List.mem_iff_getElem] at hR
              obtain ⟨i, hi, rfl⟩ := hR
              exact reads_len_le P i hi
    _ = n ^ (P : ShapePrefix).reads.length := by rw [List.length_map]

end LeanUrat.MovesD
