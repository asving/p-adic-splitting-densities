/-
Unit Sp.shStage [REV 2, F12 — the corollary spelled in full] — moves_ref: "At a
stage with read index (e, h) and pinned Bézout pair (s, t) (e·s + t·h = 1; (P2):
t = 0 at e = 1)".
deps: Sp.shCongr, Sp.shE1. sketch: instantiate at (σs.e, σs.h, σs.s, σs.t) via
σs.hbez (mind the ℕ→ℤ casts); sh_e1_stage rewrites σs.t = 0 (he1t) into Sp.shE1.
difficulty: easy. (The only Stage-typed unit — reuse, not duplication.)
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

universe u

namespace LeanUrat.MovesSp

theorem sh_congr_stage {p : ℕ} {F : Type u} [Fact p.Prime] [Field F]
    [Finite F] (σs : Moves.Stage p F) (γ u0 s0 : ℤ)
    (hγ : γ = σs.e * u0 + s0 * σs.h) : σs.t * γ ≡ s0 [ZMOD σs.e] := by
  -- instantiate Sp.shCongr at (σs.e, σs.h, σs.s, σs.t) via σs.hbez (ℕ→ℤ casts)
  have hb : (σs.e : ℤ) * σs.s + (σs.h : ℤ) * σs.t = 1 := σs.hbez
  rw [Int.modEq_iff_dvd]
  refine ⟨σs.s * s0 - σs.t * u0, ?_⟩
  subst hγ
  linear_combination (-s0) * hb

/-- σ = 0 AND the position identity — the "systems coincide" display at a Stage;
via `σs.he1t he1 : σs.t = 0` and Sp.shE1. -/
theorem sh_e1_stage {p : ℕ} {F : Type u} [Fact p.Prime] [Field F] [Finite F]
    (σs : Moves.Stage p F) (γ s0 : ℤ) (he1 : σs.e = 1) :
    shSigma σs.t γ σs.e = 0 ∧ Sh σs.t γ σs.e (geoPos σs.e σs.t γ s0) = s0 := by
  -- (P2): σs.he1t he1 : σs.t = 0, then Sp.shE1's `simp` normal form at e = 1
  have ht : σs.t = 0 := σs.he1t he1
  have hcast : (σs.e : ℤ) = 1 := by exact_mod_cast he1
  rw [hcast]
  simp [shSigma, Sh, geoPos, Int.fdiv_one, ht]

end LeanUrat.MovesSp
