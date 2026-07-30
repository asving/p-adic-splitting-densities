/-
Unit Sp.selfloopFull [REV 2, F13 — hypothesis types in full] — moves_ref: "n = 3
check: the two loop classes Q2.3▸(1,2) and Q3▸(1,3) are exactly the full POST-REC
letters at stages (1,1,2) and (1,1,3), per (i)."
deps: Sp.selfloopChar. sketch: unfold IsFull; direct from the characterization.
difficulty: easy.
AS-BUILT (2026-07-30 verify-2 fold-in): the deps/sketch above are the blueprint
plan, not the built proof — the file imports only Defs and re-derives the full
self-loop characterization inline; Sp.selfloopChar is neither imported nor
cited. Inline duplication tracked under the Class-D watch
(notes/GOLF_CAMPAIGN_2026-07-30.md).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem selfloop_isFull {n : ℕ} {s : Species} (hc : Coherent s)
    (hb : Budget n s) (h : SuccStep n s s) : IsFull s ∧ s.tag = .postRec := by
  -- Extract the fields of `Coherent s` that we need: (WellTyped) D ≥ 1, e ≥ 1,
  -- λ-parts positive, and (G4) selection ∈ λ.
  obtain ⟨⟨hD1, -, -, -, -, hlampos⟩, -, -, -, ⟨-, hselmem⟩, -⟩ := hc
  -- The stage laws of the self-loop edge `s → s`.
  have hstage := h.1
  unfold StageLaws at hstage
  cases hsel : s.sel with
  | none => simp only [hsel] at hstage
  | some gm =>
    obtain ⟨g, μ⟩ := gm
    rw [hsel] at hstage
    obtain ⟨hDeq, -, hWeq, -, htagRec⟩ := hstage
    -- (g, μ) ∈ λ, so g ≥ 1 (WellTyped's positivity of λ-parts).
    have hgmem : (g, μ) ∈ s.lam := hselmem (g, μ) hsel
    have hg1 : 1 ≤ g := (hlampos (g, μ) hgmem).1
    -- D = (e·g)·D with D ≥ 1 forces e·g = 1, hence e = 1 and g = 1.
    have hk : s.e * g = 1 :=
      Nat.eq_of_mul_eq_mul_right hD1 (by rw [one_mul, ← hDeq])
    have he' : s.e = 1 := Nat.eq_one_of_mul_eq_one_right hk
    have hg' : g = 1 := Nat.eq_one_of_mul_eq_one_left hk
    refine ⟨?_, htagRec.mpr ⟨he', hg'⟩⟩
    -- `IsFull s` is `s.sel = some (1, s.W)`; here `s.sel = some (g, μ)`, `g = 1`,
    -- and `s.W = μ` (the window law), so it holds.
    change s.sel = some (1, s.W)
    rw [hsel, hg', hWeq]

end LeanUrat.MovesSp
