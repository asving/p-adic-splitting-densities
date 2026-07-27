/-
Unit U1b.nodeLift_exists  (HC-2 campaign, E-phase — rev 2, audit GAP-1: THE OWNED
STAGE↔NODE BRIDGE; the F10 trap gets a named unit instead of an inline check)
moves_ref: §B2-DEF D.5 (the lift at the READ's own pair, per the F10 adjudication);
MovesC `IsNodeLift` docstring.
deps: D8, Moves L3_liftExists (the stage-pair sibling — proof SHAPE only, never its
statement), Stage.hS6b.  difficulty: medium.
hypothesis_fields: none (target) — the named D.5 side conditions `hdvd`/`hthr` below are
the E-phase concretization of the blueprint's "(the read's D.5 side conditions)" ellipsis
(the pre-authorized fallback; statement-fence: hypothesis narrowing, sign-off pending —
recorded in MANIFEST deviations).
NAMED RISK (blueprint): the stride/stretch arithmetic — `hStretch` puts C-weights in
`e·ℤ` while the read pair wants `σ.w (t_k) = h'·(g−k)`.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- Read-pair lift existence from stage data (L3's proof shape at the node's pair): the
(S6b) realizers taken at the read's `h'` on the frame's CURRENT valuation. -/
theorem nodeLift_exists {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (ψ : Polynomial ↥σ.K) (g e' h' : ℕ) (hψm : ψ.Monic) (hψd : ψ.natDegree = g)
    (hg : 1 ≤ g) (hh' : 1 ≤ h')
    (hdvd : ∀ k : ℕ, k < g → (σ.e : ℤ) ∣ (h' : ℤ) * ((g : ℤ) - (k : ℤ)))
    (hthr : ∀ k : ℕ, k < g → (σ.e : ℤ) * σ.wPrev σ.Φ < (h' : ℤ) * ((g : ℤ) - (k : ℤ))) :
    ∃ Φhat, IsReadLift σ ψ g e' h' Φhat := by
  classical
  -- The stride `e = σ.e` is positive (`he`).
  have he_pos : (0 : ℤ) < (σ.e : ℤ) := by have h := σ.he; omega
  -- The (S6b) realizer at slot `k` is taken at the PARENT weight `ν_k = h'·(g−k)/σ.e`
  -- (exact by `hdvd`), so its CURRENT weight is `σ.e·ν_k = h'·(g−k)` via `hStretch` — the
  -- read pair's own weight (D8), NOT the frame-creating pair's `σ.h·(g−k)` (the F10 trap).
  have hediv : ∀ k : ℕ, k < g →
      (σ.e : ℤ) * (((h' : ℤ) * ((g : ℤ) - (k : ℤ))) / (σ.e : ℤ))
        = (h' : ℤ) * ((g : ℤ) - (k : ℤ)) :=
    fun k hk => Int.mul_ediv_cancel' (hdvd k hk)
  -- The parent weight `ν_k` clears the (S6b) threshold `wPrev Φ` — this is `hthr` divided by
  -- the positive stride `σ.e`.
  have hthr' : ∀ k : ℕ, k < g →
      σ.wPrev σ.Φ < ((h' : ℤ) * ((g : ℤ) - (k : ℤ))) / (σ.e : ℤ) := by
    intro k hk
    refine Int.lt_of_mul_lt_mul_left ?_ (le_of_lt he_pos)
    rw [hediv k hk]; exact hthr k hk
  -- The read-pair realizer function (L3's proof SHAPE at the node's own `(e', h')`): at each
  -- present slot the (S6b) realizer at parent weight `ν_k`, digit scalar `ψ_k ∈ Kˣ`; else `0`.
  set tt : ℕ → Polynomial ℤ_[p] := fun k =>
    if h : k < g ∧ ψ.coeff k ≠ 0 then
      (σ.hS6b (((h' : ℤ) * ((g : ℤ) - (k : ℤ))) / (σ.e : ℤ))
        (Units.mk0 (ψ.coeff k) h.2) (hthr' k h.1)).choose
    else 0
    with htt_def
  refine ⟨σ.Φ ^ (e' * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k), tt, ?_, ?_, rfl⟩
  · -- Absent slots: `ψ_k = 0 ⟹ t_k = 0`.
    intro k hk0
    have hcond : ¬ (k < g ∧ ψ.coeff k ≠ 0) := fun h => h.2 hk0
    simp only [htt_def, dif_neg hcond]
  · -- Present slots: unpack the (S6b) realizer and convert its parent-weight data to the
    -- read-pair current-weight clauses.
    intro k hkg hkne
    have hcond : k < g ∧ ψ.coeff k ≠ 0 := ⟨hkg, hkne⟩
    have htt : tt k =
        (σ.hS6b (((h' : ℤ) * ((g : ℤ) - (k : ℤ))) / (σ.e : ℤ))
          (Units.mk0 (ψ.coeff k) hkne) (hthr' k hkg)).choose := by
      simp only [htt_def, dif_pos hcond]
    obtain ⟨hBne, hBmem, hBwp, hBR⟩ :=
      (σ.hS6b (((h' : ℤ) * ((g : ℤ) - (k : ℤ))) / (σ.e : ℤ))
        (Units.mk0 (ψ.coeff k) hkne) (hthr' k hkg)).choose_spec
    rw [htt]
    refine ⟨hBne, hBmem, ?_, ?_⟩
    · -- Read-pair weight: `w(t_k) = σ.e·wPrev(t_k) = σ.e·ν_k = h'·(g−k)`.
      rw [σ.hStretch _ hBne hBmem, hBwp]
      exact hediv k hkg
    · -- Residual: the (S6b) output, with the position rendered at `wPrev(t_k) = ν_k`.
      -- Rewrite `wPrev(t_k)` first so `.choose` leaves the goal before the `Units.mk0`
      -- coercion (which occurs inside `.choose`'s dependent proof term) is unfolded.
      rw [hBwp, hBR, Units.val_mk0]

end LeanUrat.MovesJ
