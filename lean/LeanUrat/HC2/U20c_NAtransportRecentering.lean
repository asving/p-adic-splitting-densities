/-
Unit U20c.NA_transport_recentering  (HC-2 campaign — blueprint §9 F-2 pre-split of U20;
NEW unit, census +1; sub-lemma discipline: this statement is PROVER-REFINABLE, the
assembled `readsOf_NA` in U20_NA.lean is normative and byte-unchanged)
moves_ref: §C C.0 (NA) display; the F-2 semantic spec — cross-frame VERTEX-VALUE
TRANSPORT at a RECENTERING parent, routed through the species-specific transition clause:
via `IsRecenteringCore` (`Φ′ = Φ − t`, coherence's recentering leg) + D.10's recentered
development identity (`L5_recLiftIndep_R4`'s development side).
deps: D4 (`SideReads` at reads i and i+1), `HistoryCoherent` (the recorded recentering
transition at the recorded center/lift), Moves `IsRecenteringCore`/`L5_recLiftIndep_R4`.
difficulty: hard-ish.  hypothesis_fields: none.
SCALE NOTE (C.1.0(c)): stage-(i+1) weights are `STR_{i+1} ×` absolute (a recentering has
`e = 1`, so the stretch is unchanged across this step), and `Node.line` is absolute
v_p-scale — the transport equation is stated multiplied through by `H.strFrame (i+1)`.
Guards as in U20a.

PROOF NOTE. The route is NOT `L5_recLiftIndep_R4` (whose `RecenterSubstCore`
input is StageCore-gated and unavailable here); instead (the machine below — helpers AND
the parent-side scaffold `recentering_scaffold` — lives in the shared
`LeanUrat.HC2.SharedRecenter`, also consumed by U22-E1's recentering leg):
* `Φ' = Φ − lift` is the `g = 1` STANDARD LIFT of `ψ = X − C center` in the PARENT stage
  (the `L5_recVV` construction, rebuilt without `StageCore.R_neg`: the sign
  `R(−lift) = C(−center)` is derived from bare `Stage` — `R(−1)` is a constant `C d` with
  `d² = 1` by the S5 digit of `−lift`, and `d = 1` forces `char K = 2` via an (S6b)
  realizer pair for `±1` plus `hRadd`/`hRlt`), so `L5_landVertex` applies to the given
  child development: `w(B μ) = w(f) − μ·σ.h` and `B μ ≠ 0`.
* PARENT SIDE: at `e = 1` (so `t = 0`, `s = 1`, `a = s0`) the slot residuals are
  distinct-position monomials, so `R f` decomposes over the `w`-minimizing slots
  (a distinct-position residual-sum machine, cancellation excluded through the constant
  `R(−1)`); the recorded anchor `R f = z^{s0}·Ranch` then pins `s0` and `s0 + wSide` as
  minimizing slots, and SideReads(ii) at both pattern endpoints yields `ν.h = σ.h` and
  `w(f) = γ` (using `1 ≤ μ ≤ wSide` from `ord_ψ Ranch = μ`).
* SCALES: slope law + γ-tie + `hLineU` give `STR_{i+1}·line.at(μ·childWidth) = γ − μ·h`.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.SharedRecenter
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L5_landVertex

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD SharedRecenter

/-- (NA) vertex-value transport, RECENTERING parent (F-2/U20c): at consecutive reads of a
run whose parent read `i` is a RECENTERING, the parent's line value at the standing vertex
base `μ·childWidth` is realized as the frame-(i+1) actual slot weight of f's development
at the vertex slot (stage scale: `σ.w = STR ×` absolute), and that vertex coefficient is
nonzero. -/
theorem NA_transport_recentering {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  classical
  have hi : i < H.nodes.length := by omega
  obtain ⟨hf, he1σ, hccne, hΦ', hw', hanchf, hordψ, hlift, hwf, hheq, hline⟩ :=
    recentering_scaffold h i hi1 hi hsp
  set ν : Node p F := H.nodes[i]'hi
  -- the vertex transport at the child key (L5_landVertex through the standard-lift view)
  have hψmon : (Polynomial.X - Polynomial.C ν.center).Monic := Polynomial.monic_X_sub_C _
  have hψdeg : (Polynomial.X - Polynomial.C ν.center).natDegree = 1 :=
    Polynomial.natDegree_X_sub_C _
  have hψirr : Irreducible (Polynomial.X - Polynomial.C ν.center) :=
    Polynomial.irreducible_X_sub_C ν.center
  have hψz : (Polynomial.X - Polynomial.C ν.center) ≠ Polynomial.X := by
    intro hX
    exact hccne (Polynomial.C_eq_zero.mp (sub_eq_self.mp hX))
  rw [hΦ'] at hdev
  obtain ⟨hveq, hvne⟩ := L5_landVertex ν.σ (Polynomial.X - Polynomial.C ν.center) 1 hψdeg
    hψmon hψirr hψz (ν.σ.Φ - ν.lift) hlift f hf ν.μ ν.a ν.Ranch hanchf hordψ B Nd hdev
  refine ⟨hvne, ?_⟩
  -- the recentered valuation is the parent valuation
  rw [hw' (B ν.μ)]
  -- integer value of the vertex slot
  have hwBμ : ν.σ.w (B ν.μ) = ν.gam - (ν.μ : ℤ) * (ν.h : ℤ) := by
    rw [he1σ, hwf, hheq] at hveq
    push_cast at hveq
    linarith
  -- the ℚ-scale line law at the vertex slot
  rw [hwBμ, hline ν.μ]
  push_cast
  ring

end LeanUrat.MovesJ
