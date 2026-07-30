/-
Unit U22-E1.SAE_spanStrict_endpoint  (HC-2 campaign — blueprint §9 F-4 endpoint of U22;
NEW unit, census +1; statement landed in-file from the proven reduction and
PROVER-REFINABLE — the assembled `readsOf_SAE` in U22_SAE.lean is normative and
byte-unchanged)
moves_ref: §C rev 12 (SAE) display; the F-4 semantic spec — THE STRICT SPAN-ENTRY
ENDPOINT: "at every recorded span slot strictly below the parent vertex, f's actual
frame-weight strictly exceeds the parent line's value (the parent's (ZC)-zeroed-strips
content: interior zeros push actual valuations strictly above the old line)".
deps: D4 (`SideReads` at reads i and i+1), the parent's (ZC)-zeroed strips, K1 slot
reading.  difficulty: HARD (the genuine frontier of the F-4 reduction).
hypothesis_fields: none.
SCALE NOTE (C.1.0(c)): stage-(i+1) weights are `STR_{i+1} ×` absolute, and `Node.line`
is absolute v_p-scale — the strict inequality is stated multiplied through by
`H.strFrame (i+1)`.  The guard `B j ≠ 0` keeps the claim statable (`σ.w` of the zero
polynomial is junk; a vanished span coefficient exceeds every finite line value morally,
and the assembled proof consumes this endpoint only at slots SideReads(ii) makes
nonzero).

PROVED (E1 close round, 2026-07-28; statement BYTE-UNCHANGED).  Species dispatch on the
PARENT read, mirroring the K1 kernel's perimeter:
* RECENTERING parent — the honest leg: U20c's landed machine (the `g = 1` standard-lift
  view `Φ' = Φ − lift` of `ψ = X − C center` at the PARENT stage, the distinct-position
  residual-sum machine pinning the two side endpoints, whence the h-tie `ν.h = σ.h` and
  `σ.w f = γ`), with `L5_landVertex` swapped for **`L5_landBox`** — D.8's STRICT (BOX)
  clause below the vertex: `σ.w f < σ.w (B j) + j·σ.h` for `j < μ`, `B j ≠ 0`.  The
  recentered valuation is the parent valuation (`σ'.w = σ.w`), and the slope law +
  γ-tie + `hLineU` convert `γ − j·h < σ.w (B j)` to the fenced ℚ-form (the helper
  machine is the shared `LeanUrat.HC2.SharedRecenter`, also consumed by U20c).
* NON-RECENTERING parent — `HC1.V9_E1box_nonrec` (V9's REV-6 addition, same file as the
  kernel): the `e·g ≥ 2` legs close by the V10 INCONSISTENCY finding (vacuous perimeter
  — read V9's REV-4 disclosure; never cite those legs as transport mathematics),
  `i ≥ 1 ∧ e·g = 1` by the species inventory, and the genuine `i = 0 ∧ e·g = 1` corner
  by `v9c_cornerBox` — the strict Taylor-VANISHING sibling of the REV-5 corner core: a
  minimizing child slot `j < μ` would pin its nonzero digit to the `j`-th Taylor
  coefficient of `X^{s0}·Ranch` at the recorded root, which vanishes below the recorded
  ψ-order (`v9c_taylor_zero`; only the divisibility half of `hOrd` is consumed).
SideReads(iii) is consumed HERE only on the recentering leg (the anchor `σ.R f =
T(a)·Ranch` — exactly U20c's consumption perimeter; single-side reads, where the
U31-fenced rendering is faithful per the fence's own text).  ZERO axioms beyond
Lean core; no new `sorry` anywhere in the cone.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.SharedRecenter
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L5_landBox
import LeanUrat.HC1.V9_K1nonrec

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD SharedRecenter

/-- (SAE) strict span-entry endpoint (F-4/U22-E1): at consecutive reads of a run, at every
recorded span slot `j` of the child read strictly below the parent vertex (`j < μ`), f's
actual frame-(i+1) weight at slot `j` strictly exceeds the parent line's value at `j`'s
base index (stage scale: `σ.w = STR ×` absolute). -/
theorem SAE_spanStrict_endpoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd) :
    ∀ j : ℕ, (H.nodes[i+1]'hi1).s0 ≤ j →
      j ≤ (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide →
      j < (H.nodes[i]'(by omega)).μ → B j ≠ 0 →
      (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
        < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := by
  classical
  have hi : i < H.nodes.length := by omega
  intro j hj1 hj2 hjμ hBj
  by_cases hsp : (H.nodes[i]'hi).species = ReadSpecies.recentering
  · -- RECENTERING parent — the shared scaffold with `L5_landBox` at the strict slot
    obtain ⟨hf, he1σ, hccne, hΦ', hw', hanchf, hordψ, hlift, hwf, hheq, hline⟩ :=
      recentering_scaffold h i hi1 hi hsp
    set ν : Node p F := H.nodes[i]'hi
    -- the STRICT (BOX) transport at the child key (`L5_landBox` through the
    -- standard-lift view)
    have hψmon : (Polynomial.X - Polynomial.C ν.center).Monic := Polynomial.monic_X_sub_C _
    have hψdeg : (Polynomial.X - Polynomial.C ν.center).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C _
    have hψirr : Irreducible (Polynomial.X - Polynomial.C ν.center) :=
      Polynomial.irreducible_X_sub_C ν.center
    have hψz : (Polynomial.X - Polynomial.C ν.center) ≠ Polynomial.X := by
      intro hX
      exact hccne (Polynomial.C_eq_zero.mp (sub_eq_self.mp hX))
    rw [hΦ'] at hdev
    have hbox := L5_landBox ν.σ (Polynomial.X - Polynomial.C ν.center) 1 hψdeg
      hψmon hψirr hψz (ν.σ.Φ - ν.lift) hlift f hf ν.μ ν.a ν.Ranch hanchf hordψ B Nd hdev
      j hjμ hBj
    -- the recentered valuation is the parent valuation
    rw [hw' (B j)]
    -- integer content: γ − j·h < σ.w (B j)
    rw [he1σ, hwf, hheq] at hbox
    push_cast at hbox
    have hZ : ν.gam - (j : ℤ) * (ν.h : ℤ) < ν.σ.w (B j) := by linarith [hbox]
    -- the ℚ-scale line law at the strict slot
    rw [hline j]
    exact_mod_cast hZ
  · -- NON-RECENTERING parent — the V9 REV-6 Box law (V10-vacuous legs + species
    -- inventory + the strict Taylor corner)
    exact LeanUrat.HC1.V9_E1box_nonrec h i hi1 hsp B Nd hdev j hjμ hBj

end LeanUrat.MovesJ
