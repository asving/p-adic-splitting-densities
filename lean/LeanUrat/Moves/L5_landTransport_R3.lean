import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-! # L5.landTransport (MANIFEST_R3) — REFUTED AS STATED; honest `sorry`

**DEPRECATED — REFUTED AS STATED (machine counterexample in-file). Superseded by
`L5_landTransport_R4.lean` (sorry-free, restated with the K1At slot-tie hypothesis per
machine-checked finding 2). Do not import.**

**Verdict: the fenced statement is FALSE in the intended model, hence unprovable.**
The statement quantifies over an ARBITRARY `Φhat : Polynomial ℤ_[p]` with no hypothesis tying
it to `σ` — no `IsStandardLift σ ψ g Φhat`, no `K1At σ.w Φhat _`, no `SlotDecomp σ`
(all available in `Defs`/`DefsT` but not assumed here).

**Counterexample (in the layer-L1 base stage, which satisfies every `Stage` axiom).**
Base stage: `Φ = X`, `e = 1`, `h = 1`, `s = 1`, `t = 0`, `wPrev = w`,
`w (Σ aᵢ Xⁱ) = minᵢ (v_p(aᵢ) + i)` over the support, `R` = the leading form of the graded
ring specialized by `p̄ ↦ 1`, `X̄ ↦ z` (faithful on each graded piece since `v + i = γ`
pins `v` from `i`; this validates `hRne/hRmul/hRadd/hRlt`, and `hRΦ/hS5/hS6a/hS6b/hK1`
hold by direct computation). Now take
* `Φhat = 1 + X`  (so `w Φhat = 0`, `R Φhat = 1` — the min is attained only at `i = 0`);
* `N = 2`, `f = p + X` with `B₀ = C (p−1)`, `B₁ = 1`  (indeed `f = (p−1) + (1+X)`);
* `f' = p² + X` with `B'₀ = C (p²−1)`, `B'₁ = 1`.

Slot hypotheses hold: `R B₀ = −1 = R B'₀`, `R B₁ = 1 = R B'₁` (`hslotR`), and
`w B₀ = 0 = w B'₀`, `w B₁ = 0 = w B'₁` (`hslotw`). But the minimal-weight block TOTALLY
CANCELS residually (`−1 + 1·R(Φhat) = 0`), so `w` jumps and `R f` is read off sub-leading
data that the slot residuals do NOT pin: `w (p+X) = 1` with BOTH monomials minimal, so
`R (p+X)` has two nonzero coefficients, while `w (p²+X) = 1` is attained only at `X`, so
`R (p²+X)` is a single monomial. Hence `R f ≠ R f'`: the conclusion fails.

**Why D.8 (TRANSPORT, MOVES ~2326-2358) is not violated.** D.8's determinacy is stated at
the STANDARD LIFT `Φ̂` of the stage, where K1(Φ̂/w) plus D.3(d) give the minimizing slot
terms DISTINCT ψ-orders — total cancellation of the minimal block is impossible there.
That graded-independence input is exactly `SlotDecomp σ` (DefsT, DEF-1 independence half)
plus a `K1At`-style link between `Φhat` and `σ.w`; the R3 statement carries neither.
(The round-2→3 repair added `hslotw`, which fixes the unequal-weight strata via `hRlt`,
but not the equal-weight cancellation stratum above.)

**Owner action needed**: add `SlotDecomp σ` and tie `Φhat` to `σ` (e.g. `IsStandardLift`
+ `K1At σ.w Φhat (σ.w Φhat)`), or restate at `Φhat = σ.Φ`. Under the statement fence the
only honest body is `sorry`. -/

theorem L5_landTransport {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (f f' : Polynomial ℤ_[p]) (hf : f ≠ 0) (hf' : f' ≠ 0) (B B' : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hd : IsDevelopment Φhat f B N) (hd' : IsDevelopment Φhat f' B' N) (hslotR : ∀ j, j < N → σ.R (B j) = σ.R (B' j)) (hslotw : ∀ j, j < N → σ.w (B j) = σ.w (B' j)) : σ.R f = σ.R f' := by
  sorry

end LeanUrat.Moves
