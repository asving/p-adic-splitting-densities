/-
Kernels/KC7 — BP4-c5 E-phase skeleton for unit KC7: the consumer-glue
verify-only record — (COMP-hΣ) + HMC ⟹ (COMP-Σ)
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §1 (G-C) consumers + §4 KC7;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

THE RECORD THIS UNIT COMPILES: the built V5-5 conditional
(`MovesV.comp_sigma`, MovesV/V5_compsig.lean:26, and its HasSum packaging
`comp_sigma_hasSum`, ibid.:81) consumes `HMC TE D` VERBATIM and nothing
stronger.  Checked against the source this pass:
· the hypothesis is literally `(hHMC : HMC TE D)` — the bare open kernel of
  MovesV/Defs.lean:1180, not HMCAug, not a refinement-carrier variant;
· HMC enters the proof at exactly ONE point: `comp_upgrade X D Xs hHMC`
  (V4-12(a), MovesV/V4_naming.lean) producing `Factorizes X D`;
· the (COMP-hΣ) input (`comp_hsum`, MovesV/V5_comphs.lean) is HMC-FREE by
  its own header ("(COMP-hΣ) GIVEN XHD-d/s, NO HMC").
The theorem below RE-STATES comp_sigma's conclusion under the identical
hypothesis surface; its expected discharge is the one-line verbatim
application `comp_sigma cc P X U Xs hTie hHMC ε β₀ γ hq` — compiling it IS
the machine-checked confirmation that the consumer edge (COMP-Σ)/V5-5 pulls
through the named `HMC` Prop only (what KC5's reduction and any future
perimeter/named-law discharge would feed).

deps: MovesV V5 modules (import V5_compsig).  difficulty: routine-opus,
record-plus-one-line; no new proof content expected.

Build: cd lean && lake build LeanUrat.Kernels.KC7
-/
import LeanUrat.MovesV.V5_compsig

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesV

/-- KC7 — the verify-only consumer-glue record: (COMP-Σ)'s algebraic collapse
under EXACTLY the hypothesis surface of the built `MovesV.comp_sigma`, with
the HMC hypothesis stated as the bare `HMC TE D` (nothing stronger).
Expected discharge: `comp_sigma cc P X U Xs hTie hHMC ε β₀ γ hq` verbatim —
see the file header for the recorded source check. -/
theorem compSigma_consumes_hmc_verbatim {n : ℕ} {C : CtsFamily n}
    {S : StepSys n} {V : CtsMeasured n C S} {TE : TmplEvents n S}
    {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (Xs : XHDs n S X D) (hTie : MarkFiberTie TE) (hHMC : HMC TE D)
    (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ}
    (hq : q₀ ∈ V.Pools) :
    iotaEps cc ε β₀ q₀ * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
        * gcVal Xs γ q₀
      = iotaEps cc ε β₀ q₀ * stepProdVal V Xs γ q₀ := by
  sorry

end LeanUrat.Kernels
