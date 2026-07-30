/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# BP1 group C — the solve family + the checksum transport (IB-C1 … IB-C5)

E-phase skeletons per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.5
(†10a)–(†10c) / §4 group C, cluster BP1-c6.  File name per the blueprint's §4
prescription ("New files: … BridgeSolve.lean (C)").  Units in this file:

* IB-C1  `bridgeSolve` + `bridgeSolve_r_is_solve` (rfl) + `bridgeSolve_ok`
* IB-C2  `bridge_evalAt_sigmas_one` — per-prime evaluation-1 (†10b step ii)
* IB-C3a `evalAt_eq_num_div_denom` + `num_eval_eq_zero_of_evalAt_eq_zero`
* IB-C3b `eq_zero_of_evalAt_primes_zero` — infinite-roots vanishing
* IB-C4  `rs4_checksum_bridge` — Σ σ, R σ = 1 in ℚ(q) (†10b)
* IB-C5  `bridgeSolveSeam` — the `SolveSeam` assembly given the series_tie row

IB-C6 (the n = 2 OM-gate consistency display) is NOT here: it is gated on the
S-area's n = 2 `UCarriers` pack (blueprint §4, ADJ).

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase charge):
1. Where the sketch writes "evalAt p g" with a bare membership conjunct
   (`g ∈ OKat p ∧ evalAt p g = 0`), the membership is packaged as the ∃-binder
   `∃ hok : g ∈ OKat p, evalAt p ⟨g, hok⟩ = …` — `evalAt` is only defined ON the
   subring, and this is the repo's own idiom (`RS4Chain.rsh_interp`,
   `MovesS.W17ii`, `AVAgree`).  Applied in IB-C2 and IB-C3b.
2. IB-C3a's "with g.denom.eval q₀ ≠ 0" conjunct is not restated: it IS the
   hypothesis `hok`, read through `MovesS.mem_OKat_iff` (definitional).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-! ## IB-C1 — the solve family pinned to the real shallow convolution (†10a) -/

/-- IB-C1 (def): `bridgeSolve C hdet : SolveData n` — THE per-σ fixed rational
    function, pinned to `MovesS.Rsh` (RS.1-SH's shallow convolution over the
    blockSolve) at the chain's own `WshP` presentation, read through the
    vocabulary bridge `vmap`.  `hdet : MovesS.DetHyp C.T C.RB C.hK` is
    p-INDEPENDENT (a symbolic ℚ(q) determinant nonvanishing), carried by
    `BridgePre` as a named warranted hypothesis (blueprint §3.7; adjudication Q3
    RATIFIED).  With `hdet` fixed, `r_is_solve` is `rfl` — no dite junk branch
    (kills RISK R5 by construction).  Deps: — (statement); A6's `vmap_mem` face
    already exists as `UCarriers.vmap_mem_Sigmas` (DefsCarriers). -/
noncomputable def bridgeSolve {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK) : SolveData n where
  R := fun σ =>
    MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP (vmap C.T σ)

/-- IB-C1 (law 1): `r_is_solve` at the constructed family — for ANY determinant
    witness `hdet'`, `(bridgeSolve C hdet).R σ` IS the real solve output.
    Blueprint (†10a)/(†10c): `rfl` by definitional proof irrelevance of the
    `DetHyp` Prop binder. -/
theorem bridgeSolve_r_is_solve {n : ℕ} (C : UCarriers n)
    (hdet hdet' : MovesS.DetHyp C.T C.RB C.hK) (σ : SplittingType n) :
    (bridgeSolve C hdet).R σ
      = MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet' C.Fam C.chain.WshP (vmap C.T σ) :=
  rfl

/-- IB-C1 (law 2): `bridgeSolve_ok` — OKat membership at every prime.  Sketch:
    `(p : ℚ) ∈ C.chain.PrimePools` by `prime_base`; `vmap C.T σ ∈ C.chain.Sigmas`
    by `UCarriers.vmap_mem_Sigmas`; then `C.chain.rsh_interp` supplies the
    membership witness (its `∃ hok` head).  Deps: — (repo-built vocabulary only). -/
theorem bridgeSolve_ok {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK) (p : ℕ) (hp : p.Prime)
    (σ : SplittingType n) :
    (bridgeSolve C hdet).R σ ∈ MovesS.OKat ((p : ℚ)) := sorry

/-! ## IB-C2 — per-prime evaluation-1 (†10b step ii) -/

/-- IB-C2: at EVERY prime p, the σ-indexed sum of the real solve outputs over the
    chain's exact σ-index `Sigmas` evaluates (through the `evalAt` ring hom on the
    regular subring at p) to 1:
    `evalAt p (∑ s ∈ Sigmas, Rsh s) = ∑ Rval s p = decidedTotal p = 1`.
    Sketch: OKat membership per summand from `rsh_interp` (so the sum is in the
    subring — subring closure); `map_sum` for `evalAt`; then
    `rsh_interp` + `rs1_equates` + `x3_total`; the cast-back needs `rsh_interp`'s
    ℚ→ℝ equality read injectively (`Rat.cast_injective` — `Rval` is ℝ-valued).
    Membership packaged as the ∃-binder (header resolution 1).
    Deps: C1.  Consumer: C4 (via C3a/C3b's num/den translation). -/
theorem bridge_evalAt_sigmas_one {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK) (p : ℕ) (hp : p.Prime) :
    ∃ hok : (∑ s ∈ C.chain.Sigmas,
        MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP s)
          ∈ MovesS.OKat ((p : ℚ)),
      MovesS.evalAt ((p : ℚ))
        ⟨∑ s ∈ C.chain.Sigmas,
          MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP s, hok⟩ = 1 :=
  sorry

/-! ## IB-C3a — the OKat → num/den translation -/

/-- IB-C3a (main): for `g ∈ OKat q₀` the subring evaluation is the literal
    num/den quotient: `evalAt q₀ ⟨g, hok⟩ = g.num.eval q₀ / g.denom.eval q₀`.
    (The sketch's `g.denom.eval q₀ ≠ 0` conjunct IS `hok` via `mem_OKat_iff` —
    header resolution 2.)  Sketch: this is where the archaeology lives —
    `RatFunc.eval` vs the OKat subring presentation; reuse the
    `SolveSeam.rs4_eval` calc block's cast patterns in reverse
    (`RatFunc.eval_eq_num_div`-flavored API at the id ring hom).
    Deps: —. -/
theorem evalAt_eq_num_div_denom {q₀ : ℚ} (g : MovesS.Qq)
    (hok : g ∈ MovesS.OKat q₀) :
    MovesS.evalAt q₀ ⟨g, hok⟩ = g.num.eval q₀ / g.denom.eval q₀ := sorry

/-- IB-C3a (corollary): a vanishing regular evaluation kills the numerator at the
    point: `evalAt q₀ ⟨g, hok⟩ = 0 → g.num.eval q₀ = 0`.  Sketch: from the main
    identity, `div_eq_zero_iff` + the denominator nonvanishing (= `hok`).
    Deps: IB-C3a main. -/
theorem num_eval_eq_zero_of_evalAt_eq_zero {q₀ : ℚ} (g : MovesS.Qq)
    (hok : g ∈ MovesS.OKat q₀) (h0 : MovesS.evalAt q₀ ⟨g, hok⟩ = 0) :
    g.num.eval q₀ = 0 := sorry

/-! ## IB-C3b — infinite-roots vanishing -/

/-- IB-C3b: a fixed rational function regular and vanishing at EVERY rational
    prime is 0.  Sketch: by IB-C3a's corollary `g.num.eval p = 0` at every
    cast-prime; the primes are infinite (`Nat.infinite_setOf_prime`) and cast
    injectively into ℚ, so `g.num` has infinitely many roots
    (`Polynomial.eq_zero_of_infinite_isRoot`), hence `g.num = 0`, hence `g = 0`
    (`RatFunc.num_eq_zero_iff`-flavored: num vanishes iff the function does).
    Membership packaged as the ∃-binder (header resolution 1).
    Deps: C3a.  Consumer: C4. -/
theorem eq_zero_of_evalAt_primes_zero (g : MovesS.Qq)
    (h : ∀ p : ℕ, p.Prime → ∃ hok : g ∈ MovesS.OKat ((p : ℚ)),
      MovesS.evalAt ((p : ℚ)) ⟨g, hok⟩ = 0) :
    g = 0 := sorry

/-! ## IB-C4 — the checksum transport (†10b, "the area's prettiest theorem") -/

/-- IB-C4: `rs4_checksum_bridge` — the ℚ(q) checksum at the constructed solve
    family: `∑ σ : SplittingType n, (bridgeSolve C hdet).R σ = 1`.
    Sketch (†10b): (i) transport the Fintype sum to `∑ s ∈ C.chain.Sigmas, Rsh s`
    through the vmap bijection (IB-A7's `sum_vmap_eq_sum_Sigmas`, †1c);
    (ii) IB-C2: the sum evaluates to 1 at every prime; (iii) apply IB-C3b to
    `g := (∑ σ, R σ) − 1` (a difference of OKat members is OKat; its evaluation
    is 0 at every prime), so g = 0.  This feeds `CapstoneLedger.rs4_checksum`
    (assembly IB-F3) and, through the DERIVED `SolveSeam.rs4_eval`, U6's
    un-bracket.  Deps: A7 (other cluster — proof-time only), C2, C3b. -/
theorem rs4_checksum_bridge {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK) :
    ∑ σ : SplittingType n, (bridgeSolve C hdet).R σ = 1 := sorry

/-! ## IB-C5 — the SolveSeam assembly -/

/-- IB-C5: `bridgeSolveSeam` — the `SolveSeam` assembly at the constructed solve
    family, GIVEN the series_tie kernel row (the named open [3t] premise
    `BridgeKernels.series_tie`, blueprint §3.7: the Haar-mass-vs-measured-chain
    seam — NEVER proved here, consumed as the explicit hypothesis `hseries`).
    Sketch (†10c): `series_tie := hseries`; `r_is_solve := fun _ σ => rfl`
    (definitional proof irrelevance for the hdet binder — IB-C1's law 1).
    Deps: C1.  Consumer: IB-F3 (`bridgeCapstoneLedger`'s `ssrc`). -/
theorem bridgeSolveSeam {n p : ℕ} (C : UCarriers n) {X : ClassifierSpec n p}
    (F : FiberSeries n p X) (hdet : MovesS.DetHyp C.T C.RB C.hK)
    (hseries : ∀ σ : SplittingType n,
      F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) ((p : ℚ)))) :
    SolveSeam n p C F (bridgeSolve C hdet) := sorry

end LeanUrat.MovesU
