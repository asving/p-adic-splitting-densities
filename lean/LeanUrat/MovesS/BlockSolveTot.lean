/-
Unit U-16c `blockSolveTot` (medium) — the σ′-FREE totalized triangular solve
(R2-17): `bTot(τ) := Σ_{term o} TG + Σ_{split o} J · ∏_j legTot` (halted legs 1,
continuing legs `powSubst δ (blockSolveTot …)`), and `blockSolveTot e :=
(1 - Kmat)⁻¹ *ᵥ bTot` — the exit-total vector the MARKED pairing consumes.
moves_ref: "the scalar output ι_e^T (I − K_e)^{−1} b_e" (ORIENTATION).
No hdet parameter (Mathlib `⁻¹` total — the R29 clarifier's convention).
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

/-- The totalized branch-member leg factor (the σ′-free face of `legFactor`):
a verdict-halted member contributes the constant FACTOR 1 (its verdict multiset is
summed away in the totalization), a continuing member contributes the smaller-block
totalized solve fed through `powSubst` at its base-change δ.  The `size < e` guard is
the E-phase deviation D-2 (junk `0` off the support; every actual continuing leg has
size `< e` by DegCons + (K-TRI), so the guard is never hit on split outcomes). -/
private noncomputable def legTot (T : TableShape n) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) (βlt : ∀ e', e' < e → T.State e' → Qq)
    (j : Fin (T.odata e τ o).mem.length) : Qq :=
  match ((T.odata e τ o).mem.get j).status with
  | Sum.inl _ => 1
  | Sum.inr τ' =>
      if hsz : ((T.odata e τ o).mem.get j).size < e
      then powSubst ((T.odata e τ o).mem.get j).δ (βlt _ hsz τ')
      else 0

/-- The totalized exit-RHS vector `bTot(τ) := Σ_{term o} TG + Σ_{split o} J · ∏_j legTot`,
parameterized by the strictly-smaller-block totalized solves `βlt`. -/
private noncomputable def bTotVec (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (e : ℕ)
    (βlt : ∀ e', e' < e → T.State e' → Qq) (τ : T.State e) : Qq :=
  (∑ o : T.Out e τ,
      if routeOf (T.odata e τ o) = .termFin then RB.TG e τ o else 0)
  + ∑ o ∈ splitOuts T e τ, RB.J e τ o *
      ∏ j : Fin (T.odata e τ o).mem.length, legTot T e τ o βlt j

/-- Strong-recursion core of `blockSolveTot`: the σ′-free triangular fixed-point
vector `(1 - K_e)⁻¹ *ᵥ bTot_e`, where the split legs feed back the totalized solves at
strictly smaller block sizes (dite-guarded onto `Icc 1 n`; junk `0` off it).
Well-founded on `e`. -/
private noncomputable def blockSolveTotCore (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) (τ : T.State e) : Qq :=
  ((1 - Kmat T RB e (hK e he))⁻¹ *ᵥ
    bTotVec T RB e
      (fun e' hlt τ'' =>
        if he' : e' ∈ Finset.Icc 1 n then
          blockSolveTotCore T RB hdc hK e' he' τ''
        else 0)) τ
termination_by e
decreasing_by exact hlt

noncomputable def bTot (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) : T.State e → Qq :=
  bTotVec T RB e
    (fun e' _ τ'' =>
      if he' : e' ∈ Finset.Icc 1 n then
        blockSolveTotCore T RB hdc hK e' he' τ''
      else 0)

noncomputable def blockSolveTot (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) : T.State e → Qq :=
  (1 - Kmat T RB e (hK e he))⁻¹ *ᵥ bTot T M RB hdc hK e he

end LeanUrat.MovesS
