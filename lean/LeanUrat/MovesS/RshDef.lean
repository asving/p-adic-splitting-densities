/-
Unit U-18 `rsh_def` (medium) — the shallow convolution and THE symbolic R_σ.
moves_ref: "R_σ = Σ_{Ŝ} W_Ŝ(q) · Σ_{σ = σ₀(Ŝ) ⊎ …} ∏ β_{e_i,τ_i}(σ_i)(q^{δ_i})".
Takes `WshP ·` as the W_Ŝ presentation (PolyGeom.val).  The decomposition Fintype
instance is a sorried instance obligation (same class as U-11's).
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.DecompFintype
import LeanUrat.MovesS.PowSubst
import LeanUrat.MovesS.BlockSolve

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- Sorried instance obligation (U-11's class, shifted base point σ₀). -/
noncomputable instance shDecompFintype {T : TableShape n} (Ŝ : Shape T)
    (σ : Multiset T.VType) :
    Fintype {g : Fin Ŝ.k → Multiset T.VType // σ = Ŝ.σ0 + ∑ i, g i} :=
  sorry

/-- The per-shape convolution Σ_{σ = σ₀(Ŝ) ⊎ ⊎ᵢ σᵢ} ∏ᵢ β_{e_i,τ_i}(σ_i)(q^{δ_i}). -/
noncomputable def shConv (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK)
    (Ŝ : Shape T) (σ : Multiset T.VType) : Qq :=
  ∑ g : {g : Fin Ŝ.k → Multiset T.VType // σ = Ŝ.σ0 + ∑ i, g i},
    ∏ i, powSubst (Ŝ.δOf i)
      (blockSolve T RB hdc hK hdet (Ŝ.eOf i) (Ŝ.eIcc i) (Ŝ.τOf i) (g.1 i))

/-- THE one fixed rational function R_σ (RS.2's object, derived not assumed). -/
noncomputable def Rsh (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK)
    (F : ShapeFam T) (WshP : Shape T → PolyGeom) (σ : Multiset T.VType) : Qq :=
  ∑ Ŝ ∈ F.Sh, (WshP Ŝ).val * shConv T M RB hdc hK hdet Ŝ σ

end LeanUrat.MovesS
