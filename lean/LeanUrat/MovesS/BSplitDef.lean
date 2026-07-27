/-
Unit U-16a1 `bSplit_def` (medium) — the split exit vector, with the summand's
def-equation PINNED (Fable G3).  moves_ref: "b_e^split(τ)(σ′) := Σ_{o branching}
J_{τ,o}(q) · Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m β_{e_j,τ_j(o)}(σ_j)(q^{δ_j}) [… the
product ranges over ALL branch members]"; "τ-halted members contribute FACTOR 1
with σ_j their verdict value, per §T.4's leaf convention" (S.0): a halted leg is
the verdict-singleton indicator, continuing legs are β at q^δ.
(kTarget lives in Defs.lean — the E-phase fill of the §2.C skeleton.)
E-PHASE NOTE (deviation D-2): `legFactor` guards the member-size bound by dite
(else 0); under DegCons + U-2 (ktri) the guard always holds on split outcomes —
threading ktri through the DEFINITION would make the statement depend on the
sorried U-2.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.DecompFintype
import LeanUrat.MovesS.PowSubst

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

variable {n : ℕ}

/-- The flipped-orientation decomposition Fintype (the displayed binder is
`σ' = ∑ j, g j`); derived from U-11's instance. -/
noncomputable instance decompFintypeFlip {V : Type*} [DecidableEq V] (m : ℕ)
    (σ' : Multiset V) : Fintype {g : Fin m → Multiset V // σ' = ∑ j, g j} :=
  Fintype.ofEquiv {g : Fin m → Multiset V // ∑ j, g j = σ'}
    (Equiv.subtypeEquivRight fun g => eq_comm)

/-- One branch-member leg factor: verdict-halted ⟹ the σ_j-singleton indicator;
continuing ⟹ β at q^δ (the smaller-block solve fed through `powSubst`). -/
noncomputable def legFactor (T : TableShape n) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ)
    (βlt : ∀ e', e' < e → T.State e' → Multiset T.VType → Qq)
    (g : Fin (T.odata e τ o).mem.length → Multiset T.VType)
    (j : Fin (T.odata e τ o).mem.length) : Qq :=
  match ((T.odata e τ o).mem.get j).status with
  | Sum.inl v => if g j = {v} then 1 else 0
  | Sum.inr τ' =>
      if hsz : ((T.odata e τ o).mem.get j).size < e
      then powSubst ((T.odata e τ o).mem.get j).δ (βlt _ hsz τ' (g j))
      else 0

/-- b_e^split (the DegCons argument licenses the smaller-block legs via U-2). -/
noncomputable def bSplit (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T) (e : ℕ) (he : e ∈ Finset.Icc 1 n)
    (βlt : ∀ e', e' < e → T.State e' → Multiset T.VType → Qq)
    (σ' : Multiset T.VType) (τ : T.State e) : Qq :=
  ∑ o ∈ splitOuts T e τ, RB.J e τ o *
    ∑ g : {g : Fin (T.odata e τ o).mem.length → Multiset T.VType // σ' = ∑ j, g j},
      ∏ j, legFactor T e τ o βlt g.1 j

/-- The PINNED def-equation (U-16a1's spec obligation). -/
theorem bSplit_def (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T) (e : ℕ) (he : e ∈ Finset.Icc 1 n)
    (βlt : ∀ e', e' < e → T.State e' → Multiset T.VType → Qq)
    (σ' : Multiset T.VType) (τ : T.State e) :
    bSplit T RB hdc e he βlt σ' τ =
      ∑ o ∈ splitOuts T e τ, RB.J e τ o *
        ∑ g : {g : Fin (T.odata e τ o).mem.length → Multiset T.VType // σ' = ∑ j, g j},
          ∏ j, legFactor T e τ o βlt g.1 j :=
  sorry

end LeanUrat.MovesS
