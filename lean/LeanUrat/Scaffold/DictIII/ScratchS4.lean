import LeanUrat.Scaffold.DictIII.CU2t

namespace LeanUrat.Scaffold.DictIII

namespace S4Refute

open Polynomial

/-- The single TERMINAL node (sel = none): row T5, all numeric fields minimal. -/
def nu0 : ENodeData :=
  { e := 1, h := 1, ℓ := 1, s := 0, u := 0, sel := none, inc := false
    he := le_refl 1, hh := le_refl 1, hcop := by norm_num, hl := le_refl 1
    hsel := by intro gμ hgμ; simp at hgμ }

/-- A length-1 history whose single node is terminal, over F = ZMod 2, a₀ = 1. -/
noncomputable def H0 : EHist 2 (ZMod 2) :=
  { base := ⊤
    psi0 := X - C 1
    hpsi0 := ⟨monic_X_sub_C 1, irreducible_X_sub_C 1⟩
    a0 := 1
    ha0 := le_refl 1
    nodes := [nu0]
    fld := fun _ => ⊤
    psihat := fun _ => X - C 1
    hpsihat := fun _ => ⟨monic_X_sub_C 1, irreducible_X_sub_C 1, by
      intro hXC
      have h0 := congrArg (fun q => q.coeff 0) hXC
      simp at h0⟩ }

/-- Garbage semantic data: EMPTY principal-side lists everywhere, rootOrder 1. -/
noncomputable def D0 : GMNData (X : Polynomial ℤ_[2]) (Theta H0) :=
  { principalSides := fun _ => []
    residualOrder := fun _ => 0
    residualDegree := fun _ => 0
    rootOrder := 1 }

/-- The (unique possible) lawful reader for `D0`: every lookup returns none. -/
noncomputable def R0 : GMNReader (X : Polynomial ℤ_[2]) (Theta H0) D0 :=
  { side := fun _ => none
    side_spec := by intro i S; simp [D0]
    side_unique := by intro i S T hS _ _ _; simp [D0] at hS
    resOrd := fun _ => 0
    resOrd_spec := fun _ => rfl
    rootOrd := 1
    rootOrd_spec := rfl
    resDeg_eq_sideDeg := by intro i S h; simp at h }

theorem hdec0 : DecIrr H0 ∨ DecHen (X : Polynomial ℤ_[2]) H0 :=
  Or.inr ⟨rfl, Or.inl rfl⟩

theorem hcons0 : ConsF (X : Polynomial ℤ_[2]) H0 D0 R0 := by
  refine ⟨rfl, ?_⟩
  intro i ν h
  simp [EHist.continuingPart, H0, nu0] at h

theorem hsq0 : ∀ φ : Polynomial (ZMod 2), Irreducible φ →
    ¬φ ^ 2 ∣ Polynomial.map (PadicInt.toZMod (p := 2)) (X : Polynomial ℤ_[2]) := by
  intro φ hφ hdvd
  rw [Polynomial.map_X] at hdvd
  have hsf : Squarefree (X : Polynomial (ZMod 2)) :=
    Polynomial.separable_X.squarefree
  exact hφ.not_isUnit (hsf φ (by rwa [← sq]))

/-- REFUTATION: the ∀-closure of the §1.9 `cu2t_readForcing` display, under the
sole type-correct reading of its `hsq` reduction map (`PadicInt.toZMod`), is
FALSE. -/
theorem cu2t_readForcing_false :
    ¬ (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F]
        (f : Polynomial ℤ_[p]) (H : EHist p F)
        (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
        (DecIrr H ∨ DecHen f H) → ConsF f H D R →
        (∀ φ : Polynomial (ZMod p), Irreducible φ →
          ¬φ ^ 2 ∣ Polynomial.map PadicInt.toZMod f) →
        ∃! S, S ∈ D.principalSides H.nodes.length ∧ S.ℓ = 1) := by
  intro hthm
  obtain ⟨S, ⟨hS, -⟩, -⟩ := hthm 2 (ZMod 2) X H0 D0 R0 hdec0 hcons0 hsq0
  simp [D0] at hS

end S4Refute

end LeanUrat.Scaffold.DictIII
