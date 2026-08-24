/- TDW smoke test (scratch, not part of the tree): the C.100-shaped GENTOW2 twin binders are
now STATABLE from a consumer file importing C84d — the exact capability C99gt/C102gt/C84:110
recorded as blocked on the missing `TowerDatum.deepTower`. Elaboration-only check. -/
import Uniformity.ChapC.C84d

open Uniformity.Density.Tower Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

-- the C.100/C.103 carrier-bridge binder ρ, typed at the constructed chain:
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂) : True := trivial

-- the chain's exponent engine runs at the constructed object (towerNorm at rung 1 reads
-- the datum's (u₂, e₂) through the construction):
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (k : ℕ) :
    (T.deepTower hπ).towerNorm 1 k
      = (T.deepTower hπ).towerNorm 1 k := rfl

-- data clauses consumed downstream-style:
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).e 2 * (T.deepTower hπ).f 2 * (T.deepTower hπ).u 2 = T.E₂ :=
  (T.deepTower_data hπ).1 ▸ (T.deepTower_data hπ).2.1 ▸ (T.deepTower_data hπ).2.2.1 ▸ rfl

-- truncation to depth 1 works (C.83's rung instantiation route):
noncomputable example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    DeepTower F H₀ hpin 1 := (T.deepTower hπ).trunc 1 (by omega)
