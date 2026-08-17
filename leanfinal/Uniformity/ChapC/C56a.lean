/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C15
import Uniformity.ChapC.C44
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C56a — the base-resolved K₂-digit lift

**Chapter C, NODE C.56a** [def] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §7, the A-7 SCC repair's split-out of C.56).  Three
definitions, transcribed byte-exactly from `leanspec/Leanspec/ChapC.lean`:

* `k2Coord` — the canonical-representative digit read of `s ∈ K₂` over the `β`-basis (the
  chosen `AdjoinRoot.mk`-preimage's coefficient; C.14a's `stageCoord` handles the `η`-basis
  leg inside `k2DigitLift`).
* `n2Exp` — the two-step `n̂₂`-solve (C.15/C.16's pattern at `(u₂, e₂)` composed with the
  frame solve): at height `m` it returns `(a₀, i, b)` with
  `e₁e₂a₀ + ie₂h + bu₂ = m`, `i < e₁`, `b < e₂` (the exactness/`deg < D₂` companions are
  fleet-time nodes, not this def's obligation).
* `k2DigitLift` — the `.62` TERMINAL display: the base-resolved lift
  `Σ_{r,t} d_{r,t}·M_{r,t}(m)` with `Δ(r,t) = e₁e₂h·r + e₂u₂·t`.  The frozen fixed-base
  display is DEAD (its compensating `π`-exponent goes non-integer at seam-live heights —
  the FR-A counter-instance `11/2 ∉ ℤ`); the inverse-twist normalization is pinned by the
  exact-height/`deg < D₂` companions at fleet time (determination recorded in the
  blueprint SIGNATURE block).

## Status

Definitional (no proof obligation).  Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.56a (a)** — the `β`-basis digit read on `K₂`: the `t`-th coefficient of the chosen
`AdjoinRoot.mk`-preimage. -/
noncomputable def k2Coord {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (t : ℕ) :
    F.stageField H₀ hpin :=
  (((AdjoinRoot.mk_surjective s).choose).coeff t)

/-- **C.56a (b)** — the two-step `n̂₂`-solve: `(a₀, i, b)` at height `m`. -/
noncomputable def n2Exp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) : ℕ × ℕ × ℕ :=
  let b := towerSolve T.u₂ T.e₂ m
  let m' := (m - b * T.u₂) / T.e₂
  ((m' - F.slotIdx m' * F.h) / F.e₁, F.slotIdx m', b)

/-- **C.56a (c)** — the base-resolved `K₂`-digit lift (the `.62` TERMINAL display). -/
noncomputable def k2DigitLift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (m : ℕ) : Polynomial O :=
  ∑ r ∈ Finset.range F.f₁, ∑ t ∈ Finset.range T.f₂,
    Polynomial.C
        (resLift (F.stageCoord H₀ hpin (k2Coord T s t) r)
          * π ^ (n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).1)
      * Polynomial.X
          ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.1 + F.e₁ * r)
      * F.key ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.2 + T.e₂ * t)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.k2Coord
#print axioms Uniformity.Density.Tower.n2Exp
#print axioms Uniformity.Density.Tower.k2DigitLift

end AxCheck
