import Uniformity.ChapI.IFC2

/-! GCW-3 probe: the structure-update re-assembly (read := 1) elaborates, the funnel
re-fires, and the exported read computes to 1 on the live range.  Scratch only. -/

set_option linter.style.longLine false

noncomputable section

namespace GCW3Probe

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower
open IsLocalRing
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C130s18 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130np8 Uniformity.Density.Tower.C132sg2

universe uT uG uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

def s2TowerReadWired : (i : ℕ) → LevelExponentLattice i → (S2DepthTwo h2 hq).fld 2 :=
  fun _ _ => 1

def s2SplitNodeWired (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L] (w : S2LevelOneThreshold) :
    SplitNodePointSource (L := L) (S2DepthTwo h2 hq) (FractionRing (Polynomial O))
      (s2RepositoryRealization h2 hq).receiver (s2RepositoryRealization h2 hq).keys :=
  { s2SplitNode h2 hq L w with towerRead := s2TowerReadWired h2 hq }

def s2FrontierWired (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L] (w : S2LevelOneThreshold) :
    S2SourceFrontier h2 hq (FractionRing (Polynomial O)) L :=
  { s2Frontier h2 hq L w with node := s2SplitNodeWired h2 hq L w }

variable (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

def s2FrontierWiredRealizedInput [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold) :
    RealizedInput (s2ArisingCore h2 hq L)
      (s2FrontierWired h2 hq L w).toCarrier :=
  (s2FrontierWired h2 hq L w).s2RealizedInput

theorem s2Wired_towerReadFamily_live [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j) (g : GaugeLattice.{uG} 2) :
    towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j g = 1 := by
  show (s2FrontierWired h2 hq L wT).toCarrier.node.towerReadFamily0 j
    (gaugeLatticeEquiv 2 g) = 1
  rw [SplitNodePointSource.towerReadFamily0_live _ hj]
  rfl

theorem s2Wired_hread [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j)
    (N : NormSection (GaugeLattice.{uG} 2)) (q : ℤ)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* (s2DepthTwo h2 hq).fld 2) :
    towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j (N.n ((1 : ℕ) * q)) =
      φ ((s2Mu3Calculus h2 hq).Rgr (2 * (1 * 21))
          ((s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21))) := by
  rw [s2Wired_towerReadFamily_live h2 hq L wT hj, IFC2.s2Mu3_read_eq_one h2 hq, map_one]

end GCW3Probe

end
