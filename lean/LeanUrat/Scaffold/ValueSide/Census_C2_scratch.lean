import Mathlib
import LeanUrat.Scaffold.ValueSide.Census

namespace LeanUrat.Scaffold

-- countermodel A: r = 1, e = (2,1), h = (1,1), f = (1,1)
def cmA : CensusData where
  r := 1
  e := ![2, 1]
  h := ![1, 1]
  f := ![1, 1]
  he := by decide
  hf := by decide
  triangular := by decide
  h_coprime := by decide

example : ∀ β ∈ cmA.onLineSlots, r1Bound cmA β ≤ β := by decide
example : ¬ ∀ β ∈ cmA.onLineSlots, cmA.attainDim β = cmA.d := by decide
example : cmA.r = 1 := rfl

-- countermodel B: r = 1, e = (2,1), h = (1,1), f = (1,2)
def cmB : CensusData where
  r := 1
  e := ![2, 1]
  h := ![1, 1]
  f := ![1, 2]
  he := by decide
  hf := by decide
  triangular := by decide
  h_coprime := by decide

example : ∀ β ∈ cmB.onLineSlots, cmB.attainDim β = cmB.d := by decide
example : ¬ ∀ β ∈ cmB.onLineSlots, r1Bound cmB β ≤ β := by decide
example : cmB.r = 1 := rfl

end LeanUrat.Scaffold
