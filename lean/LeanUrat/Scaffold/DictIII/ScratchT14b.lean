import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.MovesD.R7_polFillReduction

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

-- local copy of the landed M6cHyps row (Window.lean), to isolate errors
def M6cHyps' (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop :=
  GRB p F

-- probe 1: BP §1.7 realEquiv_of_m6 VERBATIM (M6cHyps → local copy to isolate)
theorem realEquiv_of_m6 {n : ℕ} {f : Polynomial ℤ_[p]}
    {H : MovesC.History p F}
    (hab : M6ABHyps p F) (hc : M6cHyps' p F)
    (hcoh : MovesC.HistoryCoherent H) :
    MovesJ.ReadsOf p F n f H ↔ MovesD.CanRealizes p F n f H := sorry

-- probe 2: the conclusion RHS alone (independent of M6ABHyps)
#check fun (n : ℕ) (f : Polynomial ℤ_[p]) (H : MovesC.History p F) =>
  MovesD.CanRealizes p F n f H

-- probe 3: the LHS alone (expected fine)
#check fun (n : ℕ) (f : Polynomial ℤ_[p]) (H : MovesC.History p F) =>
  MovesJ.ReadsOf p F n f H

end LeanUrat.Scaffold.DictIII
