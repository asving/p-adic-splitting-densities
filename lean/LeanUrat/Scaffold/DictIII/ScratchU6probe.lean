import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.Scaffold.DictIII.Locality
import LeanUrat.Scaffold.DictIII.Window

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

-- probe 2: dependency identifiers at this pin
#check @cu1
#check @read_locality
#check @realEquiv_of_m6

-- probe 3 (positive): the one non-elided binder group of the §1.8 display
example (Nstar : EHist p F → ℕ) (dress : EHist p F → MovesC.History p F)
    (hmaj : NstarMaj Nstar readCeil dress) : True := trivial

-- probe 1: the §1.8 display transcribed verbatim (elided)
theorem cu1_lvl … (hmaj : NstarMaj Nstar readCeil dress) …

end LeanUrat.Scaffold.DictIII
