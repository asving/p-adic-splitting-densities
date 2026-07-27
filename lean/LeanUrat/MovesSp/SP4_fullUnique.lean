/-
Unit Sp.fullUnique — moves_ref: "(i) At each fixed (tag, D, w, W) there is AT
MOST ONE full letter … every field determined."
deps: Sp.fullForcing. sketch: Species.ext; every remaining field pinned by
full_forces + (G2)/(G3) + sel = some (1, W). difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem full_unique {n} {s s' : Species} (hcs : Coherent s)
    (hbs : Budget n s) (hcs' : Coherent s') (hbs' : Budget n s') (hf : IsFull s)
    (hf' : IsFull s') (htag : s.tag = s'.tag) (hD : s.D = s'.D) (hw : s.w = s'.w)
    (hW : s.W = s'.W) : s = s' := sorry

end LeanUrat.MovesSp
