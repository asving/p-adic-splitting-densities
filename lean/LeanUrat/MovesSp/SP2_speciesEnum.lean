/-
Unit Sp.speciesEnumComplete — moves_ref: "𝒮_n^raw injects into the encoded set
((G1)–(G6) only shrink it)" [here: the generated candidate list].
deps: Sp.compEnumComplete, Sp.lamEnumComplete. sketch: coherence pins a/d/slots
from (s0, e, ℓ) ((G2)/(G3)); budget pins every generator range ((B1)–(B5));
membership by product-list mem lemmas. difficulty: medium-hard.
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem speciesEnum_complete {n : ℕ} {s : Species} (hc : Coherent s)
    (hb : Budget n s) : s ∈ speciesEnum n := sorry

end LeanUrat.MovesSp
