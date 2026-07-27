/-
Unit Sp.n3menuMap [REV 4, Codex-6: Bool-routed; Codex-7 FIXED: the closure wiring
is now IN the unit — global exactness over ALL Species, the sealed menu display's
real strength] — moves_ref: "The n = 3 menu map (Out, sealed; stage laws of
SP.4). ▸(1,1) → Q1; ▸(1,2) → Q2 letters; ▸(1,3) → Q3 letters; ▸(2,1) → I(2,2);
▸(3,1) → I(3,3); e=2 letters → I(2,1); e=3 letters → I(3,1)."
deps: Sp.reflSucc, Sp.speciesEnumComplete, Sp.n3closureStep. sketch: (→) a
SuccStep target carries Coherent ∧ Budget BY DEFINITION ⇒ s' ∈ speciesEnum 3 ⇒
s' ∈ catalogue3 (closure_step3, via reflSucc) ⇒ menu3_local reads off membership.
(←) menuMap3 s ⊆ catalogue3, so menu3_local's ← direction applies. THE CHAIN:
SuccStep → (Coherent ∧ Budget) → enum → closure → catalogue → local table — no
off-catalogue SuccStep edge can exist, which is exactly the sealed exactness.
difficulty: medium (perf, moderate).
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem menu3_local : (catalogue3.all fun s => catalogue3.all fun s' =>
    succStepB 3 s s' == (menuMap3 s).contains s') = true := sorry

theorem menu3_exact_global (s : Species) (hs : s ∈ catalogue3)
    (s' : Species) : SuccStep 3 s s' ↔ s' ∈ menuMap3 s := sorry

end LeanUrat.MovesSp
