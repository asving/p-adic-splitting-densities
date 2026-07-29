/-  MovesV unit V3-9b `ent_u_stmt` (RE-KEYED over the census) — (ENT-U):
    over each listed component the census polynomial is CONSTANT across the
    instantiations. -/
import LeanUrat.MovesV.V3_spwordD
import LeanUrat.MovesV.V3_entcount

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- (ENT-U) (owner [2b] M4b, never assumed here).  M1 SOUNDNESS REPAIR
(2026-07-29): the false unscoped-totality shim is DELETED, so `writeHeights`
demands its point's `Order0Perimeter` certificate; (ENT-U) internalizes the
certificates as binders (proof-irrelevant, so the census value does not
depend on the certificate) — statements gaining hypotheses is the honest
cost of the order-0 perimeter family. -/
def EntU {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) : Prop :=
  ∀ (β₀ : S.Cell) (i : V.EntIx β₀), ∃ P : Polynomial ℚ,
    (∀ hb : Order0Perimeter i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base,
      P.natDegree
        ≤ (writeHeights i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base hb).Went) ∧
    ∀ h : Hpt i.1.1.entDim, ((V.entDom i.1.1).comps.get i.1.2).Mem h →
      ∀ (hs : Order0Perimeter i.1.1 h), ∀ q₀ ∈ V.Pools,
        (P.eval q₀ : ℚ) = V.entCensus (writeHeights i.1.1 h hs) β₀ q₀

/-- EntU ⟹ the common P also witnesses EntCount's clause at every ε̊[h] on c
(the one-line corollary; the Realizable guard rides EntCount's own form). -/
theorem entU_witness_on_comp {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (hEU : EntU V) (β₀ : S.Cell) (i : V.EntIx β₀)
    (h : Hpt i.1.1.entDim) (hm : ((V.entDom i.1.1).comps.get i.1.2).Mem h)
    (hs : Order0Perimeter i.1.1 h) :
    ∃ P : Polynomial ℚ, ∀ q₀ ∈ V.Pools,
      (P.eval q₀ : ℚ) = V.entCensus (writeHeights i.1.1 h hs) β₀ q₀ := by
  obtain ⟨P, _, hP⟩ := hEU β₀ i
  exact ⟨P, hP h hm hs⟩

end LeanUrat.MovesV
