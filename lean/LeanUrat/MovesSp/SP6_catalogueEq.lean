/-
Unit Sp.n3catalogueEq — moves_ref: "**Definition (the raw catalogue; rev 3 …)**
𝒮_n^raw := the least set …" + "[RE-VERIFIED against the rev-3 definition: …]".
deps: Sp.memCoherent, Sp.speciesEnumComplete, Sp.reflSucc, Sp.n3rootLetters,
Sp.n3closureStep, Sp.n3reachable. sketch: (→) induction on InCatalogue: root case
via n3rootLetters (s ∈ enum by speciesEnumComplete); step via n3closureStep. (←)
each letter: root case by rootAdmissibleB + refl lemmas; non-root via n3reachable
+ `.step`. difficulty: medium.
-/
import LeanUrat.MovesSp.DefsN3
import LeanUrat.MovesSp.SP0_reflSucc
import LeanUrat.MovesSp.SP2_speciesEnum
import LeanUrat.MovesSp.SP6_rootLetters
import LeanUrat.MovesSp.SP6_closureStep
import LeanUrat.MovesSp.SP6_reachable

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- `groupR` sits at the head of `catalogue3 = groupR ++ …`, so its members are
catalogue members. -/
private theorem groupR_subset_catalogue {s : Species} (h : s ∈ groupR) :
    s ∈ catalogue3 := by
  simp only [catalogue3, List.mem_append]
  tauto

theorem SnRaw3_eq : ∀ s, InCatalogue 3 s ↔ s ∈ catalogue3 := by
  intro s
  constructor
  · -- (→) induction on the closure derivation.
    intro h
    induction h with
    | @root s ha =>
        -- ROOT letter: coherent + admissible ⇒ in the generated enumeration,
        -- where `root3_enum_check` reads off membership in `groupR`.
        have hc : Coherent s := ha.2.1
        have hb : Budget 3 s := ha.2.2
        have hen : s ∈ speciesEnum 3 := speciesEnum_complete hc hb
        have hrb : rootAdmissibleB 3 s = true := (rootAdmissibleB_iff 3 s).mpr ha
        have hcheck : (rootAdmissibleB 3 s == groupR.contains s) = true :=
          List.all_eq_true.mp root3_enum_check s hen
        rw [hrb, Bool.true_beq] at hcheck
        exact groupR_subset_catalogue (List.mem_of_elem_eq_true hcheck)
    | @step s s' hs hstep ih =>
        -- STEP: the target is coherent+admissible ⇒ in the enumeration, and
        -- `closure_step3` at the (in-catalogue) source keeps it in the catalogue.
        have hc' : Coherent s' := hstep.2.1
        have hb' : Budget 3 s' := hstep.2.2
        have hen' : s' ∈ speciesEnum 3 := speciesEnum_complete hc' hb'
        have hsb : succStepB 3 s s' = true := (succStepB_iff 3 s s').mpr hstep
        have hall :
            ((speciesEnum 3).all fun s' => !(succStepB 3 s s') || catalogue3.contains s')
              = true :=
          List.all_eq_true.mp closure_step3 s ih
        have hs2 : (!(succStepB 3 s s') || catalogue3.contains s') = true :=
          List.all_eq_true.mp hall s' hen'
        rw [hsb] at hs2
        simp only [Bool.not_true, Bool.false_or] at hs2
        exact List.mem_of_elem_eq_true hs2
  · -- (←) every catalogue letter is reachable: either root-admissible, or one
    -- SuccStep from a root letter (`reachable3`).
    intro h
    have hr := List.all_eq_true.mp reachable3 s h
    rw [Bool.or_eq_true] at hr
    rcases hr with hroot | hany
    · exact InCatalogue.root ((rootAdmissibleB_iff 3 s).mp hroot)
    · rw [List.any_eq_true] at hany
      obtain ⟨r, hrmem, hrsucc⟩ := hany
      have hradm : rootAdmissibleB 3 r = true :=
        List.all_eq_true.mp groupR_admissible r hrmem
      have hrIn : InCatalogue 3 r := InCatalogue.root ((rootAdmissibleB_iff 3 r).mp hradm)
      exact InCatalogue.step hrIn ((succStepB_iff 3 r s).mp hrsucc)

end LeanUrat.MovesSp
