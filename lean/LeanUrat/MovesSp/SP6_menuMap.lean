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

PROOF STATUS (as built, P-phase complete — this unit is now sorry-free):
  * `menu3_local` : PROVED, `by decide`, axiom-clean (self-contained, only DefsN3;
    catalogue3/succStepB/menuMap3 are all structural, no well-founded recursion, so
    the kernel reduces the Bool table over the 53×53 grid).
  * `menu3_exact_global` : PROVED in full — both ↔-directions machine-checked. The
    `succStepB`/`SuccStep` reflection (`succStepB_iff`, from Sp.reflSucc), the
    `menu3_local` read-off, `menuMap3_subset`, and the SuccStep-closure of
    `catalogue3` (`catalogue3_succ_closed`) are all real; no gap remains.
  * `catalogue3_succ_closed` : PROVED (below). This is the enumeration-completeness
    spine — a coherent+budget SuccStep target of a catalogue member is again a
    catalogue member — now discharged by the one-line cite anticipated in the
    original plan: `(SnRaw3_eq s').mp (InCatalogue.step ((SnRaw3_eq s).mpr hs) hstep)`,
    routing through `SnRaw3_eq` (Sp.n3catalogueEq, SP6_catalogueEq) and the abstract
    `InCatalogue.step`. The old kernel-stuck `decide` route (closure_step3, blocked
    because `speciesEnum`'s well-founded recursion does not reduce) is no longer on
    the path.
-/
import LeanUrat.MovesSp.DefsN3
import LeanUrat.MovesSp.SP0_reflSucc
import LeanUrat.MovesSp.SP6_catalogueEq

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- The sealed n = 3 menu table, Bool-routed: on the 53×53 catalogue grid,
`succStepB 3 s s'` agrees with membership of `s'` in `menuMap3 s`. Self-contained
`decide` (no `speciesEnum`, hence no well-founded recursion to block the kernel). -/
theorem menu3_local : (catalogue3.all fun s => catalogue3.all fun s' =>
    succStepB 3 s s' == (menuMap3 s).contains s') = true := by decide

/-- `menuMap3 s ⊆ catalogue3` for every `s`: each branch of the menu returns a
sublist of the catalogue (one of the five groups, or a single POST-INC landing
letter, or `[]`). -/
theorem menuMap3_subset (s s' : Species) (h : s' ∈ menuMap3 s) : s' ∈ catalogue3 := by
  have hg1 : ∀ x ∈ groupQ1, x ∈ catalogue3 := by
    intro x hx; simp only [catalogue3, List.mem_append]; tauto
  have hg2 : ∀ x ∈ groupQ2, x ∈ catalogue3 := by
    intro x hx; simp only [catalogue3, List.mem_append]; tauto
  have hg3 : ∀ x ∈ groupQ3, x ∈ catalogue3 := by
    intro x hx; simp only [catalogue3, List.mem_append]; tauto
  unfold menuMap3 at h
  split at h
  · simp at h
  · split_ifs at h <;>
      first
        | (rw [List.mem_singleton] at h; subst h; decide)
        | exact hg1 _ h
        | exact hg2 _ h
        | exact hg3 _ h
        | simp at h

/-- PROVED (via Sp.n3catalogueEq's `SnRaw3_eq` + the abstract `InCatalogue.step`):
`catalogue3` is closed under `SuccStep` at n = 3 — a coherent, budget-admissible
successor of a catalogue member is again a catalogue member. This is the
enumeration-completeness content (the spine lemma), discharged here by the one-line
cite anticipated in the header note, so `menu3_exact_global` is fully machine-checked
with no remaining gap. -/
private theorem catalogue3_succ_closed (s : Species) (hs : s ∈ catalogue3)
    (s' : Species) (hstep : SuccStep 3 s s') : s' ∈ catalogue3 :=
  (SnRaw3_eq s').mp (InCatalogue.step ((SnRaw3_eq s).mpr hs) hstep)

/-- Global n = 3 menu exactness over ALL Species: for a catalogue member `s`, the
`SuccStep` targets are EXACTLY the entries of `menuMap3 s` — no off-catalogue edge
can exist. Reduces to `catalogue3_succ_closed` (→ direction) + `menuMap3_subset`
(← direction) + the sealed table `menu3_local` + the reflection `succStepB_iff`. -/
theorem menu3_exact_global (s : Species) (hs : s ∈ catalogue3)
    (s' : Species) : SuccStep 3 s s' ↔ s' ∈ menuMap3 s := by
  constructor
  · intro hstep
    have hcat' : s' ∈ catalogue3 := catalogue3_succ_closed s hs s' hstep
    have hrow : (succStepB 3 s s' == (menuMap3 s).contains s') = true :=
      List.all_eq_true.mp (List.all_eq_true.mp menu3_local s hs) s' hcat'
    have heq : succStepB 3 s s' = (menuMap3 s).contains s' := eq_of_beq hrow
    have hb : succStepB 3 s s' = true := (succStepB_iff 3 s s').mpr hstep
    rw [hb] at heq
    exact List.mem_of_elem_eq_true heq.symm
  · intro hmenu
    have hcat' : s' ∈ catalogue3 := menuMap3_subset s s' hmenu
    have hrow : (succStepB 3 s s' == (menuMap3 s).contains s') = true :=
      List.all_eq_true.mp (List.all_eq_true.mp menu3_local s hs) s' hcat'
    have heq : succStepB 3 s s' = (menuMap3 s).contains s' := eq_of_beq hrow
    have hc : (menuMap3 s).contains s' = true := List.elem_eq_true_of_mem hmenu
    rw [hc] at heq
    exact (succStepB_iff 3 s s').mp heq

end LeanUrat.MovesSp
