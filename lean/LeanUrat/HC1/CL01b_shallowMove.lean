/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL01a_shallowBase
import LeanUrat.HC1.S9_transStage

/-!
# HC1.CL01b_shallowMove — Tshallow's one increment move (BP5 CL-01b)

**Unit CL-01b** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4 CL-01, split
per REVISION 2 finding 11). E-PHASE SKELETON: statements + `sorry` bodies; the def
bodies are the unit's construction slots.

**Informal statement.** The single g = 2 increment of ScratchC6's shallow instance,
read at `TshallowBase`: descend polynomial ψ = z² + z + 1 (genuinely irreducible over
K₀ = F₂), z̄ = a primitive cube root of unity in F₄ˣ, (e′, h′) = (1, h′) with h′ from
(I-aug) — packaged as the child stage `TshallowChild` (K₁ = F₄ = ⊤, e = 1,
deg Φ₁ = 2) and the full `MoveWitness.inc` (TransHyp + TransitionCoreL + child
`StageCoreL`), exactly what `Tower.move` consumes at CL-01c.

**Deps.** CL-01a (`TshallowBase`), DefsTower (`TransHyp`, `MoveWitness`), Moves DefsL
(`TransitionCoreL`, `StageCoreL`), S9_transStage (the recommended proof route).

**Proof sketch.** RECOMMENDED ROUTE: `S1_transHypGate_a.choose_spec` supplies a
TransHyp at ψ = X² + X + 1, g = 2, e′ = 1 for the chosen base stage (CL-01a's
recommended body); `S9_transStage TshallowBase core hyp hEG` (hEG : 1 < e·g = 2,
`by norm_num` after the e-pin) then produces the enriched child
`⟨σ', TransitionCoreL, StageCoreL σ', σ'.K = nextField z̄, σ'.e = e', σ'.h = h'⟩` —
take `TshallowChild := (S9_transStage …).choose` and assemble
`TshallowMove := .inc ψ 2 Φhat 1 h' z̄ hyp core core'`. The K-pin `TshallowChild.K = ⊤`
reduces to `nextField z̄ = ⊤` (F₂(ω) = F₄: the adjoined primitive cube root generates —
a 4-element ambient forces it); the degree pin `deg Φ₁ = 2` is
`TransitionData.child_key` (deg Φ′ = e′·g·deg Φ = 1·2·1).

**E-phase resolutions recorded.**
* e′ = 1 is PINNED in `TshallowMove_spec` (ScratchC6's shallow spec and S1's gate data);
  h′ is left existential (any h′ with (I-aug) works — S1's gate realizes h′ = 3; the
  CL-01c height computation only needs κ₁ > 0, i.e. h′ ≥ 1, which `Stage.hh` gives).
* `TshallowChild.h` is deliberately NOT pinned (same reason).
* The blueprint's "child core′" is carried inside the `MoveWitness.inc` constructor
  (the F-5 enrichment), not as a separate certificate.

**LANDING GATE (§3.1, BINDING).** SIDE-BRANCH unit — see CL01a_shallowBase's module
docstring; the same gate discipline applies verbatim. difficulty: hard-fable
(portfolio cap shared with CL-01a/c). PERMITTED OUTCOME: BLOCKED + the exact
missing-constructor list (feeds Q-2). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-! ### The S1 gate data, re-extracted at `TshallowBase` (CL-01a's `TshallowBase_spec`
is `private` there; `TshallowBase := S1_transHypGate_a.choose` makes the transport
definitional). -/

private lemma baseSpec :
    ∃ (Φhat : Polynomial ℤ_[2]) (h' : ℕ) (zbar : (GaloisField 2 2)ˣ),
      IsBaseStage TshallowBase ∧ StageCoreL TshallowBase ∧
      TshallowBase.Φ = Polynomial.X ∧ TshallowBase.e = 1 ∧ TshallowBase.h = 1 ∧
      TshallowBase.K = ⊥ ∧
      TransHyp TshallowBase (Polynomial.X ^ 2 + Polynomial.X + 1) 2 Φhat 1 h' zbar :=
  S1_transHypGate_a.choose_spec

/-- The chosen standard lift Φ̂ of the shallow increment. -/
private noncomputable def PhiHat : Polynomial ℤ_[2] := baseSpec.choose

/-- The chosen child weight numerator h′ (S1's gate realizes h′ = 3; opaque here). -/
private noncomputable def hP : ℕ := baseSpec.choose_spec.choose

/-- The chosen root z̄ of ψ = z² + z + 1 in F₄ˣ (a primitive cube root of unity). -/
private noncomputable def zb : (GaloisField 2 2)ˣ :=
  baseSpec.choose_spec.choose_spec.choose

private lemma spec2 :
    IsBaseStage TshallowBase ∧ StageCoreL TshallowBase ∧
    TshallowBase.Φ = Polynomial.X ∧ TshallowBase.e = 1 ∧ TshallowBase.h = 1 ∧
    TshallowBase.K = ⊥ ∧
    TransHyp TshallowBase (Polynomial.X ^ 2 + Polynomial.X + 1) 2 PhiHat 1 hP zb :=
  baseSpec.choose_spec.choose_spec.choose_spec

private lemma theHyp :
    TransHyp TshallowBase (Polynomial.X ^ 2 + Polynomial.X + 1) 2 PhiHat 1 hP zb :=
  spec2.2.2.2.2.2.2

/-- The adjudicated S9 increment guard at the shallow read: e·g = 1·2 > 1. -/
private lemma hEG : 1 < TshallowBase.e * 2 := by
  rw [spec2.2.2.2.1]; norm_num

/-- The S9 capstone, fired at the shallow increment. -/
private lemma S9run :
    ∃ σ' : Stage 2 (GaloisField 2 2),
      TransitionCoreL TshallowBase σ' PhiHat 1 hP zb ∧ StageCoreL σ' ∧
      σ'.K = TshallowBase.nextField zb ∧ σ'.e = 1 ∧ σ'.h = hP :=
  S9_transStage TshallowBase spec2.2.1 theHyp hEG

/-- **Tshallow stage 1** (CL-01b construction slot): the child stage of the one g = 2
increment — K₁ = F₄ = ⊤, e = e′ = 1, key degree 2. Body: the `S9_transStage` witness
(see the module docstring). -/
noncomputable def TshallowChild : Stage 2 (GaloisField 2 2) :=
  S9run.choose

private lemma childSpec :
    TransitionCoreL TshallowBase TshallowChild PhiHat 1 hP zb ∧
    StageCoreL TshallowChild ∧
    TshallowChild.K = TshallowBase.nextField zb ∧ TshallowChild.e = 1 ∧
    TshallowChild.h = hP :=
  S9run.choose_spec

/-! ### F₂(z̄) = F₄: the adjoined primitive cube root generates (a 4-element ambient
forces it — {0, 1, z̄, z̄+1} are four distinct elements of any subfield containing z̄). -/

private lemma two_eq_zero : (1 : GaloisField 2 2) + 1 = 0 := by
  have h : ((2 : ℕ) : GaloisField 2 2) = 0 := CharP.cast_eq_zero _ 2
  rw [Nat.cast_ofNat] at h
  linear_combination h

private lemma zb_root :
    (zb : GaloisField 2 2) ^ 2 + (zb : GaloisField 2 2) + 1 = 0 := by
  have h := theHyp.hroot
  have hmap : ((Polynomial.X ^ 2 + Polynomial.X + 1 :
      Polynomial ↥TshallowBase.K).map TshallowBase.K.subtype)
      = Polynomial.X ^ 2 + Polynomial.X + 1 := by
    simp
  rw [hmap] at h
  simpa using h

private lemma zb_ne_one : (zb : GaloisField 2 2) ≠ 1 := by
  intro h
  have h0 := zb_root
  rw [h] at h0
  exact one_ne_zero (by linear_combination h0 - two_eq_zero)

private lemma zbp1_ne_zero : (zb : GaloisField 2 2) + 1 ≠ 0 := by
  intro h
  exact zb_ne_one (by linear_combination h - two_eq_zero)

private lemma card4 : Nat.card (GaloisField 2 2) = 4 := by
  have h := GaloisField.card 2 2 (by norm_num)
  rw [h]; norm_num

private lemma nextField_top : TshallowBase.nextField zb = ⊤ := by
  have hz0 : (zb : GaloisField 2 2) ≠ 0 := Units.ne_zero zb
  have hzmem : (zb : GaloisField 2 2) ∈ TshallowBase.nextField zb :=
    Subfield.subset_closure (Or.inr rfl)
  have hone : (1 : GaloisField 2 2) ∈ TshallowBase.nextField zb :=
    Subfield.one_mem _
  have hz1mem : (zb : GaloisField 2 2) + 1 ∈ TshallowBase.nextField zb :=
    Subfield.add_mem _ hzmem hone
  -- {0, 1, z̄, z̄+1} has four distinct elements, so it exhausts the 4-element ambient
  have hcardA :
      ({0, 1, (zb : GaloisField 2 2), (zb : GaloisField 2 2) + 1} :
        Set (GaloisField 2 2)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem ?h0 (Set.toFinite _),
        Set.ncard_insert_of_notMem ?h1 (Set.toFinite _),
        Set.ncard_insert_of_notMem ?h2 (Set.toFinite _),
        Set.ncard_singleton]
    case h0 =>
      rintro (h | h | h)
      · exact zero_ne_one h
      · exact hz0 h.symm
      · exact zbp1_ne_zero h.symm
    case h1 =>
      rintro (h | h)
      · exact zb_ne_one h.symm
      · have h' : (1 : GaloisField 2 2) = (zb : GaloisField 2 2) + 1 := h
        exact hz0 (by linear_combination -h')
    case h2 =>
      intro h
      rw [Set.mem_singleton_iff] at h
      exact one_ne_zero (by linear_combination - h)
  have hAuniv :
      ({0, 1, (zb : GaloisField 2 2), (zb : GaloisField 2 2) + 1} :
        Set (GaloisField 2 2)) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
    rw [Set.ncard_univ, card4, hcardA]
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ ({0, 1, (zb : GaloisField 2 2), (zb : GaloisField 2 2) + 1} :
      Set (GaloisField 2 2)) := hAuniv ▸ Set.mem_univ x
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subfield.zero_mem _
  · exact hone
  · exact hzmem
  · exact hz1mem

/-- CL-01b certificate 1: the child pins CL-01c's card computation reads — full residue
field F₄ (card 4), unramified read e = 1, key degree 2 (so `slotBound 0 = 2/1 = 2`). -/
theorem TshallowChild_pins :
    TshallowChild.K = ⊤ ∧ TshallowChild.e = 1 ∧ TshallowChild.Φ.natDegree = 2 := by
  refine ⟨?_, childSpec.2.2.2.1, ?_⟩
  · rw [childSpec.2.2.1, nextField_top]
  · rw [childSpec.1.base.child_key]
    have hdeg := (L3_liftMonic TshallowBase _ 2 (by norm_num) PhiHat theHyp.hlift).2
    rw [hdeg, spec2.2.2.2.1, spec2.2.2.1, Polynomial.natDegree_X]

/-- **Tshallow's move witness** (CL-01b construction slot): the fully certified
increment `TshallowBase → TshallowChild` — the term `Tower.move` consumes at CL-01c. -/
noncomputable def TshallowMove : MoveWitness TshallowBase TshallowChild :=
  MoveWitness.inc (Polynomial.X ^ 2 + Polynomial.X + 1) 2 PhiHat 1 hP zb
    theHyp childSpec.1 childSpec.2.1

/-- CL-01b certificate 2: `TshallowMove` IS the shallow increment — an `inc` at
ψ = z² + z + 1, g = 2, e′ = 1 (h′, Φ̂, z̄ existential), carrying the full TransHyp,
the transition core, and the child stage core. -/
theorem TshallowMove_spec :
    ∃ (Φhat : Polynomial ℤ_[2]) (h' : ℕ) (zbar : (GaloisField 2 2)ˣ)
      (hyp : TransHyp TshallowBase (Polynomial.X ^ 2 + Polynomial.X + 1) 2 Φhat 1 h' zbar)
      (core : TransitionCoreL TshallowBase TshallowChild Φhat 1 h' zbar)
      (core' : StageCoreL TshallowChild),
      TshallowMove = MoveWitness.inc (Polynomial.X ^ 2 + Polynomial.X + 1) 2 Φhat 1 h'
        zbar hyp core core' :=
  ⟨PhiHat, hP, zb, theHyp, childSpec.1, childSpec.2.1, rfl⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.TshallowChild_pins
#print axioms LeanUrat.HC1.TshallowMove_spec
