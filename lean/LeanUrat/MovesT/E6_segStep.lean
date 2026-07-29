/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesC.C4_conditionalMass

/-! # T-E6 `fiber_seg_step` — UNBRANCHED SEGMENT (MOVES 7496–7499): the state↔cell tie
CONSUMED AS THE LEDGER FIELD `state_cell` (REV 3, Fable-2 CRIT-3; §0 refutation record
#6); the entrance is the CARRIER value.

PROVED (2026-07-30, the assembly-spine escalation): `L.state_cell` rewrites the state
event into the presented cell event, `L.presents` rewrites both sides into the stratum
form, and the C4 count law (`C4_conditionalMass`'s own coordinate-splitting kernel)
RELATIVIZES to the spectator event `E` — the relativization needs BOTH spectator laws:
`hspec` (E is a spectator of the fresh roster, the standing rev-2 hypothesis) and the
ADJUDICATED ledger law `L.spectator_sol` (the presented Σ's solution set is a spectator
of the fresh roster — the E6 countermodel solved a pinned coordinate value-dependently
off a fresh coordinate, which made the state locus leak into the fresh block and broke
the count). With the box split fresh/non-fresh: `fd.sat` reads only the fresh block
(`L.free`+`L.hfresh` via `LevelClause.dep`), `Σsol ∧ E` reads only the non-fresh block
(the two spectator laws), and the product structure gives the exact `p^{m*}` price. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

section SpectatorKernel

open Classical

/-- the SPECTATOR-RELATIVIZED C4 count law: cutting a locus stratum by a fresh system
prices `p^{m*}` INSIDE any event `E` that is a spectator of the fresh coordinates,
provided the locus' solution set is one too (the adjudicated `spectator_sol` law). -/
theorem spectator_conditional_mass {m : ℕ} (Sigma : Locus p m) (fd : FreshData p m)
    (fresh : Finset (Fin m)) (E : Set (Box p m))
    (hsup : ∀ cl ∈ fd.clauses, ∀ c ∈ cl.support, c ∈ fresh)
    (hsol : SpectatorFor fresh {x : Box p m | Sigma.IsSolution x})
    (hE : SpectatorFor fresh E) :
    Nat.card ↥({x : Box p m | Sigma.IsSolution x ∧ fd.sat x} ∩ E) * p ^ fd.mstar
      = Nat.card ↥({x : Box p m | Sigma.IsSolution x} ∩ E) := by
  classical
  set pred : Fin m → Prop := fun c => c ∈ fresh with hpred
  -- the fresh-block predicate (fd.sat reads only this block)
  set P : ({c // pred c} → ZMod p) → Prop :=
    fun a => fd.sat (putOn pred a (fun _ => 0)) with hP
  -- the non-fresh-block predicate (Σsol ∧ E reads only this block)
  set Q : ({c // ¬ pred c} → ZMod p) → Prop :=
    fun b => Sigma.IsSolution (putOn pred (fun _ => 0) b)
      ∧ (putOn pred (fun _ => 0) b) ∈ E with hQ
  -- `fd.sat` depends only on the fresh block (clause supports ⊆ fresh + `dep`)
  have hsat_dep : ∀ x : Box p m, fd.sat x ↔ P (fun c => x c.1) := by
    intro x
    unfold FreshData.sat
    apply forall_congr'; intro cl
    apply imp_congr_right; intro hcl
    refine cl.dep x _ (fun c hc => ?_)
    rw [putOn_apply, dif_pos (hsup cl hcl c hc)]
  -- `Σsol ∧ E` depends only on the non-fresh block (the two spectator laws)
  have hQ_dep : ∀ x : Box p m, (Sigma.IsSolution x ∧ x ∈ E) ↔ Q (fun c => x c.1) := by
    intro x
    have hagree : ∀ i : Fin m, i ∉ fresh →
        x i = putOn pred (fun _ => 0) (fun c : {c // ¬ pred c} => x c.1) i := by
      intro i hi
      rw [putOn_apply, dif_neg (show ¬ pred i from hi)]
    have h1 := hsol x _ hagree
    have h2 := hE x _ hagree
    simp only [Set.mem_setOf_eq] at h1
    exact and_congr h1 h2
  -- LHS count = |P-block| · |Q-block|
  have c1 : Nat.card ↥({x : Box p m | Sigma.IsSolution x ∧ fd.sat x} ∩ E)
      = Nat.card {a // P a} * Nat.card {b // Q b} := by
    rw [← card_joint pred P Q]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    constructor
    · rintro ⟨⟨hsl, hst⟩, hEx⟩
      exact ⟨(hsat_dep x).mp hst, (hQ_dep x).mp ⟨hsl, hEx⟩⟩
    · rintro ⟨hPa, hQb⟩
      obtain ⟨hsl, hEx⟩ := (hQ_dep x).mpr hQb
      exact ⟨⟨hsl, (hsat_dep x).mpr hPa⟩, hEx⟩
  -- RHS count = p^{|fresh|} · |Q-block|
  have hfreshcard : Nat.card {c // pred c} = fresh.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe fresh
  have c2 : Nat.card ↥({x : Box p m | Sigma.IsSolution x} ∩ E)
      = p ^ fresh.card * Nat.card {b // Q b} := by
    have hjoint := card_joint pred (fun _ : {c // pred c} → ZMod p => True) Q
    have hAtriv : Nat.card {_a : {c // pred c} → ZMod p // True} = p ^ fresh.card := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_fun,
        card_zmod, hfreshcard]
    rw [hAtriv] at hjoint
    rw [← hjoint]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    constructor
    · rintro ⟨hsl, hEx⟩
      exact ⟨trivial, (hQ_dep x).mp ⟨hsl, hEx⟩⟩
    · rintro ⟨-, hQb⟩
      obtain ⟨hsl, hEx⟩ := (hQ_dep x).mpr hQb
      exact ⟨hsl, hEx⟩
  -- the fresh-block price: |P-block| · p^{m*} = p^{|fresh|} (C4's whole-box law,
  -- factored through the block split)
  have c3 : Nat.card {a // P a} * p ^ fd.mstar = p ^ fresh.card := by
    have hfull := clausesCountFull (p := p) fd
    have hbridge : Nat.card {x : Fin m → ZMod p // fd.sat x}
        = Nat.card {a // P a} * p ^ Nat.card {c // ¬ pred c} := by
      have hjoint := card_joint pred P (fun _ : {c // ¬ pred c} → ZMod p => True)
      have hBtriv : Nat.card {_b : {c // ¬ pred c} → ZMod p // True}
          = p ^ Nat.card {c // ¬ pred c} := by
        rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_fun,
          card_zmod]
      rw [hBtriv] at hjoint
      rw [← hjoint]
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
      rw [and_true]
      exact hsat_dep x
    have hpart : Nat.card {c // pred c} + Nat.card {c // ¬ pred c} = m := by
      have h := Nat.card_congr (Equiv.sumCompl pred)
      rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at h
      exact h
    have hpos : 0 < p ^ Nat.card {c // ¬ pred c} :=
      pow_pos (Fact.out (p := Nat.Prime p)).pos _
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    have hm : p ^ fresh.card * p ^ Nat.card {c // ¬ pred c} = p ^ m := by
      rw [← pow_add, ← hfreshcard, hpart]
    calc Nat.card {a // P a} * p ^ fd.mstar * p ^ Nat.card {c // ¬ pred c}
        = Nat.card {a // P a} * p ^ Nat.card {c // ¬ pred c} * p ^ fd.mstar := by ring
      _ = Nat.card {x : Fin m → ZMod p // fd.sat x} * p ^ fd.mstar := by rw [← hbridge]
      _ = p ^ m := hfull
      _ = p ^ fresh.card * p ^ Nat.card {c // ¬ pred c} := hm.symm
  -- assemble
  rw [c1, c2, mul_right_comm, c3]

end SpectatorKernel

/-- RE-KEYED at the T RATIFICATION (2026-07-31; verdict §1): `state_cell` is now the
EXACT Σ_c tie (`stateEvent T (some H) = siteCellEvent (parentSt H) (cellAt H)`), so
the same rewrite chain lands in the spectator kernel; the per-site charge holds at
EVERY site (the former `sides H = 1` guard remains dropped). -/
theorem fiber_seg_step (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (Tr : VTree p F) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (E : Set (Box p m)) (hspec : SpectatorFor (L.freshCoords H) E) :
    Nat.card ↥(stateEvent T (some H) ∩ E) * p ^ L.siteExp H
      = Nat.card ↥(entEvent T χ (L.parentSt H) ∩ E) := by
  classical
  obtain ⟨hcell_eq, hent_eq⟩ := L.presents H hH
  rw [L.state_cell H hH, hcell_eq, hent_eq]
  exact spectator_conditional_mass (L.sys H).1 (L.sys H).2 (L.freshCoords H) E
    (L.hfresh H hH) (L.spectator_sol H hH) hspec

/-- **THE PRESENTED FACES IMPLY (JC-multi)** — the T RATIFICATION's honesty
disclosure (2026-07-31; verdict §4: "Multi-side pricing is effectively obtained
through the stronger `SitePresents`/`FreshData` setup rather than through the
declared open `(JC-multi)` law"). PROVED: a ledger whose `presents`/`spectator_sol`/
`free`/`hfresh`/`state_cell`/`hsplit_exp` rows are discharged at a multi-side site
has ALREADY assumed (JC-multi)-strength content — its per-site `JCmultiAt` instance
follows from T-E6's spectator kernel plus the exact Σ_c tie and the side-union
exponent tie. CONSEQUENCE, disclosed: TREE-EXP's `hjcm` premise (consumed at
multi-side sites in T-E8's `cone_charge`, the note's declared conditionality — the
note keeps (JC-multi) OPEN, 7476–7483) is derivable from the ledger's presented
faces via this lemma; the OPEN (JC-multi) obligation therefore sits INSIDE the
owner's discharge of the presented faces at multi-side sites, not beside it. -/
theorem presents_imply_jcMultiAt (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (Tr : VTree p F) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (h2 : 2 ≤ L.sides H) :
    JCmultiAt T CA χ (L.parentSt H) (L.splitAt H hH h2) := by
  show Nat.card ↥(siteCellEvent T CA χ (L.parentSt H) (L.cellAt H))
      * p ^ (∑ j : Fin (L.splitAt H hH h2).k, (L.splitAt H hH h2).sideExp j)
    = Nat.card ↥(entEvent T χ (L.parentSt H))
  rw [L.hsplit_exp H hH h2, ← L.state_cell H hH]
  have hspec : SpectatorFor (L.freshCoords H) (Set.univ : Set (Box p m)) := by
    intro x x' _; simp
  have h := fiber_seg_step T CA Tr χ L H hH Set.univ hspec
  rw [Set.inter_univ, Set.inter_univ] at h
  exact h

end LeanUrat.MovesT
