/-
Unit C4.conditionalMass
moves_ref: §C.1.5'(1): mass(Σ ∩ fresh) = mass(Σ)·p^{−m*} — THE per-step conditional exactness, address-free

Intersecting a locus `Σ` with a `FreshData`'s clauses cuts the mass by exactly `p^{−m*}`,
provided every clause support lives on free (unpinned) coordinates of `Σ` (`hfree`).

Proof route (self-contained, deps C0.solvedGraph + C1.clausesCount realized inline):
* `C0.solvedGraph` (imported) gives the restriction bijection `E : {Σ-solutions} ≃ (free → ZMod p)`.
* the clause count on the WHOLE box (`clausesCountList`, the C1.clausesCount content) is proved
  here by induction on the clause list: disjoint supports let each clause be peeled with its
  own `LevelClause.count` law via the coordinate product split `putOn` / `card_joint`.
* the two are stitched by `bridge`: `fd.sat` depends only on the free coordinates (`hfree` +
  `LevelClause.dep`), so the whole-box count factors as (free count)·p^{#pinned}; transporting
  the joint count through `E` identifies the free count with the intersection count.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C0_solvedGraph

open Polynomial LeanUrat.Moves
namespace LeanUrat.MovesC
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

section Helpers
variable {p m : ℕ}

def putOn (pred : Fin m → Prop) [DecidablePred pred]
    (a : {c // pred c} → ZMod p) (b : {c // ¬ pred c} → ZMod p) : Fin m → ZMod p :=
  (Equiv.piEquivPiSubtypeProd pred (fun _ => ZMod p)).symm (a, b)

lemma putOn_apply (pred : Fin m → Prop) [DecidablePred pred]
    (a : {c // pred c} → ZMod p) (b : {c // ¬ pred c} → ZMod p) (c : Fin m) :
    putOn pred a b c = if h : pred c then a ⟨c, h⟩ else b ⟨c, h⟩ := rfl

lemma card_joint (pred : Fin m → Prop) [DecidablePred pred]
    (P : ({c // pred c} → ZMod p) → Prop) (Q : ({c // ¬ pred c} → ZMod p) → Prop) :
    Nat.card {x : Fin m → ZMod p //
        P (fun c : {c // pred c} => x c.1) ∧ Q (fun c : {c // ¬ pred c} => x c.1)}
      = Nat.card {a // P a} * Nat.card {b // Q b} := by
  have step : {x : Fin m → ZMod p //
        P (fun c : {c // pred c} => x c.1) ∧ Q (fun c : {c // ¬ pred c} => x c.1)}
      ≃ {a // P a} × {b // Q b} :=
    (Equiv.subtypeEquiv (Equiv.piEquivPiSubtypeProd pred (fun _ => ZMod p))
      (fun x => Iff.rfl)).trans Equiv.subtypeProdEquivProd
  rw [Nat.card_congr step, Nat.card_prod]

lemma putOn_restrict_zero (S : Finset (Fin m)) (y : Fin m → ZMod p)
    (hz : ∀ c ∉ S, y c = 0) : putOn (· ∈ S) (fun c => y c.1) (fun _ => 0) = y := by
  funext c
  rw [putOn_apply]
  split
  · rfl
  · rename_i h; exact (hz c h).symm

lemma restrict_putOn (S : Finset (Fin m)) (a : {c // c ∈ S} → ZMod p) :
    (fun c : {c // c ∈ S} => putOn (· ∈ S) a (fun _ => 0) c.1) = a := by
  funext c
  rw [putOn_apply, dif_pos c.2]

def clauseCountEquiv (cl : LevelClause p m) :
    {a : {c // c ∈ cl.support} → ZMod p // cl.sat (putOn (· ∈ cl.support) a (fun _ => 0))}
      ≃ {y : Fin m → ZMod p // cl.sat y ∧ ∀ c ∉ cl.support, y c = 0} where
  toFun a := ⟨putOn (· ∈ cl.support) a.1 (fun _ => 0), a.2, by
    intro c hc; rw [putOn_apply, dif_neg hc]⟩
  invFun y := ⟨fun c => y.1 c.1, by
    rw [putOn_restrict_zero cl.support y.1 y.2.2]; exact y.2.1⟩
  left_inv a := by ext1; exact restrict_putOn cl.support a.1
  right_inv y := by ext1; exact putOn_restrict_zero cl.support y.1 y.2.2

lemma clause_count [Fact p.Prime] (cl : LevelClause p m) :
    Nat.card {a : {c // c ∈ cl.support} → ZMod p // cl.sat (putOn (· ∈ cl.support) a (fun _ => 0))}
      * p ^ cl.codim = p ^ cl.support.card := by
  rw [Nat.card_congr (clauseCountEquiv cl)]
  exact cl.count

lemma card_zmod [Fact p.Prime] : Nat.card (ZMod p) = p := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  rw [Nat.card_eq_fintype_card, ZMod.card]

lemma clausesCountList [Fact p.Prime] (L : List (LevelClause p m))
    (hdisj : L.Pairwise (fun c₁ c₂ => Disjoint c₁.support c₂.support)) :
    Nat.card {x : Fin m → ZMod p // ∀ cl ∈ L, cl.sat x} * p ^ (L.map LevelClause.codim).sum
      = p ^ m := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, pow_zero, mul_one]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => by simp)),
      Nat.card_fun, card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  | cons cl rest IH =>
    obtain ⟨hcl_disj, hrest_disj⟩ := List.pairwise_cons.mp hdisj
    have IH' := IH hrest_disj
    set P : ({c // c ∈ cl.support} → ZMod p) → Prop :=
      fun a => cl.sat (putOn (· ∈ cl.support) a (fun _ => 0)) with hP
    set Q : ({c // ¬ c ∈ cl.support} → ZMod p) → Prop :=
      fun b => ∀ c' ∈ rest, c'.sat (putOn (· ∈ cl.support) (fun _ => 0) b) with hQ
    have hclhead : ∀ x : Fin m → ZMod p, cl.sat x ↔ P (fun c => x c.1) := by
      intro x
      refine cl.dep x _ (fun c hc => ?_)
      rw [putOn_apply, dif_pos hc]
    have hQrest : ∀ x : Fin m → ZMod p, (∀ c' ∈ rest, c'.sat x) ↔ Q (fun c => x c.1) := by
      intro x
      apply forall_congr'; intro c'
      apply imp_congr_right; intro hmem
      refine c'.dep x _ (fun c hc => ?_)
      have hcnotin : c ∉ cl.support :=
        Finset.disjoint_right.mp (hcl_disj c' hmem) hc
      rw [putOn_apply, dif_neg hcnotin]
    have claimA : Nat.card {x : Fin m → ZMod p // cl.sat x ∧ ∀ c' ∈ rest, c'.sat x}
        = Nat.card {a // P a} * Nat.card {b // Q b} := by
      rw [← card_joint (· ∈ cl.support) P Q]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [hclhead x, hQrest x]))
    have claimB : Nat.card {x : Fin m → ZMod p // ∀ c' ∈ rest, c'.sat x}
        = p ^ cl.support.card * Nat.card {b // Q b} := by
      have hjoint := card_joint (· ∈ cl.support)
        (fun _ : {c // c ∈ cl.support} → ZMod p => True) Q
      have hAtriv : Nat.card {_a : {c // c ∈ cl.support} → ZMod p // True} = p ^ cl.support.card := by
        rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_fun, card_zmod,
          Nat.card_eq_fintype_card, Fintype.card_coe]
      rw [hAtriv] at hjoint
      rw [← hjoint]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [hQrest x, true_and]))
    have claimC : Nat.card {a // P a} * p ^ cl.codim = p ^ cl.support.card := by
      simp only [hP]; exact clause_count cl
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    rw [claimA, pow_add,
      show Nat.card {a // P a} * Nat.card {b // Q b}
          * (p ^ cl.codim * p ^ (rest.map LevelClause.codim).sum)
        = (Nat.card {a // P a} * p ^ cl.codim)
          * (Nat.card {b // Q b} * p ^ (rest.map LevelClause.codim).sum) by ring,
      claimC,
      show p ^ cl.support.card * (Nat.card {b // Q b} * p ^ (rest.map LevelClause.codim).sum)
        = (p ^ cl.support.card * Nat.card {b // Q b}) * p ^ (rest.map LevelClause.codim).sum by ring,
      ← claimB]
    exact IH'

lemma clausesCountFull [Fact p.Prime] (fd : FreshData p m) :
    Nat.card {x : Fin m → ZMod p // fd.sat x} * p ^ fd.mstar = p ^ m := by
  simpa [FreshData.sat, FreshData.mstar] using clausesCountList fd.clauses fd.disj

end Helpers

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C4_conditionalMass {m : ℕ} (Sigma : Locus p m) (fd : FreshData p m) (hfree : ∀ cl ∈ fd.clauses, ∀ c ∈ cl.support, Sigma.pinned c = false) : Nat.card {x : Fin m → ZMod p // Sigma.IsSolution x ∧ fd.sat x} * p ^ fd.mstar = Sigma.mass := by
  obtain ⟨E, hE⟩ := C0_solvedGraph Sigma
  have hdep : ∀ x y : Fin m → ZMod p,
      (∀ c, Sigma.pinned c = false → x c = y c) → (fd.sat x ↔ fd.sat y) := by
    intro x y hxy
    unfold FreshData.sat
    apply forall_congr'; intro cl
    apply imp_congr_right; intro hcl
    exact cl.dep x y (fun c hc => hxy c (hfree cl hcl c hc))
  set satF : ({c // Sigma.pinned c = false} → ZMod p) → Prop :=
    fun a => fd.sat (putOn (fun c => Sigma.pinned c = false) a (fun _ => 0)) with hsatF
  -- Step 1 : the joint count equals the free-coordinate count of `satF`
  have hagree : ∀ (a : {c // Sigma.pinned c = false} → ZMod p) (c : Fin m),
      Sigma.pinned c = false → (E.symm a).1 c = putOn (fun c => Sigma.pinned c = false) a (fun _ => 0) c := by
    intro a c hc
    rw [putOn_apply, dif_pos hc]
    have h := hE (E.symm a) ⟨c, hc⟩
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have hsatFiff : ∀ a, fd.sat (E.symm a).1 ↔ satF a := by
    intro a
    simp only [hsatF]
    exact hdep _ _ (hagree a)
  have e1 : {x : Fin m → ZMod p // Sigma.IsSolution x ∧ fd.sat x}
      ≃ {x' : {x : Fin m → ZMod p // Sigma.IsSolution x} // fd.sat x'.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter Sigma.IsSolution fd.sat).symm
  have e2 : {x' : {x : Fin m → ZMod p // Sigma.IsSolution x} // fd.sat x'.1}
      ≃ {a : {c // Sigma.pinned c = false} → ZMod p // fd.sat (E.symm a).1} :=
    Equiv.subtypeEquiv E (fun x' => by rw [E.symm_apply_apply])
  have e3 : {a : {c // Sigma.pinned c = false} → ZMod p // fd.sat (E.symm a).1} ≃ {a // satF a} :=
    Equiv.subtypeEquivRight hsatFiff
  have step1 : Nat.card {x : Fin m → ZMod p // Sigma.IsSolution x ∧ fd.sat x}
      = Nat.card {a // satF a} :=
    Nat.card_congr ((e1.trans e2).trans e3)
  -- Step 2 : the bridge — `fd.sat` on the whole box factors as free-count × pinned-box
  have bridge : Nat.card {x : Fin m → ZMod p // fd.sat x}
      = Nat.card {a // satF a} * p ^ Nat.card {c // ¬ (Sigma.pinned c = false)} := by
    have hjoint := card_joint (fun c => Sigma.pinned c = false) satF
      (fun _ : {c // ¬ (Sigma.pinned c = false)} → ZMod p => True)
    have hbtriv : Nat.card {_b : {c // ¬ (Sigma.pinned c = false)} → ZMod p // True}
        = p ^ Nat.card {c // ¬ (Sigma.pinned c = false)} := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_fun, card_zmod]
    rw [hbtriv] at hjoint
    rw [← hjoint]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    rw [and_true]
    simp only [hsatF]
    exact hdep x _ (fun c hc => by rw [putOn_apply, dif_pos hc])
  -- Step 4 : the mass in closed form
  have hmass : Sigma.mass = p ^ Nat.card {c // Sigma.pinned c = false} := by
    unfold Locus.mass
    rw [Nat.card_congr E, Nat.card_fun, card_zmod]
  -- Step 5 : the free/pinned partition of the box
  have hpartition : Nat.card {c // Sigma.pinned c = false}
      + Nat.card {c // ¬ (Sigma.pinned c = false)} = m := by
    have h := Nat.card_congr (Equiv.sumCompl (fun c => Sigma.pinned c = false))
    rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at h
    exact h
  -- Assemble
  rw [step1, hmass]
  have hpos : 0 < p ^ Nat.card {c // ¬ (Sigma.pinned c = false)} :=
    pow_pos (Fact.out (p := Nat.Prime p)).pos _
  have key : Nat.card {a // satF a} * p ^ Nat.card {c // ¬ (Sigma.pinned c = false)}
      * p ^ fd.mstar = p ^ m := by
    rw [← bridge]; exact clausesCountFull fd
  have hm : p ^ m = p ^ Nat.card {c // Sigma.pinned c = false}
      * p ^ Nat.card {c // ¬ (Sigma.pinned c = false)} := by
    rw [← pow_add, hpartition]
  rw [hm] at key
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [mul_right_comm]
  exact key

end
end LeanUrat.MovesC
