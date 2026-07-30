/-
Unit C1.TYP_toClause  (MovesC campaign)
moves_ref: §C.1.5'(1) fresh VALUE clauses are TYP content — the value branch of
           JetSetup.fresh_assembled
deps: C1.TYP_fiberCount  (here proved inline as the private lemma `TYP_fiberCount`,
      making this file self-contained: an additive surjection has equal kernel-coset
      fibers, so the value clause `φ = v` cuts exactly `(alphabet)⁻¹`).
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime]

/-- **TYP(b), the kernel-coset fiber count.** The value map `T.φ` is an additive
surjection onto the alphabet `α` reading only the level set `S`; restricted to the
subgroup of functions supported on `S` it stays surjective, so its fiber over any `v`
is a coset of the kernel. Counting: `#(fiber over v) · #α = #(supported subgroup) = p^{|S|}`. -/
private theorem TYP_fiberCount {m : ℕ} {S : Finset (Fin m)} {α : Type*} [AddCommGroup α]
    [Fintype α] (T : TypObject p m S α) (v : α) :
    Nat.card {y : Fin m → ZMod p // T.φ y = v ∧ ∀ c ∉ S, y c = 0} * Nat.card α = p ^ S.card := by
  -- the subgroup of functions supported on `S`
  set W : AddSubgroup (Fin m → ZMod p) :=
    { carrier := {y | ∀ c ∉ S, y c = 0}
      zero_mem' := fun c _ => rfl
      add_mem' := fun {x y} hx hy c hc => by simp [hx c hc, hy c hc]
      neg_mem' := fun {x} hx c hc => by simp [hx c hc] } with hWdef
  have memW : ∀ y : Fin m → ZMod p, y ∈ W ↔ ∀ c ∉ S, y c = 0 := fun y => Iff.rfl
  -- the restriction of `T.φ` to `W`
  set ψ : W →+ α := T.φ.comp W.subtype with hψdef
  -- `ψ` is surjective (extend a preimage by zero off `S`)
  have hψsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨x, hx⟩ := T.surj a
    refine ⟨⟨fun i => if i ∈ S then x i else 0, (memW _).mpr (fun c hc => by simp [hc])⟩, ?_⟩
    rw [hψdef, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, ← hx]
    exact T.dep _ _ (fun c hc => by simp [hc])
  -- `#W = p^{|S|}` via the restrict/extend bijection `W ≃ (↥S → ZMod p)`
  have hWcard : Nat.card W = p ^ S.card := by
    have e : W ≃ (↥S → ZMod p) :=
      { toFun := fun w c => (w : Fin m → ZMod p) c.1
        invFun := fun g => ⟨fun i => if h : i ∈ S then g ⟨i, h⟩ else 0,
          (memW _).mpr (fun c hc => dif_neg hc)⟩
        left_inv := by
          rintro ⟨y, hy⟩
          apply Subtype.ext
          funext i
          by_cases h : i ∈ S
          · simp [h]
          · simp only [h, dif_neg, not_false_iff]
            exact ((memW y).mp hy i h).symm
        right_inv := by
          intro g
          funext c
          simp [c.2] }
    rw [Nat.card_congr e, Nat.card_fun]
    have hz : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
    have hs : Nat.card (↥S) = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [hz, hs]
  -- Lagrange + first isomorphism theorem: `#W = #α · #(ker ψ)`
  have hLag : Nat.card W = Nat.card α * Nat.card ψ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv]
  -- the fiber over `v` is equinumerous with the kernel
  have hfib : Nat.card {y : Fin m → ZMod p // T.φ y = v ∧ ∀ c ∉ S, y c = 0}
      = Nat.card ψ.ker := by
    have e2 : {y : Fin m → ZMod p // T.φ y = v ∧ ∀ c ∉ S, y c = 0} ≃ ↥(ψ ⁻¹' {v}) :=
      { toFun := fun z => ⟨⟨z.1, (memW _).mpr z.2.2⟩, by
          rw [Set.mem_preimage, Set.mem_singleton_iff, hψdef, AddMonoidHom.comp_apply,
            AddSubgroup.subtype_apply]
          exact z.2.1⟩
        invFun := fun w => ⟨w.1.1, by
          have hw : ψ w.1 = v := w.2
          exact ⟨hw, (memW _).mp w.1.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e2, Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hψsurj v)]
  rw [hfib, ← hWcard, hLag, mul_comm]

theorem C1_TYP_toClause {m : ℕ} {S : Finset (Fin m)} {α : Type*} [AddCommGroup α] [Fintype α] (T : TypObject p m S α) (v : α) (a : ℕ) (hcard : Nat.card α = p ^ a) : ∃ cl : LevelClause p m, cl.support = S ∧ cl.codim = a ∧ ∀ x : Fin m → ZMod p, cl.sat x ↔ T.φ x = v := by
  refine ⟨{ support := S, codim := a, sat := fun x => T.φ x = v, dep := ?_, count := ?_ }, rfl, rfl, fun x => Iff.rfl⟩
  · intro x y h
    rw [T.dep x y h]
  · rw [← hcard]
    exact TYP_fiberCount T v

end LeanUrat.MovesC
