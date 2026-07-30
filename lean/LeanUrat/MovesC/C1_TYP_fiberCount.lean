/-
Unit C1.TYP_fiberCount  (moves_ref: §C Lemma TYP(b): additive surjection ⟹ equal
kernel-coset fibers ⟹ the value clause cuts (alphabet)⁻¹)

The supported subgroup `V = {y | ∀ c ∉ S, y c = 0}` has cardinality `p^{|S|}`.
Because `T.φ` reads only the `S`-coordinates (`T.dep`), its restriction `g` to `V` is still
surjective onto `α` (`T.surj`). Hence the fiber of `g` over `v` is a coset of `ker g`, so
`|fiber| · |α| = |V/ker| · |ker| = |V| = p^{|S|}` — the value clause cuts a factor `|α|`.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C1_TYP_fiberCount {m : ℕ} {S : Finset (Fin m)} {α : Type*} [AddCommGroup α] [Fintype α] (T : TypObject p m S α) (v : α) : Nat.card {y : Fin m → ZMod p // T.φ y = v ∧ ∀ c ∉ S, y c = 0} * Nat.card α = p ^ S.card := by
  classical
  -- the subgroup of functions supported on `S`
  let V : AddSubgroup (Fin m → ZMod p) :=
    { carrier := {y | ∀ c ∉ S, y c = 0}
      add_mem' := fun {a b} ha hb c hc => by simp only [Pi.add_apply, ha c hc, hb c hc, add_zero]
      zero_mem' := fun c _ => rfl
      neg_mem' := fun {a} ha c hc => by simp only [Pi.neg_apply, ha c hc, neg_zero] }
  have hVmem : ∀ y : Fin m → ZMod p, y ∈ V ↔ ∀ c ∉ S, y c = 0 := fun _ => Iff.rfl
  -- `φ` restricted to the supported subgroup
  let g : ↥V →+ α := T.φ.comp V.subtype
  have hgapp : ∀ w : ↥V, g w = T.φ w.1 := fun _ => rfl
  -- `g` is surjective: `φ` depends only on the `S`-coordinates, so zeroing outside `S`
  -- does not change the value.
  have hgsurj : Function.Surjective g := by
    intro a
    obtain ⟨x, hx⟩ := T.surj a
    refine ⟨⟨fun c => if c ∈ S then x c else 0, ?_⟩, ?_⟩
    · intro c hc; simp [hc]
    · rw [hgapp]
      refine (T.dep _ x ?_).trans hx
      intro c hc; simp [hc]
  -- `|V| = p^{|S|}` via the restriction-to-`S` bijection.
  have hV : Nat.card ↥V = p ^ S.card := by
    have e : ↥V ≃ (↥S → ZMod p) :=
      { toFun := fun w s => w.1 s.1
        invFun := fun f => ⟨fun c => if h : c ∈ S then f ⟨c, h⟩ else 0,
          (hVmem _).2 (fun c hc => dif_neg hc)⟩
        left_inv := by
          rintro ⟨y, hy⟩
          apply Subtype.ext
          funext c
          show (if h : c ∈ S then y c else 0) = y c
          by_cases h : c ∈ S
          · rw [dif_pos h]
          · rw [dif_neg h]; exact ((hVmem y).1 hy c h).symm
        right_inv := by
          intro f
          funext s
          show (if h : s.1 ∈ S then f ⟨s.1, h⟩ else 0) = f s
          rw [dif_pos s.2] }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe]
  -- our set is exactly the fiber of `g` over `v` (a repackaging of the subtype data).
  have hset : Nat.card {y : Fin m → ZMod p // T.φ y = v ∧ ∀ c ∉ S, y c = 0}
      = Nat.card {w : ↥V // g w = v} := by
    apply Nat.card_congr
    exact
      { toFun := fun y => ⟨⟨y.1, (hVmem y.1).2 y.2.2⟩, by rw [hgapp]; exact y.2.1⟩
        invFun := fun w => ⟨w.1.1,
          ⟨by have h2 := w.2; rw [hgapp] at h2; exact h2, (hVmem w.1.1).1 w.1.2⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  -- translating by a chosen preimage `w0` identifies the fiber with the kernel.
  have hfib : Nat.card {w : ↥V // g w = v} = Nat.card ↥(g.ker) := by
    obtain ⟨w0, hw0⟩ := hgsurj v
    apply Nat.card_congr
    exact
      { toFun := fun w => ⟨w.1 - w0, by
          rw [AddMonoidHom.mem_ker, map_sub, w.2, hw0, sub_self]⟩
        invFun := fun k => ⟨k.1 + w0, by
          rw [map_add, AddMonoidHom.mem_ker.1 k.2, hw0, zero_add]⟩
        left_inv := fun _ => by apply Subtype.ext; simp
        right_inv := fun _ => by apply Subtype.ext; simp }
  -- first isomorphism theorem: `V / ker g ≃ α`.
  have hquot : Nat.card (↥V ⧸ g.ker) = Nat.card α :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hgsurj).toEquiv
  -- assemble via Lagrange.
  calc Nat.card {y : Fin m → ZMod p // T.φ y = v ∧ ∀ c ∉ S, y c = 0} * Nat.card α
      = Nat.card ↥(g.ker) * Nat.card α := by rw [hset, hfib]
    _ = Nat.card (↥V ⧸ g.ker) * Nat.card ↥(g.ker) := by rw [hquot, mul_comm]
    _ = Nat.card ↥V := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker).symm
    _ = p ^ S.card := hV

end LeanUrat.MovesC
