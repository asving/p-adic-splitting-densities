/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.C3_TYPb
import LeanUrat.MovesC.C1_TYP_toClause

/-!
# HC1.C5_typToClause — the bridge to MovesC's counting

moves_ref: MOVES 3813–3815 (USE 1: "C.1.5's counting consumes exactly this
object"). deps: C3, T12; MovesC `LevelClause` (fence: consumed, not restated),
`C1_TYP_toClause` (proved). The base-coordinate chart `enc` (the block-convention
digit chart of the level set) is §C-side data, riding as an additive hypothesis.
difficulty: medium. hyp: none.

Proof route (escalation, 2026-07-28): direct `LevelClause` construction. The count
law is the kernel-coset arithmetic of `enc` restricted to the `S`-supported subgroup
`W` (mirroring MovesC's `TYP_fiberCount`, but for `enc` — only `enc`'s OWN additivity
is used), composed with C3's exact-cut clause `N_V · #𝔸 = #V`. The codim match
`#𝔸 = p^aDim` is NOT imported from C6: the count equation `N_base · #𝔸 = p^{|S|}`
itself forces `#𝔸 ∣ p^{|S|}`, so `#𝔸` is an exact p-power and `aDim = log_p #𝔸`
recovers it (`Nat.dvd_prime_pow` + `Nat.log_pow`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit C5: a TYP(b) fresh value clause yields a `MovesC.LevelClause` with support
the level set's chart, codim = aDim, and the count law from C3's equal-fiber
theorem. -/
theorem C5_typToClause {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) (m : ℕ) (S : Finset (Fin m))
    (enc : (Fin m → ZMod p) →+ (↥(T.levelSet b γ') → ↥(T.stg 0).FQ))
    (hdep : ∀ x y : Fin m → ZMod p, (∀ c ∈ S, x c = y c) → enc x = enc y)
    (hsurj : Function.Surjective enc)
    (X : T.grQ γ') (hX : X ∈ T.alphabet b γ') :
    ∃ cl : MovesC.LevelClause p m,
      cl.support = S ∧ cl.codim = T.aDim b γ' ∧
      ∀ x : Fin m → ZMod p, cl.sat x ↔ T.typComposite b γ' (enc x) = X := by
  classical
  -- (0) The digit codomain `V` is finite: it is the surjective image of the finite base box.
  haveI hVfin : Finite (↥(T.levelSet b γ') → ↥(T.stg 0).FQ) :=
    Finite.of_surjective (⇑enc) hsurj
  haveI : Fintype {v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' v = X} :=
    Fintype.ofFinite _
  -- (1) The subgroup of base digit tuples supported on `S`.
  set W : AddSubgroup (Fin m → ZMod p) :=
    { carrier := {y | ∀ c ∉ S, y c = 0}
      zero_mem' := fun c _ => rfl
      add_mem' := fun {x y} hx hy c hc => by simp [hx c hc, hy c hc]
      neg_mem' := fun {x} hx c hc => by simp [hx c hc] } with hWdef
  have memW : ∀ y : Fin m → ZMod p, y ∈ W ↔ ∀ c ∉ S, y c = 0 := fun y => Iff.rfl
  -- (2) The restriction of `enc` to `W`, and its surjectivity (extend a preimage by 0 off `S`).
  set ψ : W →+ (↥(T.levelSet b γ') → ↥(T.stg 0).FQ) := enc.comp W.subtype with hψdef
  have hψapp : ∀ w : ↥W, ψ w = enc ↑w := fun w => by
    rw [hψdef, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply]
  have hψsurj : Function.Surjective ψ := by
    intro v
    obtain ⟨x, hx⟩ := hsurj v
    refine ⟨⟨fun i => if i ∈ S then x i else 0, (memW _).mpr fun c hc => by simp [hc]⟩, ?_⟩
    rw [hψapp, ← hx]
    exact hdep _ _ fun c hc => by simp [hc]
  -- (3) `#W = p^{|S|}` via the restrict/extend bijection `W ≃ (↥S → ZMod p)`.
  have hWcard : Nat.card W = p ^ S.card := by
    have e : W ≃ (↥S → ZMod p) :=
      { toFun := fun w c => (w : Fin m → ZMod p) c.1
        invFun := fun g => ⟨fun i => if h : i ∈ S then g ⟨i, h⟩ else 0,
          (memW _).mpr fun c hc => dif_neg hc⟩
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
  -- (4) Lagrange + first isomorphism: `#W = #V · #ker ψ`.
  have hLag : Nat.card W
      = Nat.card (↥(T.levelSet b γ') → ↥(T.stg 0).FQ) * Nat.card ψ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv
  -- (5) Every ψ-fiber is a kernel coset.
  have hfib : ∀ v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ,
      Nat.card ↥(ψ ⁻¹' {v}) = Nat.card ψ.ker := fun v =>
    Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hψsurj v)
  -- (6) Partition the supported sat-set along ψ: `N_base = N_V · #ker ψ`.
  have e1 : {y : Fin m → ZMod p // T.typComposite b γ' (enc y) = X ∧ ∀ c ∉ S, y c = 0}
      ≃ {w : ↥W // T.typComposite b γ' (ψ w) = X} :=
    { toFun := fun y => ⟨⟨y.1, (memW _).mpr y.2.2⟩, by rw [hψapp]; exact y.2.1⟩
      invFun := fun w => ⟨(w.1 : Fin m → ZMod p),
        ⟨by rw [← hψapp]; exact w.2, (memW _).mp w.1.2⟩⟩
      left_inv := fun y => rfl
      right_inv := fun w => rfl }
  have e2 : {w : ↥W // T.typComposite b γ' (ψ w) = X}
      ≃ Σ v : {v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' v = X},
          ↥(ψ ⁻¹' {v.1}) :=
    { toFun := fun w => ⟨⟨ψ w.1, w.2⟩, ⟨w.1, rfl⟩⟩
      invFun := fun z => ⟨z.2.1, by
        have hz : ψ z.2.1 = z.1.1 := z.2.2
        rw [hz]; exact z.1.2⟩
      left_inv := fun w => rfl
      right_inv := by
        rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
        have hw' : ψ w = v := hw
        subst hw'
        rfl }
  have hpart : Nat.card {y : Fin m → ZMod p // T.typComposite b γ' (enc y) = X ∧ ∀ c ∉ S, y c = 0}
      = Nat.card {v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' v = X}
          * Nat.card ψ.ker := by
    calc Nat.card {y : Fin m → ZMod p // T.typComposite b γ' (enc y) = X ∧ ∀ c ∉ S, y c = 0}
        = Nat.card (Σ v : {v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' v = X},
            ↥(ψ ⁻¹' {v.1})) := Nat.card_congr (e1.trans e2)
      _ = ∑ v : {v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' v = X},
            Nat.card ↥(ψ ⁻¹' {v.1}) := Nat.card_sigma
      _ = ∑ _v : {v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' v = X},
            Nat.card ψ.ker := Finset.sum_congr rfl fun v _ => hfib v.1
      _ = Nat.card {v : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' v = X}
            * Nat.card ψ.ker := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  -- (7) C3's exact-cut clause at `X`, then THE COUNT LAW: `N_base · #𝔸 = p^{|S|}`.
  have hcut := (C3_TYPb T b γ').2.2 X hX
  have hcount : Nat.card {y : Fin m → ZMod p // T.typComposite b γ' (enc y) = X ∧ ∀ c ∉ S, y c = 0}
      * Nat.card ↥(T.alphabet b γ') = p ^ S.card := by
    rw [hpart, mul_right_comm, hcut, ← hLag, hWcard]
  -- (8) `#𝔸` divides `p^{|S|}`, so it is an EXACT p-power, and `p^aDim` recovers it.
  obtain ⟨k, -, halph⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    (Dvd.intro_left _ hcount)
  have haDim : p ^ T.aDim b γ' = Nat.card ↥(T.alphabet b γ') := by
    have h1 : T.aDim b γ' = k := by
      show Nat.log p (Nat.card ↥(T.alphabet b γ')) = k
      rw [halph, Nat.log_pow (Fact.out : p.Prime).one_lt]
    rw [h1, halph]
  have hfinal : Nat.card {y : Fin m → ZMod p // T.typComposite b γ' (enc y) = X ∧ ∀ c ∉ S, y c = 0}
      * p ^ T.aDim b γ' = p ^ S.card := by
    rw [haDim]; exact hcount
  -- (9) Package the clause.
  refine ⟨{ support := S, codim := T.aDim b γ',
            sat := fun x => T.typComposite b γ' (enc x) = X,
            dep := ?_, count := ?_ }, rfl, rfl, fun x => Iff.rfl⟩
  · intro x y h
    simp only [hdep x y h]
  · exact hfinal

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C5_typToClause
