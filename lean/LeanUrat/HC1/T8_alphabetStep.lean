/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.C2_TYPa
import LeanUrat.HC1.T7_alphabetSpan
import LeanUrat.Moves.L2_slotDecomp_R4
import LeanUrat.Moves.L2_strideRule

/-!
# HC1.T8_alphabetStep — the (ii.2) step bijection onto the alphabet

moves_ref: MOVES 2139–2160 ((ii.2), 𝔸(γ) = u(γ)·{Σ c_i z̄^i}, "an F_p-SUBSPACE … of
size Π |𝔸_k(γ_i)|; distinct attainable tuples give distinct values"). deps: T4, T5,
T7; Moves `L2_slotDecomp_R4`, `L2_strideRule` (clean). difficulty: HARD (pre-split:
T8a fixed-level bijection; T8b the tower induction on block size). hyp: none.

Proof architecture (E-phase): the (ii.2) content — the composite is an additive
BIJECTION from an attainable-tuple subgroup onto the alphabet with `p ^ aDim` many
tuples — is assembled from two cited facts about the concrete carrier:
* the composite is ADDITIVE on level-set digit tuples (unit C2, TYP(a));
* the alphabet is the finite additive span of the single-coordinate slot images, of
  cardinality exactly `p ^ aDim` (unit T7).
Given these, the attainable-tuple subgroup is a complement of the composite's kernel
inside the digit-span, obtained by the vector-space splitting of the source over
`ZMod (ringChar F)` (the digit field's prime field): every additive endomorphism is
`ZMod q`-linear there (`ZMod q`-scaling is `ℕ`-scaling), so the kernel is a subspace
and splits (`Submodule.exists_isCompl`). The splitting lemma `splitBijOn` below is
tower-free and Lean-core only; C2 and T7 are the only tower inputs.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- **Abstract splitting lemma** (tower-free, Lean-core). Let `D` be a `ZMod q`-vector
space (`q` prime), `E` an abelian group, `φ : D →+ E` an additive map, and `gens ⊆ D`
a set whose image under `φ` generates the subgroup `G = (closure gens).map φ` of `E`.
Then there is a subgroup `A ≤ D` on which `φ` is an additive bijection onto `G`, with
`Nat.card G = Nat.card A`. (`A` is a complement of `ker φ ⊓ span gens` inside
`span gens`, cut out by modularity from a complement in all of `D`.) -/
private theorem splitBijOn {D E : Type*} [AddCommGroup D] [AddCommGroup E]
    (q : ℕ) [Fact q.Prime] [Module (ZMod q) D]
    (φ : D →+ E) (gens : Set D)
    (G : AddSubgroup E) (hG : (AddSubgroup.closure gens).map φ = G) :
    ∃ A : AddSubgroup D,
      Set.BijOn φ ↑A ↑G ∧
      (∀ x ∈ A, ∀ y ∈ A, φ (x + y) = φ x + φ y) ∧
      Nat.card G = Nat.card A := by
  set Vs : Submodule (ZMod q) D := AddSubgroup.toZModSubmodule q (AddSubgroup.closure gens) with hVs
  set kerS : Submodule (ZMod q) D := AddSubgroup.toZModSubmodule q φ.ker with hkerS
  set KV : Submodule (ZMod q) D := Vs ⊓ kerS with hKV
  have hKVle : KV ≤ Vs := inf_le_left
  have hKVker : KV ≤ kerS := inf_le_right
  obtain ⟨B, hB⟩ := Submodule.exists_isCompl KV
  set A_sub : Submodule (ZMod q) D := B ⊓ Vs with hAsub
  have hAle : A_sub ≤ Vs := inf_le_right
  have hsup : KV ⊔ A_sub = Vs := by
    have h := sup_inf_assoc_of_le (α := Submodule (ZMod q) D) (x := KV) B (z := Vs) hKVle
    rw [hB.sup_eq_top, top_inf_eq] at h
    exact h.symm
  have hinf : KV ⊓ A_sub = ⊥ := by
    rw [hAsub, ← inf_assoc, hB.inf_eq_bot, bot_inf_eq]
  -- membership bridges (all definitional)
  have memVs : ∀ {x : D}, x ∈ Vs ↔ x ∈ AddSubgroup.closure gens := fun {x} => Iff.rfl
  have memker : ∀ {x : D}, x ∈ kerS ↔ φ x = 0 := fun {x} => AddMonoidHom.mem_ker
  have memA : ∀ {x : D}, x ∈ A_sub.toAddSubgroup ↔ x ∈ A_sub :=
    fun {x} => Submodule.mem_toAddSubgroup A_sub
  -- InjOn (reused by both the BijOn and the card leg)
  have hInj : Set.InjOn φ ↑(A_sub.toAddSubgroup) := by
    intro x hx y hy hxy
    have hxA : x ∈ A_sub := memA.mp hx
    have hyA : y ∈ A_sub := memA.mp hy
    have hsubA : x - y ∈ A_sub := A_sub.sub_mem hxA hyA
    have hxVs : x - y ∈ Vs := hAle hsubA
    have hkerm : x - y ∈ kerS := memker.mpr (by rw [map_sub, hxy, sub_self])
    have hInKV : x - y ∈ KV := Submodule.mem_inf.mpr ⟨hxVs, hkerm⟩
    have hbot : x - y ∈ (⊥ : Submodule (ZMod q) D) := hinf ▸ Submodule.mem_inf.mpr ⟨hInKV, hsubA⟩
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hbot)
  -- image = G (reused)
  have hImg : φ '' ↑(A_sub.toAddSubgroup) = (↑G : Set E) := by
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨x, hx, rfl⟩
      have hxA : x ∈ A_sub := memA.mp hx
      have hxcl : x ∈ AddSubgroup.closure gens := memVs.mp (hAle hxA)
      have : φ x ∈ (AddSubgroup.closure gens).map φ := AddSubgroup.mem_map.mpr ⟨x, hxcl, rfl⟩
      rw [hG] at this; exact this
    · intro y hy
      have hyG : y ∈ (AddSubgroup.closure gens).map φ := by rw [hG]; exact hy
      obtain ⟨x, hxcl, hxy⟩ := AddSubgroup.mem_map.mp hyG
      have hxVs : x ∈ Vs := memVs.mpr hxcl
      have hxsup : x ∈ KV ⊔ A_sub := hsup ▸ hxVs
      rw [Submodule.mem_sup] at hxsup
      obtain ⟨k, hk, a, ha, hka⟩ := hxsup
      have hphik : φ k = 0 := memker.mp (hKVker hk)
      refine ⟨a, memA.mpr ha, ?_⟩
      rw [← hxy, ← hka, map_add, hphik, zero_add]
  refine ⟨A_sub.toAddSubgroup, ⟨?_, hInj, ?_⟩, ?_, ?_⟩
  · -- MapsTo
    intro x hx
    rw [← hImg]
    exact ⟨x, hx, rfl⟩
  · -- SurjOn
    intro y hy
    rw [← hImg] at hy
    exact hy
  · -- additivity
    intro x _ y _; exact φ.map_add x y
  · -- cardinality
    have hcard := Nat.card_image_of_injOn hInj
    rw [hImg] at hcard
    simpa only [SetLike.coe_sort_coe] using hcard

/-- Unit T8: an attainable-tuple subgroup on which the typComposite is an additive
BIJECTION onto the alphabet, with the per-height block-size law
`p ^ aDim = #(attainable tuples)`. -/
theorem T8_alphabetStep {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) :
    ∃ A : AddSubgroup (↥(T.levelSet b γ) → ↥(T.stg 0).FQ),
      Set.BijOn (T.typComposite b γ) ↑A ↑(T.alphabet b γ) ∧
      (∀ x ∈ A, ∀ y ∈ A,
        T.typComposite b γ (x + y) = T.typComposite b γ x + T.typComposite b γ y) ∧
      p ^ T.aDim b γ = Nat.card ↥A := by
  classical
  -- the digit field and its prime characteristic
  haveI hFinFQ : Finite ↥(T.stg 0).FQ := inferInstance
  set q : ℕ := ringChar ↥(T.stg 0).FQ with hq
  haveI hCharFQ : CharP ↥(T.stg 0).FQ q := ringChar.charP _
  haveI hPrime : Fact q.Prime := ⟨CharP.char_is_prime ↥(T.stg 0).FQ q⟩
  -- the digit field is `q`-torsion, hence a `ZMod q`-vector space (Pi.module lifts it)
  have htorsFQ : ∀ y : ↥(T.stg 0).FQ, q • y = 0 := by
    intro y; simp only [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  letI instFQ : Module (ZMod q) ↥(T.stg 0).FQ := AddCommGroup.zmodModule htorsFQ
  -- the composite as an additive homomorphism (additivity is unit C2)
  set φ : (↥(T.levelSet b γ) → ↥(T.stg 0).FQ) →+ T.grQ γ :=
    AddMonoidHom.mk' (T.typComposite b γ) (C2_TYPa T b γ).2 with hφ
  -- the single-coordinate digit generators
  set gens : Set (↥(T.levelSet b γ) → ↥(T.stg 0).FQ) :=
    ⋃ c : ↥(T.levelSet b γ),
      Set.range (fun y : ↥(T.stg 0).FQ => (Pi.single c y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ)) with hgens
  -- the alphabet is (definitionally) the closure of the single-coordinate images
  have halpha : T.alphabet b γ
      = AddSubgroup.closure (⋃ c : ↥(T.levelSet b γ),
          Set.range (fun y : ↥(T.stg 0).FQ => T.typComposite b γ (Pi.single c y))) := rfl
  -- the image of the generated subgroup is exactly the alphabet
  have hG : (AddSubgroup.closure gens).map φ = T.alphabet b γ := by
    rw [halpha, AddMonoidHom.map_closure]
    congr 1
    rw [hgens, Set.image_iUnion]
    refine Set.iUnion_congr (fun c => ?_)
    rw [hφ, ← Set.range_comp]
    rfl
  -- assemble via the abstract splitting lemma
  obtain ⟨A, hbij, hadd, hcard⟩ := splitBijOn q φ gens (T.alphabet b γ) hG
  refine ⟨A, ?_, ?_, ?_⟩
  · rw [hφ] at hbij; exact hbij
  · intro x hx y hy
    rw [hφ] at hadd; exact hadd x hx y hy
  · rw [(T7_alphabetSpan T b γ).2.2]; exact hcard

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T8_alphabetStep
