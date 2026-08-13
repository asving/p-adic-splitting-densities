/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity

/-!
# UniformityCheck.DeepSet — counting the DEEPLY TANGENT level-`N` classes at `n = 2`

`Uniformity.Density.Drainage` bounds the *undecided* classes at level `2M` by `q ^ (3M)`
(`undecidedCount_le`), by routing each undecided class through a centre of tangency depth `2M`
(the dichotomy `decidedAt_of_not_tang` supplies the centre) and then pinning the class by the
pair `(γ mod 𝔪^M, a₁ mod 𝔪^{2M})`.

This file extracts the *pinning half* of that argument as a statement about the set of classes
that are deep by definition:

    deepSet π N = { c : Coeff O 2 N | some lift of `c` has a centre of tangency depth `N` }

* `card_deepSet_le` — `#(deepSet π (2M)) ≤ q ^ (3M)`.
* `deep_of_mem_deepSet` — deepness is a property of the CLASS: if one lift has a deep centre,
  every lift of the same class has one (the *same* centre, in fact).

Because the tangent centre is handed to us by the definition rather than manufactured by the
dichotomy, **no completeness hypothesis is needed**: `[IsAdicComplete …]` is absent from every
statement below (`Drainage.undecidedCount_le` needs it only for the Hensel step inside
`decidedAt_of_not_tang`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- A level-`N` class is DEEP when some lift has a centre of tangency depth `N`. -/
def deepSet (π : O) (N : ℕ) : Set (Coeff O 2 N) :=
  {c | ∃ a : Fin 2 → O, proj O 2 N a = c ∧ ∃ γ : O, Tang π a N γ}

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **The class is pinned by `(γ mod π^M, a₁ mod π^{2M})`.**

Verbatim re-proof of `Uniformity.Density.class_pinned`, which is stated inside a section whose
`variable` block carries `[IsAdicComplete (maximalIdeal O) O]`; that instance is auto-included in
its signature although the proof never uses it, and the statements below are deliberately
completeness-free. Nothing but the arithmetic of `qval`/`qder` is involved. -/
theorem class_pinned' {π : O} {M : ℕ} {a a' : Fin 2 → O} {γ γ' : O}
    (hT : Tang π a (2 * M) γ) (hT' : Tang π a' (2 * M) γ')
    (hγ : π ^ M ∣ (γ' - γ)) (h1 : π ^ (2 * M) ∣ (a' 1 - a 1)) :
    π ^ (2 * M) ∣ (a' 0 - a 0) := by
  obtain ⟨s, hs⟩ := hγ
  obtain ⟨d, hd⟩ := h1
  obtain ⟨e, he⟩ := hT.1
  obtain ⟨e', he'⟩ := hT'.1
  obtain ⟨g, hg⟩ := (show π ^ M ∣ qder a γ by
    have := hT.2; rwa [show (2 * M + 1) / 2 = M by omega] at this)
  simp only [qval] at he he'
  simp only [qder] at hg
  have hs' : γ' = γ + π ^ M * s := by linear_combination hs
  have hd' : a' 1 = a 1 + π ^ (2 * M) * d := by linear_combination hd
  rw [hs', hd'] at he'
  exact ⟨e' - e - s * g - s ^ 2 - d * γ - π ^ M * d * s,
    by linear_combination he' - he - (π ^ M * s) * hg⟩

/-- At level `2M` at most `q ^ (3M)` classes are deep. -/
theorem card_deepSet_le {π : O} (hπ : Irreducible π) (M : ℕ) :
    Nat.card (deepSet π (2 * M)) ≤ residueCard O ^ (3 * M) := by
  classical
  have key : ∀ c : deepSet π (2 * M), ∃ p : (Fin 2 → O) × O,
      proj O 2 (2 * M) p.1 = (c : Coeff O 2 (2 * M)) ∧ Tang π p.1 (2 * M) p.2 := by
    rintro ⟨c, a, ha, γ, hγ⟩
    exact ⟨(a, γ), ha, hγ⟩
  choose f hf1 hf2 using key
  have hinj : Function.Injective (fun c : deepSet π (2 * M) =>
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ M) (f c).2,
        (c : Coeff O 2 (2 * M)) 1) : Res O M × Res O (2 * M))) := by
    intro c c' hcc
    have h1 : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ M) (f c).2
        = Ideal.Quotient.mk _ (f c').2 := congrArg Prod.fst hcc
    have h2 : (c : Coeff O 2 (2 * M)) 1 = (c' : Coeff O 2 (2 * M)) 1 := congrArg Prod.snd hcc
    have hγ : π ^ M ∣ ((f c').2 - (f c).2) :=
      (mem_maximalIdeal_pow_iff_dvd hπ M _).1 (Ideal.Quotient.eq.1 h1.symm)
    have e1 : (c : Coeff O 2 (2 * M)) 1 = Ideal.Quotient.mk _ ((f c).1 1) := by rw [← hf1 c]; rfl
    have e2 : (c' : Coeff O 2 (2 * M)) 1 = Ideal.Quotient.mk _ ((f c').1 1) := by rw [← hf1 c']; rfl
    have ha1 : π ^ (2 * M) ∣ ((f c').1 1 - (f c).1 1) :=
      (mem_maximalIdeal_pow_iff_dvd hπ (2 * M) _).1 (Ideal.Quotient.eq.1 (by rw [← e1, ← e2, h2]))
    have ha0 : π ^ (2 * M) ∣ ((f c').1 0 - (f c).1 0) := class_pinned' (hf2 c) (hf2 c') hγ ha1
    refine Subtype.ext (funext fun i => ?_)
    fin_cases i
    · show (c : Coeff O 2 (2 * M)) 0 = (c' : Coeff O 2 (2 * M)) 0
      rw [← hf1 c, ← hf1 c']
      exact Ideal.Quotient.eq.2
        ((mem_maximalIdeal_pow_iff_dvd hπ (2 * M) _).2 (dvd_sub_comm.1 ha0))
    · exact h2
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, card_res, card_res] at hle
  calc Nat.card (deepSet π (2 * M)) ≤ residueCard O ^ M * residueCard O ^ (2 * M) := hle
    _ = residueCard O ^ (3 * M) := by rw [← pow_add]; ring_nf

/-- Deepness is a property of the CLASS: if one lift has a deep centre, every lift does. -/
theorem deep_of_mem_deepSet {π : O} (hπ : Irreducible π) {N : ℕ} {c : Coeff O 2 N}
    (hc : c ∈ deepSet π N) (a : Fin 2 → O) (ha : proj O 2 N a = c) :
    ∃ γ : O, Tang π a N γ := by
  obtain ⟨b, hb, γ, hv, hd⟩ := hc
  have hab : CongAt π N b a := congAt_of_proj_eq hπ (hb.trans ha.symm)
  exact ⟨γ, dvd_transfer (le_refl N) (qval_congr hab γ) hv,
    dvd_transfer (by omega) (qder_congr hab γ) hd⟩

#print axioms UniformityCheck.card_deepSet_le
#print axioms UniformityCheck.deep_of_mem_deepSet

end UniformityCheck
