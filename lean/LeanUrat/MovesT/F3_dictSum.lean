/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.F2_dictPtwise
import LeanUrat.MovesD.D2a_finite

/-! # T-F3 `preHalt_dict_sum` (MOVES 7601–7606): double count {(i, x)} both ways;
per-x the inner count is T-F2 at x's unique tree. `hsep` binds AFTER 𝒯 (REV 4,
Fable-3 GAP-4).

STATEMENT REPAIR (adjudicated round-3 item (3), 2026-07-29): the theorem is restated
**ON THE DECIDED SET** — the LHS class sets gain the conjunct `Decided T χ x`. This is
the note's OWN scoping, MOVES 7597–7603 (quoted): "Call a value-prefix η PRE-HALT if
none of its proper prefixes τ-halts … Then, **on the decided set** (undecided
complement: mass 0 GIVEN X.3 — the CL-4 tag):
  Σ_{η ∈ Pref^τ(P̂)} μ(S(η,⊤)) = Σ_T (# length-ℓ chains of T of shape P̂) ·
                                  μ{f : T_can^τ(f) = T}".
The RHS sums pruned-TREE fibers, so it never sees undecided points; the transcription
dropped the LHS scoping. The undecided-mass-0 statement is X.3-CONDITIONAL (the CL-4
tag) and is NOT this unit. Countermodel to the unscoped form: an undecided x in a
class fiber contributes to the old LHS but to no tree fiber on the RHS. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **the VTree-uniqueness lemma** (the round-3 plan's kernel): two complete finite
trees fibering the SAME box point are EQUAL — not just `VTree.ext`-equivalent.
Clauses 1/3 of `fiberAt` pin `chains`/`henV`; the structure law `hleaf` + clause 2
pin `leafV` (off the maximal chains both are `none`; on them the τ-dichotomy is
decided by the x-shared `IrrHalts`/`NsHalts`); `hns_leaf` + clause 2 pin `nsLeaf`;
`funext` + `propext` assemble, and the six proof fields ride by proof irrelevance. -/
theorem vtree_eq_of_fiberAt {T : TreeModel p F n N m pol} {χ : Fin n → Fin m}
    {Tr Tr' : VTree p F} {x : Box p m}
    (h : Tr.fiberAt T χ x) (h' : Tr'.fiberAt T χ x) : Tr = Tr' := by
  -- clause 1 pins the chain sets
  have hchains : Tr.chains = Tr'.chains := by
    ext H
    rw [h.1 H, h'.1 H]
  -- clause 3 pins the hen payload
  have hhen : Tr.henV = Tr'.henV := by
    rw [h.2.2.1, h'.2.2.1]
  -- clause 2 at a shared maximal chain: the leaf dichotomy is decided by the
  -- x-shared conditions, so the leaf data agree
  have hmax : ∀ H : History p F, H ∈ Tr.chains → IsMaximalIn Tr.chains H →
      Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H) := by
    intro H hHc hHmax
    have hHc' : H ∈ Tr'.chains := hchains ▸ hHc
    have hHmax' : IsMaximalIn Tr'.chains H := hchains ▸ hHmax
    rcases h.2.1 H hHc hHmax with ⟨hirr, hnns, hlv⟩ | ⟨hns, hnirr, hnsl, hlv⟩ <;>
      rcases h'.2.1 H hHc' hHmax' with ⟨hirr', hnns', hlv'⟩ | ⟨hns', hnirr', hnsl', hlv'⟩
    · exact ⟨hlv.trans hlv'.symm, iff_of_false hnns hnns'⟩
    · exact absurd hirr hnirr'
    · exact absurd hirr' hnirr
    · exact ⟨hlv.trans hlv'.symm, iff_of_true hnsl hnsl'⟩
  -- hleaf + clause 2 pin leafV
  have hleafV : Tr.leafV = Tr'.leafV := by
    funext H
    by_cases hHc : H ∈ Tr.chains ∧ IsMaximalIn Tr.chains H
    · exact (hmax H hHc.1 hHc.2).1
    · have h1 : ¬ (Tr.leafV H).isSome = true := fun hs => hHc ((Tr.hleaf H).mp hs)
      have h2 : ¬ (Tr'.leafV H).isSome = true := by
        intro hs
        have hm := (Tr'.hleaf H).mp hs
        rw [← hchains] at hm
        exact hHc hm
      rw [Option.not_isSome_iff_eq_none.mp h1, Option.not_isSome_iff_eq_none.mp h2]
  -- hns_leaf + clause 2 pin nsLeaf
  have hnsLeaf : Tr.nsLeaf = Tr'.nsLeaf := by
    funext H
    apply propext
    by_cases hHc : H ∈ Tr.chains ∧ IsMaximalIn Tr.chains H
    · exact (hmax H hHc.1 hHc.2).2
    · constructor
      · intro hns
        exact absurd (Tr.hns_leaf H hns) hHc
      · intro hns
        have hm := Tr'.hns_leaf H hns
        rw [← hchains] at hm
        exact absurd hm hHc
  -- assemble: the four data fields are pinned; proof fields by proof irrelevance
  clear hmax h h'
  cases Tr; cases Tr'
  simp only at hchains hhen hleafV hnsLeaf
  subst hchains; subst hhen; subst hleafV; subst hnsLeaf
  rfl

open Classical in
/-- THE DICTIONARY SUM, on the decided set (MOVES 7597–7603, quoted in the module
docstring: "Then, on the decided set …: Σ_{η ∈ Pref^τ(P̂)} μ(S(η,⊤)) = Σ_T (# length-ℓ
chains of T of shape P̂) · μ{f : T_can^τ(f) = T}"). Proof per the recorded plan: finsum
to Fintype; double count {(i, x)}; the partition `hpart.2` + the uniqueness lemma split
each class set along 𝒯; per-x the inner count is T-F2. -/
theorem preHalt_dict_sum {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (hph : PreHaltClassData (P := P) pol)
    (𝒯 : Finset (VTree p F))
    (hsep : ∀ Tr ∈ 𝒯, ∀ H H', H ∈ VTree.chains Tr → H' ∈ VTree.chains Tr →
      H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
      (∃ i : PrefIdx n pol P, SameClass i H ∧ SameClass i H') → H = H')
    (hpart : PartitionsDecided 𝒯 T χ) :
    ∑ᶠ i : PrefIdx n pol P,
        Nat.card ↥{x | x ∈ S.fiber i ∧ PreHalt (reprOf i) ∧ Decided T χ x}
      = ∑ Tr ∈ 𝒯, Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x} := by
  classical
  letI : Fintype (PrefIdx n pol P) := Fintype.ofFinite _
  -- T-F2 pointwise, in filter form
  have hF2x : ∀ Tr ∈ 𝒯, ∀ x : Box p m, Tr.fiberAt T χ x →
      (Finset.univ.filter
        (fun i : PrefIdx n pol P => x ∈ S.fiber i ∧ PreHalt (reprOf i))).card
        = Tr.chainCount n P := by
    intro Tr hTr x hfib
    rw [← preHalt_dict_ptwise S T χ hcyl hwd heta hib hph Tr x hfib (hsep Tr hTr),
      Nat.card_eq_fintype_card]
    exact (Fintype.card_of_subtype _ (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq])).symm
  -- STEP 1 (hpart.2 + uniqueness): each class's decided set splits along 𝒯
  have hsplit : ∀ i : PrefIdx n pol P,
      Nat.card ↥{x | x ∈ S.fiber i ∧ PreHalt (reprOf i) ∧ Decided T χ x}
        = ∑ Tr ∈ 𝒯, Nat.card
            ↥{x | (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x} := by
    intro i
    have hset : Finset.univ.filter
        (fun x : Box p m => x ∈ S.fiber i ∧ PreHalt (reprOf i) ∧ Decided T χ x)
        = 𝒯.biUnion (fun Tr => Finset.univ.filter
            (fun x : Box p m => (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hf, hphx, hdec⟩
        obtain ⟨Tr, hTr, hfib⟩ := hpart.2 x hdec
        exact ⟨Tr, hTr, ⟨hf, hphx⟩, hfib⟩
      · rintro ⟨Tr, hTr, ⟨hf, hphx⟩, hfib⟩
        exact ⟨hf, hphx, Tr, hfib⟩
    have hdisj : ∀ Tr ∈ 𝒯, ∀ Tr' ∈ 𝒯, Tr ≠ Tr' →
        Disjoint
          (Finset.univ.filter (fun x : Box p m =>
            (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x))
          (Finset.univ.filter (fun x : Box p m =>
            (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr'.fiberAt T χ x)) := by
      intro Tr _ Tr' _ hne
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_filter] at hx hx'
      exact hne (vtree_eq_of_fiberAt hx.2.2 hx'.2.2)
    calc Nat.card ↥{x | x ∈ S.fiber i ∧ PreHalt (reprOf i) ∧ Decided T χ x}
        = (Finset.univ.filter (fun x : Box p m =>
            x ∈ S.fiber i ∧ PreHalt (reprOf i) ∧ Decided T χ x)).card := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_of_subtype _ (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq])
      _ = ∑ Tr ∈ 𝒯, (Finset.univ.filter (fun x : Box p m =>
            (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x)).card := by
          rw [hset]
          exact Finset.card_biUnion hdisj
      _ = ∑ Tr ∈ 𝒯, Nat.card
            ↥{x | (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x} := by
          refine Finset.sum_congr rfl (fun Tr _ => ?_)
          rw [Nat.card_eq_fintype_card]
          exact (Fintype.card_of_subtype _ (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq])).symm
  -- STEP 2 (per tree): double count {(i, x)}; the inner count is T-F2
  have hper : ∀ Tr ∈ 𝒯,
      (∑ i : PrefIdx n pol P, Nat.card
          ↥{x | (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x})
        = Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x} := by
    intro Tr hTr
    have hpt : ∀ x : Box p m,
        (∑ i : PrefIdx n pol P,
          if (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x then 1 else 0)
          = if Tr.fiberAt T χ x then Tr.chainCount n P else 0 := by
      intro x
      by_cases hfib : Tr.fiberAt T χ x
      · rw [if_pos hfib, ← hF2x Tr hTr x hfib, Finset.card_filter]
        exact Finset.sum_congr rfl (fun i _ => if_congr (and_iff_left hfib) rfl rfl)
      · rw [if_neg hfib]
        exact Finset.sum_eq_zero (fun i _ => if_neg (fun hcon => hfib hcon.2))
    calc (∑ i : PrefIdx n pol P, Nat.card
            ↥{x | (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x})
        = ∑ i : PrefIdx n pol P, ∑ x : Box p m,
            if (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x then 1 else 0 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.card_filter, Nat.card_eq_fintype_card]
          exact Fintype.card_of_subtype _ (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq])
      _ = ∑ x : Box p m, ∑ i : PrefIdx n pol P,
            if (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x then 1 else 0 :=
          Finset.sum_comm
      _ = ∑ x : Box p m, if Tr.fiberAt T χ x then Tr.chainCount n P else 0 :=
          Finset.sum_congr rfl (fun x _ => hpt x)
      _ = ∑ x ∈ Finset.univ.filter (fun x : Box p m => Tr.fiberAt T χ x),
            Tr.chainCount n P := (Finset.sum_filter _ _).symm
      _ = Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x} := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
          congr 1
          rw [Nat.card_eq_fintype_card]
          exact (Fintype.card_of_subtype _ (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq])).symm
  -- ASSEMBLE: finsum to Fintype, split, swap, per-tree count
  rw [finsum_eq_sum_of_fintype]
  calc (∑ i : PrefIdx n pol P, Nat.card
          ↥{x | x ∈ S.fiber i ∧ PreHalt (reprOf i) ∧ Decided T χ x})
      = ∑ i : PrefIdx n pol P, ∑ Tr ∈ 𝒯, Nat.card
          ↥{x | (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x} :=
        Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ Tr ∈ 𝒯, ∑ i : PrefIdx n pol P, Nat.card
          ↥{x | (x ∈ S.fiber i ∧ PreHalt (reprOf i)) ∧ Tr.fiberAt T χ x} :=
        Finset.sum_comm
    _ = ∑ Tr ∈ 𝒯, Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x} :=
        Finset.sum_congr rfl hper

end LeanUrat.MovesT
