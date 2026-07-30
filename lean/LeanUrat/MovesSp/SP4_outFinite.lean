/-
Unit Sp.outFinite [REV 4, Codex-3 FIXED — restricted to the note's own
quantifier: SP.4 defines Out only on catalogue letters] — moves_ref:
"**Definition (Out; retyped at rev 3).** For s ∈ 𝒮_n^raw, the OUTGOING MENU
Out(s) ⊆ 𝒮_n^raw ∪ V_term" + "FINITENESS: |Out(s)| ≤ |𝒮_n^raw| + 3 by SP-FIN."
deps: Sp.finThm. sketch: Succ n s ⊆ SnRaw n; union card ≤ sum; card Verdict = 3.
(hs is not needed by the proof — the restriction is FAITHFULNESS to the display's
quantifier, per the adjudication: never state more than the note does.)
difficulty: easy.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP2_finThm

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- `Verdict` (SP.4) is the 3-label terminal type; a `Fintype` instance so its
`Set.univ` is finite of cardinality 3 (the "+3" in the SP-OUT bound). -/
instance : Fintype Verdict := ⟨{Verdict.z, Verdict.ep, Verdict.ns}, fun x => by cases x <;> decide⟩

theorem out_finite (n : ℕ) (hn : 1 ≤ n) (s : Species)
    (hs : InCatalogue n s) : (Out n s).Finite ∧
    Nat.card (Out n s) ≤ Nat.card (SnRaw n) + 3 := by
  -- SnRaw n is finite (SP-FIN); Succ n s ⊆ SnRaw n, hence finite too.
  have hfin : (SnRaw n).Finite := (SP_FIN n hn).1
  have hSuccSub : Succ n s ⊆ SnRaw n := fun s' hs' => hs'.1
  have hSuccFin : (Succ n s).Finite := hfin.subset hSuccSub
  -- The two legs of the disjoint union `Out n s = (inl '' Succ) ∪ (inr '' univ)`.
  have hA : ((Sum.inl : Species → Species ⊕ Verdict) '' Succ n s).Finite := hSuccFin.image _
  have hB : ((Sum.inr : Verdict → Species ⊕ Verdict) '' (Set.univ : Set Verdict)).Finite :=
    Set.finite_univ.image _
  -- Cardinality of the Verdict factor is 3.
  have hvcard : (Set.univ : Set Verdict).ncard = 3 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    decide
  refine ⟨hA.union hB, ?_⟩
  change (Out n s).ncard ≤ (SnRaw n).ncard + 3
  calc (Out n s).ncard
      ≤ ((Sum.inl : Species → Species ⊕ Verdict) '' Succ n s).ncard
          + ((Sum.inr : Verdict → Species ⊕ Verdict) '' (Set.univ : Set Verdict)).ncard :=
        Set.ncard_union_le _ _
    _ = (Succ n s).ncard + (Set.univ : Set Verdict).ncard := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective,
            Set.ncard_image_of_injective _ Sum.inr_injective]
    _ ≤ (SnRaw n).ncard + 3 := by
        rw [hvcard]
        exact Nat.add_le_add_right (Set.ncard_le_ncard hSuccSub hfin) 3

end LeanUrat.MovesSp
