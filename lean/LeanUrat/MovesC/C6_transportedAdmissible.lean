/-
Unit C6.transportedAdmissible — moves_ref: §C.2 admissible Z cuts exactly vol(Z) on the final state

An admissible terminal system `Z` (pins only coordinates FREE on the state `Sigma`) cuts a
factor `p^{−Z.numPinned}` of the state mass: the joint solution count times `p^{Z.numPinned}`
recovers `Sigma.mass`. Proof follows the sketch — form the JOINT digit system (pinned where
either pins; disjoint by admissibility), whose numPinned adds and whose solution set is the
∧-cut, then apply the digit-count mass law (`C0.digitSystemMass` content, here re-derived as
`massForm` from the sibling `C0.solvedGraph` equiv so it holds for every `p : ℕ`, no primality).
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C0_solvedGraph

namespace LeanUrat.MovesC

open LeanUrat.Moves

variable {p m : ℕ}

/-- The number of free (unpinned) coordinates is `m − numPinned`. -/
private lemma cardFree (D : Locus p m) :
    Nat.card {j : Fin m // D.pinned j = false} = m - D.numPinned := by
  rw [Nat.card_eq_fintype_card]
  have e : {i : Fin m // D.pinned i = false} ≃ {i : Fin m // ¬ (D.pinned i = true)} :=
    Equiv.subtypeEquivRight (fun i => by cases D.pinned i <;> simp)
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  rfl

/-- **The digit-count mass law** (`C0.digitSystemMass` content, D.3(e)(ii)/D.11): `mass =
p^{m−numPinned}`. Re-derived from the `C0.solvedGraph` free-coordinate equiv + `Nat.card_fun`
(which needs only a FINITE domain), so it holds for every `p : ℕ` — no `Fact p.Prime`. -/
private lemma massForm (D : Locus p m) : D.mass = p ^ (m - D.numPinned) := by
  obtain ⟨E, _⟩ := C0_solvedGraph D
  unfold Locus.mass
  rw [Nat.card_congr E, Nat.card_fun, Nat.card_zmod, cardFree D]

/-- `numPinned` never exceeds the number of coordinates. -/
private lemma numPinned_le (D : Locus p m) : D.numPinned ≤ m := by
  rw [DigitSystem.numPinned]
  calc (Finset.univ.filter (fun i => D.pinned i)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = m := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The joint digit system**: pin a coordinate where EITHER `Sigma` or `Z` pins it, and solve
it by whichever one does (`Sigma` takes priority; the two are disjoint under admissibility). -/
private def joint (Sigma Z : Locus p m) : Locus p m where
  pinned := fun i => Sigma.pinned i || Z.pinned i
  solve := fun i f => if Sigma.pinned i then Sigma.solve i f else Z.solve i f

/-- Under admissibility, solving the joint system is exactly solving both. -/
private lemma joint_isSol {Sigma Z : Locus p m} (hZ : AdmissibleZ Sigma Z)
    (x : Fin m → ZMod p) :
    (joint Sigma Z).IsSolution x ↔ Sigma.IsSolution x ∧ Z.IsSolution x := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have := h i (by simp [joint, hi])
      simpa [joint, hi] using this
    · intro i hi
      have hsig : Sigma.pinned i = false := hZ i hi
      have := h i (by simp [joint, hi])
      simpa [joint, hsig] using this
  · rintro ⟨hs, hz⟩ i hi
    simp only [joint] at hi ⊢
    rcases hsp : Sigma.pinned i with _ | _
    · rw [if_neg (by simp)]
      have : Z.pinned i = true := by
        rcases Bool.or_eq_true _ _ |>.mp hi with h | h
        · rw [hsp] at h; exact absurd h (by simp)
        · exact h
      exact hz i this
    · rw [if_pos (by simp)]
      exact hs i hsp

/-- Under admissibility the joint pins are the disjoint union, so counts add. -/
private lemma joint_numPinned {Sigma Z : Locus p m} (hZ : AdmissibleZ Sigma Z) :
    (joint Sigma Z).numPinned = Sigma.numPinned + Z.numPinned := by
  simp only [DigitSystem.numPinned, joint]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
      Bool.or_eq_true]
  · rw [Finset.disjoint_filter]
    intro i _ hs hz
    have : Sigma.pinned i = false := hZ i hz
    rw [this] at hs
    exact absurd hs (by simp)

theorem C6_transportedAdmissible {m : ℕ} (Sigma Z : Locus p m) (hZ : AdmissibleZ Sigma Z) : Nat.card {x : Fin m → ZMod p // Sigma.IsSolution x ∧ Z.IsSolution x} * p ^ Z.numPinned = Sigma.mass := by
  have hcard : Nat.card {x : Fin m → ZMod p // Sigma.IsSolution x ∧ Z.IsSolution x}
      = (joint Sigma Z).mass := by
    unfold Locus.mass
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => (joint_isSol hZ x).symm))
  rw [hcard, massForm, massForm, joint_numPinned hZ]
  have hle : Sigma.numPinned + Z.numPinned ≤ m := by
    have := numPinned_le (joint Sigma Z)
    rwa [joint_numPinned hZ] at this
  rw [← pow_add]
  congr 1
  omega

end LeanUrat.MovesC
