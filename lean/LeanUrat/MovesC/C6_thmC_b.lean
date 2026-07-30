/-
Unit C6.thmC_b — moves_ref: §C.2 THEOREM C(b): #S(H,Z)·p^{Σm*+|pins Z|} = p^{nN}
  ROUND 3 (audit R2 F36/53/blocker 57): stated on the INDEPENDENT SHZ, and totalPins' summands
  (J.fresh i).mstar are PINNED to the D.11 species inventory by J.mstar_eq (the fresh-band count
  from node data), so the RHS is §C(b)'s actual product, not a presentation artifact.

  ASSEMBLY unit. The box identity is assembled from four deps:
    · C6.thmC_a (iii)          : Nat.card (SHZ Z) = Nat.card (final joint locus Σ_len ∧ Z)
    · C6.transportedAdmissible : Nat.card (joint) · p^{|pins Z|} = mass(Σ_len)
    · C5.massCodim (k = len)   : mass(Σ_len) = p^{m − Σ m*}
    · C5.massRec   (k = len)   : numPinned(Σ_len) = Σ m*      (⇒ Σ m* ≤ m via numPinned ≤ m)
  then p^{m−Σm*} · p^{Σm*} = p^m by Σ m* ≤ m.

  DEP NOTE: `C6_thmC_a.lean` is now built in the repo (its earlier absence had forced a
  local re-proof here as a private `dep_thmC_a`; that duplicate is gone), so all four deps
  above are imported as sorry-free sibling units and this file is pure assembly.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C6_thmC_a
import LeanUrat.MovesC.C6_transportedAdmissible
import LeanUrat.MovesC.C5_massCodim
import LeanUrat.MovesC.C5_massRec

namespace LeanUrat.MovesC

open LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

-- `numPinned` never exceeds the number of coordinates (local copy of the private lemma in
-- `C6_transportedAdmissible`, needed to bound `Σ m* ≤ m`).
omit [Fact p.Prime] in
private lemma numPinned_le' {m : ℕ} (D : Locus p m) : D.numPinned ≤ m := by
  rw [DigitSystem.numPinned]
  exact (Finset.card_filter_le _ _).trans_eq
    (Finset.card_univ.trans (Fintype.card_fin m))

theorem C6_thmC_b {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (Z : Locus p m) (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z) : Nat.card (J.SHZ Z) * p ^ totalPins J Z = boxMass p m := by
  -- (iii): the classifier locus count equals the final joint-locus count
  obtain ⟨_, _, hcardSHZ⟩ := C6_thmC_a J Z hZ
  -- admissible Z peels a factor p^{|pins Z|} off the final state mass
  have htrans := C6_transportedAdmissible (J.Sigma H.nodes.length) Z hZ
  -- the final state mass is p^{m − Σ m*}
  have hcodim := C5_massCodim J H.nodes.length le_rfl
  -- and its pin count is exactly Σ m*, hence Σ m* ≤ m
  have hrec := C5_massRec J H.nodes.length le_rfl
  have hSm : (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar) ≤ m := by
    have hle := numPinned_le' (J.Sigma H.nodes.length)
    rwa [hrec] at hle
  -- assemble: card(SHZ)·p^{Σm*+|pinsZ|} = (card(joint)·p^{|pinsZ|})·p^{Σm*}
  --         = mass·p^{Σm*} = p^{m−Σm*}·p^{Σm*} = p^m
  simp only [boxMass, totalPins]
  rw [hcardSHZ, pow_add, ← mul_assoc, mul_right_comm, htrans, hcodim, ← pow_add,
    Nat.sub_add_cancel hSm]

end LeanUrat.MovesC
