/-
Unit D4R4_all (+TW)  (MovesD campaign, E-phase)
[REV 5, reconciliation (5) — Codex#3 finding 4; restated on `Threshold`.]
moves_ref: L12 QUOTED VERBATIM: "N(P̂) is finite, and for EVERY N ≥ N(P̂):
Σ_{η ∈ Pref(P̂)} #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN − A(P̂)} (D4R.4-SUM) …
#{f mod p^N ∈ S(P̂,⊤)} ≤ C_P̂(p)·p^{nN − A(P̂)} (D4R.4-EV)". MATCH: ∀ N ≥ NP, the SUM
equality ∧ the EV bound, constants CD and A′ N-free. The note quantifies over LEVELS only.
[REV 9: the range's L12-exactness rests on the SEAM pin **NP-ID** (§2.5 W4-4) —
conditionality pointer, per Codex#7 g.4.]
TW: `Threshold` has NO NP/hstab fields — TW builds the sole field `jets` from `hex` by
choice on L12's exact piecewise range; PRESENT-EXIST (§2) is consumed HERE and only here.
deps: D10, D12, D2a (CD_eq), NPu; NP_stab bridges A n N to A′ on the inhabited branch;
the empty branch is the 0 = 0 case split (L12's empty clause, every N ≥ 1).
sketch: apply D10/D12 at T.jets N with hA := NP_stab N.  difficulty: easy-medium.
hypothesis_fields: `T : Threshold` (sole field: jets — the L12 presentations, HC-2);
`hex` (PRESENT-EXIST, restated at NP) only in TW.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D10_sumLaw
import LeanUrat.MovesD.D12_evBound
import LeanUrat.MovesD.NPu_threshold
import LeanUrat.MovesD.D2a_finite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- D4R.4-SUM ∧ D4R.4-EV at EVERY N ≥ N(P̂) — L12's exact range on the threshold data. -/
theorem D4R4_all (hne : (P : ShapePrefix).reads ≠ []) (T : Threshold p F n pol P) :
    ∀ (N : ℕ) (hNP : P.NP pol ≤ N),
      ((∑ᶠ i : PrefIdx n pol P, Nat.card ↥((T.jets N hNP).fiber i))
          * p ^ ((P : ShapePrefix).A' n) = P.CD pol * p ^ (n * N)) ∧
      (Nat.card ↥(T.jets N hNP).event * p ^ ((P : ShapePrefix).A' n)
          ≤ P.CD pol * p ^ (n * N)) := by
  classical
  intro N hNP
  by_cases hInh : Nonempty (PrefIdx n pol P)
  · -- INHABITED branch: NP = NPband, so `NP_stab` discharges the ledger stabilization
    -- `hA : A n N = A′ n`, and `CD_eq` identifies the corpus constant with the class count.
    haveI : Nonempty (PrefIdx n pol P) := hInh
    have hA : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n := NP_stab N hNP
    have hCD : P.CD pol = Nat.card (PrefIdx n pol P) := CD_eq (T.jets N hNP).hnorm hne
    refine ⟨?_, ?_⟩
    · rw [hCD]; exact D4R1_SUM hne N hA (T.jets N hNP)
    · rw [hCD]; exact D4R1_EV hne N hA (T.jets N hNP)
  · -- EMPTY branch (Pref(P̂) = ∅): L12's "C_P̂(p) = 0 and S(P̂,⊤) = ∅" clause — both sides
    -- vanish at EVERY N ≥ 1, no stabilization consumed.
    rw [not_nonempty_iff] at hInh
    haveI : IsEmpty (PrefIdx n pol P) := hInh
    have hCD0 : P.CD pol = 0 := by
      unfold Shape.CD
      rw [if_neg hne]
      exact Nat.card_of_isEmpty
    have hsum0 : (∑ᶠ i : PrefIdx n pol P, Nat.card ↥((T.jets N hNP).fiber i)) = 0 :=
      finsum_of_isEmpty _
    have hev0 : (T.jets N hNP).event = ∅ := by
      simp only [Presented.event, Set.iUnion_of_empty]
    refine ⟨?_, ?_⟩
    · rw [hsum0, hCD0]; ring
    · rw [hCD0, hev0]; simp

/-- TW: the threshold witness from PRESENT-EXIST at L12's exact range. -/
theorem TW_threshold_witness
    (hex : ∀ N : ℕ, P.NP pol ≤ N → Nonempty (Presented p F n N (n * N) pol P)) :
    Nonempty (Threshold p F n pol P) :=
  ⟨{ jets := fun N hNP => (hex N hNP).some }⟩

end LeanUrat.MovesD
