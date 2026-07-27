/-
Unit D10.D4R1_SUM  (MovesD campaign, E-phase)
moves_ref: "Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)} (D4R.1-SUM)" ≡ "N(P̂) is
finite, and for EVERY N ≥ N(P̂): Σ_η #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN − A(P̂)}
(D4R.4-SUM)". THE QUANTIFIER [REV 5]: N and S universally bound at every level where the
ledger has stabilized — `hA : P.A n N = P.A' n`, DISCHARGED by L9s whenever `Nshape ≤ N`
and by NP_stab from the note's own NP on; C and A′ are N-FREE, so all levels share their
constants — D4R.4's content. The uniform-threshold packaging is D4R4_all.
deps: D0b, D9, L9s, D2a (Fintype from Finite for ∑ᶠ).
sketch: per summand thmC_top + D9 + A_stable; sum the constant. NO disjointness consumed.
difficulty: medium.  hypothesis_fields: `S.jet` only.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D0b_thmCtop
import LeanUrat.MovesD.D9_L9
import LeanUrat.MovesD.D2a_finite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- D4R.1-SUM ≡ D4R.4-SUM at every stabilized level, division-free. -/
theorem D4R1_SUM (hne : (P : ShapePrefix).reads ≠ []) (N : ℕ)
    (hA : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n)
    (S : Presented p F n N m pol P) :
    (∑ᶠ i : PrefIdx n pol P, Nat.card ↥(S.fiber i)) * p ^ ((P : ShapePrefix).A' n)
      = Nat.card (PrefIdx n pol P) * p ^ (n * N) := by
  classical
  haveI : Fintype (PrefIdx n pol P) := Fintype.ofFinite _
  -- Per summand: Theorem C(b) at Z = ⊤ (D0b), with the total pin count identified as the
  -- N-free shape exponent A′ (D9's `L9_A` composed with the stabilization hypothesis `hA`).
  have key : ∀ i : PrefIdx n pol P,
      Nat.card ↥(S.fiber i) * p ^ ((P : ShapePrefix).A' n) = p ^ (n * N) := by
    intro i
    have h2 : totalPins (S.jet i) (topLocus p m) = (P : ShapePrefix).A' n :=
      (L9_A S i).trans hA
    have h1 := thmC_top (S.jet i)
    rw [h2] at h1
    simpa [Presented.fiber] using h1
  -- Sum the constant `p ^ (n·N)` over the finite class index `PrefIdx`.
  rw [finsum_eq_sum_of_fintype, Finset.sum_mul,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => key i),
    Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]

end LeanUrat.MovesD
