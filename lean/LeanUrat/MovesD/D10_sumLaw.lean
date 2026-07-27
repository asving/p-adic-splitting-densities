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

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
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
  sorry

end LeanUrat.MovesD
