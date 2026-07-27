/-
Unit D9.L9_A  (MovesD campaign, E-phase)
moves_ref: "∏ vol(E_fresh(νᵢ)) = p^{−A(P̂)} … the product depends on P̂ alone; A(P̂) := the
resulting shape exponent" (L9).
deps: D0b, D8, D4b, F1 (reprOf ∈ PrefSet gives Matches/coherence); MovesC `mstar_eq`.
sketch: mstar_eq per read → band count → grid filter → A's summand.
difficulty: medium.  hypothesis_fields: `S.jet` only.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D0b_thmCtop
import LeanUrat.MovesD.D4b_chartCount
import LeanUrat.MovesD.D8_bandShape
import LeanUrat.MovesD.F1_enum

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- L9: the presented total pin count at Z = ⊤ is the shape exponent A(P̂, n, N).
Sketch (blueprint rev 9): `totalPins_top` (D0b) collapses the pin count to `Σ m*(νᵢ)`;
`mstar_eq` rewrites each summand as the `inFreshBand` grid count; `band_shape` (D8)
transports it to the shape band `bandS`; `chart_count` (D4b) reads that count off the
level×base grid — exactly `A`'s per-read summand. The history/shape length identity and
the `MatchesHist` hypothesis come from `reprOf_mem` (F1). -/
theorem L9_A (S : Presented p F n N m pol P) (i : PrefIdx n pol P) :
    totalPins (S.jet i) (topLocus p m) = (P : ShapePrefix).A n N := by
  classical
  obtain ⟨hlen, hmatch⟩ := (reprOf_mem i).1
  have hP : (P : ShapePrefix).MatchesHist (reprOf i) := ⟨hlen, hmatch⟩
  rw [totalPins_top]
  unfold ShapePrefix.A
  rw [← hlen]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mem_range] at hr
  rw [(S.jet i).mstar_eq r hr,
      Nat.card_congr (Equiv.subtypeEquivRight (fun c => band_shape (J := S.jet i) hP r hr c))]
  exact chart_count (S.jet i) (fun c => (P : ShapePrefix).bandS n r c)

end LeanUrat.MovesD
