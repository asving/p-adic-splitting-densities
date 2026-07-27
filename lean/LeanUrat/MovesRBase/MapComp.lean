/-
Unit R.map_comp  (MovesR base layer)  [D1's local lemma — no blueprint unit number]
moves_ref: blueprint D1 — "Mathlib LACKS … `WittVector.map_comp` (3-line local ext
lemma via `map_coeff`)". Pointwise form (the form `O_le`'s proof consumes:
`Subfield.subtype (Fsub d) = (Subfield.subtype (Fsub m)).comp (Subfield.inclusion h)`).
deps: Defs.
sketch: `WittVector.ext` + `WittVector.map_coeff` on both sides; `RingHom.comp_apply`.
-/
import Mathlib
import LeanUrat.MovesRBase.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- D1's local composition ext lemma for `WittVector.map` (absent from Mathlib). -/
theorem map_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (g : S →+* T) (f : R →+* S) (x : WittVector p R) :
    WittVector.map g (WittVector.map f x) = WittVector.map (g.comp f) x :=
  WittVector.ext fun n => by
    simp only [WittVector.map_coeff, RingHom.comp_apply]

end MovesRBase
