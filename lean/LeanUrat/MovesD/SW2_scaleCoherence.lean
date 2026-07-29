/-
Unit SW2.scaleCoherence  (MovesD campaign, ratification repair D1, 2026-07-28)
[RATIFICATION RULING — finding D1 (γ-tie STR factor) OVERRULED, coherence seal added.]
moves_ref: the ratifier (fresh context, §D4-R only) read `ShapeWF.gamTie`'s STR factor as
a deviation from L3's "γ_r := e_r·u*_r + j*_r·h_r" (note 4707). Adjudication: that display
is scale-HOMOGENEOUS at STAGE scale — §C C.0 marks γ_i "(augmented scale)" (note 3461) —
while the frozen MovesC `Node` records `ustar` ABSOLUTE and `gam` STAGE, with the
conversion stage = STR × absolute (C.1.0(c) Scale declaration, note 3635–3645). The
corpus's `gamTie`/`lineS`/`kappaS` carry the STR factor in exactly the compensating spots.
This unit is the MACHINE-CHECKED coherence seal: (i) `lineS_at_jstar` — the read line's
intercept convention and the height pair cohere (the line pinned through (j*, u*) returns
u* at the right endpoint's base index, mirroring Node.hLineU shape-side); (ii)
`gamTie_stage_form` — the displayed stage-scale identity γ = e·(STR·u*) + j*·h, i.e. L3's
display with u*_stage := STR·u*_absolute, packaged as the ruling record.
deps: Defs.  sketch: ring arithmetic from the lineS def; gamTie restated.
difficulty: easy.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {n : ℕ} {P : Shape n}

/-- **Coherence seal (i)**: the shape-side read line `lineS r` — slope `h/(e·STR·D)`,
intercept pinned through `(j*, u*)` — evaluated at the right endpoint's base index
`(s0 + wSide)·Dwidth` returns `ustar`. This is MovesC `Node.hLineU` ("the read line PASSES
THROUGH (j*, u*)", absolute v_p-scale) replayed on shape data: the intercept convention
of `lineS` and the height pair (h, u*) cohere. Needs no certificate — pure ring
arithmetic from the `lineS` definition (note 4707's height-pair retention; C.1.0(c)
scale declaration, note 3635–3645). -/
theorem lineS_at_jstar (r : ℕ) (hr : r < (P : ShapePrefix).reads.length) :
    ((P : ShapePrefix).lineS r).at
        ((((P : ShapePrefix).reads[r]'hr).s0 + ((P : ShapePrefix).reads[r]'hr).wSide)
          * ((P : ShapePrefix).reads[r]'hr).Dwidth)
      = ((P : ShapePrefix).reads[r]'hr).ustar := by
  have hs : (P : ShapePrefix).reads[r]? = some ((P : ShapePrefix).reads[r]'hr) :=
    List.getElem?_eq_getElem hr
  simp only [ShapePrefix.lineS, hs, Option.elim_some, Line.at]
  ring

/-- **Coherence seal (ii) — the ruling record for finding D1**: the certificate's γ-tie IS
L3's display "γ_r := e_r·u*_r + j*_r·h_r" (note 4707) read at STAGE scale: γ (recorded as
the stage-scale integer `gam`, §C C.0 "(augmented scale)", note 3461) equals
e·(STR·u*) + j*·h where `STR·ustar` is the ABSOLUTE-scale `ustar` converted to stage scale
per C.1.0(c)'s Scale declaration (stage = STR × absolute, note 3635–3645). The ratifier
had only §D4-R in context; this theorem is the machine-checked answer: the STR factor is
the scale CONVERSION, not a deviation. (The gate shapes have strS = 1 throughout, so the
two readings coincide there — this seal covers every shape.) -/
theorem gamTie_stage_form (r : ℕ) (hr : r < (P : ShapePrefix).reads.length) :
    ((((P : ShapePrefix).reads[r]'hr).gam : ℤ) : ℚ)
      = (((P : ShapePrefix).reads[r]'hr).e : ℚ)
          * (((P : ShapePrefix).strS r : ℚ) * ((P : ShapePrefix).reads[r]'hr).ustar)
        + (((((P : ShapePrefix).reads[r]'hr).s0 + ((P : ShapePrefix).reads[r]'hr).wSide) : ℕ) : ℚ)
          * (((P : ShapePrefix).reads[r]'hr).h : ℚ) :=
  P.2.gamTie r hr

end LeanUrat.MovesD
