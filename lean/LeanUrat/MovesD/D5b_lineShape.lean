/-
Unit D5b.line_shape  (MovesD campaign, E-phase)
moves_ref: "each line is the slope −h_r/e_r line through (j*_r, u*_r), pinned only WITH
its height … A is a function of P̂ only because u*_r ∈ P̂" (L9 rev 9 — u* enters HERE,
through the intercept).
deps: D5a, D6a.
sketch: `Line` ext; slope from coherence's slope law (e·STR·D ≠ 0 via he/D5a/strS ≥ 1);
intercept solved from `hLineU` at the matched right endpoint.  difficulty: medium.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {P : Shape n}

/-- The recorded read line IS the shape line (slope + intercept both shape data). -/
theorem line_shape {H : History p F} (hcoh : HistoryCoherent H)
    (hP : (P : ShapePrefix).MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) :
    (H.nodes[r]'hr).line = (P : ShapePrefix).lineS r := by
  obtain ⟨hlen, hmatch⟩ := hP
  have hr' : r < (P : ShapePrefix).reads.length := hlen ▸ hr
  -- the matched read / node data
  have hM : ((P : ShapePrefix).reads[r]'hr').Matches (H.nodes[r]'hr) := hmatch r hr
  obtain ⟨_, hMe, hMh, _, _, _, hMs0, hMwSide, hMDwidth, hMustar, _, _, _⟩ := hM
  -- the stretch is shape data (D6a content, proved inline)
  have hmapfull : H.nodes.map Node.e = (P : ShapePrefix).reads.map ShapeRead.e := by
    apply List.ext_getElem
    · simp only [List.length_map]; exact hlen
    · intro j hj1 hj2
      have hjr : j < H.nodes.length := by
        simpa only [List.length_map] using hj1
      simpa only [List.getElem_map] using (hmatch j hjr).2.1
  have hstr : H.strFrame r = (P : ShapePrefix).strS r := by
    show ((H.nodes.take r).map Node.e).prod
        = (((P : ShapePrefix).reads.take r).map ShapeRead.e).prod
    rw [List.map_take, List.map_take, hmapfull]
  -- positivity of the slope denominator e·STR·D
  have hstrpos : 0 < (P : ShapePrefix).strS r := by
    show 0 < (((P : ShapePrefix).reads.take r).map ShapeRead.e).prod
    apply List.prod_pos
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨R', _, rfl⟩ := hx
    exact R'.he
  have hden : (((P : ShapePrefix).reads[r]'hr').e : ℚ) * ((P : ShapePrefix).strS r : ℚ)
        * (((P : ShapePrefix).reads[r]'hr').Dwidth : ℚ) ≠ 0 := by
    have h1 : (0 : ℚ) < (((P : ShapePrefix).reads[r]'hr').e : ℚ) := by
      exact_mod_cast ((P : ShapePrefix).reads[r]'hr').he
    have h2 : (0 : ℚ) < (((P : ShapePrefix).reads[r]'hr').Dwidth : ℚ) := by
      exact_mod_cast ((P : ShapePrefix).reads[r]'hr').hDw
    have h3 : (0 : ℚ) < ((P : ShapePrefix).strS r : ℚ) := by exact_mod_cast hstrpos
    exact ne_of_gt (by positivity)
  -- the slope: coherence's absolute-scale slope law, in shape data
  have hslope : (H.nodes[r]'hr).line.slope
      = (((P : ShapePrefix).reads[r]'hr').h : ℚ)
        / ((((P : ShapePrefix).reads[r]'hr').e : ℚ) * ((P : ShapePrefix).strS r : ℚ)
            * (((P : ShapePrefix).reads[r]'hr').Dwidth : ℚ)) := by
    rw [eq_div_iff hden]
    have hco := hcoh.2.1 r hr
    rw [show (((P : ShapePrefix).reads[r]'hr').e : ℚ) = ((H.nodes[r]'hr).e : ℚ) from by
          exact_mod_cast hMe.symm,
        show ((P : ShapePrefix).strS r : ℚ) = (H.strFrame r : ℚ) from by
          exact_mod_cast hstr.symm,
        show (((P : ShapePrefix).reads[r]'hr').Dwidth : ℚ) = ((H.nodes[r]'hr).Dwidth : ℚ) from by
          exact_mod_cast hMDwidth.symm,
        show (((P : ShapePrefix).reads[r]'hr').h : ℚ) = ((H.nodes[r]'hr).h : ℚ) from by
          exact_mod_cast hMh.symm]
    exact hco
  -- the matched right-endpoint base index is shape data
  have hnat : ((H.nodes[r]'hr).s0 + (H.nodes[r]'hr).wSide) * (H.nodes[r]'hr).Dwidth
      = (((P : ShapePrefix).reads[r]'hr').s0 + ((P : ShapePrefix).reads[r]'hr').wSide)
          * ((P : ShapePrefix).reads[r]'hr').Dwidth := by
    rw [hMs0, hMwSide, hMDwidth]
  -- the intercept: solve `hLineU` at the matched right endpoint
  have hint : (H.nodes[r]'hr).line.intercept
      = ((P : ShapePrefix).reads[r]'hr').ustar
        + (((P : ShapePrefix).reads[r]'hr').h : ℚ)
          / ((((P : ShapePrefix).reads[r]'hr').e : ℚ) * ((P : ShapePrefix).strS r : ℚ)
              * (((P : ShapePrefix).reads[r]'hr').Dwidth : ℚ))
          * (((((P : ShapePrefix).reads[r]'hr').s0 + ((P : ShapePrefix).reads[r]'hr').wSide)
              * ((P : ShapePrefix).reads[r]'hr').Dwidth : ℕ) : ℚ) := by
    have hLU := (H.nodes[r]'hr).hLineU
    simp only [Line.at] at hLU
    rw [hnat, hMustar, hslope] at hLU
    linarith
  -- assemble: reduce `lineS r` and fold both fields back into `ν.line`
  have hlineS_explicit : (P : ShapePrefix).lineS r
      = ⟨((P : ShapePrefix).reads[r]'hr').ustar
          + (((P : ShapePrefix).reads[r]'hr').h : ℚ)
            / ((((P : ShapePrefix).reads[r]'hr').e : ℚ) * ((P : ShapePrefix).strS r : ℚ)
                * (((P : ShapePrefix).reads[r]'hr').Dwidth : ℚ))
            * (((((P : ShapePrefix).reads[r]'hr').s0 + ((P : ShapePrefix).reads[r]'hr').wSide)
                * ((P : ShapePrefix).reads[r]'hr').Dwidth : ℕ) : ℚ),
         (((P : ShapePrefix).reads[r]'hr').h : ℚ)
            / ((((P : ShapePrefix).reads[r]'hr').e : ℚ) * ((P : ShapePrefix).strS r : ℚ)
                * (((P : ShapePrefix).reads[r]'hr').Dwidth : ℚ))⟩ := by
    unfold ShapePrefix.lineS
    rw [List.getElem?_eq_getElem hr']
    rfl
  rw [hlineS_explicit, ← hint, ← hslope]

end LeanUrat.MovesD
