/-
Unit U22.readsOf_SAE  (HC-2 campaign, E-phase — blueprint §5 Layer D; escalation risk;
ENDPOINT-SPLIT per §9 F-4)
moves_ref: §C rev 12 (SAE) display (MovesC `TransitionAdmissible` conjuncts 3–4).
F-EMPTY CITE (mandatory per blueprint): (SAE) is the clause whose ABSENCE the certified
F-EMPTY refutation exposed (nominal fresh volume 2⁻⁶, actual census count 0 — MovesC
round-4 header); a run predicate without it would admit classifier-impossible histories.
deps: D4, the parent's (ZC)-zeroed strips (the stratum's interior zeros raise actual
valuations strictly above the old line), K1 slot reading.  difficulty: HARD.
hypothesis_fields: none.

RESTATED-AS-REDUCTION per §9 F-4 (2026-07-28; statement BYTE-UNCHANGED — the assembled
unit is normative; no fence event, census +2). The fleet escalation PROVED (report-side)
the reduction of (SAE) to two endpoint facts, which become named units:
  U22-E1 `SAE_spanStrict_endpoint` (U22E1_spanStrict.lean) — the strict span-entry
    endpoint: at every recorded span slot strictly below the parent vertex, f's actual
    frame-weight strictly exceeds the parent line's value (the parent's
    (ZC)-zeroed-strips content);
  U22-E2 `SAE_vertexEq_endpoint` (U22E2_vertexEq.lean) — the adjacent-vertex equality
    endpoint: when the new window reaches the vertex, the new side height equals the
    standing vertex height (`hLineU` + the vertex anchoring; the u*-tie).
ASSEMBLY PLAN = the proven reduction + E1 + E2; THE REDUCTION PROOF LANDS FIRST (it
exists — the endpoints are the genuine frontier): the new side's on-side slots read
ACTUAL weights (SideReads(i+1) clauses (i)/(ii)), so E1 at the digit endpoints gives
`old < new` there; both lines are affine in the base index, so strictness at the span's
digit endpoints propagates to every span slot `j < μ` (conjunct 3), and in the adjacent
case E2 + `hLineU` + coherence's width chain give conjunct 4's equality at the vertex.
The endpoint statements are prover-refinable; THIS assembled statement is not.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U22E1_spanStrict
import LeanUrat.HC2.U22E2_vertexEq

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (SAE) for runs: the span-entry inequalities — `new(j) > old(j)` STRICT at every span
slot below the window vertex, equality at the adjacent vertex (conjuncts 3–4 of
`TransitionAdmissible`, extracted). -/
theorem readsOf_SAE {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    (∀ j : ℕ, (H.nodes[i+1]'hi1).s0 ≤ j →
      j ≤ (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide →
      j < (H.nodes[i]'(by omega)).μ →
      (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
        < (H.nodes[i+1]'hi1).line.at (j * (H.nodes[i]'(by omega)).childWidth)) ∧
    ((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide = (H.nodes[i]'(by omega)).μ →
      (H.nodes[i+1]'hi1).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)
        = (H.nodes[i]'(by omega)).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) := by
  -- Assembly (F-4): the proven reduction consuming `SAE_spanStrict_endpoint` (E1) +
  -- `SAE_vertexEq_endpoint` (E2).  Structure: the goal's two conjuncts are conjuncts 3–4 of
  -- `TransitionAdmissible`; coherence supplies the geometry, E1/E2 the strict content.
  have hi0 : i < H.nodes.length := by omega
  -- STRICT affine crossing (cf. `C3.crossing`): a line descends strictly faster; anchored
  -- STRICTLY above at `B` ⇒ strictly above on `[0, B]`.
  have crossLe : ∀ (old new : Line) (Bb x : ℕ), old.slope < new.slope →
      old.at Bb < new.at Bb → x ≤ Bb → old.at x < new.at x := by
    intro old new Bb x hs hB hx
    simp only [Line.at] at hB ⊢
    have hxB : (x : ℚ) ≤ (Bb : ℚ) := by exact_mod_cast hx
    nlinarith [mul_nonneg (sub_pos.mpr hs).le (sub_nonneg.mpr hxB)]
  -- STRICT crossing from an EQUALITY at `B`: strictly above at `x < B`.
  have crossEq : ∀ (old new : Line) (Bb x : ℕ), old.slope < new.slope →
      old.at Bb = new.at Bb → x < Bb → old.at x < new.at x := by
    intro old new Bb x hs hB hx
    simp only [Line.at] at hB ⊢
    have hxB : (x : ℚ) < (Bb : ℚ) := by exact_mod_cast hx
    nlinarith [mul_pos (sub_pos.mpr hs) (sub_pos.mpr hxB)]
  -- Coherence + the read data at read `i+1`.
  have hcoh := h.2.2.1
  obtain ⟨B, Nd, Φnext, hdev, hΦ, hSR⟩ := h.2.2.2 (i+1) hi1
  -- Coherence step-data at the transition `i → i+1`.
  have hstepi := hcoh.2.2.2 i hi1
  have hwin : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide ≤ (H.nodes[i]'hi0).μ :=
    hstepi.2.2.2.2.1
  have hwidth : (H.nodes[i+1]'hi1).Dwidth = (H.nodes[i]'hi0).childWidth :=
    hstepi.2.2.2.2.2.1
  have hsteep : (H.nodes[i]'hi0).line.slope < (H.nodes[i+1]'hi1).line.slope :=
    hstepi.2.2.2.2.2.2
  -- γ-tie at read `i+1` (absolute-scale total side weight).
  have hgam : (((H.nodes[i+1]'hi1).gam : ℤ) : ℚ)
      = ((H.nodes[i+1]'hi1).e : ℚ) * ((H.strFrame (i+1) : ℚ) * (H.nodes[i+1]'hi1).ustar)
        + ((((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide) : ℕ) : ℚ)
            * ((H.nodes[i+1]'hi1).h : ℚ) :=
    hcoh.2.2.1 (i+1) hi1
  -- Positivity: the stretch factor and the parent child-width are positive.
  have hSTRpos : 0 < (H.strFrame (i+1) : ℚ) := by
    have h0 : 0 < H.strFrame (i+1) := by
      unfold History.strFrame
      apply List.prod_pos
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨ν, _, rfl⟩ := hx
      exact ν.he
    exact_mod_cast h0
  have hcWpos : 0 < (H.nodes[i]'hi0).childWidth := by
    unfold Node.childWidth
    have hD : 1 ≤ (H.nodes[i]'hi0).Dwidth := by
      rw [(H.nodes[i]'hi0).hDwidth]; exact (H.nodes[i]'hi0).σ.hdeg
    exact Nat.mul_pos (Nat.mul_pos (H.nodes[i]'hi0).he (H.nodes[i]'hi0).hg) hD
  have hepos : (0 : ℚ) < ((H.nodes[i+1]'hi1).e : ℚ) := by
    exact_mod_cast (H.nodes[i+1]'hi1).he
  -- The VERTEX-EQUALITY (conjunct 4 / E2): needed both as the second goal component and in
  -- the adjacent branch of conjunct 3.
  have hvertexEq : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide = (H.nodes[i]'hi0).μ →
      (H.nodes[i+1]'hi1).line.at
          ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
        = (H.nodes[i]'hi0).line.at
          ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth) := by
    intro hadj
    have hE2 := SAE_vertexEq_endpoint h i hi1 hadj
    have hLU := (H.nodes[i+1]'hi1).hLineU
    rw [hwidth] at hLU
    -- `line.at ((s0'+wSide')·cW) = ustar'` and `s0'+wSide' = μ`.
    rw [hadj] at hLU
    rw [hLU, hE2]
  -- KEY: strict span-entry at the top digit stride `j* = s0'+wSide'`, when `j* < μ`.
  have htop : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide < (H.nodes[i]'hi0).μ →
      (H.nodes[i]'hi0).line.at
          (((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide) * (H.nodes[i]'hi0).childWidth)
        < (H.nodes[i+1]'hi1).line.at
          (((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide) * (H.nodes[i]'hi0).childWidth) := by
    intro hlt
    -- clause (ii) of `SideReads` at the TOP stride `k = wSide/e`.
    have hstride := hSR.2.1 ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
      (le_refl _) (H.nodes[i+1]'hi1).hpatTop
    rw [Nat.mul_div_cancel' (H.nodes[i+1]'hi1).hEdvd] at hstride
    obtain ⟨hBne, hweq, _⟩ := hstride
    -- hLineU at read `i+1` (width chain folds `Dwidth' → cW`): `new.line.at(j*·cW) = ustar'`.
    have hLU := (H.nodes[i+1]'hi1).hLineU
    rw [hwidth] at hLU
    -- γ-tie + clause (ii): the development weight at `j*` equals `STR·ustar'` (÷ e).
    have key : ((H.nodes[i+1]'hi1).e : ℚ)
          * (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide)) : ℤ) : ℚ)
        = ((H.nodes[i+1]'hi1).e : ℚ)
          * ((H.strFrame (i+1) : ℚ) * (H.nodes[i+1]'hi1).ustar) := by
      have h1 : ((H.nodes[i+1]'hi1).e : ℚ)
            * (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide)) : ℤ) : ℚ)
          + ((((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide) : ℕ) : ℚ) * ((H.nodes[i+1]'hi1).h : ℚ)
          = (((H.nodes[i+1]'hi1).gam : ℤ) : ℚ) := by exact_mod_cast hweq
      linarith [h1, hgam]
    have hval_u : (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide)) : ℤ) : ℚ)
        = (H.strFrame (i+1) : ℚ) * (H.nodes[i+1]'hi1).ustar :=
      mul_left_cancel₀ (ne_of_gt hepos) key
    -- E1 at the top stride `j*` gives strict domination of the weight over the OLD line.
    have hE1 := SAE_spanStrict_endpoint h i hi1 B Nd hdev
      ((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide)
      (Nat.le_add_right _ _) (le_refl _) hlt hBne
    have hstr : (H.strFrame (i+1) : ℚ)
          * (H.nodes[i]'hi0).line.at
              (((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide) * (H.nodes[i]'hi0).childWidth)
        < (H.strFrame (i+1) : ℚ) * (H.nodes[i+1]'hi1).ustar := lt_of_lt_of_eq hE1 hval_u
    have hlt2 : (H.nodes[i]'hi0).line.at
              (((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide) * (H.nodes[i]'hi0).childWidth)
          < (H.nodes[i+1]'hi1).ustar := lt_of_mul_lt_mul_left hstr hSTRpos.le
    exact lt_of_lt_of_eq hlt2 hLU.symm
  -- Assemble the two conjuncts.
  refine ⟨?_, hvertexEq⟩
  intro j hj1 hj2 hj3
  -- window containment: `j* ≤ μ`, so either `j* < μ` (use E1 at `j*`) or `j* = μ` (use E2).
  rcases lt_or_eq_of_le hwin with hlt | heq
  · -- non-adjacent: strict at `j*`, then affine crossing back to `j ≤ j*`.
    refine crossLe (H.nodes[i]'hi0).line (H.nodes[i+1]'hi1).line
      (((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide) * (H.nodes[i]'hi0).childWidth)
      (j * (H.nodes[i]'hi0).childWidth) hsteep (htop hlt) ?_
    exact Nat.mul_le_mul_right _ hj2
  · -- adjacent: equality at the vertex `μ`, then STRICT crossing since `j < μ`.
    have heqline := hvertexEq heq
    refine crossEq (H.nodes[i]'hi0).line (H.nodes[i+1]'hi1).line
      ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
      (j * (H.nodes[i]'hi0).childWidth) hsteep heqline.symm ?_
    exact mul_lt_mul_of_pos_right hj3 hcWpos

end LeanUrat.MovesJ
