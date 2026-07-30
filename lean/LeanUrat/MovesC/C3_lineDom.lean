/-
Unit C3.lineDom — moves_ref: §C Lemma DOM for the RECORDED lines — ROUND 4 (audit R3
finding 16): rev 14's DOM quantifies over REALIZABLE prefixes and sources the span-entry
inequality from (SAE); the statement HYPOTHESIZES the realizability class.

Induction on i. Step k → k+1: the current line line_{k+1} dominates the parent line_k on
[0, μ_{k+1}·cW_{k+1}). The endpoint j* := s0_{k+1}+wSide_{k+1} anchors the comparison at base
index j*·D_{k+1} = j*·cW_k (width chain): (SAE)'s span clause gives new > old there when
j* < μ_k (non-adjacent), the (SAE) vertex-equality clause gives new = old when j* = μ_k
(adjacent, window containment forces j* ≤ μ_k). With slope_k < slope_{k+1} (coherence) the
affine map new − old is decreasing and ≥ 0 at the anchor, hence ≥ 0 on all of [0, anchor],
which contains [0, μ_{k+1}·cW_{k+1}) by C3.widthConfine (μ·cW ≤ wSide·D ≤ j*·D) — proved
inline from the ψ-adic-order degree bound μ·g ≤ deg Ranch = wSide/e. The same chain nests the
interior (μ_{k+1}·cW_{k+1} ≤ j*·cW_k ≤ μ_k·cW_k), so the IH at k applies. Base j = i trivial.
-/
import LeanUrat.MovesC.Defs

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C3_lineDom (H : History p F) (hcoh : HistoryCoherent H) (hreal : Realizable H) (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (hij : j ≤ i) (b : ℕ) (hb : b < (H.nodes[i]'hi).μ * (H.nodes[i]'hi).childWidth) : (H.nodes[j]'(by omega)).line.at b ≤ (H.nodes[i]'hi).line.at b := by
  -- the adjacent-step data of coherence (the 4th conjunct: window/width/steepness ties)
  have hstep := hcoh.2.2.2
  -- AFFINE CROSSING: a descending line anchored ≥ its rival at the RIGHT endpoint B dominates
  -- on all of [0, B].  new − old is affine with negative slope, ≥ 0 at B ⇒ ≥ 0 for x ≤ B.
  have crossing : ∀ (old new : Line) (B : ℕ), old.slope < new.slope →
      old.at B ≤ new.at B → ∀ (x : ℕ), x ≤ B → old.at x ≤ new.at x := by
    intro old new B hsteep hanchor x hx
    simp only [Line.at] at hanchor ⊢
    have hxB : (x : ℚ) ≤ (B : ℚ) := by exact_mod_cast hx
    nlinarith [mul_nonneg (sub_pos.mpr hsteep).le (sub_nonneg.mpr hxB)]
  -- WIDTH CONFINE (C3.widthConfine, inline): μ·childWidth ≤ wSide·Dwidth.
  -- ψ^μ ∣ Ranch and Ranch ≠ 0 ⇒ μ·g = deg ψ^μ ≤ deg Ranch ≤ wSide/e; scale by e (e ∣ wSide) and D.
  have widthConfine : ∀ (ν : Node p F), ν.μ * ν.childWidth ≤ ν.wSide * ν.Dwidth := by
    intro ν
    have hRne : ν.Ranch ≠ 0 := fun h0 => ν.hOrd.2 (by rw [h0]; exact dvd_zero _)
    have hdvd : (ν.ψ ^ ν.μ).natDegree ≤ ν.Ranch.natDegree :=
      Polynomial.natDegree_le_of_dvd ν.hOrd.1 hRne
    have hdegpow : (ν.ψ ^ ν.μ).natDegree = ν.μ * ν.g := by
      rw [ν.hψmonic.natDegree_pow, ν.hψdeg]
    have hdegR : ν.Ranch.natDegree ≤ ν.wSide / ν.e := by
      rw [ν.hRanch]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      simp only [Finset.mem_range] at hk
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      omega
    have hμg : ν.μ * ν.g ≤ ν.wSide / ν.e := by
      rw [← hdegpow]; exact hdvd.trans hdegR
    have hediv : ν.e * (ν.wSide / ν.e) = ν.wSide := Nat.mul_div_cancel' ν.hEdvd
    have hμeg : ν.μ * ν.e * ν.g ≤ ν.wSide := by
      calc ν.μ * ν.e * ν.g = ν.e * (ν.μ * ν.g) := by ring
        _ ≤ ν.e * (ν.wSide / ν.e) := Nat.mul_le_mul le_rfl hμg
        _ = ν.wSide := hediv
    show ν.μ * (ν.e * ν.g * ν.Dwidth) ≤ ν.wSide * ν.Dwidth
    calc ν.μ * (ν.e * ν.g * ν.Dwidth) = (ν.μ * ν.e * ν.g) * ν.Dwidth := by ring
      _ ≤ ν.wSide * ν.Dwidth := Nat.mul_le_mul hμeg le_rfl
  -- MAIN: DOM on the recorded lines, by induction on the top index.
  have key : ∀ (I : ℕ) (hI : I < H.nodes.length) (J : ℕ) (hJI : J ≤ I) (c : ℕ)
      (hc : c < (H.nodes[I]'hI).μ * (H.nodes[I]'hI).childWidth),
      (H.nodes[J]'(by omega)).line.at c ≤ (H.nodes[I]'hI).line.at c := by
    intro I
    induction I with
    | zero =>
      intro hI J hJI c hc
      obtain rfl := Nat.le_zero.mp hJI
      exact le_rfl
    | succ k ih =>
      intro hI J hJI c hc
      rcases eq_or_lt_of_le hJI with rfl | hlt
      · exact le_rfl
      · have hJk : J ≤ k := Nat.lt_succ_iff.mp hlt
        have hstepk := hstep k hI
        have hE := hstepk.2.2.2.2.1        -- window: s0'+wSide' ≤ μ_k
        have hF := hstepk.2.2.2.2.2.1      -- width chain: Dwidth' = childWidth_k
        have hG := hstepk.2.2.2.2.2.2      -- steepness: slope_k < slope_{k+1}
        have hta := hreal k hI             -- (NA)+(HV)+(SAE) at the appended read
        -- the read's interior sits left of the anchor j*·childWidth_k
        have hcB : c < ((H.nodes[k+1]'hI).s0 + (H.nodes[k+1]'hI).wSide) * (H.nodes[k]'(by omega)).childWidth := by
          calc c < (H.nodes[k+1]'hI).μ * (H.nodes[k+1]'hI).childWidth := hc
            _ ≤ (H.nodes[k+1]'hI).wSide * (H.nodes[k+1]'hI).Dwidth := widthConfine _
            _ ≤ ((H.nodes[k+1]'hI).s0 + (H.nodes[k+1]'hI).wSide) * (H.nodes[k]'(by omega)).childWidth := by
                rw [hF]; exact Nat.mul_le_mul (Nat.le_add_left _ _) le_rfl
        -- the affine step: parent line ≤ current line on the interior
        have hstepline : (H.nodes[k]'(by omega)).line.at c ≤ (H.nodes[k+1]'hI).line.at c := by
          refine crossing (H.nodes[k]'(by omega)).line (H.nodes[k+1]'hI).line
            (((H.nodes[k+1]'hI).s0 + (H.nodes[k+1]'hI).wSide) * (H.nodes[k]'(by omega)).childWidth)
            hG ?_ c hcB.le
          rcases lt_or_eq_of_le hE with hlt' | heq'
          · -- non-adjacent: (SAE) span clause at the endpoint j* is STRICT
            exact (hta.2.2.1 ((H.nodes[k+1]'hI).s0 + (H.nodes[k+1]'hI).wSide)
              (Nat.le_add_right _ _) (le_refl _) hlt').le
          · -- adjacent: (SAE) vertex-equality clause
            rw [heq']
            exact (hta.2.2.2 heq').symm.le
        -- the interior nests inside node k's interior, so the IH applies at k
        have hck : c < (H.nodes[k]'(by omega)).μ * (H.nodes[k]'(by omega)).childWidth :=
          lt_of_lt_of_le hcB (Nat.mul_le_mul hE le_rfl)
        exact (ih (by omega) J hJk c hck).trans hstepline
  exact key i hi j hij b hb

end LeanUrat.MovesC
