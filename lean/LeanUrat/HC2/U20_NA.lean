/-
Unit U20.readsOf_NA  (HC-2 campaign, E-phase — blueprint §5 Layer D; PRE-SPLIT per §9 F-2)
moves_ref: §C C.0 (NA) display; C.3 "the classifier reads actual hull sides".
deps: D4 (SideReads(i)), hull convexity (Moves L2_widthBound/L2_strideRule + line
arithmetic).  difficulty: medium-hard.  hypothesis_fields: none.
sketch: the new side is a lower hull edge of the CHILD development whose window ends
strictly left of the standing vertex; strict convexity of the hull at the vertex + the
side's minimality give the strict gap at base index μ·D.

RESTATED-AS-ASSEMBLY per §9 F-2 (2026-07-28; statement BYTE-UNCHANGED — the assembled
unit is normative; no fence event, the U9/U10 pre-split precedent, census +3). The fleet
escalation reduced (NA) to the cross-frame VERTEX-VALUE TRANSPORT, one lemma per PARENT
species (the transport routes through the species-specific transition clause):
  U20a `NA_transport_root` (U20a_NAtransportRoot.lean) — parent = the root read;
  U20b `NA_transport_increment` (U20b_NAtransportIncrement.lean) — parent an increment;
  U20c `NA_transport_recentering` (U20c_NAtransportRecentering.lean) — parent a
    recentering.
ASSEMBLY PLAN = parent-species trichotomy (`ReadSpecies` has exactly root/increment/
recentering) + the three transports + SideReads(i+1)'s clause-(i) strict-above reading at
the OFF-SPAN vertex: under `hna` (`s0'+wSide' < μ`) the vertex slot μ is off the child's
span, so clause (i)'s equality case is unreachable and `gam < e'·σ'.w(B μ) + μ·h'`
strictly; the γ-tie + slope law (coherence) convert that to `new-line.at(μ·D') <
absW(B μ)`, and the transport identifies `absW(B μ)` with the OLD line's vertex value —
the strict gap. The fleet-round chain was report-side; the assigned prover reconciles the
exact sub-lemma statements against F-2's semantic spec and records them in-file (the
sub-lemma statements are prover-refinable; THIS assembled statement is not).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U20a_NAtransportRoot
import LeanUrat.HC2.U20b_NAtransportIncrement
import LeanUrat.HC2.U20c_NAtransportRecentering

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (NA) for runs: at a non-adjacent consecutive read of a run, the pinned old vertex
lies STRICTLY ABOVE the extended new line (the (NA) conjunct of
`TransitionAdmissible`, extracted).

⚠ VACUITY CAVEAT (2026-07-30 verify-2 fold-in; task #44 / A16+A39): this assembly
INHERITS the K1-kernel perimeter through U20a/U20b — the kernel's non-recentering
legs at `e·g ≥ 2` close via the V10 INCONSISTENCY finding (`ReadsOf` admits NO such
instances; the `HistoryCoherent` read-pair keying is a flagged FAITHFULNESS BUG,
pending sign-off task #44), so this theorem is currently VACUOUS at that steep
perimeter. Never cite it as machine-checked transport mathematics there. -/
theorem readsOf_NA {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hna : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      < (H.nodes[i]'(by omega)).μ) :
    (H.nodes[i+1]'hi1).line.at
        ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)
      < (H.nodes[i]'(by omega)).line.at
        ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  -- Assembly (F-2): trichotomy on `(H.nodes[i]).species`, apply
  -- `NA_transport_root` / `NA_transport_increment` / `NA_transport_recentering`
  -- to `ReadsOf`'s frame-(i+1) development of f, then SideReads(i+1) clause (i)
  -- at the off-span vertex slot μ.
  have hi0 : i < H.nodes.length := by omega
  -- canonicalize the parent-node proof term to `hi0`
  show (H.nodes[i+1]'hi1).line.at ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
    < (H.nodes[i]'hi0).line.at ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
  -- (NA) at read i+1 in `hi0` form of the window guard
  have hna0 : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide < (H.nodes[i]'hi0).μ := hna
  -- ReadsOf's frame-(i+1) development of f + its SideReads bundle
  obtain ⟨B, Nd, Φnext, hdev, hΦ, hSR⟩ := h.2.2.2 (i+1) hi1
  -- enlarge the development length so the standing vertex μ is in range for the transport
  set Nd2 := max Nd ((H.nodes[i]'hi0).μ + 1) with hNd2def
  have hdev' : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd2 := by
    refine ⟨hdev.1, ?_, ?_⟩
    · exact fun j hj => hdev.2.1 j (by omega)
    · rw [hdev.2.2]
      refine Finset.sum_subset (fun x hx => ?_) ?_
      · rw [Finset.mem_range] at hx ⊢; omega
      · intro x _ hxns
        rw [Finset.mem_range, not_lt] at hxns
        rw [hdev.2.1 x hxns, zero_mul]
  have hNd' : (H.nodes[i]'hi0).μ < Nd2 := by omega
  -- the cross-frame vertex-value transport, by parent-species trichotomy
  have htransfull : B ((H.nodes[i]'hi0).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'hi0).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ)
          * (H.nodes[i]'hi0).line.at ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth) := by
    rcases hspv : (H.nodes[i]'hi0).species with _ | _ | _
    · exact NA_transport_root h i hi1 hspv B Nd2 hdev' hNd'
    · exact NA_transport_increment h i hi1 hspv B Nd2 hdev' hNd'
    · exact NA_transport_recentering h i hi1 hspv B Nd2 hdev' hNd'
  obtain ⟨hBμ_ne, htrans⟩ := htransfull
  -- recover μ < Nd (original) from the transported nonvanishing of the vertex coefficient
  have hμNd : (H.nodes[i]'hi0).μ < Nd :=
    not_le.mp (fun hc => hBμ_ne (hdev.2.1 _ hc))
  -- SideReads(i+1) clause (i): the read functional at the OFF-SPAN vertex slot is STRICT
  have hle := hSR.1.1 ((H.nodes[i]'hi0).μ) hμNd hBμ_ne
  have hstrict : (H.nodes[i+1]'hi1).gam
      < ((H.nodes[i+1]'hi1).e : ℤ) * (H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'hi0).μ))
        + ((H.nodes[i]'hi0).μ : ℤ) * ((H.nodes[i+1]'hi1).h : ℤ) := by
    refine lt_of_le_of_ne hle (fun heq => ?_)
    obtain ⟨k, hk, hjk, _⟩ := hSR.1.2 ((H.nodes[i]'hi0).μ) hμNd hBμ_ne heq.symm
    have hek : (H.nodes[i+1]'hi1).e * k ≤ (H.nodes[i+1]'hi1).wSide := by
      calc (H.nodes[i+1]'hi1).e * k
            ≤ (H.nodes[i+1]'hi1).e * ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e) :=
              Nat.mul_le_mul (le_refl _) hk
        _ = (H.nodes[i+1]'hi1).wSide := Nat.mul_div_cancel' (H.nodes[i+1]'hi1).hEdvd
    omega
  -- cast the strict read inequality to ℚ
  have hSide : ((H.nodes[i+1]'hi1).gam : ℚ)
      < ((H.nodes[i+1]'hi1).e : ℚ) * ((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'hi0).μ)) : ℚ)
        + ((H.nodes[i]'hi0).μ : ℚ) * ((H.nodes[i+1]'hi1).h : ℚ) := by exact_mod_cast hstrict
  -- coherence: absolute-scale slope law + γ-tie at read i+1, and the width chain D' = childWidth
  have hSlope := h.2.2.1.2.1 (i+1) hi1
  have hGam := h.2.2.1.2.2.1 (i+1) hi1
  have hDcwN : (H.nodes[i+1]'hi1).Dwidth = (H.nodes[i]'hi0).childWidth :=
    (h.2.2.1.2.2.2 i hi1).2.2.2.2.2.1
  have hDeq : ((H.nodes[i]'hi0).childWidth : ℚ) = ((H.nodes[i+1]'hi1).Dwidth : ℚ) := by
    exact_mod_cast hDcwN.symm
  -- positivity of the stretch and the read multiplicity
  have hSposN : 0 < H.strFrame (i+1) := by
    apply List.prod_pos
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨R', _, rfl⟩ := hx
    exact R'.he
  have hSpos : (0 : ℚ) < (H.strFrame (i+1) : ℚ) := by exact_mod_cast hSposN
  have hepos : (0 : ℚ) < ((H.nodes[i+1]'hi1).e : ℚ) := by exact_mod_cast (H.nodes[i+1]'hi1).he
  have hpos : (0 : ℚ) < ((H.nodes[i+1]'hi1).e : ℚ) * (H.strFrame (i+1) : ℚ) := mul_pos hepos hSpos
  -- STEP B: the new line at the vertex base, scaled by e'·STR', equals gam' − μ·h'
  have hA : (H.nodes[i+1]'hi1).line.at ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
        * (((H.nodes[i+1]'hi1).e : ℚ) * (H.strFrame (i+1) : ℚ))
      = ((H.nodes[i+1]'hi1).gam : ℚ)
        - ((H.nodes[i]'hi0).μ : ℚ) * ((H.nodes[i+1]'hi1).h : ℚ) := by
    have hLU := (H.nodes[i+1]'hi1).hLineU
    simp only [Line.at] at hLU ⊢
    push_cast at hSlope hGam hLU ⊢
    rw [hDeq]
    linear_combination
      ((((H.nodes[i+1]'hi1).s0 : ℚ) + ((H.nodes[i+1]'hi1).wSide : ℚ))
          - ((H.nodes[i]'hi0).μ : ℚ)) * hSlope
      - hGam
      + (((H.nodes[i+1]'hi1).e : ℚ) * (H.strFrame (i+1) : ℚ)) * hLU
  -- the old line at the vertex base, scaled the same, equals e'·(vertex weight)
  have hB : (H.nodes[i]'hi0).line.at ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
        * (((H.nodes[i+1]'hi1).e : ℚ) * (H.strFrame (i+1) : ℚ))
      = ((H.nodes[i+1]'hi1).e : ℚ)
        * ((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'hi0).μ)) : ℚ) := by
    rw [htrans]; ring
  -- combine: the scaled strict gap descends to the unscaled one
  have key : (H.nodes[i+1]'hi1).line.at ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
        * (((H.nodes[i+1]'hi1).e : ℚ) * (H.strFrame (i+1) : ℚ))
      < (H.nodes[i]'hi0).line.at ((H.nodes[i]'hi0).μ * (H.nodes[i]'hi0).childWidth)
        * (((H.nodes[i+1]'hi1).e : ℚ) * (H.strFrame (i+1) : ℚ)) := by
    rw [hA, hB]; linarith [hSide]
  exact lt_of_mul_lt_mul_right key (le_of_lt hpos)

end LeanUrat.MovesJ
