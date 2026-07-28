/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V4_readLanding
import LeanUrat.HC2.K1_vertexPin

/-!
# HC1.V9_K1nonrec — HC2's K1 kernel residual via the ReadFrame (blueprint §10, V9)

V′-KERNEL unit (blueprint §10.1), the REGRADE instance's payoff: HC2's
`K1_readVertexPin_nonrec` (the ONE remaining HC2 kernel sorry) as a corollary of
the V1–V4 chain.  Assembly route (§10.1 V9, steps (i)–(vi)):

 (i)  extract the read steepness from `HistoryCoherent` (slope law + strict
      steepening → `ν.h > ν.e·σ.h` — the `ReadPair` hypothesis; the short lemma
      `V9_readSteepness` below covers reads with a predecessor; the ROOT read's
      steepness comes from the recorded side data — P-phase);
 (ii) build the `ReadFrame` at (ν.e, ν.h) on σ_i (V1/V2);
 (iii) the recorded `IsNodeLift = IsReadLift` (`isNodeLift_iff`) is V3's
      standard-lift shape — K1(Φ̂/wV) + D.8 at the frame (V4);
 (iv) f's ReadFrame residual IS the recorded side pattern:
      `RV(f) = Σ_k C(pat k)·T(…)` from SideReads (i)+(ii) (the side line
      supports the development with equality exactly at the stride digits — so
      `wV(f) = ν.gam`, attained); its anchor/ord data
      `HasAnchorK (RV f) a★ (pattern-Ranch)` DERIVED from (i)+(ii);
      `ord_ψ(pattern) = ν.μ` read against SideReads (iii) — SEAM, see below;
 (v)  V4's (VERTEX) gives `B_μ ≠ 0` and `wV(B_μ) = gam − μ·ν.e·g·ν.h`, then
      `σ′.w(B_μ) = ν.e·σ.w(B_μ) = wV(B_μ)` via the RECORDED
      child_wPrev/hStretch on the ONE coefficient (no tower reconciliation —
      the kernel's conclusion touches only a child COEFFICIENT's weight);
 (vi) the ℚ-conversion to `STR_{i+1}·line.at(μ·childWidth)` is the γ-tie +
      slope-law arithmetic already PROVED in-file at HC2
      (`K1_SAE_vertexEq_endpoint`'s pattern).

⚠ **SIDEREADS-(iii) ADJUDICATION — THE STANDING E-PHASE FLAG, FENCED** (verbatim
from §10.1 V9): SideReads clause (iii) anchors `σ.R f` — the FRAME residual —
while the landing needs the READ residual `RV(f)`'s ψ-order.  At single-side
reads they agree; at multi-side polygons the frame residual sees the WRONG
slots.  The faithful object is `RV(f)` (§C's side data are side-local); the
DERIVED pattern-anchor route above consumes only (i)+(ii)+the recorded μ, so V9
keys ord_ψ to the PATTERN and treats (iii)'s `σ.R f` rendering as the
U31-gated seam it already is.  **If the gate shows the recorded μ
mis-associates on some run shape, THAT restatement (SideReads (iii) →
RV-vocabulary) is a NEW sign-off item — flagged now, not silently changed.**
This unit does NOT touch `SideReads`.

deps: V1–V4 + the HC2 records. difficulty: medium (assembly).
UNBLOCKS: `K1_readVertexPin` total (close `K1_readVertexPin_nonrec` by `exact`)
→ U20a/U20b/U22-E2 close by the staged one-line consumers.
E-phase: statements per §10.1, `sorry` bodies.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesJ

/-- V9 step (i): the READ STEEPNESS at any read with a predecessor — from
`HistoryCoherent`'s slope law + strict steepening,
`h_i > h_{i−1}·e_i·e_{i−1}·g_{i−1} ≥ e_i·h_{i−1} = e_i·σ_i.h` — the `ReadPair`
steepness hypothesis of the regrade at (ν.e, ν.h) over ν.σ. -/
theorem V9_readSteepness {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi : i < H.nodes.length) (hi0 : 1 ≤ i)
    (hsp : (H.nodes[i]'hi).species ≠ ReadSpecies.recentering) :
    ((H.nodes[i]'hi).e : ℤ) * ((H.nodes[i]'hi).σ.h : ℤ)
      < ((H.nodes[i]'hi).h : ℤ) := by
  sorry

/-- Unit V9: the K1 kernel residual — `K1_readVertexPin_nonrec`'s statement
VERBATIM, proved through the ReadFrame chain (route (i)–(vi) in the header).
Once landed, `K1_readVertexPin_nonrec` closes by
`exact V9_K1nonrec h i hi1 hsp B Nd hdev hNd`. -/
theorem V9_K1nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V9_readSteepness
#print axioms LeanUrat.HC1.V9_K1nonrec
