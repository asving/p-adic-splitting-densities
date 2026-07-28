/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.V4_readLanding
import LeanUrat.HC1.V10_transportWindow
import LeanUrat.HC2.Defs

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

**REV-2 NOTE (escalation round, 2026-07-28, post-V2/V4 landing)**: route (v)'s
"hStretch on the ONE coefficient" justification above is INVALID as written — the
vertex coefficient can have `deg σ.Φ ≤ deg (B μ) < deg σ'.Φ`, where `V.hStretch`
does not apply and no general identity ties `wV` to `ν.e·σ.w` (they differ at
`x = σ.Φ` on C_{Φ̂} itself).  Flagged per the ⚠ discipline, not silently changed.
See the REV-2 obstruction record at the `sorry`: R3a (anchor transport — now fully
spec'd and derivable WITHOUT touching SideReads(iii)), R3b (the grading bridge =
the one remaining hard core, B2-FINAL's carry composition), R3c (the root
`e·g = 1` corner).  PROVED this round, supporting step (i)/(v):
`V9_transSteepness`, `V9_readPair`, `V9_wvGeStretch`.

**REV-4 NOTE (V10 transcription round, 2026-07-28)**: the (TRANSPORT)-upward
transcription (`V10_transportWindow.lean`) LANDED — and its finding SUPERSEDES the
REV-3 route.  Transcribing the forced-window clause against the recorded transition
(the only *actual-data* carrier in scope) proves, Lean-core
(`V10_forcedKeyWeight` / `V10_readTransition_incompatible`): **the recorded
non-recentering read transition is CONTRADICTORY whenever `ν.e·ν.g ≥ 2`** — the
child-stage laws force `ν.h = ν.e²·ν.g·σ.h` (hence `ν.e = 1, ν.t = 0, ν.s = 1`),
and then `σ′.R Φ̂ = T 1` (hRΦ + the recorded `σ′.s = ν.s` tie) clashes with
`σ′.R Φ̂ = C(c^g)·T 0` (hRlt/hRmul/hS5′ through the read lift).  Consequences:
(a) R3a/R3b are MOOT at every read this kernel's hard legs concerned — the
    perimeter is EMPTY, and `V9_K1nonrec` closes there BY CONTRADICTION (below);
    this is loudly NOT transport mathematics — see V10's header;
(b) the ONE remaining leg is the R3c corner `i = 0 ∧ ν.e·ν.g = 1` (records
    consistent there; the honest g = 1 landing needs the parent's D.1(b) tie laws
    (StageCore-grade, unrecorded) or SideReads(iii) — the fenced seam, which at
    single-side reads is exactly where it would be faithful).  The corner `sorry`
    below is the kernel's entire remaining obligation;
(c) `HistoryCoherent`'s round-3 keying of `TransitionCoreL` at the READ pair on the
    READ lift is a FAITHFULNESS BUG (genuine steep increments cannot be recorded:
    the faithful child weighs `Φ̂ ↦ e★·(e★h★g)`, the regraded side value, not `h★`)
    — a NAMED SIGN-OFF ITEM, not silently changed.  U31's gate (single-node) never
    probed a 2-node instance, which is why this went unseen.

**REV-3 NOTE (carry-bridge escalation round, 2026-07-28)**: R3b adjudicated.  The
reduction is PROVED in-file, Lean-core (`V9_wvEqStretch_of_bottomSlot` /
`V9_bottomSlot_of_wvEqStretch` + the seed `V9_steepSide_frameDescent`): R3b ⟺ the
BOTTOM-WINDOW LAW at the vertex coefficient.  A sympy-verified countermodel
(f = (X+8)(Φ̂²+8X³) at the (1,1)-Gauss frame, read pair (1,2)) shows R3b is NOT
derivable from the ⚠-clean pool — SideReads(i)/(ii)/(vi) + hOrd + the V-frame engine —
and that clause (vi) carries no weight content.  The one display that supplies the
bottom-window law is §B2-DEF D.8-(TRANSPORT)'s upward FORCED-WINDOW clause (MOVES
2521–2528), which blueprint §10.1 fenced OUT of V4 as "not needed" — that fencing is
WRONG for V9 (the campaign finding on B2-FINAL).  Full record at the `sorry` (REV-3
block); R3c unchanged.

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

section V9SteepHelpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0`. -/
private lemma w_one_helper (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; omega

/-- `w (-x) = w x`. -/
private lemma w_neg_helper (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.w (-x) = σ.w x := by
  have hn1 : σ.w (-1) = 0 := by
    have h := σ.hwmul (-1) (-1) (by norm_num) (by norm_num)
    rw [neg_mul_neg, one_mul, w_one_helper σ] at h; omega
  have h := σ.hwmul (-1) x (by norm_num) hx
  rw [neg_one_mul] at h
  rw [h, hn1, zero_add]

/-- The accumulated stretch is positive (every read has `1 ≤ e`) — private copy of
the HC2 `K1Helpers` lemma (the import was reversed at REV-4: HC2/K1_vertexPin now
consumes THIS file, per the recorded delegation). -/
private lemma v9_strFrame_pos (H : History p F) (i : ℕ) : 0 < H.strFrame i := by
  unfold History.strFrame
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rw [List.prod_eq_zero_iff] at h0
  obtain ⟨ν, -, hν0⟩ := List.mem_map.mp h0
  exact absurd hν0.symm (by have := ν.he; omega)

/-- `strFrame` recursion: `STR_{k+1} = STR_k · e_k`. -/
private lemma v9_strFrame_succ (H : History p F) (k : ℕ) (hk : k < H.nodes.length) :
    H.strFrame (k + 1) = H.strFrame k * (H.nodes[k]'hk).e := by
  unfold History.strFrame
  rw [List.take_succ, List.getElem?_eq_getElem hk]
  simp only [List.map_append, List.prod_append, Option.toList_some, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- **Recentering preserves the stage slope numerator `h`.** A recentering replaces the key
by `Φ' = Φ − tt` where `w(tt) = w(Φ) = h`; the leading residuals `R Φ = z^{s}` (with `s = 1`
at `e = 1`) and `R tt = c·z^{0}` sit at DISTINCT positions, so there is no valuation jump and
`w(Φ − tt) = w Φ`.  Hence `σ'.h = σ.h`.  (Pure `Stage` fact; needs only `IsRecenteringCore`.) -/
private lemma v9_recenter_h_eq {σ σ' : Stage p F} {cc : ↥σ.K} {tt : Polynomial ℤ_[p]}
    (hrec : IsRecenteringCore σ σ' cc tt) : (σ'.h : ℤ) = (σ.h : ℤ) := by
  obtain ⟨he1, he1', hccne, hinC, htne, htw, htR, hΦ', hw', hwPrev', hKeq, hFQeq, hWSeq,
    hdig'⟩ := hrec.base
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hdeglt : tt.degree < σ.Φ.degree := hinC
  have hsubne : σ.Φ - tt ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at hdeglt; exact (lt_irrefl _) hdeglt
  have hs1 : σ.s = 1 := by
    have ht0 := σ.he1t he1
    have hb := σ.hbez
    rw [he1, ht0] at hb; push_cast at hb; linarith
  have hwtt : σ.w tt = (σ.h : ℤ) := by rw [htw, σ.hwΦ]
  have hwΦh : σ.w σ.Φ = (σ.h : ℤ) := σ.hwΦ
  have hkey : σ.w (σ.Φ - tt) = (σ.h : ℤ) := by
    have hge : (σ.h : ℤ) ≤ σ.w (σ.Φ - tt) := by
      have hult := σ.hwult σ.Φ (-tt) hΦne (neg_ne_zero.mpr htne)
        (by rw [← sub_eq_add_neg]; exact hsubne)
      rw [w_neg_helper σ tt htne, hwtt, hwΦh, min_self, ← sub_eq_add_neg] at hult
      exact hult
    rcases lt_or_eq_of_le hge with hlt | heq
    · exfalso
      have hlt' : σ.w tt < σ.w (σ.Φ - tt) := by rw [hwtt]; exact hlt
      have hsum : tt + (σ.Φ - tt) = σ.Φ := by ring
      have hRe := σ.hRlt tt (σ.Φ - tt) htne hsubne (by rw [hsum]; exact hΦne) hlt'
      rw [hsum, σ.hRΦ, htR, hs1] at hRe
      have hRe2 : LaurentPolynomial.C (1 : ↥σ.K) * LaurentPolynomial.T (1 : ℤ)
          = LaurentPolynomial.C cc * LaurentPolynomial.T (0 : ℤ) := by
        rw [map_one, one_mul]; exact hRe
      rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at hRe2
      have h' : (Finsupp.single (1 : ℤ) (1 : ↥σ.K)) = Finsupp.single 0 cc := hRe2
      have hc := DFunLike.congr_fun h' 1
      rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
        if_neg (by norm_num : ¬ (0 : ℤ) = 1)] at hc
      exact one_ne_zero hc
    · exact heq.symm
  have hres : σ.w (σ.Φ - tt) = (σ'.h : ℤ) := by
    have h := σ'.hwΦ
    rw [hΦ', hw' (σ.Φ - tt)] at h
    exact h
  rw [hres] at hkey
  exact hkey

/-- **The read steepness, for EVERY read with a predecessor** (the (I-aug) at the read scale):
`e_i·σ_i.h < h_i` for all `1 ≤ i < len`, whatever the species of `i` — a strong induction over
the recentering chain.  At a NON-recentering predecessor `TransitionCoreL.child_h` gives
`σ_i.h = h_{i−1}`; at a RECENTERING predecessor `v9_recenter_h_eq` gives `σ_i.h = σ_{i−1}.h` and
the strict inductive hypothesis bounds it.  In both cases the slope law + strict steepening
(`slope_{i−1} < slope_i`) + the width chain close the ℚ inequality. -/
private lemma v9_readSteep_all (H : History p F) (hcoh : HistoryCoherent H) :
    ∀ i, 1 ≤ i → ∀ hi : i < H.nodes.length,
      ((H.nodes[i]'hi).e : ℤ) * ((H.nodes[i]'hi).σ.h : ℤ) < ((H.nodes[i]'hi).h : ℤ) := by
  obtain ⟨hroot, hslope, hgam, htrans⟩ := hcoh
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi1 hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j < H.nodes.length := by omega
    set νj : Node p F := H.nodes[j]'hj with hνjdef
    set νi : Node p F := H.nodes[j + 1]'hi with hνidef
    obtain ⟨hrecC, hnrecC, hseq, hteq, hwin, hDweq, hsteep⟩ := htrans j hi
    -- slope laws in ℚ
    have hSLi := hslope (j + 1) hi
    have hSLj := hslope j hj
    rw [← hνidef] at hSLi
    rw [← hνjdef] at hSLj
    -- strFrame recursion
    have hSTR : (H.strFrame (j + 1) : ℚ) = (H.strFrame j : ℚ) * (νj.e : ℚ) := by
      rw [v9_strFrame_succ H j hj, ← hνjdef]; push_cast; ring
    -- Dwidth chain, as ℚ
    have hDw : (νi.Dwidth : ℚ) = (νj.e : ℚ) * (νj.g : ℚ) * (νj.Dwidth : ℚ) := by
      have := hDweq
      rw [← hνidef, ← hνjdef] at this
      rw [this]; show ((νj.e * νj.g * νj.Dwidth : ℕ) : ℚ) = _; push_cast; ring
    rw [← hνidef, ← hνjdef] at hsteep
    -- positivity facts
    have hejpos : (0 : ℚ) < (νj.e : ℚ) := by exact_mod_cast νj.he
    have heipos : (0 : ℚ) < (νi.e : ℚ) := by exact_mod_cast νi.he
    have hgjpos : (0 : ℚ) < (νj.g : ℚ) := by exact_mod_cast νj.hg
    have hDjpos : (0 : ℚ) < (νj.Dwidth : ℚ) := by
      have := νj.σ.hdeg; rw [νj.hDwidth]; exact_mod_cast this
    have hSjpos : (0 : ℚ) < (H.strFrame j : ℚ) := by exact_mod_cast v9_strFrame_pos H j
    have hhipos : (0 : ℚ) < (νi.h : ℚ) := by exact_mod_cast νi.hh
    -- slope positivity of `j`
    have hsjpos : (0 : ℚ) < νj.line.slope := by
      have hpos : (0 : ℚ) < (νj.e : ℚ) * (H.strFrame j : ℚ) * (νj.Dwidth : ℚ) := by positivity
      have hhjpos : (0 : ℚ) < (νj.h : ℚ) := by exact_mod_cast νj.hh
      nlinarith [hSLj, hpos, hhjpos]
    -- reduce the goal to ℚ
    rw [show ((νi.e : ℤ) * (νi.σ.h : ℤ) < (νi.h : ℤ))
        ↔ ((νi.e : ℚ) * (νi.σ.h : ℚ) < (νi.h : ℚ)) by
      constructor <;> intro h <;> exact_mod_cast h]
    by_cases hjrec : νj.species = ReadSpecies.recentering
    · -- RECENTERING predecessor
      have hrc := hrecC hjrec
      have hσih : (νi.σ.h : ℚ) = (νj.σ.h : ℚ) := by
        have := v9_recenter_h_eq hrc; exact_mod_cast this
      obtain ⟨hej1, hgj1⟩ := νj.hspecRec hjrec
      have hej1' : (νj.e : ℚ) = 1 := by rw [hej1]; norm_num
      have hgj1' : (νj.g : ℚ) = 1 := by rw [hgj1]; norm_num
      -- j ≥ 1 (node 0 is the root, never a recentering)
      have hjpos : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · exfalso
          apply absurd hjrec
          rw [hνjdef, (H.root_iff j hj).mpr hj0]
          decide
        · exact hj0
      have hIH := IH j (by omega) hjpos hj
      rw [← hνjdef] at hIH
      -- IH : e_j·σ_j.h < h_j ; with e_j = 1 : σ_j.h < h_j  (in ℤ, cast to ℚ)
      have hIHq : (νj.σ.h : ℚ) < (νj.h : ℚ) := by
        have : ((νj.e : ℤ) * (νj.σ.h : ℤ) < (νj.h : ℤ)) := hIH
        have hcast : (νj.e : ℚ) * (νj.σ.h : ℚ) < (νj.h : ℚ) := by exact_mod_cast this
        rw [hej1', one_mul] at hcast; exact hcast
      rw [hσih]
      -- h_j = slope_j · STR_j · Dwidth_j ; h_i = slope_i · e_i · STR_j · Dwidth_j
      rw [hSTR, hej1', mul_one] at hSLi
      rw [hej1', one_mul] at hSLj
      rw [hDw, hej1', hgj1', one_mul, one_mul] at hSLi
      have hP : (0 : ℚ) < (νi.e : ℚ) * (H.strFrame j : ℚ) * (νj.Dwidth : ℚ) := by positivity
      have hhj : (νj.h : ℚ) = νj.line.slope * ((H.strFrame j : ℚ) * (νj.Dwidth : ℚ)) := by
        rw [← hSLj]
      have hhi : (νi.h : ℚ)
          = νi.line.slope * ((νi.e : ℚ) * (H.strFrame j : ℚ) * (νj.Dwidth : ℚ)) := by
        rw [← hSLi]
      have step1 : (νi.e : ℚ) * (νj.σ.h : ℚ) < (νi.e : ℚ) * (νj.h : ℚ) :=
        mul_lt_mul_of_pos_left hIHq heipos
      have step2 : (νi.e : ℚ) * (νj.h : ℚ) < (νi.h : ℚ) := by
        rw [hhj, hhi]
        nlinarith [mul_lt_mul_of_pos_left hsteep hP]
      linarith [step1, step2]
    · -- NON-RECENTERING predecessor: σ_i.h = h_j
      obtain ⟨hlift, htcore⟩ := hnrecC hjrec
      have hσih : (νi.σ.h : ℚ) = (νj.h : ℚ) := by exact_mod_cast htcore.base.child_h
      rw [hσih]
      -- substitute the width/strFrame chains
      rw [hSTR, hDw] at hSLi
      have hsipos : (0 : ℚ) < νi.line.slope := lt_trans hsjpos hsteep
      have hegge1 : (1 : ℚ) ≤ (νj.e : ℚ) * (νj.g : ℚ) := by
        have h1 : (1 : ℚ) ≤ (νj.e : ℚ) := by exact_mod_cast νj.he
        have h2 : (1 : ℚ) ≤ (νj.g : ℚ) := by exact_mod_cast νj.hg
        nlinarith [h1, h2]
      have hkeyslope : νj.line.slope < νi.line.slope * ((νj.e : ℚ) * (νj.g : ℚ)) := by
        calc νj.line.slope < νi.line.slope := hsteep
          _ = νi.line.slope * 1 := (mul_one _).symm
          _ ≤ νi.line.slope * ((νj.e : ℚ) * (νj.g : ℚ)) :=
              mul_le_mul_of_nonneg_left hegge1 (le_of_lt hsipos)
      have hQ : (0 : ℚ) < (νi.e : ℚ) * (νj.e : ℚ) * (H.strFrame j : ℚ) * (νj.Dwidth : ℚ) := by
        positivity
      have hhj : (νj.h : ℚ)
          = νj.line.slope * ((νj.e : ℚ) * (H.strFrame j : ℚ) * (νj.Dwidth : ℚ)) := hSLj.symm
      -- goal: e_i · h_j < h_i
      rw [hhj, ← hSLi]
      nlinarith [mul_lt_mul_of_pos_left hkeyslope hQ]

/-- `w (x^n) = n·w x` (iterated `hwmul`; pure `Stage` fact). -/
private lemma w_pow_helper (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.w (x ^ n) = (n : ℤ) * σ.w x := by
  induction n with
  | zero => rw [pow_zero, w_one_helper σ]; push_cast; ring
  | succ k ih =>
      rw [pow_succ, σ.hwmul _ _ (pow_ne_zero k hx) hx, ih]
      push_cast; ring

/-- The STRICT ultrametric law, DERIVED from `hwmul`/`hwult` alone (no `StageCore` needed):
`w f < w g → w (f + g) = w f` — the two-sided min trick on `f = (f + g) + (−g)`. -/
private lemma w_strict_helper (σ : Stage p F) (f g : Polynomial ℤ_[p])
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) (hlt : σ.w f < σ.w g) :
    σ.w (f + g) = σ.w f := by
  have h1 := σ.hwult f g hf hg hfg
  have hsum : (f + g) + (-g) = f := by ring
  have h2 := σ.hwult (f + g) (-g) hfg (neg_ne_zero.mpr hg) (by rw [hsum]; exact hf)
  rw [hsum, w_neg_helper σ g hg] at h2
  omega

/-- Finite-sum ultrametric lower bound: if every nonzero summand has `w ≥ c` and the sum
is nonzero, then `w (Σ) ≥ c`. -/
private lemma w_sum_ge_helper (σ : Stage p F) (S : Finset ℕ) (f : ℕ → Polynomial ℤ_[p])
    (c : ℤ) :
    (∀ k ∈ S, f k ≠ 0 → c ≤ σ.w (f k)) → (∑ k ∈ S, f k) ≠ 0 →
    c ≤ σ.w (∑ k ∈ S, f k) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro _ hne; simp at hne
  | @insert a S' ha ih =>
      intro hterm hne
      rw [Finset.sum_insert ha] at hne ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hne ⊢
        exact ih (fun k hk hk0 => hterm k (Finset.mem_insert_of_mem hk) hk0) hne
      · by_cases hS' : (∑ k ∈ S', f k) = 0
        · rw [hS', add_zero]
          exact hterm a (Finset.mem_insert_self a S') hfa
        · have h1 := hterm a (Finset.mem_insert_self a S') hfa
          have h2 := ih (fun k hk hk0 => hterm k (Finset.mem_insert_of_mem hk) hk0) hS'
          have h3 := σ.hwult (f a) (∑ k ∈ S', f k) hfa hS' hne
          omega

end V9SteepHelpers

/-- V9 step (i): the READ STEEPNESS at any read with a predecessor — from
`HistoryCoherent`'s slope law + strict steepening,
`h_i > h_{i−1}·e_i·e_{i−1}·g_{i−1} ≥ e_i·h_{i−1} = e_i·σ_i.h` — the `ReadPair`
steepness hypothesis of the regrade at (ν.e, ν.h) over ν.σ. -/
theorem V9_readSteepness {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi : i < H.nodes.length) (hi0 : 1 ≤ i)
    (hsp : (H.nodes[i]'hi).species ≠ ReadSpecies.recentering) :
    ((H.nodes[i]'hi).e : ℤ) * ((H.nodes[i]'hi).σ.h : ℤ)
      < ((H.nodes[i]'hi).h : ℤ) :=
  v9_readSteep_all H hcoh i hi0 hi

/-- **V9 step (i) at the ROOT read, `e·g ≥ 2` (REV 2, escalation round)**: the read
steepness `e·σ.h < h` derived from the RECORDED (i, i+1) transition itself — NO
predecessor needed (`V9_readSteepness` requires `1 ≤ i`).  Mechanism (the "σ'.h is
FORCED via hwΦ" route): the child stage weighs its own key at `σ'.w Φ̂ = σ'.h = ν.h`
(`hwΦ` + `child_h`), while the recorded node lift `Φ̂ = Φ^{eg} + τ` forces
`σ'.w (Φ^{eg}) = eg·(e·σ.h)` through `hStretch`/`child_wPrev`/`child_e` on the parent
key; if steepness FAILED (`h ≤ e·σ.h`) then every τ-slot weighs `σ.w ≥ g·h`, so
`σ'.w τ ≥ e·g·h ≥ 2h > h` and the DERIVED strict law pins `σ'.w (Φ^{eg}) = h`,
forcing `eg·e·σ.h = h ≤ e·σ.h` — impossible at `e·g ≥ 2`.  The corner
`i = 0 ∧ e·g = 1` is genuinely underivable (obstruction record R3c below). -/
theorem V9_transSteepness {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species ≠ ReadSpecies.recentering)
    (hEG : 2 ≤ (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).e
      * (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).g) :
    ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).e : ℤ)
        * ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ.h : ℤ)
      < ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).h : ℤ) := by
  obtain ⟨hroot, hslope, hgam, htrans⟩ := hcoh
  obtain ⟨hrecC, hnrecC, hseq, hteq, hwin, hDweq, hsteepen⟩ := htrans i hi1
  obtain ⟨hliftraw, htcoreraw⟩ := hnrecC hsp
  set ν : Node p F := H.nodes[i]'(Nat.lt_of_succ_lt hi1) with hν
  set ν' : Node p F := H.nodes[i+1]'hi1 with hν'
  have hlift : IsNodeLift ν ν'.σ.Φ := hliftraw
  have htcore : TransitionCoreL ν.σ ν'.σ ν'.σ.Φ ν.e ν.h ν.zbar := htcoreraw
  set σ : Stage p F := ν.σ with hσdef
  set σ' : Stage p F := ν'.σ with hσ'def
  set E : ℕ := ν.e with hE
  set G : ℕ := ν.g with hG
  obtain ⟨tt, htt0, httk, hPhi⟩ := hlift
  have hce : σ'.e = E := htcore.base.child_e
  have hch : σ'.h = ν.h := htcore.base.child_h
  have hcw : ∀ f, σ'.wPrev f = σ.w f := htcore.base.child_wPrev
  by_contra hcon
  push_neg at hcon
  -- hcon : (ν.h : ℤ) ≤ E·σ.h
  have hE1 : 1 ≤ E := ν.he
  have hG1 : 1 ≤ G := ν.hg
  have hh1' : (1 : ℤ) ≤ (ν.h : ℤ) := by exact_mod_cast ν.hh
  have hσh1' : (1 : ℤ) ≤ (σ.h : ℤ) := by exact_mod_cast σ.hh
  have hE1' : (1 : ℤ) ≤ (E : ℤ) := by exact_mod_cast hE1
  have hEG2' : (2 : ℤ) ≤ (E : ℤ) * (G : ℤ) := by exact_mod_cast hEG
  have hΦmon := σ.hmonic
  have hΦne : σ.Φ ≠ 0 := hΦmon.ne_zero
  have hD1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  set D : ℕ := σ.Φ.natDegree with hD
  set τ : Polynomial ℤ_[p] := ∑ k ∈ Finset.range G, tt k * σ.Φ ^ (E * k) with hτdef
  -- degree bookkeeping
  have hpowne : σ.Φ ^ (E * G) ≠ 0 := pow_ne_zero _ hΦne
  have hdegpow : (σ.Φ ^ (E * G)).degree = ((E * G * D : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hpowne, Polynomial.natDegree_pow]
  have hτdeg : τ.degree < ((E * G * D : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro k hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · have hkG : k < G := Finset.mem_range.mp hk
      have hψk : ν.ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
      obtain ⟨-, htkC, -, -⟩ := httk k hkG hψk
      have htermne : tt k * σ.Φ ^ (E * k) ≠ 0 := mul_ne_zero htk (pow_ne_zero _ hΦne)
      refine (Polynomial.natDegree_lt_iff_degree_lt htermne).mp ?_
      rw [Polynomial.natDegree_mul htk (pow_ne_zero _ hΦne), Polynomial.natDegree_pow]
      have httdeg : (tt k).natDegree < D := Polynomial.natDegree_lt_natDegree htk htkC
      have h1 : E * k + 1 ≤ E * G := by
        have hEk : E * k + 1 ≤ E * (k + 1) := by
          rw [Nat.mul_succ]
          exact Nat.add_le_add_left hE1 (E * k)
        exact le_trans hEk (Nat.mul_le_mul_left E hkG)
      have hb : D + E * k * D ≤ E * G * D := by
        have h2 : (E * k + 1) * D ≤ (E * G) * D := Nat.mul_le_mul_right D h1
        calc D + E * k * D = (E * k + 1) * D := by ring
          _ ≤ E * G * D := h2
      exact lt_of_lt_of_le (Nat.add_lt_add_right httdeg _) hb
  have hΦ'deg : σ'.Φ.degree = ((E * G * D : ℕ) : WithBot ℕ) := by
    rw [hPhi, Polynomial.degree_add_eq_left_of_degree_lt (by rw [hdegpow]; exact hτdeg),
      hdegpow]
  have hΦ'ne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  -- child-stage weights
  have hwPhi' : σ'.w σ'.Φ = (ν.h : ℤ) := by rw [σ'.hwΦ, hch]
  have hwparent : σ'.w σ.Φ = (E : ℤ) * (σ.h : ℤ) := by
    have hinC : inC σ'.Φ σ.Φ := by
      show σ.Φ.degree < σ'.Φ.degree
      rw [hΦ'deg, Polynomial.degree_eq_natDegree hΦne]
      have hlt : D < E * G * D := by
        have h2 : 2 * D ≤ E * G * D := Nat.mul_le_mul_right D hEG
        omega
      exact_mod_cast hlt
    rw [σ'.hStretch σ.Φ hΦne hinC, hcw, σ.hwΦ, hce]
  have hwpow : σ'.w (σ.Φ ^ (E * G)) = ((E * G : ℕ) : ℤ) * ((E : ℤ) * (σ.h : ℤ)) := by
    rw [w_pow_helper σ' σ.Φ hΦne (E * G), hwparent]
  -- the common contradiction, once σ'.w (Φ^{eg}) = ν.h is pinned
  have hfinal : σ'.w (σ.Φ ^ (E * G)) = (ν.h : ℤ) → False := by
    intro hkey
    rw [hwpow] at hkey
    push_cast at hkey
    -- hkey : E·G·(E·σ.h) = ν.h  (up to orientation)
    have hX0 : (0 : ℤ) ≤ (E : ℤ) * (σ.h : ℤ) := by positivity
    have hmul : 2 * ((E : ℤ) * (σ.h : ℤ))
        ≤ ((E : ℤ) * (G : ℤ)) * ((E : ℤ) * (σ.h : ℤ)) :=
      mul_le_mul_of_nonneg_right hEG2' hX0
    nlinarith [hkey, hcon, hmul, hE1', hσh1', hh1']
  by_cases hτ0 : τ = 0
  · -- no tail: Φ̂ = Φ^{eg}
    have hkey : σ'.w (σ.Φ ^ (E * G)) = (ν.h : ℤ) := by
      rw [← hwPhi', hPhi, hτ0, add_zero]
    exact hfinal hkey
  · -- tail present: every τ-slot weighs ≥ g·h under the failure hypothesis
    have hτC : inC σ'.Φ τ := by
      show τ.degree < σ'.Φ.degree
      rw [hΦ'deg]; exact hτdeg
    have hwτbound : (G : ℤ) * (ν.h : ℤ) ≤ σ.w τ := by
      refine w_sum_ge_helper σ (Finset.range G) _ _ ?_ (by rw [← hτdef]; exact hτ0)
      intro k hk htkne
      have hkG : k < G := Finset.mem_range.mp hk
      have htk : tt k ≠ 0 := fun h0 => htkne (by rw [h0, zero_mul])
      have hψk : ν.ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
      obtain ⟨-, -, htkw, -⟩ := httk k hkG hψk
      rw [σ.hwmul _ _ htk (pow_ne_zero _ hΦne), htkw,
        w_pow_helper σ σ.Φ hΦne (E * k), σ.hwΦ]
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      have hkh : (k : ℤ) * (ν.h : ℤ) ≤ (k : ℤ) * ((E : ℤ) * (σ.h : ℤ)) :=
        mul_le_mul_of_nonneg_left hcon hk0
      push_cast
      nlinarith [hkh]
    have hwτ' : σ'.w τ = (E : ℤ) * σ.w τ := by
      rw [σ'.hStretch τ hτ0 hτC, hcw, hce]
    have hwτbig : (ν.h : ℤ) < σ'.w τ := by
      rw [hwτ']
      have hE0 : (0 : ℤ) ≤ (E : ℤ) := by linarith
      have hint1 : (E : ℤ) * ((G : ℤ) * (ν.h : ℤ)) ≤ (E : ℤ) * σ.w τ :=
        mul_le_mul_of_nonneg_left hwτbound hE0
      have hh0 : (0 : ℤ) ≤ (ν.h : ℤ) := by linarith
      have hint2 : 2 * (ν.h : ℤ) ≤ ((E : ℤ) * (G : ℤ)) * (ν.h : ℤ) :=
        mul_le_mul_of_nonneg_right hEG2' hh0
      nlinarith [hint1, hint2, hh1']
    have hkey : σ'.w (σ.Φ ^ (E * G)) = (ν.h : ℤ) := by
      have hsum : σ'.Φ + (-τ) = σ.Φ ^ (E * G) := by rw [hPhi]; ring
      have hne' : σ'.Φ + (-τ) ≠ 0 := by rw [hsum]; exact hpowne
      have hlt : σ'.w σ'.Φ < σ'.w (-τ) := by
        rw [w_neg_helper σ' τ hτ0, hwPhi']; exact hwτbig
      have hs := w_strict_helper σ' σ'.Φ (-τ) hΦ'ne (neg_ne_zero.mpr hτ0) hne' hlt
      rw [hsum, hwPhi'] at hs
      exact hs
    exact hfinal hkey

/-- **The V9 step-(i) PACKAGE**: the full `ReadPair` of the regrade at every
non-recentering read with a recorded successor — `he/hh/hcop/hbez` from the node,
the canonical `e = 1 → t = 0` from `hbezCanon`, and the steepness from
`V9_readSteepness` (`i ≥ 1`) or `V9_transSteepness` (`e·g ≥ 2`, covers the root).
The hypothesis `1 ≤ i ∨ 2 ≤ e·g` is exactly the perimeter outside obstruction R3c. -/
theorem V9_readPair {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).species ≠ ReadSpecies.recentering)
    (hcase : 1 ≤ i ∨ 2 ≤ (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).e
      * (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).g) :
    ReadPair (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ
      (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).e (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).h
      (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).s (H.nodes[i]'(Nat.lt_of_succ_lt hi1)).t := by
  set ν : Node p F := H.nodes[i]'(Nat.lt_of_succ_lt hi1) with hν
  refine ⟨ν.he, ν.hh, ν.hcop, ν.hbez, ?_, ?_⟩
  · intro he1
    have hbc := ν.hbezCanon
    rw [he1] at hbc
    push_cast at hbc
    omega
  · rcases hcase with hi0 | hEG
    · exact v9_readSteep_all H hcoh i hi0 (Nat.lt_of_succ_lt hi1)
    · exact V9_transSteepness hcoh i hi1 hsp hEG

/-- **The PROVED half of the V9 step-(v) grading bridge** (REV 2): the regrade
functional DOMINATES the stretched stage valuation, `e★·σ.w x ≤ wV(x)` for EVERY
nonzero `x` — from `σ.hK1`'s no-jump slot-min (the K1 lower bound at wV's attained
witness slot) plus the (non-strict) steepness `e★·σ.h ≤ h★`.  With V4's (VERTEX)
this pins the vertex coefficient from ABOVE: `σ'.w (B μ) = e·σ.w (B μ) ≤ wV(B μ)
= ν.gam − μ·e·h·g`.  The REVERSE inequality at the vertex slot is obstruction R3b
(the carry-algebra core) — see the record below. -/
theorem V9_wvGeStretch {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (estar hstar : ℕ)
    (hsteep : (estar : ℤ) * (σ.h : ℤ) ≤ (hstar : ℤ))
    (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    (estar : ℤ) * σ.w x ≤ childW σ σ.Φ estar hstar x := by
  obtain ⟨hex, -⟩ := S2_childW σ σ.Φ σ.hmonic σ.hdeg estar hstar
  obtain ⟨B, N, hdev, hlow, j₁, hj₁N, hj₁ne, hj₁eq⟩ := hex x hx
  obtain ⟨hKlow, -⟩ := σ.hK1 x B N hx hdev
  have hxle : σ.w x ≤ σ.w (B j₁) + (j₁ : ℤ) * σ.w σ.Φ := hKlow j₁ hj₁N hj₁ne
  rw [σ.hwΦ] at hxle
  rw [hj₁eq]
  have hj₁0 : (0 : ℤ) ≤ (j₁ : ℤ) := Int.natCast_nonneg j₁
  have hE0 : (0 : ℤ) ≤ (estar : ℤ) := Int.natCast_nonneg estar
  have h1 := mul_le_mul_of_nonneg_left hxle hE0
  have h2 := mul_le_mul_of_nonneg_left hsteep hj₁0
  nlinarith [h1, h2]

/-- **R3b REDUCED — the forward (sufficient) direction** (REV 3, R3b escalation round,
2026-07-28): if `x`'s σ.Φ-development attains its σ.w slot-min at the BOTTOM slot, the
regrade equals the stretch — `wV(x) = e★·σ.w x`.  With `V9_wvGeStretch` (the ≤ half)
this is an exact equality criterion.  The intended supplier of the bottom-slot
hypothesis at `x = B μ` is D.8-(TRANSPORT)'s upward FORCED-WINDOW clause (MOVES
2521–2528) — see the REV-3 obstruction record below. -/
theorem V9_wvEqStretch_of_bottomSlot {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (estar hstar : ℕ)
    (hsteep : (estar : ℤ) * (σ.h : ℤ) ≤ (hstar : ℤ))
    (x : Polynomial ℤ_[p]) (hx : x ≠ 0)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment σ.Φ x B N)
    (hB0 : B 0 ≠ 0) (hatt : σ.w x = σ.w (B 0)) :
    childW σ σ.Φ estar hstar x = (estar : ℤ) * σ.w x := by
  obtain ⟨-, hSMW⟩ := S2_childW σ σ.Φ σ.hmonic σ.hdeg estar hstar
  obtain ⟨hlow, -⟩ := hSMW x B N hx hdev
  have hN0 : 0 < N := by
    by_contra h0
    push_neg at h0
    exact hB0 (hdev.2.1 0 (by omega))
  have hup := hlow 0 hN0 hB0
  have hle : childW σ σ.Φ estar hstar x ≤ (estar : ℤ) * σ.w x := by
    rw [hatt]
    simpa using hup
  have hge := V9_wvGeStretch σ estar hstar hsteep x hx
  exact le_antisymm hle hge

/-- **R3b REDUCED — the converse (necessity) direction** (REV 3): under STRICT read
steepness, `wV(x) = e★·σ.w x` FORCES bottom-slot attainment of `x`'s σ.Φ-development.
Together with the forward direction: R3b at the vertex coefficient (the lower half
`σ'.w(B μ) ≥ ν.gam − μ·e·g·h`, given V4's (VERTEX) + R3a upper half) is EQUIVALENT to
the **BOTTOM-WINDOW LAW** — `B μ`'s inner σ.Φ-development has a nonzero bottom slot
attaining its σ.w slot-min.  This is the exact residue of the carry bookkeeping. -/
theorem V9_bottomSlot_of_wvEqStretch {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (estar hstar : ℕ) (hee : 1 ≤ estar)
    (hsteep : (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ))
    (x : Polynomial ℤ_[p]) (hx : x ≠ 0)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment σ.Φ x B N)
    (heq : childW σ σ.Φ estar hstar x = (estar : ℤ) * σ.w x) :
    B 0 ≠ 0 ∧ σ.w x = σ.w (B 0) := by
  obtain ⟨-, hSMW⟩ := S2_childW σ σ.Φ σ.hmonic σ.hdeg estar hstar
  obtain ⟨-, j₂, hj₂N, hj₂ne, hj₂eq⟩ := hSMW x B N hx hdev
  obtain ⟨hK1low, -⟩ := σ.hK1 x B N hx hdev
  have hK1j₂ := hK1low j₂ hj₂N hj₂ne
  rw [σ.hwΦ] at hK1j₂
  -- hK1j₂ : σ.w x ≤ σ.w (B j₂) + j₂·σ.h ;  hj₂eq : childW x = e★·σ.w (B j₂) + j₂·h★
  have hE0 : (0 : ℤ) < (estar : ℤ) := by exact_mod_cast hee
  have hcomb : (estar : ℤ) * σ.w x = (estar : ℤ) * σ.w (B j₂) + (j₂ : ℤ) * (hstar : ℤ) := by
    rw [← heq]; exact hj₂eq
  have hscaled : (estar : ℤ) * σ.w x
      ≤ (estar : ℤ) * (σ.w (B j₂) + (j₂ : ℤ) * (σ.h : ℤ)) :=
    mul_le_mul_of_nonneg_left hK1j₂ (le_of_lt hE0)
  have hj₂0 : j₂ = 0 := by
    by_contra hne
    have hj₂1 : (1 : ℤ) ≤ (j₂ : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hlt : (j₂ : ℤ) * ((estar : ℤ) * (σ.h : ℤ)) < (j₂ : ℤ) * (hstar : ℤ) :=
      mul_lt_mul_of_pos_left hsteep (by linarith)
    nlinarith [hcomb, hscaled, hlt]
  subst hj₂0
  refine ⟨hj₂ne, ?_⟩
  have hEq2 : (estar : ℤ) * σ.w x = (estar : ℤ) * σ.w (B 0) := by
    rw [hcomb]; push_cast; ring
  exact mul_left_cancel₀ (ne_of_gt hE0) hEq2

/-- **The steep-side frame descent** (REV 3, record-grounding): along the read side
(slot values tied at `gam` in the READ grading), the FRAME-grading slot values strictly
DESCEND — so at a steep read at most ONE on-side slot attains the frame minimum.  This
is the machine-checked seed of the SideReads(iii) tension in the REV-3 record below:
the `σ.R f` rendering demands the side pattern's ≥ 2 nonzero endpoint digits as frame
residual monomials, while the on-side frame values admit at most one attained minimum. -/
theorem V9_steepSide_frameDescent {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (estar hstar : ℕ)
    (hsteep : (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ))
    (gam : ℤ) (j j' : ℕ) (hjj' : j < j') (wj wj' : ℤ)
    (hj : (estar : ℤ) * wj + (j : ℤ) * (hstar : ℤ) = gam)
    (hj' : (estar : ℤ) * wj' + (j' : ℤ) * (hstar : ℤ) = gam) :
    (estar : ℤ) * (wj' + (j' : ℤ) * (σ.h : ℤ))
      < (estar : ℤ) * (wj + (j : ℤ) * (σ.h : ℤ)) := by
  have hjj : (j : ℤ) < (j' : ℤ) := by exact_mod_cast hjj'
  nlinarith [hj, hj', hsteep, hjj,
    mul_pos (by linarith : (0 : ℤ) < (j' : ℤ) - (j : ℤ))
      (by linarith : (0 : ℤ) < (hstar : ℤ) - (estar : ℤ) * (σ.h : ℤ))]

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
  -- ══════════════════════════════════════════════════════════════════════════════════
  -- E-PHASE OBSTRUCTION RECORD — REV 2 (escalation round, 2026-07-28, post-V2/V4).
  -- Rev-1's R1/R2 are CLEARED this round: `V4_readLanding` AND `V2_readResidual`/
  -- `V2_readFrame` are proved on disk (working tree).  The route (i)–(vi) was re-derived
  -- against the landed interfaces; it STILL does not close.  The exact residual:
  --
  -- (R3a) ANCHOR TRANSPORT — DERIVABLE, NOT YET BUILT (was rev-1 R3, now with a full
  --   derivation spec; it does NOT need SideReads(iii)'s `σ.R f` rendering, so the
  --   U31-fenced adjudication is DODGED, not decided): step (iv)'s
  --   `HasAnchorK (V.D.Rv f) ν.a ν.Ranch` follows from the pack alone —
  --   run the min-sum decomposition of `Rv` over f's FRAME-i development B′ (from
  --   `ReadsOf` at read i; note `wV(B′_j·σ.Φ^j) = e·σ.w(B′_j) + j·h` via
  --   `V.hStretch`+`V.hwPhi`+`V.hwmul` is EXACTLY SideReads(i)'s functional):
  --   SideReads(i) gives support at `ν.gam` with ties EXACTLY the stride digits
  --   `j = s0 + e·k, pat k ≠ 0`; tie positions `(j − t·γ)/e = a + k` (`hAnchor` +
  --   Bézout) are injective across ties, so the tie sum of monomials cannot cancel:
  --   `wV(f) = ν.gam` attained and `Rv f = Σ_k C(pat k)·T(a + k) = T(a)·(Ranch)`
  --   (scalars: `D.hS5` gives ONE unit c rendering BOTH `σ.R B′_j` and `Rv B′_j`;
  --   match c = pat k against SideReads(ii)'s recorded `σ.R` digit).  `Ranch.coeff 0
  --   = pat 0 ≠ 0` is `hpat0`; `OrdPsiPoly` is `ν.hOrd` verbatim.  A V4-kernel-sized
  --   private lemma (~300 lines, same shape as V4's min-sum core at the SIMPLER key
  --   residual `Rv Φ = T s★`).
  --
  -- (R3b) THE GRADING BRIDGE — **THE ONE REMAINING HARD CORE** (NEW finding, flagged
  --   per the header's ⚠ discipline: route (v)'s written justification is WRONG).
  --   (v) claims `σ'.w(B μ) = ν.e·σ.w(B μ) = wV(B μ)` "via the RECORDED
  --   child_wPrev/hStretch on the ONE coefficient".  The FIRST equality is fine
  --   (`σ'.hStretch`: B μ ∈ C_{Φ̂}).  The SECOND is UNJUSTIFIED: `V.hStretch` needs
  --   `inC σ.Φ`, and the vertex coefficient of the σ'.Φ-development has
  --   `deg σ.Φ ≤ deg (B μ) < deg σ'.Φ` in general.  No general identity exists —
  --   on the SAME space C_{Φ̂}: `wV(σ.Φ) = ν.h ≠ ν.e·σ.h = σ'.w(σ.Φ)` (strict by
  --   steepness).  What IS provable is one half: `ν.e·σ.w x ≤ wV(x)` for ALL x
  --   (`V9_wvGeStretch` above, PROVED — σ.hK1's no-jump slot-min at wV's attained
  --   witness + steepness), so V4's (VERTEX) + R3a pin the vertex from ABOVE:
  --   `σ'.w(B μ) ≤ ν.gam − μ·e·g·h`.  The LOWER half `σ'.w(B μ) ≥ ν.gam − μ·e·g·h`
  --   is the D.8 landing in the CHILD grading `G(j) = e·σ.w(B_j) + j·h` (the
  --   obstruction record item 4 of `K1_vertexPin.lean` — B2-FINAL's carry
  --   composition).  At ADJACENT reads (`s0'+wSide' = μ`) it closes from
  --   SideReads(ii)'s top-endpoint equality at read i+1 (K1_SAE's route); at
  --   NON-ADJACENT reads the child side data give only
  --   `σ'.w(B μ) ≥ STR_{i+1}·line_{i+1}.at(μ·D_{i+1})`, which under (NA) sits
  --   STRICTLY BELOW the target — and (NA)/`TransitionAdmissible` is REALIZABILITY
  --   data that `ReadsOf` deliberately does not record.  NOT assembled from any
  --   on-disk asset; this is the dedicated carry-algebra unit.
  --
  -- ── (R3b — REV 3: THE CARRY-BRIDGE ESCALATION FINDING, 2026-07-28) ──────────────
  --   The dispatched mechanism ("the carry term the twisted product produces is
  --   EXACTLY absorbed by the frame regrade — quot_add_carry + the V2 identity-digit
  --   route") was TESTED and does NOT close R3b.  The definitive state:
  --
  --   1. REDUCTION — PROVED above, Lean-core (`V9_wvEqStretch_of_bottomSlot`,
  --      `V9_bottomSlot_of_wvEqStretch`): R3b's lower half is EQUIVALENT to the
  --      **BOTTOM-WINDOW LAW** — B μ's own σ.Φ-development attains its σ.w slot-min
  --      at slot 0.  (Forward: bottom slot + `V9_wvGeStretch` pin
  --      wV(B μ) = e★·σ.w(B μ); converse: a wV-attaining inner slot l ≥ 1 costs
  --      deficit ≥ l·(h★ − e★·σ.h) > 0 by steepness.)  The carry cocycle
  --      (quot_add_carry / D7) is scalar bookkeeping and carries no weight content;
  --      the residue is this ONE window equation.
  --
  --   2. COUNTERMODEL — R3b (and the kernel's conclusion) is NOT derivable from
  --      SideReads(i)+(ii)+(vi) + hOrd/hAnchor/γ-tie + the V-frame engine +
  --      hStretch/child_slotmin.  Witness (numerics sympy-verified 2026-07-28 —
  --      reproducible artifact `verification/r3b_countermodel_check.py`, six checks;
  --      a Lean carrier would be a U31-gate-sized Stage-pair artifact): p = 2, σ = the
  --      (1,1)-Gauss stage at Φ = X (U31's base stage), read pair (e★,h★) = (1,2)
  --      (t★ = 0, steep: 1·1 < 2), ψ = z²+z+1, Φ̂ = X²+4X+16 (recorded IsReadLift),
  --      f = (X+8)·(Φ̂² + 8X³) = X⁵+24X⁴+176X³+512X²+1280X+2048.
  --      Read-i data: side gam = 10 attained exactly at slots {1,3,5} (values
  --      10,10,10; off-side 11,13,11), pattern (1,0,1,0,1), Ranch = ψ², μ = 2,
  --      a = 1 — clauses (i),(ii) + hOrd/hAnchor/hpat0/hpatTop/hLineU/γ-tie ALL HOLD.
  --      Φ̂-development: B₂ = X+16, B₁ = −384, B₀ = 512X+4096.  V4-(VERTEX) HOLDS:
  --      wV(B₂) = 2 = gam − μ·e★gh★ (G_V = (11,11,10), BOX strict).  Clause (vi)
  --      HOLDS: digPrime z̄ (B₂) = z̄ = ν.vtx (a − μ·m̂ = 1, vtxPoly = 1).  BUT
  --      σ'.w(B₂) = e★·σ.w(B₂) = 1 < 2 = STR·line.at(μ·childWidth): the kernel's
  --      weight conclusion is FALSE on these data (inner window of B₂ = X+16:
  --      l₋ = 1, bottom slot 16 too deep — the bottom-window law fails).
  --      The SOLE ReadsOf clause the witness violates is SideReads(iii)'s `σ.R f`
  --      rendering (σ.R f = z⁵ — frame-min at the top slot 5 alone — ≠ T(1)·ψ²'s
  --      3-term pattern): exactly the ⚠-fenced U31 seam this unit is charged NOT to
  --      consume.  In particular clause (vi) does NOT supply R3b (digit equations
  --      carry no weight content — the witness satisfies (vi) while violating the
  --      conclusion).
  --
  --   3. THE (iii)-TENSION AT STEEP READS — machine-checked seed:
  --      `V9_steepSide_frameDescent` (above): along the read side the FRAME values
  --      strictly descend, so at most ONE on-side slot attains the frame min; while
  --      (iii) + hpat0/hpatTop (hOrd/hμ force wSide/e★ ≥ μ·g ≥ 1) demand ≥ 2
  --      occupied σ.R f support positions.  So at EVERY steep read (all i ≥ 1 via
  --      `V9_readSteepness`; roots with e·g ≥ 2 + successor via `V9_transSteepness`)
  --      clause (iii) forces f's frame-min entirely OFF the read side — nonzero
  --      beyond-window slots reproducing the full pattern at the recorded anchor (a
  --      conspiracy shape); where the window reaches f's top slot, (iii) is
  --      UNSATISFIABLE and ReadsOf is vacuous.  A kernel proof routed through (iii)
  --      would lean its full weight on the seam and dies with (iii)'s queued
  --      RV-vocabulary restatement.  NOT taken.
  --
  --   4. WHAT R3b NEEDS (the SPECIFIC note display — the deliverable of record; THE
  --      CAMPAIGN FINDING ON B2-FINAL): §B2-DEF **D.8-(TRANSPORT), UPWARD leg, the
  --      FORCED-WINDOW clause** — MOVES 2521–2528: "d_j = z^{q_j}·(a polynomial of
  --      degree < g) with the window base q_j forced by the stride/width data (slot
  --      j's S5 position, plus jm̂ − a)" — re-run at the REGRADED frame (the (S5′)
  --      position law of each minimizing slot term).  At the vertex slot the clause
  --      IS the bottom-window law: window base (l₋ − t★·wV(B μ))/e★ = S5′ position
  --      −t★·σ.w(B μ) ⟺ l₋ = t★·(wV(B μ) − e★σ.w(B μ)) = t★·deficit; combined with
  --      the reduction's deficit ≥ l₋·(h★ − e★σ.h): t★ = 0 forces l₋ = 0 directly
  --      (kills the countermodel, whose l₋ = 1 at t★ = 0), and t★·(h★ − e★σ.h) ≥ 2
  --      forces deficit = 0; the BOUNDARY t★ = 1 ∧ h★ − e★σ.h = 1 is NOT decided by
  --      the window equation alone — the transcriber must take the display's full
  --      strength (or a sharper reading) there.  Blueprint §10.1 fenced (TRANSPORT)
  --      OUT of V4 as "NOT needed by any of the three discharges" — that fencing is
  --      WRONG for V9: (TRANSPORT)'s upward window is exactly R3b.  The dedicated
  --      unit = transcribe D.8-(TRANSPORT) at the ReadFrame (V4's follow-on), then
  --      close R3b by `V9_wvEqStretch_of_bottomSlot`.
  --
  -- (R3c) ROOT STEEPNESS — MOSTLY CLEARED: `V9_transSteepness` (PROVED above) derives
  --   `e·σ.h < h` from the recorded (i, i+1) transition for `e·g ≥ 2`, covering the
  --   root read (rev-1's "fourth seam") without any predecessor.  The corner
  --   `i = 0 ∧ ν.e·ν.g = 1` is GENUINELY underivable from ReadsOf + HistoryCoherent:
  --   the recorded data are consistent with `h ≤ e·σ₀.h` (`σ'.R Φ₀ = T 1 − C c` is a
  --   lawful non-monomial residual of a non-coefficient — no Stage law is violated);
  --   root steepness is (I-aug) classifier-semantics content, hypothesis class.
  --
  -- CONSUMPTION MAP once R3a + R3b land: `V9_readPair` (PROVED; R3c-corner
  -- hypothesis-carried) → `V2_readFrame` → V3/V4 at `Φ̂ = σ'.Φ` (via `isNodeLift_iff`
  -- on HistoryCoherent's non-recentering leg; `ψ ≠ X` from `ν.hzbarRoot` since
  -- `ν.zbar` is a unit) → R3a anchors, `ν.hOrd` orders → V4 (VERTEX) `wV(B μ) =
  -- ν.gam − μ·e·h·g` + `V9_wvGeStretch` give ≤, R3b gives ≥ → `σ'.hStretch` converts
  -- to `σ'.w(B μ)` → γ-tie + slope law + `hLineU` + `hDweq` give the fenced ℚ-form
  -- (`K1_SAE_vertexEq_endpoint`'s arithmetic pattern, proved in HC2).
  --
  -- ── REV 4 (V10 transcription round, 2026-07-28): THE MAP ABOVE IS SUPERSEDED. ────
  -- `V10_readTransition_incompatible` (PROVED, Lean-core) shows the recorded
  -- non-recentering transition is CONTRADICTORY at `ν.e·ν.g ≥ 2`, so every leg the
  -- map was built for closes by exfalso below — NOT by transport mathematics (the
  -- header REV-4 note and V10's ⚠⚠ header carry the full disclosure).  At
  -- `ν.e·ν.g = 1` with `i ≥ 1` the species inventory closes the goal (a
  -- non-recentering non-root read is an increment, and increments have `e·g > 1`).
  -- THE ONE REMAINING LEG: the R3c corner `i = 0 ∧ ν.e·ν.g = 1` (root read,
  -- recentering-shaped, all keys linear by `hroot`).  Its records are CONSISTENT
  -- (no V10-style collapse: `Φ ∉ C_{Φ̂}` at equal degrees, so the forcing never
  -- starts), and the honest g = 1 landing needs machinery `ReadsOf` does not
  -- record: EITHER the parent frame's D.1(b) tie laws (w_jump/w_strict at
  -- StageCore grade — underivable from bare `Stage`, per the quarantined
  -- pathological-stage findings) to assemble the Taylor-transport digit sum
  -- `D_μ(X^{s0}·Ranch at z̄) ≠ 0`, OR SideReads(iii)'s `σ.R f` anchor — the
  -- ⚠-fenced U31 seam (which at SINGLE-side reads is exactly where the fence's own
  -- text says the rendering is faithful).  Bare-derivable at the corner (recorded
  -- here for the eventual close): `σ.w(B_m) ≥ gam − m·h★` for ALL m (Taylor lower
  -- bound; needs only `σ.w(int) ≥ 0` from hwult on repeated 1s), and
  -- `min_m (σ.w(B_m) + m·h★) = gam` attained (two-sided Taylor).  Missing: the
  -- attainment AT m = μ.  `B μ ≠ 0` alone is free from SideReads(vi) + `hOrd`
  -- (`ν.vtx ≠ 0`).  This corner sorry is the kernel's ENTIRE remaining obligation.
  -- ══════════════════════════════════════════════════════════════════════════════════
  classical
  have hilen : i < H.nodes.length := by omega
  by_cases hEG : 2 ≤ (H.nodes[i]'hilen).e * (H.nodes[i]'hilen).g
  · -- NON-CORNER: the recorded transition data are contradictory (V10 finding 2)
    exfalso
    obtain ⟨hroot, hslope, hgam, htrans⟩ := h.2.2.1
    obtain ⟨hrecC, hnrecC, hseq, hteq, hwin, hDweq, hsteepen⟩ := htrans i hi1
    obtain ⟨hliftraw, htcoreraw⟩ := hnrecC hsp
    have hsteep := V9_transSteepness h.2.2.1 i hi1 hsp hEG
    -- `ψ.coeff 0 ≠ 0` from irreducibility + monicity + the unit root
    have hψ0 : (H.nodes[i]'hilen).ψ.coeff 0 ≠ 0 := by
      intro h0
      obtain ⟨u, hu⟩ := Polynomial.X_dvd_iff.mpr h0
      rcases (H.nodes[i]'hilen).hψirr.isUnit_or_isUnit hu with hX | hUnit
      · exact Polynomial.not_isUnit_X hX
      · obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hUnit
        have hψX : (H.nodes[i]'hilen).ψ = Polynomial.C c * Polynomial.X := by
          rw [hu, ← hc.2]; ring
        have hlc : c = 1 := by
          have hm := (H.nodes[i]'hilen).hψmonic
          rw [hψX] at hm
          have hlead : (Polynomial.C c * Polynomial.X).leadingCoeff = c := by
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
              Polynomial.leadingCoeff_X, mul_one]
          rw [Polynomial.Monic, hlead] at hm
          exact hm
        have hzb := (H.nodes[i]'hilen).hzbarRoot
        rw [hψX, hlc, map_one, one_mul, Polynomial.eval₂_X] at hzb
        exact Units.ne_zero _ hzb
    -- the P2 pin from the canonical Bézout window
    have he1t : (H.nodes[i]'hilen).e = 1 → (H.nodes[i]'hilen).t = 0 := by
      intro he1
      have hc := (H.nodes[i]'hilen).hbezCanon
      rw [he1] at hc
      push_cast at hc
      omega
    exact V10_readTransition_incompatible (H.nodes[i]'hilen).σ (H.nodes[i+1]'hi1).σ
      (H.nodes[i]'hilen).e (H.nodes[i]'hilen).h (H.nodes[i]'hilen).s
      (H.nodes[i]'hilen).t (H.nodes[i]'hilen).g (H.nodes[i]'hilen).ψ
      ((H.nodes[i+1]'hi1).σ.Φ) hsteep hEG (H.nodes[i]'hilen).hcop
      (H.nodes[i]'hilen).hbez he1t hψ0 hliftraw htcoreraw.base.child_key
      htcoreraw.base.child_e htcoreraw.base.child_wPrev
      htcoreraw.base.child_slotmin hseq hteq
  · -- `ν.e·ν.g = 1`
    rcases Nat.eq_zero_or_pos i with hi0 | hi1'
    · -- THE R3c CORNER `i = 0 ∧ ν.e·ν.g = 1`: the kernel's one remaining leg
      -- (full obstruction record in the REV-4 block above).
      sorry
    · -- `i ≥ 1`: a non-recentering non-root read is an increment; `hspecInc`
      -- forces `1 < e·g` against the case hypothesis.
      cases hspec : (H.nodes[i]'hilen).species with
      | root =>
          exact absurd ((H.root_iff i hilen).mp hspec) (by omega)
      | increment =>
          exact absurd ((H.nodes[i]'hilen).hspecInc hspec) (by omega)
      | recentering =>
          exact absurd hspec hsp

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V9_readSteepness
#print axioms LeanUrat.HC1.V9_transSteepness
#print axioms LeanUrat.HC1.V9_readPair
#print axioms LeanUrat.HC1.V9_wvGeStretch
#print axioms LeanUrat.HC1.V9_wvEqStretch_of_bottomSlot
#print axioms LeanUrat.HC1.V9_bottomSlot_of_wvEqStretch
#print axioms LeanUrat.HC1.V9_steepSide_frameDescent
#print axioms LeanUrat.HC1.V9_K1nonrec
