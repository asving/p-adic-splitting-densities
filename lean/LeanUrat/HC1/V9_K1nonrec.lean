/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.V4_readLanding
import LeanUrat.Moves.ResVal
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
    **[REV 5 SUPERSESSION — the corner is CLOSED, see the REV-5 note below]**;
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

**REV-5 NOTE (R3c corner round, 2026-07-28): THE CORNER IS CLOSED — `V9_K1nonrec`
IS SORRY-FREE, Lean-core.**  The REV-4 adjudication ("needs StageCore tie laws OR
SideReads(iii)") is SUPERSEDED: neither is needed, by three corner-specific
mechanisms (the `V9CornerHelpers` toolkit below; `v9c_corner` is the core):
1. at the corner BOTH keys have degree 1, so every sum in sight is a development
   with CONSTANT coefficients at distinct slots and `child_slotmin` (D.7's K1
   record) IS the cross-slot jump law — `w_jump` is never needed;
2. the binomial transport `Φ = Φ̂ − t₀` moves the READ functional's slot-min to
   the parent key (`v9c_slotmin`, the bare-derivable recentering-transport K1 —
   the S10/D.10 mechanism without `StageCoreL`), giving `σ'.w f = gam` from
   SideReads(i)+(ii) and the two forced residual computations
   `σ'.R f = Σ_{m∈M} C(β_m)T(m) = Σ_k C(b_k)(T1 − C ĉ₀)^{s0+k}` via hRadd/hRlt;
3. `child_dig_frame`'s unknown `z̄^{mfun w}` twists cancel by cross-multiplying
   its two instances at the SHARED weight `σ.w(B₀ s0) = σ.w(B₀(s0+k)·t₀^k)`, the
   (S5) positions collapse by the σ.e-cleared `hStretch` identity, and the
   surviving μ-coefficient is `unit · Σ_k pat k·z̄^k·C(s0+k, μ)` — the μ-th
   Taylor coefficient of `X^{s0}·Ranch` at the recorded root, NONZERO by `ν.hOrd`
   (`v9c_taylor_ne`, Hasse nonvanishing at an order-exactly-μ zero; `zbar` a unit
   makes the `X^{s0}` factor invisible).  So `μ ∈ M` — both conjuncts at once;
   clause (vi)/`vtx` is not even consumed.  SideReads(iii) NOT consumed (⚠ fence
   holds); ZERO new axioms; statement verbatim.  Downstream (post-rebuild):
   `K1_readVertexPin{,_nonrec}`, `K1_NA_transport_root/increment`,
   `K1_SAE_vertexEq_endpoint`, U20a/U20b/U20c, `readsOf_NA`, U22-E2 all
   Lean-core clean; `readsOf_SAE`/`readsOf_realizable` remain sorryAx solely via
   U22-E1's and U21's own independent sorries (not this kernel).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesJ

/-! SYN-M8 record (2026-07-30, C1 cluster): `w_one_helper`/`w_neg_helper`/`w_pow_helper`/
`w_sum_ge_helper`/`v9c_R_pow` deleted; call sites re-pointed at
`Moves.ResVal.w_one/w_neg/w_pow/w_sum_ge/R_pow` (statement-identical, SYN-E0 table).
`v9c_C_inj` (CommRing-general, weaker assumptions than the shared Field version) and
`w_strict_helper` (V9-specific) stay. -/
section V9SteepHelpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

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
      rw [ResVal.w_neg σ tt htne, hwtt, hwΦh, min_self, ← sub_eq_add_neg] at hult
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
    rwa [hΦ', hw' (σ.Φ - tt)] at h
  rwa [hres] at hkey

/- ═══ HK-06 WAVE ARCHIVAL RECORD (2026-07-31, task #44) — FOUR SUPPLY LEMMAS DELETED ═══
   `v9_readSteep_all` (private), `V9_readSteepness`, `V9_transSteepness`, `V9_readPair`
   were the OLD-keying read-steepness suppliers (`νᵢ.e·σᵢ.h < νᵢ.h`).  Under the ratified
   (S-a) two-step regrade keying they are REFUTED AS STATED: the (NEW) leg's `child_h`
   ties σᵢ.h = νᵢ.h at every node with a non-recentering predecessor, collapsing the
   statement to `νᵢ.e·νᵢ.h < νᵢ.h` — false at Node.he/hh (BP2 §3.2 item 1, REVISION-2
   finding 13; the compiled countermodel instance is the positive gate history H₂ram of
   HC2/HK23_twoNodeGatePos.lean at i = 1, the HK-48 record).  Full pre-wave proofs are in
   git history (HEAD^ of the wave commit).  The restated pre-augmentation-scale supply
   `(νᵢ.e : ℤ)·σᵢ.wPrev σᵢ.Φ < νᵢ.h` is HK-08's post-wave unit (risk R-9: may need the
   HK-01 addendum).  `w_strict_helper` (below) is keying-independent and stays. -/

/-- The STRICT ultrametric law, DERIVED from `hwmul`/`hwult` alone (no `StageCore` needed):
`w f < w g → w (f + g) = w f` — the two-sided min trick on `f = (f + g) + (−g)`. -/
private lemma w_strict_helper (σ : Stage p F) (f g : Polynomial ℤ_[p])
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) (hlt : σ.w f < σ.w g) :
    σ.w (f + g) = σ.w f := by
  have h1 := σ.hwult f g hf hg hfg
  have hsum : (f + g) + (-g) = f := by ring
  have h2 := σ.hwult (f + g) (-g) hfg (neg_ne_zero.mpr hg) (by rw [hsum]; exact hf)
  rw [hsum, ResVal.w_neg σ g hg] at h2
  omega

end V9SteepHelpers



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

/-! ### The R3c corner toolkit (corner round, 2026-07-28)

The `i = 0 ∧ e·g = 1` corner closes WITHOUT the fenced SideReads(iii) and WITHOUT
StageCore tie laws, by three corner-specific mechanisms:
1. **K1 is the cross-slot jump law at the corner**: both keys have degree 1, so
   every sum in sight is a development with CONSTANT coefficients at distinct
   slots, and `child_slotmin` (D.7's K1 record in `TransitionCoreL`) pins the
   weight of every partial sum — the StageCore `w_jump` is never needed across
   slots, and within a slot nothing ever sums.
2. **The binomial transport** `Φ = Φ̂ − t₀` re-expands any σ.Φ-development as a
   σ'.Φ-development with constant coefficients (the degree-1 coefficient space
   is multiplication-closed), transporting the READ functional's slot-min to the
   parent key (`v9c_slotmin` — the recentering-transport K1, bare-derivable
   exactly at the corner; cf. S10/L5_recVV, which need `StageCoreL`).
3. **The frame-unit twists cancel**: `child_dig_frame`'s unknown `z̄^{mfun w}`
   twists are eliminated by cross-multiplying its two instances at the SHARED
   weight `σ.w (B₀ s0) = σ.w (B₀ (s0+k) · t₀^k)`, and the (S5) positions
   collapse by the σ.e-cleared `hStretch` identity
   `wPrev(B₀(s0+k)) + k·wPrev(t₀) = wPrev(B₀ s0)`; the surviving digit sum is
   the μ-th Taylor coefficient of `X^{s0}·Ranch` at the recorded root `−c₀`,
   nonzero by `hOrd` (Hasse-derivative nonvanishing at an order-exactly-μ zero).
-/

section V9CornerHelpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w` of a nonzero ℕ-constant is ≥ 0 (hwult on repeated 1s). -/
private lemma v9c_w_natCast_nonneg (σ : Stage p F) : ∀ n : ℕ, n ≠ 0 →
    0 ≤ σ.w (Polynomial.C ((n : ℕ) : ℤ_[p])) := by
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simpa using (ResVal.w_one σ).ge
    · have hmne : (Polynomial.C ((m : ℕ) : ℤ_[p])) ≠ 0 := by
        rw [ne_eq, Polynomial.C_eq_zero]
        exact_mod_cast Nat.pos_iff_ne_zero.mp hm
      have hsne : (Polynomial.C (((m + 1 : ℕ)) : ℤ_[p])) ≠ 0 := by
        rw [ne_eq, Polynomial.C_eq_zero]
        exact_mod_cast Nat.succ_ne_zero m
      have hsum : Polynomial.C (((m + 1 : ℕ)) : ℤ_[p])
          = Polynomial.C ((m : ℕ) : ℤ_[p]) + 1 := by
        push_cast; rw [map_add, map_one]
      have hult := σ.hwult (Polynomial.C ((m : ℕ) : ℤ_[p])) 1 hmne one_ne_zero
        (by rw [← hsum]; exact hsne)
      rw [ResVal.w_one σ] at hult
      have ihm := ih (Nat.pos_iff_ne_zero.mp hm)
      rw [hsum]
      omega

/-- A degree-≤-0 coefficient sum over distinct slots of a monic degree-1 key is
nonzero (degree separation). -/
private lemma v9c_sum_ne_zero (Φ : Polynomial ℤ_[p]) (hmon : Φ.Monic)
    (hdeg1 : Φ.natDegree = 1) (S : Finset ℕ) (hS : S.Nonempty)
    (CC : ℕ → Polynomial ℤ_[p]) (hne : ∀ j ∈ S, CC j ≠ 0)
    (hdeg : ∀ j ∈ S, (CC j).degree ≤ 0) :
    (∑ j ∈ S, CC j * Φ ^ j) ≠ 0 := by
  intro h0
  set m := S.max' hS with hm
  have hmmem : m ∈ S := S.max'_mem hS
  obtain ⟨c, hc⟩ : ∃ c, CC m = Polynomial.C c :=
    ⟨(CC m).coeff 0, Polynomial.eq_C_of_degree_le_zero (hdeg m hmmem)⟩
  have hcne : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact hne m hmmem hc
  have hcoeff : (∑ j ∈ S, CC j * Φ ^ j).coeff m = c := by
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
    · rw [hc, Polynomial.coeff_C_mul]
      have hpow : (Φ ^ m).coeff m = 1 := by
        have := (hmon.pow m).coeff_natDegree
        rwa [Polynomial.natDegree_pow, hdeg1, mul_one] at this
      rw [hpow, mul_one]
    · intro j hj hjm
      have hjlt : j < m := lt_of_le_of_ne (S.le_max' j hj) hjm
      rcases eq_or_ne (CC j) 0 with h | h
      · rw [h, zero_mul, Polynomial.coeff_zero]
      · refine Polynomial.coeff_eq_zero_of_degree_lt ?_
        refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
        have h1 : (CC j).degree ≤ 0 := hdeg j hj
        have h2 : (Φ ^ j).degree = (j : WithBot ℕ) := by
          rw [Polynomial.degree_pow, Polynomial.degree_eq_natDegree hmon.ne_zero,
            hdeg1]
          simp [Nat.smul_one_eq_cast]
        calc (CC j).degree + (Φ ^ j).degree ≤ 0 + (j : WithBot ℕ) := by
              rw [h2]; exact add_le_add h1 le_rfl
          _ = (j : WithBot ℕ) := zero_add _
          _ < (m : WithBot ℕ) := by exact_mod_cast hjlt
    · intro h; exact absurd hmmem h
  rw [h0, Polynomial.coeff_zero] at hcoeff
  exact hcne hcoeff.symm

/-- `T 1 ≠ C c` in a Laurent ring over a nontrivial ring (position mismatch). -/
private lemma v9c_T1_ne_C {K : Type*} [CommRing K] [Nontrivial K] (c : K) :
    (LaurentPolynomial.T 1 : LaurentPolynomial K) ≠ LaurentPolynomial.C c := by
  intro h
  have h1 : (LaurentPolynomial.C (1 : K) * LaurentPolynomial.T (1 : ℤ))
      = LaurentPolynomial.C c * LaurentPolynomial.T (0 : ℤ) := by
    rw [map_one, one_mul, LaurentPolynomial.T_zero, mul_one]; exact h
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h1
  have h2 : (Finsupp.single (1 : ℤ) (1 : K)) = Finsupp.single 0 c := h1
  have hc := DFunLike.congr_fun h2 1
  rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
    if_neg (by norm_num : ¬ (0 : ℤ) = 1)] at hc
  exact one_ne_zero hc

/-- Laurent `C` is injective. -/
private lemma v9c_C_inj {K : Type*} [CommRing K] {a b : K}
    (h : (LaurentPolynomial.C a : LaurentPolynomial K) = LaurentPolynomial.C b) :
    a = b := by
  have h2 : (Polynomial.C a : Polynomial K) = Polynomial.C b :=
    Polynomial.toLaurent_injective
      (by rw [Polynomial.toLaurent_C, Polynomial.toLaurent_C]; exact h)
  exact Polynomial.C_injective h2

/-- Shift a range sum past an all-zero prefix. -/
private lemma v9c_sum_shift {M : Type*} [AddCommMonoid M] (g : ℕ → M) (s0 : ℕ) :
    ∀ W : ℕ, (∀ e, e < s0 → g e = 0) →
    ∑ e ∈ Finset.range (s0 + W), g e = ∑ k ∈ Finset.range W, g (s0 + k) := by
  intro W
  induction W with
  | zero =>
      intro h0
      rw [add_zero, Finset.range_zero, Finset.sum_empty]
      exact Finset.sum_eq_zero (fun e he => h0 e (Finset.mem_range.mp he))
  | succ V ih =>
      intro h0
      rw [Finset.sum_range_succ, ← ih h0, show s0 + (V + 1) = (s0 + V) + 1 by omega,
        Finset.sum_range_succ]

/-- **The transported slot-min at the parent key** (corner mechanism 2): at the
degree-1 keys, a σ.Φ-development sum re-expands through `Φ = Φ̂ − t₀` as a
σ'.Φ-development with constant coefficients, and `child_slotmin` then pins
`σ'.w` of the sum to the attained minimum of the READ functional over the
ORIGINAL slots.  Bare-derivable: no StageCore, no steepness. -/
private lemma v9c_slotmin (σ σ' : Stage p F) (hstar : ℕ)
    (hdeg1 : σ.Φ.natDegree = 1)
    (t₀ : Polynomial ℤ_[p]) (ht₀ne : t₀ ≠ 0) (ht₀C : inC σ.Φ t₀)
    (ht₀w : σ.w t₀ = (hstar : ℤ))
    (hkey : σ'.Φ = σ.Φ + t₀)
    (hsm : IsSlotMinWeight σ'.w σ'.Φ 1 hstar σ.w)
    (S : Finset ℕ) (hS : S.Nonempty) (CC : ℕ → Polynomial ℤ_[p])
    (hne : ∀ j ∈ S, CC j ≠ 0) (hCdeg : ∀ j ∈ S, inC σ.Φ (CC j))
    (mstar : ℤ)
    (hmin : ∀ j ∈ S, mstar ≤ σ.w (CC j) + (j : ℤ) * (hstar : ℤ))
    (hatt : ∃ j ∈ S, σ.w (CC j) + (j : ℤ) * (hstar : ℤ) = mstar) :
    σ'.w (∑ j ∈ S, CC j * σ.Φ ^ j) = mstar := by
  classical
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦdeg : σ.Φ.degree = (1 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hΦne, hdeg1]; rfl
  have hdegC : ∀ j ∈ S, (CC j).degree ≤ 0 := by
    intro j hj
    have h := hCdeg j hj
    rw [inC, hΦdeg] at h
    rcases eq_or_ne (CC j) 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]; exact bot_le
    · rw [Polynomial.degree_eq_natDegree h0] at h ⊢
      have h1 : (CC j).natDegree < 1 := by exact_mod_cast h
      have h2 : (CC j).natDegree = 0 := by omega
      simp [h2]
  have ht₀deg : t₀.degree ≤ 0 := by
    have h := ht₀C
    rw [inC, hΦdeg] at h
    rw [Polynomial.degree_eq_natDegree ht₀ne] at h ⊢
    have h1 : t₀.natDegree < 1 := by exact_mod_cast h
    have h2 : t₀.natDegree = 0 := by omega
    simp [h2]
  have hΦ'degEq : σ'.Φ.degree = σ.Φ.degree := by
    have hlt : t₀.degree < σ.Φ.degree := by
      rw [hΦdeg]
      exact lt_of_le_of_lt ht₀deg (by exact_mod_cast Nat.zero_lt_one)
    rw [hkey]
    exact Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hΦ'ne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  have hΦ'deg1 : σ'.Φ.natDegree = 1 := by
    have := Polynomial.natDegree_eq_of_degree_eq hΦ'degEq
    rw [this, hdeg1]
  -- x ≠ 0 (degree separation)
  set x : Polynomial ℤ_[p] := ∑ j ∈ S, CC j * σ.Φ ^ j with hxdef
  have hx : x ≠ 0 := v9c_sum_ne_zero σ.Φ σ.hmonic hdeg1 S hS CC hne hdegC
  -- the binomial re-expansion at Φ̂
  have hΦeq : σ.Φ = σ'.Φ + (-t₀) := by rw [hkey]; ring
  set N' : ℕ := S.max' hS + 1 with hN'def
  set D : ℕ → Polynomial ℤ_[p] := fun i =>
    ∑ j ∈ S.filter (fun j => i ≤ j),
      ((j.choose i : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - i) * CC j) with hDdef
  -- degree bookkeeping for D
  have hDconst : ∀ i, (D i).degree ≤ 0 := by
    intro i
    refine le_trans (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_le_iff]
    intro j hj
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    refine le_trans (Polynomial.degree_mul_le _ _) ?_
    have h1 : ((j.choose i : ℕ) : Polynomial ℤ_[p]).degree ≤ 0 := by
      rw [← Polynomial.C_eq_natCast]; exact Polynomial.degree_C_le
    have h2 : ((-t₀) ^ (j - i) * CC j).degree ≤ 0 := by
      refine le_trans (Polynomial.degree_mul_le _ _) ?_
      have h3 : ((-t₀) ^ (j - i)).degree ≤ 0 := by
        rw [Polynomial.degree_pow, Polynomial.degree_neg]
        have : t₀.degree = 0 :=
          le_antisymm ht₀deg (Polynomial.zero_le_degree_iff.mpr ht₀ne)
        rw [this, smul_zero]
      calc ((-t₀) ^ (j - i)).degree + (CC j).degree ≤ 0 + 0 :=
            add_le_add h3 (hdegC j hjS)
        _ = 0 := add_zero 0
    calc ((j.choose i : ℕ) : Polynomial ℤ_[p]).degree + ((-t₀) ^ (j - i) * CC j).degree
        ≤ 0 + 0 := add_le_add h1 h2
      _ = 0 := add_zero 0
  have hDvanish : ∀ i, N' ≤ i → D i = 0 := by
    intro i hi
    rw [hDdef]
    refine Finset.sum_eq_zero ?_
    intro j hj
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    exact absurd hij (by have := S.le_max' j hjS; omega)
  -- the re-expansion identity
  have hxD : x = ∑ i ∈ Finset.range N', D i * σ'.Φ ^ i := by
    have hterm : ∀ j ∈ S, CC j * σ.Φ ^ j
        = ∑ i ∈ Finset.range N', (if i ≤ j then
            ((j.choose i : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - i) * CC j) * σ'.Φ ^ i
          else 0) := by
      intro j hjS
      have hpow : σ.Φ ^ j = ∑ i ∈ Finset.range (j + 1),
          σ'.Φ ^ i * (-t₀) ^ (j - i) * ((j.choose i : ℕ) : Polynomial ℤ_[p]) := by
        rw [hΦeq]; exact add_pow σ'.Φ (-t₀) j
      have hsub : Finset.range (j + 1) ⊆ Finset.range N' := by
        intro a ha
        rw [Finset.mem_range] at ha ⊢
        have := S.le_max' j hjS
        omega
      calc CC j * σ.Φ ^ j
          = ∑ i ∈ Finset.range (j + 1), (if i ≤ j then
              ((j.choose i : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - i) * CC j) * σ'.Φ ^ i
            else 0) := by
            rw [hpow, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
            rw [if_pos hij]; ring
        _ = ∑ i ∈ Finset.range N', (if i ≤ j then
              ((j.choose i : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - i) * CC j) * σ'.Φ ^ i
            else 0) := by
            refine Finset.sum_subset hsub ?_
            intro i _ hi
            rw [Finset.mem_range, not_lt] at hi
            rw [if_neg (by omega)]
    calc x = ∑ j ∈ S, ∑ i ∈ Finset.range N', (if i ≤ j then
            ((j.choose i : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - i) * CC j) * σ'.Φ ^ i
          else 0) := Finset.sum_congr rfl hterm
      _ = ∑ i ∈ Finset.range N', ∑ j ∈ S, (if i ≤ j then
            ((j.choose i : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - i) * CC j) * σ'.Φ ^ i
          else 0) := Finset.sum_comm
      _ = ∑ i ∈ Finset.range N', D i * σ'.Φ ^ i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hDdef, Finset.sum_mul, Finset.sum_filter]
  -- the development package
  have hdev' : IsDevelopment σ'.Φ x D N' := by
    refine ⟨?_, hDvanish, hxD⟩
    intro i
    refine lt_of_le_of_lt (hDconst i) ?_
    rw [hΦ'degEq, hΦdeg]
    norm_num
  -- child_slotmin fires
  obtain ⟨hlow, i₂, hi₂N, hi₂ne, hi₂eq⟩ := hsm x D N' hx hdev'
  -- lower bound on every D-slot weight
  have hDlb : ∀ i, D i ≠ 0 → mstar - (i : ℤ) * (hstar : ℤ) ≤ σ.w (D i) := by
    intro i hDine
    simp only [hDdef]
    refine ResVal.w_sum_ge σ (S.filter (fun j => i ≤ j)) _ _ ?_ hDine
    intro j hj hterm_ne
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    have hchne : ((j.choose i : ℕ) : Polynomial ℤ_[p]) ≠ 0 := by
      rw [← Polynomial.C_eq_natCast, ne_eq, Polynomial.C_eq_zero]
      exact_mod_cast Nat.pos_iff_ne_zero.mp (Nat.choose_pos hij)
    have hpowne : ((-t₀) ^ (j - i) : Polynomial ℤ_[p]) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr ht₀ne)
    have hCCne : CC j ≠ 0 := hne j hjS
    rw [σ.hwmul _ _ hchne (mul_ne_zero hpowne hCCne),
      σ.hwmul _ _ hpowne hCCne, ResVal.w_pow σ _ (neg_ne_zero.mpr ht₀ne),
      ResVal.w_neg σ t₀ ht₀ne, ht₀w]
    have hch0 : 0 ≤ σ.w ((j.choose i : ℕ) : Polynomial ℤ_[p]) := by
      rw [← Polynomial.C_eq_natCast]
      exact v9c_w_natCast_nonneg σ (j.choose i)
        (Nat.pos_iff_ne_zero.mp (Nat.choose_pos hij))
    have hminj := hmin j hjS
    have hji : ((j - i : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by
      push_cast [Nat.cast_sub hij]; ring
    rw [hji]
    nlinarith [hminj, hch0]
  -- upper bound at the top minimizing slot
  have hSminne : (S.filter (fun j => σ.w (CC j) + (j : ℤ) * (hstar : ℤ) = mstar)).Nonempty := by
    obtain ⟨j, hjS, hjeq⟩ := hatt
    exact ⟨j, Finset.mem_filter.mpr ⟨hjS, hjeq⟩⟩
  set jstar : ℕ := (S.filter (fun j => σ.w (CC j) + (j : ℤ) * (hstar : ℤ) = mstar)).max' hSminne
    with hjstardef
  have hjstarmem := Finset.max'_mem _ hSminne
  obtain ⟨hjstarS, hjstareq⟩ := Finset.mem_filter.mp hjstarmem
  have hjstarmax : ∀ j ∈ S, σ.w (CC j) + (j : ℤ) * (hstar : ℤ) = mstar → j ≤ jstar := by
    intro j hjS hjeq
    exact Finset.le_max' _ j (Finset.mem_filter.mpr ⟨hjS, hjeq⟩)
  -- D jstar = CC jstar + tail, tail strictly heavier
  have hDjstar : D jstar = CC jstar
      + ∑ j ∈ S.filter (fun j => jstar < j),
          ((j.choose jstar : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - jstar) * CC j) := by
    simp only [hDdef]
    have hsplit : S.filter (fun j => jstar ≤ j)
        = insert jstar (S.filter (fun j => jstar < j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hjS, hle⟩
        rcases eq_or_lt_of_le hle with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨hjS, h⟩
      · rintro (rfl | ⟨hjS, hlt⟩)
        · exact ⟨hjstarS, le_refl _⟩
        · exact ⟨hjS, le_of_lt hlt⟩
    rw [hsplit, Finset.sum_insert (by
      intro hmem
      exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl _))]
    congr 1
    rw [Nat.choose_self, Nat.sub_self, pow_zero, one_mul, Nat.cast_one, one_mul]
  have htail_ge : ∀ j ∈ S.filter (fun j => jstar < j),
      ((j.choose jstar : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - jstar) * CC j) ≠ 0 →
      σ.w (CC jstar) + 1
        ≤ σ.w (((j.choose jstar : ℕ) : Polynomial ℤ_[p])
            * ((-t₀) ^ (j - jstar) * CC j)) := by
    intro j hj _
    obtain ⟨hjS, hlt⟩ := Finset.mem_filter.mp hj
    have hchne : ((j.choose jstar : ℕ) : Polynomial ℤ_[p]) ≠ 0 := by
      rw [← Polynomial.C_eq_natCast, ne_eq, Polynomial.C_eq_zero]
      exact_mod_cast Nat.pos_iff_ne_zero.mp (Nat.choose_pos (le_of_lt hlt))
    have hpowne : ((-t₀) ^ (j - jstar) : Polynomial ℤ_[p]) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr ht₀ne)
    have hCCne : CC j ≠ 0 := hne j hjS
    rw [σ.hwmul _ _ hchne (mul_ne_zero hpowne hCCne),
      σ.hwmul _ _ hpowne hCCne, ResVal.w_pow σ _ (neg_ne_zero.mpr ht₀ne),
      ResVal.w_neg σ t₀ ht₀ne, ht₀w]
    have hch0 : 0 ≤ σ.w ((j.choose jstar : ℕ) : Polynomial ℤ_[p]) := by
      rw [← Polynomial.C_eq_natCast]
      exact v9c_w_natCast_nonneg σ (j.choose jstar)
        (Nat.pos_iff_ne_zero.mp (Nat.choose_pos (le_of_lt hlt)))
    have hstrict : mstar + 1 ≤ σ.w (CC j) + (j : ℤ) * (hstar : ℤ) := by
      rcases lt_or_eq_of_le (hmin j hjS) with h | h
      · omega
      · exact absurd (hjstarmax j hjS h.symm) (by omega)
    have hji : ((j - jstar : ℕ) : ℤ) = (j : ℤ) - (jstar : ℤ) := by
      push_cast [Nat.cast_sub (le_of_lt hlt)]; ring
    rw [hji]
    nlinarith [hstrict, hch0, hjstareq]
  have hwDjstar : D jstar ≠ 0 ∧ σ.w (D jstar) = σ.w (CC jstar) := by
    set T : Polynomial ℤ_[p] := ∑ j ∈ S.filter (fun j => jstar < j),
        ((j.choose jstar : ℕ) : Polynomial ℤ_[p]) * ((-t₀) ^ (j - jstar) * CC j) with hTdef
    rcases eq_or_ne T 0 with hT0 | hTne
    · rw [hDjstar, hT0, add_zero]
      exact ⟨hne jstar hjstarS, rfl⟩
    · have hwT : σ.w (CC jstar) + 1 ≤ σ.w T := by
        rw [hTdef]
        exact ResVal.w_sum_ge σ _ _ _ (fun j hj hne' => htail_ge j hj hne') (by rw [← hTdef]; exact hTne)
      have hDne : D jstar ≠ 0 := by
        rw [hDjstar]
        intro h0
        have hCC : CC jstar = -T := by
          have := congrArg (· - T) h0
          simpa [add_sub_cancel_right, sub_eq_neg_self] using
            (add_eq_zero_iff_eq_neg.mp h0)
        have hwEq : σ.w (CC jstar) = σ.w T := by
          rw [hCC, ResVal.w_neg σ T hTne]
        omega
      constructor
      · exact hDne
      · rw [hDjstar]
        exact w_strict_helper σ (CC jstar) T (hne jstar hjstarS) hTne
          (by rw [← hDjstar]; exact hDne) (by omega)
  -- conclude
  have hub : σ'.w x ≤ mstar := by
    have hjstarN : jstar < N' := by
      have := S.le_max' jstar hjstarS; omega
    have hthis := hlow jstar hjstarN hwDjstar.1
    simp only at hthis
    rw [hwDjstar.2] at hthis
    push_cast at hthis
    linarith [hjstareq, hthis]
  have hlb : mstar ≤ σ'.w x := by
    have h1 := hDlb i₂ hi₂ne
    simp only at hi₂eq
    push_cast at hi₂eq
    linarith [hi₂eq, h1]
  omega

/-- **Sub-development slot-min at the child key** (corner mechanism 1): the
weight of any sub-sum of a child development is bounded by every occupied slot
value and attains one of them — `child_slotmin` on the restricted development. -/
private lemma v9c_subsum (σ σ' : Stage p F) (hstar : ℕ)
    (hΦ'deg1 : σ'.Φ.natDegree = 1)
    (hsm : IsSlotMinWeight σ'.w σ'.Φ 1 hstar σ.w)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdeg : ∀ m, (B m).degree < σ'.Φ.degree)
    (J : Finset ℕ) (hJr : J ⊆ Finset.range Nd) (hJne : J.Nonempty)
    (hBne : ∀ m ∈ J, B m ≠ 0) :
    (∑ m ∈ J, B m * σ'.Φ ^ m) ≠ 0 ∧
    (∀ m ∈ J, σ'.w (∑ m' ∈ J, B m' * σ'.Φ ^ m')
      ≤ σ.w (B m) + (m : ℤ) * (hstar : ℤ)) ∧
    (∃ m ∈ J, σ'.w (∑ m' ∈ J, B m' * σ'.Φ ^ m')
      = σ.w (B m) + (m : ℤ) * (hstar : ℤ)) := by
  classical
  have hΦ'ne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  have hΦ'deg : σ'.Φ.degree = (1 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hΦ'ne, hΦ'deg1]; rfl
  have hdegC : ∀ m ∈ J, (B m).degree ≤ 0 := by
    intro m _
    have h := hdeg m
    rw [hΦ'deg] at h
    rcases eq_or_ne (B m) 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]; exact bot_le
    · rw [Polynomial.degree_eq_natDegree h0] at h ⊢
      have h1 : (B m).natDegree < 1 := by exact_mod_cast h
      have h2 : (B m).natDegree = 0 := by omega
      simp [h2]
  have hx : (∑ m ∈ J, B m * σ'.Φ ^ m) ≠ 0 :=
    v9c_sum_ne_zero σ'.Φ σ'.hmonic hΦ'deg1 J hJne B hBne hdegC
  set DJ : ℕ → Polynomial ℤ_[p] := fun m => if m ∈ J then B m else 0 with hDJdef
  have hdevJ : IsDevelopment σ'.Φ (∑ m' ∈ J, B m' * σ'.Φ ^ m') DJ Nd := by
    refine ⟨?_, ?_, ?_⟩
    · intro m
      by_cases hm : m ∈ J
      · simp only [hDJdef, if_pos hm]; exact hdeg m
      · simp only [hDJdef, if_neg hm]
        rw [Polynomial.degree_zero, hΦ'deg]
        exact WithBot.bot_lt_coe 1
    · intro m hm
      simp only [hDJdef]
      rw [if_neg (fun hmem => by have := Finset.mem_range.mp (hJr hmem); omega)]
    · have h1 : (∑ m' ∈ J, B m' * σ'.Φ ^ m') = ∑ m' ∈ J, DJ m' * σ'.Φ ^ m' :=
        Finset.sum_congr rfl (fun m hm => by simp only [hDJdef, if_pos hm])
      rw [h1]
      refine Finset.sum_subset hJr ?_
      intro m _ hm
      simp only [hDJdef, if_neg hm, zero_mul]
  obtain ⟨hlow, m₂, hm₂N, hm₂ne, hm₂eq⟩ :=
    hsm (∑ m' ∈ J, B m' * σ'.Φ ^ m') DJ Nd hx hdevJ
  have hm₂J : m₂ ∈ J := by
    by_contra hmem
    simp only [hDJdef] at hm₂ne
    exact hm₂ne (if_neg hmem)
  refine ⟨hx, ?_, ⟨m₂, hm₂J, ?_⟩⟩
  · intro m hmJ
    have hlm := hlow m (Finset.mem_range.mp (hJr hmJ))
      (by simp only [hDJdef, if_pos hmJ]; exact hBne m hmJ)
    simp only [hDJdef, if_pos hmJ] at hlm
    push_cast at hlm
    linarith
  · simp only [hDJdef, if_pos hm₂J] at hm₂eq
    push_cast at hm₂eq
    linarith

/-- **The equal-weight residual chain** (hRadd iterated over a finset whose every
nonempty sub-sum is nonzero of the common weight). -/
private lemma v9c_Rsum (σ' : Stage p F) (γ : ℤ) (x : ℕ → Polynomial ℤ_[p]) :
    ∀ (S : Finset ℕ), S.Nonempty →
    (∀ j ∈ S, x j ≠ 0) → (∀ j ∈ S, σ'.w (x j) = γ) →
    (∀ J ⊆ S, J.Nonempty → (∑ j ∈ J, x j) ≠ 0 ∧ σ'.w (∑ j ∈ J, x j) = γ) →
    σ'.R (∑ j ∈ S, x j) = ∑ j ∈ S, σ'.R (x j) := by
  intro S
  induction S using Finset.cons_induction with
  | empty => exact fun h => absurd h Finset.not_nonempty_empty
  | cons a S' ha IH =>
    intro _ hne hw hJ
    rcases S'.eq_empty_or_nonempty with h' | h'
    · subst h'; simp
    · rw [Finset.sum_cons, Finset.sum_cons]
      have hS'sub : S' ⊆ Finset.cons a S' ha := Finset.subset_cons ha
      have hamem : a ∈ Finset.cons a S' ha := Finset.mem_cons_self a S'
      have hS's := hJ S' hS'sub h'
      have hfull := hJ (Finset.cons a S' ha) (subset_refl _) ⟨a, hamem⟩
      rw [Finset.sum_cons] at hfull
      have hRadd := σ'.hRadd (x a) (∑ j ∈ S', x j) (hne a hamem) hS's.1 hfull.1
        (by rw [hw a hamem, hS's.2]) (by rw [hfull.2, hw a hamem])
      rw [hRadd, IH h' (fun j hj => hne j (hS'sub hj)) (fun j hj => hw j (hS'sub hj))
        (fun J hJs hJne => hJ J (hJs.trans hS'sub) hJne)]

/-- **The Hasse/Taylor nonvanishing at the recorded root** (corner mechanism 3's
payoff): if `ord_{X+C c₀} Ranch = μ` exactly and `c₀ ≠ 0`, the μ-th Taylor
coefficient of `Ranch·X^{s0}` at `−c₀` is nonzero — displayed as the explicit
binomial digit sum `Σ_k pat k·(−c₀)^k·C(s0+k, μ) ≠ 0`. -/
private lemma v9c_taylor_ne {K : Type*} [Field K] (c₀ : K) (hc₀ : c₀ ≠ 0)
    (Ranch : Polynomial K) (μ s0 wSide : ℕ) (pat : ℕ → K)
    (hRanch : Ranch = ∑ k ∈ Finset.range (wSide + 1),
      Polynomial.C (pat k) * Polynomial.X ^ k)
    (hOrd : OrdPsiPoly (Polynomial.X + Polynomial.C c₀) Ranch μ) :
    ∑ k ∈ Finset.range (wSide + 1),
      pat k * (-c₀) ^ k * (((s0 + k).choose μ : ℕ) : K) ≠ 0 := by
  classical
  set r : K := -c₀ with hrdef
  have hr : r ≠ 0 := neg_ne_zero.mpr hc₀
  obtain ⟨⟨Q, hQ⟩, hnot⟩ := hOrd
  set P : Polynomial K := Ranch * Polynomial.X ^ s0 with hPdef
  have hQr : Q.eval r ≠ 0 := by
    intro h
    apply hnot
    have hdvd : (Polynomial.X - Polynomial.C r) ∣ Q := Polynomial.dvd_iff_isRoot.mpr h
    have hψeq : Polynomial.X - Polynomial.C r = Polynomial.X + Polynomial.C c₀ := by
      rw [hrdef, map_neg, sub_neg_eq_add]
    rw [hψeq] at hdvd
    rw [hQ, pow_succ]
    exact mul_dvd_mul_left _ hdvd
  have htaylorψ : Polynomial.taylor r (Polynomial.X + Polynomial.C c₀) = Polynomial.X := by
    rw [Polynomial.taylor_apply, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      hrdef, map_neg]
    ring
  have htayP : (Polynomial.taylor r P).coeff μ = Q.eval r * r ^ s0 := by
    have h1 : Polynomial.taylor r P
        = Polynomial.X ^ μ
          * (Polynomial.taylor r Q * (Polynomial.X + Polynomial.C r) ^ s0) := by
      rw [hPdef, hQ]
      rw [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.mul_comp,
        Polynomial.pow_comp, Polynomial.pow_comp, Polynomial.X_comp]
      rw [← Polynomial.taylor_apply, ← Polynomial.taylor_apply, htaylorψ]
      ring
    have h2 := Polynomial.coeff_X_pow_mul
      (Polynomial.taylor r Q * (Polynomial.X + Polynomial.C r) ^ s0) μ 0
    rw [zero_add] at h2
    rw [h1, h2, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add,
      Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, zero_add]
  have hdegP : P.natDegree < s0 + (wSide + 1) := by
    have h1 : P.natDegree ≤ Ranch.natDegree + s0 := by
      rw [hPdef]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      simp [Polynomial.natDegree_X_pow]
    have h2 : Ranch.natDegree ≤ wSide := by
      rw [hRanch]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
      intro k hk
      refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
      have := Finset.mem_range.mp hk
      omega
    omega
  have hexp : (Polynomial.taylor r P).coeff μ
      = ∑ e ∈ Finset.range (s0 + (wSide + 1)),
          P.coeff e * (r ^ (e - μ) * ((e.choose μ : ℕ) : K)) := by
    rw [Polynomial.taylor_apply, Polynomial.comp_eq_sum_left,
      Polynomial.sum_over_range' P (fun n => by rw [map_zero, zero_mul]) _ hdegP,
      Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro e _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  have hexp2 : (Polynomial.taylor r P).coeff μ * r ^ μ
      = ∑ e ∈ Finset.range (s0 + (wSide + 1)),
          P.coeff e * r ^ e * ((e.choose μ : ℕ) : K) := by
    rw [hexp, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro e _
    rcases le_or_gt μ e with hle | hlt
    · calc P.coeff e * (r ^ (e - μ) * ((e.choose μ : ℕ) : K)) * r ^ μ
          = P.coeff e * ((r ^ (e - μ) * r ^ μ) * ((e.choose μ : ℕ) : K)) := by ring
        _ = P.coeff e * r ^ e * ((e.choose μ : ℕ) : K) := by
            rw [← pow_add, Nat.sub_add_cancel hle]; ring
    · simp [Nat.choose_eq_zero_of_lt hlt]
  have hPcoeff : ∀ e, P.coeff e = if s0 ≤ e then Ranch.coeff (e - s0) else 0 := by
    intro e
    rw [hPdef, Polynomial.coeff_mul_X_pow']
  have hRanchCoeff : ∀ k, k ≤ wSide → Ranch.coeff k = pat k := by
    intro k hk
    rw [hRanch, Polynomial.finset_sum_coeff, Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hbk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hbk h.symm),
        mul_zero]
    · intro hknot
      exact absurd (Finset.mem_range.mpr (by omega)) hknot
  have hshift : ∑ e ∈ Finset.range (s0 + (wSide + 1)),
        P.coeff e * r ^ e * ((e.choose μ : ℕ) : K)
      = r ^ s0 * ∑ k ∈ Finset.range (wSide + 1),
          pat k * r ^ k * (((s0 + k).choose μ : ℕ) : K) := by
    rw [v9c_sum_shift (fun e => P.coeff e * r ^ e * ((e.choose μ : ℕ) : K)) s0 (wSide + 1)
      (fun e he => by rw [hPcoeff e, if_neg (by omega)]; ring), Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [hPcoeff (s0 + k), if_pos (by omega), Nat.add_sub_cancel_left,
      hRanchCoeff k (by have := Finset.mem_range.mp hk; omega), pow_add]
    ring
  intro h0
  have hcontr := hexp2
  rw [hshift, htayP, h0, mul_zero] at hcontr
  exact mul_ne_zero (mul_ne_zero hQr (pow_ne_zero _ hr)) (pow_ne_zero _ hr) hcontr

/-- **The Hasse/Taylor VANISHING below the recorded order** (REV 6, the U22-E1 Box
counterpart of `v9c_taylor_ne`): if `ψ^μ ∣ Ranch` at `ψ = X + C c₀` with `c₀ ≠ 0`, every
Taylor coefficient of `Ranch·X^{s0}` at `−c₀` of index `j < μ` VANISHES — displayed as
the explicit binomial digit sum `Σ_k pat k·(−c₀)^k·C(s0+k, j) = 0`.  Only the
divisibility half of the ψ-order is consumed. -/
private lemma v9c_taylor_zero {K : Type*} [Field K] (c₀ : K) (hc₀ : c₀ ≠ 0)
    (Ranch : Polynomial K) (μ s0 wSide : ℕ) (pat : ℕ → K)
    (hRanch : Ranch = ∑ k ∈ Finset.range (wSide + 1),
      Polynomial.C (pat k) * Polynomial.X ^ k)
    (hdvd : (Polynomial.X + Polynomial.C c₀) ^ μ ∣ Ranch)
    (j : ℕ) (hj : j < μ) :
    ∑ k ∈ Finset.range (wSide + 1),
      pat k * (-c₀) ^ k * (((s0 + k).choose j : ℕ) : K) = 0 := by
  classical
  set r : K := -c₀ with hrdef
  have hr : r ≠ 0 := neg_ne_zero.mpr hc₀
  obtain ⟨Q, hQ⟩ := hdvd
  set P : Polynomial K := Ranch * Polynomial.X ^ s0 with hPdef
  have htaylorψ : Polynomial.taylor r (Polynomial.X + Polynomial.C c₀) = Polynomial.X := by
    rw [Polynomial.taylor_apply, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      hrdef, map_neg]
    ring
  have htayPj : (Polynomial.taylor r P).coeff j = 0 := by
    have h1 : Polynomial.taylor r P
        = Polynomial.X ^ μ
          * (Polynomial.taylor r Q * (Polynomial.X + Polynomial.C r) ^ s0) := by
      rw [hPdef, hQ]
      rw [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.mul_comp,
        Polynomial.pow_comp, Polynomial.pow_comp, Polynomial.X_comp]
      rw [← Polynomial.taylor_apply, ← Polynomial.taylor_apply, htaylorψ]
      ring
    rw [h1, Polynomial.X_pow_mul, Polynomial.coeff_mul_X_pow', if_neg (by omega)]
  have hdegP : P.natDegree < s0 + (wSide + 1) := by
    have h1 : P.natDegree ≤ Ranch.natDegree + s0 := by
      rw [hPdef]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      simp [Polynomial.natDegree_X_pow]
    have h2 : Ranch.natDegree ≤ wSide := by
      rw [hRanch]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
      intro k hk
      refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
      have := Finset.mem_range.mp hk
      omega
    omega
  have hexp : (Polynomial.taylor r P).coeff j
      = ∑ e ∈ Finset.range (s0 + (wSide + 1)),
          P.coeff e * (r ^ (e - j) * ((e.choose j : ℕ) : K)) := by
    rw [Polynomial.taylor_apply, Polynomial.comp_eq_sum_left,
      Polynomial.sum_over_range' P (fun n => by rw [map_zero, zero_mul]) _ hdegP,
      Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro e _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  have hexp2 : (Polynomial.taylor r P).coeff j * r ^ j
      = ∑ e ∈ Finset.range (s0 + (wSide + 1)),
          P.coeff e * r ^ e * ((e.choose j : ℕ) : K) := by
    rw [hexp, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro e _
    rcases le_or_gt j e with hle | hlt
    · calc P.coeff e * (r ^ (e - j) * ((e.choose j : ℕ) : K)) * r ^ j
          = P.coeff e * ((r ^ (e - j) * r ^ j) * ((e.choose j : ℕ) : K)) := by ring
        _ = P.coeff e * r ^ e * ((e.choose j : ℕ) : K) := by
            rw [← pow_add, Nat.sub_add_cancel hle]; ring
    · simp [Nat.choose_eq_zero_of_lt hlt]
  have hPcoeff : ∀ e, P.coeff e = if s0 ≤ e then Ranch.coeff (e - s0) else 0 := by
    intro e
    rw [hPdef, Polynomial.coeff_mul_X_pow']
  have hRanchCoeff : ∀ k, k ≤ wSide → Ranch.coeff k = pat k := by
    intro k hk
    rw [hRanch, Polynomial.finset_sum_coeff, Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hbk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hbk h.symm),
        mul_zero]
    · intro hknot
      exact absurd (Finset.mem_range.mpr (by omega)) hknot
  have hshift : ∑ e ∈ Finset.range (s0 + (wSide + 1)),
        P.coeff e * r ^ e * ((e.choose j : ℕ) : K)
      = r ^ s0 * ∑ k ∈ Finset.range (wSide + 1),
          pat k * r ^ k * (((s0 + k).choose j : ℕ) : K) := by
    rw [v9c_sum_shift (fun e => P.coeff e * r ^ e * ((e.choose j : ℕ) : K)) s0 (wSide + 1)
      (fun e he => by rw [hPcoeff e, if_neg (by omega)]; ring), Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [hPcoeff (s0 + k), if_pos (by omega), Nat.add_sub_cancel_left,
      hRanchCoeff k (by have := Finset.mem_range.mp hk; omega), pow_add]
    ring
  have h0 : r ^ s0 * (∑ k ∈ Finset.range (wSide + 1),
      pat k * r ^ k * (((s0 + k).choose j : ℕ) : K)) = 0 := by
    rw [← hshift, ← hexp2, htayPj, zero_mul]
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hr)

/-- **THE R3c CORNER CORE**: at a root-shaped `e·g = 1` transition over a
degree-1 frame, the recorded root-side data (SideReads (i)+(ii) + the lift +
`TransitionCoreL`'s `child_slotmin`/`child_dig_frame` + the node's ψ-order)
force the child development's vertex slot: `B μ ≠ 0` and
`σ'.w (B μ) = gam − μ·h★`.  SideReads(iii) is NOT consumed; no StageCore. -/
private theorem v9c_corner (σ σ' : Stage p F) (hstar : ℕ)
    (hdeg1 : σ.Φ.natDegree = 1)
    (hσ'e : σ'.e = 1) (hσ'h : σ'.h = hstar) (hσ's : σ'.s = 1) (hσ't : σ'.t = 0)
    (hcw : ∀ x, σ'.wPrev x = σ.w x)
    (hsm : IsSlotMinWeight σ'.w σ'.Φ 1 hstar σ.w)
    (t₀ : Polynomial ℤ_[p]) (ht₀ne : t₀ ≠ 0) (ht₀C : inC σ.Φ t₀)
    (ht₀w : σ.w t₀ = (hstar : ℤ))
    (c₀ : ↥σ.K)
    (ht₀R : σ.R t₀ = LaurentPolynomial.C c₀
      * LaurentPolynomial.T (- σ.t * σ.wPrev t₀))
    (hkey : σ'.Φ = σ.Φ + t₀)
    (zbar : Fˣ) (hc₀z : ((c₀ : ↥σ.K) : F) = - ((zbar : Fˣ) : F))
    (Ranch : Polynomial ↥σ.K) (μ s0 wSide : ℕ) (pat : ℕ → ↥σ.K) (gam : ℤ)
    (hRanch : Ranch = ∑ k ∈ Finset.range (wSide + 1),
      Polynomial.C (pat k) * Polynomial.X ^ k)
    (hpat0 : pat 0 ≠ 0)
    (hOrd : OrdPsiPoly (Polynomial.X + Polynomial.C c₀) Ranch μ)
    (mfun : ℤ → ℤ)
    (hmf : ∀ Bb : Polynomial ℤ_[p], Bb ≠ 0 → inC σ'.Φ Bb →
      ∃ c' : (↥σ'.K)ˣ,
        σ'.R Bb = LaurentPolynomial.C (c' : ↥σ'.K)
            * LaurentPolynomial.T (- σ'.t * σ.w Bb) ∧
        ((c' : ↥σ'.K) : F) = σ.digPrime zbar Bb
            * ((zbar ^ (mfun (σ.w Bb)) : Fˣ) : F))
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (B₀ : ℕ → Polynomial ℤ_[p]) (Nd₀ : ℕ) (hdev₀ : IsDevelopment σ.Φ f B₀ Nd₀)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (hdev : IsDevelopment σ'.Φ f B Nd)
    (hNd : μ < Nd)
    (hside1a : ∀ j : ℕ, j < Nd₀ → B₀ j ≠ 0 →
      gam ≤ σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ))
    (hside1b : ∀ j : ℕ, j < Nd₀ → B₀ j ≠ 0 →
      σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam →
      ∃ k : ℕ, k ≤ wSide ∧ j = s0 + k ∧ pat k ≠ 0)
    (hside2 : ∀ k : ℕ, k ≤ wSide → pat k ≠ 0 →
      B₀ (s0 + k) ≠ 0 ∧
      σ.w (B₀ (s0 + k)) + ((s0 + k : ℕ) : ℤ) * (hstar : ℤ) = gam ∧
      σ.R (B₀ (s0 + k)) = LaurentPolynomial.C (pat k) *
        LaurentPolynomial.T (- σ.t * σ.wPrev (B₀ (s0 + k)))) :
    B μ ≠ 0 ∧ σ'.w (B μ) = gam - (μ : ℤ) * (hstar : ℤ) := by
  classical
  -- ══ 0. frame bookkeeping ══
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦ'ne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  have hΦdeg : σ.Φ.degree = (1 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hΦne, hdeg1]; rfl
  have ht₀deg : t₀.degree ≤ 0 := by
    have h := ht₀C
    rw [inC, hΦdeg] at h
    rw [Polynomial.degree_eq_natDegree ht₀ne] at h ⊢
    have h1 : t₀.natDegree < 1 := by exact_mod_cast h
    have h2 : t₀.natDegree = 0 := by omega
    simp [h2]
  have hΦ'degEq : σ'.Φ.degree = σ.Φ.degree := by
    have hlt : t₀.degree < σ.Φ.degree := by
      rw [hΦdeg]
      exact lt_of_le_of_lt ht₀deg (by exact_mod_cast Nat.zero_lt_one)
    rw [hkey]
    exact Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hΦ'deg1 : σ'.Φ.natDegree = 1 := by
    have h := Polynomial.natDegree_eq_of_degree_eq hΦ'degEq
    rw [h, hdeg1]
  have hΦ'deg : σ'.Φ.degree = (1 : WithBot ℕ) := by rw [hΦ'degEq, hΦdeg]
  have hwconst : ∀ x : Polynomial ℤ_[p], x ≠ 0 → inC σ'.Φ x → σ'.w x = σ.w x := by
    intro x hx hxC
    rw [σ'.hStretch x hx hxC, hσ'e, hcw]
    push_cast
    ring
  have hconstOfP : ∀ x : Polynomial ℤ_[p], inC σ.Φ x → inC σ'.Φ x := by
    intro x hxC
    rw [inC, hΦ'degEq]; exact hxC
  have hconstOf : ∀ x : Polynomial ℤ_[p], inC σ'.Φ x → x.degree ≤ 0 := by
    intro x hxC
    rw [inC, hΦ'deg] at hxC
    rcases eq_or_ne x 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]; exact bot_le
    · rw [Polynomial.degree_eq_natDegree h0] at hxC ⊢
      have h1 : x.natDegree < 1 := by exact_mod_cast hxC
      have h2 : x.natDegree = 0 := by omega
      simp [h2]
  -- ══ 1. child weights of both keys; child residual of the parent key ══
  have hwΦ' : σ'.w σ'.Φ = (hstar : ℤ) := by rw [σ'.hwΦ, hσ'h]
  have ht₀C' : inC σ'.Φ t₀ := hconstOfP t₀ ht₀C
  have hwt₀' : σ'.w t₀ = (hstar : ℤ) := by rw [hwconst t₀ ht₀ne ht₀C', ht₀w]
  have hRΦ'key : σ'.R σ'.Φ = LaurentPolynomial.T 1 := by
    rw [σ'.hRΦ, hσ's]
  obtain ⟨dt, hdtR, hdtF⟩ := hmf t₀ ht₀ne ht₀C'
  have hdtR0 : σ'.R t₀ = LaurentPolynomial.C ((dt : ↥σ'.K)) := by
    rw [hdtR, hσ't]
    simp
  have hwΦpar : σ'.w σ.Φ = (hstar : ℤ) := by
    have hge : (hstar : ℤ) ≤ σ'.w σ.Φ := by
      have hsub : σ'.Φ + (-t₀) = σ.Φ := by rw [hkey]; ring
      have hult := σ'.hwult σ'.Φ (-t₀) hΦ'ne (neg_ne_zero.mpr ht₀ne)
        (by rw [hsub]; exact hΦne)
      rw [hsub, ResVal.w_neg σ' t₀ ht₀ne, hwt₀', hwΦ', min_self] at hult
      exact hult
    rcases lt_or_eq_of_le hge with hlt | heq
    · exfalso
      have hsum : t₀ + σ.Φ = σ'.Φ := by rw [hkey]; ring
      have hRe := σ'.hRlt t₀ σ.Φ ht₀ne hΦne (by rw [hsum]; exact hΦ'ne)
        (by rw [hwt₀']; exact hlt)
      rw [hsum, hRΦ'key, hdtR0] at hRe
      exact v9c_T1_ne_C _ hRe
    · exact heq.symm
  have hRΦpar : σ'.R σ.Φ
      = LaurentPolynomial.T 1 - LaurentPolynomial.C ((dt : ↥σ'.K)) := by
    have hsum : σ.Φ + t₀ = σ'.Φ := hkey.symm
    have hRadd := σ'.hRadd σ.Φ t₀ hΦne ht₀ne (by rw [hsum]; exact hΦ'ne)
      (by rw [hwΦpar, hwt₀']) (by rw [hsum, hwΦ', hwΦpar])
    rw [hsum, hRΦ'key, hdtR0] at hRadd
    exact eq_sub_of_add_eq hRadd.symm
  -- ══ 2. the root-side index sets ══
  set Kp : Finset ℕ := (Finset.range (wSide + 1)).filter (fun k => pat k ≠ 0)
    with hKpdef
  have h0Kp : 0 ∈ Kp := by
    rw [hKpdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpat0⟩
  set Sall : Finset ℕ := (Finset.range Nd₀).filter (fun j => B₀ j ≠ 0) with hSalldef
  have hSide : ∀ k ∈ Kp, B₀ (s0 + k) ≠ 0 ∧
      σ.w (B₀ (s0 + k)) = gam - ((s0 + k : ℕ) : ℤ) * (hstar : ℤ) ∧
      σ.R (B₀ (s0 + k)) = LaurentPolynomial.C (pat k) *
        LaurentPolynomial.T (- σ.t * σ.wPrev (B₀ (s0 + k))) := by
    intro k hk
    rw [hKpdef] at hk
    obtain ⟨hkr, hkp⟩ := Finset.mem_filter.mp hk
    obtain ⟨h1, h2, h3⟩ := hside2 k (by have := Finset.mem_range.mp hkr; omega) hkp
    exact ⟨h1, by linarith [h2], h3⟩
  have hmemS : ∀ k ∈ Kp, s0 + k ∈ Sall := by
    intro k hk
    obtain ⟨h1, -, -⟩ := hSide k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, h1⟩
    by_contra hge
    exact h1 (hdev₀.2.1 _ (by omega))
  set E : Finset ℕ := Sall.filter
    (fun j => σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam) with hEdef
  set O : Finset ℕ := Sall.filter
    (fun j => ¬ (σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam)) with hOdef
  have hs0E : s0 + 0 ∈ E := by
    obtain ⟨-, h2, -⟩ := hSide 0 h0Kp
    exact Finset.mem_filter.mpr ⟨hmemS 0 h0Kp, by rw [h2]; ring⟩
  have hEeq : E = Kp.image (fun k => s0 + k) := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjS, hjeq⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjr, hjne⟩ := Finset.mem_filter.mp hjS
      obtain ⟨k, hkW, hjk, hkp⟩ := hside1b j (Finset.mem_range.mp hjr) hjne hjeq
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hkp⟩, hjk.symm⟩
    · intro hj
      obtain ⟨k, hk, hjk⟩ := Finset.mem_image.mp hj
      subst hjk
      obtain ⟨h1, h2, -⟩ := hSide k hk
      exact Finset.mem_filter.mpr ⟨hmemS k hk, by rw [h2]; ring⟩
  -- ══ 3. σ'.w f = gam ══
  have hfSall : f = ∑ j ∈ Sall, B₀ j * σ.Φ ^ j := by
    rw [hdev₀.2.2, hSalldef]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j _ hne0 h0
    exact hne0 (by rw [h0, zero_mul])
  have hwf : σ'.w f = gam := by
    rw [hfSall]
    refine v9c_slotmin σ σ' hstar hdeg1 t₀ ht₀ne ht₀C ht₀w hkey hsm Sall
      ⟨s0 + 0, (Finset.mem_filter.mp hs0E).1⟩ B₀
      (fun j hj => (Finset.mem_filter.mp hj).2)
      (fun j _ => hdev₀.1 j) gam
      (fun j hj => hside1a j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
        (Finset.mem_filter.mp hj).2) ?_
    exact ⟨s0 + 0, (Finset.mem_filter.mp hs0E).1, (Finset.mem_filter.mp hs0E).2⟩
  -- ══ 4. the digit chooser ══
  have hdigE : ∀ Bb : Polynomial ℤ_[p], Bb ≠ 0 → inC σ'.Φ Bb →
      ∃ cc : ↥σ'.K, cc ≠ 0 ∧ σ'.R Bb = LaurentPolynomial.C cc ∧
        (cc : F) = σ.digPrime zbar Bb * ((zbar ^ (mfun (σ.w Bb)) : Fˣ) : F) := by
    intro Bb h1 h2
    obtain ⟨c', hR, hF⟩ := hmf Bb h1 h2
    refine ⟨(c' : ↥σ'.K), c'.ne_zero, ?_, hF⟩
    rw [hR, hσ't]
    simp
  have hbbEx : ∀ k : ℕ, ∃ cc : ↥σ'.K, k ∈ Kp →
      (cc ≠ 0 ∧ σ'.R (B₀ (s0 + k)) = LaurentPolynomial.C cc ∧
        (cc : F) = σ.digPrime zbar (B₀ (s0 + k))
          * ((zbar ^ (mfun (σ.w (B₀ (s0 + k)))) : Fˣ) : F)) := by
    intro k
    by_cases hk : k ∈ Kp
    · obtain ⟨h1, -, -⟩ := hSide k hk
      obtain ⟨cc, hcc⟩ := hdigE (B₀ (s0 + k)) h1 (hconstOfP _ (hdev₀.1 _))
      exact ⟨cc, fun _ => hcc⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose bb hbb using hbbEx
  -- ══ 5. the child development's minimizing slots; reduce to μ ∈ M ══
  set NZ : Finset ℕ := (Finset.range Nd).filter (fun m => B m ≠ 0) with hNZdef
  set M : Finset ℕ := NZ.filter
    (fun m => σ.w (B m) + (m : ℤ) * (hstar : ℤ) = gam) with hMdef
  set MC : Finset ℕ := NZ.filter
    (fun m => ¬ (σ.w (B m) + (m : ℤ) * (hstar : ℤ) = gam)) with hMCdef
  suffices hμM : μ ∈ M by
    rw [hMdef] at hμM
    obtain ⟨hμNZ, hμw⟩ := Finset.mem_filter.mp hμM
    obtain ⟨-, hμne⟩ := Finset.mem_filter.mp hμNZ
    refine ⟨hμne, ?_⟩
    rw [hwconst (B μ) hμne (hdev.1 μ)]
    linarith [hμw]
  by_contra hμM
  -- membership unpackers
  have hMr : M ⊆ Finset.range Nd := fun m hm => by
    rw [hMdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
  have hMne0 : ∀ m ∈ M, B m ≠ 0 := fun m hm => by
    rw [hMdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  have hMw : ∀ m ∈ M, σ.w (B m) + (m : ℤ) * (hstar : ℤ) = gam := fun m hm => by
    rw [hMdef] at hm
    exact (Finset.mem_filter.mp hm).2
  have hMCr : MC ⊆ Finset.range Nd := fun m hm => by
    rw [hMCdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
  have hMCne0 : ∀ m ∈ MC, B m ≠ 0 := fun m hm => by
    rw [hMCdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  -- every occupied slot's read value is ≥ gam (LOW of the full development)
  obtain ⟨hlowf, -⟩ := hsm f B Nd hf hdev
  have hallge : ∀ m, m < Nd → B m ≠ 0 →
      gam ≤ σ.w (B m) + (m : ℤ) * (hstar : ℤ) := by
    intro m hmr hmne
    have h := hlowf m hmr hmne
    simp only at h
    push_cast at h
    linarith [hwf, h]
  -- f splits over NZ = M ∪ MC
  have hNZne : NZ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hNZ
    apply hf
    rw [hdev.2.2]
    refine Finset.sum_eq_zero ?_
    intro m hmr
    rcases eq_or_ne (B m) 0 with h0 | h0
    · rw [h0, zero_mul]
    · have hmem : m ∈ NZ := by
        rw [hNZdef]
        exact Finset.mem_filter.mpr ⟨hmr, h0⟩
      rw [hNZ] at hmem
      exact absurd hmem (Finset.notMem_empty m)
  have hfNZ : f = ∑ m ∈ NZ, B m * σ'.Φ ^ m := by
    rw [hdev.2.2, hNZdef]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro m _ hne0 h0
    exact hne0 (by rw [h0, zero_mul])
  have hfsplit : f = (∑ m ∈ M, B m * σ'.Φ ^ m) + ∑ m ∈ MC, B m * σ'.Φ ^ m := by
    rw [hfNZ, hMdef, hMCdef]
    exact (Finset.sum_filter_add_sum_filter_not NZ _ _).symm
  -- per-element and sub-sum weights on the M side
  have hMterm : ∀ m ∈ M, B m * σ'.Φ ^ m ≠ 0 ∧ σ'.w (B m * σ'.Φ ^ m) = gam := by
    intro m hm
    have hmne := hMne0 m hm
    have hne' : B m * σ'.Φ ^ m ≠ 0 := mul_ne_zero hmne (pow_ne_zero _ hΦ'ne)
    refine ⟨hne', ?_⟩
    rw [σ'.hwmul _ _ hmne (pow_ne_zero _ hΦ'ne), ResVal.w_pow σ' _ hΦ'ne, hwΦ',
      hwconst (B m) hmne (hdev.1 m)]
    linarith [hMw m hm]
  have hMsub : ∀ J ⊆ M, J.Nonempty →
      (∑ m ∈ J, B m * σ'.Φ ^ m) ≠ 0 ∧ σ'.w (∑ m ∈ J, B m * σ'.Φ ^ m) = gam := by
    intro J hJM hJne
    obtain ⟨hne0, hlow', m₂, hm₂J, hm₂eq⟩ := v9c_subsum σ σ' hstar hΦ'deg1 hsm B Nd
      hdev.1 J (fun m hm => hMr (hJM hm)) hJne (fun m hm => hMne0 m (hJM hm))
    refine ⟨hne0, ?_⟩
    rw [hm₂eq]
    exact hMw m₂ (hJM hm₂J)
  -- the MC side sits strictly above gam
  have hMC_gt : MC.Nonempty →
      (∑ m ∈ MC, B m * σ'.Φ ^ m) ≠ 0 ∧
      gam < σ'.w (∑ m ∈ MC, B m * σ'.Φ ^ m) := by
    intro hMCne
    obtain ⟨hne0, hlow', m₂, hm₂, hm₂eq⟩ := v9c_subsum σ σ' hstar hΦ'deg1 hsm B Nd
      hdev.1 MC hMCr hMCne hMCne0
    refine ⟨hne0, ?_⟩
    rw [hm₂eq]
    have h1 := hallge m₂ (Finset.mem_range.mp (hMCr hm₂)) (hMCne0 m₂ hm₂)
    have h2 : ¬ (σ.w (B m₂) + (m₂ : ℤ) * (hstar : ℤ) = gam) := by
      rw [hMCdef] at hm₂
      exact (Finset.mem_filter.mp hm₂).2
    exact lt_of_le_of_ne h1 (fun h => h2 h.symm)
  have hMne : M.Nonempty := by
    by_contra hMe
    rw [Finset.not_nonempty_iff_eq_empty] at hMe
    have hMCeq : MC = NZ := by
      rw [hMCdef]
      refine Finset.filter_true_of_mem ?_
      intro m hm heq
      have hmem : m ∈ M := by
        rw [hMdef]
        exact Finset.mem_filter.mpr ⟨hm, heq⟩
      rw [hMe] at hmem
      exact absurd hmem (Finset.notMem_empty m)
    have hMCne : MC.Nonempty := by rw [hMCeq]; exact hNZne
    obtain ⟨-, hgt⟩ := hMC_gt hMCne
    have : f = ∑ m ∈ MC, B m * σ'.Φ ^ m := by
      rw [hfsplit, hMe, Finset.sum_empty, zero_add]
    rw [← this, hwf] at hgt
    exact lt_irrefl _ hgt
  -- M-indexed digits
  have hbbMEx : ∀ m : ℕ, ∃ cc : ↥σ'.K, m ∈ M →
      σ'.R (B m) = LaurentPolynomial.C cc := by
    intro m
    by_cases hm : m ∈ M
    · obtain ⟨cc, -, hccR, -⟩ := hdigE (B m) (hMne0 m hm) (hdev.1 m)
      exact ⟨cc, fun _ => hccR⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose bbM hbbM using hbbMEx
  -- ══ 6. σ'.R f, computed on the child development (LHS) ══
  have hRfM : σ'.R f = ∑ m ∈ M, σ'.R (B m * σ'.Φ ^ m) := by
    have hchain := v9c_Rsum σ' gam (fun m => B m * σ'.Φ ^ m) M hMne
      (fun m hm => (hMterm m hm).1) (fun m hm => (hMterm m hm).2) hMsub
    rcases MC.eq_empty_or_nonempty with hMC0 | hMCne
    · rw [hfsplit, hMC0, Finset.sum_empty, add_zero, hchain]
    · obtain ⟨hne0, hgt⟩ := hMC_gt hMCne
      have hMsum := hMsub M (subset_refl M) hMne
      have hRlt := σ'.hRlt (∑ m ∈ M, B m * σ'.Φ ^ m) (∑ m ∈ MC, B m * σ'.Φ ^ m)
        hMsum.1 hne0 (by rw [← hfsplit]; exact hf) (by rw [hMsum.2]; exact hgt)
      rw [hfsplit, hRlt, hchain]
  have hRterm : ∀ m ∈ M, σ'.R (B m * σ'.Φ ^ m)
      = Polynomial.toLaurent (Polynomial.C (bbM m) * Polynomial.X ^ m) := by
    intro m hm
    rw [σ'.hRmul _ _ (hMne0 m hm) (pow_ne_zero _ hΦ'ne), ResVal.R_pow σ' _ hΦ'ne,
      hRΦ'key, hbbM m hm, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
      LaurentPolynomial.T_pow, mul_one]
  have hLHS : σ'.R f = Polynomial.toLaurent
      (∑ m ∈ M, Polynomial.C (bbM m) * Polynomial.X ^ m) := by
    rw [hRfM, map_sum]
    exact Finset.sum_congr rfl hRterm
  -- ══ 7. σ'.R f, computed on the root development (RHS) ══
  have hEterm : ∀ j ∈ E, B₀ j * σ.Φ ^ j ≠ 0 ∧ σ'.w (B₀ j * σ.Φ ^ j) = gam := by
    intro j hj
    rw [hEdef] at hj
    obtain ⟨hjS, hjeq⟩ := Finset.mem_filter.mp hj
    obtain ⟨-, hjne⟩ := Finset.mem_filter.mp hjS
    have hne' : B₀ j * σ.Φ ^ j ≠ 0 := mul_ne_zero hjne (pow_ne_zero _ hΦne)
    refine ⟨hne', ?_⟩
    rw [σ'.hwmul _ _ hjne (pow_ne_zero _ hΦne), ResVal.w_pow σ' _ hΦne, hwΦpar,
      hwconst (B₀ j) hjne (hconstOfP _ (hdev₀.1 j))]
    linarith [hjeq]
  have hEne0 : ∀ j ∈ E, B₀ j ≠ 0 := fun j hj => by
    rw [hEdef, hSalldef] at hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have hEw : ∀ j ∈ E, σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam := fun j hj => by
    rw [hEdef] at hj
    exact (Finset.mem_filter.mp hj).2
  have hEsub : ∀ J ⊆ E, J.Nonempty →
      (∑ j ∈ J, B₀ j * σ.Φ ^ j) ≠ 0 ∧ σ'.w (∑ j ∈ J, B₀ j * σ.Φ ^ j) = gam := by
    intro J hJE hJne
    constructor
    · exact v9c_sum_ne_zero σ.Φ σ.hmonic hdeg1 J hJne B₀
        (fun j hj => hEne0 j (hJE hj))
        (fun j hj => hconstOf _ (hconstOfP _ (hdev₀.1 j)))
    · refine v9c_slotmin σ σ' hstar hdeg1 t₀ ht₀ne ht₀C ht₀w hkey hsm J hJne B₀
        (fun j hj => hEne0 j (hJE hj)) (fun j _ => hdev₀.1 j) gam
        (fun j hj => le_of_eq (hEw j (hJE hj)).symm) ?_
      obtain ⟨j₀, hj₀⟩ := hJne
      exact ⟨j₀, hj₀, hEw j₀ (hJE hj₀)⟩
  have hOne0 : ∀ j ∈ O, B₀ j ≠ 0 := fun j hj => by
    rw [hOdef, hSalldef] at hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have hO_gt : O.Nonempty →
      (∑ j ∈ O, B₀ j * σ.Φ ^ j) ≠ 0 ∧ gam < σ'.w (∑ j ∈ O, B₀ j * σ.Φ ^ j) := by
    intro hOne
    have hOSall : O ⊆ Sall := by rw [hOdef]; exact Finset.filter_subset _ _
    have hOval : ∀ j ∈ O, gam < σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) := by
      intro j hj
      have h1 := hside1a j (Finset.mem_range.mp (Finset.mem_filter.mp (hOSall hj)).1)
        (hOne0 j hj)
      have h2 : ¬ (σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam) := by
        rw [hOdef] at hj
        exact (Finset.mem_filter.mp hj).2
      exact lt_of_le_of_ne h1 (fun h => h2 h.symm)
    have himne : ((O.image (fun j => σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ)))).Nonempty :=
      hOne.image _
    obtain ⟨j₀, hj₀O, hj₀⟩ := Finset.mem_image.mp (Finset.min'_mem _ himne)
    constructor
    · exact v9c_sum_ne_zero σ.Φ σ.hmonic hdeg1 O hOne B₀ hOne0
        (fun j hj => hconstOf _ (hconstOfP _ (hdev₀.1 j)))
    · have hval := v9c_slotmin σ σ' hstar hdeg1 t₀ ht₀ne ht₀C ht₀w hkey hsm O hOne B₀
        hOne0 (fun j _ => hdev₀.1 j)
        ((O.image (fun j => σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ))).min' himne)
        (fun j hj => Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj))
        ⟨j₀, hj₀O, hj₀⟩
      rw [hval, ← hj₀]
      exact hOval j₀ hj₀O
  have hfEO : f = (∑ j ∈ E, B₀ j * σ.Φ ^ j) + ∑ j ∈ O, B₀ j * σ.Φ ^ j := by
    rw [hfSall, hEdef, hOdef]
    exact (Finset.sum_filter_add_sum_filter_not Sall _ _).symm
  have hEne : E.Nonempty := ⟨s0 + 0, hs0E⟩
  have hRfE : σ'.R f = ∑ j ∈ E, σ'.R (B₀ j * σ.Φ ^ j) := by
    have hchain := v9c_Rsum σ' gam (fun j => B₀ j * σ.Φ ^ j) E hEne
      (fun j hj => (hEterm j hj).1) (fun j hj => (hEterm j hj).2) hEsub
    rcases O.eq_empty_or_nonempty with hO0 | hOne
    · rw [hfEO, hO0, Finset.sum_empty, add_zero, hchain]
    · obtain ⟨hne0, hgt⟩ := hO_gt hOne
      have hEsum := hEsub E (subset_refl E) hEne
      have hRlt := σ'.hRlt (∑ j ∈ E, B₀ j * σ.Φ ^ j) (∑ j ∈ O, B₀ j * σ.Φ ^ j)
        hEsum.1 hne0 (by rw [← hfEO]; exact hf) (by rw [hEsum.2]; exact hgt)
      rw [hfEO, hRlt, hchain]
  have hRtermE : ∀ k ∈ Kp, σ'.R (B₀ (s0 + k) * σ.Φ ^ (s0 + k))
      = Polynomial.toLaurent (Polynomial.C (bb k)
        * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) := by
    intro k hk
    obtain ⟨h1, -, -⟩ := hSide k hk
    obtain ⟨-, hbkR, -⟩ := hbb k hk
    rw [σ'.hRmul _ _ h1 (pow_ne_zero _ hΦne), ResVal.R_pow σ' _ hΦne, hRΦpar, hbkR,
      map_mul, map_pow, map_sub, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      Polynomial.toLaurent_C]
  have hRHS : σ'.R f = Polynomial.toLaurent
      (∑ k ∈ Kp, Polynomial.C (bb k)
        * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) := by
    calc σ'.R f = ∑ j ∈ E, σ'.R (B₀ j * σ.Φ ^ j) := hRfE
      _ = ∑ k ∈ Kp, σ'.R (B₀ (s0 + k) * σ.Φ ^ (s0 + k)) := by
          rw [hEeq]
          exact Finset.sum_image (fun k _ k' _ h => by omega)
      _ = ∑ k ∈ Kp, Polynomial.toLaurent (Polynomial.C (bb k)
            * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) :=
          Finset.sum_congr rfl hRtermE
      _ = Polynomial.toLaurent (∑ k ∈ Kp, Polynomial.C (bb k)
            * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) :=
          (map_sum _ _ _).symm
  -- ══ 8. the (★) polynomial identity and its μ-coefficient ══
  have hpoly : (∑ m ∈ M, Polynomial.C (bbM m) * Polynomial.X ^ m)
      = ∑ k ∈ Kp, Polynomial.C (bb k)
        * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k) :=
    Polynomial.toLaurent_injective (hLHS.symm.trans hRHS)
  have hcoefL : (∑ m ∈ M, Polynomial.C (bbM m) * Polynomial.X ^ m).coeff μ = 0 := by
    rw [Polynomial.finset_sum_coeff]
    refine Finset.sum_eq_zero ?_
    intro m hm
    have hne : ¬ (μ = m) := by
      intro h
      rw [h] at hμM
      exact hμM hm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
  have hcoefR' : ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - μ)
      * (((s0 + k).choose μ : ℕ) : ↥σ'.K)) = 0 := by
    rw [← hcoefL, hpoly, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Polynomial.coeff_C_mul, sub_eq_add_neg, ← Polynomial.C_neg,
      Polynomial.coeff_X_add_C_pow]
  -- clear the natural subtraction: multiply by (−dt)^μ
  have hstep2 : ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k)
      * (((s0 + k).choose μ : ℕ) : ↥σ'.K)) = 0 := by
    have hmul : (∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - μ)
        * (((s0 + k).choose μ : ℕ) : ↥σ'.K))) * (- ((dt : ↥σ'.K))) ^ μ = 0 := by
      rw [hcoefR', zero_mul]
    rw [Finset.sum_mul] at hmul
    calc ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k)
          * (((s0 + k).choose μ : ℕ) : ↥σ'.K))
        = ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - μ)
            * (((s0 + k).choose μ : ℕ) : ↥σ'.K)) * (- ((dt : ↥σ'.K))) ^ μ := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rcases le_or_gt μ (s0 + k) with hle | hlt
          · calc bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k)
                  * (((s0 + k).choose μ : ℕ) : ↥σ'.K))
                = bb k * (((- ((dt : ↥σ'.K))) ^ (s0 + k - μ)
                    * (- ((dt : ↥σ'.K))) ^ μ) * (((s0 + k).choose μ : ℕ) : ↥σ'.K)) := by
                  rw [← pow_add, Nat.sub_add_cancel hle]
              _ = bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - μ)
                    * (((s0 + k).choose μ : ℕ) : ↥σ'.K)) * (- ((dt : ↥σ'.K))) ^ μ := by
                  ring
          · simp [Nat.choose_eq_zero_of_lt hlt]
      _ = 0 := hmul
  -- ══ 9. the position collapse and the mfun-free per-k digit identity ══
  have hwPrevEq : ∀ k ∈ Kp, σ.wPrev (B₀ (s0 + k)) + (k : ℤ) * σ.wPrev t₀
      = σ.wPrev (B₀ (s0 + 0)) := by
    intro k hk
    obtain ⟨h1, hw1, -⟩ := hSide k hk
    obtain ⟨h10, hw10, -⟩ := hSide 0 h0Kp
    have hs1 : σ.w (B₀ (s0 + k)) = (σ.e : ℤ) * σ.wPrev (B₀ (s0 + k)) :=
      σ.hStretch _ h1 (hdev₀.1 _)
    have hs2 : σ.w t₀ = (σ.e : ℤ) * σ.wPrev t₀ := σ.hStretch _ ht₀ne ht₀C
    have hs3 : σ.w (B₀ (s0 + 0)) = (σ.e : ℤ) * σ.wPrev (B₀ (s0 + 0)) :=
      σ.hStretch _ h10 (hdev₀.1 _)
    have he1 : (1 : ℤ) ≤ (σ.e : ℤ) := by exact_mod_cast σ.he
    have hkey2 : (σ.e : ℤ) * (σ.wPrev (B₀ (s0 + k)) + (k : ℤ) * σ.wPrev t₀
        - σ.wPrev (B₀ (s0 + 0))) = 0 := by
      have hval : σ.w (B₀ (s0 + k)) + (k : ℤ) * σ.w t₀ - σ.w (B₀ (s0 + 0)) = 0 := by
        rw [hw1, ht₀w, hw10]
        push_cast
        ring
      calc (σ.e : ℤ) * (σ.wPrev (B₀ (s0 + k)) + (k : ℤ) * σ.wPrev t₀
            - σ.wPrev (B₀ (s0 + 0)))
          = σ.w (B₀ (s0 + k)) + (k : ℤ) * σ.w t₀ - σ.w (B₀ (s0 + 0)) := by
            rw [hs1, hs2, hs3]; ring
        _ = 0 := hval
    rcases mul_eq_zero.mp hkey2 with h | h
    · exact absurd h (by omega)
    · linarith [h]
  have hKEY : ∀ k ∈ Kp,
      ((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k * ((pat 0 : ↥σ.K) : F)
      = ((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k := by
    intro k hk
    obtain ⟨h1, hw1, hR1⟩ := hSide k hk
    obtain ⟨h10, hw10, hR10⟩ := hSide 0 h0Kp
    obtain ⟨hbkne, hbkR, hbkF⟩ := hbb k hk
    obtain ⟨hb0ne, hb0R, hb0F⟩ := hbb 0 h0Kp
    have ht₀kne : t₀ ^ k ≠ 0 := pow_ne_zero _ ht₀ne
    have hXkne : B₀ (s0 + k) * t₀ ^ k ≠ 0 := mul_ne_zero h1 ht₀kne
    have hXkC : inC σ'.Φ (B₀ (s0 + k) * t₀ ^ k) := by
      rw [inC, hΦ'deg]
      have hd1 : (B₀ (s0 + k)).degree ≤ 0 := hconstOf _ (hconstOfP _ (hdev₀.1 _))
      have hd2 : (t₀ ^ k).degree ≤ 0 := by
        have ht0 : t₀.degree = 0 :=
          le_antisymm ht₀deg (Polynomial.zero_le_degree_iff.mpr ht₀ne)
        rw [Polynomial.degree_pow, ht0, smul_zero]
      calc (B₀ (s0 + k) * t₀ ^ k).degree
          ≤ (B₀ (s0 + k)).degree + (t₀ ^ k).degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + 0 := add_le_add hd1 hd2
        _ = 0 := add_zero 0
        _ < 1 := by exact_mod_cast Nat.zero_lt_one
    have hwXk : σ.w (B₀ (s0 + k) * t₀ ^ k) = σ.w (B₀ (s0 + 0)) := by
      rw [σ.hwmul _ _ h1 ht₀kne, ResVal.w_pow σ _ ht₀ne, ht₀w, hw1, hw10]
      push_cast
      ring
    obtain ⟨cX, hcXne, hcXR, hcXF⟩ := hdigE (B₀ (s0 + k) * t₀ ^ k) hXkne hXkC
    have hcXval : cX = bb k * (dt : ↥σ'.K) ^ k := by
      apply v9c_C_inj
      rw [← hcXR, σ'.hRmul _ _ h1 ht₀kne, ResVal.R_pow σ' _ ht₀ne, hbkR, hdtR0,
        ← map_pow, ← map_mul]
    have hdigXk : σ.digPrime zbar (B₀ (s0 + k) * t₀ ^ k)
        = σ.digPrime zbar (B₀ (s0 + k)) * (σ.digPrime zbar t₀) ^ k := by
      unfold Stage.digPrime
      rw [σ.hRmul _ _ h1 ht₀kne, ResVal.R_pow σ _ ht₀ne, map_mul, map_pow]
    have hdig1 : σ.digPrime zbar (B₀ (s0 + k))
        = ((pat k : ↥σ.K) : F)
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F) := by
      unfold Stage.digPrime
      rw [hR1, LaurentPolynomial.eval₂_C_mul_T]
      simp
    have hdigt : σ.digPrime zbar t₀
        = ((c₀ : ↥σ.K) : F) * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) := by
      unfold Stage.digPrime
      rw [ht₀R, LaurentPolynomial.eval₂_C_mul_T]
      simp
    have hdig0 : σ.digPrime zbar (B₀ (s0 + 0))
        = ((pat 0 : ↥σ.K) : F)
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) := by
      unfold Stage.digPrime
      rw [hR10, LaurentPolynomial.eval₂_C_mul_T]
      simp
    have hq : - σ.t * σ.wPrev (B₀ (s0 + k)) + (- σ.t * σ.wPrev t₀) * (k : ℤ)
        = - σ.t * σ.wPrev (B₀ (s0 + 0)) := by
      linear_combination (- σ.t) * hwPrevEq k hk
    have hzv : ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
        * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) ^ k
        = ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) := by
      have h2 : ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k)))
          * (zbar ^ (- σ.t * σ.wPrev t₀)) ^ k : Fˣ) : F)
          = ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
            * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) ^ k := by
        rw [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [← h2]
      congr 1
      rw [← zpow_natCast (zbar ^ (- σ.t * σ.wPrev t₀)) k, ← zpow_mul, ← zpow_add, hq]
    have hcross : (cX : F)
        * σ.digPrime zbar (B₀ (s0 + 0))
        = ((bb 0 : ↥σ'.K) : F) * σ.digPrime zbar (B₀ (s0 + k) * t₀ ^ k) := by
      rw [hcXF, hb0F, hwXk]
      ring
    rw [hcXval] at hcross
    push_cast at hcross
    rw [hdigXk, hdig1, hdigt, hdig0] at hcross
    have hZ0ne : ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) ≠ 0 :=
      Units.ne_zero _
    refine mul_right_cancel₀ hZ0ne ?_
    calc ((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k * ((pat 0 : ↥σ.K) : F)
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F)
        = (((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k)
          * (((pat 0 : ↥σ.K) : F)
            * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F)) := by ring
      _ = ((bb 0 : ↥σ'.K) : F)
          * (((pat k : ↥σ.K) : F)
              * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
            * (((c₀ : ↥σ.K) : F)
              * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F)) ^ k) := hcross
      _ = ((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k
          * (((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
            * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) ^ k) := by
          rw [mul_pow]; ring
      _ = ((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) := by rw [hzv]
  -- ══ 10. cast to F, apply the KEY, cancel units ══
  have hstep3 : ∑ k ∈ Kp, ((bb k : ↥σ'.K) : F)
      * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose μ : ℕ) : F)) = 0 := by
    have hc := congrArg (fun y : ↥σ'.K => (y : F)) hstep2
    push_cast at hc
    convert hc using 2 with k hk
  have hterm10 : ∀ k ∈ Kp,
      ((bb k : ↥σ'.K) : F)
        * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose μ : ℕ) : F))
        * ((pat 0 : ↥σ.K) : F)
      = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
        * (((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
            * (((s0 + k).choose μ : ℕ) : F)) := by
    intro k hk
    have hK := hKEY k hk
    have hcz : (-1 : F) * ((c₀ : ↥σ.K) : F) = ((zbar : Fˣ) : F) := by
      rw [hc₀z]; ring
    calc ((bb k : ↥σ'.K) : F)
          * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose μ : ℕ) : F))
          * ((pat 0 : ↥σ.K) : F)
        = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * (-1 : F) ^ k)
          * ((((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k * ((pat 0 : ↥σ.K) : F))
            * (((s0 + k).choose μ : ℕ) : F)) := by
          rw [neg_pow, pow_add, pow_add]
          ring
      _ = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * (-1 : F) ^ k)
          * ((((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k)
            * (((s0 + k).choose μ : ℕ) : F)) := by rw [hK]
      _ = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
          * (((pat k : ↥σ.K) : F) * (((-1 : F)) * ((c₀ : ↥σ.K) : F)) ^ k
            * (((s0 + k).choose μ : ℕ) : F)) := by
          rw [mul_pow]
          ring
      _ = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
          * (((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
            * (((s0 + k).choose μ : ℕ) : F)) := by rw [hcz]
  have hsum0 : ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
      * (∑ k ∈ Kp, ((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
          * (((s0 + k).choose μ : ℕ) : F)) = 0 := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ Kp, ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
          * (((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
              * (((s0 + k).choose μ : ℕ) : F))
        = ∑ k ∈ Kp, ((bb k : ↥σ'.K) : F)
            * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose μ : ℕ) : F))
            * ((pat 0 : ↥σ.K) : F) :=
          (Finset.sum_congr rfl (fun k hk => (hterm10 k hk).symm))
      _ = (∑ k ∈ Kp, ((bb k : ↥σ'.K) : F)
            * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose μ : ℕ) : F)))
            * ((pat 0 : ↥σ.K) : F) := (Finset.sum_mul _ _ _).symm
      _ = 0 := by rw [hstep3, zero_mul]
  have hdtFne : ((dt : ↥σ'.K) : F) ≠ 0 := by
    intro h
    exact dt.ne_zero (by exact_mod_cast h)
  have hbb0Fne : ((bb 0 : ↥σ'.K) : F) ≠ 0 := by
    obtain ⟨hb0ne, -, -⟩ := hbb 0 h0Kp
    intro h
    exact hb0ne (by exact_mod_cast h)
  have hCne : ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ hdtFne)) hbb0Fne
  have hHasse : ∑ k ∈ Kp, ((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
      * (((s0 + k).choose μ : ℕ) : F) = 0 :=
    (mul_eq_zero.mp hsum0).resolve_left hCne
  -- ══ 11. transfer to K and contradict the Taylor nonvanishing ══
  have hHasseR : ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
      * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose μ : ℕ) : F) = 0 := by
    have hfilter : ∑ k ∈ (Finset.range (wSide + 1)).filter (fun k => pat k ≠ 0),
        ((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose μ : ℕ) : F)
        = ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
            * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose μ : ℕ) : F) := by
      refine Finset.sum_filter_of_ne ?_
      intro k _ hne0 hpk
      exact hne0 (by rw [hpk]; simp)
    rw [← hfilter, ← hKpdef]
    exact hHasse
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    rw [h] at hc₀z
    push_cast at hc₀z
    exact zbar.ne_zero (by
      have := hc₀z.symm
      rw [neg_eq_zero] at this
      exact this)
  have hKsum : (((∑ k ∈ Finset.range (wSide + 1),
      pat k * (- c₀) ^ k * (((s0 + k).choose μ : ℕ) : ↥σ.K)) : ↥σ.K) : F) = 0 := by
    push_cast
    calc ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
          * (- ((c₀ : ↥σ.K) : F)) ^ k * (((s0 + k).choose μ : ℕ) : F)
        = ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
          * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose μ : ℕ) : F) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hc₀z, neg_neg]
      _ = 0 := hHasseR
  have hKzero : ∑ k ∈ Finset.range (wSide + 1),
      pat k * (- c₀) ^ k * (((s0 + k).choose μ : ℕ) : ↥σ.K) = 0 := by
    exact_mod_cast hKsum
  exact v9c_taylor_ne c₀ hc₀ne Ranch μ s0 wSide pat hRanch hOrd hKzero

/-- **THE U22-E1 CORNER BOX** (REV 6, the strict sibling of `v9c_corner`): at a
root-shaped `e·g = 1` transition over a degree-1 frame, the recorded root-side data
force every child-development slot STRICTLY BELOW the vertex STRICTLY ABOVE the
transported side value: `j < μ` and `B j ≠ 0` give `gam − j·h★ < σ'.w (B j)`.
Same pool as `v9c_corner` (SideReads (i)+(ii) + the lift + `child_slotmin`/
`child_dig_frame` + the node's ψ-order; SideReads(iii) NOT consumed; no StageCore);
the endgame swaps `v9c_taylor_ne` (nonvanishing AT μ) for `v9c_taylor_zero`
(vanishing BELOW μ): a minimizing slot `j < μ` would pin its nonzero digit to the
`j`-th Taylor coefficient of `X^{s0}·Ranch` at the recorded root — which vanishes. -/
private theorem v9c_cornerBox (σ σ' : Stage p F) (hstar : ℕ)
    (hdeg1 : σ.Φ.natDegree = 1)
    (hσ'e : σ'.e = 1) (hσ'h : σ'.h = hstar) (hσ's : σ'.s = 1) (hσ't : σ'.t = 0)
    (hcw : ∀ x, σ'.wPrev x = σ.w x)
    (hsm : IsSlotMinWeight σ'.w σ'.Φ 1 hstar σ.w)
    (t₀ : Polynomial ℤ_[p]) (ht₀ne : t₀ ≠ 0) (ht₀C : inC σ.Φ t₀)
    (ht₀w : σ.w t₀ = (hstar : ℤ))
    (c₀ : ↥σ.K)
    (ht₀R : σ.R t₀ = LaurentPolynomial.C c₀
      * LaurentPolynomial.T (- σ.t * σ.wPrev t₀))
    (hkey : σ'.Φ = σ.Φ + t₀)
    (zbar : Fˣ) (hc₀z : ((c₀ : ↥σ.K) : F) = - ((zbar : Fˣ) : F))
    (Ranch : Polynomial ↥σ.K) (μ s0 wSide : ℕ) (pat : ℕ → ↥σ.K) (gam : ℤ)
    (hRanch : Ranch = ∑ k ∈ Finset.range (wSide + 1),
      Polynomial.C (pat k) * Polynomial.X ^ k)
    (hpat0 : pat 0 ≠ 0)
    (hOrd : OrdPsiPoly (Polynomial.X + Polynomial.C c₀) Ranch μ)
    (mfun : ℤ → ℤ)
    (hmf : ∀ Bb : Polynomial ℤ_[p], Bb ≠ 0 → inC σ'.Φ Bb →
      ∃ c' : (↥σ'.K)ˣ,
        σ'.R Bb = LaurentPolynomial.C (c' : ↥σ'.K)
            * LaurentPolynomial.T (- σ'.t * σ.w Bb) ∧
        ((c' : ↥σ'.K) : F) = σ.digPrime zbar Bb
            * ((zbar ^ (mfun (σ.w Bb)) : Fˣ) : F))
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (B₀ : ℕ → Polynomial ℤ_[p]) (Nd₀ : ℕ) (hdev₀ : IsDevelopment σ.Φ f B₀ Nd₀)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (hdev : IsDevelopment σ'.Φ f B Nd)
    (j : ℕ) (hjμ : j < μ) (hjne : B j ≠ 0)
    (hside1a : ∀ j : ℕ, j < Nd₀ → B₀ j ≠ 0 →
      gam ≤ σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ))
    (hside1b : ∀ j : ℕ, j < Nd₀ → B₀ j ≠ 0 →
      σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam →
      ∃ k : ℕ, k ≤ wSide ∧ j = s0 + k ∧ pat k ≠ 0)
    (hside2 : ∀ k : ℕ, k ≤ wSide → pat k ≠ 0 →
      B₀ (s0 + k) ≠ 0 ∧
      σ.w (B₀ (s0 + k)) + ((s0 + k : ℕ) : ℤ) * (hstar : ℤ) = gam ∧
      σ.R (B₀ (s0 + k)) = LaurentPolynomial.C (pat k) *
        LaurentPolynomial.T (- σ.t * σ.wPrev (B₀ (s0 + k)))) :
    gam - (j : ℤ) * (hstar : ℤ) < σ'.w (B j) := by
  classical
  -- ══ 0. frame bookkeeping ══
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦ'ne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  have hΦdeg : σ.Φ.degree = (1 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hΦne, hdeg1]; rfl
  have ht₀deg : t₀.degree ≤ 0 := by
    have h := ht₀C
    rw [inC, hΦdeg] at h
    rw [Polynomial.degree_eq_natDegree ht₀ne] at h ⊢
    have h1 : t₀.natDegree < 1 := by exact_mod_cast h
    have h2 : t₀.natDegree = 0 := by omega
    simp [h2]
  have hΦ'degEq : σ'.Φ.degree = σ.Φ.degree := by
    have hlt : t₀.degree < σ.Φ.degree := by
      rw [hΦdeg]
      exact lt_of_le_of_lt ht₀deg (by exact_mod_cast Nat.zero_lt_one)
    rw [hkey]
    exact Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hΦ'deg1 : σ'.Φ.natDegree = 1 := by
    have h := Polynomial.natDegree_eq_of_degree_eq hΦ'degEq
    rw [h, hdeg1]
  have hΦ'deg : σ'.Φ.degree = (1 : WithBot ℕ) := by rw [hΦ'degEq, hΦdeg]
  have hwconst : ∀ x : Polynomial ℤ_[p], x ≠ 0 → inC σ'.Φ x → σ'.w x = σ.w x := by
    intro x hx hxC
    rw [σ'.hStretch x hx hxC, hσ'e, hcw]
    push_cast
    ring
  have hconstOfP : ∀ x : Polynomial ℤ_[p], inC σ.Φ x → inC σ'.Φ x := by
    intro x hxC
    rw [inC, hΦ'degEq]; exact hxC
  have hconstOf : ∀ x : Polynomial ℤ_[p], inC σ'.Φ x → x.degree ≤ 0 := by
    intro x hxC
    rw [inC, hΦ'deg] at hxC
    rcases eq_or_ne x 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]; exact bot_le
    · rw [Polynomial.degree_eq_natDegree h0] at hxC ⊢
      have h1 : x.natDegree < 1 := by exact_mod_cast hxC
      have h2 : x.natDegree = 0 := by omega
      simp [h2]
  -- ══ 1. child weights of both keys; child residual of the parent key ══
  have hwΦ' : σ'.w σ'.Φ = (hstar : ℤ) := by rw [σ'.hwΦ, hσ'h]
  have ht₀C' : inC σ'.Φ t₀ := hconstOfP t₀ ht₀C
  have hwt₀' : σ'.w t₀ = (hstar : ℤ) := by rw [hwconst t₀ ht₀ne ht₀C', ht₀w]
  have hRΦ'key : σ'.R σ'.Φ = LaurentPolynomial.T 1 := by
    rw [σ'.hRΦ, hσ's]
  obtain ⟨dt, hdtR, hdtF⟩ := hmf t₀ ht₀ne ht₀C'
  have hdtR0 : σ'.R t₀ = LaurentPolynomial.C ((dt : ↥σ'.K)) := by
    rw [hdtR, hσ't]
    simp
  have hwΦpar : σ'.w σ.Φ = (hstar : ℤ) := by
    have hge : (hstar : ℤ) ≤ σ'.w σ.Φ := by
      have hsub : σ'.Φ + (-t₀) = σ.Φ := by rw [hkey]; ring
      have hult := σ'.hwult σ'.Φ (-t₀) hΦ'ne (neg_ne_zero.mpr ht₀ne)
        (by rw [hsub]; exact hΦne)
      rw [hsub, ResVal.w_neg σ' t₀ ht₀ne, hwt₀', hwΦ', min_self] at hult
      exact hult
    rcases lt_or_eq_of_le hge with hlt | heq
    · exfalso
      have hsum : t₀ + σ.Φ = σ'.Φ := by rw [hkey]; ring
      have hRe := σ'.hRlt t₀ σ.Φ ht₀ne hΦne (by rw [hsum]; exact hΦ'ne)
        (by rw [hwt₀']; exact hlt)
      rw [hsum, hRΦ'key, hdtR0] at hRe
      exact v9c_T1_ne_C _ hRe
    · exact heq.symm
  have hRΦpar : σ'.R σ.Φ
      = LaurentPolynomial.T 1 - LaurentPolynomial.C ((dt : ↥σ'.K)) := by
    have hsum : σ.Φ + t₀ = σ'.Φ := hkey.symm
    have hRadd := σ'.hRadd σ.Φ t₀ hΦne ht₀ne (by rw [hsum]; exact hΦ'ne)
      (by rw [hwΦpar, hwt₀']) (by rw [hsum, hwΦ', hwΦpar])
    rw [hsum, hRΦ'key, hdtR0] at hRadd
    exact eq_sub_of_add_eq hRadd.symm
  -- ══ 2. the root-side index sets ══
  set Kp : Finset ℕ := (Finset.range (wSide + 1)).filter (fun k => pat k ≠ 0)
    with hKpdef
  have h0Kp : 0 ∈ Kp := by
    rw [hKpdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpat0⟩
  set Sall : Finset ℕ := (Finset.range Nd₀).filter (fun j => B₀ j ≠ 0) with hSalldef
  have hSide : ∀ k ∈ Kp, B₀ (s0 + k) ≠ 0 ∧
      σ.w (B₀ (s0 + k)) = gam - ((s0 + k : ℕ) : ℤ) * (hstar : ℤ) ∧
      σ.R (B₀ (s0 + k)) = LaurentPolynomial.C (pat k) *
        LaurentPolynomial.T (- σ.t * σ.wPrev (B₀ (s0 + k))) := by
    intro k hk
    rw [hKpdef] at hk
    obtain ⟨hkr, hkp⟩ := Finset.mem_filter.mp hk
    obtain ⟨h1, h2, h3⟩ := hside2 k (by have := Finset.mem_range.mp hkr; omega) hkp
    exact ⟨h1, by linarith [h2], h3⟩
  have hmemS : ∀ k ∈ Kp, s0 + k ∈ Sall := by
    intro k hk
    obtain ⟨h1, -, -⟩ := hSide k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, h1⟩
    by_contra hge
    exact h1 (hdev₀.2.1 _ (by omega))
  set E : Finset ℕ := Sall.filter
    (fun j => σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam) with hEdef
  set O : Finset ℕ := Sall.filter
    (fun j => ¬ (σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam)) with hOdef
  have hs0E : s0 + 0 ∈ E := by
    obtain ⟨-, h2, -⟩ := hSide 0 h0Kp
    exact Finset.mem_filter.mpr ⟨hmemS 0 h0Kp, by rw [h2]; ring⟩
  have hEeq : E = Kp.image (fun k => s0 + k) := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjS, hjeq⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjr, hjne⟩ := Finset.mem_filter.mp hjS
      obtain ⟨k, hkW, hjk, hkp⟩ := hside1b j (Finset.mem_range.mp hjr) hjne hjeq
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hkp⟩, hjk.symm⟩
    · intro hj
      obtain ⟨k, hk, hjk⟩ := Finset.mem_image.mp hj
      subst hjk
      obtain ⟨h1, h2, -⟩ := hSide k hk
      exact Finset.mem_filter.mpr ⟨hmemS k hk, by rw [h2]; ring⟩
  -- ══ 3. σ'.w f = gam ══
  have hfSall : f = ∑ j ∈ Sall, B₀ j * σ.Φ ^ j := by
    rw [hdev₀.2.2, hSalldef]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j _ hne0 h0
    exact hne0 (by rw [h0, zero_mul])
  have hwf : σ'.w f = gam := by
    rw [hfSall]
    refine v9c_slotmin σ σ' hstar hdeg1 t₀ ht₀ne ht₀C ht₀w hkey hsm Sall
      ⟨s0 + 0, (Finset.mem_filter.mp hs0E).1⟩ B₀
      (fun j hj => (Finset.mem_filter.mp hj).2)
      (fun j _ => hdev₀.1 j) gam
      (fun j hj => hside1a j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
        (Finset.mem_filter.mp hj).2) ?_
    exact ⟨s0 + 0, (Finset.mem_filter.mp hs0E).1, (Finset.mem_filter.mp hs0E).2⟩
  -- ══ 4. the digit chooser ══
  have hdigE : ∀ Bb : Polynomial ℤ_[p], Bb ≠ 0 → inC σ'.Φ Bb →
      ∃ cc : ↥σ'.K, cc ≠ 0 ∧ σ'.R Bb = LaurentPolynomial.C cc ∧
        (cc : F) = σ.digPrime zbar Bb * ((zbar ^ (mfun (σ.w Bb)) : Fˣ) : F) := by
    intro Bb h1 h2
    obtain ⟨c', hR, hF⟩ := hmf Bb h1 h2
    refine ⟨(c' : ↥σ'.K), c'.ne_zero, ?_, hF⟩
    rw [hR, hσ't]
    simp
  have hbbEx : ∀ k : ℕ, ∃ cc : ↥σ'.K, k ∈ Kp →
      (cc ≠ 0 ∧ σ'.R (B₀ (s0 + k)) = LaurentPolynomial.C cc ∧
        (cc : F) = σ.digPrime zbar (B₀ (s0 + k))
          * ((zbar ^ (mfun (σ.w (B₀ (s0 + k)))) : Fˣ) : F)) := by
    intro k
    by_cases hk : k ∈ Kp
    · obtain ⟨h1, -, -⟩ := hSide k hk
      obtain ⟨cc, hcc⟩ := hdigE (B₀ (s0 + k)) h1 (hconstOfP _ (hdev₀.1 _))
      exact ⟨cc, fun _ => hcc⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose bb hbb using hbbEx
  -- ══ 5. the child development's minimizing slots; strictness at the Box slot ══
  set NZ : Finset ℕ := (Finset.range Nd).filter (fun m => B m ≠ 0) with hNZdef
  set M : Finset ℕ := NZ.filter
    (fun m => σ.w (B m) + (m : ℤ) * (hstar : ℤ) = gam) with hMdef
  set MC : Finset ℕ := NZ.filter
    (fun m => ¬ (σ.w (B m) + (m : ℤ) * (hstar : ℤ) = gam)) with hMCdef
  -- every occupied slot's read value is ≥ gam (LOW of the full development)
  obtain ⟨hlowf, -⟩ := hsm f B Nd hf hdev
  have hallge : ∀ m, m < Nd → B m ≠ 0 →
      gam ≤ σ.w (B m) + (m : ℤ) * (hstar : ℤ) := by
    intro m hmr hmne
    have h := hlowf m hmr hmne
    simp only at h
    push_cast at h
    linarith [hwf, h]
  have hjNd : j < Nd := by
    by_contra hge
    exact hjne (hdev.2.1 j (by omega))
  rw [hwconst (B j) hjne (hdev.1 j)]
  by_contra hcon
  push_neg at hcon
  -- hcon : σ.w (B j) ≤ gam − j·h★ ; with the LOW bound this pins j ∈ M
  have hjM : j ∈ M := by
    rw [hMdef]
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [hNZdef]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjNd, hjne⟩
    · have h1 := hallge j hjNd hjne
      linarith [h1, hcon]
  -- membership unpackers
  have hMr : M ⊆ Finset.range Nd := fun m hm => by
    rw [hMdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
  have hMne0 : ∀ m ∈ M, B m ≠ 0 := fun m hm => by
    rw [hMdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  have hMw : ∀ m ∈ M, σ.w (B m) + (m : ℤ) * (hstar : ℤ) = gam := fun m hm => by
    rw [hMdef] at hm
    exact (Finset.mem_filter.mp hm).2
  have hMCr : MC ⊆ Finset.range Nd := fun m hm => by
    rw [hMCdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
  have hMCne0 : ∀ m ∈ MC, B m ≠ 0 := fun m hm => by
    rw [hMCdef, hNZdef] at hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  -- f splits over NZ = M ∪ MC
  have hNZne : NZ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hNZ
    apply hf
    rw [hdev.2.2]
    refine Finset.sum_eq_zero ?_
    intro m hmr
    rcases eq_or_ne (B m) 0 with h0 | h0
    · rw [h0, zero_mul]
    · have hmem : m ∈ NZ := by
        rw [hNZdef]
        exact Finset.mem_filter.mpr ⟨hmr, h0⟩
      rw [hNZ] at hmem
      exact absurd hmem (Finset.notMem_empty m)
  have hfNZ : f = ∑ m ∈ NZ, B m * σ'.Φ ^ m := by
    rw [hdev.2.2, hNZdef]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro m _ hne0 h0
    exact hne0 (by rw [h0, zero_mul])
  have hfsplit : f = (∑ m ∈ M, B m * σ'.Φ ^ m) + ∑ m ∈ MC, B m * σ'.Φ ^ m := by
    rw [hfNZ, hMdef, hMCdef]
    exact (Finset.sum_filter_add_sum_filter_not NZ _ _).symm
  -- per-element and sub-sum weights on the M side
  have hMterm : ∀ m ∈ M, B m * σ'.Φ ^ m ≠ 0 ∧ σ'.w (B m * σ'.Φ ^ m) = gam := by
    intro m hm
    have hmne := hMne0 m hm
    have hne' : B m * σ'.Φ ^ m ≠ 0 := mul_ne_zero hmne (pow_ne_zero _ hΦ'ne)
    refine ⟨hne', ?_⟩
    rw [σ'.hwmul _ _ hmne (pow_ne_zero _ hΦ'ne), ResVal.w_pow σ' _ hΦ'ne, hwΦ',
      hwconst (B m) hmne (hdev.1 m)]
    linarith [hMw m hm]
  have hMsub : ∀ J ⊆ M, J.Nonempty →
      (∑ m ∈ J, B m * σ'.Φ ^ m) ≠ 0 ∧ σ'.w (∑ m ∈ J, B m * σ'.Φ ^ m) = gam := by
    intro J hJM hJne
    obtain ⟨hne0, hlow', m₂, hm₂J, hm₂eq⟩ := v9c_subsum σ σ' hstar hΦ'deg1 hsm B Nd
      hdev.1 J (fun m hm => hMr (hJM hm)) hJne (fun m hm => hMne0 m (hJM hm))
    refine ⟨hne0, ?_⟩
    rw [hm₂eq]
    exact hMw m₂ (hJM hm₂J)
  -- the MC side sits strictly above gam
  have hMC_gt : MC.Nonempty →
      (∑ m ∈ MC, B m * σ'.Φ ^ m) ≠ 0 ∧
      gam < σ'.w (∑ m ∈ MC, B m * σ'.Φ ^ m) := by
    intro hMCne
    obtain ⟨hne0, hlow', m₂, hm₂, hm₂eq⟩ := v9c_subsum σ σ' hstar hΦ'deg1 hsm B Nd
      hdev.1 MC hMCr hMCne hMCne0
    refine ⟨hne0, ?_⟩
    rw [hm₂eq]
    have h1 := hallge m₂ (Finset.mem_range.mp (hMCr hm₂)) (hMCne0 m₂ hm₂)
    have h2 : ¬ (σ.w (B m₂) + (m₂ : ℤ) * (hstar : ℤ) = gam) := by
      rw [hMCdef] at hm₂
      exact (Finset.mem_filter.mp hm₂).2
    exact lt_of_le_of_ne h1 (fun h => h2 h.symm)
  have hMne : M.Nonempty := ⟨j, hjM⟩
  -- M-indexed digits
  have hbbMEx : ∀ m : ℕ, ∃ cc : ↥σ'.K, m ∈ M →
      σ'.R (B m) = LaurentPolynomial.C cc := by
    intro m
    by_cases hm : m ∈ M
    · obtain ⟨cc, -, hccR, -⟩ := hdigE (B m) (hMne0 m hm) (hdev.1 m)
      exact ⟨cc, fun _ => hccR⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose bbM hbbM using hbbMEx
  -- ══ 6. σ'.R f, computed on the child development (LHS) ══
  have hRfM : σ'.R f = ∑ m ∈ M, σ'.R (B m * σ'.Φ ^ m) := by
    have hchain := v9c_Rsum σ' gam (fun m => B m * σ'.Φ ^ m) M hMne
      (fun m hm => (hMterm m hm).1) (fun m hm => (hMterm m hm).2) hMsub
    rcases MC.eq_empty_or_nonempty with hMC0 | hMCne
    · rw [hfsplit, hMC0, Finset.sum_empty, add_zero, hchain]
    · obtain ⟨hne0, hgt⟩ := hMC_gt hMCne
      have hMsum := hMsub M (subset_refl M) hMne
      have hRlt := σ'.hRlt (∑ m ∈ M, B m * σ'.Φ ^ m) (∑ m ∈ MC, B m * σ'.Φ ^ m)
        hMsum.1 hne0 (by rw [← hfsplit]; exact hf) (by rw [hMsum.2]; exact hgt)
      rw [hfsplit, hRlt, hchain]
  have hRterm : ∀ m ∈ M, σ'.R (B m * σ'.Φ ^ m)
      = Polynomial.toLaurent (Polynomial.C (bbM m) * Polynomial.X ^ m) := by
    intro m hm
    rw [σ'.hRmul _ _ (hMne0 m hm) (pow_ne_zero _ hΦ'ne), ResVal.R_pow σ' _ hΦ'ne,
      hRΦ'key, hbbM m hm, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
      LaurentPolynomial.T_pow, mul_one]
  have hLHS : σ'.R f = Polynomial.toLaurent
      (∑ m ∈ M, Polynomial.C (bbM m) * Polynomial.X ^ m) := by
    rw [hRfM, map_sum]
    exact Finset.sum_congr rfl hRterm
  -- ══ 7. σ'.R f, computed on the root development (RHS) ══
  have hEterm : ∀ j ∈ E, B₀ j * σ.Φ ^ j ≠ 0 ∧ σ'.w (B₀ j * σ.Φ ^ j) = gam := by
    intro j hj
    rw [hEdef] at hj
    obtain ⟨hjS, hjeq⟩ := Finset.mem_filter.mp hj
    obtain ⟨-, hjne⟩ := Finset.mem_filter.mp hjS
    have hne' : B₀ j * σ.Φ ^ j ≠ 0 := mul_ne_zero hjne (pow_ne_zero _ hΦne)
    refine ⟨hne', ?_⟩
    rw [σ'.hwmul _ _ hjne (pow_ne_zero _ hΦne), ResVal.w_pow σ' _ hΦne, hwΦpar,
      hwconst (B₀ j) hjne (hconstOfP _ (hdev₀.1 j))]
    linarith [hjeq]
  have hEne0 : ∀ j ∈ E, B₀ j ≠ 0 := fun j hj => by
    rw [hEdef, hSalldef] at hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have hEw : ∀ j ∈ E, σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam := fun j hj => by
    rw [hEdef] at hj
    exact (Finset.mem_filter.mp hj).2
  have hEsub : ∀ J ⊆ E, J.Nonempty →
      (∑ j ∈ J, B₀ j * σ.Φ ^ j) ≠ 0 ∧ σ'.w (∑ j ∈ J, B₀ j * σ.Φ ^ j) = gam := by
    intro J hJE hJne
    constructor
    · exact v9c_sum_ne_zero σ.Φ σ.hmonic hdeg1 J hJne B₀
        (fun j hj => hEne0 j (hJE hj))
        (fun j hj => hconstOf _ (hconstOfP _ (hdev₀.1 j)))
    · refine v9c_slotmin σ σ' hstar hdeg1 t₀ ht₀ne ht₀C ht₀w hkey hsm J hJne B₀
        (fun j hj => hEne0 j (hJE hj)) (fun j _ => hdev₀.1 j) gam
        (fun j hj => le_of_eq (hEw j (hJE hj)).symm) ?_
      obtain ⟨j₀, hj₀⟩ := hJne
      exact ⟨j₀, hj₀, hEw j₀ (hJE hj₀)⟩
  have hOne0 : ∀ j ∈ O, B₀ j ≠ 0 := fun j hj => by
    rw [hOdef, hSalldef] at hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have hO_gt : O.Nonempty →
      (∑ j ∈ O, B₀ j * σ.Φ ^ j) ≠ 0 ∧ gam < σ'.w (∑ j ∈ O, B₀ j * σ.Φ ^ j) := by
    intro hOne
    have hOSall : O ⊆ Sall := by rw [hOdef]; exact Finset.filter_subset _ _
    have hOval : ∀ j ∈ O, gam < σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) := by
      intro j hj
      have h1 := hside1a j (Finset.mem_range.mp (Finset.mem_filter.mp (hOSall hj)).1)
        (hOne0 j hj)
      have h2 : ¬ (σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ) = gam) := by
        rw [hOdef] at hj
        exact (Finset.mem_filter.mp hj).2
      exact lt_of_le_of_ne h1 (fun h => h2 h.symm)
    have himne : ((O.image (fun j => σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ)))).Nonempty :=
      hOne.image _
    obtain ⟨j₀, hj₀O, hj₀⟩ := Finset.mem_image.mp (Finset.min'_mem _ himne)
    constructor
    · exact v9c_sum_ne_zero σ.Φ σ.hmonic hdeg1 O hOne B₀ hOne0
        (fun j hj => hconstOf _ (hconstOfP _ (hdev₀.1 j)))
    · have hval := v9c_slotmin σ σ' hstar hdeg1 t₀ ht₀ne ht₀C ht₀w hkey hsm O hOne B₀
        hOne0 (fun j _ => hdev₀.1 j)
        ((O.image (fun j => σ.w (B₀ j) + (j : ℤ) * (hstar : ℤ))).min' himne)
        (fun j hj => Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj))
        ⟨j₀, hj₀O, hj₀⟩
      rw [hval, ← hj₀]
      exact hOval j₀ hj₀O
  have hfEO : f = (∑ j ∈ E, B₀ j * σ.Φ ^ j) + ∑ j ∈ O, B₀ j * σ.Φ ^ j := by
    rw [hfSall, hEdef, hOdef]
    exact (Finset.sum_filter_add_sum_filter_not Sall _ _).symm
  have hEne : E.Nonempty := ⟨s0 + 0, hs0E⟩
  have hRfE : σ'.R f = ∑ j ∈ E, σ'.R (B₀ j * σ.Φ ^ j) := by
    have hchain := v9c_Rsum σ' gam (fun j => B₀ j * σ.Φ ^ j) E hEne
      (fun j hj => (hEterm j hj).1) (fun j hj => (hEterm j hj).2) hEsub
    rcases O.eq_empty_or_nonempty with hO0 | hOne
    · rw [hfEO, hO0, Finset.sum_empty, add_zero, hchain]
    · obtain ⟨hne0, hgt⟩ := hO_gt hOne
      have hEsum := hEsub E (subset_refl E) hEne
      have hRlt := σ'.hRlt (∑ j ∈ E, B₀ j * σ.Φ ^ j) (∑ j ∈ O, B₀ j * σ.Φ ^ j)
        hEsum.1 hne0 (by rw [← hfEO]; exact hf) (by rw [hEsum.2]; exact hgt)
      rw [hfEO, hRlt, hchain]
  have hRtermE : ∀ k ∈ Kp, σ'.R (B₀ (s0 + k) * σ.Φ ^ (s0 + k))
      = Polynomial.toLaurent (Polynomial.C (bb k)
        * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) := by
    intro k hk
    obtain ⟨h1, -, -⟩ := hSide k hk
    obtain ⟨-, hbkR, -⟩ := hbb k hk
    rw [σ'.hRmul _ _ h1 (pow_ne_zero _ hΦne), ResVal.R_pow σ' _ hΦne, hRΦpar, hbkR,
      map_mul, map_pow, map_sub, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      Polynomial.toLaurent_C]
  have hRHS : σ'.R f = Polynomial.toLaurent
      (∑ k ∈ Kp, Polynomial.C (bb k)
        * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) := by
    calc σ'.R f = ∑ j ∈ E, σ'.R (B₀ j * σ.Φ ^ j) := hRfE
      _ = ∑ k ∈ Kp, σ'.R (B₀ (s0 + k) * σ.Φ ^ (s0 + k)) := by
          rw [hEeq]
          exact Finset.sum_image (fun k _ k' _ h => by omega)
      _ = ∑ k ∈ Kp, Polynomial.toLaurent (Polynomial.C (bb k)
            * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) :=
          Finset.sum_congr rfl hRtermE
      _ = Polynomial.toLaurent (∑ k ∈ Kp, Polynomial.C (bb k)
            * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k)) :=
          (map_sum _ _ _).symm
  -- ══ 8. the (★) polynomial identity and its j-coefficient (the pinned digit) ══
  have hpoly : (∑ m ∈ M, Polynomial.C (bbM m) * Polynomial.X ^ m)
      = ∑ k ∈ Kp, Polynomial.C (bb k)
        * (Polynomial.X - Polynomial.C ((dt : ↥σ'.K))) ^ (s0 + k) :=
    Polynomial.toLaurent_injective (hLHS.symm.trans hRHS)
  have hbbMjne : bbM j ≠ 0 := by
    obtain ⟨cc, hccne, hccR, -⟩ := hdigE (B j) (hMne0 j hjM) (hdev.1 j)
    have hceq : cc = bbM j := v9c_C_inj (hccR.symm.trans (hbbM j hjM))
    rw [← hceq]
    exact hccne
  have hcoefL : (∑ m ∈ M, Polynomial.C (bbM m) * Polynomial.X ^ m).coeff j = bbM j := by
    rw [Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single j
      (fun m _ hmj => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          if_neg (fun hh => hmj hh.symm), mul_zero])
      (fun hjnot => absurd hjM hjnot)]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  have hcoefR' : ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - j)
      * (((s0 + k).choose j : ℕ) : ↥σ'.K)) = bbM j := by
    rw [← hcoefL, hpoly, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Polynomial.coeff_C_mul, sub_eq_add_neg, ← Polynomial.C_neg,
      Polynomial.coeff_X_add_C_pow]
  -- clear the natural subtraction: multiply by (−dt)^j
  have hstep2 : ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k)
      * (((s0 + k).choose j : ℕ) : ↥σ'.K)) = bbM j * (- ((dt : ↥σ'.K))) ^ j := by
    have hmul : (∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - j)
        * (((s0 + k).choose j : ℕ) : ↥σ'.K))) * (- ((dt : ↥σ'.K))) ^ j
        = bbM j * (- ((dt : ↥σ'.K))) ^ j := by
      rw [hcoefR']
    rw [Finset.sum_mul] at hmul
    calc ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k)
          * (((s0 + k).choose j : ℕ) : ↥σ'.K))
        = ∑ k ∈ Kp, bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - j)
            * (((s0 + k).choose j : ℕ) : ↥σ'.K)) * (- ((dt : ↥σ'.K))) ^ j := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rcases le_or_gt j (s0 + k) with hle | hlt
          · calc bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k)
                  * (((s0 + k).choose j : ℕ) : ↥σ'.K))
                = bb k * (((- ((dt : ↥σ'.K))) ^ (s0 + k - j)
                    * (- ((dt : ↥σ'.K))) ^ j) * (((s0 + k).choose j : ℕ) : ↥σ'.K)) := by
                  rw [← pow_add, Nat.sub_add_cancel hle]
              _ = bb k * ((- ((dt : ↥σ'.K))) ^ (s0 + k - j)
                    * (((s0 + k).choose j : ℕ) : ↥σ'.K)) * (- ((dt : ↥σ'.K))) ^ j := by
                  ring
          · simp [Nat.choose_eq_zero_of_lt hlt]
      _ = bbM j * (- ((dt : ↥σ'.K))) ^ j := hmul
  -- ══ 9. the position collapse and the mfun-free per-k digit identity ══
  have hwPrevEq : ∀ k ∈ Kp, σ.wPrev (B₀ (s0 + k)) + (k : ℤ) * σ.wPrev t₀
      = σ.wPrev (B₀ (s0 + 0)) := by
    intro k hk
    obtain ⟨h1, hw1, -⟩ := hSide k hk
    obtain ⟨h10, hw10, -⟩ := hSide 0 h0Kp
    have hs1 : σ.w (B₀ (s0 + k)) = (σ.e : ℤ) * σ.wPrev (B₀ (s0 + k)) :=
      σ.hStretch _ h1 (hdev₀.1 _)
    have hs2 : σ.w t₀ = (σ.e : ℤ) * σ.wPrev t₀ := σ.hStretch _ ht₀ne ht₀C
    have hs3 : σ.w (B₀ (s0 + 0)) = (σ.e : ℤ) * σ.wPrev (B₀ (s0 + 0)) :=
      σ.hStretch _ h10 (hdev₀.1 _)
    have he1 : (1 : ℤ) ≤ (σ.e : ℤ) := by exact_mod_cast σ.he
    have hkey2 : (σ.e : ℤ) * (σ.wPrev (B₀ (s0 + k)) + (k : ℤ) * σ.wPrev t₀
        - σ.wPrev (B₀ (s0 + 0))) = 0 := by
      have hval : σ.w (B₀ (s0 + k)) + (k : ℤ) * σ.w t₀ - σ.w (B₀ (s0 + 0)) = 0 := by
        rw [hw1, ht₀w, hw10]
        push_cast
        ring
      calc (σ.e : ℤ) * (σ.wPrev (B₀ (s0 + k)) + (k : ℤ) * σ.wPrev t₀
            - σ.wPrev (B₀ (s0 + 0)))
          = σ.w (B₀ (s0 + k)) + (k : ℤ) * σ.w t₀ - σ.w (B₀ (s0 + 0)) := by
            rw [hs1, hs2, hs3]; ring
        _ = 0 := hval
    rcases mul_eq_zero.mp hkey2 with h | h
    · exact absurd h (by omega)
    · linarith [h]
  have hKEY : ∀ k ∈ Kp,
      ((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k * ((pat 0 : ↥σ.K) : F)
      = ((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k := by
    intro k hk
    obtain ⟨h1, hw1, hR1⟩ := hSide k hk
    obtain ⟨h10, hw10, hR10⟩ := hSide 0 h0Kp
    obtain ⟨hbkne, hbkR, hbkF⟩ := hbb k hk
    obtain ⟨hb0ne, hb0R, hb0F⟩ := hbb 0 h0Kp
    have ht₀kne : t₀ ^ k ≠ 0 := pow_ne_zero _ ht₀ne
    have hXkne : B₀ (s0 + k) * t₀ ^ k ≠ 0 := mul_ne_zero h1 ht₀kne
    have hXkC : inC σ'.Φ (B₀ (s0 + k) * t₀ ^ k) := by
      rw [inC, hΦ'deg]
      have hd1 : (B₀ (s0 + k)).degree ≤ 0 := hconstOf _ (hconstOfP _ (hdev₀.1 _))
      have hd2 : (t₀ ^ k).degree ≤ 0 := by
        have ht0 : t₀.degree = 0 :=
          le_antisymm ht₀deg (Polynomial.zero_le_degree_iff.mpr ht₀ne)
        rw [Polynomial.degree_pow, ht0, smul_zero]
      calc (B₀ (s0 + k) * t₀ ^ k).degree
          ≤ (B₀ (s0 + k)).degree + (t₀ ^ k).degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + 0 := add_le_add hd1 hd2
        _ = 0 := add_zero 0
        _ < 1 := by exact_mod_cast Nat.zero_lt_one
    have hwXk : σ.w (B₀ (s0 + k) * t₀ ^ k) = σ.w (B₀ (s0 + 0)) := by
      rw [σ.hwmul _ _ h1 ht₀kne, ResVal.w_pow σ _ ht₀ne, ht₀w, hw1, hw10]
      push_cast
      ring
    obtain ⟨cX, hcXne, hcXR, hcXF⟩ := hdigE (B₀ (s0 + k) * t₀ ^ k) hXkne hXkC
    have hcXval : cX = bb k * (dt : ↥σ'.K) ^ k := by
      apply v9c_C_inj
      rw [← hcXR, σ'.hRmul _ _ h1 ht₀kne, ResVal.R_pow σ' _ ht₀ne, hbkR, hdtR0,
        ← map_pow, ← map_mul]
    have hdigXk : σ.digPrime zbar (B₀ (s0 + k) * t₀ ^ k)
        = σ.digPrime zbar (B₀ (s0 + k)) * (σ.digPrime zbar t₀) ^ k := by
      unfold Stage.digPrime
      rw [σ.hRmul _ _ h1 ht₀kne, ResVal.R_pow σ _ ht₀ne, map_mul, map_pow]
    have hdig1 : σ.digPrime zbar (B₀ (s0 + k))
        = ((pat k : ↥σ.K) : F)
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F) := by
      unfold Stage.digPrime
      rw [hR1, LaurentPolynomial.eval₂_C_mul_T]
      simp
    have hdigt : σ.digPrime zbar t₀
        = ((c₀ : ↥σ.K) : F) * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) := by
      unfold Stage.digPrime
      rw [ht₀R, LaurentPolynomial.eval₂_C_mul_T]
      simp
    have hdig0 : σ.digPrime zbar (B₀ (s0 + 0))
        = ((pat 0 : ↥σ.K) : F)
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) := by
      unfold Stage.digPrime
      rw [hR10, LaurentPolynomial.eval₂_C_mul_T]
      simp
    have hq : - σ.t * σ.wPrev (B₀ (s0 + k)) + (- σ.t * σ.wPrev t₀) * (k : ℤ)
        = - σ.t * σ.wPrev (B₀ (s0 + 0)) := by
      linear_combination (- σ.t) * hwPrevEq k hk
    have hzv : ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
        * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) ^ k
        = ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) := by
      have h2 : ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k)))
          * (zbar ^ (- σ.t * σ.wPrev t₀)) ^ k : Fˣ) : F)
          = ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
            * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) ^ k := by
        rw [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [← h2]
      congr 1
      rw [← zpow_natCast (zbar ^ (- σ.t * σ.wPrev t₀)) k, ← zpow_mul, ← zpow_add, hq]
    have hcross : (cX : F)
        * σ.digPrime zbar (B₀ (s0 + 0))
        = ((bb 0 : ↥σ'.K) : F) * σ.digPrime zbar (B₀ (s0 + k) * t₀ ^ k) := by
      rw [hcXF, hb0F, hwXk]
      ring
    rw [hcXval] at hcross
    push_cast at hcross
    rw [hdigXk, hdig1, hdigt, hdig0] at hcross
    have hZ0ne : ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) ≠ 0 :=
      Units.ne_zero _
    refine mul_right_cancel₀ hZ0ne ?_
    calc ((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k * ((pat 0 : ↥σ.K) : F)
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F)
        = (((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k)
          * (((pat 0 : ↥σ.K) : F)
            * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F)) := by ring
      _ = ((bb 0 : ↥σ'.K) : F)
          * (((pat k : ↥σ.K) : F)
              * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
            * (((c₀ : ↥σ.K) : F)
              * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F)) ^ k) := hcross
      _ = ((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k
          * (((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + k))) : Fˣ) : F)
            * ((zbar ^ (- σ.t * σ.wPrev t₀) : Fˣ) : F) ^ k) := by
          rw [mul_pow]; ring
      _ = ((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k
          * ((zbar ^ (- σ.t * σ.wPrev (B₀ (s0 + 0))) : Fˣ) : F) := by rw [hzv]
  -- ══ 10. cast to F, apply the KEY, cancel units ══
  have hstep3 : ∑ k ∈ Kp, ((bb k : ↥σ'.K) : F)
      * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose j : ℕ) : F))
      = ((bbM j : ↥σ'.K) : F) * (- ((dt : ↥σ'.K) : F)) ^ j := by
    have hc := congrArg (fun y : ↥σ'.K => (y : F)) hstep2
    push_cast at hc
    convert hc using 2 with k hk
  have hterm10 : ∀ k ∈ Kp,
      ((bb k : ↥σ'.K) : F)
        * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose j : ℕ) : F))
        * ((pat 0 : ↥σ.K) : F)
      = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
        * (((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
            * (((s0 + k).choose j : ℕ) : F)) := by
    intro k hk
    have hK := hKEY k hk
    have hcz : (-1 : F) * ((c₀ : ↥σ.K) : F) = ((zbar : Fˣ) : F) := by
      rw [hc₀z]; ring
    calc ((bb k : ↥σ'.K) : F)
          * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose j : ℕ) : F))
          * ((pat 0 : ↥σ.K) : F)
        = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * (-1 : F) ^ k)
          * ((((bb k : ↥σ'.K) : F) * ((dt : ↥σ'.K) : F) ^ k * ((pat 0 : ↥σ.K) : F))
            * (((s0 + k).choose j : ℕ) : F)) := by
          rw [neg_pow, pow_add, pow_add]
          ring
      _ = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * (-1 : F) ^ k)
          * ((((bb 0 : ↥σ'.K) : F) * ((pat k : ↥σ.K) : F) * ((c₀ : ↥σ.K) : F) ^ k)
            * (((s0 + k).choose j : ℕ) : F)) := by rw [hK]
      _ = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
          * (((pat k : ↥σ.K) : F) * (((-1 : F)) * ((c₀ : ↥σ.K) : F)) ^ k
            * (((s0 + k).choose j : ℕ) : F)) := by
          rw [mul_pow]
          ring
      _ = ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
          * (((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
            * (((s0 + k).choose j : ℕ) : F)) := by rw [hcz]
  have hsum0 : ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
      * (∑ k ∈ Kp, ((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
          * (((s0 + k).choose j : ℕ) : F))
      = ((bbM j : ↥σ'.K) : F) * (- ((dt : ↥σ'.K) : F)) ^ j * ((pat 0 : ↥σ.K) : F) := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ Kp, ((-1 : F) ^ s0 * ((dt : ↥σ'.K) : F) ^ s0 * ((bb 0 : ↥σ'.K) : F))
          * (((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
              * (((s0 + k).choose j : ℕ) : F))
        = ∑ k ∈ Kp, ((bb k : ↥σ'.K) : F)
            * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose j : ℕ) : F))
            * ((pat 0 : ↥σ.K) : F) :=
          (Finset.sum_congr rfl (fun k hk => (hterm10 k hk).symm))
      _ = (∑ k ∈ Kp, ((bb k : ↥σ'.K) : F)
            * ((- ((dt : ↥σ'.K) : F)) ^ (s0 + k) * (((s0 + k).choose j : ℕ) : F)))
            * ((pat 0 : ↥σ.K) : F) := (Finset.sum_mul _ _ _).symm
      _ = ((bbM j : ↥σ'.K) : F) * (- ((dt : ↥σ'.K) : F)) ^ j * ((pat 0 : ↥σ.K) : F) := by
          rw [hstep3]
  -- ══ 11. the Taylor VANISHING below μ kills the pinned digit ══
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    rw [h] at hc₀z
    push_cast at hc₀z
    exact zbar.ne_zero (by
      have := hc₀z.symm
      rw [neg_eq_zero] at this
      exact this)
  have hKzero : ∑ k ∈ Finset.range (wSide + 1),
      pat k * (- c₀) ^ k * (((s0 + k).choose j : ℕ) : ↥σ.K) = 0 :=
    v9c_taylor_zero c₀ hc₀ne Ranch μ s0 wSide pat hRanch hOrd.1 j hjμ
  have hFzero : ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
      * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose j : ℕ) : F) = 0 := by
    have hc := congrArg (fun y : ↥σ.K => (y : F)) hKzero
    push_cast at hc
    calc ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
          * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose j : ℕ) : F)
        = ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
          * (- ((c₀ : ↥σ.K) : F)) ^ k * (((s0 + k).choose j : ℕ) : F) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hc₀z, neg_neg]
      _ = 0 := by convert hc using 2 with k hk
  have hKpzero : ∑ k ∈ Kp, ((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k
      * (((s0 + k).choose j : ℕ) : F) = 0 := by
    have hfilter : ∑ k ∈ (Finset.range (wSide + 1)).filter (fun k => pat k ≠ 0),
        ((pat k : ↥σ.K) : F) * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose j : ℕ) : F)
        = ∑ k ∈ Finset.range (wSide + 1), ((pat k : ↥σ.K) : F)
            * ((zbar : Fˣ) : F) ^ k * (((s0 + k).choose j : ℕ) : F) := by
      refine Finset.sum_filter_of_ne ?_
      intro k _ hne0 hpk
      exact hne0 (by rw [hpk]; simp)
    rw [hKpdef, hfilter]
    exact hFzero
  rw [hKpzero, mul_zero] at hsum0
  have hdtFne : ((dt : ↥σ'.K) : F) ≠ 0 := by
    intro h
    exact dt.ne_zero (by exact_mod_cast h)
  have hbbMjF : ((bbM j : ↥σ'.K) : F) ≠ 0 := by
    intro h
    exact hbbMjne (by exact_mod_cast h)
  have hpat0F : ((pat 0 : ↥σ.K) : F) ≠ 0 := by
    intro h
    exact hpat0 (by exact_mod_cast h)
  exact (mul_ne_zero (mul_ne_zero hbbMjF (pow_ne_zero _ (neg_ne_zero.mpr hdtFne)))
    hpat0F) hsum0.symm

end V9CornerHelpers

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
  · -- ═══ HK-06 WAVE HONEST REOPENING (2026-07-31, task #44; the (S-a) regrade re-key) ═══
    -- The OLD closure of this leg was `V10_readTransition_incompatible` — an EXFALSO from
    -- the pre-wave keying's recorded contradiction.  Under the repaired leg the recorded
    -- steep transition is CONSISTENT (HK-05 stall gate + the compiled positive 2-node gate
    -- HC2/HK23_twoNodeGatePos.lean), so no contradiction closure exists.  This leg is the
    -- honest transport obligation HK-52/HK-11a/HK-11b (BP2 §3.3), scheduled post-wave.
    -- ⚠ TRUTH-UNDER-NEW-KEYING IS PART OF THAT ADJUDICATION: the recorded child weight is
    -- now the (ν_{i+1}.e, ν_{i+1}.h)-slot-min over the σV regrade, so the displayed ℚ-form
    -- may need the HK-11b re-scope (the ν_{i+1}.e-stretch factor).  Do NOT consume this
    -- K1 steep (e·g ≥ 2 ⇒ e = 1 ∧ g ≥ 2 by the RG-2 recording fence) leg as settled mathematics; the sorry is the recorded HK-11 obligation.
    sorry
  · -- `ν.e·ν.g = 1`
    rcases Nat.eq_zero_or_pos i with hi0 | hi1'
    · -- ═══ HK-06 WAVE HONEST REOPENING (2026-07-31, task #44) — THE CORNER, RE-OPENED ═══
      -- K1 corner (i = 0 ∧ e·g = 1; OLD proof: v9c_corner toolkit): the pre-wave honest proof consumed the OLD-keyed transition record
      -- (TransitionCoreL at the PARENT pair with unguarded s/t ties); under the (S-a)
      -- re-key the record is keyed at (ν₁.e, ν₁.h) through the σV regrade, and the
      -- recorded child weight gains the ν₁.e-stretch — the corner statement itself is
      -- RE-ADJUDICATION-SUSPECT under the new keying (HK-11b scope).  Full pre-wave
      -- proof in git history (wave commit^).  Recorded HK-11 obligation; do NOT consume
      -- as settled mathematics.
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

/-- **The U22-E1 Box law, NON-RECENTERING parent** (REV 6): at consecutive reads of a
run whose parent read `i` is a root or increment read, every slot of f's frame-(i+1)
development STRICTLY BELOW the standing vertex (`j < μ`, `B j ≠ 0`) weighs STRICTLY
ABOVE the parent line's value at its base index (stage scale: `σ.w = STR_{i+1} ×`
absolute) — the strict span-entry content of (SAE) at this species, statement keyed to
`SAE_spanStrict_endpoint`'s fenced ℚ-form.  Perimeter dispatch mirrors `V9_K1nonrec`
exactly: the `e·g ≥ 2` legs close by the V10 INCONSISTENCY finding (vacuous — read
V9's REV-4 header disclosure before consuming), `i ≥ 1 ∧ e·g = 1` by the species
inventory, and the genuine `i = 0 ∧ e·g = 1` corner by `v9c_cornerBox` (the strict
Taylor-vanishing sibling of the REV-5 corner core). -/
theorem V9_E1box_nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (j : ℕ) (hjμ : j < (H.nodes[i]'(by omega)).μ) (hjne : B j ≠ 0) :
    (H.strFrame (i+1) : ℚ) *
        (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
      < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := by
  classical
  have hilen : i < H.nodes.length := by omega
  by_cases hEG : 2 ≤ (H.nodes[i]'hilen).e * (H.nodes[i]'hilen).g
  · -- ═══ HK-06 WAVE HONEST REOPENING (2026-07-31, task #44; the (S-a) regrade re-key) ═══
    -- The OLD closure of this leg was `V10_readTransition_incompatible` — an EXFALSO from
    -- the pre-wave keying's recorded contradiction.  Under the repaired leg the recorded
    -- steep transition is CONSISTENT (HK-05 stall gate + the compiled positive 2-node gate
    -- HC2/HK23_twoNodeGatePos.lean), so no contradiction closure exists.  This leg is the
    -- honest transport obligation HK-52/HK-11a/HK-11b (BP2 §3.3), scheduled post-wave.
    -- ⚠ TRUTH-UNDER-NEW-KEYING IS PART OF THAT ADJUDICATION: the recorded child weight is
    -- now the (ν_{i+1}.e, ν_{i+1}.h)-slot-min over the σV regrade, so the displayed ℚ-form
    -- may need the HK-11b re-scope (the ν_{i+1}.e-stretch factor).  Do NOT consume this
    -- E1box steep (e·g ≥ 2 ⇒ e = 1 ∧ g ≥ 2 by the RG-2 recording fence) leg as settled mathematics; the sorry is the recorded HK-11 obligation.
    sorry
  · -- `ν.e·ν.g = 1`
    rcases Nat.eq_zero_or_pos i with hi0 | hi1'
    · -- ═══ HK-06 WAVE HONEST REOPENING (2026-07-31, task #44) — THE CORNER, RE-OPENED ═══
      -- E1box corner (i = 0 ∧ e·g = 1; OLD proof: v9c_cornerBox): the pre-wave honest proof consumed the OLD-keyed transition record
      -- (TransitionCoreL at the PARENT pair with unguarded s/t ties); under the (S-a)
      -- re-key the record is keyed at (ν₁.e, ν₁.h) through the σV regrade, and the
      -- recorded child weight gains the ν₁.e-stretch — the corner statement itself is
      -- RE-ADJUDICATION-SUSPECT under the new keying (HK-11b scope).  Full pre-wave
      -- proof in git history (wave commit^).  Recorded HK-11 obligation; do NOT consume
      -- as settled mathematics.
      sorry
    · -- `i ≥ 1`: a non-recentering non-root read is an increment; `hspecInc`
      -- forces `1 < e·g` against the case hypothesis.
      exfalso
      cases hspec : (H.nodes[i]'hilen).species with
      | root =>
          exact absurd ((H.root_iff i hilen).mp hspec) (by omega)
      | increment =>
          exact absurd ((H.nodes[i]'hilen).hspecInc hspec) (by omega)
      | recentering =>
          exact absurd hspec hsp

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V9_wvGeStretch
#print axioms LeanUrat.HC1.V9_wvEqStretch_of_bottomSlot
#print axioms LeanUrat.HC1.V9_bottomSlot_of_wvEqStretch
#print axioms LeanUrat.HC1.V9_steepSide_frameDescent
#print axioms LeanUrat.HC1.V9_K1nonrec
#print axioms LeanUrat.HC1.V9_E1box_nonrec
