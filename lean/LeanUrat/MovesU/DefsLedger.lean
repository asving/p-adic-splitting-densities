/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.U0b_splitTypeFintype

/-!
# MovesU/DefsLedger — the kernel pack + capstone ledger (blueprint §2b)

Imports U0b so `Fintype (SplittingType n)` is IN SCOPE for the `∑ σ` fields
(the gap-7 / D11 circularity fix). One Prop slot per open kernel/obligation of the
capstone ledger CL-1…CL-19 (F5/F6/F7); `CapstoneLedger` a Prop structure with a field
PER CL ITEM plus the operative consumption fields; the D12 slice sub-bundles
`FinStack`/`SolveStack`/`LowerStack` with their field-selection projections.
(REG-p) is NOT a ledger field: the ONE explicit hypothesis (D5/D8).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology ENNReal

/-- THE KERNEL STATEMENT PACK (F5/F6/F7): one named Prop slot per open
    kernel/obligation of the capstone ledger. Filled with the REAL upstream statements
    at instantiation (owner per slot); filling a slot with `True` is an
    instantiation-fidelity violation adjudicated at the owner's audit (D9). -/
structure KernelStatements where
  /-- CL-1 [3]: per-pool ESCAPE(E0) active-block solvability -/
  escapeE0 : Prop
  /-- CL-2 [5]: X.1b WEIGHT-CHARGE via X.2's env constants (F6) -/
  weightCharge : Prop
  /-- CL-3 [5]+[2b]: PROGRESS — (X2-AFF)/(X2-CAP)/(X2-BRIDGE)/(X2-TAILS) with
      constants c₃(n), c₄(n), s(n) (F6) -/
  progressX2 : Prop
  /-- CL-4 [5]: X.3 termination a.e. (statement slot; its operative trace is the
      `cl4_env_tendsto` field of `CapstoneLedger`) -/
  x3Termination : Prop
  /-- CL-5(i) [2b]: XHD = M4a-X (+ (ENT-U)) -/
  xhdM4aX : Prop
  /-- CL-5(ii) [1]: D4R.0 — CLOSED upstream; ledger-echo slot -/
  d4r0 : Prop
  /-- CL-5(iii) [1v]: CTS-M(iv)-PART -/
  ctsmIvPart : Prop
  /-- CL-5(iv) [1v]: CTS-M(iv)-REP = M2(ii) -/
  ctsmIvRep : Prop
  /-- CL-5(v) [1v]: CTS-M(iv)-MEAS -/
  ctsmIvMeas : Prop
  /-- CL-5(vi) [1v]: CTS-M(v) HMC -/
  ctsmVHmc : Prop
  /-- CL-5(vii) [1v]: CTS-M(ii) ACT + (ii-c) — RELATED to (r2), SEPARATE
      (rev 6: neither implies the other) -/
  ctsmIiAct : Prop
  /-- CL-5(viii) [1v]: CTS-M(iii) INIT + ENT-COUNT (ENT-AGG/INIT-RAT) -/
  ctsmIiiInit : Prop
  /-- CL-5(ix) [1v]: CTS-M(vi) COMP-typing -/
  ctsmViComp : Prop
  /-- CL-6 [1v]: (iv)-POLY — without it R_σ ∈ ℚ(q) unfounded -/
  ctsmIvPoly : Prop
  /-- CL-7a [4]: TRACK-COUNT + explicit L(n) -/
  trackCount : Prop
  /-- CL-7b [4]: the D(n) duty (candidate n!, underived) -/
  dnDuty : Prop
  /-- CL-7c [4]: the positive genuine-increment sub-claim -/
  genuineIncrement : Prop
  /-- CL-8 [2r]: REL.1 re-scoped -/
  rel1 : Prop
  /-- CL-8 [2r]: REL.2(a) -/
  rel2a : Prop
  /-- CL-8 [2r]: REL.2(b) -/
  rel2b : Prop
  /-- CL-8 [2r]: REL.2(d) -/
  rel2d : Prop
  /-- CL-8 [2r]: REL.2(e), the β-typing (e1)–(e5) leg -/
  rel2e : Prop
  /-- CL-8 [2r]: REL.3 over O_δ -/
  rel3 : Prop
  /-- CL-9 [3]: RS.0 (α) lumpability + (β) bisimulation = XRB -/
  rs0LumpBisim : Prop
  /-- CL-10 [3t]: (SIB)/(SIB-STEP), measure-level joint form -/
  sib : Prop
  /-- CL-10 [3t]: (JC-multi) -/
  jcMulti : Prop
  /-- CL-10 [3t]: TREE-EXP(-fin, -ns) + TREE-N, (NS-ROUTE)-scoped.
      (vpSound: DELETED as a slot at REV 3 — now the TYPED ledger field
      `cl10_vpsound : VPSound X`, ruling (B); rev-2 gap 5.) -/
  treeExpTreeN : Prop
  /-- CL-11 [4]/[1v]: no-equal-e-feedback + DEG-CONS full roster.
      (ksubM1C1: typed-only since REV 3 — `KsubM1C1 M` in cl11; its content is fully
      expressible over MenuData, so no bare slot is needed.) -/
  noEqualEFeedback : Prop
  /-- CL-13 [1v], REINSTATED at REV 4 (F3-C2): the FULL CTS-M(i) statement — the ONE
      fixed finite p-independent state set with DISPLAYED cell predicates and GLOBALLY
      COMPATIBLE target-cell maps ("without it no path product or kernel index
      type-checks"); the typed face MenuWF M rides beside it in cl13, replacing
      NOTHING -/
  ctsmSyntax : Prop
  /-- CL-14 [2a]: M1 + M5 — CLOSED upstream; ledger-echo slot -/
  m1m5 : Prop
  /-- CL-15 [5]: the per-species GMN index dictionary -/
  x1aDict : Prop
  /-- CL-16 [1v]/[2b]: M4b constancy + M4b-T equivariance (π_v) -/
  m4bConstancy : Prop
  /-- CL-17 [3]: RS.1-SH + routing + unique shallow cut + W_Ŝ -/
  rs1Assembly : Prop
  /-- CL-18 [1v]/[2b]: (J-RAT) per-cell rational tables -/
  jRat : Prop
  /-- CL-19 [2b]: (JC-INV) joint digit-cell law -/
  jcInv : Prop

/-- THE CAPSTONE LEDGER (SQ.4's CL-1…CL-19, REV 16 extent) as ONE Prop structure:
    a field PER CL ITEM asserting its kernel slot (F5; CL-2/CL-3 included, F6) PLUS
    the operative consumption fields. "Neither this display nor any acceptance record
    may drop a tag while any cited CL-item is open." (REG-p) is NOT a field: the ONE
    explicit hypothesis. CL-12 is CLOSED ("NOTHING at CL-12 is open") — no slot. -/
structure CapstoneLedger (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (S : SolveData n) (D : RegData p) (M : MenuData) (K : KernelStatements) : Prop where
  cl1 : K.escapeE0
  cl2 : K.weightCharge
  cl3 : K.progressX2
  cl4 : K.x3Termination
  cl5 : K.xhdM4aX ∧ K.d4r0 ∧ K.ctsmIvPart ∧ K.ctsmIvRep ∧ K.ctsmIvMeas ∧
        K.ctsmVHmc ∧ K.ctsmIiAct ∧ K.ctsmIiiInit ∧ K.ctsmViComp
  cl6 : K.ctsmIvPoly
  cl7 : K.trackCount ∧ K.dnDuty ∧ K.genuineIncrement
  cl8 : K.rel1 ∧ K.rel2a ∧ K.rel2b ∧ K.rel2d ∧ K.rel2e ∧ K.rel3
  cl9 : K.rs0LumpBisim
  cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN
  /-- CL-10's VP-SOUND leg, TYPED over the concrete box (ruling (B)): decided-σ ⟹
      true type σ. The identification corollary (U11, clause (ii)) consumes it. -/
  cl10_vpsound : VPSound X
  cl11 : K.noEqualEFeedback ∧ KsubM1C1 M
  /-- CL-13 in FULL (F3-C2): the reinstated full-statement slot AND the typed menu
      face — no open tag dropped (SQ.4's acceptance-record rule binds this form). -/
  cl13 : K.ctsmSyntax ∧ MenuWF M
  /-- The O3 BASE-PIN DECLARATION (SQ.4's display duty, gap 6): the pinned base digit
      section is TEICHMÜLLER (D4R0K S1.4 (B4)/O3) — "declared once, as the definitive
      write-up must". -/
  o3_teichmuller : X.baseSection = BaseSection.teichmuller
  cl14 : K.m1m5
  cl15 : K.x1aDict
  cl16 : K.m4bConstancy
  cl17 : K.rs1Assembly
  cl18 : K.jRat
  cl19 : K.jcInv
  /-- OPERATIVE, the finiteness stack's consumed form (CL-7 + CL-10): TREE-N's exact
      fiber count summed over the thr ≤ N slice —
      "decided_σ(N) = Σ_{T : typemult(T) = σ, thr(T) ≤ N} #fiber(T) is a FINITE sum
      (SQ.0/CL-7) of exact fiber counts (TREE-N/CL-10)". This identity is also the
      series' tie to the classifier (D4, F2). -/
  finiteness_stack : ∀ σ N,
    (X.decided σ N : ℝ≥0∞) =
      (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T
  /-- OPERATIVE, the solve stack's consumed form (CL-1, CL-5, CL-6, CL-8, CL-9, CL-11,
      CL-13…CL-17, CL-18, CL-19 — the slots asserted above): UNDER (REG-p) the
      extended-value sum is finite, IS the literal R_σ(p), AND R_σ(p) ≥ 0 — "RS.3's
      positivity ((I − A(q₀))^{−1} ≥ 0) and R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN
      E0 + the CL-5 mass identification" (F8's repair: positivity is a conjunct, not
      an inference from `ofReal`). -/
  solve_stack : RegP S D → ∀ σ,
    F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
    0 ≤ evalℝ S σ p
  /-- RS.4's checksum (§S S.5) WITH its full inherited set riding verbatim: "E0, the
      CL-5 nine, RS.1's set, X.3/CL-4, and the whole RS.2 rationality chain incl.
      (J-RAT)/CL-18". The ℚ(q) identity — Theorem U's checksum conjunct.
      (Needs U0b's `Fintype (SplittingType n)`.) -/
  rs4_checksum : ∑ σ, S.R σ = 1
  /-- RS.4 EVALUATED at p under (REG-p) — the form SQ.3's arithmetic consumes. Same
      inherited set. (E-phase note: derivable from `rs4_checksum` + (r2)-definedness
      via RatFunc eval-hom side conditions; carried as a field until that unit lands.) -/
  rs4_eval : RegP S D → ∑ σ, evalℝ S σ p = 1
  /-- OPERATIVE trace of CL-4 = X.3 (QUALITATIVE form — "the limit consumes no
      envelope constant"; the statement slot is `cl4` above; discharges only at [5]'s
      EVENT): env(N) → 0. The quantitative rate form (CL-2/CL-3's constants) is
      asserted via the `cl2`/`cl3` slots but not consumed by any MovesU proof — gate
      SQUEEZE-n3 is a census artifact, not a Lean unit. -/
  cl4_env_tendsto : Tendsto X.env atTop (𝓝 0)

/-- THE PER-p INSTANTIATION BUNDLE (for U10's quantifier shape): everything Theorem U
    needs at one prime, over the FIXED p-uniform data (S, M, K — F3-C2/G4: one menu
    vocabulary and one kernel pack for ALL primes, so CL-13's p-independence and the
    slots' p-uniform referents are expressible). -/
structure UInstance (n : ℕ) (S : SolveData n) (M : MenuData) (K : KernelStatements)
    (p : ℕ) where
  X : ClassifierSpec n p
  F : FiberSeries n p X
  D : RegData p
  L : CapstoneLedger n p X F S D M K

/-- SQ.2-partial's EXACT stack (D12): the finiteness stack {CL-7; CL-10} + the
    operative TREE-N identity — nothing else (Codex-FINAL 1). -/
structure FinStack (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (K : KernelStatements) : Prop where
  cl7 : K.trackCount ∧ K.dnDuty ∧ K.genuineIncrement
  cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN
  /-- REV 6 (Codex-FINAL#2): CL-10 is cited WHOLE by the (U-n) upper side ("the [3t]
      package (CL-10)"), and VP-SOUND is part of CL-10's own entry — so the typed
      VP-SOUND field belongs to THIS slice, not only to the capstone. -/
  cl10_vpsound : VPSound X
  finiteness_stack : ∀ σ N,
    (X.decided σ N : ℝ≥0∞) =
      (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T

/-- SQ.2-upper's EXACT solve stack (D12): the (U-n) upper-side citation list —
    CL-1, CL-5, CL-6, CL-8, CL-9, CL-11, CL-13…CL-16, CL-17, CL-18, CL-19 — + the
    operative RegP-guarded identification. NO CL-2/CL-3/CL-4, NO RS.4, NO VP-SOUND,
    NO O3 (Codex-FINAL 2). -/
structure SolveStack (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (S : SolveData n) (D : RegData p) (M : MenuData) (K : KernelStatements) : Prop where
  cl1 : K.escapeE0
  cl5 : K.xhdM4aX ∧ K.d4r0 ∧ K.ctsmIvPart ∧ K.ctsmIvRep ∧ K.ctsmIvMeas ∧
        K.ctsmVHmc ∧ K.ctsmIiAct ∧ K.ctsmIiiInit ∧ K.ctsmViComp
  cl6 : K.ctsmIvPoly
  cl8 : K.rel1 ∧ K.rel2a ∧ K.rel2b ∧ K.rel2d ∧ K.rel2e ∧ K.rel3
  cl9 : K.rs0LumpBisim
  cl11 : K.noEqualEFeedback ∧ KsubM1C1 M
  cl13 : K.ctsmSyntax ∧ MenuWF M
  cl14 : K.m1m5
  cl15 : K.x1aDict
  cl16 : K.m4bConstancy
  cl17 : K.rs1Assembly
  cl18 : K.jRat
  cl19 : K.jcInv
  solve_stack : RegP S D → ∀ σ,
    F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
    0 ≤ evalℝ S σ p

/-- (U-n)-LOWER's ADDITIONAL slice (D12): RS.4's checksum with its inherited set —
    the CL-4 slot ("X.3/CL-4 included") + both checksum forms. CL-2/CL-3 attach ONLY
    to the rate form = gate SQUEEZE-n3, not a Lean unit (Codex-FINAL 3). -/
structure LowerStack (n p : ℕ) (S : SolveData n) (D : RegData p)
    (K : KernelStatements) : Prop where
  cl4 : K.x3Termination
  rs4_checksum : ∑ σ, S.R σ = 1
  rs4_eval : RegP S D → ∑ σ, evalℝ S σ p = 1

/-- Field-selection projection (D12/G9): U10 fires the earlier units without
    re-packing. A LITERAL `⟨…⟩` re-bundling — no strengthening or weakening. -/
def CapstoneLedger.finStack {n p : ℕ} {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {S : SolveData n} {D : RegData p} {M : MenuData} {K : KernelStatements}
    (L : CapstoneLedger n p X F S D M K) :
    FinStack n p X F K := ⟨L.cl7, L.cl10, L.cl10_vpsound, L.finiteness_stack⟩

/-- Field-selection projection (D12/G9), the solve-stack slice. -/
def CapstoneLedger.solveStack {n p : ℕ} {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {S : SolveData n} {D : RegData p} {M : MenuData} {K : KernelStatements}
    (L : CapstoneLedger n p X F S D M K) :
    SolveStack n p X F S D M K :=
  ⟨L.cl1, L.cl5, L.cl6, L.cl8, L.cl9, L.cl11, L.cl13, L.cl14, L.cl15, L.cl16,
   L.cl17, L.cl18, L.cl19, L.solve_stack⟩

/-- Field-selection projection (D12/G9), the lower-stack slice. -/
def CapstoneLedger.lowerStack {n p : ℕ} {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {S : SolveData n} {D : RegData p} {M : MenuData} {K : KernelStatements}
    (L : CapstoneLedger n p X F S D M K) :
    LowerStack n p S D K := ⟨L.cl4, L.rs4_checksum, L.rs4_eval⟩

end LeanUrat.MovesU
