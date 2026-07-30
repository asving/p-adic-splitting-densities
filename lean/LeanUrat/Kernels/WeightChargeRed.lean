/-
Kernels/WeightChargeRed — BP4-c5 E-phase skeletons for the WEIGHT-CHARGE/X.1b
reduction: units KD2, KD3, KD4 (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.D
+ §4 KD; F3 disposition binding; adjudications per
BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).  File name per blueprint §2.3.

THE KERNEL (MOVES 11153-11160): #{recentering nodes of H} ≤ s(n)·v_p(disc f),
FULL population (T4 + uncertified T1).  This file carries the blueprint's NEW
reduction observation: WEIGHT-CHARGE ⇐ TRACK-COUNT + (REC-DISC), where

  (REC-DISC)  a stratum history with ≥ 1 recentering node forces
              v_p(disc f) ≥ 1                                   [KD2]

and the two implications KD3/KD4 consume a `Cl7Kernel.track_restarts`-style
constant bound (MovesU/DefsLedger.lean:206) as a HYPOTHESIS.

STATUS NOTES (REV 2, F3 — binding on consumers):
· KD3/KD4 are SOUND as implications, but their constant-L premise (T-const)
  has NO supported general route in this campaign (risk R11: plausibly false;
  its only support is the finite 15/15 probe; the KD6∘KD7 ladder/cap
  composition CANNOT deliver it — it grows with vdisc).  NO prover is
  assigned to (T-const); the schedulable WeightCharge discharge is KD10
  (ladder + cap + REC-DISC, sibling unit), which never needs a constant
  restart cap.  These implications are still built: they machine-check the
  reduction and serve KD10's assembly pattern.
· R7/Q5: `XConsts.s` is existential data — instantiating it at L (or at
  KD10's 2·D(n)·c(n)) is not a statement-fence event; the CL-2 record line
  is annotated at discharge time only.
· Fence (§3.D): the (CD)-pinned X1B reading A binds every KD unit; the units
  in THIS file touch only the population counts countPop (.recT1/.t4) and
  vdisc — no d_cert consumption, so no reading-A obligation arises here
  (recorded for KD8's audit).

GATE SEQUENCING (REV 2, F5): KD1 — the python CM gate (s(n)-candidate
refuter + the REC-DISC probe leg: search for f with a recentering node and
vdisc f = 0, which would REFUTE KD2 — risk R6) — is a sibling verification/
unit sequenced BEFORE the KD2 prover.  Not an import (no Lean content).

Build: cd lean && lake build LeanUrat.Kernels.WeightChargeRed
-/
import LeanUrat.MovesX.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesX

/-- KD2 — `recentering_vdisc_pos` (REC-DISC): H in the stratum of f,
f ∉ discZero, countPop H .recT1 + countPop H .t4 ≥ 1 ⟹ 1 ≤ vdisc f.
deps: KD1 clean (CM gate — the REC-DISC probe leg runs FIRST; a found f with
a recentering and vdisc = 0 refutes this statement, risk R6).
Sketch: a recentering node presupposes a non-hen root read ⟹ repeated factor
of f̄ = f mod p ⟹ p ∣ disc f (Res(f̄, f̄′) = 0 — Mathlib discriminant/
resultant or the L3Squarefree route, LeanUrat/L3Squarefree.lean) ⟹
1 ≤ vdisc f.  Pre-approved split: KD2a (the mod-p discriminant lemma,
unconditional) / KD2b (the classifier leg).
RECORDED RESOLUTION + FALLBACK (blueprint's own fence): the statement is
quantified over the corpus's shared `XFamily` parameter, mirroring the §D
kernel Props (X1aAlignP etc.); but `GMNIndex` carries only
ind/inStratum/p2 — NO law ties `inStratum` to f̄'s factorization, so the
classifier leg (KD2b) needs an XCtx/GMN law that may be unbuilt.  If so,
the pre-declared fallback binds: hoist the classifier leg to the ⚑ named
hypothesis `RecImpliesWild` (Q4 shape: hypothesis, never a new field on the
frozen structures), prove the mod-p lemma unconditionally, and record the
obstruction — never a silent sorry, never a weakened statement. -/
theorem recentering_vdisc_pos {n : ℕ} (X : XFamily n) :
    ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
      1 ≤ countPop H .recT1 + countPop H .t4 →
      1 ≤ vdisc f := by
  sorry

/-- KD3 — `weightChargeFull_of_trackCount`: a `Cl7Kernel.track_restarts`-
style constant bound (∀ …, countPop H .recT1 + countPop H .t4 ≤ L, the
hypothesis displayed verbatim from MovesU/DefsLedger.lean:206 over the bare
XFamily) + REC-DISC (KD2's conclusion, consumed as a hypothesis) ⟹
WeightChargeFullP n X K at the constants ⟨s := L, …⟩.
RECORDED RESOLUTION: the blueprint's "⟨s := L, …⟩" is transcribed as an
arbitrary `K : XConsts n` with the pinning hypothesis `K.s = L` (XConsts
carries many further constants inert here; `s` is existential data — R7).
deps: KD2.  Sketch: per instance, case vdisc f = 0 (then the count is 0 by
the REC-DISC contrapositive, since 1 ≤ count would force 1 ≤ vdisc) vs
1 ≤ vdisc (then count ≤ L = L·1 ≤ L·vdisc = K.s·vdisc).  routine-opus.
STATUS NOTE (REV 2, F3): sound as an implication; the constant-L premise
has no supported general route this campaign (see file header). -/
theorem weightChargeFull_of_trackCount {n : ℕ} (X : XFamily n)
    (K : XConsts n) (L : ℕ) (hsK : K.s = L)
    (htrack : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
      countPop H .recT1 + countPop H .t4 ≤ L)
    (hrec : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
      1 ≤ countPop H .recT1 + countPop H .t4 → 1 ≤ vdisc f) :
    WeightChargeFullP n X K := by
  sorry

/-- KD4 — `weightChargeT4_of_trackCount`: the T4-burden variant, same
premises: countPop H .t4 ≤ the full count ≤ L, then the KD3 case split
verbatim.  deps: KD3 (expected discharge: monotonicity of the count +
KD3's argument, or directly `Nat.le_trans` into KD3's conclusion shape).
Same F3 status note as KD3. -/
theorem weightChargeT4_of_trackCount {n : ℕ} (X : XFamily n)
    (K : XConsts n) (L : ℕ) (hsK : K.s = L)
    (htrack : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
      countPop H .recT1 + countPop H .t4 ≤ L)
    (hrec : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
      1 ≤ countPop H .recT1 + countPop H .t4 → 1 ≤ vdisc f) :
    WeightChargeT4P n X K := by
  sorry

end LeanUrat.Kernels
