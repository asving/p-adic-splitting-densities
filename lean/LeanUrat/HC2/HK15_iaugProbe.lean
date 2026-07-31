/-
Unit HK-15-PROBE — the COMPILED IAug PROBE for `gateChildStage` (queue item 16 evidence;
PROBE-C round, 2026-07-31).

WHAT IS EVIDENCED (round-3 SUSPECT-FALSE record, upgraded here to evidence-complete).
`LeanUrat/HC2/HK15_gateChildCarrier.lean:94–98` states (sorried E-phase skeleton):

  noncomputable def gateChildStage (e' h' : ℕ) (s' t' : ℤ)
      (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
      (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0) :
      Stage 2 F4

together with its unconditional pair pins (`gateChildStage_pair`: `σ₁.(e,h,s,t) =
(e',h',s',t')`) and key pin (`gateChildStage_Phi`: `σ₁.Φ = U31.fq`).  The stated
hypothesis list is TOO WEAK: the tuple `(e',h',s',t') = (1,1,1,0)` satisfies every
stated hypothesis (compiled below as `gateTuple_satisfies_hyps`), yet the read pair
`(e',h') = (1,1)` at the key `Φ̂ = U31.fq` over the carrier `bStageP` VIOLATES (I-aug) —
`(h' : ℤ) > e' · bStageP.w U31.fq` — because `bStageP.w U31.fq = 2` (compiled below:
`bStageP_w_fq`, the HK-47:174 value re-derived; the violation is `¬((1:ℤ) > 1·2)`,
compiled as `gateTuple_iaug_violation` / `gateTuple_not_IAug`).  So no genuine D.4/D.7
child stage of the root read exists at that tuple: any faithful σ₁ construction (HK-18's
`hiaug` consumption; HK-47's TransHyp head takes `(e',h') = (1,3)`, whose (I-aug) HOLDS)
is impossible at `(1,1,1,0)`, while the sorried `gateChildStage` + its unconditional
pins CLAIM one.  Repair is a statement-fence event (add the (I-aug) guard to the
hypothesis row, or key σ₁'s pins to it), owned by the designer queue — never a prover
fill.

M1 COEXISTENCE DISCIPLINE.  This file does NOT import `HK15_gateChildCarrier` (the
module holding the sorried `gateChildStage` and its sorried pin universals).  The
hypothesis Props of `gateChildStage`'s statement row are restated below as byte-identical
LOCAL COPIES instantiated at the tuple (provenance of every conjunct:
`HK15_gateChildCarrier.lean:95–96`, binders `he' hh' hcop hbez he1t`).  The carrier
vocabulary (`bStageP`, `U31.fq`, `U31.bw_eq`, `HK13R.NF_θ_fq`, `IAug`) is imported from
its sorry-free home modules (`HC2/HK13_bStageCoreP1a` — grep-verified sorry-free,
2026-07-31 — and the definitions-only `Moves/Defs` via the `HC2/Defs` chain), NOT
copied.  `HK47` is NOT imported (its w = 2 value `HK47.lean:174` is re-derived here by
the same term `U31.bw_eq HK13R.NF_θ_fq`).

deps: HC2.HK13_bStageCoreP1a (the `bStageP` carrier + `HK13R.NF_θ_fq`; sorry-free).
axioms: Lean core only.

M1 DATED NOTE (2026-07-31, queue item 16 EXECUTED — Asvin sign-off on the consolidated
queue): this leaf refutes the OLD (pre-hiaug) form of the `gateChildStage` family ONLY —
the hypothesis row quoted above (provenance `HK15_gateChildCarrier.lean:95–96` at the
PRE-repair HEAD: binders `he' hh' hcop hbez he1t`, no steepness guard). At the repaired
HEAD the family carries `hiaug : IAug bStageP U31.fq e' h'` and is DISCHARGED (all six
sorries; S9-forged σ₁): the probe's tuple (1,1,1,0) now FAILS the hypothesis row —
`gateTuple_not_IAug` below is exactly the certificate that `hiaug` excludes it. The
leaf stays intact as the durable fence evidence; the refuted hypothesis-row shape now
exists only as the local copies in this file (M1 coexistence rule satisfied).
-/
import Mathlib
import LeanUrat.HC2.HK13_bStageCoreP1a

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

namespace HK15Probe

/-- (a) THE TUPLE SATISFIES THE STATED HYPOTHESIS LIST.  Byte-identical LOCAL COPIES of
`gateChildStage`'s five hypothesis Props (provenance: `HK15_gateChildCarrier.lean:95–96`,
binders `he' : 1 ≤ e'`, `hh' : 1 ≤ h'`, `hcop : Nat.gcd e' h' = 1`,
`hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1`, `he1t : e' = 1 → t' = 0`), instantiated at
`(e', h', s', t') = (1, 1, 1, 0)`.  [PROBE-C, queue item 16.] -/
theorem gateTuple_satisfies_hyps :
    (1 ≤ (1 : ℕ)) ∧ (1 ≤ (1 : ℕ)) ∧ (Nat.gcd 1 1 = 1) ∧
    (((1 : ℕ) : ℤ) * (1 : ℤ) + ((1 : ℕ) : ℤ) * (0 : ℤ) = 1) ∧
    ((1 : ℕ) = 1 → (0 : ℤ) = 0) :=
  ⟨le_refl 1, le_refl 1, by norm_num, by norm_num, fun _ => rfl⟩

/-- The carrier weight of the landing key: `bStageP.w U31.fq = 2` — the value PROVEN at
`HK47.lean:174`, re-derived here by the same term (`U31.bw_eq` at `HK13R.NF_θ_fq`;
`bStageP.w = U31.bw` is definitional).  [PROBE-C, queue item 16.] -/
theorem bStageP_w_fq : bStageP.w U31.fq = 2 := U31.bw_eq HK13R.NF_θ_fq

/-- (b) THE (I-aug) VIOLATION at the tuple, raw-inequality form: with `(e', h') = (1, 1)`
the (I-aug) head `(h' : ℤ) > e' · bStageP.w U31.fq` is FALSE — it reads `1 > 1·2`.
[PROBE-C, queue item 16.] -/
theorem gateTuple_iaug_violation : ¬ ((1 : ℤ) > (1 : ℤ) * bStageP.w U31.fq) := by
  rw [bStageP_w_fq]
  norm_num

/-- (b′) THE (I-aug) VIOLATION, named-predicate form: `IAug bStageP U31.fq 1 1` is FALSE
(`IAug σ Φhat e' h' := (h' : ℤ) > (e' : ℤ) * σ.w Φhat`, `Moves/Defs.lean:241` —
definitions-only module, imported not copied).  [PROBE-C, queue item 16.] -/
theorem gateTuple_not_IAug : ¬ IAug bStageP U31.fq 1 1 := by
  intro h
  unfold IAug at h
  rw [bStageP_w_fq] at h
  norm_num at h

end HK15Probe

-- Axiom audit: Lean core only ({propext, Classical.choice, Quot.sound}).
#print axioms HK15Probe.gateTuple_satisfies_hyps
#print axioms HK15Probe.bStageP_w_fq
#print axioms HK15Probe.gateTuple_iaug_violation
#print axioms HK15Probe.gateTuple_not_IAug

end LeanUrat.MovesJ
