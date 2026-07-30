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
KD1 PASSED 2026-07-30 (exit 0; REC-DISC clean on both boxes) — KD2 prover
unblocked.

⚑ KD2b FALLBACK EXECUTED (2026-07-30, prover pass; flagged for orchestrator
ratification per Q4).  The skeleton's own RECORDED RESOLUTION + FALLBACK
clause fired: `GMNIndex` carries only ind/inStratum/p2 — NO law in any
corpus ties `inStratum`'s recentering populations to f̄'s factorization
(verified by grep over every `inStratum` consumer: only `gmnLink` and the
kernel Props touch it, none constrain it), so KD2 AS A BARE ∀-X STATEMENT
is unprovable (countermodel SHAPE, recorded for the countermodel gate:
inStratum := fun _ _ => True with ind := 0 satisfies every GMNIndex/XFamily
law, and any f with unit discriminant + the T1-recentering node
⟨e=1,ℓ=2,h=1,s0=0,u0=0,sel=some(1,1),inc=false⟩ then violates the
conclusion; compiling it needs a full junk XCtx — orchestrator's call).
Per the pre-declared fallback (blueprint §4 KD2 verbatim + the cluster
briefing): the classifier leg is hoisted to the ⚑ NAMED hypothesis
`RecImpliesWild` (hypothesis shape, never a new field on the frozen
structures), the mod-p discriminant lemma KD2a is proved UNCONDITIONALLY
(`kd2a_vdisc_pos_of_not_squarefree`, via OM/Discriminant.lean's
`discr_map_monic` resultant route), and the head `recentering_vdisc_pos`
carries `hwild : RecImpliesWild n X` as its (only) new premise — the ONE
sanctioned statement delta of this file; KD3/KD4 below are byte-identical
to the skeleton.  Discharge duty for `RecImpliesWild`: the real-instance
classifier (HC-2/OM engine wave) — a recentering read presupposes a
non-hen root read, i.e. a repeated factor of f̄ (the (c2)/(R) covering law).

Build: cd lean && lake build LeanUrat.Kernels.WeightChargeRed
-/
import LeanUrat.MovesX.Defs
import LeanUrat.OM.Discriminant

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesX

/-- The mod-`p` residue of `w : ℤ_[p]` vanishes exactly on the divisibility
locus.  (Verbatim the proof of `OM.QpTypeChainLeaves.toZMod_eq_zero_iff`,
inlined to keep this file's import cone at OM/Discriminant only.) -/
private theorem toZMod_eq_zero_iff_dvd {p : ℕ} [Fact p.Prime] (w : ℤ_[p]) :
    PadicInt.toZMod w = 0 ↔ (p : ℤ_[p]) ∣ w := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/-- KD2a — the mod-p discriminant lemma, UNCONDITIONAL (the pre-approved
split's arithmetic leg): if the reduction f̄ = f mod p has a repeated factor
(¬ Squarefree), then p ∣ disc f, i.e. 1 ≤ vdisc f (off discZero).
Route: ¬Squarefree f̄ ⟹ ¬Separable f̄ (`Separable.squarefree`) ⟹
¬IsCoprime f̄ f̄′ (`separable_def`) ⟹ resultant f̄ f̄′ = 0 over the field
ZMod p (`isUnit_resultant_iff_isCoprime` + `isUnit_iff_ne_zero`) ⟹
discr f̄ = 0 (`discr_monic_eq_resultant` + `resultant_deriv_eq_default`) ⟹
toZMod (disc f) = 0 (`discr_map_monic` naturality) ⟹ p ∣ disc f ⟹
1 ≤ valuation (disc f ≠ 0). -/
theorem kd2a_vdisc_pos_of_not_squarefree {n p : ℕ} [Fact p.Prime]
    (f : MonicBox n p) (hf : f ∉ discZero n p)
    (hns : ¬ Squarefree (f.1.map (PadicInt.toZMod))) :
    1 ≤ vdisc f := by
  have hd0 : f.1.discr ≠ 0 := hf
  have hmonic : (f.1.map (PadicInt.toZMod)).Monic := f.2.1.map _
  -- degree is positive, else f̄ = 1 is squarefree — contradiction with hns
  have hdegpos : 0 < (f.1.map (PadicInt.toZMod)).natDegree := by
    rcases Nat.eq_zero_or_pos (f.1.map (PadicInt.toZMod)).natDegree with h0 | h
    · exact absurd (by
        rw [Polynomial.eq_one_of_monic_natDegree_zero hmonic h0]
        exact squarefree_one) hns
    · exact h
  -- not squarefree ⟹ not separable ⟹ not coprime with the derivative
  have hncop : ¬ IsCoprime (f.1.map (PadicInt.toZMod))
      (f.1.map (PadicInt.toZMod)).derivative := fun hcop =>
    hns (Polynomial.Separable.squarefree ((Polynomial.separable_def _).mpr hcop))
  -- resultant vanishes over the field ZMod p
  have hres0 : Polynomial.resultant (f.1.map (PadicInt.toZMod))
      (f.1.map (PadicInt.toZMod)).derivative = 0 := by
    by_contra hne
    exact hncop ((Polynomial.isUnit_resultant_iff_isCoprime hmonic).mp
      (isUnit_iff_ne_zero.mpr hne))
  -- discr f̄ = 0
  have hdiscr0 : (f.1.map (PadicInt.toZMod)).discr = 0 := by
    rw [LeanUrat.OM.M_F4.discr_monic_eq_resultant _ hmonic hdegpos,
      LeanUrat.OM.M_F4.resultant_deriv_eq_default hmonic, hres0, mul_zero]
  -- naturality: toZMod (disc f) = discr f̄ = 0, so p ∣ disc f
  have hmap : PadicInt.toZMod f.1.discr = 0 := by
    rw [← LeanUrat.OM.M_F4.discr_map_monic (PadicInt.toZMod) f.1 f.2.1]
    exact hdiscr0
  have hdvd : (p : ℤ_[p]) ∣ f.1.discr := (toZMod_eq_zero_iff_dvd _).mp hmap
  -- 1 ≤ valuation of a nonzero multiple of p
  have h1 : 1 ≤ (f.1.discr).valuation :=
    (PadicInt.mem_span_pow_iff_le_valuation _ hd0 1).mp
      (by rw [Ideal.mem_span_singleton, pow_one]; exact hdvd)
  exact h1

/-- KD2b — ⚑ the NAMED classifier-leg hypothesis `RecImpliesWild` (Q4 shape:
hypothesis, never a new field on the frozen structures; pre-declared
fallback of the blueprint's §4 KD2 clause, executed 2026-07-30 — see the
file header for the obstruction record).  Content: on a stratum history
off discZero, ≥ 1 recentering-population node forces a repeated factor of
f̄ = f mod p ("a recentering presupposes a non-hen root read" — the
(c2)/(R) covering law of §3.B).  Discharge owner: the real-instance
classifier (HC-2/OM engine). -/
def RecImpliesWild (n : ℕ) (X : XFamily n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H →
    1 ≤ countPop H .recT1 + countPop H .t4 →
    ¬ Squarefree (f.1.map (PadicInt.toZMod))

/-- KD2 — `recentering_vdisc_pos` (REC-DISC): H in the stratum of f,
f ∉ discZero, countPop H .recT1 + countPop H .t4 ≥ 1 ⟹ 1 ≤ vdisc f.
deps: KD1 clean (CM gate — PASSED 2026-07-30, exit 0: no f with a
recentering and vdisc = 0 in either box).
⚑ AS-BUILT (fallback executed; the skeleton's own pre-declared resolution):
the bare ∀-X statement is unprovable — `GMNIndex` carries no law tying
`inStratum` to f̄'s factorization (full obstruction record in the file
header) — so the classifier leg rides the NAMED hypothesis
`hwild : RecImpliesWild n X` (the ONE statement delta of this file, Q4
shape, flagged for ratification), and the arithmetic leg is the
unconditional KD2a above.  Proof = KD2a ∘ hwild. -/
theorem recentering_vdisc_pos {n : ℕ} (X : XFamily n)
    (hwild : RecImpliesWild n X) :
    ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
      1 ≤ countPop H .recT1 + countPop H .t4 →
      1 ≤ vdisc f := by
  intro p hp f H hf hstrat hcount
  exact kd2a_vdisc_pos_of_not_squarefree f hf (hwild p f H hf hstrat hcount)

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
  intro p hp f H hf hstrat
  rcases Nat.eq_zero_or_pos (countPop H .recT1 + countPop H .t4) with h0 | h1
  · simp only [h0]
    exact Nat.zero_le _
  · have hv : 1 ≤ vdisc f := hrec p f H hf hstrat h1
    calc countPop H .recT1 + countPop H .t4
        ≤ L := htrack p f H hf hstrat
      _ = L * 1 := (mul_one L).symm
      _ ≤ L * vdisc f := Nat.mul_le_mul_left L hv
      _ = K.s * vdisc f := by rw [hsK]

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
  intro p hp f H hf hstrat
  exact Nat.le_trans (Nat.le_add_left _ _)
    (weightChargeFull_of_trackCount X K L hsK htrack hrec p f H hf hstrat)

end LeanUrat.Kernels
