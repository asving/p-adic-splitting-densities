/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeE0_zpCountermodel

/-!
# IB-E12 — THE IP-1 BOUNDARY GATE (bridge campaign BP1; runs BEFORE IB-E4)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §4 group E
(IB-E12, post-Codex finding 7) and §3.6 (†11c).  A genuine falsification attempt
at IP-1's universal, run before its prover.

THE UNIVERSAL UNDER ATTACK (†11c, stated below as `IP1`): h monic over ℤ_p with
ℚ_p-irreducible image ⇒ `IsLocalRing (AdjoinRoot h)`.  (Degree positivity is
DERIVABLE — a monic degree-0 polynomial is 1, whose image is a unit, never
irreducible — so it is not a separate binder; resolution recorded here.)

SEALED PREDICTIONS (recorded before any proving):
(a) NEAR-MISS — irreducibility is LOAD-BEARING: at every odd prime p,
    `¬ IsLocalRing (AdjoinRoot (X² − 1 : ℤ_p[X]))`.  X² − 1 = (X−1)(X+1) with
    X−1, X+1 coprime over ℤ_p (2 is a unit at odd p), so CRT splits
    AdjoinRoot ≅ ℤ_p × ℤ_p — a nontrivial idempotent, two maximal ideals.
(b) STRESS CHECK (positive evidence, kept SEPARATE from the gate): E0's
    NON-MAXIMAL order X² + 9 at p = 3 still satisfies IP-1's conclusion —
    locality ≠ maximality; wired verbatim from E0a (`e0_isLocalRing`).
(c) MEMO — candidate failure classes for IP-1 itself, enumerated (NONE expected):
    (i)  h reducible over ℚ_p — excluded by hypothesis; (a) shows the exclusion
         is necessary (the gate's content);
    (ii) h constant/unit — excluded: monic + irreducible image forces degree ≥ 1;
    (iii) `AdjoinRoot h` not a domain — cannot happen: monic h with irreducible
         ℚ_p-image is prime in the UFD ℤ_p[X] (Gauss), so the quotient is a domain;
    (iv) infinite/limit pathologies — cannot happen: AdjoinRoot h is a finite free
         ℤ_p-module; ℤ_p is complete local hence HENSELIAN, a finite algebra over a
         henselian local ring is a finite product of local rings, and a domain
         admits no nontrivial idempotents, so exactly one factor survives.
    If, against prediction, a genuine countermodel to IP-1 lands, IB-E4 is
    BLOCKED → orchestrator adjudication (blueprint E12 disposition).

Deps: IB-E0 (locality-machinery reuse for the stress check).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- IP-1 (†11c), THE UNIVERSAL THE GATE ATTACKS — the §9 instance-plumbing law
    `ZpBridge`'s docstring residue (ii) names: for monic h over ℤ_p with
    ℚ_p-irreducible image, the order `AdjoinRoot h` is local.  Stated as a named
    Prop so IB-E4's prover and this gate speak about the SAME sentence.
    (Resolution recorded: no `0 < h.natDegree` binder — derivable, see header.) -/
def IP1 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ h : Polynomial ℤ_[p], h.Monic → Irreducible (h.map PadicInt.Coe.ringHom) →
    IsLocalRing (AdjoinRoot h)

/-- E12(a) piece: the near-miss witness is monic (so ONLY the irreducibility
    hypothesis of `IP1` separates it from the conclusion-violating split). -/
theorem e12_nearMiss_monic (p : ℕ) [Fact p.Prime] :
    (X ^ 2 - 1 : Polynomial ℤ_[p]).Monic := by
  simpa using monic_X_pow_sub_C (1 : ℤ_[p]) (two_ne_zero)

/-- E12(a) — THE NEAR-MISS: at odd p, `AdjoinRoot (X² − 1)` is NOT local.
    X² − 1 = (X − 1)(X + 1), the factors are coprime (their difference is the
    unit 2), CRT gives AdjoinRoot ≅ ℤ_p × ℤ_p — a nontrivial idempotent kills
    locality.  This compiles the claim that `IP1`'s irreducibility hypothesis is
    LOAD-BEARING: the falsification attempt at the full universal stops exactly
    here, and no attack surface survives inside the hypotheses (memo (c)). -/
theorem e12_squareSplit_not_local (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ IsLocalRing (AdjoinRoot (X ^ 2 - 1 : Polynomial ℤ_[p])) := by
  intro hLocal
  haveI := hLocal
  set f : Polynomial ℤ_[p] := X ^ 2 - 1 with hf
  set r : AdjoinRoot f := AdjoinRoot.root f with hrdef
  -- (0) 2 is a unit in ℤ_[p] at odd p (norm 1: p ∤ 2)
  have h2 : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
    have hcast : ((2 : ℤ) : ℤ_[p]) = (2 : ℤ_[p]) := by norm_cast
    rw [← hcast] at hlt
    have hdvdZ : (p : ℤ) ∣ 2 := (PadicInt.norm_int_lt_one_iff_dvd 2).mp hlt
    have hdvdN : p ∣ 2 := by exact_mod_cast hdvdZ
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvdN)
  -- ... hence in AdjoinRoot f
  have h2A : IsUnit (2 : AdjoinRoot f) := by
    have h := h2.map (AdjoinRoot.of f)
    rwa [map_ofNat] at h
  -- (1) the root squares to 1
  have hsq : r ^ 2 = 1 := by
    have h1 : r ^ 2 - 1 = 0 := by
      calc r ^ 2 - 1
          = AdjoinRoot.mk f (X ^ 2 - 1) := by
            rw [map_sub, map_pow, map_one, AdjoinRoot.mk_X]
        _ = 0 := hf ▸ AdjoinRoot.mk_self
    exact sub_eq_zero.mp h1
  -- (2) the idempotent pair: (1+r) + (1−r) = 2 is a unit, (1+r)(1−r) = 1 − r² = 0
  have hsum : IsUnit ((1 + r) + (1 - r)) := by
    have heq : (1 + r) + (1 - r) = (2 : AdjoinRoot f) := by ring
    rw [heq]; exact h2A
  have hprod : (1 + r) * (1 - r) = 0 := by
    have heq : (1 + r) * (1 - r) = 1 - r ^ 2 := by ring
    rw [heq, hsq, sub_self]
  -- (3) locality forces one factor to be a unit, hence the other to vanish;
  --     either way the root is ±1, i.e. f ∣ X ∓ 1 — killed by degrees (2 ≤ 1)
  have hfdeg : f.natDegree = 2 := by
    rw [hf]
    simpa using natDegree_X_pow_sub_C (n := 2) (r := (1 : ℤ_[p]))
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
  · -- 1 + r a unit ⇒ 1 − r = 0 ⇒ r = 1 ⇒ f ∣ X − 1
    have hb0 : (1 - r) = 0 := (hu.mul_right_eq_zero).mp hprod
    have hr1 : r = 1 := (sub_eq_zero.mp hb0).symm
    have hmk : AdjoinRoot.mk f (X - C 1) = 0 := by
      rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one, ← hrdef, hr1, sub_self]
    have hdvd : f ∣ (X - C 1 : Polynomial ℤ_[p]) := AdjoinRoot.mk_eq_zero.mp hmk
    have hled := natDegree_le_of_dvd hdvd (X_sub_C_ne_zero (1 : ℤ_[p]))
    rw [hfdeg, natDegree_X_sub_C] at hled
    omega
  · -- 1 − r a unit ⇒ 1 + r = 0 ⇒ r = −1 ⇒ f ∣ X + 1
    have ha0 : (1 + r) = 0 := (hu.mul_left_eq_zero).mp hprod
    have hmk : AdjoinRoot.mk f (X + C 1) = 0 := by
      rw [map_add, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one, ← hrdef, add_comm]
      exact ha0
    have hdvd : f ∣ (X + C 1 : Polynomial ℤ_[p]) := AdjoinRoot.mk_eq_zero.mp hmk
    have hled := natDegree_le_of_dvd hdvd (X_add_C_ne_zero (1 : ℤ_[p]))
    rw [hfdeg, natDegree_X_add_C] at hled
    omega

/-- E12(b) — STRESS CHECK, wired from E0a (positive evidence, separate decl per
    the blueprint): the NON-MAXIMAL order `ℤ_3[3√−1] = AdjoinRoot (X² + 9)`
    still satisfies IP-1's conclusion — locality ≠ maximality, so E0's
    countermodel does NOT propagate into a countermodel of IP-1. -/
theorem e12_stress_e0_order_local : IsLocalRing (AdjoinRoot e0Poly) :=
  e0_isLocalRing

end LeanUrat.MovesU
