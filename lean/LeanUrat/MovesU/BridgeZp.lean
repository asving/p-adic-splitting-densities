/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeE12_ip1Gate

/-!
# BridgeZp — BP1 group E, the genuine ℤ_p[X] side (cluster BP1-c8)

E-phase skeletons per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.6
(†11a)–(†11e), §4 group E, and `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`.
Units in this file: **IB-E1, IB-E2, IB-E3, IB-E11, IB-E8, IB-E10, IB-E4**.

NOT in this file (other owners): IB-E0/IB-E12 (the gates — already landed as
`BridgeE0_zpCountermodel.lean` / `BridgeE12_ip1Gate.lean`), IB-E5/E6/E7 (the
`zf_pos`/pointwise-(e·f=deg)/`zf_factor` LAWS — **Q2-GATED** on the
`MovesT.ramIdx`/`resDeg` repair, adjudications file), IB-E9 (the `bridgeZpBridge`
assembly), IB-D9a/D9b (trueType def + `lift_true`, group D).  Everything HERE is
Q2-stable: `bridgeZfType` (IB-E11) is textually stable (it reads whatever
`ramIdx`/`resDeg` the repair lands — blueprint E11), and no statement below
constrains the (e, f) values.

TRANSCRIPTION RESOLUTIONS (statement fence; recorded per E-phase rule):
1. `monicFactors` is TOTAL on `Polynomial ℤ_[p]` (junk on non-monic inputs, the
   MovesT junk-dispatch style) so that IB-E11's def matches `ZpBridge.zfType`'s
   total signature (DefsLedger.lean:722); all its LAWS carry the `Monic`
   hypothesis, per (†11a) "for monic g".
2. The blueprint names IB-E11's deliverable `zfType`; here it is `bridgeZfType`,
   per the area's `bridge*` family convention (`bridgeRegData`, `bridgeSolve`,
   `bridgeCanonical`, …) and to avoid field-name shadowing in IB-E9's record
   literal (`zfType := bridgeZfType`).
3. IB-E3's Gauss transfer is stated over `PadicInt.Coe.ringHom` (the repo
   vocabulary — `ZpBridge.zf_factor`, IB-E0) rather than `algebraMap ℤ_[p] ℚ_[p]`;
   the two are THE SAME subring inclusion (`padicCoe_eq_algebraMap` below, rfl).
4. IB-E3 keeps the (derivable) `0 < h.natDegree` binder — (†11b) says "with
   positive degree" verbatim, and IB-E2 supplies it at the consumers.
5. IB-E10 is stated at (N, f) — two σ's satisfying the ∀-lift predicate
   `ZpReads` agree — consuming IB-E8's lift internally, per its blueprint deps
   (E11, E8) and (†8u)'s "uniqueness rides ONE lift".
6. IB-E4 states `IP1 p` VERBATIM from IB-E12's named Prop (the gate's "same
   sentence" discipline, BridgeE12_ip1Gate.lean).

Build: `lake build LeanUrat.MovesU.BridgeZp`.  Orchestrator note: MANIFEST.json's
BRIDGE section (blueprint §7 acceptance) is NOT edited here (frozen file).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ## IB-E1 — ℤ_p[X] UFD wiring + `monicFactors` + the product law (†11a)

Informal statement: ℤ_p is a DVR, hence ℤ_p[X] is a UFD; for monic g the
multiset `monicFactors g` of monic irreducible factors exists with
`(monicFactors g).prod = g`.  Deps: none.  Sketch (†11a): extract from
`UniqueFactorizationMonoid.factors g` by scaling each factor monic — units of
ℤ_p[X] are units of ℤ_p, and each factor of a monic polynomial over a domain
has unit leading coefficient (leadingCoeff multiplicativity); the unit product
telescopes to 1 by comparing leading coefficients.  Pre-approved split:
E1a (def + factor monic), E1b (prod law). -/

/-- IB-E1 wiring record (†11a, compiled verification): `ℤ_p` is a UFD — the
    pinned-Mathlib instance chain `IsDiscreteValuationRing ℤ_[p]`
    (PadicIntegers.lean:521) → `IsPrincipalIdealRing` →
    `to_uniqueFactorizationMonoid` synthesizes.  Verified 2026-07-30. -/
theorem padicInt_ufd : UniqueFactorizationMonoid ℤ_[p] := inferInstance

/-- IB-E1 wiring record (†11a, compiled verification): hence `ℤ_p[X]` is a UFD
    (`Polynomial.uniqueFactorizationMonoid`, priority-100 instance over a
    domain UFD).  Verified 2026-07-30. -/
theorem padicInt_poly_ufd : UniqueFactorizationMonoid (Polynomial ℤ_[p]) :=
  inferInstance

/-- IB-E1a (†11a) — THE MONIC FACTOR MULTISET: for monic g, the multiset of
    monic irreducible ℤ_p[X]-factors of g, extracted from
    `UniqueFactorizationMonoid.factors g` by scaling each factor monic.
    TOTAL (junk on non-monic inputs — resolution 1 in the module header);
    every law about it carries the `Monic` hypothesis. -/
noncomputable def monicFactors (g : Polynomial ℤ_[p]) :
    Multiset (Polynomial ℤ_[p]) :=
  (UniqueFactorizationMonoid.factors g).map
    fun h => C (Ring.inverse h.leadingCoeff) * h

/-- Proof-internal helper (IB-E1/IB-E2, NOT a fenced statement): every UFD
    factor of a monic polynomial over the domain ℤ_p[X] has unit leading
    coefficient — leadingCoeff multiplicativity at a factorization g = q·k. -/
theorem leadingCoeff_isUnit_of_mem_factors (g : Polynomial ℤ_[p]) (hg : g.Monic)
    (q : Polynomial ℤ_[p]) (hq : q ∈ UniqueFactorizationMonoid.factors g) :
    IsUnit q.leadingCoeff := by
  obtain ⟨k, hk⟩ := UniqueFactorizationMonoid.dvd_of_mem_factors hq
  have h2 := congrArg Polynomial.leadingCoeff hk
  rw [Polynomial.leadingCoeff_mul, hg.leadingCoeff] at h2
  exact IsUnit.of_mul_eq_one _ h2.symm

/-- IB-E1a (†11a) — each extracted factor is monic.  Deps: `monicFactors`.
    Sketch: each UFD factor of monic g has unit leading coefficient
    (leadingCoeff multiplicativity in the domain ℤ_p[X]); the extraction scales
    by that unit's inverse. -/
theorem monicFactors_monic (g : Polynomial ℤ_[p]) (hg : g.Monic) :
    ∀ h ∈ monicFactors g, h.Monic := by
  intro h hmem
  unfold monicFactors at hmem
  rw [Multiset.mem_map] at hmem
  obtain ⟨q, hq, rfl⟩ := hmem
  have hu := leadingCoeff_isUnit_of_mem_factors g hg q hq
  change (C (Ring.inverse q.leadingCoeff) * q).leadingCoeff = 1
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  exact Ring.inverse_mul_cancel _ hu

/-- IB-E1b (†11a) — THE PRODUCT LAW: the monic-scaled factors multiply back to
    g.  Deps: `monicFactors`.  Sketch: `UniqueFactorizationMonoid.factors_prod`
    gives (factors g).prod = g up to a unit; after the monic rescale the
    residual unit is a monic unit of ℤ_p[X], i.e. a unit CONSTANT with leading
    coefficient 1, hence 1 (compare leading coefficients — the telescoping of
    †11a). -/
theorem monicFactors_prod (g : Polynomial ℤ_[p]) (hg : g.Monic) :
    (monicFactors g).prod = g := by
  have hmon : (monicFactors g).prod.Monic := by
    have h := Polynomial.monic_multiset_prod_of_monic (monicFactors g) id
      (fun h hh => monicFactors_monic g hg h hh)
    rwa [Multiset.map_id] at h
  have hcunit : IsUnit (((UniqueFactorizationMonoid.factors g).map
      fun h => (C (Ring.inverse h.leadingCoeff) : Polynomial ℤ_[p])).prod) := by
    refine Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    exact Polynomial.isUnit_C.mpr
      (leadingCoeff_isUnit_of_mem_factors g hg q hq).ringInverse
  have hassoc : Associated (monicFactors g).prod g := by
    refine Associated.trans ?_ (UniqueFactorizationMonoid.factors_prod hg.ne_zero)
    unfold monicFactors
    rw [Multiset.prod_map_mul]
    have hid : ((UniqueFactorizationMonoid.factors g).map fun h => h).prod
        = (UniqueFactorizationMonoid.factors g).prod := by
      rw [Multiset.map_id']
    rw [hid]
    exact associated_unit_mul_left _ _ hcunit
  exact Polynomial.eq_of_monic_of_associated hmon hg hassoc

/-! ## IB-E2 — factors irreducible in ℤ_p[X] + degree-positive

Informal statement: every element of `monicFactors g` (g monic) is irreducible
in ℤ_p[X] and has positive natDegree.  Deps: IB-E1.  Sketch: irreducibility is
unit-multiple-invariant (`Irreducible` transfers along `Associated`, and the
monic rescale is a unit multiple of a `UniqueFactorizationMonoid.factors`
element, which is irreducible by `UniqueFactorizationMonoid.irreducible_of_factor`);
a monic degree-0 polynomial is 1, a unit, never irreducible — so positive
degree follows (†11b's "degree-0 factors cannot occur"). -/

/-- IB-E2 — each monic factor is irreducible in ℤ_p[X]. -/
theorem monicFactors_irreducible (g : Polynomial ℤ_[p]) (hg : g.Monic) :
    ∀ h ∈ monicFactors g, Irreducible h := by
  intro h hmem
  unfold monicFactors at hmem
  rw [Multiset.mem_map] at hmem
  obtain ⟨q, hq, rfl⟩ := hmem
  have hirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_factor q hq
  have hu : IsUnit (C (Ring.inverse q.leadingCoeff) : Polynomial ℤ_[p]) :=
    Polynomial.isUnit_C.mpr
      (leadingCoeff_isUnit_of_mem_factors g hg q hq).ringInverse
  exact ((associated_unit_mul_left q _ hu).symm).irreducible hirr

/-- IB-E2 — each monic factor has positive degree (a monic degree-0 polynomial
    is 1, a unit, contradicting irreducibility). -/
theorem monicFactors_natDegree_pos (g : Polynomial ℤ_[p]) (hg : g.Monic) :
    ∀ h ∈ monicFactors g, 0 < h.natDegree := by
  intro h hmem
  have hmon := monicFactors_monic g hg h hmem
  have hirr := monicFactors_irreducible g hg h hmem
  by_contra hnot
  have hzero : h.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have h1 : h = 1 := hmon.natDegree_eq_zero.mp hzero
  rw [h1] at hirr
  exact hirr.not_isUnit isUnit_one

/-! ## IB-E3 — Gauss transfer (†11b) + the `IsFractionRing ℤ_[p] ℚ_[p]` VERIFY

Informal statement: a monic irreducible of ℤ_p[X] with positive degree is
irreducible over ℚ_p.  Deps: IB-E2.  Sketch:
`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (pinned Mathlib:
GaussLemma.lean:149, hypothesis `[IsIntegrallyClosed ℤ_[p]]` — a DVR is a UFD
is integrally closed, instance chain) at `IsFractionRing ℤ_[p] ℚ_[p]`, then
rewrite `algebraMap` to `PadicInt.Coe.ringHom` (they are equal — below).

VERIFY OUTCOME (the unit's archaeology charge, resolved 2026-07-30): the
instance EXISTS in the pinned Mathlib — `PadicInt.isFractionRing`
(Mathlib/NumberTheory/Padics/PadicIntegers.lean:564), riding
`PadicInt.algebra : Algebra ℤ_[p] ℚ_[p]` (ibid.:557) whose `algebraMap` is the
subring inclusion with `PadicInt.algebraMap_apply : algebraMap ℤ_[p] ℚ_[p] x = x`
by rfl.  No new instance owed; the records below compile the verification. -/

/-- IB-E3 verify record (compiled): `IsFractionRing ℤ_[p] ℚ_[p]` synthesizes
    from the pinned Mathlib (`PadicInt.isFractionRing`). -/
theorem padicInt_isFractionRing : IsFractionRing ℤ_[p] ℚ_[p] := inferInstance

/-- IB-E3 verify record (compiled): the repo's coercion `PadicInt.Coe.ringHom`
    (= `(PadicInt.subring p).subtype`) IS the `algebraMap` of
    `PadicInt.algebra` — so the Mathlib fraction-field Gauss lemma speaks about
    the same map `ZpBridge.zf_factor` uses. -/
theorem padicCoe_eq_algebraMap :
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] :=
  rfl

/-- IB-E3 (†11b) — GAUSS TRANSFER: a monic irreducible of ℤ_p[X] with positive
    degree is irreducible over ℚ_p.  (The degree binder is derivable — monic +
    irreducible forces degree ≥ 1 — kept per (†11b)'s verbatim statement;
    resolution 4 in the module header.) -/
theorem monic_irreducible_map_coe (h : Polynomial ℤ_[p]) (hm : h.Monic)
    (hdeg : 0 < h.natDegree) (hirr : Irreducible h) :
    Irreducible (h.map PadicInt.Coe.ringHom) := by
  rw [padicCoe_eq_algebraMap]
  exact (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirr

/-! ## IB-E11 — the `zfType` reading, DEF only

Informal statement: the ℤ_p factorization-type reading
`g ↦ multiset of (ramIdx h, resDeg h) over the monic irreducible factors h`.
Deps: IB-E1 (the def only — NOT the assembly IB-E9; split per post-Codex
finding 1 to break the D9/E9/E10 cycle).  Q2-STABILITY: textually stable — it
reads whatever `MovesT.ramIdx`/`resDeg` the Q2 repair lands; its LAWS
(zf_pos/zf_factor conjuncts) stay Q2-gated at IB-E5–E7, NOT here. -/

/-- IB-E11 — `bridgeZfType` (the blueprint's `zfType`; resolution 2 in the
    module header): the factorization-type reading feeding `ZpBridge.zfType`
    at IB-E9 and `bridgeTrueType` at IB-D9a. -/
noncomputable def bridgeZfType (g : Polynomial ℤ_[p]) : Multiset (ℕ × ℕ) :=
  (monicFactors g).map (fun h => (MovesT.ramIdx h, MovesT.resDeg h))

/-! ## IB-E8 — `lift_exists` (†11d)

Informal statement: every level-N box class f has a monic degree-n ℤ_p lift
through `PadicInt.toZModPow N`.  Deps: none.  Sketch (†11d): the explicit
witness g := Xⁿ + Σ_i C ((f i).val : ℤ_[p]) X^i — monic (leading 1), natDegree
n, and `g.map (toZModPow N) = f.toPoly` coefficientwise (`PadicInt.toZModPow`
of a nat-cast is the ZMod cast of `.val`, then `ZMod.natCast_val`/
`ZMod.cast_id'` — routine cast plumbing).  Holds at ALL N including N = 0
(the map condition is automatic in the trivial ring ZMod 1). -/

/-- IB-E8 (†11d) — the explicit monic lift of a box class:
    Xⁿ + Σ_i C ((f i).val) Xⁱ over ℤ_p. -/
noncomputable def boxLift {n N : ℕ} (f : Box p n N) : Polynomial ℤ_[p] :=
  X ^ n + ∑ i : Fin n, C (((f i).val : ℤ_[p])) * X ^ (i : ℕ)

/-- Proof-internal helper (IB-E8, NOT a fenced statement): the lower-order sum
    of `boxLift` has degree < n (each summand degree ≤ i < n; empty at n = 0,
    where ⊥ < 0). -/
theorem boxLift_sum_degree_lt {n N : ℕ} (f : Box p n N) :
    (∑ i : Fin n, C (((f i).val : ℤ_[p])) * X ^ (i : ℕ)).degree
      < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro i _
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
    (by exact_mod_cast i.isLt)

/-- IB-E8 piece — the lift is monic (leading coefficient 1 in degree n; at
    n = 0 it is the monic constant 1). -/
theorem boxLift_monic {n N : ℕ} (f : Box p n N) : (boxLift f).Monic := by
  unfold boxLift
  exact Polynomial.monic_X_pow_add (boxLift_sum_degree_lt f)

/-- IB-E8 piece — the lift has natDegree n (the sum's degrees are < n). -/
theorem boxLift_natDegree {n N : ℕ} (f : Box p n N) :
    (boxLift f).natDegree = n := by
  have hd : (boxLift f).degree = n := by
    unfold boxLift
    rw [Polynomial.degree_add_eq_left_of_degree_lt
      (by rw [Polynomial.degree_X_pow]; exact boxLift_sum_degree_lt f),
      Polynomial.degree_X_pow]
  exact Polynomial.natDegree_eq_of_degree_eq_some hd

/-- IB-E8 piece — the lift reduces to the box polynomial:
    `(boxLift f).map (toZModPow N) = f.toPoly` (coefficientwise cast plumbing;
    automatic at N = 0 in the trivial ring). -/
theorem boxLift_map {n N : ℕ} (f : Box p n N) :
    (boxLift f).map (PadicInt.toZModPow N) = f.toPoly := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  unfold boxLift Box.toPoly
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    map_natCast, ZMod.natCast_zmod_val]

/-- IB-E8 (†11d) — `lift_exists`, in the exact `ZpBridge.lift_exists` field
    shape (DefsLedger.lean:732): assembled from the three witness laws above
    (the wiring is real; only the pieces carry sorries — the IB-E0 precedent). -/
theorem bridge_lift_exists (n N : ℕ) (f : Box p n N) :
    ∃ g : Polynomial ℤ_[p], g.Monic ∧ g.natDegree = n ∧
      g.map (PadicInt.toZModPow N) = f.toPoly :=
  ⟨boxLift f, boxLift_monic f, boxLift_natDegree f, boxLift_map f⟩

/-! ## IB-E10 — the (†8u)-feeding uniqueness

Informal statement: two splitting types satisfying the ∀-lift reading predicate
`ZpReads n p bridgeZfType N f ·` at the same (N, f) are EQUAL.  Deps: IB-E11,
IB-E8.  Sketch (†8u): take THE ONE lift g from `bridge_lift_exists` (available
at every N including 0); `ZpReads` (the ∀-lift predicate, DefsLedger.lean:686 —
verified against source, post-Codex finding 6) evaluates both σ's on it:
σ.1 = bridgeZfType g = σ'.1, then `Subtype.ext` transports across
`SplittingType n`.  This is the uniqueness IB-D9b's `choose` consumes for
`lift_true` at ALL N. -/

/-- IB-E10 (†8u) — ZpReads-uniqueness at (N, f) through the one lift. -/
theorem zpReads_bridgeZfType_unique (n N : ℕ) (f : Box p n N)
    {σ σ' : SplittingType n}
    (hσ : ZpReads n p bridgeZfType N f σ)
    (hσ' : ZpReads n p bridgeZfType N f σ') :
    σ = σ' := by
  obtain ⟨g, hm, hd, hmap⟩ := bridge_lift_exists n N f
  exact Subtype.ext ((hσ g hm hd hmap).symm.trans (hσ' g hm hd hmap))

/-! ## IB-E4 — IP-1 (†11c)

Informal statement: for h monic over ℤ_p with ℚ_p-irreducible image,
`AdjoinRoot h` is a local ring — stated VERBATIM as IB-E12's named Prop `IP1 p`
(same-sentence discipline; resolution 6).  Deps: IB-E3, IB-E12 (gate — the
near-miss `¬IsLocalRing (AdjoinRoot (X² − 1))` at odd p shows irreducibility is
load-bearing; no countermodel to IP-1 itself expected, memo (c) there).
Sketch (†11c): `AdjoinRoot h = ℤ_p[X]/(h)` is a finite ℤ_p-algebra and a
DOMAIN (h prime in the UFD ℤ_p[X] by Gauss/IB-E3); ℤ_p is complete local hence
HENSELIAN (`HenselianLocalRing` — E4a probes the pinned instance; else via
`IsAdicComplete`); a finite algebra over a henselian local ring is a product of
local rings (E4b1), and a domain has no nontrivial idempotents, so exactly one
factor survives (E4b2).  Fallback (own re-scope event, NOT inline): nonunits
closed under addition via the norm/integrality argument.  This discharges the
`ZpBridge` docstring's residue item (ii) (DefsLedger.lean:702–706). -/

/-! ### IB-E4 proof-internal infrastructure (the pre-approved E4a/E4b1 splits)

The four helpers below are proof-internal (NOT fenced blueprint statements).
E4a (henselian wiring): `ℤ_p` is `maximalIdeal`-adically complete (pinned
Mathlib instance, PadicIntegers.lean:532); completeness transfers to the
finite free module `AdjoinRoot h` through the `powerBasis'` coordinates
(`isAdicComplete_of_linearEquiv` ∘ `isAdicComplete_pi_of_fintype`), and
`IsAdicComplete.map_algebraMap_iff` upgrades it to ring-level completeness at
the extended ideal J — so the Mathlib instance `IsAdicComplete.henselianRing`
fires: `HenselianRing (AdjoinRoot h) J` (simple roots over A/J lift; the E4a
probe outcome is that the pinned Mathlib has NO finite-algebra-over-henselian
product decomposition, so E4b1/E4b2 run through idempotents instead).
E4b1 (idempotent factory): a commutative Artinian ring with two distinct
maximal ideals has a nontrivial idempotent
(`IsArtinianRing.quotNilradicalEquivPi` CRT + nil-kernel idempotent lifting
`exists_isIdempotentElem_eq_of_ker_isNilpotent`).  E4b2 (domain collapse) is
inlined in `ip1_holds`: Newton/Hensel lifts the residue idempotent along
X² − X (derivative 2e−1 squares to 1 mod J), and a domain has no nontrivial
idempotents — so two distinct maximal ideals of `AdjoinRoot h` are absurd. -/

/-- Proof-internal (IB-E4a, NOT a fenced statement): `IsAdicComplete`
    transfers along a linear equivalence. -/
theorem isAdicComplete_of_linearEquiv {R M N : Type*} [CommRing R] {I : Ideal R}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  have hmem : ∀ (n : ℕ) (y : N), y ∈ (I ^ n • ⊤ : Submodule R N) ↔
      e.symm y ∈ (I ^ n • ⊤ : Submodule R M) := by
    intro n y
    have hmap : (I ^ n • (⊤ : Submodule R M)).map (e : M →ₗ[R] N)
        = (I ^ n • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    rw [← hmap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hx
      exact ⟨e.symm y, hx, by simp⟩
  haveI hH : IsHausdorff I N := by
    constructor
    intro x hx
    have h0 : e.symm x = 0 := by
      refine IsHausdorff.haus (inferInstance : IsHausdorff I M) (e.symm x) fun n => ?_
      rw [SModEq.sub_mem, sub_zero]
      refine (hmem n x).mp ?_
      have hx' := SModEq.sub_mem.mp (hx n)
      rwa [sub_zero] at hx'
    have := congrArg e h0
    simpa using this
  haveI hP : IsPrecomplete I N := by
    constructor
    intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I M)
      (f := fun n => e.symm (f n)) (fun {m n} hmn => by
        rw [SModEq.sub_mem, ← map_sub]
        exact (hmem m _).mp (SModEq.sub_mem.mp (hf hmn)))
    refine ⟨e L, fun n => ?_⟩
    rw [SModEq.sub_mem, hmem n]
    have := SModEq.sub_mem.mp (hL n)
    simpa [map_sub] using this
  exact IsAdicComplete.mk

set_option linter.unusedFintypeInType false in
/-- Proof-internal (IB-E4a, NOT a fenced statement): `IsAdicComplete` passes to
    finite powers — the shape `Basis.equivFun` reduces a finite free module to.
    (`Fintype ι` is used through `Finset.univ` in the single-decomposition.) -/
theorem isAdicComplete_pi_of_fintype {R M : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] : IsAdicComplete I (ι → M) := by
  classical
  have hmem : ∀ (n : ℕ) (x : ι → M), x ∈ (I ^ n • ⊤ : Submodule R (ι → M)) ↔
      ∀ i, x i ∈ (I ^ n • ⊤ : Submodule R M) := by
    intro n x
    constructor
    · intro hx i
      have hle : (I ^ n • (⊤ : Submodule R (ι → M))).map
          (LinearMap.proj i) ≤ (I ^ n • ⊤ : Submodule R M) := by
        rw [Submodule.map_smul'']
        exact Submodule.smul_mono le_rfl le_top
      exact hle (Submodule.mem_map_of_mem hx)
    · intro hx
      have hle : ∀ i : ι, (I ^ n • (⊤ : Submodule R M)).map
          (LinearMap.single R (fun _ : ι => M) i)
          ≤ (I ^ n • ⊤ : Submodule R (ι → M)) := by
        intro i
        rw [Submodule.map_smul'']
        exact Submodule.smul_mono le_rfl le_top
      have hx' : x = ∑ i : ι, Pi.single i (x i) := (Finset.univ_sum_single x).symm
      rw [hx']
      exact Submodule.sum_mem _ fun i _ => hle i (Submodule.mem_map_of_mem (hx i))
  haveI hH : IsHausdorff I (ι → M) := by
    constructor
    intro x hx
    funext i
    change x i = 0
    refine IsHausdorff.haus (inferInstance : IsHausdorff I M) (x i) fun n => ?_
    rw [SModEq.sub_mem, sub_zero]
    have hxn := SModEq.sub_mem.mp (hx n)
    rw [sub_zero] at hxn
    exact (hmem n x).mp hxn i
  haveI hP : IsPrecomplete I (ι → M) := by
    constructor
    intro f hf
    have hcomp : ∀ i : ι, ∃ L : M, ∀ n : ℕ,
        f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] := by
      intro i
      refine IsPrecomplete.prec (inferInstance : IsPrecomplete I M)
        (f := fun n => f n i) (fun {m n} hmn => ?_)
      rw [SModEq.sub_mem]
      have := (hmem m _).mp (SModEq.sub_mem.mp (hf hmn)) i
      simpa using this
    choose L hL using hcomp
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, hmem n]
    intro i
    have := SModEq.sub_mem.mp (hL i n)
    simpa using this
  exact IsAdicComplete.mk

/-- Proof-internal (IB-E4a, NOT a fenced statement): the monic order
    `AdjoinRoot h` is adically complete at the extended maximal ideal —
    completeness rides the `powerBasis'` coordinates, then
    `IsAdicComplete.map_algebraMap_iff` moves it to the ring level. -/
theorem adjoinRoot_isAdicComplete (h : Polynomial ℤ_[p]) (hm : h.Monic) :
    IsAdicComplete ((IsLocalRing.maximalIdeal ℤ_[p]).map
      (algebraMap ℤ_[p] (AdjoinRoot h))) (AdjoinRoot h) := by
  haveI h1 : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p])
      (Fin (AdjoinRoot.powerBasis' hm).dim → ℤ_[p]) :=
    isAdicComplete_pi_of_fintype _
  haveI h2 : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) (AdjoinRoot h) :=
    isAdicComplete_of_linearEquiv ((AdjoinRoot.powerBasis' hm).basis.equivFun).symm
  exact (IsAdicComplete.map_algebraMap_iff
    (IsLocalRing.maximalIdeal ℤ_[p]) (AdjoinRoot h)).mpr h2

/-- Proof-internal (IB-E4b1, NOT a fenced statement): a commutative Artinian
    ring with two distinct maximal ideals has a nontrivial idempotent —
    `IsArtinianRing.quotNilradicalEquivPi` (CRT across the nilradical)
    supplies it on the product side, and idempotents lift along the nil
    kernel (`exists_isIdempotentElem_eq_of_ker_isNilpotent`). -/
theorem exists_nontrivial_idempotent_of_two_maximal {B : Type*} [CommRing B]
    [IsArtinianRing B] {N₁ N₂ : Ideal B} (hN₁ : N₁.IsMaximal) (hN₂ : N₂.IsMaximal)
    (hne : N₁ ≠ N₂) : ∃ e : B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  set I₁ : MaximalSpectrum B := ⟨N₁, hN₁⟩ with hI₁def
  set I₂ : MaximalSpectrum B := ⟨N₂, hN₂⟩ with hI₂def
  have hI : I₂ ≠ I₁ := by
    intro hh
    exact hne (congrArg MaximalSpectrum.asIdeal hh).symm
  set ψ := IsArtinianRing.quotNilradicalEquivPi B with hψdef
  set x : ∀ J : MaximalSpectrum B, B ⧸ J.asIdeal := Pi.single I₁ 1 with hxdef
  have hxid : x * x = x := by
    funext j
    by_cases hj : j = I₁
    · subst hj
      simp [hxdef]
    · simp [hxdef, Pi.single_eq_of_ne hj]
  have he₁ : IsIdempotentElem (ψ.symm x) := by
    rw [IsIdempotentElem, ← map_mul, hxid]
  obtain ⟨e, heid, heq⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (f := (Ideal.Quotient.mk (nilradical B)))
    (fun y hy => by
      rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hy
      exact mem_nilradical.mp hy)
    (ψ.symm x)
    (RingHom.mem_range.mpr (Ideal.Quotient.mk_surjective (ψ.symm x)))
    he₁
  refine ⟨e, heid, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at heq
    have hx0 : x = 0 := by
      have hψ := congrArg (fun t => ψ t) heq
      simpa using hψ.symm
    have h10 := congrFun hx0 I₁
    rw [hxdef] at h10
    simp only [Pi.single_eq_same, Pi.zero_apply] at h10
    exact one_ne_zero h10
  · intro h1
    rw [h1, map_one] at heq
    have hx1 : x = 1 := by
      have hψ := congrArg (fun t => ψ t) heq
      simpa using hψ.symm
    have h01 := congrFun hx1 I₂
    rw [hxdef] at h01
    simp only [Pi.single_eq_of_ne hI, Pi.one_apply] at h01
    exact zero_ne_one h01

/-- IB-E4 (†11c) — IP-1 holds: `IP1 p` (BridgeE12_ip1Gate.lean's sentence). -/
theorem ip1_holds : IP1 p := by
  intro h hm hirr
  classical
  -- STEP 0 (domain): h is prime in the UFD ℤ_p[X] (reverse Gauss transfer),
  -- so AdjoinRoot h = ℤ_p[X]/(h) is a domain — E12 memo (c)(iii).
  have hirrZ : Irreducible h := by
    rw [padicCoe_eq_algebraMap] at hirr
    exact (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mpr hirr
  have hprime : Prime h := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirrZ
  haveI hspan : (Ideal.span {h} : Ideal (Polynomial ℤ_[p])).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  haveI hdom : IsDomain (AdjoinRoot h) :=
    Ideal.Quotient.isDomain (Ideal.span {h} : Ideal (Polynomial ℤ_[p]))
  -- STEP 1 (E4a): adic completeness at the extended ideal J, hence henselian.
  set J : Ideal (AdjoinRoot h) :=
    (IsLocalRing.maximalIdeal ℤ_[p]).map (AdjoinRoot.of h) with hJdef
  haveI hJcomplete : IsAdicComplete J (AdjoinRoot h) := by
    rw [hJdef, ← AdjoinRoot.algebraMap_eq]
    exact adjoinRoot_isAdicComplete h hm
  haveI hHens : HenselianRing (AdjoinRoot h) J := inferInstance
  -- STEP 2: the residue presentation φ : AdjoinRoot h →+* AdjoinRoot h̄ over
  -- the residue field (Mathlib's `quotAdjoinRootEquivQuotPolynomialQuot`).
  set hbar : Polynomial (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
    h.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])) with hbardef
  set ε : (AdjoinRoot h ⧸ J) ≃+* AdjoinRoot hbar :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
      (IsLocalRing.maximalIdeal ℤ_[p]) h with hεdef
  set φ : AdjoinRoot h →+* AdjoinRoot hbar :=
    ε.toRingHom.comp (Ideal.Quotient.mk J) with hφdef
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, hz⟩ := ε.surjective y
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (I := J) z
    exact ⟨w, by simp [hφdef, hw, hz]⟩
  have hker : ∀ a : AdjoinRoot h, φ a = 0 ↔ a ∈ J := by
    intro a
    constructor
    · intro ha
      have h0 : Ideal.Quotient.mk J a = 0 := by
        apply ε.injective
        rw [map_zero]
        simpa [hφdef] using ha
      rwa [Ideal.Quotient.eq_zero_iff_mem] at h0
    · intro ha
      have h0 : Ideal.Quotient.mk J a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
      simp [hφdef, h0]
  -- STEP 3 (E4a): the residue ring AdjoinRoot h̄ is Artinian (finite
  -- dimensional over the residue field through the power basis).
  have hbarM : hbar.Monic := hm.map _
  -- the residue field is finite (≅ ZMod p), so the monic power basis makes
  -- AdjoinRoot h̄ a FINITE ring, hence Artinian — no quotient-field instance
  -- needed (avoids the `Ideal.Quotient.field` non-instance diamond).
  haveI hkFin : Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
    Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  haveI hBFin : Finite (AdjoinRoot hbar) :=
    Finite.of_equiv _ ((AdjoinRoot.powerBasis' hbarM).basis.equivFun).symm.toEquiv
  haveI hArtB : IsArtinianRing (AdjoinRoot hbar) := isArtinian_of_finite
  -- STEP 4: locality via unique maximal ideal; J sits below every maximal
  -- ideal (completeness ⇒ J ≤ Jacobson radical).
  have hJle : ∀ M : Ideal (AdjoinRoot h), M.IsMaximal → J ≤ M := by
    intro M hM
    refine le_trans (IsAdicComplete.le_jacobson_bot J) ?_
    exact sInf_le ⟨bot_le, hM⟩
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (AdjoinRoot h)
  refine ⟨M₀, hM₀, fun M₁ hM₁ => ?_⟩
  by_contra hMne
  -- Two distinct maximal ideals push to two distinct maximal ideals of the
  -- Artinian residue ring (φ surjective, ker φ = J below both).
  have hpush : ∀ M : Ideal (AdjoinRoot h), M.IsMaximal →
      (Ideal.map φ M).IsMaximal ∧ Ideal.comap φ (Ideal.map φ M) = M := by
    intro M hM
    have hcm : Ideal.comap φ (Ideal.map φ M) = M := by
      rw [Ideal.comap_map_of_surjective φ hφsurj]
      refine sup_eq_left.mpr ?_
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_bot] at ha
      exact hJle M hM ((hker a).mp ha)
    refine ⟨?_, hcm⟩
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective φ hφsurj hM with htop | hmax
    · exfalso
      apply hM.ne_top
      rw [← hcm, htop, Ideal.comap_top]
    · exact hmax
  obtain ⟨hN₁max, hN₁c⟩ := hpush M₁ hM₁
  obtain ⟨hN₀max, hN₀c⟩ := hpush M₀ hM₀
  have hNne : Ideal.map φ M₁ ≠ Ideal.map φ M₀ := by
    intro hh
    exact hMne (by rw [← hN₁c, hh, hN₀c])
  -- E4b1: a nontrivial idempotent downstairs …
  obtain ⟨eB, heBid, heB0, heB1⟩ :=
    exists_nontrivial_idempotent_of_two_maximal hN₁max hN₀max hNne
  -- … E4b2: Hensel-lift it along X² − X (derivative 2e−1 is a unit mod J) and
  -- collapse in the domain.
  obtain ⟨a₀, ha₀⟩ := hφsurj eB
  have hevJ : a₀ ^ 2 - a₀ ∈ J := by
    refine (hker _).mp ?_
    rw [map_sub, map_pow, ha₀, sq, heBid.eq, sub_self]
  have hev : Polynomial.eval a₀ ((X : Polynomial (AdjoinRoot h)) ^ 2 - X) ∈ J := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    exact hevJ
  have hder : IsUnit (Ideal.Quotient.mk J
      (Polynomial.eval a₀ (Polynomial.derivative
        ((X : Polynomial (AdjoinRoot h)) ^ 2 - X)))) := by
    have hd : Polynomial.eval a₀ (Polynomial.derivative
        ((X : Polynomial (AdjoinRoot h)) ^ 2 - X)) = 2 * a₀ - 1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
      simp only [Nat.cast_ofNat, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      norm_num
    rw [hd]
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (2 * a₀ - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    have hcalc : (2 * a₀ - 1) * (2 * a₀ - 1) - 1 = 4 * (a₀ ^ 2 - a₀) := by ring
    rw [hcalc]
    exact Ideal.mul_mem_left _ _ hevJ
  have hmonic : ((X : Polynomial (AdjoinRoot h)) ^ 2 - X).Monic := by
    refine Polynomial.monic_X_pow_sub ?_
    rw [Polynomial.degree_X]
    exact_mod_cast one_lt_two
  obtain ⟨a, haroot, hamod⟩ := hHens.is_henselian
    ((X : Polynomial (AdjoinRoot h)) ^ 2 - X) hmonic a₀ hev hder
  have hroot : a ^ 2 - a = 0 := by simpa using haroot
  have hphia : φ a = eB := by
    have h0 : φ (a - a₀) = 0 := (hker _).mpr hamod
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, ha₀]
  have hfact : a * (a - 1) = 0 := by
    calc a * (a - 1) = a ^ 2 - a := by ring
    _ = 0 := hroot
  rcases mul_eq_zero.mp hfact with h0 | h1
  · exact heB0 (by rw [← hphia, h0, map_zero])
  · exact heB1 (by rw [← hphia, show a = 1 by rwa [sub_eq_zero] at h1, map_one])

/-- IB-E4 consumption wrapper (real wiring, no sorry of its own): the unfolded
    IP-1 shape the `MovesT.ramIdx`/`resDeg` junk-dispatch consumers read —
    `IsLocalRing (AdjoinRoot h)` for monic h with ℚ_p-irreducible image. -/
theorem isLocalRing_adjoinRoot (h : Polynomial ℤ_[p]) (hm : h.Monic)
    (hirr : Irreducible (h.map PadicInt.Coe.ringHom)) :
    IsLocalRing (AdjoinRoot h) :=
  ip1_holds h hm hirr

end LeanUrat.MovesU
