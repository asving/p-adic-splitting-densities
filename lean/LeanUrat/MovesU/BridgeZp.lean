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
  sorry

/-- IB-E1a (†11a) — each extracted factor is monic.  Deps: `monicFactors`.
    Sketch: each UFD factor of monic g has unit leading coefficient
    (leadingCoeff multiplicativity in the domain ℤ_p[X]); the extraction scales
    by that unit's inverse. -/
theorem monicFactors_monic (g : Polynomial ℤ_[p]) (hg : g.Monic) :
    ∀ h ∈ monicFactors g, h.Monic :=
  sorry

/-- IB-E1b (†11a) — THE PRODUCT LAW: the monic-scaled factors multiply back to
    g.  Deps: `monicFactors`.  Sketch: `UniqueFactorizationMonoid.factors_prod`
    gives (factors g).prod = g up to a unit; after the monic rescale the
    residual unit is a monic unit of ℤ_p[X], i.e. a unit CONSTANT with leading
    coefficient 1, hence 1 (compare leading coefficients — the telescoping of
    †11a). -/
theorem monicFactors_prod (g : Polynomial ℤ_[p]) (hg : g.Monic) :
    (monicFactors g).prod = g :=
  sorry

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
    ∀ h ∈ monicFactors g, Irreducible h :=
  sorry

/-- IB-E2 — each monic factor has positive degree (a monic degree-0 polynomial
    is 1, a unit, contradicting irreducibility). -/
theorem monicFactors_natDegree_pos (g : Polynomial ℤ_[p]) (hg : g.Monic) :
    ∀ h ∈ monicFactors g, 0 < h.natDegree :=
  sorry

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
    Irreducible (h.map PadicInt.Coe.ringHom) :=
  sorry

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

/-- IB-E8 piece — the lift is monic (leading coefficient 1 in degree n; at
    n = 0 it is the monic constant 1). -/
theorem boxLift_monic {n N : ℕ} (f : Box p n N) : (boxLift f).Monic :=
  sorry

/-- IB-E8 piece — the lift has natDegree n (the sum's degrees are < n). -/
theorem boxLift_natDegree {n N : ℕ} (f : Box p n N) :
    (boxLift f).natDegree = n :=
  sorry

/-- IB-E8 piece — the lift reduces to the box polynomial:
    `(boxLift f).map (toZModPow N) = f.toPoly` (coefficientwise cast plumbing;
    automatic at N = 0 in the trivial ring). -/
theorem boxLift_map {n N : ℕ} (f : Box p n N) :
    (boxLift f).map (PadicInt.toZModPow N) = f.toPoly :=
  sorry

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
    σ = σ' :=
  sorry

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

/-- IB-E4 (†11c) — IP-1 holds: `IP1 p` (BridgeE12_ip1Gate.lean's sentence). -/
theorem ip1_holds : IP1 p :=
  sorry

/-- IB-E4 consumption wrapper (real wiring, no sorry of its own): the unfolded
    IP-1 shape the `MovesT.ramIdx`/`resDeg` junk-dispatch consumers read —
    `IsLocalRing (AdjoinRoot h)` for monic h with ℚ_p-irreducible image. -/
theorem isLocalRing_adjoinRoot (h : Polynomial ℤ_[p]) (hm : h.Monic)
    (hirr : Irreducible (h.map PadicInt.Coe.ringHom)) :
    IsLocalRing (AdjoinRoot h) :=
  ip1_holds h hm hirr

end LeanUrat.MovesU
