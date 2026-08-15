/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The fundamental identity in the local case — QUARRY BACKPORT

**Provenance (quarry charter).** Backported from
`vendor/FLT` (ImperialCollegeLondon/FLT), commit `58f25c6f305e1cf794c7666f89adcd0375bcc047`,
file `FLT/Mathlib/RingTheory/RamificationInertia/Basic.lean:28`, Apache-2.0 (same licence as
mathlib and as this repo), **verified 2026-08-15**. Shortlist item **#1** of
`docs/VENDOR_QUARRY_MAP_2026-08-15.md` §5.

**Dedup-audit statement.** The declaration
`Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`
is a NEW declaration in this tree. It is a **near-verbatim move** with exactly three adaptations,
each forced by the two-month mathlib drift between FLT's pin (`v4.34.0-rc1`) and ours
(`v4.31.0`, mathlib `fabf563a`):

1. **Module-system header surgery.** FLT's file opens with `module` / `public import` /
   `@[expose] public section` (mathlib's post-4.32 module system). Our pin predates it, so the
   header is plain `import`s and there is no `public section` / trailing `end`.
2. **`ramificationIdx'` / `inertiaDeg'` instead of `ramificationIdx` / `inertiaDeg`.** At our rev
   the *rank-form* fundamental identity `Ideal.sum_ramification_inertia_eq_finrank`
   (`Mathlib/RingTheory/RamificationInertia/Basic.lean:72`) is stated in the **primed**
   generation — `q.ramificationIdx' R`, `q.inertiaDeg' R` — which upstream renamed to the
   unprimed names when it deprecated the old `(p, q)`-keyed pair in Aug 2026. FLT's source text
   is against the post-rename tree. So `ramificationIdx' R` here IS FLT's `ramificationIdx R`,
   same definition, older name. (`Ideal.ramificationIdx_eq_ramificationIdx'` and
   `Ideal.inertiaDeg_eq_inertiaDeg'` reconcile the primed names with the old `(p, q)`-keyed
   `Ideal.ramificationIdx p q` / `p.inertiaDeg q` used by `Mathlib/NumberTheory/`.)
3. **Two instances supplied by hand.** Our `sum_ramification_inertia_eq_finrank` carries
   `[Module.Flat R S]` and `[Fintype (p.primesOver S)]` as hypotheses; FLT's newer copy does not.
   Both are discharged here (flatness from `IsDedekindDomain` + torsion-freeness, finiteness of
   the fibre from `IsLocalRing.primesOver_eq`), which is why the proof is longer than FLT's.

**Why we took it** (survey §5 row 1): `e * f = [S : R]` in **rank form** `Module.finrank R S` —
the form the tower chapters want — and the future-proof replacement for
`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
(`Mathlib/NumberTheory/RamificationInertia/Basic.lean:650`), which is live at our rev only
because our rev predates its Aug-2026 deprecation, and which is stated in fraction-field form
`Module.finrank K L` instead.

The mathematical content, in FLT's own words: `Ideal.sum_ramification_inertia_eq_finrank` says
that if `S` is a finite flat algebra over a domain `R` and `p` is a prime of `R`, then
`∑ q, e q * f q = finrank R S`, the sum being over the primes `q` of `S` above `p`. If `S` is
local then there is exactly one such `q`, namely the maximal ideal of `S`, and the identity
becomes `e * f = finrank R S`.
-/

namespace Ideal

/-- The **fundamental identity** `e * f = [S : R]` for a local ring `S`, finite over a Dedekind
domain `R`, and `p` a nonzero maximal ideal of `R`.

(Backport; see the file header for provenance and the three adaptations. FLT's in-source comment,
kept: `ramificationIdx_mul_inertiaDeg_of_isLocalRing` is deprecated in Aug 2026 so we use a
longer name.) -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [IsLocalRing S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (IsLocalRing.maximalIdeal S).ramificationIdx' R *
      (IsLocalRing.maximalIdeal S).inertiaDeg' R = Module.finrank R S := by
  have : IsDomain R := .of_faithfulSMul R S
  -- adaptation (3): flatness of `S` over the Dedekind domain `R`, from torsion-freeness
  have : Module.IsTorsionFree R S := Module.IsTorsionFree.of_smul_eq_zero fun r m h ↦ by
    rwa [Algebra.smul_def, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at h
  have : Module.Flat R S := inferInstance
  -- the fibre over `p` is the single point `𝔪_S`
  have hsingle : Ideal.primesOver p S = {IsLocalRing.maximalIdeal S} :=
    IsLocalRing.primesOver_eq S hp0
  have hmax : IsLocalRing.maximalIdeal S ∈ p.primesOver S := by rw [hsingle]; rfl
  have : (IsLocalRing.maximalIdeal S).LiesOver p := hmax.2
  have heq (q : p.primesOver S) : q.1 = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (q.2.1.isMaximal (ne_bot_of_mem_primesOver hp0 q.2))
  have : Subsingleton (p.primesOver S) := ⟨fun q q' ↦ Subtype.ext ((heq q).trans (heq q').symm)⟩
  -- adaptation (3): our `sum_ramification_inertia_eq_finrank` wants a `Fintype` on the fibre
  have : Finite (p.primesOver S) := by rw [hsingle]; infer_instance
  have : Fintype (p.primesOver S) := Fintype.ofFinite _
  rw [← sum_ramification_inertia_eq_finrank p S,
    Fintype.sum_subsingleton _ (⟨IsLocalRing.maximalIdeal S, hmax⟩ : p.primesOver S)]

end Ideal

/-! ## Axiom footprint -/

#print axioms Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing
