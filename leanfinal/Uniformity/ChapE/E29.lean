/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E10
import Uniformity.ChapE.E27
import Uniformity.ChapE.E28

/-!
# Uniformity.ChapE.E29 — the twisted slot specification, RE-SIGNED at AMENDMENT A-E.4

**Chapter E, NODE E.29** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §5, as repaired by
A-E.1/E-D4 and **re-signed by A-E.4, 2026-08-16**), ENV-E2 + ENV-E3 + `open scoped Classical`
(declaration-scoped, exactly as the amendment prescribes). R1-b's twisted slot lemma; `(SLOT₂)`
is its `ϑ ≡ 1` instance.

**STATUS: LANDED at the A-E.4 form.** The COMMITTED signature was refuted here, machine-checked
(`twisted_slot_spec_false`), and the refuted claim never entered the environment as a fact (the
H.71 / E.36 discipline). AMENDMENT A-E.4 adjudicated the re-sign in favour of **repair candidate
1** — `hatt` records the ATTAINED VALUE, the class location is derived — and the signed name
`twisted_slot_spec` now lands at the end of this file, over that candidate, with the signed
conclusion byte-for-byte and every other binder byte-unchanged. Also landing: the counterexample
(kept as provenance), the class-location lemma the node actually needs, and both repair
candidates under their non-signed names.

## The COMMITTED signed statement (REFUTED; preserved verbatim for the record)

```
theorem twisted_slot_spec {O} [CommRing O] {K K'} [Field K] [Field K'] [Algebra K K']
    (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K') (hint : IsIntegral K η)
    (hg : R.g = Module.finrank K K') (c : ℕ → Polynomial O)
    (hdeg : ∀ s, (c s).natDegree < C.D) (hsupp : ∀ s, R.slotCount ≤ s → c s = 0)
    (hocc : ∃ s < R.slotCount, c s ≠ 0) (ϑ : Fin R.g → K) (hϑ : ∀ t, ϑ t ≠ 0)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hmin : ∀ s < R.slotCount, c s ≠ 0 → ∀ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) →
      (k : ℤ) ≤ R.ℓ * v + s * R.u)
    (hatt : ∃ s < R.slotCount, c s ≠ 0 ∧
      C.hgt (c s) = (((m₀ : ℤ) - (((s - s₀) / R.ℓ : ℕ) : ℤ) * (R.u : ℤ)) : WithTop ℤ)) :
    seamSumT (fun t : Fin R.g =>
        if s₀ + R.ℓ * (t : ℕ) < R.slotCount ∧ c (s₀ + R.ℓ * (t : ℕ)) ≠ 0
          then C.dig (c (s₀ + R.ℓ * (t : ℕ))) else 0) ϑ η ≠ 0
```

`twisted_slot_spec_false` below is its negation (binders at `Type` rather than `Type*`, which
only makes the refutation stronger: the universe-polymorphic form instantiates at `Type`), proved
outright.

## The counterexample: an attainer OUTSIDE the class of `s₀`

Everything happens at the smallest legal frame. Take `O = K = K' = ℚ`, `η = 0` (so
`Module.finrank ℚ ℚ = 1 = (minpoly ℚ 0).natDegree`, and `η` is integral), and

* `C = oneHeightCarrier` — the `D = 1` slot carrier over `ℚ`: `hgt A = ⊤` for `A = 0` and `1`
  otherwise, `dig A = A.coeff 0`, `Full k ↔ k = 1`. **Every** `SlotCarrier` law holds, including
  the two ultrametric laws, digit additivity at a shared height, and `(LIFT)` — the lift is
  genuinely realised at the carrier's one full height (`A := C c`), so this is not a
  vacuous-`Full` carrier;
* `R = rungTwoOne = (ℓ, g, u, T) = (2, 1, 1, 0)` — legal (`1 ≤ ℓ`, `1 ≤ g`, `Coprime u ℓ`,
  `ℓ*T < u`), with `slotCount = ℓg = 2`: slots `{0, 1}`, and the class of `s₀ = 0` is `{0}`;
* `c = outOfClassSlots`, the family occupying slot `1` ONLY (`c 1 = 1`, `c s = 0` otherwise);
* `ϑ ≡ 1`, `s₀ = 0`, `m₀ = 1`, `k = ℓm₀ + s₀u = 2`.

Every signed hypothesis holds:

* `hdeg`, `hsupp`, `hocc` — immediate (`natDegree = 0 < 1 = D`; slot `1 < 2` is occupied);
* `hs₀ : 0 < 2` and `hk : 2*1 + 0*1 = 2`;
* `hmin` — the only occupied slot is `s = 1`, with height `v = 1`, and
  `k = 2 ≤ ℓv + su = 2*1 + 1*1 = 3`. So `k` is a genuine lower bound for the slot values;
* `hatt` — at `s = 1`: `(s − s₀)/ℓ = 1/2 = 0` in `ℕ`, so the required height is
  `m₀ − 0*u = 1`, and `hgt (c 1) = 1`. **The hypothesis is satisfied by a slot that does not lie
  in the class of `s₀`.**

The conclusion FAILS: the guarded coefficient vector is indexed by `t : Fin g = Fin 1`, i.e. by
the single in-class slot `s₀ + ℓ·0 = 0`, where `c 0 = 0`; the guard is false, `γ ≡ 0`, and
`seamSumT γ ϑ η = 0`.

## Where the signed statement breaks

`hatt` is meant to say *"the minimum `k` is ATTAINED"*, and the node's PROOF step 1 reads it that
way ("the `hmin`/`hatt` hypotheses are the cleared form of `k` is the min, attained"). As spelled,
it does not say that. The truncating `ℕ`-division `((s − s₀) / R.ℓ : ℕ)` silently rounds an
out-of-class index into the class ladder: for `s = s₀ + ℓt + r` with `0 < r < ℓ` the hypothesis
asks for height `m₀ − tu`, whose slot value is `ℓ(m₀ − tu) + su = k + ru > k` — consistent with
`hmin`, and no in-class slot need be occupied at all. The class location that STATEMENT clause (i)
announces ("the minimum is attained in one class `s₀ + ℓ·{t < g}` (E.28)") is therefore a
*conclusion the hypotheses do not support*: E.28's separation argument needs the attained VALUE,
which the signed `hatt` never records.

This is a hypothesis-set defect, not a defect in R1-b's mathematics: `EFF.HE7.110` Step 2 fixes
`k` as the minimum *of the slot values* and then locates its attainers, and every attainer of the
minimum IS in the class of `s₀` (that is `attainer_in_class` below, proved). The gap is entirely
in the cleared transcription.

## What lands here

* `attainer_in_class` (chapter-internal helper, non-signed name) — E.28's separation content at
  `ℤ`-valued heights: if `ℓv + su = k = ℓm₀ + s₀u` with `s < slotCount` and `s₀ < ℓ`, then
  `s = s₀ + ℓt` for some `t < g`. Proof: `ℓ ∣ (s₀ − s)u` from the two value equations,
  `gcd(u, ℓ) = 1` (E.01's `hcop` field) strips the `u`, `s % ℓ = s₀` follows, and the quotient
  `t = s / ℓ` obeys `ℓt ≤ s < ℓg`. This is the ℤ-height twin of E.28's `rung_class_sep`, which is
  stated for `ℕ` heights and so cannot be applied directly here (carrier heights are
  `WithTop ℤ` by DECISION D-E1).
* `twisted_slot_spec_of_attain_value` — **repair candidate 1, ADOPTED by A-E.4**, the signed
  statement with the single change that `hatt` records the attained VALUE:
  `∃ s < slotCount, c s ≠ 0 ∧ ∃ v, hgt (c s) = v ∧ ℓv + su = k`. PROVED. This is the faithful
  reading of "the minimum is attained": the class location is then *derived*
  (`attainer_in_class`), exactly as STATEMENT clause (i) promises.
* `twisted_slot_spec` — **the SIGNED NAME**, at that re-signed type (A-E.4), over candidate 1.
* `twisted_slot_spec_of_attain_inClass` — **repair candidate 2, RECORDED AND NOT ADOPTED**
  (A-E.4), the minimal one: `hatt` names an occupied in-class slot directly
  (`∃ t : Fin g, s₀ + ℓt < slotCount ∧ c (s₀ + ℓt) ≠ 0`). PROVED. `k`, `m₀`, `hk`, `hmin` are
  then not needed at all, so this candidate drops them. It is not the source's shape: it
  ASSUMES what `EFF.HE7.11` Step 2 DERIVES ("The minimum … is therefore attained inside a single
  class s₀ + ℓ·{0,…,d_r−1}"). Kept as the interface for a consumer that has already located the
  class (e.g. through E.28).

Both candidates end in the signed conclusion, byte-for-byte, under the `open scoped Classical`
the amendment mandates; both fire E.27 (`seamSumT_ne_zero`) on a `γ`-vector shown nonzero at one
index through E.10's `dig_ne_zero`.

**A reading worth recording:** candidate 1's proof never uses `hmin`. Minimality is what makes
`k` the next level's HEIGHT; the kill clause (`seamSumT ≠ 0`, "no cancellation") needs only that
some in-class slot attains. The signed binder is kept in candidate 1 for signature fidelity (with
the `unusedVariables` linter disabled at the declaration), because the node's contract is the
bundle, not the kill clause alone — and A-E.4 keeps it in the signed form for the same reason:
the source defines `k := min_{s<L}(ℓ·w(c_s) + s·u)`, of which `hmin` is the lower-bound half, so
dropping it would silently un-name `k`.

## What is still NOT here

The SIGNATURE NOTE's bundle (`TwistedSlotRead`: `k, s₀, γ, hclass, hattain, hkill`) is the
node's full contract; this file lands the kill clause and the class location, which are its
two mathematical halves. The evaluation reading (`dv₂(C(ξ)) = k` at points `ξ`) is carrier
content and is an instance obligation (C placeholder at E.23), per the node's own
**WHAT IS NOT HERE** field. The `g₂ = 1` disclosure rides E.27's TEETH note.

DEPENDS: E.10 (`SlotCarrier`, `dig_ne_zero`), E.26 (`seamSumT`), E.27 (`seamSumT_ne_zero`),
E.28 (the `ℕ`-height separation this file's `attainer_in_class` re-proves at `ℤ`) · mathlib
`Int.dvd_of_dvd_mul_left_of_gcd_one`, `Int.gcd_natCast_natCast`, `Int.modEq_iff_dvd`,
`Nat.div_add_mod`, `Nat.lt_of_mul_lt_mul_left`.

SOURCE: `EFF.HE7.110` (ANNEX-THEOREM R1-b, statement + Steps 1–3, incl. "At i = 1 every θ_t = 1 …
and the display is (SLOT₂) byte-for-byte", and "what the correction moves is the residue's
COORDINATES (γ_t ↦ γ_t·ϑ_t)"); `EFF.HE7.11` ((SLOT₂), the `ϑ ≡ 1` instance); `EFF.T2.06` (the
level-1 `(GAMMA)` instance).

TEETH: Q2 / HE7-SLOT2 (12,632 exactness identities, 0 violations) + `he7rannex_supp.py`
(level 3, 79/79) — **the numerics are untouched by this refutation and never contradicted it**:
those batteries sample slot families and read the minimum off the family, so their attainers are
in-class by construction; the defect lives in the hypothesis that was written to *stand in* for
attainment. The tooth's disposition "→ Lean theorem" is therefore MET by repair candidate 1 and
NOT met by the signed form.

ENVIRONMENT: ENV-E2 + ENV-E3 + `open scoped Classical` (A-E.1/E-D4).

## Status

Sorry-free. `twisted_slot_spec` (the signed name, A-E.4 form), `attainer_in_class`, both repair
candidates and every counterexample declaration are proved, Lean-core axioms only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

open Polynomial

/-! ## The counterexample -/

namespace E29Refutation

/-- The **one-full-height slot carrier** over `ℚ`: key degree `D = 1`, heights `{⊤, 1}`, digit =
constant coefficient, `Full k ↔ k = 1`. All of E.10's laws hold, and `(LIFT)` is realised (not
vacuous) at the single full height. -/
noncomputable def oneHeightCarrier : SlotCarrier ℚ ℚ where
  D := 1
  hD := Nat.one_pos
  eC := 1
  fC := 1
  hef := by norm_num
  heC := le_refl 1
  hfC := le_refl 1
  hgt := fun A => if A = 0 then (⊤ : WithTop ℤ) else ((1 : ℤ) : WithTop ℤ)
  dig := fun A => A.coeff 0
  hgt_zero := by simp
  dig_zero := by simp
  hgt_ne_top := by intro A hA _; simp [hA]
  dig_ne_zero := by
    intro A hA hdeg hc
    have h0 : A.natDegree = 0 := Nat.lt_one_iff.mp hdeg
    exact hA (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero])
  hgt_add_ge := by
    intro A B
    by_cases hA : A = 0
    · simp [hA]
    · by_cases hB : B = 0
      · simp [hB]
      · simp only [if_neg hA, if_neg hB, min_self]
        split <;> simp
  hgt_add_eq := by
    intro A B hne
    by_cases hA : A = 0
    · by_cases hB : B = 0
      · simp [hA, hB] at hne
      · simp [hA, hB]
    · by_cases hB : B = 0
      · simp [hA, hB]
      · simp [hA, hB] at hne
  dig_add := by
    intro A B k hA hB hne
    have hA0 : A ≠ 0 := by intro h; rw [h] at hA; simp at hA
    have hB0 : B ≠ 0 := by intro h; rw [h] at hB; simp at hB
    rw [if_neg hA0] at hA
    have hk1 : k = 1 := by exact_mod_cast hA.symm
    have hAB : A + B ≠ 0 := by
      intro h
      apply hne
      have hc : (A + B).coeff 0 = 0 := by rw [h]; simp
      simpa [Polynomial.coeff_add] using hc
    refine ⟨?_, ?_⟩
    · rw [if_neg hAB, hk1]
    · simp [Polynomial.coeff_add]
  Full := fun k => k = 1
  hlift := by
    intro k hk c hc
    refine ⟨Polynomial.C c, Polynomial.C_ne_zero.mpr hc, by simp, ?_, by simp⟩
    rw [if_neg (Polynomial.C_ne_zero.mpr hc), hk]

/-- The rung `(ℓ, g, u, T) = (2, 1, 1, 0)`: two slots, and the class of `s₀ = 0` is the
singleton `{0}`. -/
def rungTwoOne : RungDatum where
  ℓ := 2
  g := 1
  u := 1
  T := 0
  hℓ := by norm_num
  hg := le_refl 1
  hcop := Nat.coprime_one_left 2
  hnode := by norm_num

/-- The slot family occupying slot `1` only — the slot OUTSIDE the class of `s₀ = 0`. -/
noncomputable def outOfClassSlots : ℕ → Polynomial ℚ := fun s => if s = 1 then 1 else 0

@[simp] lemma rungTwoOne_ℓ : rungTwoOne.ℓ = 2 := rfl
@[simp] lemma rungTwoOne_g : rungTwoOne.g = 1 := rfl
@[simp] lemma rungTwoOne_u : rungTwoOne.u = 1 := rfl
@[simp] lemma rungTwoOne_slotCount : rungTwoOne.slotCount = 2 := rfl
@[simp] lemma oneHeightCarrier_D : oneHeightCarrier.D = 1 := rfl

@[simp] lemma oneHeightCarrier_hgt (A : Polynomial ℚ) :
    oneHeightCarrier.hgt A = if A = 0 then (⊤ : WithTop ℤ) else ((1 : ℤ) : WithTop ℤ) := rfl

@[simp] lemma oneHeightCarrier_dig (A : Polynomial ℚ) :
    oneHeightCarrier.dig A = A.coeff 0 := rfl

@[simp] lemma outOfClassSlots_zero : outOfClassSlots 0 = 0 := rfl
@[simp] lemma outOfClassSlots_one : outOfClassSlots 1 = 1 := rfl

lemma outOfClassSlots_eq_zero_of_ne_one {s : ℕ} (hs : s ≠ 1) : outOfClassSlots s = 0 := if_neg hs

end E29Refutation

open scoped Classical in
/-- **NODE E.29's signed statement is FALSE.** The refutation is stated at `Type` (rather than
the signed `Type*`), which is the stronger claim: the universe-polymorphic form instantiates
here. The witness is the frame `(O, K, K') = (ℚ, ℚ, ℚ)`, `η = 0`, `C = oneHeightCarrier`,
`R = (2, 1, 1, 0)`, `c = outOfClassSlots`, `ϑ ≡ 1`, `(k, m₀, s₀) = (2, 1, 0)`: every hypothesis
holds — `hatt` is satisfied at the slot `s = 1`, which is NOT in the class of `s₀ = 0`, because
the truncating `ℕ`-division `(s − s₀)/ℓ = 0` rounds it in — while the conclusion's coefficient
vector is supported on the class of `s₀`, where the family is zero. -/
theorem twisted_slot_spec_false :
    ¬ (∀ {O : Type} [CommRing O] {K K' : Type} [Field K] [Field K'] [Algebra K K']
        (C : SlotCarrier O K) (R : RungDatum) {η : K'},
        (minpoly K η).natDegree = Module.finrank K K' → IsIntegral K η →
        R.g = Module.finrank K K' →
        ∀ c : ℕ → Polynomial O,
        (∀ s, (c s).natDegree < C.D) → (∀ s, R.slotCount ≤ s → c s = 0) →
        (∃ s < R.slotCount, c s ≠ 0) →
        ∀ ϑ : Fin R.g → K, (∀ t, ϑ t ≠ 0) →
        ∀ {k m₀ s₀ : ℕ}, s₀ < R.ℓ → R.ℓ * m₀ + s₀ * R.u = k →
        (∀ s < R.slotCount, c s ≠ 0 → ∀ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) →
          (k : ℤ) ≤ R.ℓ * v + s * R.u) →
        (∃ s < R.slotCount, c s ≠ 0 ∧
          C.hgt (c s) = (((m₀ : ℤ) - (((s - s₀) / R.ℓ : ℕ) : ℤ) * (R.u : ℤ)) : WithTop ℤ)) →
        seamSumT (fun t : Fin R.g =>
            if s₀ + R.ℓ * (t : ℕ) < R.slotCount ∧ c (s₀ + R.ℓ * (t : ℕ)) ≠ 0
              then C.dig (c (s₀ + R.ℓ * (t : ℕ))) else 0) ϑ η ≠ 0) := by
  intro h
  -- the stage data: `η = 0` generates `ℚ` over `ℚ`, of degree `1 = R.g`
  have hgen : (minpoly ℚ (0 : ℚ)).natDegree = Module.finrank ℚ ℚ := by
    simp [minpoly.zero]
  have hint : IsIntegral ℚ (0 : ℚ) := isIntegral_zero
  have hgg : E29Refutation.rungTwoOne.g = Module.finrank ℚ ℚ := by simp
  -- the slot family: degrees, support, occupancy
  have hdeg : ∀ s, (E29Refutation.outOfClassSlots s).natDegree < E29Refutation.oneHeightCarrier.D := by
    intro s
    by_cases hs : s = 1 <;> simp [E29Refutation.outOfClassSlots, hs]
  have hsupp : ∀ s, E29Refutation.rungTwoOne.slotCount ≤ s → E29Refutation.outOfClassSlots s = 0 := by
    intro s hs
    exact E29Refutation.outOfClassSlots_eq_zero_of_ne_one (by simp at hs; omega)
  have hocc : ∃ s < E29Refutation.rungTwoOne.slotCount, E29Refutation.outOfClassSlots s ≠ 0 :=
    ⟨1, by simp, by simp⟩
  -- `k = 2` IS a lower bound for the slot values (the only occupied slot has value `3`)
  have hmin : ∀ s < E29Refutation.rungTwoOne.slotCount, E29Refutation.outOfClassSlots s ≠ 0 →
      ∀ v : ℤ, E29Refutation.oneHeightCarrier.hgt (E29Refutation.outOfClassSlots s) =
        (v : WithTop ℤ) →
      ((2 : ℕ) : ℤ) ≤ E29Refutation.rungTwoOne.ℓ * v + s * E29Refutation.rungTwoOne.u := by
    intro s hs hne v hv
    have hs1 : s = 1 := by
      by_contra hc
      exact hne (E29Refutation.outOfClassSlots_eq_zero_of_ne_one hc)
    subst hs1
    have hv1 : v = 1 := by
      have h1 : ((1 : ℤ) : WithTop ℤ) = (v : WithTop ℤ) := by simpa using hv
      exact_mod_cast h1.symm
    subst hv1
    norm_num
  -- and the signed `hatt` is satisfied — at the OUT-OF-CLASS slot `s = 1`
  have hatt : ∃ s < E29Refutation.rungTwoOne.slotCount, E29Refutation.outOfClassSlots s ≠ 0 ∧
      E29Refutation.oneHeightCarrier.hgt (E29Refutation.outOfClassSlots s) =
        ((((1 : ℕ) : ℤ) - (((s - 0) / E29Refutation.rungTwoOne.ℓ : ℕ) : ℤ)
          * (E29Refutation.rungTwoOne.u : ℤ)) : WithTop ℤ) := by
    refine ⟨1, by simp, by simp, ?_⟩
    norm_num
  have hfalse := h E29Refutation.oneHeightCarrier E29Refutation.rungTwoOne hgen hint hgg
    E29Refutation.outOfClassSlots hdeg hsupp hocc (fun _ => 1) (fun _ => one_ne_zero)
    (k := 2) (m₀ := 1) (s₀ := 0) (by simp) (by simp) hmin hatt
  -- but the guarded coefficient vector is supported on the class of `s₀ = 0`, where `c` vanishes
  apply hfalse
  simp [seamSumT]

/-! ## The class location of an attainer (E.28's content at `ℤ`-valued heights) -/

/-- **The attainer of the slot minimum lies in the class of `s₀`.** If the slot `s < slotCount`
carries height `v` with value `ℓv + su = k`, and `k = ℓm₀ + s₀u` with `s₀ < ℓ`, then
`s = s₀ + ℓt` for a unique `t < g`. This is E.28's separation content (`EFF.HE7.11` Step 2) at
`ℤ`-valued heights, which E.28's `ℕ`-height statements cannot reach (carrier heights are
`WithTop ℤ` by DECISION D-E1). Coprimality of `(u, ℓ)` — E.01's `hcop` field — is what strips
the `u`. -/
theorem attainer_in_class (R : RungDatum) {k m₀ s₀ s : ℕ} {v : ℤ}
    (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k) (hs : s < R.slotCount)
    (hval : (R.ℓ : ℤ) * v + (s : ℤ) * (R.u : ℤ) = (k : ℤ)) :
    ∃ t < R.g, s = s₀ + R.ℓ * t := by
  have hk' : (R.ℓ : ℤ) * (m₀ : ℤ) + (s₀ : ℤ) * (R.u : ℤ) = (k : ℤ) := by exact_mod_cast hk
  -- the two value equations give `ℓ ∣ (s₀ − s)·u`
  have hdvd : (R.ℓ : ℤ) ∣ ((s₀ : ℤ) - (s : ℤ)) * (R.u : ℤ) := ⟨v - m₀, by linarith⟩
  have hgcd : Int.gcd (R.ℓ : ℤ) (R.u : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.symm R.hcop
  have hdvd' : (R.ℓ : ℤ) ∣ ((s₀ : ℤ) - (s : ℤ)) :=
    Int.dvd_of_dvd_mul_left_of_gcd_one hdvd hgcd
  -- hence `s ≡ s₀ (mod ℓ)`, and `s₀ < ℓ` makes `s₀` the residue itself
  have hmod : s % R.ℓ = s₀ := by
    have h1 : (s : ℤ) % (R.ℓ : ℤ) = (s₀ : ℤ) % (R.ℓ : ℤ) := Int.modEq_iff_dvd.mpr hdvd'
    have h2 : ((s % R.ℓ : ℕ) : ℤ) = ((s₀ % R.ℓ : ℕ) : ℤ) := by
      rw [Int.natCast_mod, Int.natCast_mod]; exact h1
    have h3 : s % R.ℓ = s₀ % R.ℓ := Nat.cast_inj.mp h2
    rwa [Nat.mod_eq_of_lt hs₀] at h3
  obtain ⟨t, ht⟩ : ∃ t, s = s₀ + R.ℓ * t := by
    refine ⟨s / R.ℓ, ?_⟩
    have hdm : R.ℓ * (s / R.ℓ) + s % R.ℓ = s := Nat.div_add_mod s R.ℓ
    rw [hmod] at hdm
    rw [Nat.add_comm]
    exact hdm.symm
  refine ⟨t, ?_, ht⟩
  -- `ℓt ≤ s < ℓg`
  have h1 : s₀ + R.ℓ * t < R.ℓ * R.g := by
    rw [← ht]; simpa [RungDatum.slotCount] using hs
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt (Nat.le_add_left _ _) h1)

/-! ## The two repair candidates (non-signed names, awaiting an orchestrator amendment) -/

section Repair

open scoped Classical in
set_option linter.unusedVariables false in
/-- **Repair candidate 1** — the signed statement with the single change that `hatt` records the
attained VALUE (`ℓv + su = k`) instead of a height computed through a truncating division. This
is the faithful reading of R1-b Step 2's "the minimum is attained": the class location is then a
CONCLUSION (`attainer_in_class`), exactly as STATEMENT clause (i) promises. PROVED.

`hmin` and `hocc` are carried for signature fidelity and are not consumed: minimality is what
makes `k` the next level's height, while the kill clause needs only that some in-class slot
attains it. -/
theorem twisted_slot_spec_of_attain_value {O : Type*} [CommRing O] {K K' : Type*} [Field K]
    [Field K'] [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    (c : ℕ → Polynomial O)
    (hdeg : ∀ s, (c s).natDegree < C.D) (hsupp : ∀ s, R.slotCount ≤ s → c s = 0)
    (hocc : ∃ s < R.slotCount, c s ≠ 0)
    (ϑ : Fin R.g → K) (hϑ : ∀ t, ϑ t ≠ 0)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hmin : ∀ s < R.slotCount, c s ≠ 0 → ∀ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) →
      (k : ℤ) ≤ R.ℓ * v + s * R.u)
    (hatt : ∃ s < R.slotCount, c s ≠ 0 ∧ ∃ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) ∧
      (R.ℓ : ℤ) * v + (s : ℤ) * (R.u : ℤ) = (k : ℤ)) :
    seamSumT (fun t : Fin R.g =>
        if s₀ + R.ℓ * (t : ℕ) < R.slotCount ∧ c (s₀ + R.ℓ * (t : ℕ)) ≠ 0
          then C.dig (c (s₀ + R.ℓ * (t : ℕ))) else 0) ϑ η ≠ 0 := by
  obtain ⟨s, hs, hcs, v, hv, hval⟩ := hatt
  obtain ⟨t, htg, hts⟩ := attainer_in_class R hs₀ hk hs hval
  refine seamSumT_ne_zero hgen hint hg _ ϑ ⟨⟨t, htg⟩, ?_⟩ hϑ
  have hidx : s₀ + R.ℓ * ((⟨t, htg⟩ : Fin R.g) : ℕ) = s := hts.symm
  rw [hidx, if_pos ⟨hs, hcs⟩]
  exact C.dig_ne_zero _ hcs (hdeg s)

open scoped Classical in
set_option linter.unusedVariables false in
/-- **Repair candidate 2** — the minimal repair: `hatt` names an occupied in-class slot
directly. `k`, `m₀`, `hk` and `hmin` are then not needed and are dropped from the binders (this
is the shape a consumer that has already located the class — e.g. through E.28 — will want).
PROVED. -/
theorem twisted_slot_spec_of_attain_inClass {O : Type*} [CommRing O] {K K' : Type*} [Field K]
    [Field K'] [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    (c : ℕ → Polynomial O)
    (hdeg : ∀ s, (c s).natDegree < C.D) (hsupp : ∀ s, R.slotCount ≤ s → c s = 0)
    (ϑ : Fin R.g → K) (hϑ : ∀ t, ϑ t ≠ 0)
    {s₀ : ℕ} (hs₀ : s₀ < R.ℓ)
    (hatt : ∃ t : Fin R.g, s₀ + R.ℓ * (t : ℕ) < R.slotCount ∧ c (s₀ + R.ℓ * (t : ℕ)) ≠ 0) :
    seamSumT (fun t : Fin R.g =>
        if s₀ + R.ℓ * (t : ℕ) < R.slotCount ∧ c (s₀ + R.ℓ * (t : ℕ)) ≠ 0
          then C.dig (c (s₀ + R.ℓ * (t : ℕ))) else 0) ϑ η ≠ 0 := by
  obtain ⟨t, htlt, htne⟩ := hatt
  refine seamSumT_ne_zero hgen hint hg _ ϑ ⟨t, ?_⟩ hϑ
  rw [if_pos ⟨htlt, htne⟩]
  exact C.dig_ne_zero _ htne (hdeg _)

end Repair

/-! ## The SIGNED NAME, at the A-E.4 re-signed form -/

open scoped Classical in
/-- **NODE E.29's signed contract, `twisted_slot_spec`, at the AMENDMENT A-E.4 form.** The single
change against the committed signature is `hatt`: it records the ATTAINED VALUE
(`∃ v, C.hgt (c s) = v ∧ ℓv + su = k`) rather than a height computed through the truncating
`ℕ`-division `((s − s₀)/ℓ)`, which admitted out-of-class attainers and made the committed form
FALSE (`twisted_slot_spec_false` above). Every other binder — including `hocc` and `hmin` — is
byte-unchanged: `hmin` is the lower-bound half of the source's `k := min_s(ℓ·w(c_s) + s·u)`
(`EFF.HE7.11` Step 2 / `EFF.HE7.110` Step 3), so it stays as an honest inert binder even though
this clause's proof does not consume it.

The class location that STATEMENT clause (i) announces is DERIVED here, not assumed — through
`attainer_in_class`, which is `EFF.HE7.11` Step 2's separation argument at `ℤ`-valued heights.
Proof: the re-signed statement is repair candidate 1, so this is that candidate under the signed
name. -/
theorem twisted_slot_spec {O : Type*} [CommRing O] {K K' : Type*} [Field K]
    [Field K'] [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    (c : ℕ → Polynomial O)
    (hdeg : ∀ s, (c s).natDegree < C.D) (hsupp : ∀ s, R.slotCount ≤ s → c s = 0)
    (hocc : ∃ s < R.slotCount, c s ≠ 0)
    (ϑ : Fin R.g → K) (hϑ : ∀ t, ϑ t ≠ 0)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hmin : ∀ s < R.slotCount, c s ≠ 0 → ∀ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) →
      (k : ℤ) ≤ R.ℓ * v + s * R.u)
    (hatt : ∃ s < R.slotCount, c s ≠ 0 ∧ ∃ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) ∧
      (R.ℓ : ℤ) * v + (s : ℤ) * (R.u : ℤ) = (k : ℤ)) :
    seamSumT (fun t : Fin R.g =>
        if s₀ + R.ℓ * (t : ℕ) < R.slotCount ∧ c (s₀ + R.ℓ * (t : ℕ)) ≠ 0
          then C.dig (c (s₀ + R.ℓ * (t : ℕ))) else 0) ϑ η ≠ 0 :=
  twisted_slot_spec_of_attain_value C R hgen hint hg c hdeg hsupp hocc ϑ hϑ hs₀ hk hmin hatt

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.E29Refutation.oneHeightCarrier
#print axioms Uniformity.Density.Ladder.E29Refutation.rungTwoOne
#print axioms Uniformity.Density.Ladder.E29Refutation.outOfClassSlots
#print axioms Uniformity.Density.Ladder.twisted_slot_spec_false
#print axioms Uniformity.Density.Ladder.attainer_in_class
#print axioms Uniformity.Density.Ladder.twisted_slot_spec_of_attain_value
#print axioms Uniformity.Density.Ladder.twisted_slot_spec_of_attain_inClass
#print axioms Uniformity.Density.Ladder.twisted_slot_spec

end AxCheck
