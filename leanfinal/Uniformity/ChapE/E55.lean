/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapE.E55a

/-!
# Uniformity.ChapE.E55 — LEMMA HE7-8, RE-SIGNED at AMENDMENT A-E.5

**Chapter E, NODE E.55** [theorem] [fresh] — **HARD NODE**
(`blueprint/CHAP-E_sigma_ladder.md` §8, `refine_chain_finite`, **re-signed by A-E.5, 2026-08-16**;
stub twin `leanspec/Leanspec/ChapE.lean:1112-1141`). ENV-E2 +
`[IsAdicComplete (IsLocalRing.maximalIdeal O) O]`.

**STATUS: LANDED at the A-E.5 form.** The COMMITTED signature was refuted here, twice, with
machine-checked counterexamples; the signed name was WITHHELD pending adjudication (the E.29 /
`E29.lean` discipline: a claim shown false never enters the environment as a fact, the
counterexample lands as provenance, the repair lands under a non-signed name). **AMENDMENT A-E.5
adjudicated the re-sign in favour of `refine_chain_finite_of_key`** — the committed binders plus
the two frame data the stub dropped, both traced to the SOURCE display (`EFF.HE7.53` via
`EFF.HE7.44`(c)(6) and `EFF.HE7.11`) — so §6 below declares the signed name
`refine_chain_finite` at that type. Both refutations are RETAINED, verbatim, as the permanent
record of what the committed form asserted.

## What the corpus lemma says (unchanged, and PROVED below)

LEMMA HE7-8 / `(REF-TERM)` (`EFF.HE7.53`, characteristic-free): an INFINITE α-refine chain —
keys `Ψ^{(0)} = Ψ`, `Ψ^{(j+1)} = Ψ^{(j)} − w_j`, increment heights `λ^{(j)}` strictly increasing,
each stage clearing the single-side floor `hgt (A_m^{(j)}) ≥ (μ₂ − m)λ^{(j)}` — forces
`F = (Ψ − W)^{μ₂}` for the π-adic limit `W` of the partial sums, so with `μ₂ ≥ 2` the image of `F`
in the fraction field is not squarefree. Contradiction; hence every α-refine chain is finite. The
limit half is `E55a.lean` (`exists_limit_key`); the squarefree half is `refine_chain_finite_of_key`
below.

## DEFECT E-D14 — the committed signature is FALSE (two independent holes)

The committed binders are (stub, verbatim): a carrier `C`, the coefficient link `hcoeff` (a
statement about polynomials of degree `< C.D` ONLY), `hμ : 2 ≤ μ₂`,
`hsq : Squarefree (F.map (algebraMap O (FractionRing O)))`, increments `w` with
`hdeg : (w j).natDegree < C.D`, `hh : C.hgt (w j) = lam j`, `hmono : StrictMono lam`, development
coefficients `A` with `hdev` and `hfloor`, concluding `False`. Missing, and each independently
fatal:

1. **no degree bound on the development coefficients `A j m`.** `hcoeff` converts a HEIGHT into
   divisibilities of the `O`-coefficients only for polynomials of degree `< C.D`. A carrier whose
   `hgt` reads one coefficient (a legitimate `SlotCarrier` — every field is checked below) lets
   `A j m` hide an arbitrarily large part above that coefficient, and then the floors constrain
   nothing. `refine_chain_finite_false` builds exactly that: over `(ZMod 2)⟦T⟧` with `C.D = 1`,
   `Ψ = x`, `F = x + 1` (degree 1, hence squarefree over the fraction field), increments
   `w i = T^i(1 + T)` of heights `λ_i = i`, and `A j 0 = x² + x + T^{2j}` whose CONSTANT
   coefficient meets the floor `2j` exactly while its `x²`-part carries the whole discrepancy.
   Every committed hypothesis holds; `False` does not.
2. **no degree hypothesis on the key `Ψ`.** Even with hole 1 patched, `Ψ` may be constant, and
   then `Ψ − W` is a unit in the fraction field, so `(Ψ − W)^{μ₂}` IS squarefree and the corpus's
   step 4 has nothing to contradict. `refine_chain_finite_boundedDev_false` is that: same carrier,
   `Ψ = 0`, `F = 1`, `A j 0 = T^{2j}` (degree 0, so the patched hypothesis holds).

Neither hole is in the SOURCE: in `EFF.HE7.53` the `A_m` ARE the key-development coefficients
(degree `< D″` by construction) and `Ψ` IS the current key (degree exactly `D″`). The stub dropped
two data of the frame. **This is a signature defect, not a mathematical one** — the repair adds
the two data back and the corpus proof goes through unchanged.

## The source displays behind the two added binders (verbatim, A-E.5's verification)

`hAdeg`, i.e. `deg (A j m) < D″`. `EFF.HE7.53`'s own proof invokes `(SLOT₂)` on the development
coefficients — “*Now dv₂(A) → ∞ forces the Φ′-development coefficients of A, hence its
O-coefficients, to converge π-adically to 0 (by (SLOT₂): dv₂(A) = min_s(ℓ dv(c_s) + su), so every
dv(c_s) → ∞, so every v of every O-coefficient → ∞)*”. `(SLOT₂)` is stated with the degree bound
as its FIRST hypothesis (`EFF.HE7.11`): “*Let C ∈ O[x] with **deg C < D″** and let
C = Σ_{s<ℓd_r} c_s·Φ′^{s} (deg c_s < D′) be its Φ′-development.*” And the `A_m` meet it by
construction, `EFF.HE7.44`(c) item (6): “*the developments in powers of the monic degree-D″
polynomial Ψ^{(w)} have **coefficients of degree < D″**, so (SLOT₂) applies to them*.” So the
Lean binder `hAdeg : ∀ j m, (A j m).natDegree < C.D` is the source's `deg A_m^{(2,j)} < D″` at
`C.D = D″`, and `hcoeff` (the Lean transcription of the `(SLOT₂)` implication) carries exactly
that side condition.

`hkey`, i.e. `D″ ≤ deg Ψ`. The key's degree is fixed by `DEFINITION HE7-1` (`EFF.HE7.06`):
“*the **order-2 key** Ψ := Ψ_{λ,r} of DEFINITION HE6-1, **monic of degree D″ := D′ℓd_r***; never
assumed irreducible*”, and it is preserved along a refine chain — `EFF.HE7.44`: “*Put
Ψ^{(w)} := Ψ − w, **monic of degree D″***”, restated in that lemma's item (11) as
“*deg Ψ^{(w)} = D″*”. The Lean binder asks only for the `≤` half of that equality (`C.D` is the
carrier's *current key degree* field, E.10), which is all the squarefree step consumes; it is
therefore strictly weaker than the source datum and cannot over-assume.

The counterexamples are minimal in the sense that matters: each satisfies the OTHER repair
hypothesis (in 1, `C.D ≤ Ψ.natDegree` holds — `1 ≤ 1`; in 2, `hAdeg` holds — all development
coefficients are constants), so neither added hypothesis can be dropped.

## The repair (proved), and the signed name over it

`refine_chain_finite_of_key` = the committed signature **plus**
`hAdeg : ∀ j m, (A j m).natDegree < C.D` and `hkey : C.D ≤ Ψ.natDegree`, concluding `False`. Every
other binder is byte-identical to the committed one, in the committed order. **AMENDMENT A-E.5
adopted exactly this statement as E.55's signed contract**; §6 declares `refine_chain_finite` at
it, and `leanspec/Leanspec/ChapE.lean`'s stub is re-signed to match. The two added binders are
frame data the instances supply for free (the displays quoted above).

## Faithfulness

**⚠ Mandatory, trust-boundary content** (parent CLAUDE.md): this file declares the refuting
INSTANCE data — a `SlotCarrier` (`coeffZeroCarrier`), a ring, increments, and a development. Three
recasts to check:

* *the counterexample carrier is a real `SlotCarrier`, not a degenerate stub.* `coeffZeroCarrier`
  has `D = 1`, `hgt A = addVal (A.coeff 0)`, `dig A = 1` off the coefficient-zero vanishing locus.
  All fields are discharged: both ultrametric laws hold because `addVal` is an `AddValuation` and
  `(A+B).coeff 0 = A.coeff 0 + B.coeff 0`; `dig_add` holds because at a shared FINITE height both
  digits are `1` and `1 + 1 = 0` in `ZMod 2`, so its hypothesis `dig A + dig B ≠ 0` is never met.
  ⚠ That last one is a vacuity, and it is deliberate: the digit layer plays no role in HE7-8, and
  a vacuous `dig_add` weakens the counterexample not at all (`dig_add` is a constraint ON the
  carrier — a carrier satisfying it vacuously is still a carrier). `Full = fun _ => False` makes
  `hlift` vacuous for the same reason, and this IS a real weakening of the carrier's strength: see
  the fence below.
* *the fence on `Full`.* A reader may object that a counterexample with no full heights is cheap.
  It is not available as a rescue: `(LIFT)` is a statement about which digits are REALISED at a
  height, and HE7-8's proof (`EFF.HE7.53`) never invokes it — the corpus's own summary is that
  "the node condition … plus `λ^{(j)} → ∞` is all that is used". Adding `Full` values could only
  add hypotheses to the counterexample's carrier, and the defect is that the committed statement
  omits a hypothesis about `A j m`, which no `Full` value supplies.
* *the ambient ring is char 2, the label field is `ZMod 2`, and neither is load-bearing.*
  Characteristic 2 buys arithmetic convenience only (`(1 + T^j)² = 1 + T^{2j}`, and the vacuous
  `dig_add`); the same construction runs over any complete DVR with the geometric-series limit,
  at the price of one unit inversion. `(ZMod 2)⟦T⟧` is chosen because mathlib has all four
  instances the committed binders demand — `CommRing`, `IsDomain`, `IsDiscreteValuationRing`,
  `IsAdicComplete (maximalIdeal ·) ·` — so the refutation is not vacuous for lack of a model.

**DEPENDS.** E.10 (`SlotCarrier`), E.55a (`exists_limit_key`, `CoeffsIn`) · mathlib
`PowerSeries` (DVR + adic completeness of `k⟦X⟧`), `IsDiscreteValuationRing.addVal`,
`Polynomial.separable_X_sub_C`, `Squarefree`.

**SOURCE.** `EFF.HE7.53` (LEMMA HE7-8 statement and proof); `EFF.HE7.11` (`(SLOT₂)`, whose
`deg C < D″` hypothesis is `hAdeg`), `EFF.HE7.44`(c)(6) + `EFF.HE7.06`/`DEFINITION HE7-1` (the
key monic of degree `D″`, which is `hkey`); `EFF.T2.26`/`EFF.T2.52` (`HE7-REF-TERM` as the
`(SEC-RANK)` supplier in well-foundedness form). The defect record is E's own (E-D14, this file),
adjudicated by AMENDMENT A-E.5 in the A-E.3/A-E.4 pattern.

**TEETH.** unchanged — Q1's 42 one-step refines, PE2's 2-step chains, `he7annex_supp.py` P4
(48/48 wrong-continuation cycles). None of them exercises the missing binders, which is exactly
why the defect survived to the stub gate.

## Status

Sorry-free, axiom-free (Lean core only). `refine_chain_finite` — the SIGNED NAME — is declared in
§6 at the A-E.5 re-signed type, over `refine_chain_finite_of_key`.
-/

open Polynomial IsDiscreteValuationRing

namespace Uniformity.Density.Ladder

/-! ## §1 The refuting carrier: heights read the constant coefficient -/

/-- `ℕ∞ → WithTop ℤ`, the reading `hcoeff` uses. -/
private noncomputable def nv : ℕ∞ → WithTop ℤ := fun x => x.map (fun n : ℕ => (n : ℤ))

private lemma nv_le_nv {x y : ℕ∞} : nv x ≤ nv y ↔ x ≤ y := by
  induction x with
  | top => cases y with
    | top => simp [nv]
    | coe m => simp [nv]
  | coe n => cases y with
    | top => simp [nv]
    | coe m => simp [nv]

private lemma nv_mono : Monotone nv := fun _ _ h => nv_le_nv.mpr h

private lemma nv_min (x y : ℕ∞) : nv (min x y) = min (nv x) (nv y) := nv_mono.map_min

open scoped Classical in
/-- **The refuting carrier.** Over any DVR `O`, the `D = 1` slot carrier whose height is the
`addVal` of the constant coefficient and whose digit is the indicator of that coefficient's
non-vanishing, valued in `ZMod 2`. Every `SlotCarrier` law is discharged below (see the header's
faithfulness note on the two vacuous ones). -/
noncomputable def coeffZeroCarrier (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : SlotCarrier O (ZMod 2) where
  D := 1
  hD := one_pos
  eC := 1
  fC := 1
  hef := (one_mul 1).symm
  heC := le_refl 1
  hfC := le_refl 1
  hgt A := nv (addVal O (A.coeff 0))
  dig A := if A.coeff 0 = 0 then 0 else 1
  hgt_zero := by simp [nv]
  dig_zero := by simp
  hgt_ne_top := by
    intro A hA hdeg
    have h0 : A.coeff 0 ≠ 0 := fun h => hA (by
      have hC : A = C (A.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hdeg)
      rw [hC, h, map_zero])
    have hne : addVal O (A.coeff 0) ≠ ⊤ := by simpa [addVal_eq_top_iff] using h0
    cases hx : addVal O (A.coeff 0) with
    | top => exact absurd hx hne
    | coe m => simp [nv]
  dig_ne_zero := by
    intro A hA hdeg
    have h0 : A.coeff 0 ≠ 0 := fun h => hA (by
      have hC : A = C (A.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hdeg)
      rw [hC, h, map_zero])
    rw [if_neg h0]
    decide
  hgt_add_ge := by
    intro A B
    simp only [coeff_add]
    rw [← nv_min]
    exact nv_mono addVal_add
  hgt_add_eq := by
    intro A B h
    have hne : addVal O (A.coeff 0) ≠ addVal O (B.coeff 0) := fun hcon => h (by rw [hcon])
    simp only [coeff_add]
    rw [AddValuation.map_add_of_distinct_val _ hne, nv_min]
  dig_add := by
    intro A B k hA hB hne
    exfalso
    have hA0 : A.coeff 0 ≠ 0 := by intro h; rw [h] at hA; simp [nv] at hA
    have hB0 : B.coeff 0 ≠ 0 := by intro h; rw [h] at hB; simp [nv] at hB
    exact hne (by rw [if_neg hA0, if_neg hB0]; decide)
  Full := fun _ => False
  hlift := by intro k hk; exact hk.elim

/-- The carrier's coefficient link `hcoeff` — at `D = 1` it is the definition at `i = 0` and the
vanishing of the higher coefficients elsewhere. -/
lemma coeffZeroCarrier_hcoeff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Polynomial O) (v : ℤ) (hd : A.natDegree < (coeffZeroCarrier O).D)
    (hle : (v : WithTop ℤ) ≤ (coeffZeroCarrier O).hgt A) (i : ℕ) :
    (v : WithTop ℤ) ≤ (addVal O (A.coeff i)).map (fun n : ℕ => (n : ℤ)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact hle
  · have h0 : A.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simp only [coeffZeroCarrier] at hd; omega)
    rw [h0, addVal_zero]
    simp

/-- Definitional unfoldings, so the proofs below never change a goal by `show`. -/
private lemma coeffZeroCarrier_D {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    (coeffZeroCarrier O).D = 1 := rfl

private lemma coeffZeroCarrier_hgt {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (A : Polynomial O) :
    (coeffZeroCarrier O).hgt A = nv (addVal O (A.coeff 0)) := rfl

private lemma nv_natCast (n : ℕ) : nv (n : ℕ∞) = ((n : ℤ) : WithTop ℤ) := rfl

/-! ## §2 The refuting ring `(ZMod 2)⟦T⟧` and the refuting chain -/

/-- The refuting ring: power series over `ZMod 2`. A complete DVR of characteristic 2. -/
abbrev CexRing := PowerSeries (ZMod 2)

noncomputable instance : IsAdicComplete (IsLocalRing.maximalIdeal CexRing) CexRing := by
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

instance : CharP CexRing 2 := charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod 2)) 2

lemma cex_two_eq_zero : (2 : CexRing) = 0 := by
  have := CharP.cast_eq_zero CexRing 2
  simpa using this

/-- The uniformizer of the refuting ring. -/
noncomputable abbrev cexT : CexRing := PowerSeries.X

/-- The refuting increments: `w i = T^i + T^(i+1) = T^i(1 + T)`, of height exactly `i`. -/
noncomputable def cexIncr : ℕ → Polynomial CexRing := fun i => C (cexT ^ i + cexT ^ (i + 1))

/-- The refuting slopes: `λ_i = i`, strictly increasing. -/
def cexSlope : ℕ → ℤ := fun i => (i : ℤ)

/-- The refuting development coefficients for hole 1: `A j 0 = x² + x + T^{2j}`, whose CONSTANT
coefficient `T^{2j}` meets the floor `2j` exactly while the `x²`-part is invisible to the
carrier — this is the whole defect. -/
noncomputable def cexDev : ℕ → ℕ → Polynomial CexRing
  | j, 0 => (X : Polynomial CexRing) ^ 2 + X + C (cexT ^ (2 * j))
  | _, _ + 1 => 0

/-- The refuting development coefficients for hole 2: constants, so sub-key degree. -/
noncomputable def cexDev' : ℕ → ℕ → Polynomial CexRing
  | j, 0 => C (cexT ^ (2 * j))
  | _, _ + 1 => 0

private lemma cexDev_succ (j m : ℕ) : cexDev j (m + 1) = 0 := rfl

private lemma cexDev'_succ (j m : ℕ) : cexDev' j (m + 1) = 0 := rfl

private lemma hgt_C (a : CexRing) :
    (coeffZeroCarrier CexRing).hgt (C a) = nv (addVal CexRing a) := by
  rw [coeffZeroCarrier_hgt, coeff_C_zero]

/-- The partial sums telescope: `∑_{i<j} w i = 1 + T^j` (at `j = 0` this reads `1 + 1 = 0`,
char 2). -/
lemma cex_sum_incr (j : ℕ) : ∑ i ∈ Finset.range j, cexIncr i = C (1 + cexT ^ j) := by
  induction j with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
      rw [show (1 : CexRing) + 1 = 0 by linear_combination cex_two_eq_zero, map_zero]
  | succ j ih =>
      rw [Finset.sum_range_succ, ih, cexIncr, ← map_add]
      congr 1
      linear_combination (cexT ^ j) * cex_two_eq_zero

lemma cex_hh (i : ℕ) :
    (coeffZeroCarrier CexRing).hgt (cexIncr i) = ((cexSlope i : ℤ) : WithTop ℤ) := by
  have hu : IsUnit (1 + cexT) := by rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  have hfac : cexT ^ i + cexT ^ (i + 1) = cexT ^ i * (1 + cexT) := by ring
  rw [cexIncr, hgt_C, hfac, addVal_mul, Irreducible.addVal_pow PowerSeries.X_irreducible i,
    addVal_eq_zero_iff.mpr hu, add_zero]
  simp [nv, cexSlope]

lemma cex_hmono : StrictMono cexSlope := fun _ _ hab => by simpa [cexSlope] using hab

lemma cex_hdeg (i : ℕ) : (cexIncr i).natDegree < (coeffZeroCarrier CexRing).D := by
  rw [coeffZeroCarrier_D, cexIncr, natDegree_C]
  norm_num

/-- The char-2 identity the two developments run on. -/
private lemma cex_key (j : ℕ) : ((1 : CexRing) + cexT ^ j) ^ 2 + cexT ^ (2 * j) = 1 := by
  linear_combination (cexT ^ j + cexT ^ (2 * j)) * cex_two_eq_zero

private lemma cex_keyC (j : ℕ) :
    (C ((1 : CexRing) + cexT ^ j)) ^ 2 + C (cexT ^ (2 * j)) = 1 := by
  rw [← map_pow, ← map_add, cex_key, map_one]

private lemma cex_two_poly : (2 : Polynomial CexRing) = 0 := by
  have h : (Polynomial.C (2 : CexRing)) = (2 : Polynomial CexRing) := map_ofNat Polynomial.C 2
  rw [← h, cex_two_eq_zero, map_zero]

/-- Hole 1's development identity, at the key `Ψ = x`: for EVERY `j`,
`x + 1 = (x − (1 + T^j))² + (x² + x + T^{2j})`. -/
lemma cex_hdev (j : ℕ) :
    (X : Polynomial CexRing) + 1
      = ((X : Polynomial CexRing) - ∑ i ∈ Finset.range j, cexIncr i) ^ 2
        + ∑ m ∈ Finset.range 2,
            cexDev j m * ((X : Polynomial CexRing) - ∑ i ∈ Finset.range j, cexIncr i) ^ m := by
  rw [cex_sum_incr]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, cexDev,
    mul_one, zero_mul, add_zero]
  linear_combination (C ((1 : CexRing) + cexT ^ j) * X - X ^ 2) * cex_two_poly - cex_keyC j

/-- Hole 1's floors: the constant coefficient of `A j 0` has height exactly `2j`. -/
lemma cex_hfloor (j : ℕ) (m : ℕ) (hm : m < 2) :
    ((((2 - m : ℕ) : ℤ) * cexSlope j : ℤ) : WithTop ℤ)
      ≤ (coeffZeroCarrier CexRing).hgt (cexDev j m) := by
  interval_cases m
  · have hgtv : (coeffZeroCarrier CexRing).hgt (cexDev j 0)
        = nv (addVal CexRing (cexT ^ (2 * j))) := by
      rw [coeffZeroCarrier_hgt, cexDev]
      simp only [coeff_add, coeff_C_zero, coeff_X_zero, coeff_X_pow]
      norm_num
    rw [hgtv, Irreducible.addVal_pow PowerSeries.X_irreducible, nv_natCast]
    norm_num [cexSlope]
  · rw [cexDev_succ, (coeffZeroCarrier CexRing).hgt_zero]
    exact le_top

lemma cex_hsq :
    Squarefree (((X : Polynomial CexRing) + 1).map
      (algebraMap CexRing (FractionRing CexRing))) := by
  have hmap : ((X : Polynomial CexRing) + 1).map (algebraMap CexRing (FractionRing CexRing))
      = X - C (-1) := by
    simp [Polynomial.map_add, Polynomial.map_one, sub_eq_add_neg]
  rw [hmap]
  exact (Polynomial.separable_X_sub_C).squarefree

/-! ## §3 REFUTATION 1 — the committed signature is false (no degree bound on `A j m`) -/

/-- **DEFECT E-D14(1), machine-checked.** The COMMITTED E.55 signature
(`leanspec/Leanspec/ChapE.lean:1118-1136`, transcribed binder-for-binder with the two type
universes specialised to `Type`, which only strengthens the refutation) is FALSE.

Witness: `O = (ZMod 2)⟦T⟧`, `K = ZMod 2`, `C = coeffZeroCarrier` (`D = 1`), `Ψ = x`, `F = x + 1`
(squarefree over the fraction field), `μ₂ = 2`, `w i = T^i(1+T)` with `λ_i = i` strictly
increasing, and `A j 0 = x² + x + T^{2j}`, `A j 1 = 0`. Every committed hypothesis holds — the
floors are met with EQUALITY at `m = 0` — and no contradiction follows: the chain is genuinely
infinite because `F` is NOT the `μ₂`-th power of anything (the development coefficients are not
sub-key-degree, so `hcoeff` never sees the `x²`-part they hide).

Note `C.D ≤ Ψ.natDegree` holds here (`1 ≤ 1`), so this refutation is independent of the second
hole. -/
theorem refine_chain_finite_false :
    ¬ ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
      {K : Type} [Field K] (C : SlotCarrier O K),
      (∀ (A : Polynomial O) (v : ℤ), A.natDegree < C.D →
        (v : WithTop ℤ) ≤ C.hgt A → ∀ i,
          (v : WithTop ℤ) ≤ (IsDiscreteValuationRing.addVal O (A.coeff i)).map
            (fun n : ℕ => (n : ℤ))) →
      ∀ {F Ψ : Polynomial O} {μ₂ : ℕ}, 2 ≤ μ₂ →
      Squarefree (F.map (algebraMap O (FractionRing O))) →
      ∀ (w : ℕ → Polynomial O) (lam : ℕ → ℤ),
      (∀ j, (w j).natDegree < C.D) →
      (∀ j, C.hgt (w j) = (lam j : WithTop ℤ)) →
      StrictMono lam →
      ∀ (A : ℕ → ℕ → Polynomial O),
      (∀ j, F = (Ψ - ∑ i ∈ Finset.range j, w i) ^ μ₂
        + ∑ m ∈ Finset.range μ₂, A j m * (Ψ - ∑ i ∈ Finset.range j, w i) ^ m) →
      (∀ j, ∀ m < μ₂, (((((μ₂ - m : ℕ) : ℤ) * lam j : ℤ)) : WithTop ℤ) ≤ C.hgt (A j m)) →
      False := by
  intro h
  exact h (O := CexRing) (K := ZMod 2) (coeffZeroCarrier CexRing) coeffZeroCarrier_hcoeff
    (F := (X : Polynomial CexRing) + 1) (Ψ := (X : Polynomial CexRing)) (μ₂ := 2) le_rfl cex_hsq
    cexIncr cexSlope cex_hdeg cex_hh cex_hmono cexDev cex_hdev cex_hfloor

/-- The independence claim of the header, machine-checked: refutation 1's witness DOES satisfy the
second repair hypothesis `C.D ≤ Ψ.natDegree` (here `1 ≤ 1`), so hole 1 is not a shadow of hole 2. -/
example : (coeffZeroCarrier CexRing).D ≤ ((X : Polynomial CexRing)).natDegree := by
  rw [coeffZeroCarrier_D, natDegree_X]

/-! ## §4 REFUTATION 2 — patching hole 1 alone is not enough (`Ψ` may be constant) -/

/-- Hole 2's development identity, at the key `Ψ = 0`: `1 = (0 − (1 + T^j))² + T^{2j}`. -/
lemma cex_hdev' (j : ℕ) :
    (1 : Polynomial CexRing)
      = ((0 : Polynomial CexRing) - ∑ i ∈ Finset.range j, cexIncr i) ^ 2
        + ∑ m ∈ Finset.range 2,
            cexDev' j m * ((0 : Polynomial CexRing) - ∑ i ∈ Finset.range j, cexIncr i) ^ m := by
  rw [cex_sum_incr]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, cexDev',
    mul_one, zero_mul, add_zero]
  linear_combination -cex_keyC j

lemma cex_hfloor' (j : ℕ) (m : ℕ) (hm : m < 2) :
    ((((2 - m : ℕ) : ℤ) * cexSlope j : ℤ) : WithTop ℤ)
      ≤ (coeffZeroCarrier CexRing).hgt (cexDev' j m) := by
  interval_cases m
  · have hgtv : (coeffZeroCarrier CexRing).hgt (cexDev' j 0)
        = nv (addVal CexRing (cexT ^ (2 * j))) := by
      rw [coeffZeroCarrier_hgt, cexDev', coeff_C_zero]
    rw [hgtv, Irreducible.addVal_pow PowerSeries.X_irreducible, nv_natCast]
    norm_num [cexSlope]
  · rw [cexDev'_succ, (coeffZeroCarrier CexRing).hgt_zero]
    exact le_top

lemma cex_hAdeg' (j m : ℕ) : (cexDev' j m).natDegree < (coeffZeroCarrier CexRing).D := by
  rw [coeffZeroCarrier_D]
  match m with
  | 0 => rw [cexDev', natDegree_C]; norm_num
  | _ + 1 => rw [cexDev'_succ, natDegree_zero]; norm_num

/-- **DEFECT E-D14(2), machine-checked.** The committed signature PLUS the sub-key-degree bound on
the development coefficients is STILL false: with `Ψ = 0` and `F = 1` the limit is a unit, and a
unit's `μ₂`-th power is squarefree.

Witness: same carrier and increments, `Ψ = 0`, `F = 1`, `A j 0 = T^{2j}` (a constant, so
`hAdeg` holds), `A j 1 = 0`. So the repair needs a degree hypothesis on the KEY as well — the
frame datum `deg Ψ = D″` that the stub dropped. -/
theorem refine_chain_finite_boundedDev_false :
    ¬ ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
      {K : Type} [Field K] (C : SlotCarrier O K),
      (∀ (A : Polynomial O) (v : ℤ), A.natDegree < C.D →
        (v : WithTop ℤ) ≤ C.hgt A → ∀ i,
          (v : WithTop ℤ) ≤ (IsDiscreteValuationRing.addVal O (A.coeff i)).map
            (fun n : ℕ => (n : ℤ))) →
      ∀ {F Ψ : Polynomial O} {μ₂ : ℕ}, 2 ≤ μ₂ →
      Squarefree (F.map (algebraMap O (FractionRing O))) →
      ∀ (w : ℕ → Polynomial O) (lam : ℕ → ℤ),
      (∀ j, (w j).natDegree < C.D) →
      (∀ j, C.hgt (w j) = (lam j : WithTop ℤ)) →
      StrictMono lam →
      ∀ (A : ℕ → ℕ → Polynomial O),
      (∀ j m, (A j m).natDegree < C.D) →
      (∀ j, F = (Ψ - ∑ i ∈ Finset.range j, w i) ^ μ₂
        + ∑ m ∈ Finset.range μ₂, A j m * (Ψ - ∑ i ∈ Finset.range j, w i) ^ m) →
      (∀ j, ∀ m < μ₂, (((((μ₂ - m : ℕ) : ℤ) * lam j : ℤ)) : WithTop ℤ) ≤ C.hgt (A j m)) →
      False := by
  intro h
  refine h (O := CexRing) (K := ZMod 2) (coeffZeroCarrier CexRing) coeffZeroCarrier_hcoeff
    (F := (1 : Polynomial CexRing)) (Ψ := (0 : Polynomial CexRing)) (μ₂ := 2) le_rfl ?_
    cexIncr cexSlope cex_hdeg cex_hh cex_hmono cexDev' cex_hAdeg' cex_hdev' cex_hfloor'
  simp

/-! ## §5 THE REPAIR — LEMMA HE7-8 with the two frame data restored, PROVED -/

/-- **NODE E.55, repaired** (LEMMA HE7-8 / `(REF-TERM)`, `EFF.HE7.53`). An α-refine chain with
strictly increasing increment heights, sub-key-degree increments AND development coefficients, a
key of at least the carrier's degree, and squarefree `F` over the fraction field, cannot be
infinite: the hypotheses are contradictory.

The two binders `hAdeg` and `hkey` are the frame data the committed signature dropped; both are
necessary (`refine_chain_finite_false`, `refine_chain_finite_boundedDev_false`). Every other
binder is the committed one, in the committed order.

**AMENDMENT A-E.5 adopted this statement as the signed contract**; the signed name
`refine_chain_finite` (§6) is declared over it. This declaration is retained under its
adjudication-era name so that the amendment's citation stays resolvable. -/
theorem refine_chain_finite_of_key {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {K : Type*} [Field K] (C : SlotCarrier O K)
    (hcoeff : ∀ (A : Polynomial O) (v : ℤ), A.natDegree < C.D →
      (v : WithTop ℤ) ≤ C.hgt A → ∀ i,
        (v : WithTop ℤ) ≤ (addVal O (A.coeff i)).map (fun n : ℕ => (n : ℤ)))
    {F Ψ : Polynomial O} {μ₂ : ℕ} (hμ : 2 ≤ μ₂)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O))))
    (hkey : C.D ≤ Ψ.natDegree)
    (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hdeg : ∀ j, (w j).natDegree < C.D)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hmono : StrictMono lam)
    (A : ℕ → ℕ → Polynomial O)
    (hAdeg : ∀ j m, (A j m).natDegree < C.D)
    (hdev : ∀ j, F = (Ψ - ∑ i ∈ Finset.range j, w i) ^ μ₂
      + ∑ m ∈ Finset.range μ₂, A j m * (Ψ - ∑ i ∈ Finset.range j, w i) ^ m)
    (hfloor : ∀ j, ∀ m < μ₂, ((((μ₂ - m : ℕ) : ℤ) * lam j : ℤ) : WithTop ℤ) ≤ C.hgt (A j m)) :
    False := by
  obtain ⟨W, hWdeg, hFW⟩ :=
    exists_limit_key C hcoeff (μ₂ := μ₂) w lam hdeg hh hmono A hAdeg hdev hfloor
  have hdegsub : (Ψ - W).natDegree = Ψ.natDegree :=
    natDegree_sub_eq_left_of_natDegree_lt (lt_of_lt_of_le hWdeg hkey)
  set p := (Ψ - W).map (algebraMap O (FractionRing O)) with hp
  have hpdeg : p.natDegree = Ψ.natDegree := by
    rw [hp, natDegree_map_eq_of_injective (IsFractionRing.injective O (FractionRing O)), hdegsub]
  have hFmap : F.map (algebraMap O (FractionRing O)) = p ^ μ₂ := by
    rw [hFW, hp, Polynomial.map_pow]
  have hdvd : p * p ∣ F.map (algebraMap O (FractionRing O)) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hμ
    rw [hFmap, hk, pow_add]
    exact ⟨p ^ k, by ring⟩
  have hunit := hsq p hdvd
  have hpos : 0 < p.natDegree := by rw [hpdeg]; exact lt_of_lt_of_le C.hD hkey
  have := Polynomial.natDegree_eq_zero_of_isUnit hunit
  omega

/-! ## §6 THE SIGNED NAME, at the A-E.5 re-signed form -/

/-- **NODE E.55's signed contract, `refine_chain_finite`, at the AMENDMENT A-E.5 form**
(LEMMA HE7-8 / `(REF-TERM)`, `EFF.HE7.53`). The changes against the committed signature are
exactly two added binders, both frame data of the SOURCE that the stub dropped:

* `hkey : C.D ≤ Ψ.natDegree` (after `hsq`) — `DEFINITION HE7-1`'s key is "monic of degree
  `D″ := D′ℓd_r`", preserved along the chain by `EFF.HE7.44` ("Put `Ψ^{(w)} := Ψ − w`, monic of
  degree `D″`"); the binder takes only the `≤` half;
* `hAdeg : ∀ j m, (A j m).natDegree < C.D` (after `A`) — `EFF.HE7.44`(c)(6): the developments in
  powers of the monic degree-`D″` key "have coefficients of degree `< D″`, so `(SLOT₂)` applies to
  them", and `(SLOT₂)` (`EFF.HE7.11`) is precisely what `hcoeff` transcribes.

Every other binder is byte-unchanged, in the committed order. Both additions are INDEPENDENT and
NEITHER is removable: the committed form is refuted by `refine_chain_finite_false` (which
satisfies `hkey`) and the `hAdeg`-only patch by `refine_chain_finite_boundedDev_false` (which
satisfies `hAdeg`) — machine-checked, above. Proof: the re-signed statement IS the adopted repair,
so this is that repair under the signed name. -/
theorem refine_chain_finite {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {K : Type*} [Field K] (C : SlotCarrier O K)
    (hcoeff : ∀ (A : Polynomial O) (v : ℤ), A.natDegree < C.D →
      (v : WithTop ℤ) ≤ C.hgt A → ∀ i,
        (v : WithTop ℤ) ≤ (addVal O (A.coeff i)).map (fun n : ℕ => (n : ℤ)))
    {F Ψ : Polynomial O} {μ₂ : ℕ} (hμ : 2 ≤ μ₂)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O))))
    (hkey : C.D ≤ Ψ.natDegree)
    (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hdeg : ∀ j, (w j).natDegree < C.D)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hmono : StrictMono lam)
    (A : ℕ → ℕ → Polynomial O)
    (hAdeg : ∀ j m, (A j m).natDegree < C.D)
    (hdev : ∀ j, F = (Ψ - ∑ i ∈ Finset.range j, w i) ^ μ₂
      + ∑ m ∈ Finset.range μ₂, A j m * (Ψ - ∑ i ∈ Finset.range j, w i) ^ m)
    (hfloor : ∀ j, ∀ m < μ₂, ((((μ₂ - m : ℕ) : ℤ) * lam j : ℤ) : WithTop ℤ) ≤ C.hgt (A j m)) :
    False :=
  refine_chain_finite_of_key C hcoeff hμ hsq hkey w lam hdeg hh hmono A hAdeg hdev hfloor

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.refine_chain_finite_false
#print axioms Uniformity.Density.Ladder.refine_chain_finite_boundedDev_false
#print axioms Uniformity.Density.Ladder.refine_chain_finite_of_key
#print axioms Uniformity.Density.Ladder.refine_chain_finite
#print axioms Uniformity.Density.Ladder.coeffZeroCarrier

end AxCheck
