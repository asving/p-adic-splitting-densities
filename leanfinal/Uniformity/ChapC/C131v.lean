/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131m
import Uniformity.ChapC.C73

/-!
# Uniformity.ChapC.C131v — the shadow-discrepancy semantic identification

**Chapter C, NODE C.131v′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §3.8 (`Cnv13`) and §5).

This file identifies v2 `Cnv13`'s left-hand side — the value of the normal form produced by
C.131m′'s tagged structural census — with the displayed difference

```lean
shadowDev T f j - dev (composedKey T) f j
```

NON-circularly: nothing below is defined as a normal form *of* that difference.  The census
object is `taggedOuterNF F (xNF F (composedKey T)) f j` (C.131m′), split by its `paid` tag into

* the **unpaid value** (`paid = 0` terms — the coefficients reduced mod `Φ′`, §3.8's "reduced
  normal form produced by the tagged structural census"), and
* the **paid value** (`paid ≥ 1` terms — the branch-priced overflow),

each collapsed to `O[x]` by the canonical two-step evaluation at `Y = F.key` (`collapse`).
The semantics established here, all through C.131m′'s erasure theorem and C.131k′'s
reconstruction:

1. **The shadow read IS the census's unpaid collapse** (`shadowDev_eq_collapse_unpaid`):
   `shadowDev T f j = collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j))`.
   Mechanism: C.127's `shadowDev_of_ingrid` at the in-grid presentations `xNF F (composedKey T)`
   and `xNF F f` (C.131k′'s reduced digits), plus the new monic commutation `devQ_map` — the
   whole shadow division tower is the `AdjoinRoot.mk`-image of the two-variable tower.
2. **The paid census collapse, redeveloped at the composed key, is exactly the discrepancy**
   (`shadow_discrepancy` — the landed `Cnv13`):
   `shadowDev T f j - dev (composedKey T) f j = - dev (composedKey T) (censusOverflow T f) j`,
   where `censusOverflow T f` sums the paid census collapses against the powers of
   `composedKey T` — built from the tagged census ALONE.  Equivalently
   (`shadowDev_eq_dev_corrected`): the shadow read of `f` is the HONEST read of the
   census-corrected input `f - censusOverflow T f`, at EVERY coordinate `j`.

The proof is reconstruction + uniqueness at both keys: the new `devQ_reconstruct` (the public
reconstruction lemma v2 §2.7 F10 flagged as missing) presents `xNF F f` in the powers of
`xNF F (composedKey T)`; evaluation at `Y = F.key` — through C.131m′'s erasure theorem and
C.131k′'s `outerNF_reconstruct` — presents `f` as `Σ (unpaid_{j'} + paid_{j'})·Φ₂^{j'}`; the
unpaid collapses are reduced (`degree < deg Φ₂`), so B.06's `dev_unique` identifies them with
the honest digits of `f - censusOverflow T f`, and `dev`'s subtractivity peels off the honest
read of `f`.

`hπ : Irreducible π` is consumed only through C.47's `composedKey_natDegree`, exactly as in
C.73.  No `towerLocus` or `μ₂` hypothesis is needed: the identification is exact and
unconditional, the strongest form C.131w′ can consume (`Cnv14` adds the locus only to price
the paid terms via the census floor F11).

**DEPENDS.** C.131m′ (`taggedOuterNF`, `taggedOuterNF_erasure`, `eraseTagged`, `atOuter`,
`eraseTagged_append`, `eraseTagged_map_atOuter`) · C.131k′–l′ (`xNF`, `xNF_coeff`, `xNF_eval`,
`xNF_coeff_degree_lt`, `outerNF_reconstruct`, `xDigit_eq_dev`) · C.71 (`shadowDev`, `devQ`) ·
C.127 (`shadowDev_of_ingrid`, `reass`, `reass_eq_sum_range`, `devQ_add`, `devQ_of_zero`,
`devQ_eq_zero_of_lt`, `devQ_eq_dev`) · C.73 (`biRep`) · C.47 (`composedKey_monic`,
`composedKey_natDegree`) · C.44 (`towerLabel_spec`) · B.02–B.06 (`dev`, `dev_eq_zero_of_lt`,
`dev_unique`).

## Status

Sorry-free and axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131v

open Polynomial
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131k Uniformity.Density.Tower.C131m

/-! ## Part 0 — generic `devQ` complements (map commutation, degree, reconstruction, linearity) -/

section Generic

variable {R : Type*} [CommRing R] {Ψ : Polynomial R}

/-- Monic division commutes with any ring-map image, coordinatewise through the whole
division tower: the mapped `devQ`-digit is the `devQ`-digit of the mapped data. -/
theorem devQ_map {S : Type*} [CommRing S] (φ : R →+* S) (hΨ : Ψ.Monic) :
    ∀ (j : ℕ) (P : Polynomial R),
      (devQ Ψ P j).map φ = devQ (Ψ.map φ) (P.map φ) j := by
  intro j
  induction j with
  | zero => intro P; exact map_modByMonic φ hΨ
  | succ j ih =>
      intro P
      show (devQ Ψ (P /ₘ Ψ) j).map φ = devQ (Ψ.map φ) (P.map φ /ₘ Ψ.map φ) j
      rw [← map_divByMonic φ hΨ]
      exact ih (P /ₘ Ψ)

/-- Every `devQ`-digit is a remainder, hence has degree below the (monic) key. -/
theorem devQ_degree_lt [Nontrivial R] (hΨ : Ψ.Monic) :
    ∀ (j : ℕ) (P : Polynomial R), (devQ Ψ P j).degree < Ψ.degree := by
  intro j
  induction j with
  | zero => intro P; exact degree_modByMonic_lt P hΨ
  | succ j ih => intro P; exact ih (P /ₘ Ψ)

/-- **`devQ` reconstruction** (the public reconstruction lemma flagged missing at v2 §2.7 F10):
past the degree, the `devQ`-digits sum back to the dividend against the powers of the key. -/
theorem devQ_reconstruct [Nontrivial R] (hΨ : Ψ.Monic) :
    ∀ (n : ℕ) (P : Polynomial R), P.natDegree < n * Ψ.natDegree →
      ∑ j ∈ Finset.range n, devQ Ψ P j * Ψ ^ j = P := by
  intro n
  induction n with
  | zero =>
      intro P hP
      rw [zero_mul] at hP
      exact absurd hP (Nat.not_lt_zero _)
  | succ n ih =>
      intro P hP
      rw [Finset.sum_range_succ']
      have htail : ∀ i, devQ Ψ P (i + 1) * Ψ ^ (i + 1)
          = devQ Ψ (P /ₘ Ψ) i * Ψ ^ i * Ψ := by
        intro i
        rw [show devQ Ψ P (i + 1) = devQ Ψ (P /ₘ Ψ) i from rfl, pow_succ]
        ring
      have hhead : devQ Ψ P 0 * Ψ ^ 0 = P %ₘ Ψ := by
        rw [pow_zero, mul_one]; rfl
      rw [Finset.sum_congr rfl (fun i _ => htail i), ← Finset.sum_mul, hhead]
      by_cases hlt : P.degree < Ψ.degree
      · have hq0 : P /ₘ Ψ = 0 := (divByMonic_eq_zero_iff hΨ).2 hlt
        rw [hq0]
        simp only [devQ_of_zero, zero_mul, Finset.sum_const_zero, zero_add]
        exact (modByMonic_eq_self_iff hΨ).2 hlt
      · have hle : Ψ.natDegree ≤ P.natDegree :=
          natDegree_le_natDegree (not_lt.mp hlt)
        have hq : (P /ₘ Ψ).natDegree < n * Ψ.natDegree := by
          rw [natDegree_divByMonic P hΨ]
          rw [Nat.succ_mul] at hP
          omega
        rw [ih (P /ₘ Ψ) hq]
        linear_combination modByMonic_add_div P Ψ

/-- `devQ` of a negation is the negated digit. -/
theorem devQ_neg [Nontrivial R] (hΨ : Ψ.Monic) (B : Polynomial R) (j : ℕ) :
    devQ Ψ (-B) j = - devQ Ψ B j := by
  have h := devQ_add hΨ B (-B) j
  rw [add_neg_cancel, devQ_of_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- `devQ` of a difference is the difference of digits. -/
theorem devQ_sub [Nontrivial R] (hΨ : Ψ.Monic) (A B : Polynomial R) (j : ℕ) :
    devQ Ψ (A - B) j = devQ Ψ A j - devQ Ψ B j := by
  rw [sub_eq_add_neg, devQ_add hΨ, devQ_neg hΨ, sub_eq_add_neg]

end Generic

section GenericO

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- B.02's `dev` is subtractive in the dividend (via the generic `devQ` copy). -/
theorem dev_sub {φ : Polynomial O} (hφ : φ.Monic) (A B : Polynomial O) (j : ℕ) :
    dev φ (A - B) j = dev φ A j - dev φ B j := by
  simp only [← devQ_eq_dev]
  exact devQ_sub hφ A B j

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The quotient of a monic polynomial by a monic divisor of no larger degree is monic. -/
theorem monic_divByMonic {p q : Polynomial O} (hp : p.Monic) (hq : q.Monic)
    (h : q.degree ≤ p.degree) : (p /ₘ q).Monic :=
  show (p /ₘ q).leadingCoeff = 1 by
    rw [leadingCoeff_divByMonic_of_monic hq h]; exact hp

/-- **The leading digit of a monic polynomial of exactly full key-degree is `1`.** -/
theorem dev_top_eq_one {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    ∀ (m : ℕ) (A : Polynomial O), A.Monic → A.natDegree = m * φ.natDegree →
      dev φ A m = 1 := by
  intro m
  induction m with
  | zero =>
      intro A hA hdeg
      rw [zero_mul] at hdeg
      have hA1 : A = 1 := (hA.natDegree_eq_zero).mp hdeg
      subst hA1
      show (1 : Polynomial O) %ₘ φ = 1
      refine (modByMonic_eq_self_iff hφ).2 ?_
      rw [degree_one]
      exact natDegree_pos_iff_degree_pos.mp hd
  | succ m ih =>
      intro A hA hdeg
      show dev φ (A /ₘ φ) m = 1
      have hdle : φ.degree ≤ A.degree := by
        rw [degree_eq_natDegree hφ.ne_zero, degree_eq_natDegree hA.ne_zero, hdeg]
        exact_mod_cast Nat.le_mul_of_pos_left φ.natDegree (Nat.succ_pos m)
      refine ih (A /ₘ φ) (monic_divByMonic hA hφ hdle) ?_
      rw [natDegree_divByMonic A hφ, hdeg, Nat.succ_mul]
      omega

end GenericO

/-! ## Part 1 — the two-variable lift of a full-degree monic key is monic

`xNF F A` (C.131k′) of a monic `A` of degree `m·D′` is monic of `Y`-degree `m`: the depth-`m`
digit is `1` (`dev_top_eq_one`) and everything above vanishes (`dev_eq_zero_of_lt`).  Applied
below at `A = composedKey T`, `m = e₂f₂` (degree via C.47's `composedKey_natDegree`). -/

section XNFMonic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The two structural presentations coincide: C.131k′'s `xNF` IS C.73's `biRep`. -/
theorem xNF_eq_biRep (F : KeyFrame O π) (A : Polynomial O) : xNF F A = biRep F A := by
  rw [xNF, biRep]
  exact Finset.sum_congr rfl fun b _ => by rw [xDigit_eq_dev]

/-- The top coefficient of the two-variable lift of a full-degree monic polynomial is `1`. -/
theorem xNF_coeff_top (F : KeyFrame O π) {A : Polynomial O} (hA : A.Monic)
    {m : ℕ} (hdeg : A.natDegree = m * F.key.natDegree) :
    (xNF F A).coeff m = 1 := by
  rw [xNF_coeff, xDigit_eq_dev]
  exact dev_top_eq_one F.hmonic F.natDegree_key_pos m A hA hdeg

/-- Above the top coordinate the two-variable lift vanishes. -/
theorem xNF_coeff_eq_zero_of_top_lt (F : KeyFrame O π) {A : Polynomial O}
    {m : ℕ} (hdeg : A.natDegree = m * F.key.natDegree) {b : ℕ} (hb : m < b) :
    (xNF F A).coeff b = 0 := by
  rw [xNF_coeff, xDigit_eq_dev]
  refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos A b ?_
  rw [hdeg]
  exact mul_lt_mul_of_pos_right hb F.natDegree_key_pos

/-- The two-variable lift of a full-degree monic polynomial has `Y`-degree exactly `m`. -/
theorem xNF_natDegree (F : KeyFrame O π) {A : Polynomial O} (hA : A.Monic)
    {m : ℕ} (hdeg : A.natDegree = m * F.key.natDegree) :
    (xNF F A).natDegree = m := by
  refine le_antisymm ?_ ?_
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun N hN =>
      xNF_coeff_eq_zero_of_top_lt F hdeg hN
  · refine le_natDegree_of_ne_zero ?_
    rw [xNF_coeff_top F hA hdeg]
    exact one_ne_zero

/-- **The two-variable lift of a full-degree monic polynomial is monic.** -/
theorem xNF_monic (F : KeyFrame O π) {A : Polynomial O} (hA : A.Monic)
    {m : ℕ} (hdeg : A.natDegree = m * F.key.natDegree) :
    (xNF F A).Monic := by
  show (xNF F A).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, xNF_natDegree F hA hdeg, xNF_coeff_top F hA hdeg]

end XNFMonic

/-! ## Part 2 — the census split: unpaid and paid values

The tagged census (C.131m′) is split by its `paid` tag.  `unpaidValue` keeps exactly the
`paid = 0` contributions (the coefficients reduced mod `Φ′` — the REDUCED normal form of §3.8);
`paidValue` keeps the `paid ≥ 1` contributions (the priced overflow).  Erasure is their sum. -/

section CensusSplit

variable {R : Type*} [AddCommMonoid R]

/-- The value of the tag-zero (unpaid) part of a tagged census. -/
def unpaidValue (l : List (TaggedTerm R)) : R :=
  eraseTagged (l.filter fun t => t.paid == 0)

/-- The value of the tag-positive (paid) part of a tagged census. -/
def paidValue (l : List (TaggedTerm R)) : R :=
  eraseTagged (l.filter fun t => t.paid != 0)

/-- The census value splits exactly into its unpaid and paid parts. -/
theorem unpaidValue_add_paidValue (l : List (TaggedTerm R)) :
    unpaidValue l + paidValue l = eraseTagged l := by
  induction l with
  | nil => simp [unpaidValue, paidValue, eraseTagged]
  | cons t ts ih =>
      by_cases h : t.paid = 0
      · have h1 : (t :: ts).filter (fun t => t.paid == 0)
            = t :: ts.filter (fun t => t.paid == 0) := by
          simp [h]
        have h2 : (t :: ts).filter (fun t => t.paid != 0)
            = ts.filter (fun t => t.paid != 0) := by
          simp [h]
        simp only [unpaidValue, paidValue] at ih ⊢
        rw [h1, h2]
        show t.term + eraseTagged (ts.filter fun t => t.paid == 0)
            + eraseTagged (ts.filter fun t => t.paid != 0)
          = t.term + eraseTagged ts
        rw [add_assoc, ih]
      · have h1 : (t :: ts).filter (fun t => t.paid == 0)
            = ts.filter (fun t => t.paid == 0) := by
          simp [h]
        have h2 : (t :: ts).filter (fun t => t.paid != 0)
            = t :: ts.filter (fun t => t.paid != 0) := by
          simp [h]
        simp only [unpaidValue, paidValue] at ih ⊢
        rw [h1, h2]
        show eraseTagged (ts.filter fun t => t.paid == 0)
            + (t.term + eraseTagged (ts.filter fun t => t.paid != 0))
          = t.term + eraseTagged ts
        rw [add_left_comm, ih]

/-- `unpaidValue` distributes over appended censuses. -/
theorem unpaidValue_append (xs ys : List (TaggedTerm R)) :
    unpaidValue (xs ++ ys) = unpaidValue xs + unpaidValue ys := by
  simp only [unpaidValue, List.filter_append, eraseTagged_append]

end CensusSplit

section CensusTransport

variable {R : Type*} [Semiring R]

/-- Filtering on the zero tag commutes with the outer transport `atOuter` (which preserves
tags by construction). -/
theorem filter_zero_map_atOuter (b : ℕ) (xs : List (TaggedTerm (Polynomial R))) :
    (xs.map (atOuter b)).filter (fun t => t.paid == 0)
      = (xs.filter (fun t => t.paid == 0)).map (atOuter b) := by
  induction xs with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, List.filter_cons]
      have hpaid : (atOuter b t).paid = t.paid := rfl
      rw [hpaid]
      cases hp : (t.paid == 0) with
      | false => simpa [hp] using ih
      | true => simp [ih]

/-- The unpaid value of an outer-transported census is the transported unpaid value. -/
theorem unpaidValue_map_atOuter (b : ℕ) (xs : List (TaggedTerm (Polynomial R))) :
    unpaidValue (xs.map (atOuter b))
      = Polynomial.C (unpaidValue xs) * Polynomial.X ^ b := by
  simp only [unpaidValue]
  rw [filter_zero_map_atOuter, eraseTagged_map_atOuter]

end CensusTransport

/-! ## Part 3 — the unpaid value of the tagged outer census, computed

The `paid = 0` terms of `taggedXNFUpTo` are exactly the depth-`0` digits, so the unpaid value
of the census at coordinate `j` is the coefficientwise mod-`Φ′` reduction of the two-variable
digit `devQ K (xNF F A) j` — §3.8's "reduced normal form produced by the tagged structural
census", as a THEOREM about C.131m′'s recursion rather than a definition. -/

section CensusUnpaid

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The unpaid part of the inner tagged recursion is the single depth-`0` digit. -/
theorem unpaidValue_taggedXNFUpTo (F : KeyFrame O π) (A : Polynomial O) :
    ∀ n : ℕ, 1 ≤ n →
      unpaidValue (taggedXNFUpTo F A n) = Polynomial.C (A %ₘ F.key) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro _
      have hsucc : taggedXNFUpTo F A (n + 1)
          = taggedXNFUpTo F A n ++
            [⟨n, Polynomial.C (xDigit F.key A n) * Polynomial.X ^ n⟩] := rfl
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [hsucc, unpaidValue_append]
        have h0e : unpaidValue (taggedXNFUpTo F A 0)
            = (0 : Polynomial (Polynomial O)) := rfl
        have hsing : unpaidValue
            [(⟨0, Polynomial.C (xDigit F.key A 0) * Polynomial.X ^ 0⟩ :
              TaggedTerm (Polynomial (Polynomial O)))]
            = Polynomial.C (xDigit F.key A 0) * Polynomial.X ^ 0 + 0 := rfl
        rw [h0e, zero_add, hsing, add_zero, pow_zero, mul_one]
        rfl
      · rw [hsucc, unpaidValue_append, ih hpos]
        have hb : ((n : ℕ) == 0) = false := by
          simp [Nat.pos_iff_ne_zero.mp hpos]
        have hzero : unpaidValue
            [(⟨n, Polynomial.C (xDigit F.key A n) * Polynomial.X ^ n⟩ :
              TaggedTerm (Polynomial (Polynomial O)))] = 0 := by
          simp [unpaidValue, hb, eraseTagged]
        rw [hzero, add_zero]

/-- The unpaid part of the full inner tagged census is the mod-`Φ′` reduction. -/
theorem unpaidValue_taggedXNF (F : KeyFrame O π) (A : Polynomial O) :
    unpaidValue (taggedXNF F A) = Polynomial.C (A %ₘ F.key) :=
  unpaidValue_taggedXNFUpTo F A (A.natDegree + 1) (by omega)

/-- The unpaid part of the coefficientwise tagged census: one reduced digit per coordinate. -/
theorem unpaidValue_taggedCoeffwiseUpTo (F : KeyFrame O π)
    (S : Polynomial (Polynomial O)) :
    ∀ n : ℕ, unpaidValue (taggedCoeffwiseUpTo F S n)
      = ∑ b ∈ Finset.range n,
          Polynomial.C (Polynomial.C (S.coeff b %ₘ F.key)) * Polynomial.X ^ b := by
  intro n
  induction n with
  | zero => simp [taggedCoeffwiseUpTo, unpaidValue, eraseTagged]
  | succ n ih =>
      have hsucc : taggedCoeffwiseUpTo F S (n + 1)
          = taggedCoeffwiseUpTo F S n ++ (taggedXNF F (S.coeff n)).map (atOuter n) := rfl
      rw [hsucc, unpaidValue_append, ih, unpaidValue_map_atOuter, unpaidValue_taggedXNF,
        Finset.sum_range_succ]

/-- **The unpaid value of C.131m′'s tagged outer census**: the coefficientwise mod-`Φ′`
reduction of the two-variable digit at coordinate `j`. -/
theorem unpaidValue_taggedOuterNF (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    unpaidValue (taggedOuterNF F K A j)
      = ∑ b ∈ Finset.range ((devQ K (xNF F A) j).natDegree + 1),
          Polynomial.C (Polynomial.C ((devQ K (xNF F A) j).coeff b %ₘ F.key))
            * Polynomial.X ^ b :=
  unpaidValue_taggedCoeffwiseUpTo F (devQ K (xNF F A) j)
    ((devQ K (xNF F A) j).natDegree + 1)

end CensusUnpaid

/-! ## Part 4 — the collapse: evaluating the census back at `Y = F.key` -/

section Collapse

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The two-step evaluation at `Y = F.key`: first the inner reduced variable, then the outer
coordinate variable.  A ring hom, so it distributes over the census split. -/
noncomputable def collapse (F : KeyFrame O π) :
    Polynomial (Polynomial (Polynomial O)) →+* Polynomial O :=
  (Polynomial.evalRingHom F.key).comp (Polynomial.mapRingHom (Polynomial.evalRingHom F.key))

theorem collapse_apply (F : KeyFrame O π) (P : Polynomial (Polynomial (Polynomial O))) :
    collapse F P = Polynomial.eval F.key (P.map (Polynomial.evalRingHom F.key)) := rfl

/-- **Collapse of the erased census** (C.131m′'s erasure theorem + C.131l′'s reconstruction):
the full census value at coordinate `j` collapses to the evaluated two-variable digit. -/
theorem collapse_eraseTagged (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    collapse F (eraseTagged (taggedOuterNF F K A j))
      = Polynomial.eval F.key (devQ K (xNF F A) j) := by
  rw [taggedOuterNF_erasure, collapse_apply, outerNF_reconstruct]

/-- **Collapse of the unpaid census**: the reduced reassembly of the two-variable digit. -/
theorem collapse_unpaidValue (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    collapse F (unpaidValue (taggedOuterNF F K A j))
      = ∑ b ∈ Finset.range ((devQ K (xNF F A) j).natDegree + 1),
          ((devQ K (xNF F A) j).coeff b %ₘ F.key) * F.key ^ b := by
  rw [unpaidValue_taggedOuterNF, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_pow]
  simp only [collapse, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_C, Polynomial.map_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X]

/-- The unpaid and paid collapses reassemble the evaluated two-variable digit. -/
theorem collapse_unpaid_add_paid (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    collapse F (unpaidValue (taggedOuterNF F K A j))
      + collapse F (paidValue (taggedOuterNF F K A j))
      = Polynomial.eval F.key (devQ K (xNF F A) j) := by
  rw [← map_add, unpaidValue_add_paidValue, collapse_eraseTagged]

end Collapse

/-! ## Part 5 — the shadow read IS the unpaid census collapse -/

section ShadowTie

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-- Reassembly of a transported two-variable polynomial: the coefficientwise remainders
against the powers of `Φ′`. -/
theorem reass_map (F : KeyFrame O π) (N : Polynomial (Polynomial O)) :
    reass F (N.map (AdjoinRoot.mk F.key))
      = ∑ b ∈ Finset.range (N.natDegree + 1), (N.coeff b %ₘ F.key) * F.key ^ b := by
  rw [reass_eq_sum_range F _ (lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coeff_map, AdjoinRoot.modByMonicHom_mk]

/-- The shadow read through the in-grid `xNF` presentations (C.127's transfer, restated at the
two-variable lift the census actually uses). -/
theorem shadowDev_eq_reass_devQ (T : TowerDatum F H₀ hpin) (f : Polynomial O) (j : ℕ) :
    shadowDev T f j
      = reass F (devQ ((xNF F (composedKey T)).map (AdjoinRoot.mk F.key))
          ((xNF F f).map (AdjoinRoot.mk F.key)) j) :=
  shadowDev_of_ingrid T (xNF_coeff_degree_lt F (composedKey T)) (xNF_coeff_degree_lt F f)
    (xNF_eval F (composedKey T)) (xNF_eval F f) j

/-- The composed key's degree in the frame's units (C.73's bookkeeping, factored out). -/
theorem composedKey_natDegree_mul (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (composedKey T).natDegree = (T.e₂ * T.f₂) * F.key.natDegree := by
  have hd : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
  have hl : (T.levelDatum hπ).ℓ = T.e₂ := rfl
  rw [composedKey_natDegree T hπ, LevelDatum.keyDeg₂, hd, hl, F.hdeg]
  ring

/-- **The shadow read IS the census's unpaid collapse** — the first half of the semantic
identification: `shadowDev T f j` is the value of the `paid = 0` stratum of C.131m′'s tagged
census at the composed key's two-variable lift.  Non-circular: the right-hand side is built
from the tagged census alone. -/
theorem shadowDev_eq_collapse_unpaid (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (f : Polynomial O) (j : ℕ) :
    shadowDev T f j
      = collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j)) := by
  have h𝕂monic : (xNF F (composedKey T)).Monic :=
    xNF_monic F (composedKey_monic T) (composedKey_natDegree_mul T hπ)
  rw [shadowDev_eq_reass_devQ T f j,
    ← devQ_map (AdjoinRoot.mk F.key) h𝕂monic j (xNF F f), reass_map,
    collapse_unpaidValue]

end ShadowTie

/-! ## Part 6 — the census overflow and the discrepancy identification (v2 `Cnv13`) -/

section Capstone

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-- **The census overflow**: the paid (tag `≥ 1`) census values, collapsed at `Y = F.key` and
summed against the powers of the composed key.  Built from the tagged census ALONE — no
`shadowDev`, no honest read, no difference — so the identification below is non-circular. -/
noncomputable def censusOverflow (T : TowerDatum F H₀ hpin) (f : Polynomial O) :
    Polynomial O :=
  ∑ j' ∈ Finset.range ((xNF F f).natDegree + 1),
    collapse F (paidValue (taggedOuterNF F (xNF F (composedKey T)) f j'))
      * composedKey T ^ j'

/-- The unpaid collapse is reduced below the composed key's degree (every summand carries at
most `(D′ − 1) + b·D′ ≤ m·D′ − 1` of degree). -/
theorem collapse_unpaidValue_degree_lt (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (f : Polynomial O) (j : ℕ) :
    (collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j))).degree
      < (composedKey T).degree := by
  have hD : 0 < F.key.natDegree := F.natDegree_key_pos
  have hm : 0 < T.e₂ * T.f₂ := by have := T.hcomp; omega
  have hΦdeg := composedKey_natDegree_mul T hπ
  have h𝕂monic : (xNF F (composedKey T)).Monic :=
    xNF_monic F (composedKey_monic T) hΦdeg
  have h𝕂deg : (xNF F (composedKey T)).natDegree = T.e₂ * T.f₂ :=
    xNF_natDegree F (composedKey_monic T) hΦdeg
  set N := devQ (xNF F (composedKey T)) (xNF F f) j with hN
  have hNlt : N.natDegree < T.e₂ * T.f₂ := by
    by_cases h0 : N = 0
    · rw [h0, natDegree_zero]; exact hm
    · have hdlt := devQ_degree_lt h𝕂monic j (xNF F f)
      rw [← hN] at hdlt
      have := natDegree_lt_natDegree h0 hdlt
      omega
  rw [collapse_unpaidValue, ← hN]
  refine degree_lt_degree ?_
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun b hb => ?_)
    (show (T.e₂ * T.f₂) * F.key.natDegree - 1 < (composedKey T).natDegree by
      rw [hΦdeg]
      have hpos : 0 < (T.e₂ * T.f₂) * F.key.natDegree := Nat.mul_pos hm hD
      omega)
  have hb' : b ≤ N.natDegree := by
    rw [Finset.mem_range] at hb; omega
  have h1 : (N.coeff b %ₘ F.key).natDegree ≤ F.key.natDegree - 1 := by
    by_cases h0 : N.coeff b %ₘ F.key = 0
    · rw [h0, natDegree_zero]; omega
    · have hlt := degree_modByMonic_lt (N.coeff b) F.hmonic
      have := natDegree_lt_natDegree h0 hlt
      omega
  have h2 : b * F.key.natDegree ≤ (T.e₂ * T.f₂ - 1) * F.key.natDegree :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (T.e₂ * T.f₂ - 1) * F.key.natDegree
      = (T.e₂ * T.f₂) * F.key.natDegree - F.key.natDegree := Nat.sub_one_mul _ _
  have h4 : F.key.natDegree ≤ (T.e₂ * T.f₂) * F.key.natDegree :=
    Nat.le_mul_of_pos_left _ hm
  calc ((N.coeff b %ₘ F.key) * F.key ^ b).natDegree
      ≤ (N.coeff b %ₘ F.key).natDegree + (F.key ^ b).natDegree := natDegree_mul_le
    _ ≤ (F.key.natDegree - 1) + b * F.key.natDegree :=
        Nat.add_le_add h1 natDegree_pow_le
    _ ≤ (T.e₂ * T.f₂) * F.key.natDegree - 1 := by omega

/-- **The semantic identification, corrected-input form**: the shadow read of `f` is the
HONEST read of the census-corrected input `f - censusOverflow T f`, at every coordinate. -/
theorem shadowDev_eq_dev_corrected (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (f : Polynomial O) (j : ℕ) :
    shadowDev T f j = dev (composedKey T) (f - censusOverflow T f) j := by
  classical
  have hD : 0 < F.key.natDegree := F.natDegree_key_pos
  have hm : 0 < T.e₂ * T.f₂ := by have := T.hcomp; omega
  have hΦmonic : (composedKey T).Monic := composedKey_monic T
  have hΦdeg := composedKey_natDegree_mul T hπ
  have hΦpos : 0 < (composedKey T).natDegree := by
    rw [hΦdeg]; exact Nat.mul_pos hm hD
  have h𝕂monic : (xNF F (composedKey T)).Monic := xNF_monic F hΦmonic hΦdeg
  have h𝕂pos : 0 < (xNF F (composedKey T)).natDegree := by
    rw [xNF_natDegree F hΦmonic hΦdeg]; exact hm
  set n₀ : ℕ := (xNF F f).natDegree + 1 with hn₀
  set n : ℕ := max n₀ (j + 1) with hn
  have hn₀n : n₀ ≤ n := le_max_left _ _
  -- two-variable reconstruction of the dividend
  have hrec : ∑ j' ∈ Finset.range n,
      devQ (xNF F (composedKey T)) (xNF F f) j' * (xNF F (composedKey T)) ^ j'
        = xNF F f := by
    refine devQ_reconstruct h𝕂monic n (xNF F f) ?_
    have h1 : (xNF F f).natDegree < n := by omega
    calc (xNF F f).natDegree < n := h1
      _ = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (xNF F (composedKey T)).natDegree := Nat.mul_le_mul_left n h𝕂pos
  -- evaluated at `Y = F.key`
  have hevalrec : ∑ j' ∈ Finset.range n,
      Polynomial.eval F.key (devQ (xNF F (composedKey T)) (xNF F f) j')
        * composedKey T ^ j' = f := by
    have h := congrArg (Polynomial.eval F.key) hrec
    rw [eval_finsetSum, xNF_eval F f] at h
    calc ∑ j' ∈ Finset.range n,
        Polynomial.eval F.key (devQ (xNF F (composedKey T)) (xNF F f) j')
          * composedKey T ^ j'
        = ∑ j' ∈ Finset.range n, Polynomial.eval F.key
            (devQ (xNF F (composedKey T)) (xNF F f) j' * (xNF F (composedKey T)) ^ j') := by
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [eval_mul, eval_pow, xNF_eval F (composedKey T)]
      _ = f := h
  -- the paid terms vanish past the dividend degree
  have hpaidzero : ∀ j' ∈ Finset.range n, j' ∉ Finset.range n₀ →
      collapse F (paidValue (taggedOuterNF F (xNF F (composedKey T)) f j'))
        * composedKey T ^ j' = 0 := by
    intro j' _ hj'
    have hj0 : n₀ ≤ j' := by
      rw [Finset.mem_range, not_lt] at hj'; exact hj'
    have hN0 : devQ (xNF F (composedKey T)) (xNF F f) j' = 0 := by
      refine devQ_eq_zero_of_lt h𝕂monic (xNF F f) j' ?_
      calc (xNF F f).natDegree < n₀ := by omega
        _ ≤ j' := hj0
        _ = j' * 1 := (Nat.mul_one j').symm
        _ ≤ j' * (xNF F (composedKey T)).natDegree := Nat.mul_le_mul_left j' h𝕂pos
    have hu : collapse F
        (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j')) = 0 := by
      rw [collapse_unpaidValue, hN0]
      simp [zero_modByMonic]
    have h := collapse_unpaid_add_paid F (xNF F (composedKey T)) f j'
    rw [hN0, eval_zero, hu, zero_add] at h
    rw [h, zero_mul]
  -- the overflow sum extends from range n₀ to range n by zeros
  have hg : censusOverflow T f
      = ∑ j' ∈ Finset.range n,
          collapse F (paidValue (taggedOuterNF F (xNF F (composedKey T)) f j'))
            * composedKey T ^ j' := by
    rw [censusOverflow, ← hn₀]
    exact Finset.sum_subset (Finset.range_subset_range.mpr hn₀n) hpaidzero
  -- the reduced presentation of the corrected input
  have hpres : ∑ j' ∈ Finset.range n,
      collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j'))
        * composedKey T ^ j' = f - censusOverflow T f := by
    rw [hg]
    have hsplitsum : ∑ j' ∈ Finset.range n,
        collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j'))
          * composedKey T ^ j'
        = ∑ j' ∈ Finset.range n,
            (Polynomial.eval F.key (devQ (xNF F (composedKey T)) (xNF F f) j')
                * composedKey T ^ j'
              - collapse F (paidValue (taggedOuterNF F (xNF F (composedKey T)) f j'))
                * composedKey T ^ j') := by
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← collapse_unpaid_add_paid F (xNF F (composedKey T)) f j']
      ring
    rw [hsplitsum, Finset.sum_sub_distrib, hevalrec]
  -- uniqueness of the reduced development at the composed key
  have huniq : ∀ j' < n,
      collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j'))
        = dev (composedKey T) (f - censusOverflow T f) j' :=
    dev_unique hΦmonic hΦpos
      (fun j' => collapse_unpaidValue_degree_lt T hπ f j') hpres
  have hj : j < n := by omega
  calc shadowDev T f j
      = collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j)) :=
        shadowDev_eq_collapse_unpaid T hπ f j
    _ = dev (composedKey T) (f - censusOverflow T f) j := huniq j hj

/-- ★ **NODE C.131v′ — the shadow-discrepancy semantic identification (v2 §3.8 `Cnv13`).**
The displayed difference of C.71's two reads IS the (negated) erased tagged discrepancy: the
paid census values, collapsed at `Y = F.key`, summed against the composed key's powers
(`censusOverflow`, built from the tagged census alone), and redeveloped at the composed key. -/
theorem shadow_discrepancy (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (f : Polynomial O) (j : ℕ) :
    shadowDev T f j - dev (composedKey T) f j
      = - dev (composedKey T) (censusOverflow T f) j := by
  rw [shadowDev_eq_dev_corrected T hπ f j, dev_sub (composedKey_monic T)]
  ring

/-- The positively-signed companion: honest minus shadow is the redeveloped census overflow. -/
theorem dev_sub_shadowDev (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (f : Polynomial O) (j : ℕ) :
    dev (composedKey T) f j - shadowDev T f j
      = dev (composedKey T) (censusOverflow T f) j := by
  rw [shadowDev_eq_dev_corrected T hπ f j, dev_sub (composedKey_monic T)]
  ring

end Capstone

end Uniformity.Density.Tower.C131v

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131v.devQ_map
#print axioms Uniformity.Density.Tower.C131v.devQ_degree_lt
#print axioms Uniformity.Density.Tower.C131v.devQ_reconstruct
#print axioms Uniformity.Density.Tower.C131v.devQ_neg
#print axioms Uniformity.Density.Tower.C131v.devQ_sub
#print axioms Uniformity.Density.Tower.C131v.dev_sub
#print axioms Uniformity.Density.Tower.C131v.monic_divByMonic
#print axioms Uniformity.Density.Tower.C131v.dev_top_eq_one
#print axioms Uniformity.Density.Tower.C131v.xNF_eq_biRep
#print axioms Uniformity.Density.Tower.C131v.xNF_coeff_top
#print axioms Uniformity.Density.Tower.C131v.xNF_coeff_eq_zero_of_top_lt
#print axioms Uniformity.Density.Tower.C131v.xNF_natDegree
#print axioms Uniformity.Density.Tower.C131v.xNF_monic
#print axioms Uniformity.Density.Tower.C131v.unpaidValue
#print axioms Uniformity.Density.Tower.C131v.paidValue
#print axioms Uniformity.Density.Tower.C131v.unpaidValue_add_paidValue
#print axioms Uniformity.Density.Tower.C131v.unpaidValue_append
#print axioms Uniformity.Density.Tower.C131v.filter_zero_map_atOuter
#print axioms Uniformity.Density.Tower.C131v.unpaidValue_map_atOuter
#print axioms Uniformity.Density.Tower.C131v.unpaidValue_taggedXNFUpTo
#print axioms Uniformity.Density.Tower.C131v.unpaidValue_taggedXNF
#print axioms Uniformity.Density.Tower.C131v.unpaidValue_taggedCoeffwiseUpTo
#print axioms Uniformity.Density.Tower.C131v.unpaidValue_taggedOuterNF
#print axioms Uniformity.Density.Tower.C131v.collapse
#print axioms Uniformity.Density.Tower.C131v.collapse_apply
#print axioms Uniformity.Density.Tower.C131v.collapse_eraseTagged
#print axioms Uniformity.Density.Tower.C131v.collapse_unpaidValue
#print axioms Uniformity.Density.Tower.C131v.collapse_unpaid_add_paid
#print axioms Uniformity.Density.Tower.C131v.reass_map
#print axioms Uniformity.Density.Tower.C131v.shadowDev_eq_reass_devQ
#print axioms Uniformity.Density.Tower.C131v.composedKey_natDegree_mul
#print axioms Uniformity.Density.Tower.C131v.shadowDev_eq_collapse_unpaid
#print axioms Uniformity.Density.Tower.C131v.censusOverflow
#print axioms Uniformity.Density.Tower.C131v.collapse_unpaidValue_degree_lt
#print axioms Uniformity.Density.Tower.C131v.shadowDev_eq_dev_corrected
#print axioms Uniformity.Density.Tower.C131v.shadow_discrepancy
#print axioms Uniformity.Density.Tower.C131v.dev_sub_shadowDev

end AxCheck
