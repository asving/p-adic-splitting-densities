/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.HenselFactorization — Hensel's lemma in FACTORIZATION form

**What this file proves.** Over a commutative local ring `R` that is complete for its maximal
ideal `𝔪`, a *coprime* monic factorization of the residue reduction of a monic polynomial lifts
to a factorization over `R`:

    f monic, f mod 𝔪 = g₀ * h₀ with g₀, h₀ monic and coprime
      ⟹  ∃ g h monic over R with f = g * h, g mod 𝔪 = g₀, h mod 𝔪 = h₀

(`exists_monic_factorization`), the lifted pair is unique (`monic_factorization_unique`), the
lifted factors are *Bézout*-coprime in `R[X]` (`isCoprime_of_map_eq`), and the underlying
interpolation problem `w = h * u + g * v` with `deg u < deg g`, `deg v < deg h` is exactly
solvable (`exists_eq_add_mul_of_degree_lt`).

No discreteness, no finiteness of the residue field, no domain hypothesis, no restriction on the
residue characteristic: the base is any `[CommRing R] [IsLocalRing R] [IsAdicComplete 𝔪 R]`.

## Provenance (checked 2026-08-13)

This is **not** in Mathlib. Pinned mathlib v4.31 and mathlib master both carry only the ROOT form
of Hensel's lemma (`HenselianRing`, `HenselianLocalRing`, `HenselianLocalRing.TFAE`,
`IsAdicComplete.henselianRing` in `Mathlib/RingTheory/Henselian.lean`; `hensels_lemma` in
`Mathlib/NumberTheory/Padics/Hensel.lean`). `Mathlib/RingTheory/Henselian.lean`'s own `## TODO`
block records the factorization form as an open goal. The closest existing results are
`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`
(`Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean`, `@[stacks 00UH]`), which lifts
only to an étale algebra, and `HenselianLocalRing.exists_lift_of_to_ResidueField` in the FLT
project (`FLT/HenselianLocalRing/Finite.lean`), which supplies the missing section but is written
against mathlib master and depends on FLT-internal étale-decomposition files. Backporting either
was *judged* (a development-time judgement call, not a checked fact) to cost more than proving the
result directly, so the classical Newton/successive-approximation proof is given here. Full audit,
including the evidence behind the absence check:
`leanfinal/notes/HENSEL_FACT_2026-08-13.md`.

## Method

`coeffIdeal J = Ideal.map C J` is the ideal of `R[X]` of polynomials with all coefficients in `J`.
The proof is a Newton iteration on the `𝔪`-adic filtration whose correction step
(`exists_solve_step`) comes from the residue-field Bézout identity (`exists_solve_field`) by
*linearity in the coefficients of the error*: solve for each monomial `X ^ i` with `i < n`, then
take the `R`-linear combination. That replaces the textbook step "write the error as `π ^ j`
times something", which needs `𝔪` principal; the argument here works for a non-discrete `𝔪`.

## Status

Zero `sorry`; no axiom is declared here and every theorem's `#print axioms` footprint is the Lean
core triple `propext, Classical.choice, Quot.sound`.  Every statement in this file is new and is
flagged for human review in §4 of the unit note.
-/

set_option linter.style.longLine false

namespace Uniformity

namespace Hensel

open Polynomial IsLocalRing

/-! ## 1. `coeffIdeal` — polynomials with all coefficients in a given ideal -/

section CoeffIdeal

variable {R : Type*} [CommRing R]

/-- **`coeffIdeal J`** — the ideal of `R[X]` consisting of the polynomials all of whose
coefficients lie in `J`.  Defined as `Ideal.map C J`; the coefficient description is
`mem_coeffIdeal`. Being an *ideal* is what makes the bookkeeping cheap: it is automatically closed
under multiplication by arbitrary polynomials. -/
noncomputable abbrev coeffIdeal (J : Ideal R) : Ideal (Polynomial R) := J.map (Polynomial.C (R := R))

theorem mem_coeffIdeal {J : Ideal R} {p : Polynomial R} :
    p ∈ coeffIdeal J ↔ ∀ i, p.coeff i ∈ J :=
  Ideal.mem_map_C_iff

theorem coeffIdeal_mono {J J' : Ideal R} (h : J ≤ J') : coeffIdeal J ≤ coeffIdeal J' := by
  intro p hp
  rw [mem_coeffIdeal] at hp ⊢
  exact fun i => h (hp i)

theorem C_mem_coeffIdeal {J : Ideal R} {a : R} (ha : a ∈ J) : Polynomial.C a ∈ coeffIdeal J :=
  Ideal.mem_map_of_mem _ ha

/-- The multiplicativity of the filtration: `coeffIdeal J * coeffIdeal J' ⊆ coeffIdeal (J * J')`
(in fact `Ideal.map_mul` makes it an equality). -/
theorem mul_mem_coeffIdeal_mul {J J' : Ideal R} {p q : Polynomial R}
    (hp : p ∈ coeffIdeal J) (hq : q ∈ coeffIdeal J') : p * q ∈ coeffIdeal (J * J') := by
  rw [coeffIdeal, Ideal.map_mul]
  exact Ideal.mul_mem_mul hp hq

/-- Membership in `coeffIdeal J` is exactly vanishing of the reduction mod `J`. -/
theorem map_mk_eq_zero_iff {J : Ideal R} {p : Polynomial R} :
    p.map (Ideal.Quotient.mk J) = 0 ↔ p ∈ coeffIdeal J := by
  rw [mem_coeffIdeal, Polynomial.ext_iff]
  simp [coeff_map, Ideal.Quotient.eq_zero_iff_mem]

end CoeffIdeal

section CoeffIdealLocal

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem map_residue_eq_zero_iff {p : Polynomial R} :
    p.map (residue R) = 0 ↔ p ∈ coeffIdeal (maximalIdeal R) :=
  map_mk_eq_zero_iff

/-- Two polynomials have the same residue reduction iff their difference has all coefficients in
`𝔪`. -/
theorem sub_mem_coeffIdeal_maximalIdeal_iff {p q : Polynomial R} :
    p - q ∈ coeffIdeal (maximalIdeal R) ↔ p.map (residue R) = q.map (residue R) := by
  rw [← map_residue_eq_zero_iff, Polynomial.map_sub, sub_eq_zero]

end CoeffIdealLocal

/-! ## 2. The residue-field solve

Over a field, a coprime monic pair `(g₀, h₀)` of degrees `m, l` lets one write every polynomial of
degree `< m + l` as `h₀ * u + g₀ * v` with `deg u < m` and `deg v < l`. Note the pairing: the
low-degree factor `u` sits against `h₀`. That is the pairing the Newton correction needs, since
`(g + δg) * (h + δh) = g * h + h * δg + g * δh + δg * δh`. -/

section ResidueSolve

variable {k : Type*} [Field k]

theorem exists_solve_field {g₀ h₀ : Polynomial k} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) {w : Polynomial k}
    (hw : w.degree < (g₀.natDegree + h₀.natDegree : ℕ)) :
    ∃ u v : Polynomial k, u.degree < (g₀.natDegree : ℕ) ∧ v.degree < (h₀.natDegree : ℕ) ∧
      w = h₀ * u + g₀ * v := by
  obtain ⟨a, b, hab⟩ := hcop
  have hg₀deg : g₀.degree = (g₀.natDegree : WithBot ℕ) := degree_eq_natDegree hg₀.ne_zero
  have hh₀deg : h₀.degree = (h₀.natDegree : WithBot ℕ) := degree_eq_natDegree hh₀.ne_zero
  set u : Polynomial k := (b * w) %ₘ g₀ with hu_def
  set v : Polynomial k := a * w + h₀ * ((b * w) /ₘ g₀) with hv_def
  have hu : u.degree < (g₀.natDegree : WithBot ℕ) := by
    rw [hu_def, ← hg₀deg]; exact degree_modByMonic_lt (b * w) hg₀
  have key : w = h₀ * u + g₀ * v := by
    have hdiv : u + g₀ * ((b * w) /ₘ g₀) = b * w := modByMonic_add_div (b * w) g₀
    have expand : h₀ * u + g₀ * v = h₀ * (u + g₀ * ((b * w) /ₘ g₀)) + a * g₀ * w := by
      rw [hv_def]; ring
    rw [expand, hdiv]
    calc w = (a * g₀ + b * h₀) * w := by rw [hab, one_mul]
    _ = h₀ * (b * w) + a * g₀ * w := by ring
  refine ⟨u, v, hu, ?_, key⟩
  -- the degree bound on `v` is forced by monicity of `g₀`, not chosen
  have h1 : (g₀ * v).degree = (g₀.natDegree : WithBot ℕ) + v.degree := by
    rw [degree_mul, hg₀deg]
  have h2 : (h₀ * u).degree < (g₀.natDegree : WithBot ℕ) + (h₀.natDegree : WithBot ℕ) := by
    rw [degree_mul, hh₀deg, add_comm ((g₀.natDegree : WithBot ℕ))]
    exact WithBot.add_lt_add_left (by simp) hu
  have h3 : (g₀ * v).degree < (g₀.natDegree : WithBot ℕ) + (h₀.natDegree : WithBot ℕ) := by
    have hgv : g₀ * v = w - h₀ * u := by rw [key]; ring
    rw [hgv]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ h2)
    simpa [Nat.cast_add] using hw
  rw [h1] at h3
  exact (WithBot.add_lt_add_iff_left (by simp)).mp h3

end ResidueSolve

/-! ## 3. Truncated expansions -/

section Truncation

variable {R : Type*} [CommRing R]

theorem coeff_sum_range_C_mul_X_pow (c : ℕ → R) (d j : ℕ) :
    (∑ i ∈ Finset.range d, Polynomial.C (c i) * X ^ i).coeff j = if j < d then c j else 0 := by
  classical
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range d) j c]
  simp [Finset.mem_range]

theorem degree_C_mul_le_degree (a : R) (p : Polynomial R) :
    (Polynomial.C a * p).degree ≤ p.degree := by
  rw [← smul_eq_C_mul]
  exact degree_smul_le a p

/-- Expanding a linear combination of solved monomials. -/
theorem sum_C_mul_solve_expand (c : ℕ → R) (A B : ℕ → Polynomial R) (g h : Polynomial R) (d : ℕ) :
    ∑ i ∈ Finset.range d, Polynomial.C (c i) * ((X : Polynomial R) ^ i - (h * A i + g * B i))
      = (∑ i ∈ Finset.range d, Polynomial.C (c i) * X ^ i)
        - (h * (∑ i ∈ Finset.range d, Polynomial.C (c i) * A i)
          + g * (∑ i ∈ Finset.range d, Polynomial.C (c i) * B i)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A polynomial of degree `< d` is its own truncated expansion in degrees `< d`. -/
theorem eq_sum_range_of_degree_lt {p : Polynomial R} {d : ℕ} (hp : p.degree < (d : WithBot ℕ)) :
    p = ∑ i ∈ Finset.range d, Polynomial.C (p.coeff i) * X ^ i := by
  ext j
  rw [coeff_sum_range_C_mul_X_pow]
  by_cases hj : j < d
  · rw [if_pos hj]
  · rw [if_neg hj]
    exact coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hp (by exact_mod_cast Nat.le_of_not_lt hj))

theorem degree_sum_range_C_mul_X_pow_lt (c : ℕ → R) (d : ℕ) :
    (∑ i ∈ Finset.range d, Polynomial.C (c i) * X ^ i).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < (d : WithBot ℕ))]
  intro i hi
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le i (c i)) (by exact_mod_cast Finset.mem_range.mp hi)

end Truncation

/-! ## 4. Solving the interpolation problem modulo `𝔪`, and one filtration step

`exists_solve_mod` is the residue-field solve transported to `R` by a degree-preserving lift.
`exists_solve_step` upgrades it from "solve mod `𝔪`" to "solve an error in `𝔪 ^ j` up to
`𝔪 ^ (j+1)`, with corrections again in `𝔪 ^ j`" — the Newton step. Its proof is *linearity in the
coefficients of the error*: solve once for each monomial `X ^ i` with `i < n`, then take the
`R`-linear combination with the coefficients of the error. This is what makes the argument work
for a non-principal `𝔪`, where one cannot write the error as `π ^ j` times something. -/

section SolveMod

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem exists_solve_mod {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    {w : Polynomial R} (hw : w.degree < (g₀.natDegree + h₀.natDegree : ℕ)) :
    ∃ u v : Polynomial R, u.degree < (g₀.natDegree : ℕ) ∧ v.degree < (h₀.natDegree : ℕ) ∧
      w - (h * u + g * v) ∈ coeffIdeal (maximalIdeal R) := by
  have hwmap : (w.map (residue R)).degree < (g₀.natDegree + h₀.natDegree : ℕ) :=
    lt_of_le_of_lt (degree_map_le) hw
  obtain ⟨u₀, v₀, hu₀, hv₀, hkey⟩ := exists_solve_field hg₀ hh₀ hcop hwmap
  obtain ⟨u, humap, hudeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) u₀)
  obtain ⟨v, hvmap, hvdeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) v₀)
  refine ⟨u, v, hudeg ▸ hu₀, hvdeg ▸ hv₀, ?_⟩
  rw [← map_residue_eq_zero_iff, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_mul, hgr, hhr, humap, hvmap, sub_eq_zero]
  exact hkey

theorem exists_solve_step {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    (j : ℕ) {e : Polynomial R} (he : e ∈ coeffIdeal (maximalIdeal R ^ j))
    (hdeg : e.degree < (g₀.natDegree + h₀.natDegree : ℕ)) :
    ∃ u v : Polynomial R, u.degree < (g₀.natDegree : ℕ) ∧ v.degree < (h₀.natDegree : ℕ) ∧
      u ∈ coeffIdeal (maximalIdeal R ^ j) ∧ v ∈ coeffIdeal (maximalIdeal R ^ j) ∧
      e - (h * u + g * v) ∈ coeffIdeal (maximalIdeal R ^ (j + 1)) := by
  classical
  set m := g₀.natDegree with hm
  set l := h₀.natDegree with hl
  have key : ∀ i : ℕ, ∃ uv : Polynomial R × Polynomial R,
      uv.1.degree < (m : WithBot ℕ) ∧ uv.2.degree < (l : WithBot ℕ) ∧
      (i < m + l → (X : Polynomial R) ^ i - (h * uv.1 + g * uv.2)
        ∈ coeffIdeal (maximalIdeal R)) := by
    intro i
    by_cases hi : i < m + l
    · obtain ⟨u, v, h1, h2, h3⟩ := exists_solve_mod hg₀ hh₀ hcop hgr hhr
        (w := (X : Polynomial R) ^ i) (by rw [degree_X_pow]; exact_mod_cast hi)
      exact ⟨(u, v), h1, h2, fun _ => h3⟩
    · exact ⟨(0, 0), by simp, by simp, fun hc => absurd hc hi⟩
  choose UV hU hV hr using key
  set u : Polynomial R := ∑ i ∈ Finset.range (m + l), Polynomial.C (e.coeff i) * (UV i).1 with hu
  set v : Polynomial R := ∑ i ∈ Finset.range (m + l), Polynomial.C (e.coeff i) * (UV i).2 with hv
  have hudeg : u.degree < (m : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < (m : WithBot ℕ))]
    exact fun i _ => lt_of_le_of_lt (degree_C_mul_le_degree _ _) (hU i)
  have hvdeg : v.degree < (l : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < (l : WithBot ℕ))]
    exact fun i _ => lt_of_le_of_lt (degree_C_mul_le_degree _ _) (hV i)
  refine ⟨u, v, hudeg, hvdeg, ?_, ?_, ?_⟩
  · exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_right _ _ (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
  · exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_right _ _ (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
  · have hexp : e - (h * u + g * v)
        = ∑ i ∈ Finset.range (m + l), Polynomial.C (e.coeff i) *
            ((X : Polynomial R) ^ i - (h * (UV i).1 + g * (UV i).2)) := by
      rw [sum_C_mul_solve_expand (fun i => e.coeff i) (fun i => (UV i).1) (fun i => (UV i).2)
        g h (m + l), hu, hv]
      congr 1
      exact eq_sum_range_of_degree_lt hdeg
    rw [hexp]
    refine Ideal.sum_mem _ fun i hi => ?_
    have := mul_mem_coeffIdeal_mul (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
      (hr i (Finset.mem_range.mp hi))
    rwa [← pow_succ] at this

end SolveMod

/-! ## 5. The adic limit of a degree-bounded Cauchy sequence of polynomials -/

section Limit

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

theorem exists_adicLimit_of_degree_lt (d : ℕ) (p : ℕ → Polynomial R)
    (hdeg : ∀ k, (p k).degree < (d : WithBot ℕ))
    (hstep : ∀ k, p (k + 1) - p k ∈ coeffIdeal (maximalIdeal R ^ k)) :
    ∃ P : Polynomial R, P.degree < (d : WithBot ℕ) ∧
      ∀ k, P - p k ∈ coeffIdeal (maximalIdeal R ^ k) := by
  classical
  have hCauchy : ∀ (i a b : ℕ), a ≤ b →
      (p a).coeff i - (p b).coeff i ∈ maximalIdeal R ^ a := by
    intro i a b hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction c with
    | zero => simp
    | succ c ih =>
      have h1 : (p (a + c + 1)).coeff i - (p (a + c)).coeff i ∈ maximalIdeal R ^ (a + c) := by
        have := (mem_coeffIdeal.mp (hstep (a + c))) i
        rwa [coeff_sub] at this
      have h1' : (p (a + c)).coeff i - (p (a + c + 1)).coeff i ∈ maximalIdeal R ^ (a + c) := by
        have hneg := (Ideal.neg_mem_iff (maximalIdeal R ^ (a + c))).mpr h1
        simpa using hneg
      have h2 : (p (a + c)).coeff i - (p (a + c + 1)).coeff i ∈ maximalIdeal R ^ a :=
        Ideal.pow_le_pow_right (Nat.le_add_right a c) h1'
      have hsplit : (p a).coeff i - (p (a + (c + 1))).coeff i
          = ((p a).coeff i - (p (a + c)).coeff i)
            + ((p (a + c)).coeff i - (p (a + c + 1)).coeff i) := by
        rw [← Nat.add_assoc]; ring
      rw [hsplit]
      exact Ideal.add_mem _ ih h2
  have hprec : ∀ i : ℕ, ∃ L : R,
      ∀ k, (p k).coeff i ≡ L [SMOD (maximalIdeal R ^ k • ⊤ : Ideal R)] := by
    intro i
    refine IsPrecomplete.prec' (fun k => (p k).coeff i) ?_
    intro a b hab
    rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    exact hCauchy i a b hab
  choose L hL using hprec
  refine ⟨∑ i ∈ Finset.range d, Polynomial.C (L i) * X ^ i,
    degree_sum_range_C_mul_X_pow_lt L d, ?_⟩
  intro k
  rw [mem_coeffIdeal]
  intro i
  rw [coeff_sub, coeff_sum_range_C_mul_X_pow]
  by_cases hi : i < d
  · rw [if_pos hi]
    have := hL i k
    rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at this
    have hneg := (Ideal.neg_mem_iff (maximalIdeal R ^ k)).mpr this
    simpa using hneg
  · rw [if_neg hi]
    have hpi : (p k).coeff i = 0 :=
      coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le (hdeg k) (by exact_mod_cast Nat.le_of_not_lt hi))
    simp [hpi]

end Limit

/-! ## 6. The factorization theorem -/

section Main

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A monic polynomial over the residue field lifts to a monic polynomial of the same degree. -/
theorem exists_monic_lift {p₀ : Polynomial (ResidueField R)} (hp₀ : p₀.Monic) :
    ∃ p : Polynomial R, p.Monic ∧ p.map (residue R) = p₀ ∧ p.natDegree = p₀.natDegree := by
  obtain ⟨p, hmap, hdeg, hmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) p₀) hp₀
  exact ⟨p, hmonic, hmap, natDegree_eq_of_degree_eq hdeg⟩

/-- The `natDegree` of a monic polynomial is read off its residue reduction. -/
theorem natDegree_eq_of_map_eq {p : Polynomial R} {p₀ : Polynomial (ResidueField R)}
    (hp : p.Monic) (hmap : p.map (residue R) = p₀) : p.natDegree = p₀.natDegree := by
  rw [← hmap, hp.natDegree_map]

/-- Difference of two monic polynomials of the same degree drops degree. -/
theorem degree_sub_lt_of_monic_of_natDegree_eq {p q : Polynomial R} (hp : p.Monic) (hq : q.Monic)
    (hd : p.natDegree = q.natDegree) : (p - q).degree < (p.natDegree : WithBot ℕ) := by
  have hdd : p.degree = q.degree := by
    rw [degree_eq_natDegree hp.ne_zero, degree_eq_natDegree hq.ne_zero, hd]
  have := degree_sub_lt hdd hp.ne_zero (by rw [hp.leadingCoeff, hq.leadingCoeff])
  rwa [degree_eq_natDegree hp.ne_zero] at this

variable [IsAdicComplete (maximalIdeal R) R]

/-- **Hensel's lemma, factorization form.**  Over a complete local ring, a coprime monic
factorization of the residue reduction of a monic polynomial lifts to a monic factorization.
The degrees of the lifted factors are those of the residual factors. -/
theorem exists_monic_factorization {f : Polynomial R} (hf : f.Monic)
    {g₀ h₀ : Polynomial (ResidueField R)} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue R) = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree := by
  classical
  -- degrees
  have hfdeg : f.natDegree = g₀.natDegree + h₀.natDegree := by
    have h1 : (f.map (residue R)).natDegree = f.natDegree := hf.natDegree_map (residue R)
    rw [hfgh, hg₀.natDegree_mul hh₀] at h1
    exact h1.symm
  -- the degree of the error is bounded whenever the approximants are monic lifts
  have hdeglt : ∀ x : Polynomial R × Polynomial R, x.1.Monic → x.2.Monic →
      x.1.map (residue R) = g₀ → x.2.map (residue R) = h₀ →
      (f - x.1 * x.2).degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ) := by
    intro x h1 h3 h5 h6
    have h2 : x.1.natDegree = g₀.natDegree := natDegree_eq_of_map_eq h1 h5
    have h4 : x.2.natDegree = h₀.natDegree := natDegree_eq_of_map_eq h3 h6
    have hprod : (x.1 * x.2).Monic := h1.mul h3
    have hpd : (x.1 * x.2).natDegree = g₀.natDegree + h₀.natDegree := by
      rw [h1.natDegree_mul h3, h2, h4]
    have := degree_sub_lt_of_monic_of_natDegree_eq hf hprod (by rw [hfdeg, hpd])
    rwa [hfdeg] at this
  -- the base lifts
  obtain ⟨G₁, hG₁mon, hG₁map, hG₁deg⟩ := exists_monic_lift (R := R) hg₀
  obtain ⟨H₁, hH₁mon, hH₁map, hH₁deg⟩ := exists_monic_lift (R := R) hh₀
  have hbase : f - G₁ * H₁ ∈ coeffIdeal (maximalIdeal R ^ (0 + 1)) := by
    rw [zero_add, pow_one, ← map_residue_eq_zero_iff, Polynomial.map_sub, Polynomial.map_mul,
      hG₁map, hH₁map, hfgh, sub_self]
  -- the Newton step, made total by `by_cases` so that it can be iterated by `Nat.rec`
  have step : ∀ (k : ℕ) (x : Polynomial R × Polynomial R),
      ∃ y : Polynomial R × Polynomial R,
        (x.1.Monic ∧ x.2.Monic ∧ x.1.map (residue R) = g₀ ∧ x.2.map (residue R) = h₀ ∧
            f - x.1 * x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1))) →
          (y.1.Monic ∧ y.2.Monic ∧ y.1.map (residue R) = g₀ ∧ y.2.map (residue R) = h₀ ∧
            f - y.1 * y.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1))) ∧
          y.1 - x.1 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) ∧
          y.2 - x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) := by
    intro k x
    by_cases hx : x.1.Monic ∧ x.2.Monic ∧ x.1.map (residue R) = g₀ ∧
        x.2.map (residue R) = h₀ ∧ f - x.1 * x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1))
    · obtain ⟨hx1, hx3, hx5, hx6, hx7⟩ := hx
      obtain ⟨δG, δH, hδGdeg, hδHdeg, hδGmem, hδHmem, herr⟩ :=
        exists_solve_step hg₀ hh₀ hcop hG₁map hH₁map (k + 1) hx7 (hdeglt x hx1 hx3 hx5 hx6)
      have hx2 : x.1.natDegree = g₀.natDegree := natDegree_eq_of_map_eq hx1 hx5
      have hx4 : x.2.natDegree = h₀.natDegree := natDegree_eq_of_map_eq hx3 hx6
      have hx1deg : x.1.degree = (g₀.natDegree : WithBot ℕ) := by
        rw [degree_eq_natDegree hx1.ne_zero, hx2]
      have hx2deg : x.2.degree = (h₀.natDegree : WithBot ℕ) := by
        rw [degree_eq_natDegree hx3.ne_zero, hx4]
      have hmle : maximalIdeal R ^ (k + 1) ≤ maximalIdeal R := by
        simpa using Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.succ_le_succ (Nat.zero_le k))
      have hδGm : δG ∈ coeffIdeal (maximalIdeal R) := coeffIdeal_mono hmle hδGmem
      have hδHm : δH ∈ coeffIdeal (maximalIdeal R) := coeffIdeal_mono hmle hδHmem
      refine ⟨(x.1 + δG, x.2 + δH), fun _ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
      · exact hx1.add_of_left (by rw [hx1deg]; exact hδGdeg)
      · exact hx3.add_of_left (by rw [hx2deg]; exact hδHdeg)
      · have : δG.map (residue R) = 0 := map_residue_eq_zero_iff.mpr hδGm
        simp [Polynomial.map_add, this, hx5]
      · have : δH.map (residue R) = 0 := map_residue_eq_zero_iff.mpr hδHm
        simp [Polynomial.map_add, this, hx6]
      · -- the error recursion
        have hH₁x : H₁ - x.2 ∈ coeffIdeal (maximalIdeal R) :=
          sub_mem_coeffIdeal_maximalIdeal_iff.mpr (by rw [hH₁map, hx6])
        have hG₁x : G₁ - x.1 ∈ coeffIdeal (maximalIdeal R) :=
          sub_mem_coeffIdeal_maximalIdeal_iff.mpr (by rw [hG₁map, hx5])
        have t1 : δG * (H₁ - x.2) ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1)) := by
          have := mul_mem_coeffIdeal_mul hδGmem hH₁x
          rwa [← pow_succ] at this
        have t2 : δH * (G₁ - x.1) ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1)) := by
          have := mul_mem_coeffIdeal_mul hδHmem hG₁x
          rwa [← pow_succ] at this
        have t3 : δG * δH ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1)) := by
          have h0 := mul_mem_coeffIdeal_mul hδGmem hδHmem
          rw [← pow_add] at h0
          exact coeffIdeal_mono (Ideal.pow_le_pow_right (by omega)) h0
        have hsplit : f - (x.1 + δG) * (x.2 + δH)
            = ((f - x.1 * x.2) - (H₁ * δG + G₁ * δH))
              + δG * (H₁ - x.2) + δH * (G₁ - x.1) - δG * δH := by ring
        rw [hsplit]
        exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ herr t1) t2) t3
      · simpa using hδGmem
      · simpa using hδHmem
    · exact ⟨x, fun hc => absurd hc hx⟩
  choose next hnext using step
  obtain ⟨A, hA0, hAsucc⟩ : ∃ A : ℕ → Polynomial R × Polynomial R,
      A 0 = (G₁, H₁) ∧ ∀ k, A (k + 1) = next k (A k) :=
    ⟨fun k => Nat.rec (G₁, H₁) (fun j acc => next j acc) k, rfl, fun _ => rfl⟩
  have hInvA : ∀ k, (A k).1.Monic ∧ (A k).2.Monic ∧ (A k).1.map (residue R) = g₀ ∧
      (A k).2.map (residue R) = h₀ ∧
      f - (A k).1 * (A k).2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) := by
    intro k
    induction k with
    | zero => rw [hA0]; exact ⟨hG₁mon, hH₁mon, hG₁map, hH₁map, hbase⟩
    | succ k ih => rw [hAsucc k]; exact (hnext k (A k) ih).1
  have hstepA1 : ∀ k, (A (k + 1)).1 - (A k).1 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k
    have := (hnext k (A k) (hInvA k)).2.1
    rw [← hAsucc k] at this
    exact coeffIdeal_mono (Ideal.pow_le_pow_right (Nat.le_succ k)) this
  have hstepA2 : ∀ k, (A (k + 1)).2 - (A k).2 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k
    have := (hnext k (A k) (hInvA k)).2.2
    rw [← hAsucc k] at this
    exact coeffIdeal_mono (Ideal.pow_le_pow_right (Nat.le_succ k)) this
  -- pass to the limit on the tails
  have htail1 : ∀ k, ((A k).1 - X ^ g₀.natDegree).degree < (g₀.natDegree : WithBot ℕ) := by
    intro k
    have h1 := (hInvA k).1
    have h2 : (A k).1.natDegree = g₀.natDegree := natDegree_eq_of_map_eq h1 (hInvA k).2.2.1
    have := degree_sub_lt_of_monic_of_natDegree_eq h1 (monic_X_pow (R := R) g₀.natDegree)
      (by rw [h2, natDegree_X_pow])
    rwa [h2] at this
  have htail2 : ∀ k, ((A k).2 - X ^ h₀.natDegree).degree < (h₀.natDegree : WithBot ℕ) := by
    intro k
    have h1 := (hInvA k).2.1
    have h2 : (A k).2.natDegree = h₀.natDegree := natDegree_eq_of_map_eq h1 (hInvA k).2.2.2.1
    have := degree_sub_lt_of_monic_of_natDegree_eq h1 (monic_X_pow (R := R) h₀.natDegree)
      (by rw [h2, natDegree_X_pow])
    rwa [h2] at this
  obtain ⟨TG, hTGdeg, hTGlim⟩ := exists_adicLimit_of_degree_lt g₀.natDegree
    (fun k => (A k).1 - X ^ g₀.natDegree) htail1 (by intro k; simpa using hstepA1 k)
  obtain ⟨TH, hTHdeg, hTHlim⟩ := exists_adicLimit_of_degree_lt h₀.natDegree
    (fun k => (A k).2 - X ^ h₀.natDegree) htail2 (by intro k; simpa using hstepA2 k)
  set G : Polynomial R := X ^ g₀.natDegree + TG with hGdef
  set H : Polynomial R := X ^ h₀.natDegree + TH with hHdef
  have hGmon : G.Monic := (monic_X_pow _).add_of_left (by rwa [degree_X_pow])
  have hHmon : H.Monic := (monic_X_pow _).add_of_left (by rwa [degree_X_pow])
  have hGdeg : G.natDegree = g₀.natDegree := by
    have : G.degree = (g₀.natDegree : WithBot ℕ) := by
      rw [hGdef, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  have hHdeg : H.natDegree = h₀.natDegree := by
    have : H.degree = (h₀.natDegree : WithBot ℕ) := by
      rw [hHdef, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  have hGlim : ∀ k, G - (A k).1 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k
    have h0 := hTGlim k
    have hid : G - (A k).1 = TG - ((A k).1 - X ^ g₀.natDegree) := by rw [hGdef]; ring
    rw [hid]; exact h0
  have hHlim : ∀ k, H - (A k).2 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k
    have h0 := hTHlim k
    have hid : H - (A k).2 = TH - ((A k).2 - X ^ h₀.natDegree) := by rw [hHdef]; ring
    rw [hid]; exact h0
  have hGmap : G.map (residue R) = g₀ := by
    have h1 := hGlim 1
    rw [pow_one] at h1
    rw [sub_mem_coeffIdeal_maximalIdeal_iff] at h1
    rw [h1]
    exact (hInvA 1).2.2.1
  have hHmap : H.map (residue R) = h₀ := by
    have h1 := hHlim 1
    rw [pow_one] at h1
    rw [sub_mem_coeffIdeal_maximalIdeal_iff] at h1
    rw [h1]
    exact (hInvA 1).2.2.2.1
  have hzero : f - G * H = 0 := by
    have hall : ∀ k, f - G * H ∈ coeffIdeal (maximalIdeal R ^ k) := by
      intro k
      have h1 : f - (A k).1 * (A k).2 ∈ coeffIdeal (maximalIdeal R ^ k) :=
        coeffIdeal_mono (Ideal.pow_le_pow_right (Nat.le_succ k)) (hInvA k).2.2.2.2
      have h2 : (G - (A k).1) * H ∈ coeffIdeal (maximalIdeal R ^ k) :=
        Ideal.mul_mem_right _ _ (hGlim k)
      have h3 : (A k).1 * (H - (A k).2) ∈ coeffIdeal (maximalIdeal R ^ k) :=
        Ideal.mul_mem_left _ _ (hHlim k)
      have hid : f - G * H
          = (f - (A k).1 * (A k).2) - (G - (A k).1) * H - (A k).1 * (H - (A k).2) := by ring
      rw [hid]
      exact Ideal.sub_mem _ (Ideal.sub_mem _ h1 h2) h3
    ext i
    rw [coeff_zero]
    refine IsHausdorff.haus' (I := maximalIdeal R) ((f - G * H).coeff i) ?_
    intro n
    rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    exact (mem_coeffIdeal.mp (hall n)) i
  exact ⟨G, H, hGmon, hHmon, sub_eq_zero.mp hzero, hGmap, hHmap, hGdeg, hHdeg⟩

/-! ## 7. The exact interpolation solve, Bézout coprimality, and uniqueness

`exists_eq_add_mul_of_degree_lt` is the *exact* form of the interpolation problem: the Newton step
`exists_solve_step` only solves it modulo one more power of `𝔪`, but iterating and passing to the
limit solves it on the nose. Its `w = 1` case says that two monic lifts of a coprime residual pair
are Bézout-coprime in `R[X]` — a genuinely stronger statement than residual coprimality, and the
engine of the uniqueness theorem. -/

/-- **Exact interpolation.** With `g, h` monic lifts of a coprime monic residual pair, every
polynomial of degree `< deg g + deg h` is `h * u + g * v` with `deg u < deg g`, `deg v < deg h`. -/
theorem exists_eq_add_mul_of_degree_lt {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg : g.Monic) (hh : h.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    {w : Polynomial R} (hw : w.degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ)) :
    ∃ u v : Polynomial R, u.degree < (g₀.natDegree : WithBot ℕ) ∧
      v.degree < (h₀.natDegree : WithBot ℕ) ∧ w = h * u + g * v := by
  classical
  have hgdeg : g.degree = (g₀.natDegree : WithBot ℕ) := by
    rw [degree_eq_natDegree hg.ne_zero, natDegree_eq_of_map_eq hg hgr]
  have hhdeg : h.degree = (h₀.natDegree : WithBot ℕ) := by
    rw [degree_eq_natDegree hh.ne_zero, natDegree_eq_of_map_eq hh hhr]
  -- the residual error of a degree-bounded pair is degree-bounded
  have herrdeg : ∀ x : Polynomial R × Polynomial R,
      x.1.degree < (g₀.natDegree : WithBot ℕ) → x.2.degree < (h₀.natDegree : WithBot ℕ) →
      (w - (h * x.1 + g * x.2)).degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ) := by
    intro x h1 h2
    have e1 : (h * x.1).degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (degree_mul_le _ _) ?_
      rw [hhdeg, Nat.cast_add, add_comm ((g₀.natDegree : WithBot ℕ))]
      exact WithBot.add_lt_add_left (by simp) h1
    have e2 : (g * x.2).degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (degree_mul_le _ _) ?_
      rw [hgdeg, Nat.cast_add]
      exact WithBot.add_lt_add_left (by simp) h2
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt hw ?_)
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt e1 e2)
  have step : ∀ (k : ℕ) (x : Polynomial R × Polynomial R),
      ∃ y : Polynomial R × Polynomial R,
        (x.1.degree < (g₀.natDegree : WithBot ℕ) ∧ x.2.degree < (h₀.natDegree : WithBot ℕ) ∧
            w - (h * x.1 + g * x.2) ∈ coeffIdeal (maximalIdeal R ^ k)) →
          (y.1.degree < (g₀.natDegree : WithBot ℕ) ∧ y.2.degree < (h₀.natDegree : WithBot ℕ) ∧
            w - (h * y.1 + g * y.2) ∈ coeffIdeal (maximalIdeal R ^ (k + 1))) ∧
          y.1 - x.1 ∈ coeffIdeal (maximalIdeal R ^ k) ∧
          y.2 - x.2 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k x
    by_cases hx : x.1.degree < (g₀.natDegree : WithBot ℕ) ∧
        x.2.degree < (h₀.natDegree : WithBot ℕ) ∧
        w - (h * x.1 + g * x.2) ∈ coeffIdeal (maximalIdeal R ^ k)
    · obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨δu, δv, hδu, hδv, hδum, hδvm, herr⟩ :=
        exists_solve_step hg₀ hh₀ hcop hgr hhr k hx3 (herrdeg x hx1 hx2)
      refine ⟨(x.1 + δu, x.2 + δv), fun _ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
      · exact lt_of_le_of_lt (degree_add_le _ _) (max_lt hx1 hδu)
      · exact lt_of_le_of_lt (degree_add_le _ _) (max_lt hx2 hδv)
      · have hid : w - (h * (x.1 + δu) + g * (x.2 + δv))
            = (w - (h * x.1 + g * x.2)) - (h * δu + g * δv) := by ring
        rw [hid]; exact herr
      · simpa using hδum
      · simpa using hδvm
    · exact ⟨x, fun hc => absurd hc hx⟩
  choose next hnext using step
  obtain ⟨A, hA0, hAsucc⟩ : ∃ A : ℕ → Polynomial R × Polynomial R,
      A 0 = (0, 0) ∧ ∀ k, A (k + 1) = next k (A k) :=
    ⟨fun k => Nat.rec (0, 0) (fun j acc => next j acc) k, rfl, fun _ => rfl⟩
  have hInvA : ∀ k, (A k).1.degree < (g₀.natDegree : WithBot ℕ) ∧
      (A k).2.degree < (h₀.natDegree : WithBot ℕ) ∧
      w - (h * (A k).1 + g * (A k).2) ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k
    induction k with
    | zero =>
      rw [hA0]
      refine ⟨by simp, by simp, ?_⟩
      rw [pow_zero, Ideal.one_eq_top]
      exact mem_coeffIdeal.mpr fun i => Submodule.mem_top
    | succ k ih => rw [hAsucc k]; exact (hnext k (A k) ih).1
  have hstep1 : ∀ k, (A (k + 1)).1 - (A k).1 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k; have := (hnext k (A k) (hInvA k)).2.1; rwa [← hAsucc k] at this
  have hstep2 : ∀ k, (A (k + 1)).2 - (A k).2 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k; have := (hnext k (A k) (hInvA k)).2.2; rwa [← hAsucc k] at this
  obtain ⟨u, hudeg, hulim⟩ := exists_adicLimit_of_degree_lt g₀.natDegree (fun k => (A k).1)
    (fun k => (hInvA k).1) hstep1
  obtain ⟨v, hvdeg, hvlim⟩ := exists_adicLimit_of_degree_lt h₀.natDegree (fun k => (A k).2)
    (fun k => (hInvA k).2.1) hstep2
  refine ⟨u, v, hudeg, hvdeg, ?_⟩
  have hall : ∀ k, w - (h * u + g * v) ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k
    have hid : w - (h * u + g * v)
        = (w - (h * (A k).1 + g * (A k).2)) - h * (u - (A k).1) - g * (v - (A k).2) := by ring
    rw [hid]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ (hInvA k).2.2
      (Ideal.mul_mem_left _ _ (hulim k))) (Ideal.mul_mem_left _ _ (hvlim k))
  have hzero : w - (h * u + g * v) = 0 := by
    ext i
    rw [coeff_zero]
    refine IsHausdorff.haus' (I := maximalIdeal R) ((w - (h * u + g * v)).coeff i) ?_
    intro n
    rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    exact (mem_coeffIdeal.mp (hall n)) i
  exact sub_eq_zero.mp hzero

/-- **Bézout coprimality of the lifted factors.**  Two monic lifts of a coprime monic residual
pair satisfy an honest Bézout identity `a * g + b * h = 1` in `R[X]`. -/
theorem isCoprime_of_map_eq {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg : g.Monic) (hh : h.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀) : IsCoprime g h := by
  rcases Nat.eq_zero_or_pos (g₀.natDegree + h₀.natDegree) with hn | hn
  · have hg1 : g = 1 :=
      eq_one_of_monic_natDegree_zero hg (by rw [natDegree_eq_of_map_eq hg hgr]; omega)
    rw [hg1]
    exact isCoprime_one_left
  · obtain ⟨u, v, _, _, heq⟩ :=
      exists_eq_add_mul_of_degree_lt hg hh hg₀ hh₀ hcop hgr hhr (w := 1)
        (by rw [degree_one]; exact_mod_cast hn)
    exact ⟨v, u, by linear_combination -heq⟩

set_option linter.unusedVariables false in
/-- **Uniqueness of the Hensel factorization.**  Among monic pairs reducing to the *same* coprime
monic residual pair, the factorization of a given polynomial is unique.

(`hh` and `hhr` are kept for symmetry of the statement — the proof does not need them, since `h`
is pinned by cancelling the monic `g`.) -/
theorem monic_factorization_unique {g h g' h' : Polynomial R}
    {g₀ h₀ : Polynomial (ResidueField R)}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    (hgr' : g'.map (residue R) = g₀) (hhr' : h'.map (residue R) = h₀)
    (heq : g * h = g' * h') : g = g' ∧ h = h' := by
  have hcop' : IsCoprime g h' := isCoprime_of_map_eq hg hh' hg₀ hh₀ hcop hgr hhr'
  have hdvd : g ∣ (g' - g) * h' := ⟨h - h', by linear_combination -heq⟩
  have hgU : g ∣ g' - g := hcop'.dvd_of_dvd_mul_right hdvd
  have hdeg : (g' - g).degree < g.degree := by
    have h1 := degree_sub_lt_of_monic_of_natDegree_eq hg' hg
      (by rw [natDegree_eq_of_map_eq hg' hgr', natDegree_eq_of_map_eq hg hgr])
    rwa [degree_eq_natDegree hg.ne_zero, natDegree_eq_of_map_eq hg hgr,
      ← natDegree_eq_of_map_eq hg' hgr']
  have hU0 : g' - g = 0 := by
    have e1 : (g' - g) %ₘ g = 0 := (modByMonic_eq_zero_iff_dvd hg).mpr hgU
    have e2 : (g' - g) %ₘ g = g' - g := (modByMonic_eq_self_iff hg).mpr hdeg
    rw [← e2, e1]
  have hgg' : g = g' := by linear_combination -hU0
  refine ⟨hgg', ?_⟩
  have : g * h = g * h' := by rw [heq, hgg']
  exact hg.isRegular.left this

/-- **Peeling a simple residual root.**  If the reduction of a monic `f` has `ρ₀` as a root at
which the derivative does not vanish, then `f = (X - ρ) * q` over `R` with `q` monic, `ρ` lifting
`ρ₀`, and the reduction of `q` pinned to `f̄ /ₘ (X - ρ₀)`.  Nothing at all is assumed about the
cofactor: it may reduce to a repeated quadratic.

**This corollary is a convenience, not new strength.** It is also reachable from the ROOT form
(`HenselianLocalRing.is_henselian` lifts `ρ₀` to a root `ρ`, and monic division by `X - C ρ`
supplies `q`); what it saves the caller is discharging the coprimality hypothesis, which is done
here from `hsimple` via `isCoprime_of_is_root_of_eval_derivative_ne_zero`.  The results in this
file that the root form genuinely does *not* give are `exists_monic_factorization` when no residual
factor is a simple linear one — e.g. a degree-4 reduction `(X - a) ^ 2 * (X - b) ^ 2` with
`a ≠ b`, or a product of two distinct irreducible quadratics — together with
`isCoprime_of_map_eq` and `monic_factorization_unique`. -/
theorem exists_linear_factorization {f : Polynomial R} (hf : f.Monic) {ρ₀ : ResidueField R}
    (hroot : (f.map (residue R)).IsRoot ρ₀)
    (hsimple : (f.map (residue R)).derivative.eval ρ₀ ≠ 0) :
    ∃ (ρ : R) (q : Polynomial R), q.Monic ∧ f = (X - Polynomial.C ρ) * q ∧ residue R ρ = ρ₀ ∧
      q.map (residue R) = (f.map (residue R)) /ₘ (X - Polynomial.C ρ₀) := by
  have hf₀ : (f.map (residue R)).Monic := hf.map _
  have hmul : f.map (residue R)
      = (X - Polynomial.C ρ₀) * ((f.map (residue R)) /ₘ (X - Polynomial.C ρ₀)) :=
    (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
  have hq₀ : ((f.map (residue R)) /ₘ (X - Polynomial.C ρ₀)).Monic :=
    (monic_X_sub_C ρ₀).of_mul_monic_left (by rw [← hmul]; exact hf₀)
  have hcop : IsCoprime (X - Polynomial.C ρ₀) ((f.map (residue R)) /ₘ (X - Polynomial.C ρ₀)) :=
    isCoprime_of_is_root_of_eval_derivative_ne_zero _ ρ₀ hsimple
  obtain ⟨g, q, hgm, hqm, hfgq, hgr, hqr, hgd, _⟩ :=
    exists_monic_factorization hf (monic_X_sub_C ρ₀) hq₀ hcop hmul
  have hgd1 : g.natDegree = 1 := by rw [hgd, natDegree_X_sub_C]
  have hgform : g = X + Polynomial.C (g.coeff 0) := hgm.eq_X_add_C hgd1
  refine ⟨-g.coeff 0, q, hqm, ?_, ?_, hqr⟩
  · rw [hfgq]
    congr 1
    rw [hgform]
    simp
  · -- read the constant term off the reduction `g ↦ X - C ρ₀`
    have : (g.map (residue R)).coeff 0 = (X - Polynomial.C ρ₀ : Polynomial (ResidueField R)).coeff 0 := by
      rw [hgr]
    rw [coeff_map] at this
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at this
    rw [map_neg, this, neg_neg]

end Main

/-! ## 8. Instances — the theorem is non-vacuous on the bases this repo uses -/

section Instances

example (p : ℕ) [Fact (Nat.Prime p)] {f : Polynomial ℤ_[p]} (hf : f.Monic)
    {g₀ h₀ : Polynomial (ResidueField ℤ_[p])} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue ℤ_[p]) = g₀ * h₀) :
    ∃ g h : Polynomial ℤ_[p], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue ℤ_[p]) = g₀ ∧ h.map (residue ℤ_[p]) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree :=
  exists_monic_factorization hf hg₀ hh₀ hcop hfgh

/-- The complete-DVR bundle used throughout `Uniformity.Density` (`LocalData.lean`) is an instance:
`IsDiscreteValuationRing` supplies `IsLocalRing`, so the general theorem applies verbatim, with no
finiteness of the residue field required. -/
theorem exists_monic_factorization_dvr (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {f : Polynomial O}
    (hf : f.Monic) {g₀ h₀ : Polynomial (ResidueField O)} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue O) = g₀ * h₀) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue O) = g₀ ∧ h.map (residue O) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree :=
  exists_monic_factorization hf hg₀ hh₀ hcop hfgh

end Instances

end Hensel

end Uniformity
