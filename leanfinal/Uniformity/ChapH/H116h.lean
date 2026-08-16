/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapH.H116h — Hensel's lemma for a NON-MONIC `f`, one monic factor

**Chapter H, HELPER NODE H.116h.**  The missing input recorded in the module docstring of
`Uniformity/ChapH/H116.lean`, verbatim:

> Let `R` be a complete local ring, `f : R[X]` (NOT assumed monic), and
> `f.map (residue R) = g₀ * h₀` with `g₀` MONIC and `IsCoprime g₀ h₀`.  Then `f = g * h` with
> `g` monic, `g.natDegree = g₀.natDegree`, `g.map (residue R) = g₀`, `h.map (residue R) = h₀`.

That is `exists_monic_factorization_of_monic_left` in §5.  It is the form that has Weierstrass
preparation as its special case (`h₀` a nonzero constant), the form
`Mathlib/RingTheory/Henselian.lean` lists in its own `## TODO` (v4.31 carries only the root form),
and the form `Uniformity/HenselFactorization.lean` does NOT have: that file's
`exists_monic_factorization` requires `f.Monic`, and H.116's divided β frame is monic only when
`D = m k` (machine-checked counter-cell in `ChapH/H116.lean` §4).

## Method — the same Newton iteration, with the degree bookkeeping rebuilt

`HenselFactorization.lean` proves the monic case by a Newton iteration on the `𝔪`-adic filtration
whose correction step comes from a residue-field Bézout solve.  That iteration generalizes; what
does NOT generalize is its degree bookkeeping, which is stated throughout in terms of
`g₀.natDegree + h₀.natDegree` and uses monicity of BOTH residual factors.  So §§2–4 below rebuild
the three helper lemmas (`exists_solve_field`, `exists_solve_mod`, `exists_solve_step`) with

* `h₀` NOT monic — only `g₀.Monic` and `IsCoprime g₀ h₀` are assumed, and
* the total degree carried as an EXPLICIT BUDGET `l`: hypotheses become `h₀.degree ≤ l` and
  `w.degree ≤ g₀.natDegree + l`, and the cofactor bound becomes `v.degree ≤ l` (the monic file's
  `v.degree < h₀.natDegree`, which is false here — `h₀` may drop degree, and `f` may not).

The budget is what makes the iteration close: the cofactor approximants live in the fixed
`R`-module of polynomials of degree `≤ l`, so `exists_adicLimit_of_degree_lt` applies to them
DIRECTLY (in the monic case one first had to subtract the tail `X ^ h₀.natDegree`).  The other
change is that the error `f - gₖ hₖ` is degree-bounded for the cheap reason `deg (gₖ hₖ) ≤ m + l`,
rather than by leading-coefficient cancellation between two monics.

Reused verbatim from `Uniformity/HenselFactorization.lean` (no copy here): `coeffIdeal` and its
API, the truncation lemmas of its §3, `exists_adicLimit_of_degree_lt`, `exists_monic_lift`,
`natDegree_eq_of_map_eq`, `degree_sub_lt_of_monic_of_natDegree_eq`.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
Statements are new and flagged for human review.
-/

set_option linter.style.longLine false

namespace Uniformity

namespace Hensel

open Polynomial IsLocalRing

/-! ## 1. Degree-budget plumbing -/

section Budget

variable {R : Type*} [CommRing R]

/-- `degree ≤ n` upgraded to the strict form `degree < n + 1` that the truncation lemmas want. -/
theorem degree_lt_succ_of_degree_le {p : Polynomial R} {n : ℕ} (h : p.degree ≤ (n : WithBot ℕ)) :
    p.degree < ((n + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self n)

/-- The converse direction: over `WithBot ℕ`, `degree < n + 1` is `degree ≤ n`. -/
theorem degree_le_of_degree_lt_succ {p : Polynomial R} {n : ℕ}
    (h : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) : p.degree ≤ (n : WithBot ℕ) := by
  by_contra hcon
  rw [not_le] at hcon
  have h1 := Nat.WithBot.add_one_le_of_lt hcon
  rw [show ((n + 1 : ℕ) : WithBot ℕ) = (n : WithBot ℕ) + 1 by push_cast; ring] at h
  exact absurd h (not_lt.mpr h1)

/-- The product bound behind every degree step below: a factor of degree `≤ m` times a
polynomial of degree `≤ l` has degree `≤ m + l`. -/
theorem degree_mul_le_of_le {p q : Polynomial R} {m l : ℕ} (hp : p.degree ≤ (m : WithBot ℕ))
    (hq : q.degree ≤ (l : WithBot ℕ)) : (p * q).degree ≤ ((m + l : ℕ) : WithBot ℕ) := by
  refine le_trans (degree_mul_le p q) ?_
  push_cast
  exact add_le_add hp hq

end Budget

/-! ## 2. The residue-field solve with only the LEFT factor monic -/

section ResidueSolve

variable {k : Type*} [Field k]

/-- **The non-monic residue solve.**  Over a field, with `g₀` monic of degree `m`, `h₀` coprime to
it of degree `≤ l`, every `w` of degree `≤ m + l` is `h₀ * u + g₀ * v` with `deg u < m` and
`deg v ≤ l`.

Compare `Hensel.exists_solve_field`, which assumes both factors monic and produces
`deg v < h₀.natDegree`.  The witnesses are the same (`u = (b w) %ₘ g₀`); what changes is the
bound on `v`, which is read off `g₀ * v = w - h₀ * u` using only monicity of `g₀`. -/
theorem exists_solve_field_of_monic_left {g₀ h₀ : Polynomial k} (hg₀ : g₀.Monic)
    (hcop : IsCoprime g₀ h₀) {l : ℕ} (hh₀ : h₀.degree ≤ (l : WithBot ℕ))
    {w : Polynomial k} (hw : w.degree ≤ ((g₀.natDegree + l : ℕ) : WithBot ℕ)) :
    ∃ u v : Polynomial k, u.degree < (g₀.natDegree : WithBot ℕ) ∧ v.degree ≤ (l : WithBot ℕ) ∧
      w = h₀ * u + g₀ * v := by
  obtain ⟨a, b, hab⟩ := hcop
  have hg₀deg : g₀.degree = (g₀.natDegree : WithBot ℕ) := degree_eq_natDegree hg₀.ne_zero
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
  -- the bound on `v` is forced by monicity of `g₀` alone; `h₀` only supplies its budget
  have h2 : (h₀ * u).degree < ((g₀.natDegree + l : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add hh₀ (le_refl u.degree)) ?_
    refine lt_of_lt_of_le (WithBot.add_lt_add_left (by simp) hu) ?_
    exact le_of_eq (by push_cast; ring)
  have h3 : (g₀ * v).degree ≤ ((g₀.natDegree + l : ℕ) : WithBot ℕ) := by
    have hgv : g₀ * v = w - h₀ * u := by rw [key]; ring
    rw [hgv]
    exact le_trans (degree_sub_le _ _) (max_le hw (le_of_lt h2))
  rw [degree_mul, hg₀deg,
    show ((g₀.natDegree + l : ℕ) : WithBot ℕ) = (g₀.natDegree : WithBot ℕ) + (l : WithBot ℕ) by
      push_cast; ring] at h3
  exact (WithBot.add_le_add_iff_left (by simp)).mp h3

end ResidueSolve

/-! ## 3. Solving modulo `𝔪`, and the Newton step -/

section SolveMod

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **The non-monic solve, modulo `𝔪`.**  `exists_solve_field_of_monic_left` transported to `R`
along a degree-preserving lift of the field witnesses. -/
theorem exists_solve_mod_of_monic_left {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg₀ : g₀.Monic) (hcop : IsCoprime g₀ h₀) {l : ℕ} (hh₀ : h₀.degree ≤ (l : WithBot ℕ))
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    {w : Polynomial R} (hw : w.degree ≤ ((g₀.natDegree + l : ℕ) : WithBot ℕ)) :
    ∃ u v : Polynomial R, u.degree < (g₀.natDegree : WithBot ℕ) ∧ v.degree ≤ (l : WithBot ℕ) ∧
      w - (h * u + g * v) ∈ coeffIdeal (maximalIdeal R) := by
  have hwmap : (w.map (residue R)).degree ≤ ((g₀.natDegree + l : ℕ) : WithBot ℕ) :=
    le_trans degree_map_le hw
  obtain ⟨u₀, v₀, hu₀, hv₀, hkey⟩ := exists_solve_field_of_monic_left hg₀ hcop hh₀ hwmap
  obtain ⟨u, humap, hudeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) u₀)
  obtain ⟨v, hvmap, hvdeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) v₀)
  refine ⟨u, v, hudeg ▸ hu₀, hvdeg ▸ hv₀, ?_⟩
  rw [← map_residue_eq_zero_iff, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_mul, hgr, hhr, humap, hvmap, sub_eq_zero]
  exact hkey

/-- **The Newton step, non-monic.**  An error in `𝔪 ^ j` of degree `≤ m + l` is corrected to an
error in `𝔪 ^ (j+1)` by corrections that are themselves in `𝔪 ^ j` and respect the budget.

As in `Hensel.exists_solve_step` the proof is LINEARITY IN THE COEFFICIENTS OF THE ERROR: solve
once for each monomial `X ^ i` with `i ≤ m + l`, then take the `R`-linear combination.  That is
what lets the argument run over a non-principal `𝔪`. -/
theorem exists_solve_step_of_monic_left {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg₀ : g₀.Monic) (hcop : IsCoprime g₀ h₀) {l : ℕ} (hh₀ : h₀.degree ≤ (l : WithBot ℕ))
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    (j : ℕ) {e : Polynomial R} (he : e ∈ coeffIdeal (maximalIdeal R ^ j))
    (hdeg : e.degree ≤ ((g₀.natDegree + l : ℕ) : WithBot ℕ)) :
    ∃ u v : Polynomial R, u.degree < (g₀.natDegree : WithBot ℕ) ∧ v.degree ≤ (l : WithBot ℕ) ∧
      u ∈ coeffIdeal (maximalIdeal R ^ j) ∧ v ∈ coeffIdeal (maximalIdeal R ^ j) ∧
      e - (h * u + g * v) ∈ coeffIdeal (maximalIdeal R ^ (j + 1)) := by
  classical
  set m := g₀.natDegree with hm
  have key : ∀ i : ℕ, ∃ uv : Polynomial R × Polynomial R,
      uv.1.degree < (m : WithBot ℕ) ∧ uv.2.degree ≤ (l : WithBot ℕ) ∧
      (i < m + l + 1 → (X : Polynomial R) ^ i - (h * uv.1 + g * uv.2)
        ∈ coeffIdeal (maximalIdeal R)) := by
    intro i
    by_cases hi : i < m + l + 1
    · obtain ⟨u, v, h1, h2, h3⟩ := exists_solve_mod_of_monic_left hg₀ hcop hh₀ hgr hhr
        (w := (X : Polynomial R) ^ i)
        (by rw [degree_X_pow]; exact_mod_cast Nat.lt_succ_iff.mp hi)
      exact ⟨(u, v), h1, h2, fun _ => h3⟩
    · exact ⟨(0, 0), by simp, by simp, fun hc => absurd hc hi⟩
  choose UV hU hV hr using key
  set u : Polynomial R := ∑ i ∈ Finset.range (m + l + 1), Polynomial.C (e.coeff i) * (UV i).1
    with hu
  set v : Polynomial R := ∑ i ∈ Finset.range (m + l + 1), Polynomial.C (e.coeff i) * (UV i).2
    with hv
  have hudeg : u.degree < (m : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < (m : WithBot ℕ))]
    exact fun i _ => lt_of_le_of_lt (degree_C_mul_le_degree _ _) (hU i)
  have hvdeg : v.degree ≤ (l : WithBot ℕ) := by
    refine le_trans (degree_sum_le _ _) (Finset.sup_le fun i _ => ?_)
    exact le_trans (degree_C_mul_le_degree _ _) (hV i)
  refine ⟨u, v, hudeg, hvdeg, ?_, ?_, ?_⟩
  · exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_right _ _ (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
  · exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_right _ _ (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
  · have hexp : e - (h * u + g * v)
        = ∑ i ∈ Finset.range (m + l + 1), Polynomial.C (e.coeff i) *
            ((X : Polynomial R) ^ i - (h * (UV i).1 + g * (UV i).2)) := by
      rw [sum_C_mul_solve_expand (fun i => e.coeff i) (fun i => (UV i).1) (fun i => (UV i).2)
        g h (m + l + 1), hu, hv]
      congr 1
      exact eq_sum_range_of_degree_lt (degree_lt_succ_of_degree_le hdeg)
    rw [hexp]
    refine Ideal.sum_mem _ fun i hi => ?_
    have := mul_mem_coeffIdeal_mul (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
      (hr i (Finset.mem_range.mp hi))
    rwa [← pow_succ] at this

end SolveMod

/-! ## 4. The factorization theorem with a degree budget -/

section Main

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

/-- **Hensel's lemma, non-monic factorization form, with an explicit budget.**  If `f` has degree
`≤ m + l` and its reduction splits as `g₀ * h₀` with `g₀` monic of degree `m` and coprime to `h₀`,
then `f = g * h` with `g` monic of degree `m` lifting `g₀` and `h` of degree `≤ l` lifting `h₀`.

`f` is NOT assumed monic; `h₀` is NOT assumed monic; no discreteness, no finiteness of the residue
field, no domain hypothesis, no restriction on the residue characteristic. -/
theorem exists_monic_factorization_of_degree_le {f : Polynomial R}
    {g₀ h₀ : Polynomial (ResidueField R)} (hg₀ : g₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hfgh : f.map (residue R) = g₀ * h₀) {l : ℕ}
    (hf : f.degree ≤ ((g₀.natDegree + l : ℕ) : WithBot ℕ)) :
    ∃ g h : Polynomial R, g.Monic ∧ g.natDegree = g₀.natDegree ∧
      h.degree ≤ (l : WithBot ℕ) ∧ f = g * h ∧
      g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ := by
  classical
  set m := g₀.natDegree with hm
  -- the residual cofactor respects the budget: `deg g₀ + deg h₀ = deg (f mod 𝔪) ≤ m + l`
  have hh₀ : h₀.degree ≤ (l : WithBot ℕ) := by
    have h1 : (f.map (residue R)).degree ≤ ((m + l : ℕ) : WithBot ℕ) := le_trans degree_map_le hf
    rw [hfgh, degree_mul, degree_eq_natDegree hg₀.ne_zero, ← hm] at h1
    rw [show ((m + l : ℕ) : WithBot ℕ) = (m : WithBot ℕ) + (l : WithBot ℕ) by push_cast; ring] at h1
    exact (WithBot.add_le_add_iff_left (by simp)).mp h1
  -- the base lifts: `G₁` monic of degree `m`, `H₁` of the same degree as `h₀`
  obtain ⟨G₁, hG₁mon, hG₁map, hG₁deg⟩ := exists_monic_lift (R := R) hg₀
  obtain ⟨H₁, hH₁map, hH₁degeq⟩ := Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) h₀)
  have hH₁deg : H₁.degree ≤ (l : WithBot ℕ) := hH₁degeq ▸ hh₀
  have hbase : f - G₁ * H₁ ∈ coeffIdeal (maximalIdeal R ^ (0 + 1)) := by
    rw [zero_add, pow_one, ← map_residue_eq_zero_iff, Polynomial.map_sub, Polynomial.map_mul,
      hG₁map, hH₁map, hfgh, sub_self]
  -- the error of a budget-respecting pair is budget-bounded — no cancellation needed
  have hdeglt : ∀ x : Polynomial R × Polynomial R, x.1.Monic → x.1.natDegree = m →
      x.2.degree ≤ (l : WithBot ℕ) →
      (f - x.1 * x.2).degree ≤ ((m + l : ℕ) : WithBot ℕ) := by
    intro x h1 h2 h3
    refine le_trans (degree_sub_le _ _) (max_le hf ?_)
    exact degree_mul_le_of_le (le_of_eq (by rw [degree_eq_natDegree h1.ne_zero, h2])) h3
  -- the Newton step, made total by `by_cases` so that it can be iterated by `Nat.rec`
  have step : ∀ (k : ℕ) (x : Polynomial R × Polynomial R),
      ∃ y : Polynomial R × Polynomial R,
        (x.1.Monic ∧ x.1.map (residue R) = g₀ ∧ x.2.degree ≤ (l : WithBot ℕ) ∧
            x.2.map (residue R) = h₀ ∧
            f - x.1 * x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1))) →
          (y.1.Monic ∧ y.1.map (residue R) = g₀ ∧ y.2.degree ≤ (l : WithBot ℕ) ∧
            y.2.map (residue R) = h₀ ∧
            f - y.1 * y.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1))) ∧
          y.1 - x.1 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) ∧
          y.2 - x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) := by
    intro k x
    by_cases hx : x.1.Monic ∧ x.1.map (residue R) = g₀ ∧ x.2.degree ≤ (l : WithBot ℕ) ∧
        x.2.map (residue R) = h₀ ∧ f - x.1 * x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1))
    · obtain ⟨hx1, hx5, hx3, hx6, hx7⟩ := hx
      have hx2 : x.1.natDegree = m := natDegree_eq_of_map_eq hx1 hx5
      obtain ⟨δG, δH, hδGdeg, hδHdeg, hδGmem, hδHmem, herr⟩ :=
        exists_solve_step_of_monic_left hg₀ hcop hh₀ hG₁map hH₁map (k + 1) hx7
          (hdeglt x hx1 hx2 hx3)
      have hx1deg : x.1.degree = (m : WithBot ℕ) := by
        rw [degree_eq_natDegree hx1.ne_zero, hx2]
      have hmle : maximalIdeal R ^ (k + 1) ≤ maximalIdeal R := by
        simpa using Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.succ_le_succ (Nat.zero_le k))
      have hδGm : δG ∈ coeffIdeal (maximalIdeal R) := coeffIdeal_mono hmle hδGmem
      have hδHm : δH ∈ coeffIdeal (maximalIdeal R) := coeffIdeal_mono hmle hδHmem
      refine ⟨(x.1 + δG, x.2 + δH), fun _ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
      · exact hx1.add_of_left (by rw [hx1deg]; exact hδGdeg)
      · have h0 : δG.map (residue R) = 0 := map_residue_eq_zero_iff.mpr hδGm
        simp [Polynomial.map_add, h0, hx5]
      · exact le_trans (degree_add_le _ _) (max_le hx3 hδHdeg)
      · have h0 : δH.map (residue R) = 0 := map_residue_eq_zero_iff.mpr hδHm
        simp [Polynomial.map_add, h0, hx6]
      · -- the error recursion, verbatim from the monic case
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
  have hInvA : ∀ k, (A k).1.Monic ∧ (A k).1.map (residue R) = g₀ ∧
      (A k).2.degree ≤ (l : WithBot ℕ) ∧ (A k).2.map (residue R) = h₀ ∧
      f - (A k).1 * (A k).2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) := by
    intro k
    induction k with
    | zero => rw [hA0]; exact ⟨hG₁mon, hG₁map, hH₁deg, hH₁map, hbase⟩
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
  -- pass to the limit: the monic side on its tail, the cofactor side DIRECTLY (fixed budget)
  have htail1 : ∀ k, ((A k).1 - X ^ m).degree < (m : WithBot ℕ) := by
    intro k
    have h1 := (hInvA k).1
    have h2 : (A k).1.natDegree = m := natDegree_eq_of_map_eq h1 (hInvA k).2.1
    have := degree_sub_lt_of_monic_of_natDegree_eq h1 (monic_X_pow (R := R) m)
      (by rw [h2, natDegree_X_pow])
    rwa [h2] at this
  obtain ⟨TG, hTGdeg, hTGlim⟩ := exists_adicLimit_of_degree_lt m
    (fun k => (A k).1 - X ^ m) htail1 (by intro k; simpa using hstepA1 k)
  obtain ⟨H, hHdeglt, hHlim⟩ := exists_adicLimit_of_degree_lt (l + 1)
    (fun k => (A k).2) (fun k => degree_lt_succ_of_degree_le (hInvA k).2.2.1) hstepA2
  set G : Polynomial R := X ^ m + TG with hGdef
  have hGmon : G.Monic := (monic_X_pow _).add_of_left (by rwa [degree_X_pow])
  have hGdeg : G.natDegree = m := by
    have : G.degree = (m : WithBot ℕ) := by
      rw [hGdef, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  have hGlim : ∀ k, G - (A k).1 ∈ coeffIdeal (maximalIdeal R ^ k) := by
    intro k
    have h0 := hTGlim k
    have hid : G - (A k).1 = TG - ((A k).1 - X ^ m) := by rw [hGdef]; ring
    rw [hid]; exact h0
  have hGmap : G.map (residue R) = g₀ := by
    have h1 := hGlim 1
    rw [pow_one, sub_mem_coeffIdeal_maximalIdeal_iff] at h1
    rw [h1]
    exact (hInvA 1).2.1
  have hHmap : H.map (residue R) = h₀ := by
    have h1 := hHlim 1
    rw [pow_one, sub_mem_coeffIdeal_maximalIdeal_iff] at h1
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
  exact ⟨G, H, hGmon, hGdeg, degree_le_of_degree_lt_succ hHdeglt, sub_eq_zero.mp hzero,
    hGmap, hHmap⟩

/-- **THE MISSING INPUT of `ChapH/H116.lean`**, in the exact shape its module docstring quotes.
Over a complete local ring, a coprime residual split of `f.map (residue R)` with a MONIC left
factor lifts to a factorization of `f` with a monic left factor of the same degree — `f` itself
need not be monic.

The budget is discharged at `l = f.natDegree - g₀.natDegree`; the inequality `g₀.natDegree ≤
f.natDegree` that makes this legitimate is proved inline (it is forced by the split, using
coprimality in the degenerate case `h₀ = 0`). -/
theorem exists_monic_factorization_of_monic_left {f : Polynomial R}
    {g₀ h₀ : Polynomial (ResidueField R)} (hg₀ : g₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hfgh : f.map (residue R) = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ f = g * h ∧ g.natDegree = g₀.natDegree ∧
      g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ := by
  have hle : g₀.natDegree ≤ f.natDegree := by
    by_cases hh0 : h₀ = 0
    · subst hh0
      rw [hg₀.eq_one_of_isUnit (isCoprime_zero_right.mp hcop), natDegree_one]
      exact Nat.zero_le _
    · have h1 : (g₀ * h₀).natDegree = g₀.natDegree + h₀.natDegree :=
        natDegree_mul hg₀.ne_zero hh0
      have h2 : (f.map (residue R)).natDegree ≤ f.natDegree := natDegree_map_le
      rw [hfgh, h1] at h2
      omega
  obtain ⟨g, h, hgm, hgd, -, hfe, hgr, hhr⟩ :=
    exists_monic_factorization_of_degree_le hg₀ hcop hfgh
      (l := f.natDegree - g₀.natDegree)
      (by
        rw [show g₀.natDegree + (f.natDegree - g₀.natDegree) = f.natDegree by omega]
        exact degree_le_natDegree)
  exact ⟨g, h, hgm, hfe, hgd, hgr, hhr⟩

end Main

end Hensel

end Uniformity

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Hensel.exists_solve_field_of_monic_left
#print axioms Uniformity.Hensel.exists_solve_mod_of_monic_left
#print axioms Uniformity.Hensel.exists_solve_step_of_monic_left
#print axioms Uniformity.Hensel.exists_monic_factorization_of_degree_le
#print axioms Uniformity.Hensel.exists_monic_factorization_of_monic_left

end AxCheck
