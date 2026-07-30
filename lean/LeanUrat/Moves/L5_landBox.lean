/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L0_GRg
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L3_liftResidual
import LeanUrat.Moves.LaurentOrd
import LeanUrat.Moves.ResVal

/-!
# Moves/L5_landBox — the increment landing, BOX side (§B2 D.8, MOVES ~2318-2337)

On the descend stratum at ψ with multiplicity μ ≥ 1 — i.e. `f` with `ord_ψ R(f) = μ`, where
`R(f) = z^{a}·R_anch` with `R_anch ∈ ↥K[z]`, `R_anch(0) ≠ 0` — the Φ̂-development of `f` has every
slot `j < μ` strictly NON-minimizing:

  (BOX)  `w(f) < w(B_j) + j·(e·h·g)`   for `j < μ`.

## Proof structure

* `w(Φ̂) = e·h·g` (`ResVal.w_Phat`): Φ̂'s displayed formula IS a Φ-adic development all of whose
  nonzero slots have slot-weight `e·h·g`; the stage's own K1 axiom (`σ.hK1`) pins the attained
  minimum.
* Each slot term `B_j·Φ̂^j` (`B_j ≠ 0`) has residual of ψ-order EXACTLY `j` (`ordAt_term`):
  `R(B_j Φ̂^j) = R(B_j)·(z^{−thg}ψ)^j` by `L3_liftResidual`, and `ψ ∤ R(B_j)` at sub-Φ̂ width
  (`ResVal.psiNotDvd`).
* The minimizing-slot part of the development sums WITHOUT cancellation (`sum_min_ord`): terms of
  equal weight and pairwise-distinct ψ-orders — if a partial sum cancelled, `hRlt` would force
  `R(x_{j₀}) = R(−1)·R(rest)`, clashing with the distinct orders since `R(−1)² = 1`.  Hence
  `w(f) = min_j (w(B_j) + j·ehg)` and `ord_ψ R(f) =` the least minimizing slot.
* `ord_ψ R(f) = μ` read off the ANCHORED polynomial (`hanch`/`hord`, transported through
  `toLaurent` — `LaurentOrd.pow_dvd_of_toLaurent_pow_dvd`).  So the least minimizing slot is `μ`,
  and no slot `j < μ` is minimizing: `w(f) < w(B_j) + j·ehg`.  ∎

## SYN-M1 record (2026-07-30, C1 cluster)

The file-private engine copies (w_one … R_pow; OrdAt/ordAt_unique/ordAt_unit_mul/ordAt_add/
pow_dvd_of_toLaurent_pow_dvd; landBox_psiNotDvd; w_lift) are deleted in favor of
`Moves/LaurentOrd.lean` + `Moves/ResVal.lean` (SYN-E0 concordance:
`lean/notes/SYN_E0_CONCORDANCE_2026-07-30.md`). Per-conjunct equivalences: all statements
identical per the table except (a) `landBox_psiNotDvd` → `ResVal.psiNotDvd` (α-rename only),
(b) `w_lift` → `ResVal.w_Phat` (binder reorder + the `hg1 : 1 ≤ g` hypothesis, supplied at the
single call site from `hψ.natDegree_pos`; the unconsumed g = 0 strengthening of `w_lift` is
retired, SYN-E0 §3 VAR-S). File-specific lemmas (`ordAt_anchor`, `ordAt_term`, `sum_min_ord`,
`sum_rest`) stay. Public statement `L5_landBox` byte-identical.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.Moves

open Polynomial LaurentOrd ResVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## ψ-adic order at a fixed exponent, over the Laurent ring -/

/-- ψ-order of an anchored Laurent element: `x = z^a·R_anch` with `ord_ψ(R_anch) = μ` (as
polynomials) has `OrdAt (ψ) x μ` in the Laurent ring. -/
private lemma ordAt_anchor (σ : Stage p F) {ψ : Polynomial ↥σ.K}
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    {x : LaurentPolynomial ↥σ.K} {a : ℤ} {Ranch : Polynomial ↥σ.K} {μ : ℕ}
    (hanch : x = LaurentPolynomial.T a * Polynomial.toLaurent Ranch)
    (hord : OrdPsiPoly ψ Ranch μ) : OrdAt (Polynomial.toLaurent ψ) x μ := by
  constructor
  · have h1 : (Polynomial.toLaurent ψ) ^ μ ∣ Polynomial.toLaurent Ranch := by
      rw [← map_pow]
      exact map_dvd _ hord.1
    rw [hanch]
    exact h1.mul_left _
  · intro hd
    rw [hanch] at hd
    have h2 := hd.mul_left (LaurentPolynomial.T (-a))
    rw [← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero,
      one_mul] at h2
    exact hord.2 (pow_dvd_of_toLaurent_pow_dvd hmon hψ hψz h2)

/-- Each nonzero slot term `B·Φ̂^i` has residual ψ-order exactly `i` (D.3(d) + D.5). -/
private lemma ordAt_term (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    {Φhat : Polynomial ℤ_[p]} (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (Bi : Polynomial ℤ_[p]) (hBi : Bi ≠ 0) (hBdeg : Bi.degree < Φhat.degree) (i : ℕ) :
    OrdAt (Polynomial.toLaurent ψ) (σ.R (Bi * Φhat ^ i)) i := by
  have hψL_ne : Polynomial.toLaurent ψ ≠ 0 := fun h0 =>
    hψ.ne_zero (Polynomial.toLaurent_injective (by rw [h0, map_zero]))
  have hBnd : Bi.natDegree < σ.e * g * σ.Φ.natDegree := by
    rw [← hΦd]
    exact Polynomial.natDegree_lt_natDegree hBi hBdeg
  have hnd := psiNotDvd σ ψ g hg hmon hψ hψz Bi hBi hBnd
  have hRterm : σ.R (Bi * Φhat ^ i)
      = σ.R Bi * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ i
          * (Polynomial.toLaurent ψ) ^ i := by
    rw [σ.hRmul _ _ hBi (pow_ne_zero i hΦne), R_pow σ Φhat hΦne i,
      L3_liftResidual σ ψ g Φhat hlift, mul_pow, ← mul_assoc]
  rw [hRterm]
  constructor
  · exact dvd_mul_left _ _
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hcancel : σ.R Bi * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ i
        = Polynomial.toLaurent ψ * c := by
      apply mul_right_cancel₀ (pow_ne_zero i hψL_ne)
      rw [hc]
      ring
    have hdvd2 : Polynomial.toLaurent ψ
        ∣ σ.R Bi * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ i := ⟨c, hcancel⟩
    have h2 := hdvd2.mul_right ((LaurentPolynomial.T (σ.t * (σ.h : ℤ) * (g : ℤ))) ^ i)
    rw [mul_assoc, ← mul_pow, ← LaurentPolynomial.T_add,
      show - σ.t * (σ.h : ℤ) * (g : ℤ) + σ.t * (σ.h : ℤ) * (g : ℤ) = 0 by ring,
      LaurentPolynomial.T_zero, one_pow, mul_one] at h2
    exact hnd h2
/-! ## The non-cancelling minimal-weight sum -/

/-- Sum of terms of equal stage-weight `m` whose residuals have pairwise-distinct ψ-orders
(order = slot index): the sum is nonzero, has weight `m`, and its residual has ψ-order the LEAST
slot.  Cancellation is impossible: it would force `R(x_{j₀}) = R(−1)·R(rest)` via `hRlt`, and
`R(−1)² = 1` preserves ψ-order, clashing with distinctness. -/
private lemma sum_min_ord (σ : Stage p F) (P : LaurentPolynomial ↥σ.K)
    (x : ℕ → Polynomial ℤ_[p]) (m : ℤ) :
    ∀ S : Finset ℕ, ∀ hS : S.Nonempty,
      (∀ j ∈ S, x j ≠ 0) → (∀ j ∈ S, σ.w (x j) = m) →
      (∀ j ∈ S, OrdAt P (σ.R (x j)) j) →
      (∑ j ∈ S, x j) ≠ 0 ∧ σ.w (∑ j ∈ S, x j) = m ∧
        OrdAt P (σ.R (∑ j ∈ S, x j)) (S.min' hS) := by
  classical
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS hne hw hord
    set j0 := S.min' hS with hj0def
    have hj0S : j0 ∈ S := S.min'_mem hS
    have hsum : ∑ j ∈ S, x j = x j0 + ∑ j ∈ S.erase j0, x j :=
      (Finset.add_sum_erase S x hj0S).symm
    rcases (S.erase j0).eq_empty_or_nonempty with hE | hNE
    · rw [hsum, hE, Finset.sum_empty, add_zero]
      exact ⟨hne j0 hj0S, hw j0 hj0S, hord j0 hj0S⟩
    · have hssub : S.erase j0 ⊂ S := Finset.erase_ssubset hj0S
      obtain ⟨hPne, hPw, hPord⟩ := ih (S.erase j0) hssub hNE
        (fun j hj => hne j (Finset.mem_of_mem_erase hj))
        (fun j hj => hw j (Finset.mem_of_mem_erase hj))
        (fun j hj => hord j (Finset.mem_of_mem_erase hj))
      set Ps := ∑ j ∈ S.erase j0, x j with hPsdef
      set j1 := (S.erase j0).min' hNE with hj1def
      have hj1S' : j1 ∈ S.erase j0 := Finset.min'_mem _ hNE
      have hj01 : j0 < j1 := by
        have h1 : j0 ≤ j1 := Finset.min'_le S j1 (Finset.mem_of_mem_erase hj1S')
        have h2 : j1 ≠ j0 := Finset.ne_of_mem_erase hj1S'
        omega
      have hx0ne : x j0 ≠ 0 := hne j0 hj0S
      have hclash : σ.R (x j0) ≠ σ.R (-1) * σ.R Ps := by
        intro h
        have h1 : OrdAt P (σ.R (-1) * σ.R Ps) j1 := ordAt_unit_mul (R_neg_one_sq σ) hPord
        rw [← h] at h1
        exact absurd (ordAt_unique (hord j0 hj0S) h1) (by omega)
      have hXP : x j0 + Ps ≠ 0 := by
        intro h0
        apply hclash
        rw [eq_neg_of_add_eq_zero_left h0, neg_eq_neg_one_mul,
          σ.hRmul (-1) Ps (neg_ne_zero.mpr one_ne_zero) hPne]
      have hwXP : σ.w (x j0 + Ps) = m := by
        have hge : m ≤ σ.w (x j0 + Ps) := by
          have h := σ.hwult (x j0) Ps hx0ne hPne hXP
          rw [hw j0 hj0S, hPw, min_self] at h
          exact h
        rcases lt_or_eq_of_le hge with hlt | heq2
        · exfalso
          apply hclash
          have hnegne : -Ps ≠ 0 := neg_ne_zero.mpr hPne
          have hwneg : σ.w (-Ps) = m := (w_neg σ Ps hPne).trans hPw
          have hRlt := σ.hRlt (-Ps) (x j0 + Ps) hnegne hXP
            (by rw [show -Ps + (x j0 + Ps) = x j0 by ring]; exact hx0ne)
            (by rw [hwneg]; exact hlt)
          rw [show -Ps + (x j0 + Ps) = x j0 by ring] at hRlt
          rw [hRlt, neg_eq_neg_one_mul, σ.hRmul (-1) Ps (neg_ne_zero.mpr one_ne_zero) hPne]
        · exact heq2.symm
      have hRXP : σ.R (x j0 + Ps) = σ.R (x j0) + σ.R Ps :=
        σ.hRadd (x j0) Ps hx0ne hPne hXP (by rw [hw j0 hj0S, hPw]) (by rw [hwXP, hw j0 hj0S])
      refine ⟨?_, ?_, ?_⟩
      · rw [hsum]
        exact hXP
      · rw [hsum]
        exact hwXP
      · rw [hsum, hRXP]
        exact ordAt_add (hord j0 hj0S) hPord hj01

/-- Sum of terms all of weight `> m` is zero or of weight `> m`. -/
private lemma sum_rest (σ : Stage p F) (x : ℕ → Polynomial ℤ_[p]) (m : ℤ) (T : Finset ℕ)
    (hne : ∀ i ∈ T, x i ≠ 0) (hw : ∀ i ∈ T, m < σ.w (x i)) :
    (∑ i ∈ T, x i) = 0 ∨ ((∑ i ∈ T, x i) ≠ 0 ∧ m < σ.w (∑ i ∈ T, x i)) := by
  classical
  induction T using Finset.induction_on with
  | empty => left; simp
  | @insert a T' haT' ih =>
    have hane : x a ≠ 0 := hne a (Finset.mem_insert_self a T')
    have hawe : m < σ.w (x a) := hw a (Finset.mem_insert_self a T')
    have hsum : ∑ i ∈ insert a T', x i = x a + ∑ i ∈ T', x i := Finset.sum_insert haT'
    rcases ih (fun i hi => hne i (Finset.mem_insert_of_mem hi))
        (fun i hi => hw i (Finset.mem_insert_of_mem hi)) with h0 | ⟨hT'ne, hT'w⟩
    · right
      rw [hsum, h0, add_zero]
      exact ⟨hane, hawe⟩
    · by_cases hz : x a + ∑ i ∈ T', x i = 0
      · left
        rw [hsum]
        exact hz
      · right
        refine ⟨by rw [hsum]; exact hz, ?_⟩
        rw [hsum]
        have h := σ.hwult (x a) _ hane hT'ne hz
        exact lt_of_lt_of_le (lt_min hawe hT'w) h

/-! ## The theorem -/

theorem L5_landBox {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ) (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) (j : ℕ) (hj : j < μ) (hjnz : B j ≠ 0) : σ.w f < σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
  classical
  -- the slot lies in range
  have hjN : j < N := by
    by_contra h
    exact hjnz (hdev.2.1 j (not_lt.mp h))
  have hg1 : 1 ≤ g := by
    have := hψ.natDegree_pos
    omega
  obtain ⟨hΦm, hΦd⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦne : Φhat ≠ 0 := hΦm.ne_zero
  have hwhat : σ.w Φhat = (σ.e : ℤ) * σ.h * g := w_Phat σ ψ g (by have := hψ.natDegree_pos; omega) Φhat hlift hΦne
  -- the nonzero-slot set
  set S : Finset ℕ := (Finset.range N).filter (fun i => B i ≠ 0) with hSdef
  have hjS : j ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨hjN, hjnz⟩
  -- slot weights
  have hxw : ∀ i ∈ S, σ.w (B i * Φhat ^ i)
      = σ.w (B i) + (i : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro i hi
    rw [hSdef, Finset.mem_filter] at hi
    rw [σ.hwmul _ _ hi.2 (pow_ne_zero i hΦne), w_pow σ Φhat hΦne i, hwhat]
  -- slot-term ψ-orders
  have hxord : ∀ i ∈ S, OrdAt (Polynomial.toLaurent ψ) (σ.R (B i * Φhat ^ i)) i := by
    intro i hi
    rw [hSdef, Finset.mem_filter] at hi
    exact ordAt_term σ hg hmon hψ hψz hlift hΦne hΦd (B i) hi.2 (hdev.1 i) i
  -- the attained minimum slot weight
  obtain ⟨i0, hi0S, hi0min⟩ :=
    S.exists_min_image (fun i => σ.w (B i) + (i : ℤ) * ((σ.e : ℤ) * σ.h * g)) ⟨j, hjS⟩
  set m : ℤ := σ.w (B i0) + (i0 : ℤ) * ((σ.e : ℤ) * σ.h * g) with hmdef
  have hi0min' : ∀ i ∈ S, m ≤ σ.w (B i) + (i : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro i hi
    rw [hmdef]
    exact hi0min i hi
  set Smin : Finset ℕ :=
    S.filter (fun i => σ.w (B i) + (i : ℤ) * ((σ.e : ℤ) * σ.h * g) = m) with hSmindef
  have hSminsub : Smin ⊆ S := by
    rw [hSmindef]
    exact Finset.filter_subset _ _
  have hSminne : Smin.Nonempty := by
    refine ⟨i0, ?_⟩
    rw [hSmindef, Finset.mem_filter]
    exact ⟨hi0S, by rw [hmdef]⟩
  -- f as the S-sum
  have hfS : f = ∑ i ∈ S, B i * Φhat ^ i := by
    rw [hdev.2.2, hSdef]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro i _ hterm hB0
    exact hterm (by rw [hB0, zero_mul])
  have hfsplit : f = (∑ i ∈ Smin, B i * Φhat ^ i) + ∑ i ∈ S \ Smin, B i * Φhat ^ i := by
    rw [hfS, ← Finset.sum_sdiff hSminsub]
    exact add_comm _ _
  -- the minimal part
  obtain ⟨hFne, hFw, hFord⟩ := sum_min_ord σ (Polynomial.toLaurent ψ)
      (fun i => B i * Φhat ^ i) m Smin hSminne
      (fun i hi => by
        have hiS := hSminsub hi
        rw [hSdef, Finset.mem_filter] at hiS
        exact mul_ne_zero hiS.2 (pow_ne_zero i hΦne))
      (fun i hi => by
        have hiS := hSminsub hi
        rw [hSmindef, Finset.mem_filter] at hi
        rw [hxw i hiS]
        exact hi.2)
      (fun i hi => hxord i (hSminsub hi))
  -- the rest
  have hrest := sum_rest σ (fun i => B i * Φhat ^ i) m (S \ Smin)
      (fun i hi => by
        rw [Finset.mem_sdiff] at hi
        have hiS := hi.1
        rw [hSdef, Finset.mem_filter] at hiS
        exact mul_ne_zero hiS.2 (pow_ne_zero i hΦne))
      (fun i hi => by
        rw [Finset.mem_sdiff] at hi
        rw [hxw i hi.1]
        rcases lt_or_eq_of_le (hi0min' i hi.1) with h | h
        · exact h
        · exact absurd (by
            rw [hSmindef, Finset.mem_filter]
            exact ⟨hi.1, h.symm⟩) hi.2)
  -- w f = m and R f = R (min part)
  have hfw_and : σ.w f = m ∧ σ.R f = σ.R (∑ i ∈ Smin, B i * Φhat ^ i) := by
    rcases hrest with h0 | ⟨hRne0, hRgt⟩
    · rw [hfsplit, h0, add_zero]
      exact ⟨hFw, rfl⟩
    · have hfsum_ne : (∑ i ∈ Smin, B i * Φhat ^ i) + ∑ i ∈ S \ Smin, B i * Φhat ^ i ≠ 0 := by
        rw [← hfsplit]
        exact hf
      constructor
      · have hge : m ≤ σ.w f := by
          have h := σ.hwult _ _ hFne hRne0 hfsum_ne
          rw [hFw, min_eq_left hRgt.le, ← hfsplit] at h
          exact h
        have hle2 : σ.w f ≤ m := by
          by_contra hgt
          rw [not_le] at hgt
          have hkey : (∑ i ∈ Smin, B i * Φhat ^ i)
              = f + -(∑ i ∈ S \ Smin, B i * Φhat ^ i) := by
            rw [hfsplit]
            ring
          have hnegne : -(∑ i ∈ S \ Smin, B i * Φhat ^ i) ≠ 0 := neg_ne_zero.mpr hRne0
          have h := σ.hwult f _ hf hnegne (by rw [← hkey]; exact hFne)
          rw [← hkey, hFw, w_neg σ _ hRne0] at h
          have h2 : m < min (σ.w f) (σ.w (∑ i ∈ S \ Smin, B i * Φhat ^ i)) :=
            lt_min hgt hRgt
          omega
        exact le_antisymm hle2 hge
      · rw [hfsplit]
        exact σ.hRlt _ _ hFne hRne0 hfsum_ne (by rw [hFw]; exact hRgt)
  -- ψ-order of R f, two ways
  have hordf_min : OrdAt (Polynomial.toLaurent ψ) (σ.R f) (Smin.min' hSminne) := by
    rw [hfw_and.2]
    exact hFord
  have hordf_mu : OrdAt (Polynomial.toLaurent ψ) (σ.R f) μ :=
    ordAt_anchor σ hmon hψ hψz hanch.2 hord
  have hminμ : Smin.min' hSminne = μ := ordAt_unique hordf_min hordf_mu
  -- conclude: weak bound + strictness
  have hle : σ.w f ≤ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    rw [hfw_and.1]
    exact hi0min' j hjS
  have hne2 : σ.w f ≠ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro heq
    have hjmin : j ∈ Smin := by
      rw [hSmindef, Finset.mem_filter]
      exact ⟨hjS, by rw [← heq]; exact hfw_and.1⟩
    have h := Finset.min'_le Smin j hjmin
    rw [hminμ] at h
    omega
  exact lt_of_le_of_ne hle hne2

end LeanUrat.Moves
