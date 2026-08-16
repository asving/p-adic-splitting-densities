/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B40
import Uniformity.ChapB.B41a

/-!
# Uniformity.ChapB.B41b — NODE B.41, the graded factorization

**Chapter B, NODE B.41** `exists_graded_factorization` (`blueprint/CHAP-B_leaf_layer.md` §6),
ENV-C.

**⚠ ENVIRONMENT NOTE (a 0e-gate finding).** The landed declaration carries
`[IsAdicComplete (maximalIdeal O) O]` — it must, because the limit step is B.40's
`exists_graded_limit`, and without completeness the statement is **false** (it implies Hensel's
lemma, which characterises henselian DVRs). The `leanspec` stub for this node carries **no**
instance at all: `axiom`s drop section instances their *statement* does not mention, and B.41's
statement does not mention completeness. So the 0e type diff for this node must be adjudicated
against the **landed B.40 precedent** (`Uniformity/ChapB/B40.lean`, whose landed type also
carries `[IsAdicComplete …]` while its stub does not), *not* by `omit`ting the instance — an
`omit` here would make the node unprovable. The same applies to B.48 (which needs both
completeness, via this node, and `[Finite (ResidueField O)]`, via B.45), so the §12 rule-7
`omit` rider recorded at A-F.8/A-F.9 is wrong for B.48.

**⚠ This node consumes B.39 at its `R3`-repaired signature** (`B39b.lean`): the level
hypothesis `hc` is discharged here from `suppVal φ (g_k * h_k) u ℓ = suppVal φ f u ℓ < c_k`.

## The route (blueprint steps 1–5)

1. `exists_monic_pure_lift` (B41a) gives the initial approximation `g₀`, `h₀` — monic, pure, of
   the pinned degrees, with residual polynomials `G`, `H`.
2. The unit of `hprod` is forced to `1` by monicity, so `resPoly f = G * H`; then
   `resPoly (g₀ * h₀) = G * H` too (landed B.35), so the level detector of B41a lifts the error
   `f − g₀h₀` one level above `suppVal φ f u ℓ`.
3. The Newton step is B.39; the perturbation law of B41a keeps every iterate monic, pure, of
   fixed degree and residual polynomial.
4. B.40 passes the two tails `g_k − φ^(ℓa)`, `h_k − φ^(ℓb)` to the limit.
5. The limit's residual data is the iterates' (the perturbation law again), and `f = g·h`
   because the error has infinite weight (`eq_zero_of_suppVal_eq_top`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. The polygon of `1`, and two `ℕ∞` conveniences -/

section One

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- The polygon of `1` is the single point `(0,0)`. -/
theorem npHgt_one (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    npHgt φ (1 : Polynomial O) 0 = 0 := by
  have hone : (1 : Polynomial O).degree < φ.degree := by
    rw [Polynomial.degree_one]
    exact Polynomial.natDegree_pos_iff_degree_pos.1 hd
  have hdev : dev φ (1 : Polynomial O) 0 = 1 :=
    (Polynomial.modByMonic_eq_self_iff hφ).2 hone
  rw [npHgt, hdev, gaussVal, Polynomial.natDegree_one, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_one_zero]
  exact AddValuation.map_one _

/-- `1` has weight `0`. -/
theorem suppVal_one (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ) :
    suppVal φ (1 : Polynomial O) u ℓ = 0 := by
  refine le_antisymm ?_ (by simp)
  refine le_trans (suppVal_le_weight hφ hd hℓ u 1 0) ?_
  rw [npHgt_one hφ hd]
  simp

/-- `1` is `(u,ℓ)`-pure. -/
theorem isPure_one (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ) :
    IsPure φ (1 : Polynomial O) u ℓ := by
  have hon : OnSide φ (1 : Polynomial O) u ℓ 0 := by
    show ℓ • npHgt φ (1 : Polynomial O) 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ (1 : Polynomial O) u ℓ
    rw [npHgt_one hφ hd, suppVal_one hφ hd hℓ]
    simp
  refine ⟨hon, ?_⟩
  rw [Polynomial.natDegree_one, Nat.zero_div]
  exact hon

/-- The residual polynomial of `1` is `1`. -/
theorem resPoly_one (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hne : (sideSet φ (1 : Polynomial O) u ℓ).Nonempty) :
    resPoly π φ (1 : Polynomial O) u ℓ hne 0 = 1 := by
  classical
  have hall : ∀ x ∈ sideSet φ (1 : Polynomial O) u ℓ, x = 0 := by
    intro x hx
    have hx' : x ∈ Finset.filter (OnSide φ (1 : Polynomial O) u ℓ)
      (Finset.range ((1 : Polynomial O).natDegree + 1)) := hx
    have := Finset.mem_range.1 (Finset.mem_filter.1 hx').1
    rw [Polynomial.natDegree_one] at this
    omega
  have hmin : sideMin φ (1 : Polynomial O) u ℓ hne = 0 :=
    hall _ (Finset.min'_mem _ hne)
  have hmax : sideMax φ (1 : Polynomial O) u ℓ hne = 0 :=
    hall _ (Finset.max'_mem _ hne)
  have hsd : sideDeg φ (1 : Polynomial O) u ℓ hne = 0 := by rw [sideDeg, hmin, hmax]; simp
  have hdev : dev φ (1 : Polynomial O) 0 = 1 :=
    (Polynomial.modByMonic_eq_self_iff hφ).2 (by
      rw [Polynomial.degree_one]; exact Polynomial.natDegree_pos_iff_degree_pos.1 hd)
  rw [resPoly, hsd, Finset.sum_range_one, pow_zero, mul_one, resCoeff, hmin]
  show Polynomial.C (resMk π φ (0 - u * 0) (dev φ (1 : Polynomial O) (0 + ℓ * 0))) = 1
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  rw [hdev, resMk_one hπ, Polynomial.C_1]

end One

/-! ## 2. Two `ℕ∞` conveniences -/

/-- Cancelling a finite summand on the right of a cast inequality. -/
theorem le_sub_of_natCast_add_le {S T : ℕ} {x : ℕ∞}
    (h : ((S : ℕ) : ℕ∞) ≤ ((T : ℕ) : ℕ∞) + x) : ((S - T : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hv] at h ⊢
  have : S ≤ T + v := by exact_mod_cast h
  exact_mod_cast (by omega : S - T ≤ v)

/-- An element of `ℕ∞` above every natural is `⊤`. -/
theorem eq_top_of_forall_natCast_le {x : ℕ∞} (h : ∀ k : ℕ, ((k : ℕ) : ℕ∞) ≤ x) : x = ⊤ := by
  by_contra hT
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hT
  have := h (v + 1)
  rw [← hv] at this
  have : v + 1 ≤ v := by exact_mod_cast this
  omega

/-! ## 3. The perturbation law, in equation form -/

section Perturb

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- `pure_add_of_lt` (B41a) with the perturbed polynomial given by an **equation** `z = x + y`
rather than syntactically as a sum. The limit step needs this form: `z` there is the adic limit
`X ^ deg + T`, and rewriting `x + y` into `z` inside the residual clause is not a legal `rw`
(the clause binds `hne : (sideSet φ (x + y) u ℓ).Nonempty`, so the rewrite is dependent). -/
theorem pure_of_add_eq (hπ : Irreducible π) (hφ : IsKey φ) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {x y z : Polynomial O} {n : ℕ}
    (hx : x.Monic) (hxdeg : x.natDegree = ℓ * n * φ.natDegree) (hxp : IsPure φ x u ℓ)
    (hxne : (sideSet φ x u ℓ).Nonempty) {Hx : ℕ} (hHx : npHgt φ x 0 = (Hx : ℕ∞))
    (hydeg : y.degree < x.degree)
    (hy : ((ℓ * Hx + 1 : ℕ) : ℕ∞) ≤ suppVal φ y u ℓ) (hz : z = x + y) :
    z.Monic ∧ z.natDegree = x.natDegree ∧ IsPure φ z u ℓ ∧
      npHgt φ z 0 = (Hx : ℕ∞) ∧
      ∀ hne : (sideSet φ z u ℓ).Nonempty,
        resPoly π φ z u ℓ hne Hx = resPoly π φ x u ℓ hxne Hx := by
  subst hz
  exact pure_add_of_lt hπ hφ hℓ hcop hx hxdeg hxp hxne hHx hydeg hy

end Perturb

/-! ## 4. NODE B.41 — the graded factorization -/

section ENVC

variable [IsAdicComplete (maximalIdeal O) O]

/-- **B.41 — the graded factorization (the engine).** A coprime factorization of the residual
polynomial of a monic `(u,ℓ)`-pure `f` of `φ.natDegree`-divisible degree lifts to a
factorization of `f` into monic `(u,ℓ)`-pure, `(u,ℓ)`-coprime factors of the pinned degrees. -/
theorem exists_graded_factorization (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O}
    (hf : f.Monic) (hfd : φ.natDegree ∣ f.natDegree)
    (hpure : IsPure φ f u ℓ) {H₀ : ℕ} (hH₀ : npHgt φ f 0 = (H₀ : ℕ∞))
    (hne : (sideSet φ f u ℓ).Nonempty)
    {G H : Polynomial (resField φ)} (hG : G.Monic) (hH : H.Monic) (hGH : IsCoprime G H)
    (hprod : ∃ c : (resField φ)ˣ,
      resPoly π φ f u ℓ hne H₀ = Polynomial.C (c : resField φ) * (G * H)) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.natDegree = ℓ * φ.natDegree * G.natDegree ∧
      h.natDegree = ℓ * φ.natDegree * H.natDegree ∧
      IsPure φ g u ℓ ∧ IsPure φ h u ℓ ∧ GradedCoprime π φ u ℓ g h := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  set a := G.natDegree with hadef
  set b := H.natDegree with hbdef
  -- ## f's side data
  have hfdeg0 : f.natDegree = (f.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hfd).symm
  have htf : suppVal φ f u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ.monic hφ.pos hf hfdeg0 hpure]; exact ENat.coe_ne_top _
  have hfmin : sideMin φ f u ℓ hne = 0 := sideMin_of_pure hpure hne
  have hHf : npHgt φ f (sideMin φ f u ℓ hne) = (H₀ : ℕ∞) := by rw [hfmin]; exact hH₀
  have hdl : ℓ * sideDeg φ f u ℓ hne = f.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hpure hne
  set dd := sideDeg φ f u ℓ hne with hdddef
  have hfdegd : f.natDegree = ℓ * dd * φ.natDegree := by rw [hdl]; exact hfdeg0
  have hH₀d : H₀ = u * dd := height_eq_of_pure hφ.monic hφ.pos hf hfdegd hℓ hcop hpure hne hH₀
  have hRfdeg : (resPoly π φ f u ℓ hne H₀).natDegree = dd :=
    (natDegree_resPoly hπ hφ hℓ hcop htf hne hHf).1
  have hRf0 : (resPoly π φ f u ℓ hne H₀).coeff 0 ≠ 0 :=
    (natDegree_resPoly hπ hφ hℓ hcop htf hne hHf).2
  have hRfmonic : (resPoly π φ f u ℓ hne H₀).Monic := by
    show (resPoly π φ f u ℓ hne H₀).coeff (resPoly π φ f u ℓ hne H₀).natDegree = 1
    rw [hRfdeg, resPoly_coeff_of_pure hπ hφ.monic hφ.pos hf hfdegd hℓ hcop hpure hne H₀ dd,
      hH₀d, Nat.sub_self, dev_top hφ.monic hφ.pos hf (μ := ℓ * dd) hfdegd, resMk_one hπ]
  -- ## the unit of `hprod` is `1`
  obtain ⟨cu, hcu⟩ := hprod
  have hGHmonic : (G * H).Monic := hG.mul hH
  have hGHdeg : (G * H).natDegree = a + b := by
    rw [Polynomial.natDegree_mul hG.ne_zero hH.ne_zero]
  have hCcne : (Polynomial.C (cu : resField φ)) ≠ 0 :=
    Polynomial.C_ne_zero.2 (Units.ne_zero cu)
  have hddab : dd = a + b := by
    rw [← hRfdeg, hcu, Polynomial.natDegree_mul hCcne hGHmonic.ne_zero, Polynomial.natDegree_C,
      hGHdeg, Nat.zero_add]
  have hcu1 : (cu : resField φ) = 1 := by
    have h1 : (resPoly π φ f u ℓ hne H₀).coeff dd = 1 := by
      rw [← hRfdeg]; exact hRfmonic.coeff_natDegree
    have h2 : (G * H).coeff (a + b) = 1 := by rw [← hGHdeg]; exact hGHmonic.coeff_natDegree
    rw [hcu, Polynomial.coeff_C_mul, hddab, h2, mul_one] at h1
    exact h1
  have hresf : resPoly π φ f u ℓ hne H₀ = G * H := by
    rw [hcu, hcu1, Polynomial.C_1, one_mul]
  have hG0 : G.coeff 0 ≠ 0 := by
    intro hz
    exact hRf0 (by rw [hresf, Polynomial.mul_coeff_zero, hz, zero_mul])
  have hH0 : H.coeff 0 ≠ 0 := by
    intro hz
    exact hRf0 (by rw [hresf, Polynomial.mul_coeff_zero, hz, mul_zero])
  -- ## the degenerate cases: one residual factor is `1`
  have hone : (sideSet φ (1 : Polynomial O) u ℓ).Nonempty :=
    sideSet_nonempty_gen φ (1 : Polynomial O) u ℓ
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · refine ⟨1, f, monic_one, hf, (one_mul f).symm, ?_, ?_,
      isPure_one hφ.monic hφ.pos hℓ, hpure,
      ⟨0, H₀, hone, hne, npHgt_one hφ.monic hφ.pos, hH₀,
        isPure_one hφ.monic hφ.pos hℓ, hpure, ?_⟩⟩
    · rw [Polynomial.natDegree_one, ha0, Nat.mul_zero]
    · rw [hfdegd, hddab, ha0, Nat.zero_add]; ring
    · rw [resPoly_one hπ hφ.monic hφ.pos]
      exact isCoprime_one_left
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · refine ⟨f, 1, hf, monic_one, (mul_one f).symm, ?_, ?_, hpure,
      isPure_one hφ.monic hφ.pos hℓ,
      ⟨H₀, 0, hne, hone, hH₀, npHgt_one hφ.monic hφ.pos, hpure,
        isPure_one hφ.monic hφ.pos hℓ, ?_⟩⟩
    · rw [hfdegd, hddab, hb0, Nat.add_zero]; ring
    · rw [Polynomial.natDegree_one, hb0, Nat.mul_zero]
    · rw [resPoly_one hπ hφ.monic hφ.pos]
      exact isCoprime_one_right
  -- ## the main case: both residual factors have positive degree
  set Sf := u * (ℓ * dd) with hSfdef
  have hfsupp : suppVal φ f u ℓ = ((Sf : ℕ) : ℕ∞) :=
    suppVal_of_pure hφ.monic hφ.pos hf hfdegd hpure
  have hSfsplit : Sf = ℓ * (u * a) + ℓ * (u * b) := by rw [hSfdef, hddab]; ring
  have hfpos : 0 < f.natDegree := by
    rw [hfdegd]
    exact Nat.mul_pos (Nat.mul_pos hℓ (by omega)) hφ.pos
  obtain ⟨g₀, hg₀m, hg₀deg, hg₀p, hg₀H, hg₀res⟩ :=
    exists_monic_pure_lift (u := u) hπ hφ hℓ hcop hG hG0
  obtain ⟨h₀, hh₀m, hh₀deg, hh₀p, hh₀H, hh₀res⟩ :=
    exists_monic_pure_lift (u := u) hπ hφ hℓ hcop hH hH0
  -- the invariant carried by the iteration
  set Inv : ℕ → Polynomial O × Polynomial O → Prop := fun k p =>
    p.1.Monic ∧ p.2.Monic ∧
    p.1.natDegree = ℓ * a * φ.natDegree ∧ p.2.natDegree = ℓ * b * φ.natDegree ∧
    IsPure φ p.1 u ℓ ∧ IsPure φ p.2 u ℓ ∧
    npHgt φ p.1 0 = ((u * a : ℕ) : ℕ∞) ∧ npHgt φ p.2 0 = ((u * b : ℕ) : ℕ∞) ∧
    (∀ hne1 : (sideSet φ p.1 u ℓ).Nonempty, resPoly π φ p.1 u ℓ hne1 (u * a) = G) ∧
    (∀ hne2 : (sideSet φ p.2 u ℓ).Nonempty, resPoly π φ p.2 u ℓ hne2 (u * b) = H) ∧
    ((Sf + k + 1 : ℕ) : ℕ∞) ≤ suppVal φ (f - p.1 * p.2) u ℓ with hInvdef
  -- ## the digits of a pure full-degree pair agree with those of `f`
  have hlattice : ∀ (j Hj : ℕ), ℓ * Hj + u * j = Sf → ∃ kk : ℕ, j = ℓ * kk ∧ Hj + u * kk = H₀ := by
    intro j Hj hj
    have hH₀Sf : ℓ * H₀ = Sf := by rw [hH₀d, hSfdef]; ring
    have hHjle : Hj ≤ H₀ := Nat.le_of_mul_le_mul_left (by omega) hℓ
    have hsub : ℓ * (H₀ - Hj) = ℓ * H₀ - ℓ * Hj := Nat.mul_sub ℓ H₀ Hj
    have hdvd : ℓ ∣ u * j := ⟨H₀ - Hj, by omega⟩
    obtain ⟨kk, hkk⟩ := (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcop) hdvd)
    refine ⟨kk, hkk, ?_⟩
    refine Nat.eq_of_mul_eq_mul_left hℓ ?_
    have h2 : u * (ℓ * kk) = ℓ * (u * kk) := by ring
    have h3 : ℓ * (Hj + u * kk) = ℓ * Hj + ℓ * (u * kk) := by ring
    rw [hkk] at hj
    omega
  -- ## the base case
  have hbase : Inv 0 (g₀, h₀) := by
    have hprodm : (g₀ * h₀).Monic := hg₀m.mul hh₀m
    have hproddeg : (g₀ * h₀).natDegree = ℓ * dd * φ.natDegree := by
      rw [Polynomial.natDegree_mul hg₀m.ne_zero hh₀m.ne_zero, hg₀deg, hh₀deg, hddab]; ring
    have hprodp : IsPure φ (g₀ * h₀) u ℓ :=
      isPure_mul_of_pure hπ hφ hu hℓ hcop hg₀m hh₀m hg₀deg hh₀deg hg₀p hh₀p hg₀H hh₀H rfl rfl
    have hprodH : npHgt φ (g₀ * h₀) 0 = ((u * a + u * b : ℕ) : ℕ∞) :=
      npHgt_mul_of_pure hπ hφ hu hℓ hcop hg₀m hh₀m hg₀deg hh₀deg hg₀p hh₀p hg₀H hh₀H rfl rfl
    have hprodsupp : suppVal φ (g₀ * h₀) u ℓ = ((Sf : ℕ) : ℕ∞) := by
      rw [suppVal_of_pure hφ.monic hφ.pos hprodm hproddeg hprodp, hSfdef]
    have hg₀ne : (sideSet φ g₀ u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hh₀ne : (sideSet φ h₀ u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hprodne : (sideSet φ (g₀ * h₀) u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hprodres : resPoly π φ (g₀ * h₀) u ℓ hprodne (u * a + u * b) = G * H := by
      rw [resPoly_mul_of_pure hπ hφ hu hℓ hcop hg₀m hh₀m
        (by rw [hg₀deg]; exact dvd_mul_left _ _) (by rw [hh₀deg]; exact dvd_mul_left _ _)
        hg₀p hh₀p hg₀H hh₀H hg₀ne hh₀ne hprodne, hg₀res hg₀ne, hh₀res hh₀ne]
    have hH₀ab : H₀ = u * a + u * b := by rw [hH₀d, hddab]; ring
    refine ⟨hg₀m, hh₀m, hg₀deg, hh₀deg, hg₀p, hh₀p, hg₀H, hh₀H, hg₀res, hh₀res, ?_⟩
    refine le_suppVal_succ_of_lineDigits_zero hπ hφ hℓ hcop ?_ ?_
    · rw [sub_eq_add_neg]
      refine le_trans (le_min ?_ ?_) (min_suppVal_le_suppVal_add hφ.monic hφ.pos hℓ u _ _)
      · rw [hfsupp]
      · rw [suppVal_neg hφ.monic, hprodsupp]
    · intro j Hj hj
      obtain ⟨kk, hkk, hHj⟩ := hlattice j Hj hj
      have bf : ((Hj : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j) := by
        have := le_lineDigit_gaussVal (u := u) hφ.monic hφ.pos hℓ (A := Hj) (r := j)
          (x := f) (t := 0) (by rw [hj, hfsupp])
        simpa using this
      have bp : ((Hj : ℕ) : ℕ∞) ≤ gaussVal (dev φ (g₀ * h₀) j) := by
        have := le_lineDigit_gaussVal (u := u) hφ.monic hφ.pos hℓ (A := Hj) (r := j)
          (x := g₀ * h₀) (t := 0) (by rw [hj, hprodsupp])
        simpa using this
      have hdf : resMk π φ Hj (dev φ f j)
          = (resPoly π φ f u ℓ hne H₀).coeff kk := by
        rw [resPoly_coeff_of_pure hπ hφ.monic hφ.pos hf hfdegd hℓ hcop hpure hne H₀ kk, hkk]
        congr 1
        omega
      have hdp : resMk π φ Hj (dev φ (g₀ * h₀) j)
          = (resPoly π φ (g₀ * h₀) u ℓ hprodne (u * a + u * b)).coeff kk := by
        rw [resPoly_coeff_of_pure hπ hφ.monic hφ.pos hprodm hproddeg hℓ hcop hprodp hprodne
          (u * a + u * b) kk, hkk]
        congr 1
        omega
      rw [sub_eq_add_neg, dev_add_of_monic hφ.monic, dev_neg hφ.monic,
        resMk_add hπ bf (by rw [gaussVal_neg]; exact bp), resMk_neg hπ bp, hdf, hdp, hresf,
        hprodres, add_neg_cancel]
  -- ## the Newton step
  have step : ∀ (k : ℕ) (p : Polynomial O × Polynomial O),
      ∃ q : Polynomial O × Polynomial O,
        Inv k p → Inv (k + 1) q ∧
          ((ℓ * (u * a) + k + 1 : ℕ) : ℕ∞) ≤ suppVal φ (q.1 - p.1) u ℓ ∧
          ((ℓ * (u * b) + k + 1 : ℕ) : ℕ∞) ≤ suppVal φ (q.2 - p.2) u ℓ := by
    intro k p
    by_cases hp : Inv k p
    · rw [hInvdef] at hp
      obtain ⟨hp1m, hp2m, hp1deg, hp2deg, hp1p, hp2p, hp1H, hp2H, hp1res, hp2res, herr⟩ := hp
      have hp1ne : (sideSet φ p.1 u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
      have hp2ne : (sideSet φ p.2 u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
      have hp1d : φ.natDegree ∣ p.1.natDegree := by rw [hp1deg]; exact dvd_mul_left _ _
      have hp2d : φ.natDegree ∣ p.2.natDegree := by rw [hp2deg]; exact dvd_mul_left _ _
      have hgc : GradedCoprime π φ u ℓ p.1 p.2 :=
        ⟨u * a, u * b, hp1ne, hp2ne, hp1H, hp2H, hp1p, hp2p, by
          rw [hp1res hp1ne, hp2res hp2ne]; exact hGH⟩
      have hprodm : (p.1 * p.2).Monic := hp1m.mul hp2m
      have hproddeg : (p.1 * p.2).natDegree = f.natDegree := by
        rw [Polynomial.natDegree_mul hp1m.ne_zero hp2m.ne_zero, hp1deg, hp2deg, hfdegd, hddab]
        ring
      have hedeg : (f - p.1 * p.2).natDegree < (p.1 * p.2).natDegree := by
        rw [hproddeg]
        by_cases hz : f - p.1 * p.2 = 0
        · rw [hz, Polynomial.natDegree_zero]; exact hfpos
        · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2
            (Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq hf hprodm hproddeg.symm)
      have hp1supp : suppVal φ p.1 u ℓ = ((u * (ℓ * a) : ℕ) : ℕ∞) :=
        suppVal_of_pure hφ.monic hφ.pos hp1m hp1deg hp1p
      have hp2supp : suppVal φ p.2 u ℓ = ((u * (ℓ * b) : ℕ) : ℕ∞) :=
        suppVal_of_pure hφ.monic hφ.pos hp2m hp2deg hp2p
      have hprodsupp : suppVal φ (p.1 * p.2) u ℓ = ((Sf : ℕ) : ℕ∞) := by
        rw [suppVal_mul_eq_of_pure hπ hφ hℓ hp1m hp2m hp1deg hp2deg hp1p hp2p, hSfdef, hddab]
        congr 1
        ring
      obtain ⟨U, V, hUdeg, hVdeg, hUw, hVw, herr'⟩ :=
        exists_graded_solve hπ hφ hu hℓ hcop hp1m hp2m hp1d hp2d hgc hedeg
          (c := Sf + k + 1) (by rw [hprodsupp]; exact_mod_cast (by omega : Sf ≤ Sf + k + 1)) herr
      -- the two weight bounds on the corrections
      have hUwt : ((ℓ * (u * a) + k + 1 : ℕ) : ℕ∞) ≤ suppVal φ U u ℓ := by
        rw [hp2supp] at hUw
        have := le_sub_of_natCast_add_le hUw
        refine le_trans ?_ this
        have harith : Sf + k + 1 - u * (ℓ * b) = ℓ * (u * a) + k + 1 := by
          have h1 : u * (ℓ * b) = ℓ * (u * b) := by ring
          omega
        rw [harith]
      have hVwt : ((ℓ * (u * b) + k + 1 : ℕ) : ℕ∞) ≤ suppVal φ V u ℓ := by
        rw [hp1supp] at hVw
        have := le_sub_of_natCast_add_le hVw
        refine le_trans ?_ this
        have harith : Sf + k + 1 - u * (ℓ * a) = ℓ * (u * b) + k + 1 := by
          have h1 : u * (ℓ * a) = ℓ * (u * a) := by ring
          omega
        rw [harith]
      -- the perturbation law keeps the side data
      obtain ⟨hq1m, hq1deg, hq1p, hq1H, hq1res⟩ :=
        pure_add_of_lt hπ hφ hℓ hcop hp1m hp1deg hp1p hp1ne hp1H
          (by rw [Polynomial.degree_eq_natDegree hp1m.ne_zero] at hUdeg ⊢
              exact hUdeg)
          (le_trans (by exact_mod_cast (by omega : ℓ * (u * a) + 1 ≤ ℓ * (u * a) + k + 1)) hUwt)
      obtain ⟨hq2m, hq2deg, hq2p, hq2H, hq2res⟩ :=
        pure_add_of_lt hπ hφ hℓ hcop hp2m hp2deg hp2p hp2ne hp2H
          (by rw [Polynomial.degree_eq_natDegree hp2m.ne_zero] at hVdeg ⊢
              exact hVdeg)
          (le_trans (by exact_mod_cast (by omega : ℓ * (u * b) + 1 ≤ ℓ * (u * b) + k + 1)) hVwt)
      refine ⟨(p.1 + U, p.2 + V), fun _ => ⟨?_, ?_, ?_⟩⟩
      · rw [hInvdef]
        refine ⟨hq1m, hq2m, by rw [hq1deg]; exact hp1deg, by rw [hq2deg]; exact hp2deg,
          hq1p, hq2p, hq1H, hq2H, ?_, ?_, ?_⟩
        · intro hne1; rw [hq1res hne1]; exact hp1res hp1ne
        · intro hne2; rw [hq2res hne2]; exact hp2res hp2ne
        · have hid : f - (p.1 + U) * (p.2 + V)
              = ((f - p.1 * p.2) - (p.2 * U + p.1 * V)) + (-(U * V)) := by ring
          rw [hid]
          refine le_trans (le_min ?_ ?_) (min_suppVal_le_suppVal_add hφ.monic hφ.pos hℓ u _ _)
          · exact_mod_cast herr'
          · rw [suppVal_neg hφ.monic]
            refine le_trans ?_ (suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u U V)
            calc ((Sf + (k + 1) + 1 : ℕ) : ℕ∞)
                ≤ ((ℓ * (u * a) + k + 1 : ℕ) : ℕ∞) + ((ℓ * (u * b) + k + 1 : ℕ) : ℕ∞) := by
                  push_cast
                  have : (Sf : ℕ) + (k + 1) + 1
                      ≤ (ℓ * (u * a) + k + 1) + (ℓ * (u * b) + k + 1) := by omega
                  exact_mod_cast this
              _ ≤ suppVal φ U u ℓ + suppVal φ V u ℓ := add_le_add hUwt hVwt
      · simpa using hUwt
      · simpa using hVwt
    · exact ⟨p, fun hc => absurd hc hp⟩
  -- ## the iterates (the landed `exists_monic_factorization` pattern)
  choose Q hQ using step
  obtain ⟨P, hP0, hPsucc⟩ : ∃ P : ℕ → Polynomial O × Polynomial O,
      P 0 = (g₀, h₀) ∧ ∀ k, P (k + 1) = Q k (P k) :=
    ⟨fun k => Nat.rec (g₀, h₀) (fun j acc => Q j acc) k, rfl, fun _ => rfl⟩
  have hInv : ∀ k, Inv k (P k) := by
    intro k
    induction k with
    | zero => rw [hP0]; exact hbase
    | succ k ih => rw [hPsucc k]; exact (hQ k (P k) ih).1
  have hI : ∀ k, (P k).1.Monic ∧ (P k).2.Monic ∧
      (P k).1.natDegree = ℓ * a * φ.natDegree ∧ (P k).2.natDegree = ℓ * b * φ.natDegree ∧
      IsPure φ (P k).1 u ℓ ∧ IsPure φ (P k).2 u ℓ ∧
      npHgt φ (P k).1 0 = ((u * a : ℕ) : ℕ∞) ∧ npHgt φ (P k).2 0 = ((u * b : ℕ) : ℕ∞) ∧
      (∀ hne1 : (sideSet φ (P k).1 u ℓ).Nonempty, resPoly π φ (P k).1 u ℓ hne1 (u * a) = G) ∧
      (∀ hne2 : (sideSet φ (P k).2 u ℓ).Nonempty, resPoly π φ (P k).2 u ℓ hne2 (u * b) = H) ∧
      ((Sf + k + 1 : ℕ) : ℕ∞) ≤ suppVal φ (f - (P k).1 * (P k).2) u ℓ := by
    intro k
    have h := hInv k
    rw [hInvdef] at h
    exact h
  have hstep1 : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ ((P (k + 1)).1 - (P k).1) u ℓ := by
    intro k
    have h1 := (hQ k (P k) (hInv k)).2.1
    rw [← hPsucc k] at h1
    exact le_trans (by exact_mod_cast (by omega : k ≤ ℓ * (u * a) + k + 1)) h1
  have hstep2 : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ ((P (k + 1)).2 - (P k).2) u ℓ := by
    intro k
    have h1 := (hQ k (P k) (hInv k)).2.2
    rw [← hPsucc k] at h1
    exact le_trans (by exact_mod_cast (by omega : k ≤ ℓ * (u * b) + k + 1)) h1
  -- ## the limit (blueprint step 4): B.40 on the two tails
  have hd1pos : 0 < ℓ * a * φ.natDegree := Nat.mul_pos (Nat.mul_pos hℓ hapos) hφ.pos
  have hd2pos : 0 < ℓ * b * φ.natDegree := Nat.mul_pos (Nat.mul_pos hℓ hbpos) hφ.pos
  have htail1 : ∀ k, ((P k).1 - Polynomial.X ^ (ℓ * a * φ.natDegree)).degree
      < ((ℓ * a * φ.natDegree : ℕ) : WithBot ℕ) := by
    intro k
    have h2 := (hI k).2.2.1
    have h3 := Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq (hI k).1
      (Polynomial.monic_X_pow (R := O) (ℓ * a * φ.natDegree))
      (by rw [h2, Polynomial.natDegree_X_pow])
    rwa [h2] at h3
  have htail2 : ∀ k, ((P k).2 - Polynomial.X ^ (ℓ * b * φ.natDegree)).degree
      < ((ℓ * b * φ.natDegree : ℕ) : WithBot ℕ) := by
    intro k
    have h2 := (hI k).2.2.2.1
    have h3 := Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq (hI k).2.1
      (Polynomial.monic_X_pow (R := O) (ℓ * b * φ.natDegree))
      (by rw [h2, Polynomial.natDegree_X_pow])
    rwa [h2] at h3
  have hdeg1 : ∀ k, ((P k).1 - Polynomial.X ^ (ℓ * a * φ.natDegree)).natDegree
      < ℓ * a * φ.natDegree := by
    intro k
    by_cases hz : (P k).1 - Polynomial.X ^ (ℓ * a * φ.natDegree) = 0
    · rw [hz, Polynomial.natDegree_zero]; exact hd1pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 (htail1 k)
  have hdeg2 : ∀ k, ((P k).2 - Polynomial.X ^ (ℓ * b * φ.natDegree)).natDegree
      < ℓ * b * φ.natDegree := by
    intro k
    by_cases hz : (P k).2 - Polynomial.X ^ (ℓ * b * φ.natDegree) = 0
    · rw [hz, Polynomial.natDegree_zero]; exact hd2pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 (htail2 k)
  obtain ⟨T1, hT1deg, hT1lim⟩ := exists_graded_limit hπ hφ.monic hφ.pos hℓ
    (ℓ * a * φ.natDegree) (fun k => (P k).1 - Polynomial.X ^ (ℓ * a * φ.natDegree)) hdeg1
    (by
      intro k
      show ((k : ℕ) : ℕ∞) ≤ suppVal φ
        (((P (k + 1)).1 - Polynomial.X ^ (ℓ * a * φ.natDegree))
          - ((P k).1 - Polynomial.X ^ (ℓ * a * φ.natDegree))) u ℓ
      have hid : ((P (k + 1)).1 - Polynomial.X ^ (ℓ * a * φ.natDegree))
          - ((P k).1 - Polynomial.X ^ (ℓ * a * φ.natDegree)) = (P (k + 1)).1 - (P k).1 := by ring
      rw [hid]
      exact hstep1 k)
  obtain ⟨T2, hT2deg, hT2lim⟩ := exists_graded_limit hπ hφ.monic hφ.pos hℓ
    (ℓ * b * φ.natDegree) (fun k => (P k).2 - Polynomial.X ^ (ℓ * b * φ.natDegree)) hdeg2
    (by
      intro k
      show ((k : ℕ) : ℕ∞) ≤ suppVal φ
        (((P (k + 1)).2 - Polynomial.X ^ (ℓ * b * φ.natDegree))
          - ((P k).2 - Polynomial.X ^ (ℓ * b * φ.natDegree))) u ℓ
      have hid : ((P (k + 1)).2 - Polynomial.X ^ (ℓ * b * φ.natDegree))
          - ((P k).2 - Polynomial.X ^ (ℓ * b * φ.natDegree)) = (P (k + 1)).2 - (P k).2 := by ring
      rw [hid]
      exact hstep2 k)
  have hT1degb : T1.degree < ((ℓ * a * φ.natDegree : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hT1deg)
  have hT2degb : T2.degree < ((ℓ * b * φ.natDegree : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hT2deg)
  set g := Polynomial.X ^ (ℓ * a * φ.natDegree) + T1 with hgdef
  set h := Polynomial.X ^ (ℓ * b * φ.natDegree) + T2 with hhdef
  have hgm : g.Monic :=
    (Polynomial.monic_X_pow _).add_of_left (by rwa [Polynomial.degree_X_pow])
  have hhm : h.Monic :=
    (Polynomial.monic_X_pow _).add_of_left (by rwa [Polynomial.degree_X_pow])
  have hgdeg : g.natDegree = ℓ * a * φ.natDegree := by
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [hgdef, Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  have hhdeg : h.natDegree = ℓ * b * φ.natDegree := by
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [hhdef, Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  have hglim : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (g - (P k).1) u ℓ := by
    intro k
    have h0 := hT1lim k
    have hid : g - (P k).1 = T1 - ((P k).1 - Polynomial.X ^ (ℓ * a * φ.natDegree)) := by
      rw [hgdef]; ring
    rw [hid]
    exact h0
  have hhlim : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (h - (P k).2) u ℓ := by
    intro k
    have h0 := hT2lim k
    have hid : h - (P k).2 = T2 - ((P k).2 - Polynomial.X ^ (ℓ * b * φ.natDegree)) := by
      rw [hhdef]; ring
    rw [hid]
    exact h0
  -- ## the residual data of the limit (blueprint step 5): the perturbation law once more
  set k₀ := ℓ * (u * a) + ℓ * (u * b) + 1 with hk₀def
  obtain ⟨hk1m, hk2m, hk1deg, hk2deg, hk1p, hk2p, hk1H, hk2H, hk1res, hk2res, hkerr⟩ := hI k₀
  have hk1ne : (sideSet φ (P k₀).1 u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
  have hk2ne : (sideSet φ (P k₀).2 u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
  have hydeg1 : (g - (P k₀).1).degree < ((P k₀).1).degree := by
    have hid : g - (P k₀).1 = T1 - ((P k₀).1 - Polynomial.X ^ (ℓ * a * φ.natDegree)) := by
      rw [hgdef]; ring
    rw [hid, Polynomial.degree_eq_natDegree hk1m.ne_zero, hk1deg]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hT1degb (htail1 k₀))
  have hydeg2 : (h - (P k₀).2).degree < ((P k₀).2).degree := by
    have hid : h - (P k₀).2 = T2 - ((P k₀).2 - Polynomial.X ^ (ℓ * b * φ.natDegree)) := by
      rw [hhdef]; ring
    rw [hid, Polynomial.degree_eq_natDegree hk2m.ne_zero, hk2deg]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hT2degb (htail2 k₀))
  have hyw1 : ((ℓ * (u * a) + 1 : ℕ) : ℕ∞) ≤ suppVal φ (g - (P k₀).1) u ℓ :=
    le_trans (by exact_mod_cast (by omega : ℓ * (u * a) + 1 ≤ k₀)) (hglim k₀)
  have hyw2 : ((ℓ * (u * b) + 1 : ℕ) : ℕ∞) ≤ suppVal φ (h - (P k₀).2) u ℓ :=
    le_trans (by exact_mod_cast (by omega : ℓ * (u * b) + 1 ≤ k₀)) (hhlim k₀)
  obtain ⟨-, -, hgp, hgH, hgres⟩ :=
    pure_of_add_eq (z := g) hπ hφ hℓ hcop hk1m hk1deg hk1p hk1ne hk1H hydeg1 hyw1 (by ring)
  obtain ⟨-, -, hhp, hhH, hhres⟩ :=
    pure_of_add_eq (z := h) hπ hφ hℓ hcop hk2m hk2deg hk2p hk2ne hk2H hydeg2 hyw2 (by ring)
  have hgne : (sideSet φ g u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
  have hhne : (sideSet φ h u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
  -- ## the product identity: the error has infinite weight
  have hfgh : f = g * h := by
    have hall : ∀ n : ℕ, ((n : ℕ) : ℕ∞) ≤ suppVal φ (f - g * h) u ℓ := by
      intro n
      have hnerr := (hI n).2.2.2.2.2.2.2.2.2.2
      have hid : f - g * h
          = (f - (P n).1 * (P n).2)
            + (-((g - (P n).1) * h + (P n).1 * (h - (P n).2))) := by ring
      rw [hid]
      refine le_trans (le_min ?_ ?_) (min_suppVal_le_suppVal_add hφ.monic hφ.pos hℓ u _ _)
      · exact le_trans (by exact_mod_cast (by omega : n ≤ Sf + n + 1)) hnerr
      · rw [suppVal_neg hφ.monic]
        refine le_trans (le_min ?_ ?_) (min_suppVal_le_suppVal_add hφ.monic hφ.pos hℓ u _ _)
        · refine le_trans ?_ (suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u _ _)
          exact le_trans (hglim n) le_self_add
        · refine le_trans ?_ (suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u _ _)
          exact le_trans (hhlim n) le_add_self
    exact eq_of_sub_eq_zero
      (eq_zero_of_suppVal_eq_top hφ.monic hφ.pos (eq_top_of_forall_natCast_le hall))
  -- ## the contract
  refine ⟨g, h, hgm, hhm, hfgh, by rw [hgdeg]; ring, by rw [hhdeg]; ring, hgp, hhp,
    ⟨u * a, u * b, hgne, hhne, hgH, hhH, hgp, hhp, ?_⟩⟩
  rw [hgres hgne, hhres hhne, hk1res hk1ne, hk2res hk2ne]
  exact hGH

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.npHgt_one
#print axioms Uniformity.Density.Leaf.suppVal_one
#print axioms Uniformity.Density.Leaf.isPure_one
#print axioms Uniformity.Density.Leaf.resPoly_one
#print axioms Uniformity.Density.Leaf.le_sub_of_natCast_add_le
#print axioms Uniformity.Density.Leaf.eq_top_of_forall_natCast_le
#print axioms Uniformity.Density.Leaf.pure_of_add_eq
#print axioms Uniformity.Density.Leaf.exists_graded_factorization
end AxCheck
