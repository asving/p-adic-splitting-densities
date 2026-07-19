/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# F-B4 — SparseResultant: resultants of sparse polygon twists

The last rung of the Master Lemma count form (`RESTART_FORMALIZATION_BLUEPRINT.md`, "F-B4
REFINED"; math source `RESTART_LEMMA.md` §8).  Leaf module: imports Mathlib only.

Numeric gate (2026-07-04, `/workspace-vast/asving/tmp/fb4_gate/`, exact PARI arithmetic):

* (i) `Res(f(x^e), g(x^e), m·e, n·e) = Res(f, g, m, n)^e` with sign `+1` for **all**
  `(deg f, deg g, e)`, including padded sizes `m > deg f`, `n > deg g`.
* (ii) for sparse twists `F(x) = Σ_k t^((d-k)h)·f_k·x^(ek)` over `ℤ[t]`:
  `Res(F_i, F_j, d_i e, d_j e) = t^(d_i d_j e h) · Res(f_i, f_j)^e` **exactly** (sign `+1`,
  no `p`-correction term, no monicity/unit-constant hypotheses).
* (iii) cross-side `(e_i, h_i)` vs `(e_j, h_j)` with `h_i/e_i < h_j/e_j`:
  `v_t(Res) = d_i d_j e_j h_i` and the lowest coefficient is
  `(-1)^(MN) · lc(f_j)^M · f_i(0)^N` (`M = e_i d_i`, `N = e_j d_j`); a unit constant term on
  the **shallow** side is required, coprimality of the residuals is **not**.

Contents (deliverables in blueprint order):

1. **SPARSE** (`resultant_expand`): over any `CommRing R`,
   `Res(expand e f, expand e g, m·e, n·e) = Res(f, g, m, n)^e` for `f.natDegree ≤ m`,
   `g.natDegree ≤ n` (any `e`, including `e = 0`).  Split case is purely Euclidean
   (`resultant_X_pow_sub_C_expand`: `g(x^e) ≡ g(α) mod (x^e - α)`), transferred to `CommRing`
   by mathlib's `induction_of_Splits_of_injective_of_surjective`, mirroring
   `resultant_mul_right`.
2. **DOMINANT-TRANSVERSAL DET** (`det_eq_pow_mul_unit_of_dominant_transversal` /
   `..._of_colWeights`): for a square matrix over a `CommRing` with a nilpotent `π`
   (specialize `π := (p : ZMod (p^N))`, `isNilpotent_p_zmod`), if the `τ`-transversal product
   is `π^V · unit` and every other permutation product is divisible by `π^(V+1)`, then
   `det = π^V · unit`.  Leibniz-dominance; no `Σ w < N` hypothesis is needed for this
   existence form (the exponent-pinning hypothesis `c < N` lives in the F-B1 consumers).
3. **SCALE/TWIST** (`resultant_sparseTwist`, `resultant_sparseTwist_isUnit`): the sparse
   twist is `sparseTwist π ψ e h = expand e (ψ.scaleRoots (π^h))`, so deliverable 1 plus
   mathlib's `resultant_scaleRoots` give the **exact identity**
   `Res(F_i, F_j) = π^(d_i d_j e h) · Res(ψ_i, ψ_j)^e` over any `CommRing` — the gate's (ii).
   Over `ZMod (p^N)` with `Res(ψ_i, ψ_j)` a unit this is `p^(d_i d_j e h) · unit`; note **no
   margin hypothesis `d_i d_j e h < N` is needed for the identity** (it is only needed by
   downstream consumers to pin the valuation), and no monic/unit-constant hypotheses either.
4. **CROSS-SIDE** (`resultant_sparseTwist_cross`): slopes `h_i/e_i < h_j/e_j` give
   `Res(F_i, F_j) = p^(d_i d_j e_j h_i) · unit`, via deliverable 2 on the Sylvester matrix.
   The dominant transversal `crossPerm`: each `F_j`-block column `j₁` picks row `j₁ + N`
   (leading coefficient `1`), each `F_i`-block column `j₂` picks row `j₂` (constant
   coefficient `p^(d_i h_i)·ψ_i(0)`).  The combinatorial core (`cross_count`): for any other
   support-compatible permutation, with `A = Σ k'`, `B = Σ k` the chosen coefficient indices,
   the row-sum identity forces `e_j·A + e_i·B = MN`, whence
   `e_j·(T - V) = (h_j e_i - h_i e_j)·B`; `B = 0` forces the transversal, so `σ ≠ τ` gives
   `T ≥ V + 1`.  Hypotheses: `ψ_j` monic, `ψ_i(0)` a unit (gate (iii) shows the latter is
   genuinely needed), slopes strict; **no residual-coprimality**.

No `sorry`, no `axiom`, no `native_decide`; all public results elaborate with core-only
axiom footprints (`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option linter.style.longLine false

namespace LeanUrat.OM.SparseResultant

open Polynomial Matrix

variable {R : Type*} [CommRing R]

/-! ## Deliverable 1 — SPARSE: `Res(f(x^e), g(x^e)) = Res(f,g)^e`

Stated via `Polynomial.expand` (`expand R e f = f.comp (X^e)`), whose `natDegree` API is
unconditional over any `CommRing`. -/

/-- Parity helper for the padding step: `(-1)^(a·e·e) = (-1)^(a·e)`. -/
private lemma neg_one_pow_mul_self (a e : ℕ) :
    ((-1 : R)) ^ (a * e * e) = (-1 : R) ^ (a * e) := by
  rcases Nat.even_or_odd (a * e) with hpar | hpar
  · rw [(hpar.mul_right e).neg_one_pow, hpar.neg_one_pow]
  · rw [(hpar.mul (Nat.odd_mul.mp hpar).2).neg_one_pow, hpar.neg_one_pow]

/-- **The Euclidean core of SPARSE** (any `CommRing`, no roots of unity): since
`x^e ≡ α mod (x^e - α)`, we get `g(x^e) ≡ g(α)`, hence
`Res(x^e - α, g(x^e), e, n·e) = g(α)^e`. -/
theorem resultant_X_pow_sub_C_expand {e : ℕ} (he : 0 < e) (α : R) (g : R[X]) (n : ℕ)
    (hg : g.natDegree ≤ n) :
    resultant (X ^ e - C α) (expand R e g) e (n * e) = g.eval α ^ e := by
  nontriviality R
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (Nat.le_zero.mp hg)
    rw [expand_C, Nat.zero_mul, resultant_C_zero_right, eval_C]
  · have hkey : expand R e g
        = C (g.eval α) + (X ^ e - C α) * expand R e (g /ₘ (X - C α)) := by
      conv_lhs => rw [← modByMonic_add_div g (X - C α)]
      rw [map_add, map_mul, modByMonic_X_sub_C_eq_C_eval, expand_C, map_sub, expand_X,
        expand_C]
    have hp : (expand R e (g /ₘ (X - C α))).natDegree + e ≤ n * e := by
      rw [natDegree_expand]
      have h1 : (g /ₘ (X - C α)).natDegree + 1 ≤ n := by
        rw [natDegree_divByMonic g (monic_X_sub_C α), natDegree_X_sub_C]
        omega
      calc (g /ₘ (X - C α)).natDegree * e + e
          = ((g /ₘ (X - C α)).natDegree + 1) * e := by ring
        _ ≤ n * e := Nat.mul_le_mul_right e h1
    have hf : (X ^ e - C α).natDegree ≤ e := le_of_eq natDegree_X_pow_sub_C
    have hc : (X ^ e - C α).coeff e = 1 := by
      rw [coeff_sub, coeff_X_pow, if_pos rfl, coeff_C, if_neg he.ne', sub_zero]
    rw [hkey, resultant_add_mul_right _ _ _ _ _ hp hf, resultant_C_right, hc, one_pow,
      one_mul]

/-- Multiplicative accumulation of the Euclidean core over a multiset of linear factors. -/
private theorem resultant_multiset_prod_expand {K : Type*} [Field K] {e : ℕ} (he : 0 < e)
    (s : Multiset K) (g : K[X]) (n : ℕ) (hg : g.natDegree ≤ n) :
    resultant ((s.map fun a => X ^ e - C a).prod) (expand K e g) (Multiset.card s * e)
        (n * e)
      = (s.map fun a => g.eval a ^ e).prod := by
  have hGle : (expand K e g).natDegree ≤ n * e := by
    rw [natDegree_expand]; exact Nat.mul_le_mul_right e hg
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hd1 : (X ^ e - C a).natDegree = e := natDegree_X_pow_sub_C
    have h0 : (0 : K[X]) ∉ s.map fun b => X ^ e - C b := by
      intro hmem
      obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hmem
      exact X_pow_sub_C_ne_zero he b hb
    have hd2 : ((s.map fun b => X ^ e - C b).prod).natDegree = Multiset.card s * e := by
      rw [natDegree_multiset_prod _ h0, Multiset.map_map]
      rw [show ((fun q : K[X] => q.natDegree) ∘ fun b : K => X ^ e - C b) = fun _ : K => e
          from funext fun b => natDegree_X_pow_sub_C]
      rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.map_cons,
      Multiset.prod_cons]
    rw [show (Multiset.card s + 1) * e
          = (X ^ e - C a).natDegree + ((s.map fun b => X ^ e - C b).prod).natDegree from by
        rw [hd1, hd2]; ring]
    rw [resultant_mul_left _ _ _ _ hGle, hd1, hd2,
      resultant_X_pow_sub_C_expand he a g n hg, ih]

/-- SPARSE at exact degree, split case over a field. -/
private theorem resultant_expand_of_splits {K : Type*} [Field K] {e : ℕ} (he : 0 < e)
    (f g : K[X]) (n : ℕ) (hg : g.natDegree ≤ n) (hf : f.Splits) :
    resultant (expand K e f) (expand K e g) (f.natDegree * e) (n * e)
      = resultant f g f.natDegree n ^ e := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [map_zero, natDegree_zero, Nat.zero_mul, resultant_zero_left, resultant_zero_left]
    simp [pow_mul]
  · have hexp : expand K e f
        = C f.leadingCoeff * (f.roots.map fun a => X ^ e - C a).prod := by
      conv_lhs => rw [hf.eq_prod_roots]
      rw [map_mul, expand_C, map_multiset_prod, Multiset.map_map]
      congr 2
      refine Multiset.map_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, map_sub, expand_X, expand_C]
    rw [resultant_eq_prod_eval f g n hg hf, hexp, hf.natDegree_eq_card_roots,
      resultant_C_mul_left, resultant_multiset_prod_expand he f.roots g n hg, mul_pow,
      ← pow_mul, ← Multiset.prod_map_pow]

/-- SPARSE at exact degree over any `CommRing`, by mathlib's `Splits`-induction
combinator (the `resultant_mul_right` template). -/
private theorem resultant_expand_natDegree {R : Type*} [CommRing R] {e : ℕ} (he : 0 < e)
    (f : R[X]) (n : ℕ) :
    ∀ g : R[X], g.natDegree ≤ n →
      resultant (expand R e f) (expand R e g) (f.natDegree * e) (n * e)
        = resultant f g f.natDegree n ^ e := by
  induction f using Polynomial.induction_of_Splits_of_injective_of_surjective with
  | Splits K f hf => exact fun g hg => resultant_expand_of_splits he f g n hg hf
  | injective R' S φ hφ f IH =>
    intro g hg
    apply hφ
    have h1 := IH (g.map φ) (natDegree_map_le.trans hg)
    rw [natDegree_map_eq_of_injective hφ, ← map_expand, ← map_expand, resultant_map_map,
      resultant_map_map, ← map_pow] at h1
    exact h1
  | surjective R' S φ hφ f IH =>
    intro g hg
    obtain ⟨f', hf', hfd⟩ := Polynomial.exists_natDegree_eq_of_mem_lifts
      (Polynomial.map_surjective φ hφ f)
    obtain ⟨g', hg', hgd⟩ := Polynomial.exists_natDegree_eq_of_mem_lifts
      (Polynomial.map_surjective φ hφ g)
    rw [← hfd, ← hf', ← hg', ← map_expand, ← map_expand, resultant_map_map,
      resultant_map_map, ← map_pow]
    exact congrArg φ (IH f' g' (hgd.trans_le hg))

/-- **Deliverable 1 (SPARSE).** Over any `CommRing R`, for `f.natDegree ≤ m` and
`g.natDegree ≤ n`,
`Res(f(x^e), g(x^e), m·e, n·e) = Res(f, g, m, n)^e`.

The sign is `+1` for **all** `(m, n, e)` — pinned by the numeric gate (item (i), including
padded sizes) and forced here by the parity identity `(-1)^(n·e·c·e) = ((-1)^(n·c))^e`.
The case `e = 0` holds trivially (both sides are `1`). -/
theorem resultant_expand (e : ℕ) (f g : R[X]) (m n : ℕ) (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) :
    resultant (expand R e f) (expand R e g) (m * e) (n * e) = resultant f g m n ^ e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [Nat.mul_zero, Nat.mul_zero, resultant_zero_left_deg, pow_zero, pow_zero]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hf
  have hpad1 := resultant_add_left_deg (expand R e f) (expand R e g) (f.natDegree * e)
    (n * e) (c * e) (le_of_eq (natDegree_expand e f))
  have hpad2 := resultant_add_left_deg f g f.natDegree n c le_rfl
  rw [add_mul, hpad1, hpad2, resultant_expand_natDegree he f n g hg, mul_pow, mul_pow,
    coeff_expand_mul he, pow_mul (g.coeff n) c e,
    show n * e * (c * e) = n * c * e * e from by ring, neg_one_pow_mul_self,
    pow_mul (-1 : R) (n * c) e]

/-! ## Deliverable 2 — dominant-transversal determinants

Over any `CommRing` with a nilpotent `π` (e.g. `π = (p : ZMod (p^N))`): if one transversal
attains `π^V · unit` and every other permutation product is strictly deeper, the determinant
is `π^V · unit`.  No `V < N`-type hypothesis is needed for this existence form; consumers
(F-B1/F-B2 shapes) supply `c < N` separately to pin the valuation. -/

/-- `(p : ZMod (p^N))` is nilpotent (for any `p`, `N`). -/
theorem isNilpotent_p_zmod (p N : ℕ) : IsNilpotent ((p : ZMod (p ^ N))) :=
  ⟨N, by rw [← Nat.cast_pow, ZMod.natCast_self]⟩

/-- **Deliverable 2, permutation form (Leibniz dominance).** If the `τ`-transversal product
is `π^V · u` with `u` a unit and every other permutation product is divisible by `π^(V+1)`,
then `det A = π^V · unit`. -/
theorem det_eq_pow_mul_unit_of_dominant_transversal {ι : Type*} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι R) {π : R} (hπ : IsNilpotent π) (τ : Equiv.Perm ι) (V : ℕ)
    (hτ : ∃ u : Rˣ, ∏ i, A (τ i) i = π ^ V * u)
    (hoff : ∀ σ : Equiv.Perm ι, σ ≠ τ → π ^ (V + 1) ∣ ∏ i, A (σ i) i) :
    ∃ u : Rˣ, A.det = π ^ V * u := by
  obtain ⟨u, hu⟩ := hτ
  have hrest : π ^ (V + 1)
      ∣ ∑ σ ∈ Finset.univ.erase τ, Equiv.Perm.sign σ • ∏ i, A (σ i) i := by
    refine Finset.dvd_sum fun σ hσ => ?_
    have hd := hoff σ (Finset.mem_erase.mp hσ).1
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
    · simpa using hd
    · simpa [Units.smul_def, neg_one_zsmul] using dvd_neg.mpr hd
  obtain ⟨r, hr⟩ := hrest
  have hsplit : A.det = Equiv.Perm.sign τ • ∏ i, A (τ i) i
      + ∑ σ ∈ Finset.univ.erase τ, Equiv.Perm.sign σ • ∏ i, A (σ i) i := by
    rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ τ)]
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, Equiv.Perm.sign τ • (π ^ V * (u : R)) = π ^ V * (w : R) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> rw [hs]
    · exact ⟨u, one_smul _ _⟩
    · exact ⟨-u, by simp [Units.smul_def, mul_neg]⟩
  obtain ⟨k, hk⟩ := hπ
  have hnil : IsNilpotent (π * r) := ⟨k, by rw [mul_pow, hk, zero_mul]⟩
  have hun : IsUnit ((w : R) + π * r) :=
    hnil.isUnit_add_left_of_commute w.isUnit (Commute.all _ _)
  refine ⟨hun.unit, ?_⟩
  rw [IsUnit.unit_spec, hsplit, hu, hw, hr, pow_succ]
  ring

/-- **Deliverable 2, column-weight form** (the blueprint's spelling): a weight `w j` per
column, the `τ`-transversal entry `A (τ j) j = π^(w j) · unit`, and all off-transversal
entries of column `j` divisible by `π^(w j + 1)`; then `det A = π^(Σ w) · unit`.
(Consequently `π^(w j) ∣ A i j` for every entry of column `j`.) -/
theorem det_eq_pow_mul_unit_of_colWeights {ι : Type*} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι R) {π : R} (hπ : IsNilpotent π) (w : ι → ℕ) (τ : Equiv.Perm ι)
    (hdiag : ∀ j, ∃ u : Rˣ, A (τ j) j = π ^ w j * u)
    (hoff : ∀ i j, i ≠ τ j → π ^ (w j + 1) ∣ A i j) :
    ∃ u : Rˣ, A.det = π ^ (∑ j, w j) * u := by
  choose uu huu using hdiag
  refine det_eq_pow_mul_unit_of_dominant_transversal A hπ τ (∑ j, w j) ⟨∏ j, uu j, ?_⟩ ?_
  · calc ∏ i, A (τ i) i = ∏ i, (π ^ w i * (uu i : R)) :=
        Finset.prod_congr rfl fun i _ => huu i
      _ = (∏ i, π ^ w i) * ∏ i, (uu i : R) := Finset.prod_mul_distrib
      _ = π ^ (∑ i, w i) * ((∏ i, uu i : Rˣ) : R) := by
        rw [Finset.prod_pow_eq_pow_sum, Units.coe_prod]
  · intro σ hσ
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, σ j₀ ≠ τ j₀ := by
      by_contra hall
      push Not at hall
      exact hσ (Equiv.ext hall)
    have hdvd : ∀ j, π ^ (w j + if j = j₀ then 1 else 0) ∣ A (σ j) j := by
      intro j
      rcases eq_or_ne j j₀ with rfl | hj
      · rw [if_pos rfl]
        exact hoff _ _ hj₀
      · rw [if_neg hj, Nat.add_zero]
        rcases eq_or_ne (σ j) (τ j) with hsj | hsj
        · rw [hsj, huu j]
          exact dvd_mul_right _ _
        · exact dvd_trans (pow_dvd_pow π (Nat.le_succ _)) (hoff _ _ hsj)
    calc π ^ (∑ j, w j + 1) = ∏ j, π ^ (w j + if j = j₀ then 1 else 0) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
            Finset.sum_ite_eq' Finset.univ j₀ (fun _ => 1), if_pos (Finset.mem_univ j₀)]
      _ ∣ ∏ j, A (σ j) j := Finset.prod_dvd_prod_of_dvd _ _ fun j _ => hdvd j

/-! ## The sparse twist -/

/-- The **sparse twist** `F_ψ(x) = Σ_k π^((d-k)h) · ψ_k · x^(ek)` of `ψ` (`d = ψ.natDegree`),
realized as `expand e (ψ.scaleRoots (π^h))` — see `sparseTwist_eq_sum` for the sum form.
Over `ZMod (p^N)` with `π = p` this is the standard block for a polygon side of slope `h/e`
with residual `ψ`. -/
noncomputable def sparseTwist (π : R) (ψ : R[X]) (e h : ℕ) : R[X] :=
  expand R e (ψ.scaleRoots (π ^ h))

/-- The spec's sum form of the sparse twist. -/
theorem sparseTwist_eq_sum (π : R) (ψ : R[X]) {e : ℕ} (he : 0 < e) (h : ℕ) :
    sparseTwist π ψ e h
      = ∑ k ∈ Finset.range (ψ.natDegree + 1),
          C (π ^ ((ψ.natDegree - k) * h)) * C (ψ.coeff k) * X ^ (e * k) := by
  ext m
  rw [sparseTwist, coeff_expand he, finsetSum_coeff]
  simp_rw [mul_assoc, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hdvd : e ∣ m
  · obtain ⟨k₀, rfl⟩ := hdvd
    rw [if_pos (dvd_mul_right e k₀), Nat.mul_div_cancel_left k₀ he, coeff_scaleRoots]
    simp_rw [mul_right_inj' he.ne']
    rw [Finset.sum_ite_eq (Finset.range (ψ.natDegree + 1)) k₀
      (fun k => π ^ ((ψ.natDegree - k) * h) * ψ.coeff k)]
    rcases le_or_gt k₀ ψ.natDegree with hk | hk
    · rw [if_pos (Finset.mem_range.mpr (by omega)), ← pow_mul,
        Nat.mul_comm h (ψ.natDegree - k₀), mul_comm]
    · rw [if_neg (by simp only [Finset.mem_range]; omega),
        coeff_eq_zero_of_natDegree_lt hk, zero_mul]
  · rw [if_neg hdvd]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg fun heq => hdvd ⟨k, heq⟩]

/-- Coefficient of the sparse twist at a multiple of `e` (valid for **all** `k`, including
`k > d` where both sides vanish). -/
theorem sparseTwist_coeff_mul (π : R) (ψ : R[X]) {e : ℕ} (he : 0 < e) (h k : ℕ) :
    (sparseTwist π ψ e h).coeff (e * k) = π ^ ((ψ.natDegree - k) * h) * ψ.coeff k := by
  rw [sparseTwist, coeff_expand_mul' he, coeff_scaleRoots, ← pow_mul,
    Nat.mul_comm h (ψ.natDegree - k), mul_comm]

theorem sparseTwist_coeff_of_not_dvd (π : R) (ψ : R[X]) {e : ℕ} (he : 0 < e) (h : ℕ)
    {m : ℕ} (hm : ¬ e ∣ m) : (sparseTwist π ψ e h).coeff m = 0 := by
  rw [sparseTwist, coeff_expand he, if_neg hm]

theorem sparseTwist_coeff_zero (π : R) (ψ : R[X]) {e : ℕ} (he : 0 < e) (h : ℕ) :
    (sparseTwist π ψ e h).coeff 0 = π ^ (ψ.natDegree * h) * ψ.coeff 0 := by
  simpa using sparseTwist_coeff_mul π ψ he h 0

theorem sparseTwist_coeff_top (π : R) (ψ : R[X]) {e : ℕ} (he : 0 < e) (h : ℕ) :
    (sparseTwist π ψ e h).coeff (e * ψ.natDegree) = ψ.leadingCoeff := by
  rw [sparseTwist_coeff_mul π ψ he h, Nat.sub_self, Nat.zero_mul, pow_zero, one_mul,
    ← coeff_natDegree]

theorem sparseTwist_natDegree (π : R) (ψ : R[X]) (e h : ℕ) :
    (sparseTwist π ψ e h).natDegree = ψ.natDegree * e := by
  rw [sparseTwist, natDegree_expand, natDegree_scaleRoots]

theorem sparseTwist_monic (π : R) {ψ : R[X]} (hψ : ψ.Monic) {e : ℕ} (he : 0 < e) (h : ℕ) :
    (sparseTwist π ψ e h).Monic :=
  Monic.expand he ((monic_scaleRoots_iff (π ^ h)).mpr hψ)

/-- If a sparse-twist coefficient is nonzero, its index is `e·k` with `k ≤ d`, and the
coefficient is divisible by `π^((d-k)·h)`. -/
private theorem sparseTwist_coeff_structure (π : R) (ψ : R[X]) {e : ℕ} (he : 0 < e)
    (h : ℕ) {m : ℕ} (hne : (sparseTwist π ψ e h).coeff m ≠ 0) :
    ∃ k, m = e * k ∧ k ≤ ψ.natDegree
      ∧ π ^ ((ψ.natDegree - k) * h) ∣ (sparseTwist π ψ e h).coeff m := by
  by_cases hdvd : e ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    refine ⟨k, rfl, ?_, ?_⟩
    · by_contra hk
      push Not at hk
      exact hne (by rw [sparseTwist_coeff_mul π ψ he h,
        coeff_eq_zero_of_natDegree_lt hk, mul_zero])
    · rw [sparseTwist_coeff_mul π ψ he h]
      exact dvd_mul_right _ _
  · exact absurd (sparseTwist_coeff_of_not_dvd π ψ he h hdvd) hne

/-! ## Deliverable 3 — SCALE/TWIST (same side) -/

/-- **Deliverable 3, exact form** (any `CommRing`, no hypotheses at all): the same-side
closed form
`Res(F_i, F_j, d_i·e, d_j·e) = π^(d_i d_j e h) · Res(ψ_i, ψ_j)^e`, with sign `+1` and **no
correction term** — via `F = expand e (scaleRoots ψ (π^h))`, deliverable 1, and mathlib's
`resultant_scaleRoots`.  This is the gate's item (ii) as a polynomial identity. -/
theorem resultant_sparseTwist (π : R) (ψi ψj : R[X]) (e h : ℕ) :
    resultant (sparseTwist π ψi e h) (sparseTwist π ψj e h) (ψi.natDegree * e)
        (ψj.natDegree * e)
      = π ^ (ψi.natDegree * ψj.natDegree * e * h)
        * resultant ψi ψj ψi.natDegree ψj.natDegree ^ e := by
  rw [sparseTwist, sparseTwist,
    resultant_expand e _ _ _ _ (le_of_eq (natDegree_scaleRoots ψi (π ^ h)))
      (le_of_eq (natDegree_scaleRoots ψj (π ^ h)))]
  have hsr := Polynomial.resultant_scaleRoots ψi ψj (π ^ h)
  rw [natDegree_scaleRoots, natDegree_scaleRoots] at hsr
  rw [hsr, mul_pow, ← pow_mul, ← pow_mul]
  congr 2
  ring

/-- **Deliverable 3 over `ZMod (p^N)`**: coprime residuals (`Res(ψ_i, ψ_j)` a unit — over
`ZMod (p^N)` this is exactly "unit mod `p`") give
`Res(F_i, F_j) = p^(d_i d_j e h) · unit`.

Blueprint erratum: no margin `d_i d_j e h < N`, no monicity and no unit-constant-term
hypotheses are needed for this identity (the margin only pins the valuation downstream). -/
theorem resultant_sparseTwist_isUnit {p N : ℕ} {ψi ψj : (ZMod (p ^ N))[X]} {di dj : ℕ}
    (hdi : ψi.natDegree = di) (hdj : ψj.natDegree = dj) (e h : ℕ)
    (hres : IsUnit (resultant ψi ψj di dj)) :
    ∃ u : (ZMod (p ^ N))ˣ,
      resultant (sparseTwist (p : ZMod (p ^ N)) ψi e h)
          (sparseTwist (p : ZMod (p ^ N)) ψj e h) (di * e) (dj * e)
        = (p : ZMod (p ^ N)) ^ (di * dj * e * h) * u := by
  subst hdi hdj
  exact ⟨(hres.pow e).unit, by rw [IsUnit.unit_spec, resultant_sparseTwist]⟩

/-! ## Deliverable 4 — CROSS-SIDE -/

/-- The dominant transversal for the cross-side Sylvester matrix: column `castAdd n j₁`
(`g`-block) picks row `n + j₁`, column `natAdd m j₂` (`f`-block) picks row `j₂`. -/
def crossPerm (m n : ℕ) : Equiv.Perm (Fin (m + n)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin m) (Fin n)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_comm n m))))

lemma crossPerm_castAdd_val (m n : ℕ) (j : Fin m) :
    ((crossPerm m n) (Fin.castAdd n j) : ℕ) = n + j := by
  simp [crossPerm]
  omega

lemma crossPerm_natAdd_val (m n : ℕ) (j : Fin n) :
    ((crossPerm m n) (Fin.natAdd m j) : ℕ) = j := by
  simp [crossPerm]

/-- Entry of the Sylvester matrix in the `g`-block (first `m` columns). -/
private lemma sylvester_castAdd (f g : R[X]) (m n : ℕ) (i : Fin (m + n)) (j : Fin m) :
    sylvester f g m n i (Fin.castAdd n j)
      = if (i : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) then g.coeff (i - j) else 0 := by
  simp only [sylvester, Matrix.of_apply, Fin.addCases_left]

/-- Entry of the Sylvester matrix in the `f`-block (last `n` columns). -/
private lemma sylvester_natAdd (f g : R[X]) (m n : ℕ) (i : Fin (m + n)) (j : Fin n) :
    sylvester f g m n i (Fin.natAdd m j)
      = if (i : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + m) then f.coeff (i - j) else 0 := by
  simp only [sylvester, Matrix.of_apply, Fin.addCases_right]

/-- **The combinatorial core of cross-side dominance** (pure `ℕ` arithmetic).  For a
support-compatible assignment with column data `kL : Fin (di·ei) → ℕ` (`≤ dj`),
`kR : Fin (dj·ej) → ℕ` (`≤ di`), the row-sum identity `ej·ΣkL + ei·ΣkR = (di·ei)·(dj·ej)`
and strict slopes `hi·ej < hj·ei` force: either the assignment is the transversal
(`kL ≡ dj`, `kR ≡ 0`), or the total valuation `T = Σ(dj−kL)·hj + Σ(di−kR)·hi` satisfies
`T ≥ di·dj·ej·hi + 1`.  Key identity: `ej·T = ej·V + (hj·ei − hi·ej)·ΣkR`. -/
private lemma cross_count {di dj ei ej hi hj : ℕ} (hslope : hi * ej < hj * ei)
    (hej : 0 < ej) (kL : Fin (di * ei) → ℕ) (kR : Fin (dj * ej) → ℕ)
    (hkL : ∀ j, kL j ≤ dj) (hkR : ∀ j, kR j ≤ di)
    (hAB : ej * (∑ j, kL j) + ei * (∑ j, kR j) = (di * ei) * (dj * ej))
    (hne : (∃ j, kL j ≠ dj) ∨ (∃ j, kR j ≠ 0)) :
    di * dj * ej * hi + 1 ≤ (∑ j, (dj - kL j) * hj) + (∑ j, (di - kR j) * hi) := by
  have hT1 : (∑ j, (dj - kL j) * hj) + hj * (∑ j, kL j) = (di * ei) * (dj * hj) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun j _ =>
      show (dj - kL j) * hj + hj * kL j = dj * hj from by
        rw [Nat.mul_comm hj (kL j), ← Nat.add_mul, Nat.sub_add_cancel (hkL j)]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hT2 : (∑ j, (di - kR j) * hi) + hi * (∑ j, kR j) = (dj * ej) * (di * hi) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun j _ =>
      show (di - kR j) * hi + hi * kR j = di * hi from by
        rw [Nat.mul_comm hi (kR j), ← Nat.add_mul, Nat.sub_add_cancel (hkR j)]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  by_cases hB : ∃ j, kR j ≠ 0
  · obtain ⟨j₀, hj₀⟩ := hB
    have hB1 : 1 ≤ ∑ j, kR j :=
      le_trans (Nat.one_le_iff_ne_zero.mpr hj₀)
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀))
    by_contra hcon
    push Not at hcon
    have hcon' : ((∑ j, (dj - kL j) * hj : ℕ) : ℤ) + ((∑ j, (di - kR j) * hi : ℕ) : ℤ)
        ≤ (di : ℤ) * dj * ej * hi := by
      have := Nat.lt_succ_iff.mp hcon
      push_cast
      exact_mod_cast this
    have h1 : ((∑ j, (dj - kL j) * hj : ℕ) : ℤ) + (hj : ℤ) * ((∑ j, kL j : ℕ) : ℤ)
        = ((di : ℤ) * ei) * ((dj : ℤ) * hj) := by exact_mod_cast hT1
    have h2 : ((∑ j, (di - kR j) * hi : ℕ) : ℤ) + (hi : ℤ) * ((∑ j, kR j : ℕ) : ℤ)
        = ((dj : ℤ) * ej) * ((di : ℤ) * hi) := by exact_mod_cast hT2
    have h3 : (ej : ℤ) * ((∑ j, kL j : ℕ) : ℤ) + (ei : ℤ) * ((∑ j, kR j : ℕ) : ℤ)
        = ((di : ℤ) * ei) * ((dj : ℤ) * ej) := by exact_mod_cast hAB
    have key : (ej : ℤ) * (((∑ j, (dj - kL j) * hj : ℕ) : ℤ)
          + ((∑ j, (di - kR j) * hi : ℕ) : ℤ))
        = (ej : ℤ) * ((di : ℤ) * dj * ej * hi)
          + ((hj : ℤ) * ei - (hi : ℤ) * ej) * ((∑ j, kR j : ℕ) : ℤ) := by
      linear_combination (ej : ℤ) * h1 + (ej : ℤ) * h2 - (hj : ℤ) * h3
    have hD : (1 : ℤ) ≤ (hj : ℤ) * ei - (hi : ℤ) * ej := by
      have : ((hi : ℤ)) * ej < (hj : ℤ) * ei := by exact_mod_cast hslope
      linarith
    have hBz : (1 : ℤ) ≤ ((∑ j, kR j : ℕ) : ℤ) := by exact_mod_cast hB1
    have h5 : (1 : ℤ) ≤ ((hj : ℤ) * ei - (hi : ℤ) * ej) * ((∑ j, kR j : ℕ) : ℤ) := by
      nlinarith
    have hejz : (0 : ℤ) ≤ (ej : ℤ) := by positivity
    linarith [key, h5, mul_le_mul_of_nonneg_left hcon' hejz]
  · push Not at hB
    exfalso
    have hB0 : (∑ j, kR j) = 0 := Finset.sum_eq_zero fun j _ => hB j
    rw [hB0, Nat.mul_zero, Nat.add_zero] at hAB
    obtain ⟨j₀, hj₀⟩ := hne.resolve_right (by push Not; exact fun j => hB j)
    have hA_eq : (∑ j, kL j) = (di * ei) * dj := by
      refine Nat.eq_of_mul_eq_mul_left hej ?_
      rw [hAB]; ring
    have hA_lt : (∑ j, kL j) < (di * ei) * dj := by
      calc (∑ j, kL j) < ∑ _j : Fin (di * ei), dj :=
            Finset.sum_lt_sum (fun j _ => hkL j)
              ⟨j₀, Finset.mem_univ j₀, lt_of_le_of_ne (hkL j₀) hj₀⟩
        _ = (di * ei) * dj := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact absurd hA_eq hA_lt.ne

/-- **Deliverable 4 (CROSS-SIDE).** For sparse twists `F_i` (slope `h_i/e_i`, residual
`ψ_i`) and `F_j` (slope `h_j/e_j`, residual `ψ_j`) with `h_i/e_i < h_j/e_j`, `ψ_j` monic and
`ψ_i(0)` a unit:
`Res(F_i, F_j, d_i·e_i, d_j·e_j) = p^(d_i d_j e_j h_i) · unit`.

Gate item (iii): the unit is `(-1)^(MN)·ψ_i(0)^(d_j e_j) + p·(…)`; the unit constant term on
the shallow side is genuinely needed, residual coprimality is **not**.  No margin hypothesis
is needed for this existence form. -/
theorem resultant_sparseTwist_cross {p N : ℕ} {ψi ψj : (ZMod (p ^ N))[X]} {di dj : ℕ}
    (hdi : ψi.natDegree = di) (hdj : ψj.natDegree = dj) {ei hi ej hj : ℕ}
    (hei : 0 < ei) (hej : 0 < ej) (hslope : hi * ej < hj * ei)
    (hψj : ψj.Monic) (hψi0 : IsUnit (ψi.coeff 0)) :
    ∃ u : (ZMod (p ^ N))ˣ,
      resultant (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
          (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (di * ei) (dj * ej)
        = (p : ZMod (p ^ N)) ^ (di * dj * ej * hi) * u := by
  subst hdi hdj
  -- the transversal product: `1` on the `F_j`-block, `p^(d_i h_i)·ψ_i(0)` on the `F_i`-block
  have hgblock : ∀ j : Fin (ψi.natDegree * ei),
      sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
          (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei) (ψj.natDegree * ej)
          (crossPerm (ψi.natDegree * ei) (ψj.natDegree * ej)
            (Fin.castAdd (ψj.natDegree * ej) j))
          (Fin.castAdd (ψj.natDegree * ej) j) = 1 := by
    intro j
    rw [sylvester_castAdd, crossPerm_castAdd_val,
      if_pos (Set.mem_Icc.mpr ⟨by omega, by omega⟩), Nat.add_sub_cancel,
      Nat.mul_comm ψj.natDegree ej, sparseTwist_coeff_top _ _ hej, hψj.leadingCoeff]
  have hfblock : ∀ j : Fin (ψj.natDegree * ej),
      sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
          (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei) (ψj.natDegree * ej)
          (crossPerm (ψi.natDegree * ei) (ψj.natDegree * ej)
            (Fin.natAdd (ψi.natDegree * ei) j))
          (Fin.natAdd (ψi.natDegree * ei) j)
        = (p : ZMod (p ^ N)) ^ (ψi.natDegree * hi) * ψi.coeff 0 := by
    intro j
    rw [sylvester_natAdd, crossPerm_natAdd_val,
      if_pos (Set.mem_Icc.mpr ⟨le_rfl, by omega⟩), Nat.sub_self,
      sparseTwist_coeff_zero _ _ hei]
  have hτ : ∃ u : (ZMod (p ^ N))ˣ,
      ∏ c, sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
          (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei) (ψj.natDegree * ej)
          (crossPerm (ψi.natDegree * ei) (ψj.natDegree * ej) c) c
        = (p : ZMod (p ^ N)) ^ (ψi.natDegree * ψj.natDegree * ej * hi) * u := by
    refine ⟨(hψi0.pow (ψj.natDegree * ej)).unit, ?_⟩
    rw [Fin.prod_univ_add]
    rw [Finset.prod_congr rfl fun j _ => hgblock j,
      Finset.prod_congr rfl fun j _ => hfblock j, Finset.prod_const_one, one_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
      IsUnit.unit_spec,
      show ψi.natDegree * hi * (ψj.natDegree * ej)
          = ψi.natDegree * ψj.natDegree * ej * hi from by ring]
  -- every other permutation is strictly deeper
  have hoff : ∀ σ : Equiv.Perm (Fin (ψi.natDegree * ei + ψj.natDegree * ej)),
      σ ≠ crossPerm (ψi.natDegree * ei) (ψj.natDegree * ej) →
      (p : ZMod (p ^ N)) ^ (ψi.natDegree * ψj.natDegree * ej * hi + 1)
        ∣ ∏ c, sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
            (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei)
            (ψj.natDegree * ej) (σ c) c := by
    intro σ hσ
    by_cases hzero : ∃ c, sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
        (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei) (ψj.natDegree * ej)
        (σ c) c = 0
    · obtain ⟨c, hc⟩ := hzero
      have hprod : ∏ c' : Fin (ψi.natDegree * ei + ψj.natDegree * ej),
          sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
            (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei)
            (ψj.natDegree * ej) (σ c') c' = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ c) hc
      rw [hprod]
      exact dvd_zero _
    push Not at hzero
    -- column data in the `F_j`-block
    have hcolL : ∀ j : Fin (ψi.natDegree * ei), ∃ k, k ≤ ψj.natDegree
        ∧ (σ (Fin.castAdd (ψj.natDegree * ej) j) : ℕ) = (j : ℕ) + ej * k
        ∧ (p : ZMod (p ^ N)) ^ ((ψj.natDegree - k) * hj)
            ∣ sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
                (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei)
                (ψj.natDegree * ej) (σ (Fin.castAdd (ψj.natDegree * ej) j))
                (Fin.castAdd (ψj.natDegree * ej) j) := by
      intro j
      have hne := hzero (Fin.castAdd (ψj.natDegree * ej) j)
      rw [sylvester_castAdd] at hne
      split_ifs at hne with hIcc
      swap
      · exact absurd rfl hne
      obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hIcc
      obtain ⟨k, hk_eq, hk_le, hk_dvd⟩ :=
        sparseTwist_coeff_structure (p : ZMod (p ^ N)) ψj hej hj hne
      refine ⟨k, hk_le, by rw [← hk_eq]; omega, ?_⟩
      rw [sylvester_castAdd, if_pos hIcc]
      exact hk_dvd
    -- column data in the `F_i`-block
    have hcolR : ∀ j : Fin (ψj.natDegree * ej), ∃ k, k ≤ ψi.natDegree
        ∧ (σ (Fin.natAdd (ψi.natDegree * ei) j) : ℕ) = (j : ℕ) + ei * k
        ∧ (p : ZMod (p ^ N)) ^ ((ψi.natDegree - k) * hi)
            ∣ sylvester (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
                (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (ψi.natDegree * ei)
                (ψj.natDegree * ej) (σ (Fin.natAdd (ψi.natDegree * ei) j))
                (Fin.natAdd (ψi.natDegree * ei) j) := by
      intro j
      have hne := hzero (Fin.natAdd (ψi.natDegree * ei) j)
      rw [sylvester_natAdd] at hne
      split_ifs at hne with hIcc
      swap
      · exact absurd rfl hne
      obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hIcc
      obtain ⟨k, hk_eq, hk_le, hk_dvd⟩ :=
        sparseTwist_coeff_structure (p : ZMod (p ^ N)) ψi hei hi hne
      refine ⟨k, hk_le, by rw [← hk_eq]; omega, ?_⟩
      rw [sylvester_natAdd, if_pos hIcc]
      exact hk_dvd
    choose kL hkL_le hkL_row hkL_dvd using hcolL
    choose kR hkR_le hkR_row hkR_dvd using hcolR
    -- the row-sum identity: `ej·ΣkL + ei·ΣkR = M·N`
    have hrowsum : ∑ c : Fin (ψi.natDegree * ei + ψj.natDegree * ej), ((σ c : ℕ))
        = ∑ c : Fin (ψi.natDegree * ei + ψj.natDegree * ej), (c : ℕ) :=
      Equiv.sum_comp σ _
    rw [Fin.sum_univ_add (f := fun c : Fin (ψi.natDegree * ei + ψj.natDegree * ej) =>
        ((σ c : ℕ))),
      Fin.sum_univ_add (f := fun c : Fin (ψi.natDegree * ei + ψj.natDegree * ej) =>
        (c : ℕ))] at hrowsum
    simp only [hkL_row, hkR_row, Fin.val_castAdd, Fin.val_natAdd] at hrowsum
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hrowsum
    have hAB : ej * (∑ j, kL j) + ei * (∑ j, kR j)
        = (ψi.natDegree * ei) * (ψj.natDegree * ej) := by
      have hNM : (ψj.natDegree * ej) * (ψi.natDegree * ei)
          = (ψi.natDegree * ei) * (ψj.natDegree * ej) := Nat.mul_comm _ _
      linarith [hrowsum, hNM]
    -- `σ ≠ τ` in terms of the column data
    have hne' : (∃ j, kL j ≠ ψj.natDegree) ∨ (∃ j, kR j ≠ 0) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hL, hR⟩ := hcon
      refine hσ (Equiv.ext fun c => ?_)
      induction c using Fin.addCases with
      | left j =>
        refine Fin.ext ?_
        rw [hkL_row j, hL j, crossPerm_castAdd_val, Nat.mul_comm ej ψj.natDegree,
          Nat.add_comm]
      | right j =>
        refine Fin.ext ?_
        rw [hkR_row j, hR j, Nat.mul_zero, Nat.add_zero, crossPerm_natAdd_val]
    -- assemble: total valuation ≥ V + 1, then entrywise divisibility
    have hT := cross_count hslope hej kL kR hkL_le hkR_le hAB hne'
    refine dvd_trans (pow_dvd_pow (p : ZMod (p ^ N)) hT) ?_
    rw [Fin.prod_univ_add, pow_add]
    exact mul_dvd_mul
      (by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ => hkL_dvd j)
      (by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ => hkR_dvd j)
  exact det_eq_pow_mul_unit_of_dominant_transversal _ (isNilpotent_p_zmod p N)
    (crossPerm (ψi.natDegree * ei) (ψj.natDegree * ej))
    (ψi.natDegree * ψj.natDegree * ej * hi) hτ hoff


end LeanUrat.OM.SparseResultant
