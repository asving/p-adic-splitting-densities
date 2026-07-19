/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.LinearFiber

/-!
# F-B2 — HenselCount: level-N quantitative Hensel with fiber count

Fix `[Fact p.Prime]`, `N`, and monic `A₀ B₀ : (ZMod (p^N))[X]` of `natDegree` `a`, `b`, with
`resultant A₀ B₀ a b = p^c * unit` and the Hensel margin `2*c < N`.  On the coefficient cells

* `cell P₀ d k := {P | P.Monic ∧ P.natDegree = d ∧ ∀ i, p^k ∣ (P - P₀).coeff i}`

(with `k = c+1`), the multiplication map `(A, B) ↦ A*B` has all fibers over its image of size
exactly `p^c` (`fiber_card`), and the image count satisfies
`Nat.card (image) * p^c = Nat.card cellA * Nat.card cellB` (`image_card`).

**Cell encoding.**  Cells are sets of raw polynomials with a *coefficientwise divisibility*
congruence `p^k ∣ (P - P₀).coeff i` (not `Set.range`-membership and not `degreeLT`-subtypes):
divisibility composes with `dvd_trans`/`dvd_add` in every bootstrap step below, and raw
polynomials avoid `degreeLT`-coercion noise; the increment-with-bounded-degree view is recovered
on demand through `sub_coeff_eq_zero_of_ge` (two monics of the same degree differ in degree `< d`).

**The ladder.**

1. *Sylvester bridge* (`sylvester_mulVec_coeff`, `polyOf_sylvester_mulVec`,
   `sylvesterMulVec_eq`): under the identification `polyOf : (Fin d → R) → R[X]`
   (coefficient vector ↦ polynomial of degree `< d`), the matrix-vector action of mathlib's
   `Polynomial.sylvester f g m n` is the linear map `(α, β) ↦ g*α + f*β`, where `α := polyOf`
   of the **first `m`** coordinates (`leftPart`, paired with `g` — mathlib's `sylvester` puts
   the `g`-block in the first `m` columns, cf. `Fin.addCases` in its definition and
   `Polynomial.sylvesterMap`/`toMatrix_sylvesterMap'`) and `β := polyOf` of the **last `n`**
   coordinates (`rightPart`, paired with `f`).  No reindexing is used: the identification is
   on-the-nose, so F-B1's `mulVec` counts apply verbatim.
2. *Resultant stability* (`det_sylvester_stable`, `resultant_stable`): a `p^(c+1)`-perturbation
   of the coefficients moves `det (sylvester · ·)` by a `p^(c+1)`-multiple (`dvd_det_sub`, via
   the quotient ring `R ⧸ span {p^(c+1)}`), and `p^c*u + p^(c+1)*x = p^c*(u + p*x)` is again
   `p^c * unit` (`p*x` is nilpotent).
3. *The torsor* (`fiber_card`): the fiber through `(A, B)` is in bijection
   (`fiberEquivKer`) with the kernel of `(sylvester A B a b).mulVec`, whose size is `p^c` by
   F-B1 (`LinearFiber.card_ker_mulVec_of_det`).  The two directions:
   * kernel → fiber (`ker_shift_mem_fiber`): a kernel vector is automatically
     `p^(N-c)`-divisible (`dvd_of_mulVec_eq_zero`: multiply `M *ᵥ x = 0` by the adjugate,
     cancel `p^c`), hence the quadratic term `α*β` of `(A+α)(B+β)` is killed by
     `p^(2(N-c)) = 0` — **no Newton correction is ever needed**;
   * fiber → kernel (`fiber_sub_dvd`, `mulVec_vecOf_eq_zero`): the blueprint's Newton
     *iteration* collapses to a divisibility *bootstrap*: increments of two factorizations
     satisfy `S(α,β) = -α*β`, and `p^k`-divisibility of `(α,β)` upgrades to
     `p^(min (2k-c) (N-c))`-divisibility through the adjugate (`dvd_of_mulVec_dvd`); after
     `N` rounds the increments are `p^(N-c)`-divisible, so `α*β = 0` and `(α,β)` lies in the
     honest kernel.
4. *Assembly* (`image_card`): fiber-sum via `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`.

**Blueprint notes.** (i) The pinned rescaling lemma (`p^(c+1)`-divisible sublattice ≅ box at
level `N-c-1`, F-B1 at the lower level) is *not needed*: the adjugate bootstrap stays at level
`N`, which also removes the boundary defect the rescale would have had at `N = 2c+1` (the
rescale needs `2c+1 < N`, which does **not** follow from `2c < N`; this file needs only
`2c < N` throughout).  (ii) Monicity/degree hypotheses on `A₀, B₀` are not needed for any of
the results: the cells impose monicity and degree on their members directly.

This is blueprint item F-B2 (count form; everything is `Nat.card`, no measure theory).
-/

set_option linter.style.longLine false

namespace LeanUrat.OM.HenselCount

open Matrix Polynomial

/-! ## The coefficient-vector ↔ polynomial dictionary -/

section PolyOf

variable {S : Type*} [Semiring S]

/-- Left block (first `m` coordinates) of a `Fin (m + n)`-indexed vector. -/
def leftPart {α : Type*} {m n : ℕ} (x : Fin (m + n) → α) (j : Fin m) : α :=
  x (Fin.castAdd n j)

/-- Right block (last `n` coordinates) of a `Fin (m + n)`-indexed vector. -/
def rightPart {α : Type*} {m n : ℕ} (x : Fin (m + n) → α) (j : Fin n) : α :=
  x (Fin.natAdd m j)

/-- The polynomial `∑ j < d, v j • X^j` with coefficient vector `v`. -/
noncomputable def polyOf {d : ℕ} (v : Fin d → S) : S[X] :=
  ∑ j : Fin d, Polynomial.monomial (j : ℕ) (v j)

theorem coeff_polyOf {d : ℕ} (v : Fin d → S) (k : ℕ) :
    (polyOf v).coeff k = if h : k < d then v ⟨k, h⟩ else 0 := by
  rw [polyOf, Polynomial.finsetSum_coeff]
  by_cases h : k < d
  · rw [dif_pos h, Finset.sum_eq_single (⟨k, h⟩ : Fin d)]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro j _ hj
      rw [Polynomial.coeff_monomial, if_neg (fun hjk : (j : ℕ) = k => hj (Fin.ext hjk))]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Polynomial.coeff_monomial, if_neg (fun hjk : (j : ℕ) = k => h (hjk ▸ j.isLt))]

theorem coeff_polyOf_of_lt {d : ℕ} (v : Fin d → S) (j : Fin d) :
    (polyOf v).coeff (j : ℕ) = v j := by
  rw [coeff_polyOf, dif_pos j.isLt]

theorem coeff_polyOf_of_le {d : ℕ} (v : Fin d → S) {k : ℕ} (h : d ≤ k) :
    (polyOf v).coeff k = 0 := by
  rw [coeff_polyOf, dif_neg (by omega)]

/-- `polyOf` is a left inverse of coefficient extraction on polynomials with vanishing
coefficients from `d` on. -/
theorem polyOf_coeff {d : ℕ} {P : S[X]} (h : ∀ i, d ≤ i → P.coeff i = 0) :
    polyOf (fun j : Fin d => P.coeff (j : ℕ)) = P := by
  ext k
  rw [coeff_polyOf]
  by_cases hk : k < d
  · rw [dif_pos hk]
  · rw [dif_neg hk, h k (by omega)]

/-- `(P * monomial j a).coeff k`, resolved. -/
theorem coeff_mul_monomial' (P : S[X]) (j : ℕ) (r : S) (k : ℕ) :
    (P * Polynomial.monomial j r).coeff k
      = if j ≤ k then P.coeff (k - j) * r else 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, Polynomial.coeff_mul_X_pow']
  split_ifs with h
  · rw [Polynomial.coeff_mul_C]
  · rfl

/-- The interleaved vector with left block the coefficients of `α` and right block the
coefficients of `β` — the coordinate avatar of an increment pair `(α, β)`. -/
def vecOf {m : ℕ} (n : ℕ) (α β : S[X]) : Fin (m + n) → S :=
  Fin.addCases (fun j => α.coeff (j : ℕ)) (fun j => β.coeff (j : ℕ))

variable {m n : ℕ}

@[simp] theorem vecOf_castAdd (α β : S[X]) (j : Fin m) :
    vecOf (m := m) n α β (Fin.castAdd n j) = α.coeff (j : ℕ) := by
  simp [vecOf]

@[simp] theorem vecOf_natAdd (α β : S[X]) (j : Fin n) :
    vecOf (m := m) n α β (Fin.natAdd m j) = β.coeff (j : ℕ) := by
  simp [vecOf]

theorem leftPart_vecOf {α β : S[X]} :
    leftPart (vecOf (m := m) n α β) = fun j : Fin m => α.coeff (j : ℕ) :=
  funext fun j => vecOf_castAdd α β j

theorem rightPart_vecOf {α β : S[X]} :
    rightPart (vecOf (m := m) n α β) = fun j : Fin n => β.coeff (j : ℕ) :=
  funext fun j => vecOf_natAdd α β j

theorem polyOf_leftPart_vecOf {α β : S[X]} (h : ∀ i, m ≤ i → α.coeff i = 0) :
    polyOf (leftPart (vecOf (m := m) n α β)) = α := by
  rw [leftPart_vecOf]
  exact polyOf_coeff h

theorem polyOf_rightPart_vecOf {α β : S[X]} (h : ∀ i, n ≤ i → β.coeff i = 0) :
    polyOf (rightPart (vecOf (m := m) n α β)) = β := by
  rw [rightPart_vecOf]
  exact polyOf_coeff h

end PolyOf

/-! ## Deliverable 1 — the Sylvester-map bridge -/

section Bridge

variable {S : Type*} [Semiring S]

/-- Entry of the Sylvester matrix in the `g`-block (first `m` columns). -/
theorem sylvester_apply_castAdd (f g : S[X]) (m n : ℕ) (i : Fin (m + n)) (j : Fin m) :
    Polynomial.sylvester f g m n i (Fin.castAdd n j)
      = if (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + n then g.coeff ((i : ℕ) - (j : ℕ))
        else 0 := by
  simp [Polynomial.sylvester, Set.mem_Icc]

/-- Entry of the Sylvester matrix in the `f`-block (last `n` columns). -/
theorem sylvester_apply_natAdd (f g : S[X]) (m n : ℕ) (i : Fin (m + n)) (j : Fin n) :
    Polynomial.sylvester f g m n i (Fin.natAdd m j)
      = if (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + m then f.coeff ((i : ℕ) - (j : ℕ))
        else 0 := by
  simp [Polynomial.sylvester, Set.mem_Icc]

/-- One Sylvester column against one vector entry is one shifted-polynomial coefficient. -/
theorem sylvester_term_eq {P : S[X]} {dP : ℕ} (hP : P.natDegree ≤ dP) (j k : ℕ) (r : S) :
    (if j ≤ k ∧ k ≤ j + dP then P.coeff (k - j) else 0) * r
      = (P * Polynomial.monomial j r).coeff k := by
  rw [coeff_mul_monomial']
  by_cases h1 : j ≤ k
  · by_cases h2 : k ≤ j + dP
    · rw [if_pos ⟨h1, h2⟩, if_pos h1]
    · rw [if_neg (fun hand : j ≤ k ∧ k ≤ j + dP => h2 hand.2), if_pos h1,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  · rw [if_neg (fun hand : j ≤ k ∧ k ≤ j + dP => h1 hand.1), if_neg h1, zero_mul]

/-- **F-B2 deliverable 1 (pointwise form).**  The `mulVec` action of
`Polynomial.sylvester f g m n` computes, under the `polyOf` identification, the coefficients of
`g * (left block) + f * (right block)`.  Orientation: the first `m` coordinates are the
coefficient vector of the polynomial multiplying `g` (mathlib's `sylvester` has the `g`-block
in the first `m` columns), the last `n` those of the polynomial multiplying `f`. -/
theorem sylvester_mulVec_coeff (f g : S[X]) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (x : Fin (m + n) → S) (i : Fin (m + n)) :
    (Polynomial.sylvester f g m n).mulVec x i
      = (g * polyOf (leftPart x) + f * polyOf (rightPart x)).coeff (i : ℕ) := by
  have hL : (g * polyOf (leftPart x)).coeff (i : ℕ)
      = ∑ j : Fin m, (g * Polynomial.monomial (j : ℕ) (leftPart x j)).coeff (i : ℕ) := by
    rw [polyOf, Finset.mul_sum, Polynomial.finsetSum_coeff]
  have hR : (f * polyOf (rightPart x)).coeff (i : ℕ)
      = ∑ j : Fin n, (f * Polynomial.monomial (j : ℕ) (rightPart x j)).coeff (i : ℕ) := by
    rw [polyOf, Finset.mul_sum, Polynomial.finsetSum_coeff]
  rw [Polynomial.coeff_add, hL, hR]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [sylvester_apply_castAdd]
    exact sylvester_term_eq hg (j : ℕ) (i : ℕ) (x (Fin.castAdd n j))
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [sylvester_apply_natAdd]
    exact sylvester_term_eq hf (j : ℕ) (i : ℕ) (x (Fin.natAdd m j))

/-- The polynomial `g * polyOf (leftPart x) + f * polyOf (rightPart x)` has no coefficients
at indices `≥ m + n`. -/
theorem coeff_mul_polyOf_eq_zero {P : S[X]} {dP : ℕ} (hP : P.natDegree ≤ dP) {d : ℕ}
    (v : Fin d → S) {k : ℕ} (hk : dP + d ≤ k) :
    (P * polyOf v).coeff k = 0 := by
  rw [polyOf, Finset.mul_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_mul_monomial']
  have hj := j.isLt
  split_ifs with h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  · rfl

theorem coeff_combo_eq_zero (f g : S[X]) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (x : Fin (m + n) → S) {k : ℕ}
    (hk : m + n ≤ k) :
    (g * polyOf (leftPart x) + f * polyOf (rightPart x)).coeff k = 0 := by
  rw [Polynomial.coeff_add, coeff_mul_polyOf_eq_zero hg (leftPart x) (by omega),
    coeff_mul_polyOf_eq_zero hf (rightPart x) (by omega), add_zero]

/-- **F-B2 deliverable 1 (packaged form).**  `polyOf` of the `mulVec` image is exactly the
polynomial combination — the Sylvester matrix *is* the multiplication map's linearization. -/
theorem polyOf_sylvester_mulVec (f g : S[X]) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (x : Fin (m + n) → S) :
    polyOf ((Polynomial.sylvester f g m n).mulVec x)
      = g * polyOf (leftPart x) + f * polyOf (rightPart x) := by
  ext k
  rw [coeff_polyOf]
  by_cases hk : k < m + n
  · rw [dif_pos hk, sylvester_mulVec_coeff f g hf hg x ⟨k, hk⟩]
  · rw [dif_neg hk, coeff_combo_eq_zero f g hf hg x (by omega)]

/-- Kernel membership under the identification: `mulVec = 0` iff the polynomial combination
vanishes. -/
theorem mulVec_eq_zero_iff_combo (f g : S[X]) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (x : Fin (m + n) → S) :
    (Polynomial.sylvester f g m n).mulVec x = 0
      ↔ g * polyOf (leftPart x) + f * polyOf (rightPart x) = 0 := by
  constructor
  · intro h
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < m + n
    · have h' := congrFun h (⟨k, hk⟩ : Fin (m + n))
      rw [sylvester_mulVec_coeff f g hf hg] at h'
      exact h'
    · rw [coeff_combo_eq_zero f g hf hg x (by omega)]
  · intro h
    funext i
    rw [sylvester_mulVec_coeff f g hf hg, h, Polynomial.coeff_zero]
    rfl

end Bridge

/-! ## Deliverable 2 — determinant/resultant stability under `p^(c+1)`-perturbation -/

section DetPerturb

variable {S : Type*} [CommRing S]

/-- Coefficientwise divisibility of products of polynomials. -/
theorem dvd_coeff_mul {x y : S} {P Q : S[X]}
    (hP : ∀ i, x ∣ P.coeff i) (hQ : ∀ i, y ∣ Q.coeff i) (k : ℕ) :
    x * y ∣ (P * Q).coeff k := by
  rw [Polynomial.coeff_mul]
  exact Finset.dvd_sum fun ij _ => mul_dvd_mul (hP ij.1) (hQ ij.2)

/-- If all entries of `M - M'` are divisible by `d`, so is `det M - det M'` (pass to the
quotient by `span {d}`, where the matrices agree). -/
theorem dvd_det_sub {k : ℕ} {d : S} {M M' : Matrix (Fin k) (Fin k) S}
    (h : ∀ i j, d ∣ M i j - M' i j) : d ∣ M.det - M'.det := by
  rw [← Ideal.mem_span_singleton]
  have hmap : (Ideal.Quotient.mk (Ideal.span {d})).mapMatrix M
      = (Ideal.Quotient.mk (Ideal.span {d})).mapMatrix M' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
    exact h i j
  have hdet := congrArg Matrix.det hmap
  rw [← RingHom.map_det, ← RingHom.map_det] at hdet
  rwa [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]

/-- Entries of the Sylvester matrix move by `d`-multiples under coefficientwise
`d`-perturbation of the two polynomials. -/
theorem dvd_sylvester_sub {f g f' g' : S[X]} {m n : ℕ} {d : S}
    (hf : ∀ i, d ∣ (f' - f).coeff i) (hg : ∀ i, d ∣ (g' - g).coeff i)
    (i j : Fin (m + n)) :
    d ∣ Polynomial.sylvester f' g' m n i j - Polynomial.sylvester f g m n i j := by
  induction j using Fin.addCases with
  | left j =>
    rw [sylvester_apply_castAdd, sylvester_apply_castAdd]
    split_ifs with hcond
    · have h := hg ((i : ℕ) - (j : ℕ))
      rwa [Polynomial.coeff_sub] at h
    · simp
  | right j =>
    rw [sylvester_apply_natAdd, sylvester_apply_natAdd]
    split_ifs with hcond
    · have h := hf ((i : ℕ) - (j : ℕ))
      rwa [Polynomial.coeff_sub] at h
    · simp

end DetPerturb

/-! ## The `ZMod (p ^ N)` setting -/

variable {p : ℕ} [hp : Fact p.Prime] {N : ℕ}

/-- The coefficient cell around `P₀`: monic of `natDegree = d`, congruent to `P₀`
coefficientwise mod `p^k`. -/
def cell (P₀ : (ZMod (p ^ N))[X]) (d k : ℕ) : Set ((ZMod (p ^ N))[X]) :=
  {P | P.Monic ∧ P.natDegree = d ∧ ∀ i, (p : ZMod (p ^ N)) ^ k ∣ (P - P₀).coeff i}

omit hp in
theorem mem_cell_self {P₀ : (ZMod (p ^ N))[X]} {d : ℕ} (hP₀ : P₀.Monic)
    (hd : P₀.natDegree = d) (k : ℕ) : P₀ ∈ cell P₀ d k :=
  ⟨hP₀, hd, fun i => by rw [sub_self, Polynomial.coeff_zero]; exact dvd_zero _⟩

/-- Two monics of the same `natDegree = d` differ only in degrees `< d`. -/
theorem sub_coeff_eq_zero_of_ge {S : Type*} [Ring S] {P Q : S[X]} {d : ℕ}
    (hP : P.Monic) (hQ : Q.Monic) (hPd : P.natDegree = d) (hQd : Q.natDegree = d)
    {i : ℕ} (hi : d ≤ i) : (P - Q).coeff i = 0 := by
  rw [Polynomial.coeff_sub]
  by_cases hi' : d = i
  · subst hi'
    have h1 : P.coeff d = 1 := by rw [← hPd]; exact hP.coeff_natDegree
    have h2 : Q.coeff d = 1 := by rw [← hQd]; exact hQ.coeff_natDegree
    rw [h1, h2, sub_self]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPd]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQd]; omega), sub_self]

omit hp in
/-- Differences of cell members are coefficientwise `p^k`-divisible. -/
theorem cell_sub_dvd {P₀ : (ZMod (p ^ N))[X]} {d k : ℕ} {P Q : (ZMod (p ^ N))[X]}
    (hP : P ∈ cell P₀ d k) (hQ : Q ∈ cell P₀ d k) (i : ℕ) :
    (p : ZMod (p ^ N)) ^ k ∣ (P - Q).coeff i := by
  have hPQ : P - Q = P - P₀ - (Q - P₀) := by ring
  rw [hPQ, Polynomial.coeff_sub]
  exact dvd_sub (hP.2.2 i) (hQ.2.2 i)

/-- Monic + degree bookkeeping for a perturbation supported in degrees `< d`. -/
theorem monic_add_of_coeff {S : Type*} [Semiring S] [Nontrivial S] {P Q : S[X]} {d : ℕ}
    (hP : P.Monic) (hPd : P.natDegree = d) (hQ : ∀ i, d ≤ i → Q.coeff i = 0) :
    (P + Q).Monic ∧ (P + Q).natDegree = d := by
  have hcd : (P + Q).coeff d = 1 := by
    rw [Polynomial.coeff_add, hQ d le_rfl, add_zero, ← hPd]
    exact hP.coeff_natDegree
  have hup : ∀ i, d < i → (P + Q).coeff i = 0 := by
    intro i hi
    rw [Polynomial.coeff_add, hQ i hi.le,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), add_zero]
  have hle : (P + Q).natDegree ≤ d := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hup
  have hge : d ≤ (P + Q).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcd]; exact one_ne_zero)
  have hdeg : (P + Q).natDegree = d := le_antisymm hle hge
  refine ⟨?_, hdeg⟩
  show (P + Q).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, hdeg, hcd]

/-! ### Deliverable 2, concluded -/

omit hp in
/-- **F-B2 deliverable 2 (determinant form).**  `det (sylvester · · a b)` keeps the exact
`p^c * unit` shape under coefficientwise `p^(c+1)`-perturbation. -/
theorem det_sylvester_stable {a b c : ℕ} {A₀ B₀ A B : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A₀ B₀ a b).det = (p : ZMod (p ^ N)) ^ c * u)
    (hA : ∀ i, (p : ZMod (p ^ N)) ^ (c + 1) ∣ (A - A₀).coeff i)
    (hB : ∀ i, (p : ZMod (p ^ N)) ^ (c + 1) ∣ (B - B₀).coeff i) :
    ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A B a b).det = (p : ZMod (p ^ N)) ^ c * u := by
  obtain ⟨u, hu⟩ := hres
  obtain ⟨x, hx⟩ := dvd_det_sub (M := Polynomial.sylvester A B a b)
    (M' := Polynomial.sylvester A₀ B₀ a b) (fun i j => dvd_sylvester_sub hA hB i j)
  have hnil : IsNilpotent ((p : ZMod (p ^ N)) * x) := by
    refine ⟨N, ?_⟩
    rw [mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have hunit : IsUnit ((u : ZMod (p ^ N)) + (p : ZMod (p ^ N)) * x) :=
    hnil.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  have hdet : (Polynomial.sylvester A B a b).det
      = (p : ZMod (p ^ N)) ^ c * u + (p : ZMod (p ^ N)) ^ (c + 1) * x := by
    rw [← hu]
    linear_combination hx
  rw [hdet, pow_succ]
  ring

omit hp in
/-- **F-B2 deliverable 2 (`resultant_stable`).**  For `A ≡ A₀`, `B ≡ B₀` mod `p^(c+1)`
(coefficientwise, i.e. on the cells), the resultant of `(A, B)` is still `p^c * unit`. -/
theorem resultant_stable {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A₀ B₀ a b = (p : ZMod (p ^ N)) ^ c * u)
    {A B : (ZMod (p ^ N))[X]}
    (hA : A ∈ cell A₀ a (c + 1)) (hB : B ∈ cell B₀ b (c + 1)) :
    ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A B a b = (p : ZMod (p ^ N)) ^ c * u :=
  det_sylvester_stable hres hA.2.2 hB.2.2

/-! ## Deliverable 3 — the torsor

The adjugate toolkit: from `det M = p^c * unit`, divisibility of `M *ᵥ x` upgrades to
divisibility of `x` (at the cost of `p^c`, floored at the annihilator level `N - c`). -/

/-- **Adjugate divisibility upgrade.**  If `det M = p^c * u` (`c ≤ k`, `c ≤ N`) and every entry
of `M *ᵥ x` is divisible by `p^k`, then every entry of `x` is divisible by
`p^(min (k-c) (N-c))`. -/
theorem dvd_of_mulVec_dvd {nn : ℕ} (M : Matrix (Fin nn) (Fin nn) (ZMod (p ^ N))) {c k : ℕ}
    (hcN : c ≤ N) (hck : c ≤ k)
    (hdet : ∃ u : (ZMod (p ^ N))ˣ, M.det = (p : ZMod (p ^ N)) ^ c * u)
    {x : Fin nn → ZMod (p ^ N)}
    (hdvd : ∀ i, (p : ZMod (p ^ N)) ^ k ∣ M.mulVec x i) (i : Fin nn) :
    (p : ZMod (p ^ N)) ^ min (k - c) (N - c) ∣ x i := by
  obtain ⟨u, hu⟩ := hdet
  have hadj : M.det • x = (Matrix.adjugate M).mulVec (M.mulVec x) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h1 : (p : ZMod (p ^ N)) ^ k ∣ (M.det • x) i := by
    rw [hadj]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hdvd j) _
  have hentry : (p : ZMod (p ^ N)) ^ k ∣ M.det * x i := by
    rwa [Pi.smul_apply, smul_eq_mul] at h1
  rw [hu, mul_assoc] at hentry
  obtain ⟨y, hy⟩ := hentry
  have h0 : (p : ZMod (p ^ N)) ^ c
      * ((u : ZMod (p ^ N)) * x i - (p : ZMod (p ^ N)) ^ (k - c) * y) = 0 := by
    have hsplit : (p : ZMod (p ^ N)) ^ k
        = (p : ZMod (p ^ N)) ^ c * (p : ZMod (p ^ N)) ^ (k - c) := by
      rw [← pow_add]
      congr 1
      omega
    rw [mul_sub, hy, hsplit]
    ring
  obtain ⟨z, hz⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero hcN h0
  have hxi : (u : ZMod (p ^ N)) * x i
      = (p : ZMod (p ^ N)) ^ (k - c) * y + (p : ZMod (p ^ N)) ^ (N - c) * z := by
    rw [sub_eq_iff_eq_add.mp hz]
    ring
  have hdvdu : (p : ZMod (p ^ N)) ^ min (k - c) (N - c) ∣ (u : ZMod (p ^ N)) * x i := by
    rw [hxi]
    exact dvd_add (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_left _ _)) y)
      (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_right _ _)) z)
  have hxieq : x i = (u⁻¹ : (ZMod (p ^ N))ˣ) * ((u : ZMod (p ^ N)) * x i) := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hxieq]
  exact Dvd.dvd.mul_left hdvdu _

/-- Kernel vectors of a `det = p^c * unit` matrix are automatically `p^(N-c)`-divisible. -/
theorem dvd_of_mulVec_eq_zero {nn : ℕ} (M : Matrix (Fin nn) (Fin nn) (ZMod (p ^ N))) {c : ℕ}
    (hcN : c ≤ N)
    (hdet : ∃ u : (ZMod (p ^ N))ˣ, M.det = (p : ZMod (p ^ N)) ^ c * u)
    {x : Fin nn → ZMod (p ^ N)} (hx : M.mulVec x = 0) (i : Fin nn) :
    (p : ZMod (p ^ N)) ^ (N - c) ∣ x i := by
  have h := dvd_of_mulVec_dvd M (k := N) hcN hcN hdet
    (fun j => by rw [hx]; exact dvd_zero _) i
  rwa [min_self] at h

omit hp in
/-- A product of two polynomials with `p^(N-c)`-divisible coefficients vanishes
(given the margin `2*c ≤ N`). -/
theorem mul_eq_zero_of_coeff_dvd {c : ℕ} (h2c : 2 * c ≤ N) {P Q : (ZMod (p ^ N))[X]}
    (hP : ∀ i, (p : ZMod (p ^ N)) ^ (N - c) ∣ P.coeff i)
    (hQ : ∀ i, (p : ZMod (p ^ N)) ^ (N - c) ∣ Q.coeff i) :
    P * Q = 0 := by
  ext k
  rw [Polynomial.coeff_zero]
  have h := dvd_coeff_mul hP hQ k
  rw [← pow_add] at h
  have hz : (p : ZMod (p ^ N)) ^ (N - c + (N - c)) = 0 := by
    have hsplit : (p : ZMod (p ^ N)) ^ (N - c + (N - c))
        = (p : ZMod (p ^ N)) ^ N * (p : ZMod (p ^ N)) ^ (N - c + (N - c) - N) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  rw [hz] at h
  exact zero_dvd_iff.mp h

/-! ### Torsor direction 1 (fiber → kernel): the divisibility bootstrap

The blueprint's Newton iteration, collapsed: for two factorizations in the cell the increments
`(α, β) = (A' - A, B' - B)` satisfy `B*α + A*β = -α*β`; if the increments are coefficientwise
`p^k`-divisible then the right side is `p^(2k)`-divisible, and the adjugate upgrade pushes the
increments to `p^(min (2k-c) (N-c))` — a strict gain until the annihilator floor `N - c`
is reached (invariant `min (c+1+j) (N-c)` after `j` rounds; `N` rounds suffice). -/

theorem fiber_sub_dvd {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]} (hc : 2 * c < N)
    {A B A' B' : (ZMod (p ^ N))[X]}
    (hdet : ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A B a b).det = (p : ZMod (p ^ N)) ^ c * u)
    (hA : A ∈ cell A₀ a (c + 1)) (hB : B ∈ cell B₀ b (c + 1))
    (hA' : A' ∈ cell A₀ a (c + 1)) (hB' : B' ∈ cell B₀ b (c + 1))
    (hprod : A' * B' = A * B) :
    (∀ i, (p : ZMod (p ^ N)) ^ (N - c) ∣ (A' - A).coeff i)
      ∧ ∀ i, (p : ZMod (p ^ N)) ^ (N - c) ∣ (B' - B).coeff i := by
  have hαdeg : ∀ i, a ≤ i → (A' - A).coeff i = 0 := fun i hi =>
    sub_coeff_eq_zero_of_ge hA'.1 hA.1 hA'.2.1 hA.2.1 hi
  have hβdeg : ∀ i, b ≤ i → (B' - B).coeff i = 0 := fun i hi =>
    sub_coeff_eq_zero_of_ge hB'.1 hB.1 hB'.2.1 hB.2.1 hi
  have hkey : B * (A' - A) + A * (B' - B) = -((A' - A) * (B' - B)) := by
    linear_combination hprod
  have main : ∀ j : ℕ,
      (∀ i, (p : ZMod (p ^ N)) ^ min (c + 1 + j) (N - c) ∣ (A' - A).coeff i)
        ∧ ∀ i, (p : ZMod (p ^ N)) ^ min (c + 1 + j) (N - c) ∣ (B' - B).coeff i := by
    intro j
    induction j with
    | zero =>
      constructor <;> intro i
      · exact dvd_trans (pow_dvd_pow _ (by omega : min (c + 1 + 0) (N - c) ≤ c + 1))
          (cell_sub_dvd hA' hA i)
      · exact dvd_trans (pow_dvd_pow _ (by omega : min (c + 1 + 0) (N - c) ≤ c + 1))
          (cell_sub_dvd hB' hB i)
    | succ j ih =>
      obtain ⟨ihα, ihβ⟩ := ih
      set k := min (c + 1 + j) (N - c) with hk
      have hq : ∀ i : ℕ, (p : ZMod (p ^ N)) ^ (k + k) ∣ ((A' - A) * (B' - B)).coeff i := by
        intro i
        rw [pow_add]
        exact dvd_coeff_mul ihα ihβ i
      have hmv : ∀ i : Fin (a + b), (p : ZMod (p ^ N)) ^ (k + k)
          ∣ (Polynomial.sylvester A B a b).mulVec (vecOf (m := a) b (A' - A) (B' - B)) i := by
        intro i
        rw [sylvester_mulVec_coeff A B (le_of_eq hA.2.1) (le_of_eq hB.2.1),
          polyOf_leftPart_vecOf hαdeg, polyOf_rightPart_vecOf hβdeg, hkey,
          Polynomial.coeff_neg]
        exact dvd_neg.mpr (hq (i : ℕ))
      have hstep := dvd_of_mulVec_dvd (Polynomial.sylvester A B a b)
        (by omega : c ≤ N) (by omega : c ≤ k + k) hdet hmv
      constructor <;> intro i
      · by_cases hi : i < a
        · have h := hstep (Fin.castAdd b ⟨i, hi⟩)
          rw [vecOf_castAdd] at h
          exact dvd_trans (pow_dvd_pow _ (by omega)) h
        · rw [hαdeg i (by omega)]
          exact dvd_zero _
      · by_cases hi : i < b
        · have h := hstep (Fin.natAdd a ⟨i, hi⟩)
          rw [vecOf_natAdd] at h
          exact dvd_trans (pow_dvd_pow _ (by omega)) h
        · rw [hβdeg i (by omega)]
          exact dvd_zero _
  obtain ⟨hα, hβ⟩ := main N
  constructor <;> intro i
  · have h := hα i
    rwa [min_eq_right (by omega)] at h
  · have h := hβ i
    rwa [min_eq_right (by omega)] at h

/-- **Torsor direction 1, concluded.**  The increment vector of any second factorization in
the cell lies in the kernel of the Sylvester matrix at the base point. -/
theorem mulVec_vecOf_eq_zero {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]} (hc : 2 * c < N)
    {A B A' B' : (ZMod (p ^ N))[X]}
    (hdet : ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A B a b).det = (p : ZMod (p ^ N)) ^ c * u)
    (hA : A ∈ cell A₀ a (c + 1)) (hB : B ∈ cell B₀ b (c + 1))
    (hA' : A' ∈ cell A₀ a (c + 1)) (hB' : B' ∈ cell B₀ b (c + 1))
    (hprod : A' * B' = A * B) :
    (Polynomial.sylvester A B a b).mulVec (vecOf (m := a) b (A' - A) (B' - B)) = 0 := by
  have hαdeg : ∀ i, a ≤ i → (A' - A).coeff i = 0 := fun i hi =>
    sub_coeff_eq_zero_of_ge hA'.1 hA.1 hA'.2.1 hA.2.1 hi
  have hβdeg : ∀ i, b ≤ i → (B' - B).coeff i = 0 := fun i hi =>
    sub_coeff_eq_zero_of_ge hB'.1 hB.1 hB'.2.1 hB.2.1 hi
  obtain ⟨hα, hβ⟩ := fiber_sub_dvd hc hdet hA hB hA' hB' hprod
  have hzero : (A' - A) * (B' - B) = 0 :=
    mul_eq_zero_of_coeff_dvd (by omega) hα hβ
  have hkey : B * (A' - A) + A * (B' - B) = -((A' - A) * (B' - B)) := by
    linear_combination hprod
  funext i
  rw [sylvester_mulVec_coeff A B (le_of_eq hA.2.1) (le_of_eq hB.2.1),
    polyOf_leftPart_vecOf hαdeg, polyOf_rightPart_vecOf hβdeg, hkey, hzero, neg_zero,
    Polynomial.coeff_zero]
  rfl

/-! ### Torsor direction 2 (kernel → fiber): shifting by a kernel element -/

/-- **Torsor direction 2.**  Shifting a cell factorization by (the polynomials of) a kernel
vector of its Sylvester matrix stays in the cell and preserves the product: kernel vectors are
`p^(N-c)`-divisible, so the quadratic term dies outright — the Newton correction is zero. -/
theorem ker_shift_mem_fiber {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]} (hc : 2 * c < N)
    {A B : (ZMod (p ^ N))[X]}
    (hdet : ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A B a b).det = (p : ZMod (p ^ N)) ^ c * u)
    (hA : A ∈ cell A₀ a (c + 1)) (hB : B ∈ cell B₀ b (c + 1))
    {x : Fin (a + b) → ZMod (p ^ N)}
    (hx : (Polynomial.sylvester A B a b).mulVec x = 0) :
    A + polyOf (leftPart x) ∈ cell A₀ a (c + 1)
      ∧ B + polyOf (rightPart x) ∈ cell B₀ b (c + 1)
      ∧ (A + polyOf (leftPart x)) * (B + polyOf (rightPart x)) = A * B := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow (by omega : N ≠ 0) hp.out.one_lt⟩
  have hxdvd : ∀ i, (p : ZMod (p ^ N)) ^ (N - c) ∣ x i :=
    dvd_of_mulVec_eq_zero _ (by omega) hdet hx
  have hLdvd : ∀ i, (p : ZMod (p ^ N)) ^ (N - c) ∣ (polyOf (leftPart x)).coeff i := by
    intro i
    rw [coeff_polyOf]
    split_ifs with h
    · exact hxdvd _
    · exact dvd_zero _
  have hRdvd : ∀ i, (p : ZMod (p ^ N)) ^ (N - c) ∣ (polyOf (rightPart x)).coeff i := by
    intro i
    rw [coeff_polyOf]
    split_ifs with h
    · exact hxdvd _
    · exact dvd_zero _
  have hcombo : B * polyOf (leftPart x) + A * polyOf (rightPart x) = 0 :=
    (mulVec_eq_zero_iff_combo A B (le_of_eq hA.2.1) (le_of_eq hB.2.1) x).mp hx
  have hquad : polyOf (leftPart x) * polyOf (rightPart x) = 0 :=
    mul_eq_zero_of_coeff_dvd (by omega) hLdvd hRdvd
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hmon, hdeg⟩ := monic_add_of_coeff hA.1 hA.2.1
      (fun i hi => coeff_polyOf_of_le (leftPart x) hi)
    refine ⟨hmon, hdeg, fun i => ?_⟩
    have hAL : A + polyOf (leftPart x) - A₀ = A - A₀ + polyOf (leftPart x) := by ring
    rw [hAL, Polynomial.coeff_add]
    exact dvd_add (hA.2.2 i)
      (dvd_trans (pow_dvd_pow _ (by omega : c + 1 ≤ N - c)) (hLdvd i))
  · obtain ⟨hmon, hdeg⟩ := monic_add_of_coeff hB.1 hB.2.1
      (fun i hi => coeff_polyOf_of_le (rightPart x) hi)
    refine ⟨hmon, hdeg, fun i => ?_⟩
    have hBR : B + polyOf (rightPart x) - B₀ = B - B₀ + polyOf (rightPart x) := by ring
    rw [hBR, Polynomial.coeff_add]
    exact dvd_add (hB.2.2 i)
      (dvd_trans (pow_dvd_pow _ (by omega : c + 1 ≤ N - c)) (hRdvd i))
  · have hexp : (A + polyOf (leftPart x)) * (B + polyOf (rightPart x))
        = A * B + (B * polyOf (leftPart x) + A * polyOf (rightPart x))
          + polyOf (leftPart x) * polyOf (rightPart x) := by ring
    rw [hexp, hcombo, hquad, add_zero, add_zero]

/-! ### The torsor bijection and the fiber count -/

/-- **The torsor.**  The fiber of `(A, B) ↦ A*B` through a cell point `(A, B)` is in bijection
with the kernel of `(sylvester A B a b).mulVec` — translation by increments, both directions
justified by the two torsor lemmas above. -/
noncomputable def fiberEquivKer {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]} (hc : 2 * c < N)
    {A B : (ZMod (p ^ N))[X]}
    (hA : A ∈ cell A₀ a (c + 1)) (hB : B ∈ cell B₀ b (c + 1))
    (hdet : ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A B a b).det = (p : ZMod (p ^ N)) ^ c * u) :
    {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
        AB.1 ∈ cell A₀ a (c + 1) ∧ AB.2 ∈ cell B₀ b (c + 1) ∧ AB.1 * AB.2 = A * B}
      ≃ {x : Fin (a + b) → ZMod (p ^ N) //
          (Polynomial.sylvester A B a b).mulVec x = 0} where
  toFun AB' := ⟨vecOf (m := a) b (AB'.1.1 - A) (AB'.1.2 - B),
    mulVec_vecOf_eq_zero hc hdet hA hB AB'.2.1 AB'.2.2.1 AB'.2.2.2⟩
  invFun x :=
    ⟨(A + polyOf (leftPart x.1), B + polyOf (rightPart x.1)),
      (ker_shift_mem_fiber hc hdet hA hB x.2).1,
      (ker_shift_mem_fiber hc hdet hA hB x.2).2.1,
      (ker_shift_mem_fiber hc hdet hA hB x.2).2.2⟩
  left_inv := by
    rintro ⟨⟨A', B'⟩, hA', hB', hprod⟩
    apply Subtype.ext
    dsimp only
    have h1 : polyOf (leftPart (vecOf (m := a) b (A' - A) (B' - B))) = A' - A :=
      polyOf_leftPart_vecOf
        (fun i hi => sub_coeff_eq_zero_of_ge hA'.1 hA.1 hA'.2.1 hA.2.1 hi)
    have h2 : polyOf (rightPart (vecOf (m := a) b (A' - A) (B' - B))) = B' - B :=
      polyOf_rightPart_vecOf
        (fun i hi => sub_coeff_eq_zero_of_ge hB'.1 hB.1 hB'.2.1 hB.2.1 hi)
    rw [h1, h2]
    have e1 : A + (A' - A) = A' := by ring
    have e2 : B + (B' - B) = B' := by ring
    rw [e1, e2]
  right_inv := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    dsimp only
    have e1 : A + polyOf (leftPart x) - A = polyOf (leftPart x) := by ring
    have e2 : B + polyOf (rightPart x) - B = polyOf (rightPart x) := by ring
    rw [e1, e2]
    funext i
    induction i using Fin.addCases with
    | left j =>
      rw [vecOf_castAdd]
      exact coeff_polyOf_of_lt (leftPart x) j
    | right j =>
      rw [vecOf_natAdd]
      exact coeff_polyOf_of_lt (rightPart x) j

/-- **F-B2 deliverable 3 (`fiber_card`).**  Every fiber of `(A, B) ↦ A*B` over a point of its
image on `cell A₀ a (c+1) × cell B₀ b (c+1)` has exactly `p^c` elements. -/
theorem fiber_card {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A₀ B₀ a b = (p : ZMod (p ^ N)) ^ c * u)
    (hc : 2 * c < N) {g : (ZMod (p ^ N))[X]}
    (hg : g ∈ (fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
      (cell A₀ a (c + 1) ×ˢ cell B₀ b (c + 1))) :
    Nat.card {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
        AB.1 ∈ cell A₀ a (c + 1) ∧ AB.2 ∈ cell B₀ b (c + 1) ∧ AB.1 * AB.2 = g}
      = p ^ c := by
  obtain ⟨AB₀, hABmem, hgeq⟩ := hg
  obtain ⟨A, B⟩ := AB₀
  have hg' : A * B = g := hgeq
  subst hg'
  rw [Set.mem_prod] at hABmem
  obtain ⟨hA, hB⟩ := hABmem
  have hdet : ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A B a b).det = (p : ZMod (p ^ N)) ^ c * u :=
    det_sylvester_stable hres hA.2.2 hB.2.2
  exact (Nat.card_congr (fiberEquivKer hc hA hB hdet)).trans
    (LinearFiber.card_ker_mulVec_of_det _ (by omega : c < N) hdet)

/-! ## Deliverable 4 — F-B3 assembly -/

/-- Cells are finite (they inject into the coefficient tuples of length `d + 1`). -/
theorem cell_finite (P₀ : (ZMod (p ^ N))[X]) (d k : ℕ) : (cell P₀ d k).Finite := by
  have hinj : Set.InjOn
      (fun P : (ZMod (p ^ N))[X] => fun i : Fin (d + 1) => P.coeff (i : ℕ))
      (cell P₀ d k) := by
    intro P hP Q hQ hPQ
    ext i
    by_cases hi : i < d + 1
    · exact congrFun hPQ ⟨i, hi⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < i by rw [hP.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (show Q.natDegree < i by rw [hQ.2.1]; omega)]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

/-- **F-B2 deliverable 4 (`image_card`, the F-B3 count identity).**
`Nat.card (image) * p^c = Nat.card cellA * Nat.card cellB`, by fiber-summing `fiber_card`. -/
theorem image_card {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A₀ B₀ a b = (p : ZMod (p ^ N)) ^ c * u)
    (hc : 2 * c < N) :
    Nat.card ((fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
        (cell A₀ a (c + 1) ×ˢ cell B₀ b (c + 1))) * p ^ c
      = Nat.card (cell A₀ a (c + 1)) * Nat.card (cell B₀ b (c + 1)) := by
  classical
  set D : Set ((ZMod (p ^ N))[X] × (ZMod (p ^ N))[X]) :=
    cell A₀ a (c + 1) ×ˢ cell B₀ b (c + 1) with hD
  set f : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] → (ZMod (p ^ N))[X] :=
    fun AB => AB.1 * AB.2 with hf
  have hDfin : D.Finite := (cell_finite A₀ a (c + 1)).prod (cell_finite B₀ b (c + 1))
  have hIfin : (f '' D).Finite := hDfin.image f
  haveI : Fintype ↥(f '' D) := hIfin.fintype
  haveI : Finite ↥D := hDfin.to_subtype
  let F : ↥D → ↥(f '' D) := fun x => ⟨f x.1, Set.mem_image_of_mem f x.2⟩
  have hcard : ∀ gg : ↥(f '' D), Nat.card {x : ↥D // F x = gg} = p ^ c := by
    intro gg
    have e : {x : ↥D // F x = gg}
        ≃ {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
            AB.1 ∈ cell A₀ a (c + 1) ∧ AB.2 ∈ cell B₀ b (c + 1) ∧ AB.1 * AB.2 = gg.1} :=
      { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1⟩, Subtype.ext y.2.2.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => rfl }
    rw [Nat.card_congr e]
    exact fiber_card hres hc gg.2
  have h1 : Nat.card ↥D = Nat.card ↥(f '' D) * p ^ c := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma,
      Finset.sum_congr rfl fun gg _ => hcard gg, Finset.sum_const, smul_eq_mul,
      Finset.card_univ, Nat.card_eq_fintype_card]
  have h2 : Nat.card ↥D = Nat.card (cell A₀ a (c + 1)) * Nat.card (cell B₀ b (c + 1)) := by
    rw [hD, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  rw [← h1]
  exact h2

/-! ## Spec-named alias for deliverable 1 -/

omit hp in
/-- **`sylvesterMulVec_eq`** (the blueprint's spelling): under the coefficient identification,
`(sylvester A₀ B₀ a b).mulVec αβ` is `A₀ * (β-part) + B₀ * (α-part)`, where the α-part
(increment of the `A`-side, degree `< a`) occupies the **first `a`** coordinates and the β-part
(degree `< b`) the **last `b`** — see the module docstring for the orientation discussion. -/
theorem sylvesterMulVec_eq {a b : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hA₀ : A₀.natDegree ≤ a) (hB₀ : B₀.natDegree ≤ b)
    (αβ : Fin (a + b) → ZMod (p ^ N)) :
    polyOf ((Polynomial.sylvester A₀ B₀ a b).mulVec αβ)
      = A₀ * polyOf (rightPart αβ) + B₀ * polyOf (leftPart αβ) := by
  rw [polyOf_sylvester_mulVec A₀ B₀ hA₀ hB₀ αβ, add_comm]

end LeanUrat.OM.HenselCount
