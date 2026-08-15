/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapB.B78 — the window dictionary: window-exactness of the Hensel peel

**Chapter B, NODE B.78** (`blueprint/CHAP-B_leaf_layer.md`, the leaf / order-1 layer), all three
clauses (the blueprint's mandated `B78a`/`B78b` split is realised here as the two sections
`## (i)–(ii)` and `## (iii)` of a single node file, so the roll-up wiring stays one file per node).

* **(i) `monicPoly_congr`** — coefficientwise congruence of vectors passes to the monic
  polynomials they cut out: the leading `X ^ n` cancels and the rest *is* the vector difference.
* **(ii) `factor_congr_of_coprime`** — *binary block stability*: if two given monic factorizations
  `f = g·h` and `f' = g'·h'` have the *same* coprime monic residual pair `(g₀, h₀)`, then a
  level-`N` congruence of the products forces the level-`N` congruence of the factors.
* **(iii) `peel_congr`** — the same over a `Finset` of pairwise-coprime residual blocks.

**No completeness is assumed anywhere.** The factorizations are *given*; the content is that the
level-`N` window of the product pins the level-`N` window of each factor. Producing the
factorizations is landed Hensel (`Uniformity.Hensel.exists_monic_factorization_finset`,
`MultiHensel.lean:111`) and needs adic completeness; that happens at B.80, not here.

**Clause (ii) at `N = ∞` is landed.** `Uniformity.Hensel.monic_factorization_unique`
(`HenselFactorization.lean:694`) proves `g = g'` from `g·h = g'·h'` exactly, by cancelling in one
step (divisibility plus a degree bound). The finite-precision form below cannot cancel — division
by `h'` is unavailable mod `π ^ N` — so it runs the height-by-height induction instead.

DEPENDS: landed `Uniformity.Hensel.natDegree_eq_of_map_eq`,
`Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq` (`HenselFactorization.lean:376,381`) ·
landed `Uniformity.Density.monicPoly` (`Density/LocalData.lean:151`) · mathlib
`Polynomial.C_dvd_iff_dvd_coeff`, `Polynomial.degree_le_of_dvd`, `Polynomial.degree_map_le`,
`IsCoprime.dvd_of_dvd_mul_right`, `IsCoprime.prod_right`, `Finset.induction_on`.

**PROOF.**
1. **(i)** `monicPoly a - monicPoly b = ∑ i, C (a i - b i) * X ^ i`; its `j`-th coefficient is
   `(a i - b i) * (X ^ i).coeff j`, divisible by `π ^ N` term by term.
2. **(ii)**, by induction on `k ≤ N` for the claim `C (π ^ k) ∣ (g' - g)` and
   `C (π ^ k) ∣ (h' - h)`. The base `k = 1` is `ḡ = ḡ'`, `h̄ = h̄'` read coefficientwise.
3. Step `k → k+1` with `k ≥ 1`: write `g' - g = C (π ^ k) * A₁`, `h' - h = C (π ^ k) * B₁`, so
   `g'h' - gh = C (π ^ k) * (A₁·h + g·B₁ + C (π ^ k) * (A₁·B₁))`. Since `C (π ^ (k+1))` divides
   the left side (`k + 1 ≤ N`) and `C (π ^ k)` cancels in the domain `O[X]`, we get
   `C π ∣ A₁·h + g·B₁ + C (π ^ k) * (A₁·B₁)`; the tail is divisible by `C π` because `k ≥ 1`, so
   `C π ∣ A₁·h + g·B₁`.
4. Reducing mod `π`: `Ā₁·h₀ + g₀·B̄₁ = 0`, hence `g₀ ∣ Ā₁·h₀` and, by coprimality, `g₀ ∣ Ā₁`;
   but `deg Ā₁ ≤ deg A₁ = deg (g' - g) < deg g₀` (monic, equal degrees), so `Ā₁ = 0`, i.e.
   `C (π ^ (k+1)) ∣ (g' - g)`. Symmetrically `B̄₁ = 0`.
5. **(iii)**, by `Finset.induction_on`: split `∏_{insert i s} = g i * ∏_s`, note the complement
   product is monic with reduction `∏_{j ∈ s} g₀ j`, coprime to `g₀ i` by `IsCoprime.prod_right`;
   clause (ii) peels `i` and hands the complement congruence to the inductive hypothesis.

SOURCE: `EFF.W12.21` (`LEMMA W12-S2.1`, "the level-0 product structure (window-exact Hensel)"),
statement and quoted proof — clauses (ii)/(iii) are its injectivity leg, stated over `O` rather
than `O/π^N`. The surjectivity leg is landed `exists_monic_factorization_finset` and is consumed
at B.67, not re-proved here.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- Clause (i) does not use `[IsDiscreteValuationRing O]`, but the signature is frozen against the
-- gate-verified stub (`leanspec/Leanspec/ChapB.lean`, **B.78a**), which is elaborated in exactly
-- the ENV-A′ `variable` block reproduced below; trimming the binders would break the type diff.
set_option linter.unusedSectionVars false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section EnvA

-- ENV-A′: the polynomial arena over a DVR, with `π` an explicit uniformizer hypothesis on the
-- statements that need it.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## (i) The `monicPoly` congruence -/

/-- **B.78 (i) — `monicPoly` congruence.** Coefficient vectors congruent mod `π ^ N` cut out
monic polynomials congruent mod `π ^ N`: the leading `X ^ n` cancels and the remaining
coefficients *are* the vector entries. -/
theorem monicPoly_congr {n N : ℕ} {a b : Fin n → O}
    (hab : ∀ i, π ^ N ∣ (a i - b i)) (j : ℕ) :
    π ^ N ∣ (Uniformity.Density.monicPoly a - Uniformity.Density.monicPoly b).coeff j := by
  classical
  have hsub : Uniformity.Density.monicPoly a - Uniformity.Density.monicPoly b
      = ∑ i : Fin n, C (a i - b i) * X ^ (i : ℕ) := by
    simp only [Uniformity.Density.monicPoly, map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsub, finsetSum_coeff]
  refine Finset.dvd_sum fun i _ => ?_
  rw [coeff_C_mul]
  exact (hab i).mul_right _

/-! ## The `π`-divisibility dictionary on coefficients -/

/-- `C π ∣ p` is exactly the vanishing of the residue reduction of `p`. -/
private theorem C_dvd_iff_map_residue_eq_zero (hπ : Irreducible π) (p : Polynomial O) :
    C π ∣ p ↔ p.map (residue O) = 0 := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  refine forall_congr' fun i => ?_
  rw [coeff_map, coeff_zero]
  constructor
  · intro hd
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  · intro hz
    have hmem := Ideal.Quotient.eq_zero_iff_mem.1 hz
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem

/-! ## (ii) Binary block stability -/

/-- **B.78 (ii) — binary block stability.** Two given monic factorizations with the *same* coprime
monic residual pair are congruent factorwise as soon as their products are congruent: from
`π ^ N ∣ (g·h − g'·h').coeff i` for every `i` one gets `π ^ N ∣ (g − g').coeff i` and
`π ^ N ∣ (h − h').coeff i` for every `i`. No completeness is used. -/
theorem factor_congr_of_coprime (hπ : Irreducible π) {N : ℕ} {g h g' h' : Polynomial O}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    {g₀ h₀ : Polynomial (ResidueField O)} (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (IsLocalRing.residue O) = g₀) (hhr : h.map (IsLocalRing.residue O) = h₀)
    (hgr' : g'.map (IsLocalRing.residue O) = g₀) (hhr' : h'.map (IsLocalRing.residue O) = h₀)
    (hff' : ∀ i, π ^ N ∣ (g * h - g' * h').coeff i) :
    (∀ i, π ^ N ∣ (g - g').coeff i) ∧ (∀ i, π ^ N ∣ (h - h').coeff i) := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  -- the residual data: monic, of the common degree of the two lifts
  have hg₀mon : g₀.Monic := by rw [← hgr]; exact hg.map _
  have hh₀mon : h₀.Monic := by rw [← hhr]; exact hh.map _
  have hg₀0 : g₀ ≠ 0 := hg₀mon.ne_zero
  have hh₀0 : h₀ ≠ 0 := hh₀mon.ne_zero
  have hgdeg : g.natDegree = g₀.natDegree := Uniformity.Hensel.natDegree_eq_of_map_eq hg hgr
  have hg'deg : g'.natDegree = g₀.natDegree := Uniformity.Hensel.natDegree_eq_of_map_eq hg' hgr'
  have hhdeg : h.natDegree = h₀.natDegree := Uniformity.Hensel.natDegree_eq_of_map_eq hh hhr
  have hh'deg : h'.natDegree = h₀.natDegree := Uniformity.Hensel.natDegree_eq_of_map_eq hh' hhr'
  have hdegA : (g' - g).degree < (g₀.natDegree : WithBot ℕ) := by
    have hd := Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq hg' hg
      (by rw [hg'deg, hgdeg])
    rwa [hg'deg] at hd
  have hdegB : (h' - h).degree < (h₀.natDegree : WithBot ℕ) := by
    have hd := Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq hh' hh
      (by rw [hh'deg, hhdeg])
    rwa [hh'deg] at hd
  -- the level-`N` hypothesis, packaged as a `C`-divisibility
  have hCN : C (π ^ N) ∣ (g' * h' - g * h) := by
    have h1 : C (π ^ N) ∣ (g * h - g' * h') := (C_dvd_iff_dvd_coeff _ _).2 hff'
    rw [← neg_sub (g * h) (g' * h')]
    exact dvd_neg.2 h1
  -- the height-by-height induction
  have key : ∀ k, k ≤ N → C (π ^ k) ∣ (g' - g) ∧ C (π ^ k) ∣ (h' - h) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · -- base: `ḡ = ḡ'` and `h̄ = h̄'` are the hypotheses
        refine ⟨?_, ?_⟩
        · rw [pow_one, C_dvd_iff_map_residue_eq_zero hπ, Polynomial.map_sub, hgr', hgr, sub_self]
        · rw [pow_one, C_dvd_iff_map_residue_eq_zero hπ, Polynomial.map_sub, hhr', hhr, sub_self]
      · obtain ⟨hAk, hBk⟩ := ih (Nat.le_of_succ_le hk)
        obtain ⟨A₁, hA₁⟩ := hAk
        obtain ⟨B₁, hB₁⟩ := hBk
        have eg' : g' = g + C (π ^ k) * A₁ := by rw [← hA₁]; ring
        have eh' : h' = h + C (π ^ k) * B₁ := by rw [← hB₁]; ring
        have hexp : g' * h' - g * h
            = C (π ^ k) * (A₁ * h + g * B₁ + C (π ^ k) * (A₁ * B₁)) := by
          rw [eg', eh']; ring
        have hdvd1 : C (π ^ (k + 1)) ∣ (g' * h' - g * h) :=
          dvd_trans (map_dvd C (pow_dvd_pow π hk)) hCN
        have hCk0 : (C (π ^ k) : Polynomial O) ≠ 0 := C_ne_zero.2 (pow_ne_zero k hπ0)
        have hcancel : C (π ^ k) * C π
            ∣ C (π ^ k) * (A₁ * h + g * B₁ + C (π ^ k) * (A₁ * B₁)) := by
          rw [← hexp, ← C_mul, ← pow_succ]
          exact hdvd1
        have hstep : C π ∣ A₁ * h + g * B₁ + C (π ^ k) * (A₁ * B₁) :=
          (mul_dvd_mul_iff_left hCk0).1 hcancel
        have htail : C π ∣ C (π ^ k) * (A₁ * B₁) :=
          (map_dvd C (dvd_pow_self π hkpos.ne')).mul_right _
        have hmain : C π ∣ A₁ * h + g * B₁ := by
          have hd := dvd_sub hstep htail
          simpa using hd
        -- reduce mod `π` : `Ā₁·h₀ + g₀·B̄₁ = 0`
        have hres : (A₁.map (residue O)) * h₀ + g₀ * (B₁.map (residue O)) = 0 := by
          have hz := (C_dvd_iff_map_residue_eq_zero hπ _).1 hmain
          rwa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hhr, hgr] at hz
        -- degree bounds on the quotients
        have hdegA₁ : A₁.degree = (g' - g).degree := by
          rw [hA₁, degree_mul, degree_C (pow_ne_zero k hπ0), zero_add]
        have hdegB₁ : B₁.degree = (h' - h).degree := by
          rw [hB₁, degree_mul, degree_C (pow_ne_zero k hπ0), zero_add]
        have hA0 : A₁.map (residue O) = 0 := by
          by_contra hne
          have h1 : g₀.degree ≤ (A₁.map (residue O)).degree :=
            degree_le_of_dvd (hcop.dvd_of_dvd_mul_right ⟨-(B₁.map (residue O)),
              by linear_combination hres⟩) hne
          rw [degree_eq_natDegree hg₀0] at h1
          exact absurd (h1.trans ((degree_map_le).trans hdegA₁.le)) (not_le.2 hdegA)
        have hB0 : B₁.map (residue O) = 0 := by
          by_contra hne
          have h1 : h₀.degree ≤ (B₁.map (residue O)).degree :=
            degree_le_of_dvd (hcop.symm.dvd_of_dvd_mul_left ⟨-(A₁.map (residue O)),
              by linear_combination hres⟩) hne
          rw [degree_eq_natDegree hh₀0] at h1
          exact absurd (h1.trans ((degree_map_le).trans hdegB₁.le)) (not_le.2 hdegB)
        refine ⟨?_, ?_⟩
        · rw [hA₁, pow_succ, C_mul]
          exact mul_dvd_mul_left _ ((C_dvd_iff_map_residue_eq_zero hπ A₁).2 hA0)
        · rw [hB₁, pow_succ, C_mul]
          exact mul_dvd_mul_left _ ((C_dvd_iff_map_residue_eq_zero hπ B₁).2 hB0)
  obtain ⟨hfA, hfB⟩ := key N le_rfl
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hd : C (π ^ N) ∣ (g - g') := by rw [← neg_sub g' g]; exact dvd_neg.2 hfA
    exact (C_dvd_iff_dvd_coeff _ _).1 hd i
  · have hd : C (π ^ N) ∣ (h - h') := by rw [← neg_sub h' h]; exact dvd_neg.2 hfB
    exact (C_dvd_iff_dvd_coeff _ _).1 hd i

/-! ## (iii) Finset block stability -/

/-- **B.78 (iii) — `Finset` block stability.** For two given monic factorizations of the *same*
pairwise-coprime monic residual family over a `Finset`, a level-`N` congruence of the products
forces the level-`N` congruence of every block. Proved by peeling one index at a time with clause
(ii); the complement product is coprime to the peeled residual block by `IsCoprime.prod_right`. -/
theorem peel_congr (hπ : Irreducible π) {N : ℕ} {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {g g' : ι → Polynomial O} {g₀ : ι → Polynomial (ResidueField O)}
    (hgmon : ∀ i ∈ s, (g i).Monic) (hgmon' : ∀ i ∈ s, (g' i).Monic)
    (h₀mon : ∀ i ∈ s, (g₀ i).Monic)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g₀ i) (g₀ j))
    (hgr : ∀ i ∈ s, (g i).map (IsLocalRing.residue O) = g₀ i)
    (hgr' : ∀ i ∈ s, (g' i).map (IsLocalRing.residue O) = g₀ i)
    (hff' : ∀ k, π ^ N ∣ ((∏ i ∈ s, g i) - (∏ i ∈ s, g' i)).coeff k) :
    ∀ i ∈ s, ∀ k, π ^ N ∣ ((g i) - (g' i)).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro i hi; exact absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
    -- peel the block at `a`
    have hmemA : a ∈ insert a s := Finset.mem_insert_self a s
    have hsub : ∀ j ∈ s, j ∈ insert a s := fun j hj => Finset.mem_insert_of_mem hj
    have hPg : (∏ i ∈ s, g i).Monic :=
      monic_prod_of_monic _ _ fun j hj => hgmon j (hsub j hj)
    have hPg' : (∏ i ∈ s, g' i).Monic :=
      monic_prod_of_monic _ _ fun j hj => hgmon' j (hsub j hj)
    have hP₀ : (∏ i ∈ s, g₀ i).Monic :=
      monic_prod_of_monic _ _ fun j hj => h₀mon j (hsub j hj)
    have hcopA : IsCoprime (g₀ a) (∏ i ∈ s, g₀ i) :=
      IsCoprime.prod_right fun j hj =>
        hcop a hmemA j (hsub j hj) (by rintro rfl; exact ha hj)
    have hPgr : (∏ i ∈ s, g i).map (residue O) = ∏ i ∈ s, g₀ i := by
      rw [Polynomial.map_prod]
      exact Finset.prod_congr rfl fun j hj => hgr j (hsub j hj)
    have hPgr' : (∏ i ∈ s, g' i).map (residue O) = ∏ i ∈ s, g₀ i := by
      rw [Polynomial.map_prod]
      exact Finset.prod_congr rfl fun j hj => hgr' j (hsub j hj)
    have hsplit : ∀ k, π ^ N ∣ (g a * (∏ i ∈ s, g i) - g' a * (∏ i ∈ s, g' i)).coeff k := by
      intro k
      have hk := hff' k
      rwa [Finset.prod_insert ha, Finset.prod_insert ha] at hk
    obtain ⟨hA, hB⟩ := factor_congr_of_coprime hπ (hgmon a hmemA) hPg (hgmon' a hmemA) hPg'
      hcopA (hgr a hmemA) hPgr (hgr' a hmemA) hPgr' hsplit
    have hrec := ih (fun j hj => hgmon j (hsub j hj)) (fun j hj => hgmon' j (hsub j hj))
      (fun j hj => h₀mon j (hsub j hj))
      (fun j hj k hk hjk => hcop j (hsub j hj) k (hsub k hk) hjk)
      (fun j hj => hgr j (hsub j hj)) (fun j hj => hgr' j (hsub j hj)) hB
    intro i hi k
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · exact hA k
    · exact hrec i hi' k

end EnvA

section AxCheck
#print axioms Uniformity.Density.Leaf.monicPoly_congr
#print axioms Uniformity.Density.Leaf.factor_congr_of_coprime
#print axioms Uniformity.Density.Leaf.peel_congr
end AxCheck

end Uniformity.Density.Leaf
