/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapE.E10

/-!
# Uniformity.ChapE.E55a — the π-adic limit of an α-refine chain (LEMMA HE7-8, steps 1–3)

**Chapter E, NODE E.55a** [theorem] [fresh] — the first (and here also the second) member of the
SPLIT-MANDATED ×3 decomposition of the chapter's hardest node, E.55
(`blueprint/CHAP-E_sigma_ladder.md` §8: *"`E55a` (step 1, the coefficientwise completeness limit —
reusable), `E55b` (step 3, the limit-passing in a polynomial identity), `E55` (the assembly +
step 4)"*). ENV-E2 + `[IsAdicComplete (IsLocalRing.maximalIdeal O) O]` (the completeness
hypothesis is declared per GC-6.4 — only at this node and its splits).

**What lands here:** steps 1 AND 3 of the corpus proof, as ONE theorem `exists_limit_key`, because
the limit-passing (E55b) is three lines once the coefficients are known to be Cauchy and cannot be
stated without the limit that step 1 produces. Step 4 (the squarefree contradiction) and the
assembly are `E55.lean`, together with the **machine-checked refutation of the committed E.55
signature** — read `E55.lean`'s header before consuming anything here as "LEMMA HE7-8".

## The statement, in words

`F` is developed, at every stage `j` of a refine chain, along the recentred key
`Ψ − W_j` where `W_j = ∑_{i<j} w i` is the partial sum of the increments:

```
F = (Ψ − W_j)^μ₂ + ∑_{m<μ₂} A_{j,m} · (Ψ − W_j)^m .
```

The increments have slot heights `hgt (w j) = λ_j` STRICTLY INCREASING, and the development
coefficients clear the single-side floor `hgt (A_{j,m}) ≥ (μ₂ − m)·λ_j`. Both the increments and
the development coefficients are sub-key-degree (`natDegree < C.D`), so the carrier's coefficient
link `hcoeff` converts heights into `ϖ`-divisibilities of the `O`-coefficients. Conclusion: the
partial sums converge coefficientwise in the `maximalIdeal`-adic topology, and the development
passes to the limit —

```
∃ W, W.natDegree < C.D ∧ F = (Ψ − W)^μ₂ .
```

This is `EFF.HE7.53`'s own argument: *"dv₂(A) → ∞ forces the Φ′-development coefficients of A,
hence its O-coefficients, to converge π-adically to 0 … The partial sums W_j therefore converge in
the (complete) O-module of polynomials of degree < D″ … Passing to the limit … gives
f_S = (Ψ − W)^{μ₂} in O[x]"* — with no "binomial kill" (the corpus's own NON-IMPORT: the node
condition plus `λ^{(j)} → ∞` is all that is used, and that is all this proof uses).

## ⚠ THE HYPOTHESIS THE COMMITTED STUB WAS MISSING — `hAdeg`

`hAdeg : ∀ j m, (A j m).natDegree < C.D` is **not** in the committed signature
(`leanspec/Leanspec/ChapE.lean:1117-1136`, blueprint §8 NODE E.55). It is indispensable, and not
for convenience: `hcoeff` is a statement about polynomials of degree `< C.D` ONLY, so without
`hAdeg` the floor `hgt (A j m) ≥ (μ₂ − m)λ_j` constrains a single carrier value and says nothing
about the `O`-coefficients of `A j m`. `E55.lean` carries the counterexample that exploits exactly
this (a `D = 1` carrier reads the constant coefficient only; the development coefficients hide an
unbounded `x`-part). The corpus is on the right side of this: its `A`'s ARE the `Φ′`-development
coefficients, which have degree `< D″` by construction — the stub dropped the datum, the source
did not.

## Faithfulness

**⚠ Mandatory, trust-boundary definitions** (parent CLAUDE.md): this file declares ONE new
predicate, `CoeffsIn J P` = "every coefficient of `P` lies in the ideal `J`" — pure bookkeeping
(the five closure lemmas below are its whole content), used to move divisibilities through sums,
differences and products of polynomials. It has no corpus counterpart and asserts nothing about
the ladder.

Three recasts to check on the chapter cross-read:

* *the completeness is used coefficientwise, not on the polynomial module.* `IsPrecomplete` is
  applied to `O` itself, once per coefficient index; the polynomial `W` is then assembled from the
  `C.D` limits. This is the corpus's "the complete `O`-module of polynomials of degree `< D″`",
  realised as `O^{C.D}` rather than as an instance about `Polynomial O` (which is NOT adically
  complete — it is a direct sum, not a product; assembling by hand is what keeps the statement
  true).
* *`λ_j → ∞` is used only through `StrictMono lam`*, via `lam 0 + j ≤ lam j`; no rate is assumed,
  and the index shift `jj n = n + |lam 0|` absorbs a negative `lam 0` (the slopes may start
  negative — the ladder's heights are `ℤ`-valued).
* *the floors are used only at `m < μ₂`*, where `μ₂ − m ≥ 1` makes `(μ₂ − m)·λ_j ≥ λ_j`; the
  hypothesis `2 ≤ μ₂` is NOT needed for the limit (it is step 4's, in `E55.lean`), so it is not a
  binder here — this lemma is correspondingly stronger.

**DEPENDS.** E.10 (`SlotCarrier`: `hgt`, `D`, `hD`) · mathlib `IsAdicComplete`
(`IsPrecomplete.prec'`, `IsHausdorff.haus'`), `IsDiscreteValuationRing.addVal` and
`addVal_le_iff_dvd`, `Polynomial.coeff` API. **Not** used: E.38 (`slot_fold`). The blueprint's
DEPENDS lists it "for the partial sums' heights", but the proof never needs the partial sums'
HEIGHTS — only their coefficients' valuations, which come from the increments one at a time
through `hcoeff`. Recorded as a DAG simplification, not a gap.

**SOURCE.** `EFF.HE7.53` (LEMMA HE7-8, statement and proof; the convergence argument quoted
above); `EFF.T2.26`/`EFF.T2.52` (`HE7-REF-TERM` as the pinned `(SEC-RANK)` supplier "in its
well-foundedness form"). The `[HE6-A3-UNADJUDICATED FOR HE7]` flag of honesty item E-1 applies to
the SOURCE unit, not to this file's content: nothing here is stated from HE6 frozen text.

**TEETH.** Q1's 42 one-step refines, PE2's first 2-step chains, `he7annex_supp.py` P4 (the WRONG
continuation cycles, 48/48) — machine evidence for the theorem, retained at §13; the Lean leg is
this file.

## Status

Sorry-free, axiom-free (Lean core only: `propext`, `Classical.choice`, `Quot.sound`).
-/

open Polynomial IsDiscreteValuationRing

namespace Uniformity.Density.Ladder

section CoeffsIn

variable {O : Type*} [CommRing O]

/-- Every coefficient of `P` lies in the ideal `J`. Bookkeeping only (see the header's
trust-boundary note): the ladder's content enters through `hcoeff`, never through this. -/
def CoeffsIn (J : Ideal O) (P : Polynomial O) : Prop := ∀ i, P.coeff i ∈ J

lemma CoeffsIn.add {J : Ideal O} {P Q : Polynomial O} (hP : CoeffsIn J P) (hQ : CoeffsIn J Q) :
    CoeffsIn J (P + Q) := fun i => by
  rw [coeff_add]; exact Ideal.add_mem _ (hP i) (hQ i)

lemma CoeffsIn.sub {J : Ideal O} {P Q : Polynomial O} (hP : CoeffsIn J P) (hQ : CoeffsIn J Q) :
    CoeffsIn J (P - Q) := fun i => by
  rw [coeff_sub]; exact Ideal.sub_mem _ (hP i) (hQ i)

lemma CoeffsIn.mul_right {J : Ideal O} {P : Polynomial O} (hP : CoeffsIn J P) (Q : Polynomial O) :
    CoeffsIn J (P * Q) := fun i => by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (hP x.1)

lemma CoeffsIn.sum {J : Ideal O} {s : Finset ℕ} {P : ℕ → Polynomial O}
    (hP : ∀ m ∈ s, CoeffsIn J (P m)) : CoeffsIn J (∑ m ∈ s, P m) := fun i => by
  rw [finsetSum_coeff]
  exact Ideal.sum_mem _ fun m hm => hP m hm i

lemma CoeffsIn.of_dvd {J : Ideal O} {P Q : Polynomial O} (hP : CoeffsIn J P) (h : P ∣ Q) :
    CoeffsIn J Q := by
  obtain ⟨R, rfl⟩ := h
  exact hP.mul_right R

end CoeffsIn

/-- The carrier's coefficient link is stated in `WithTop ℤ` through `WithTop.map`; this reads it
back as an inequality of `ℕ∞`-valuations. -/
lemma nat_le_of_map_le {n : ℕ} {x : ℕ∞}
    (h : ((n : ℤ) : WithTop ℤ) ≤ x.map (fun m : ℕ => (m : ℤ))) : (n : ℕ∞) ≤ x := by
  cases x with
  | top => exact le_top
  | coe m =>
      have : (n : ℤ) ≤ (m : ℤ) := by simpa using h
      exact_mod_cast this

/-- **NODE E.55a** — *the α-refine chain converges, and the development passes to the limit*
(LEMMA HE7-8, steps 1–3; `EFF.HE7.53`).

Given the carrier coefficient link `hcoeff`, increments `w j` of sub-key degree with strictly
increasing heights `lam j`, and stage-`j` developments of `F` along `Ψ − ∑_{i<j} w i` whose
coefficients `A j m` are of sub-key degree and clear the single-side floors
`(μ₂ − m)·lam j ≤ hgt (A j m)`, the partial sums converge to a `W` of sub-key degree with
`F = (Ψ − W)^μ₂`.

⚠ `hAdeg` (sub-key degree of the development coefficients) is the hypothesis the committed E.55
signature omitted; without it the statement is FALSE (`E55.lean`, `refine_chain_finite_false`).
`2 ≤ μ₂` is NOT needed here. -/
theorem exists_limit_key {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {K : Type*} [Field K] (C : SlotCarrier O K)
    (hcoeff : ∀ (A : Polynomial O) (v : ℤ), A.natDegree < C.D →
      (v : WithTop ℤ) ≤ C.hgt A → ∀ i,
        (v : WithTop ℤ) ≤ (addVal O (A.coeff i)).map (fun n : ℕ => (n : ℤ)))
    {F Ψ : Polynomial O} {μ₂ : ℕ}
    (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hdeg : ∀ j, (w j).natDegree < C.D)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hmono : StrictMono lam)
    (A : ℕ → ℕ → Polynomial O)
    (hAdeg : ∀ j m, (A j m).natDegree < C.D)
    (hdev : ∀ j, F = (Ψ - ∑ i ∈ Finset.range j, w i) ^ μ₂
      + ∑ m ∈ Finset.range μ₂, A j m * (Ψ - ∑ i ∈ Finset.range j, w i) ^ m)
    (hfloor : ∀ j, ∀ m < μ₂, ((((μ₂ - m : ℕ) : ℤ) * lam j : ℤ) : WithTop ℤ) ≤ C.hgt (A j m)) :
    ∃ W : Polynomial O, W.natDegree < C.D ∧ F = (Ψ - W) ^ μ₂ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set I : Ideal O := IsLocalRing.maximalIdeal O with hIdef
  have hϖI : ϖ ∈ I := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  -- STEP 0. heights control coefficients, read as ideal membership
  have key : ∀ (P : Polynomial O) (n : ℕ), P.natDegree < C.D →
      ((n : ℤ) : WithTop ℤ) ≤ C.hgt P → CoeffsIn (I ^ n) P := by
    intro P n hPdeg hPh i
    have h := hcoeff P (n : ℤ) hPdeg hPh i
    have hdvd : ϖ ^ n ∣ P.coeff i := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow]
      exact nat_le_of_map_le h
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖI n)
  -- the partial sums, and their degrees
  set Wsum : ℕ → Polynomial O := fun j => ∑ i ∈ Finset.range j, w i with hWsumdef
  have hWsucc : ∀ j, Wsum (j + 1) = Wsum j + w j := by
    intro j; simp [hWsumdef, Finset.sum_range_succ]
  have hWdeg : ∀ j, (Wsum j).natDegree < C.D := by
    intro j
    induction j with
    | zero => simpa [hWsumdef] using C.hD
    | succ j ih =>
        rw [hWsucc]
        exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ih (hdeg j))
  have hwcoeff : ∀ (t n : ℕ), (n : ℤ) ≤ lam t → CoeffsIn (I ^ n) (w t) := by
    intro t n hn
    refine key (w t) n (hdeg t) ?_
    rw [hh t]
    exact_mod_cast hn
  -- STEP 1. the slopes grow at least linearly, so every modulus is eventually cleared
  have hlamge : ∀ j : ℕ, lam 0 + j ≤ lam j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hstep : lam j < lam (j + 1) := hmono (by omega)
        push_cast at ih ⊢
        omega
  set jj : ℕ → ℕ := fun n => n + (lam 0).natAbs with hjjdef
  have hjjmono : Monotone jj := fun a b hab => by simp only [hjjdef]; omega
  have hjj : ∀ n : ℕ, (n : ℤ) ≤ lam (jj n) := by
    intro n
    have h := hlamge (jj n)
    have habs : (0 : ℤ) ≤ lam 0 + ((lam 0).natAbs : ℤ) := by omega
    have hcast : ((jj n : ℕ) : ℤ) = (n : ℤ) + ((lam 0).natAbs : ℤ) := by
      simp only [hjjdef, Nat.cast_add]
    rw [hcast] at h
    linarith
  -- the coefficient sequences are Cauchy along the reindexed chain
  have hdiff : ∀ (m n : ℕ), m ≤ n → CoeffsIn (I ^ m) (Wsum (jj n) - Wsum (jj m)) := by
    intro m n hmn
    have hle : jj m ≤ jj n := hjjmono hmn
    have hsub : Wsum (jj n) - Wsum (jj m) = ∑ t ∈ Finset.Ico (jj m) (jj n), w t := by
      simp only [hWsumdef]
      rw [Finset.sum_Ico_eq_sub _ hle]
    rw [hsub]
    refine CoeffsIn.sum ?_
    intro t ht
    refine hwcoeff t m ?_
    have h1 : (m : ℤ) ≤ lam (jj m) := hjj m
    have h2 : lam (jj m) ≤ lam t := hmono.monotone (Finset.mem_Ico.mp ht).1
    linarith
  have hlim : ∀ i : ℕ, ∃ L : O, ∀ n : ℕ,
      (Wsum (jj n)).coeff i ≡ L [SMOD (I ^ n • ⊤ : Ideal O)] := by
    intro i
    refine IsPrecomplete.prec' (fun n => (Wsum (jj n)).coeff i) ?_
    intro m n hmn
    rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    have h := hdiff m n hmn i
    rw [coeff_sub] at h
    exact (Ideal.neg_mem_iff _).mp (by simpa [neg_sub] using h)
  choose L hL using hlim
  -- STEP 2. assemble the limit key, of sub-key degree
  set W : Polynomial O := ∑ i ∈ Finset.range C.D, Polynomial.C (L i) * Polynomial.X ^ i with hWdef
  have hWcoeff : ∀ t, W.coeff t = if t < C.D then L t else 0 := by
    intro t
    simp only [hWdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range C.D) t L]
    simp [Finset.mem_range]
  have hWdegree : W.natDegree < C.D := by
    have hle : W.natDegree ≤ C.D - 1 := by
      refine natDegree_le_iff_coeff_eq_zero.mpr ?_
      intro m hm
      rw [hWcoeff]
      have hnot : ¬ m < C.D := by have := C.hD; omega
      simp [hnot]
    have := C.hD
    omega
  have hWapprox : ∀ n : ℕ, CoeffsIn (I ^ n) (W - Wsum (jj n)) := by
    intro n t
    rw [coeff_sub, hWcoeff]
    by_cases ht : t < C.D
    · rw [if_pos ht]
      have h := hL t n
      rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at h
      exact (Ideal.neg_mem_iff _).mp (by simpa [neg_sub] using h)
    · rw [if_neg ht]
      have h0 : (Wsum (jj n)).coeff t = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hWdeg _) (not_lt.mp ht))
      rw [h0, sub_zero]
      exact Ideal.zero_mem _
  refine ⟨W, hWdegree, ?_⟩
  -- STEP 3. pass to the limit in the development, coefficient by coefficient
  have hest : ∀ n : ℕ, CoeffsIn (I ^ n) (F - (Ψ - W) ^ μ₂) := by
    intro n
    have h1 : CoeffsIn (I ^ n) (F - (Ψ - Wsum (jj n)) ^ μ₂) := by
      rw [hdev (jj n)]
      have heq : ((Ψ - Wsum (jj n)) ^ μ₂
            + ∑ m ∈ Finset.range μ₂, A (jj n) m * (Ψ - Wsum (jj n)) ^ m)
          - (Ψ - Wsum (jj n)) ^ μ₂
          = ∑ m ∈ Finset.range μ₂, A (jj n) m * (Ψ - Wsum (jj n)) ^ m := by ring
      rw [heq]
      refine CoeffsIn.sum ?_
      intro m hm
      refine CoeffsIn.mul_right ?_ _
      refine key (A (jj n) m) n (hAdeg _ _) ?_
      refine le_trans ?_ (hfloor (jj n) m (Finset.mem_range.mp hm))
      have hlamn : (n : ℤ) ≤ lam (jj n) := hjj n
      have hge1 : (1 : ℤ) ≤ ((μ₂ - m : ℕ) : ℤ) := by
        have hm' : 1 ≤ μ₂ - m := by have := Finset.mem_range.mp hm; omega
        exact_mod_cast hm'
      have hnn : (0 : ℤ) ≤ lam (jj n) := le_trans (Int.natCast_nonneg n) hlamn
      have hmul : lam (jj n) ≤ ((μ₂ - m : ℕ) : ℤ) * lam (jj n) :=
        le_mul_of_one_le_left hnn hge1
      have : (n : ℤ) ≤ ((μ₂ - m : ℕ) : ℤ) * lam (jj n) := by linarith
      exact_mod_cast this
    have h2 : CoeffsIn (I ^ n) ((Ψ - Wsum (jj n)) ^ μ₂ - (Ψ - W) ^ μ₂) := by
      refine CoeffsIn.of_dvd ?_ (sub_dvd_pow_sub_pow (Ψ - Wsum (jj n)) (Ψ - W) μ₂)
      have hrw : (Ψ - Wsum (jj n)) - (Ψ - W) = W - Wsum (jj n) := by ring
      rw [hrw]
      exact hWapprox n
    have hsplit : F - (Ψ - W) ^ μ₂
        = (F - (Ψ - Wsum (jj n)) ^ μ₂) + ((Ψ - Wsum (jj n)) ^ μ₂ - (Ψ - W) ^ μ₂) := by ring
    rw [hsplit]
    exact h1.add h2
  ext t
  have hz : F.coeff t - ((Ψ - W) ^ μ₂).coeff t = 0 := by
    refine IsHausdorff.haus' (I := I) _ ?_
    intro n
    rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    have h := hest n t
    rwa [coeff_sub] at h
  exact sub_eq_zero.mp hz

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.exists_limit_key

end AxCheck
