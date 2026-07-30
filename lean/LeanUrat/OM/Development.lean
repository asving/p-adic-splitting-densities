import Mathlib
import LeanUrat.OM.QuotientBox

/-!
# F-A — the φ-adic development bijection (Restart Lemma, Lemma A, level `N`)

Rung F-A of `RESTART_FORMALIZATION_BLUEPRINT.md`, the count-native form of
`RESTART_LEMMA.md` §1 (Lemma A).  NO measure theory: at level `N` the φ-adic development is a
BIJECTION of finite coefficient boxes.

Over a general commutative ring `R` (the general form is free, as the blueprint predicts):

* `develop φ k g` — the first `k` φ-adic digits of `g`, by iterated `%ₘ` / `/ₘ`
  (structural recursion on `k`; the closed form `develop φ k g j = g /ₘ φ ^ j %ₘ φ` suggested by
  the blueprint is proved as `develop_eq_divByMonic_pow_modByMonic`).
* `develop_digit_degree` / `develop_digit_natDegree` — each digit has `degree < φ.degree`.
* `develop_reassemble` — for `g.natDegree < k * φ.natDegree` the digits reassemble to `g`:
  `∑ j : Fin k, develop φ k g j * φ ^ j = g` (proved from the degree-form
  `develop_reassemble_degree`, whose induction is clean at `k = 0`).
* `develop_unique` — any degree-bounded digit tuple summing to `g` *is* `develop φ k g`
  (via `Polynomial.div_modByMonic_unique`).

Then, over the level-`N` residue ring `ZMod (p ^ N)` of `LeanUrat.OM.QuotientBox`:

* `developEquiv` — **the deliverable**: for monic `φ` of degree `m`, the monic box of degree
  `k * m` is in bijection with `k`-tuples of digits of degree `< m`:
  `QuotientBox.monicBox p N (k * m) ≃ (Fin k → Polynomial.degreeLT (ZMod (p ^ N)) m)`.
  The top digit is handled by subtracting `φ ^ k` (a monic `g` of degree `k·m` has `k`-th digit
  `1`); the inverse is `b ↦ φ ^ k + ∑ j, b j * φ ^ j`.
* `card_digitTuples` and `developEquiv_card_consistency` — the counting corollary and the
  dimensional cross-check against `QuotientBox.card_monicBox`.

NOTE (blueprint erratum): `developEquiv` needs the hypothesis `0 < N`, which the blueprint
signature omits.  At `N = 0` the residue ring `ZMod 1` is trivial, so for `k * m > 0` the monic
box is *empty* (the only polynomial `0` has `natDegree 0`) while the digit side is a singleton;
the bijection is false there.  This matches `QuotientBox.card_monicBox`, which also takes
`0 < N`.  The hypothesis `0 < m` from the blueprint is kept in the signature for fidelity,
although the proof does not use it.

Namespace: `LeanUrat.OM.Development` (sibling of `LeanUrat.OM.QuotientBox`, per the blueprint's
"new leaf module `LeanUrat/OM/Development.lean`").
-/

namespace LeanUrat.OM.Development

open Polynomial

/-! ## The φ-adic digits over a general commutative ring -/

section Digits

variable {R : Type*} [CommRing R]

/-- The first `k` φ-adic digits of `g`: `develop φ k g = (b_0, …, b_{k-1})` where
`g = b_0 + b_1 φ + ⋯ + b_{k-1} φ^{k-1} + φ^k · (remainder)`-style division data, obtained by
iterating Euclidean division by the monic `φ` (`b_0 = g %ₘ φ`, then recurse on `g /ₘ φ`).
Equivalently `develop φ k g j = g /ₘ φ ^ j %ₘ φ`
(`develop_eq_divByMonic_pow_modByMonic`). -/
noncomputable def develop (φ : R[X]) : (k : ℕ) → R[X] → Fin k → R[X]
  | 0, _ => Fin.elim0
  | k + 1, g => Fin.cons (g %ₘ φ) (develop φ k (g /ₘ φ))

@[simp]
theorem develop_zero (φ : R[X]) (k : ℕ) (g : R[X]) : develop φ (k + 1) g 0 = g %ₘ φ := rfl

@[simp]
theorem develop_succ (φ : R[X]) (k : ℕ) (g : R[X]) (j : Fin k) :
    develop φ (k + 1) g j.succ = develop φ k (g /ₘ φ) j :=
  rfl

/-- **Naturality of the development under a ring hom** (`develop` commutes with `Polynomial.map`).
For a ring hom `f : R →+* S` and a *monic* divisor `φ`, mapping the `j`-th φ-adic digit of `g`
equals the `j`-th `(φ.map f)`-adic digit of `g.map f`:
`(develop φ k g j).map f = develop (φ.map f) k (g.map f) j`.
Both `%ₘ` and `/ₘ` by a monic commute with `map` (`Polynomial.map_modByMonic` /
`Polynomial.map_divByMonic`), so the structural recursion transports digit-by-digit.  This is the
polynomial-arithmetic core behind reduction-stability of the φ-adic digits: reducing coefficients
by a ring hom is the same as developing over the reduced ring.  (`φ.map f` is monic by
`Polynomial.Monic.map`, so the recursive call is well-formed.) -/
theorem develop_map {S : Type*} [CommRing S] (f : R →+* S) {φ : R[X]} (hφ : φ.Monic)
    (k : ℕ) (g : R[X]) (j : Fin k) :
    (develop φ k g j).map f = develop (φ.map f) k (g.map f) j := by
  induction k generalizing g with
  | zero => exact j.elim0
  | succ k ih =>
    induction j using Fin.cases with
    | zero =>
      rw [develop_zero, develop_zero, Polynomial.map_modByMonic f hφ]
    | succ i =>
      rw [develop_succ, develop_succ, ih (g /ₘ φ) i, Polynomial.map_divByMonic f hφ]

/-- **Digit degree bound** (blueprint deliverable 2): every φ-adic digit has degree strictly
below `φ.degree`. -/
theorem develop_digit_degree [Nontrivial R] {φ : R[X]} (hφ : φ.Monic) (k : ℕ) (g : R[X])
    (j : Fin k) : (develop φ k g j).degree < φ.degree := by
  induction k generalizing g with
  | zero => exact j.elim0
  | succ k ih =>
    induction j using Fin.cases with
    | zero => rw [develop_zero]; exact degree_modByMonic_lt g hφ
    | succ i => rw [develop_succ]; exact ih (g /ₘ φ) i

/-- `natDegree` form of the digit degree bound, for `0 < φ.natDegree`. -/
theorem develop_digit_natDegree [Nontrivial R] {φ : R[X]} (hφ : φ.Monic)
    (hm0 : 0 < φ.natDegree) (k : ℕ) (g : R[X]) (j : Fin k) :
    (develop φ k g j).natDegree < φ.natDegree := by
  by_cases h : develop φ k g j = 0
  · rw [h, natDegree_zero]; exact hm0
  · exact natDegree_lt_natDegree h (develop_digit_degree hφ k g j)

/-- **Reassembly, degree form** (blueprint deliverable 3): if `degree g < k * φ.natDegree` then
the first `k` φ-adic digits reassemble to `g`.  Stated with `Polynomial.degree` so that the
`k = 0` base case (`g = 0`) is non-vacuous and the inductive step needs no case split on
`k = 0`; the `natDegree` form of the blueprint is `develop_reassemble` below. -/
theorem develop_reassemble_degree {φ : R[X]} (hφ : φ.Monic) (k : ℕ) (g : R[X])
    (hg : g.degree < ((k * φ.natDegree : ℕ) : WithBot ℕ)) :
    ∑ j : Fin k, develop φ k g j * φ ^ (j : ℕ) = g := by
  induction k generalizing g with
  | zero =>
    have hg0 : g = 0 := by
      by_contra h
      rw [degree_eq_natDegree h, Nat.cast_lt] at hg
      omega
    simp [hg0]
  | succ k ih =>
    -- the quotient `g /ₘ φ` satisfies the degree bound one level down
    have hdiv : (g /ₘ φ).degree < ((k * φ.natDegree : ℕ) : WithBot ℕ) := by
      by_cases h0 : g /ₘ φ = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      · haveI : Nontrivial R := Nontrivial.of_polynomial_ne h0
        have hg' : g ≠ 0 := fun h => h0 (by rw [h, zero_divByMonic])
        have hglt : g.natDegree < (k + 1) * φ.natDegree := by
          rw [degree_eq_natDegree hg', Nat.cast_lt] at hg
          exact hg
        by_cases hmle : φ.natDegree ≤ g.natDegree
        · rw [degree_eq_natDegree h0, natDegree_divByMonic g hφ, Nat.cast_lt]
          rw [add_one_mul] at hglt
          omega
        · exact absurd ((divByMonic_eq_zero_iff hφ).2 (degree_lt_degree (by omega))) h0
    calc
      ∑ j : Fin (k + 1), develop φ (k + 1) g j * φ ^ (j : ℕ)
          = g %ₘ φ + φ * ∑ i : Fin k, develop φ k (g /ₘ φ) i * φ ^ (i : ℕ) := by
            rw [Fin.sum_univ_succ, Finset.mul_sum]
            congr 1
            · rw [develop_zero, Fin.val_zero, pow_zero, mul_one]
            · exact Finset.sum_congr rfl fun i _ => by
                rw [develop_succ, Fin.val_succ, pow_succ]; ring
      _ = g %ₘ φ + φ * (g /ₘ φ) := by rw [ih (g /ₘ φ) hdiv]
      _ = g := modByMonic_add_div g φ

/-- **Reassembly** (blueprint deliverable 3, `natDegree` form): for `g` of `natDegree`
`< k * φ.natDegree`, `∑ j : Fin k, develop φ k g j * φ ^ j = g`. -/
theorem develop_reassemble {φ : R[X]} (hφ : φ.Monic) (k : ℕ) (g : R[X])
    (hg : g.natDegree < k * φ.natDegree) :
    ∑ j : Fin k, develop φ k g j * φ ^ (j : ℕ) = g :=
  develop_reassemble_degree hφ k g (lt_of_le_of_lt degree_le_natDegree (Nat.cast_lt.2 hg))

/-- **Uniqueness of the development** (blueprint deliverable 4): any tuple of digits of degree
`< φ.natDegree` that reassembles to `g` *is* `develop φ k g`.  From the uniqueness of monic
division (`Polynomial.div_modByMonic_unique`), peeling one digit at a time. -/
theorem develop_unique {φ : R[X]} (hφ : φ.Monic) (k : ℕ) (g : R[X]) (b : Fin k → R[X])
    (hdeg : ∀ j, (b j).degree < (φ.natDegree : WithBot ℕ))
    (hsum : ∑ j : Fin k, b j * φ ^ (j : ℕ) = g) : b = develop φ k g := by
  induction k generalizing g with
  | zero => exact funext fun j => j.elim0
  | succ k ih =>
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    have hdeg0 : (b 0).degree < φ.degree := by
      rw [degree_eq_natDegree hφ.ne_zero]
      exact hdeg 0
    have hsplit : b 0 + φ * ∑ i : Fin k, b i.succ * φ ^ (i : ℕ) = g := by
      rw [← hsum, Fin.sum_univ_succ, Finset.mul_sum]
      congr 1
      · rw [Fin.val_zero, pow_zero, mul_one]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [Fin.val_succ, pow_succ]; ring
    obtain ⟨hdiv, hmod⟩ :=
      div_modByMonic_unique (∑ i : Fin k, b i.succ * φ ^ (i : ℕ)) (b 0) hφ ⟨hsplit, hdeg0⟩
    have htail : (fun i : Fin k => b i.succ) = develop φ k (g /ₘ φ) :=
      ih (g /ₘ φ) (fun i => b i.succ) (fun i => hdeg i.succ) hdiv.symm
    funext j
    induction j using Fin.cases with
    | zero => rw [develop_zero]; exact hmod.symm
    | succ i => rw [develop_succ]; exact congrFun htail i

/-! ### The closed form suggested by the blueprint

The blueprint suggests the spelling `develop φ k g j := g /ₘ φ ^ j %ₘ φ`.  We chose structural
recursion (it makes reassembly/uniqueness inductions clean), and recover the closed form as a
theorem.  The bridge is the composition law for monic division, which is not in mathlib. -/

/-- Composition of Euclidean division by monics: `p /ₘ q /ₘ r = p /ₘ (q * r)`. -/
theorem divByMonic_divByMonic {q r : R[X]} (hq : q.Monic) (hr : r.Monic) (p : R[X]) :
    p /ₘ q /ₘ r = p /ₘ (q * r) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have key : p %ₘ q + q * (p /ₘ q %ₘ r) + q * r * (p /ₘ q /ₘ r) = p := by
    have h2 : p /ₘ q %ₘ r + r * (p /ₘ q /ₘ r) = p /ₘ q := modByMonic_add_div _ r
    calc
      p %ₘ q + q * (p /ₘ q %ₘ r) + q * r * (p /ₘ q /ₘ r)
          = p %ₘ q + q * (p /ₘ q %ₘ r + r * (p /ₘ q /ₘ r)) := by ring
      _ = p %ₘ q + q * (p /ₘ q) := by rw [h2]
      _ = p := modByMonic_add_div p q
  have hqr : (q * r).degree = ((q.natDegree + r.natDegree : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (hq.mul hr).ne_zero, hq.natDegree_mul hr]
  have hdeg : (p %ₘ q + q * (p /ₘ q %ₘ r)).degree < (q * r).degree := by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · calc
        (p %ₘ q).degree < q.degree := degree_modByMonic_lt p hq
        _ ≤ (q * r).degree := by
            rw [hqr, degree_eq_natDegree hq.ne_zero, Nat.cast_le]
            omega
    · by_cases h0 : p /ₘ q %ₘ r = 0
      · rw [h0, mul_zero, degree_zero, hqr]
        exact WithBot.bot_lt_coe _
      · have hs : (p /ₘ q %ₘ r).natDegree < r.natDegree :=
          natDegree_lt_natDegree h0 (degree_modByMonic_lt _ hr)
        refine lt_of_le_of_lt degree_le_natDegree ?_
        rw [hqr, Nat.cast_lt]
        have hmul := natDegree_mul_le (p := q) (q := p /ₘ q %ₘ r)
        omega
  exact ((div_modByMonic_unique (p /ₘ q /ₘ r) _ (hq.mul hr) ⟨key, hdeg⟩).1).symm

/-- The closed form of the digits, as suggested by the blueprint:
`develop φ k g j = g /ₘ φ ^ j %ₘ φ`. -/
theorem develop_eq_divByMonic_pow_modByMonic {φ : R[X]} (hφ : φ.Monic) (k : ℕ) (g : R[X])
    (j : Fin k) : develop φ k g j = g /ₘ φ ^ (j : ℕ) %ₘ φ := by
  induction k generalizing g with
  | zero => exact j.elim0
  | succ k ih =>
    induction j using Fin.cases with
    | zero => rw [develop_zero, Fin.val_zero, pow_zero, divByMonic_one]
    | succ i =>
      rw [develop_succ, ih (g /ₘ φ) i, Fin.val_succ, pow_succ',
        divByMonic_divByMonic hφ (hφ.pow (i : ℕ))]

/-! ### Degree bookkeeping for digit sums (towards the bijection) -/

/-- A sum of digits of degree `< m` against powers `φ^0, …, φ^{k-1}` of a monic `φ` of degree
`m` has degree `< k * m`. -/
theorem degree_digit_sum_lt [Nontrivial R] {φ : R[X]} (hφ : φ.Monic) {m : ℕ}
    (hm : φ.natDegree = m) (k : ℕ) (b : Fin k → R[X])
    (hb : ∀ j, (b j).degree < (m : WithBot ℕ)) :
    (∑ j : Fin k, b j * φ ^ (j : ℕ)).degree < ((k * m : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
  intro j _
  by_cases hbj : b j = 0
  · rw [hbj, zero_mul, degree_zero]
    exact WithBot.bot_lt_coe _
  · have h1 : (b j).natDegree < m := by
      have h := hb j
      rwa [degree_eq_natDegree hbj, Nat.cast_lt] at h
    refine lt_of_le_of_lt degree_le_natDegree (Nat.cast_lt.2 ?_)
    calc
      (b j * φ ^ (j : ℕ)).natDegree
          ≤ (b j).natDegree + (φ ^ (j : ℕ)).natDegree := natDegree_mul_le
      _ = (b j).natDegree + (j : ℕ) * m := by rw [hφ.natDegree_pow, hm]
      _ < ((j : ℕ) + 1) * m := by rw [add_one_mul]; omega
      _ ≤ k * m := Nat.mul_le_mul (Nat.succ_le_of_lt j.isLt) (le_refl m)

/-- `φ^k` plus a digit sum of degree `< k * m` is monic of `natDegree` exactly `k * m` — the
well-definedness of the inverse of `developEquiv` (this conjunction *is* membership in
`QuotientBox.monicBox`). -/
theorem monic_pow_add_digit_sum [Nontrivial R] {φ : R[X]} (hφ : φ.Monic) {m : ℕ}
    (hm : φ.natDegree = m) (k : ℕ) (b : Fin k → R[X])
    (hb : ∀ j, (b j).degree < (m : WithBot ℕ)) :
    (φ ^ k + ∑ j : Fin k, b j * φ ^ (j : ℕ)).Monic ∧
      (φ ^ k + ∑ j : Fin k, b j * φ ^ (j : ℕ)).natDegree = k * m := by
  have hpowdeg : (φ ^ k).degree = ((k * m : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (hφ.pow k).ne_zero, hφ.natDegree_pow, hm]
  have hlt : (∑ j : Fin k, b j * φ ^ (j : ℕ)).degree < (φ ^ k).degree := by
    rw [hpowdeg]
    exact degree_digit_sum_lt hφ hm k b hb
  exact ⟨(hφ.pow k).add_of_left hlt,
    natDegree_eq_of_degree_eq_some (by rw [degree_add_eq_left_of_degree_lt hlt, hpowdeg])⟩

end Digits

/-! ## The bijection of level-`N` boxes (THE deliverable) -/

section Box

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Lemma A at level `N`** (blueprint deliverable 5, `RESTART_LEMMA.md` §1 count-native form):
for monic `φ` over `ZMod (p ^ N)` with `φ.natDegree = m`, the φ-adic development is a bijection
between the box of monic polynomials of degree `k * m` and `k`-tuples of digits of degree `< m`.

Forward: read the digits of `g - φ ^ k` (for monic `g` of degree `k·m` the `k`-th digit is `1`,
so subtracting `φ ^ k` leaves exactly the digits `0, …, k - 1`).
Inverse: `b ↦ φ ^ k + ∑ j, b j * φ ^ j`.

Blueprint erratum: the hypothesis `hN : 0 < N` is required (see module docstring); `hm0 : 0 < m`
is kept from the blueprint signature but is not needed. -/
noncomputable def developEquiv (N m k : ℕ) (hN : 0 < N) (φ : (ZMod (p ^ N))[X])
    (hφ : φ.Monic) (hm : φ.natDegree = m) (_hm0 : 0 < m) :
    QuotientBox.monicBox p N (k * m) ≃ (Fin k → Polynomial.degreeLT (ZMod (p ^ N)) m) :=
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  { toFun := fun g j =>
      ⟨develop φ k (g.1 - φ ^ k) j,
        mem_degreeLT.2 (by
          have h := develop_digit_degree hφ k (g.1 - φ ^ k) j
          rwa [degree_eq_natDegree hφ.ne_zero, hm] at h)⟩
    invFun := fun b =>
      ⟨φ ^ k + ∑ j : Fin k, (b j : (ZMod (p ^ N))[X]) * φ ^ (j : ℕ),
        monic_pow_add_digit_sum hφ hm k (fun j => (b j : (ZMod (p ^ N))[X]))
          (fun j => mem_degreeLT.1 (b j).2)⟩
    left_inv := fun g => by
      obtain ⟨f, hfm, hfd⟩ := g
      apply Subtype.ext
      show φ ^ k + ∑ j : Fin k, develop φ k (f - φ ^ k) j * φ ^ (j : ℕ) = f
      have h1 : f.degree = (φ ^ k).degree := by
        rw [degree_eq_natDegree hfm.ne_zero, degree_eq_natDegree (hφ.pow k).ne_zero, hfd,
          hφ.natDegree_pow, hm]
      have hsub : (f - φ ^ k).degree < ((k * m : ℕ) : WithBot ℕ) := by
        have h2 := degree_sub_lt h1 hfm.ne_zero
          (by rw [hfm.leadingCoeff, (hφ.pow k).leadingCoeff])
        rwa [degree_eq_natDegree hfm.ne_zero, hfd] at h2
      rw [develop_reassemble_degree hφ k (f - φ ^ k) (by rw [hm]; exact hsub)]
      ring
    right_inv := fun b => by
      funext j
      apply Subtype.ext
      show develop φ k
          ((φ ^ k + ∑ i : Fin k, (b i : (ZMod (p ^ N))[X]) * φ ^ (i : ℕ)) - φ ^ k) j
        = (b j : (ZMod (p ^ N))[X])
      rw [add_sub_cancel_left]
      have h := develop_unique hφ k (∑ i : Fin k, (b i : (ZMod (p ^ N))[X]) * φ ^ (i : ℕ))
        (fun i => (b i : (ZMod (p ^ N))[X]))
        (fun i => by rw [hm]; exact mem_degreeLT.1 (b i).2) rfl
      exact (congrFun h j).symm }

/-! ## The counting corollary and the dimensional cross-check (blueprint deliverable 6) -/

/-- The digit side counts to `((p^N)^m)^k`, via `Nat.card_pi` and `degreeLTEquiv`
(the `QuotientBox.card_monicBox` technique). -/
theorem card_digitTuples (N m k : ℕ) :
    Nat.card (Fin k → Polynomial.degreeLT (ZMod (p ^ N)) m) = ((p ^ N) ^ m) ^ k := by
  have h1 : Nat.card (Polynomial.degreeLT (ZMod (p ^ N)) m) = (p ^ N) ^ m := by
    rw [Nat.card_congr (Polynomial.degreeLTEquiv (ZMod (p ^ N)) m).toEquiv, Nat.card_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      QuotientBox.card_residueRing]
  rw [Nat.card_pi]
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Consistency cross-check**: counting the monic box through `developEquiv` gives
`((p^N)^m)^k`, and chaining with the independently proved
`QuotientBox.card_monicBox : Nat.card (monicBox p N (k*m)) = (p^N)^(k*m)` forces the arithmetic
identity `((p^N)^m)^k = (p^N)^(k*m)` — the bijection is dimensionally right.  (Both components
are proved through the equivalence, NOT by `pow_mul`, so the second genuinely cross-checks the
first against `card_monicBox`.) -/
theorem developEquiv_card_consistency (N m k : ℕ) (hN : 0 < N) (φ : (ZMod (p ^ N))[X])
    (hφ : φ.Monic) (hm : φ.natDegree = m) (hm0 : 0 < m) :
    Nat.card (QuotientBox.monicBox p N (k * m)) = ((p ^ N) ^ m) ^ k ∧
      ((p ^ N) ^ m) ^ k = (p ^ N) ^ (k * m) := by
  have h1 : Nat.card (QuotientBox.monicBox p N (k * m)) = ((p ^ N) ^ m) ^ k := by
    rw [Nat.card_congr (developEquiv p N m k hN φ hφ hm hm0), card_digitTuples]
  exact ⟨h1, by rw [← h1]; exact QuotientBox.card_monicBox p N (k * m) hN⟩

end Box

end LeanUrat.OM.Development
