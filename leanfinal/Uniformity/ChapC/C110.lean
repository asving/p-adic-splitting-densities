/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData
import Uniformity.ChapB.B03
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06
import Uniformity.ChapB.B13a
import Uniformity.ChapB.B22
import Uniformity.ChapB.B29
import Uniformity.ChapB.B30
import Uniformity.ChapB.B35c
import Uniformity.ChapB.B36
import Uniformity.ChapB.B39b

/-!
# Uniformity.ChapC.C110 — Step 2: transfer at one repeated linear root

**Chapter C, NODE C.110** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C3**.  `[signed: A-C.1; split → 2]`.

Both clauses of the split land here:

* `ht_conservative_card` — the conservative cell `C_a(k) = {(b_j) : v(b_j) ≥ (a−j)k + 1}` has
  `#C_a(k) = Q ^ D_u(N)` at general block degree `d`, where `Q = q ^ d`; the `d·Σ` shape of the
  exponent IS that `Q = q ^ d` clearing.
* `ht_transfer_residual_iff` — at an `e = 1` side of slope `−k` on a full-degree pure polygon,
  recentring the key to `Ψ = Φ − z·π ^ k` pushes the polygon strictly above the conservative
  bounds exactly when the residual polynomial is `(Y − z̄) ^ a`.

## What the statement says, term by term

The counted objects are level-`N` coefficient classes `c : Coeff O (a·d) N`
(`Coeff O n N = Fin n → O ⧸ 𝔪 ^ N`, landed in `Uniformity/Density/LocalData.lean`) that admit
an integral lift `b : Fin (a·d) → O` whose `i`-th entry has valuation at least
`(a − i/d)·k + 1`.  The index arithmetic `i / d` is the BLOCK read: the `a·d` scalar
coordinates are grouped into `a` consecutive blocks of length `d`, block `j` being the
coefficient vector of the degree-`< d` development coefficient `b_j`, and the conservative
bound is constant on a block.  So the constraint really is `v(b_j) ≥ (a − j)k + 1` for
`j < a`, stated coordinatewise.

The count is `q ^ (d · ∑_{j<a} (N − ((a−j)k + 1)))`.  Two disciplines are visible in that
exponent and both are load-bearing:

* the summand `N − ((a−j)k + 1)` is **ℕ-subtraction**, i.e. the C.53 CLIP `max(·, 0)`: when the
  conservative bound `(a−j)k + 1` lies at or beyond the window `N`, that block contributes the
  single zero class, not a negative exponent.  This is exactly the "including when conservative
  bounds lie beyond the window" clause of the STATEMENT, and it is where `card_res_ge` splits
  into its two cases;
* the leading `d ·` is the block clearing `Q = q ^ d`: each of the `a` blocks carries `d` scalar
  coordinates subject to the same bound.

## Proof route (the three moves)

1. **The lift is coordinatewise.**  `∃ b, proj b = c ∧ ∀ i, bound i ≤ v(b i)` is equivalent to
   `∀ i, ∃ x, mk x = c i ∧ bound i ≤ v(x)` — one direction reads off `congrFun`, the other
   chooses a lift per coordinate.  So the counted subtype is a Π of one-coordinate subtypes
   (`Equiv.subtypePiEquivPi`), and `Nat.card_pi` turns the count into a product.
2. **One coordinate: `#{r : O ⧸ 𝔪 ^ N | r has a lift of valuation ≥ m} = q ^ (N − m)`**
   (`card_res_ge`).  For `m ≤ N` the set is the range of `x ↦ [x·π ^ m]`, an additive map with
   kernel `𝔪 ^ (N−m)`, so the count is `#(O ⧸ 𝔪 ^ (N−m)) = q ^ (N−m)` by `card_res`.  For
   `N ≤ m` every such class is `0` and the count is `1 = q ^ 0` — the clip.
3. **Regrouping.**  `∑_{i < a·d} g(i / d) = d · ∑_{j < a} g j` (`sum_range_mul_div`), by
   induction on `a` with `Nat.mul_add_div`.

Nothing in clause 1 needs `π` beyond `Irreducible π`, and nothing needs completeness or a key:
it is pure valuation bookkeeping in the coefficient box.

## Clause 2 — the transfer, and why it is an identity of DIGITS

Write `A_i = dev Φ G i` for the `Φ`-adic development of `G` (`G` monic of degree `a·d`, so
`A_a = 1`), `c = z·π ^ k` and `Ψ = Φ − C c`.  The proof is four moves.

1. **The two-key binomial** (`dev_sub_C`).  From `G = ∑_{i≤a} A_i Φ ^ i` and `Φ = Ψ + c`,
   `dev Ψ G j = ∑_{i} C(c ^ (i−j)·binom(i,j))·A_i`.  This is `dev_unique` (B.06) applied to the
   rearranged family, whose degree bound is inherited from `degree_dev_lt` (B.03) and whose sum
   identity is `add_pow` plus `Finset.sum_Ico_Ico_comm` plus `sum_dev_eq` (B.05).  It is the
   honest replacement for a "translation is unitriangular" hand-wave: no matrix, no
   characteristic hypothesis, no window — the identity is exact in `O[X]`.
2. **Every term clears the conservative height.**  Purity gives `v(A_i) ≥ (a−i)k`
   (`suppVal_le_weight` + `suppVal_of_pure`, B.35b), and `v(c ^ (i−j)) ≥ (i−j)k`, and
   `(i−j)k + (a−i)k = (a−j)k`.  So `v(dev Ψ G j) ≥ (a−j)k` always: the recentred polygon can
   only sit ON or ABOVE the conservative line, never below.
3. **The digit at that height is a Taylor coefficient.**  `resMk` is additive over the sum and
   multiplicative with heights adding (B.35a), and `resMk π Φ K (C(π ^ K)·P) = resMk π Φ 0 P`
   (B.39b), so the height-`(a−j)k` digit of `dev Ψ G j` is
   `∑_i binom(i,j)·z̄ ^ (i−j)·R.coeff i`, which is `(taylor z̄ R).coeff j` — where
   `R = resPoly π Φ G k 1 hne H₀` and `R.coeff i = resMk π Φ ((a−i)k) A_i` by
   `resPoly_coeff_of_pure` (B.35c) once `H₀ = k·a` is read off purity.
4. **The criterion.**  `resMk π Φ K x = 0 ↔ digPoly π K x = 0 ↔ K+1 ≤ v(x)` (B.36 + B.24), so
   strict improvement over the conservative line at every `j < a` says exactly that all
   sub-leading Taylor coefficients of `R` vanish.  `R` is monic of degree `a`
   (`natDegree_resPoly`, `sideDeg_of_pure`, and `R.coeff a = resMk π Φ 0 1 = 1`), so
   `taylor z̄ R` is monic of degree `a` too, and a monic degree-`a` polynomial with vanishing
   sub-leading coefficients is `Y ^ a`.  Undoing the shift (`taylor_taylor`) turns that into
   `R = (Y − z̄) ^ a`.

**Lift-independence is a corollary, not an extra proof.**  The right-hand side of the
equivalence does not mention `z` except through `z̄ = digAt π 0 z`, so two lifts of the same
residue satisfy the left-hand side together — which is the STATEMENT's "the node and fiber
size are lift-independent" for this clause.

**What clause 2 does NOT ship.**  It is the equivalence, not the counting: that the transfer
is a bijection of cells of equal size is clause 1's count plus this criterion, assembled at
C.111/C.114, not here.

**DEPENDS.** C.108 (the `D_v` quantity whose value this is) · landed `card_coeff`/`card_res`
(`Uniformity/Density/LocalData.lean`).

**SOURCE.** `EFF.W12.84` step 2 (verbatim).

**TEETH.** the certificate's 300 translation-rank tests → retained; §13 fires one translate at
each prime.

**ENVIRONMENT.** ENV-C3.

## Status

Both clauses sorry-free, axiom-free (Lean core only).  Every helper is `private`: the node's
signed surface is exactly `ht_conservative_card` and `ht_transfer_residual_iff`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Valuation bookkeeping in one coordinate

PROMOTED (2026-08-20): the former `private` cluster (`le_addVal_iff_pow_dvd`,
`mem_pow_maximalIdeal_iff`, `card_res_ge_of_le`, `card_res_ge_of_ge`, `card_res_ge`) now
lives PUBLIC in `Uniformity/Density/LocalData.lean` §5b — the RE-PLAN item this file's
header flagged.  Consumed from there below; statements byte-identical. -/

/-! ### The block regrouping -/

/-- `∑_{i < a·d} g(i / d) = d · ∑_{j < a} g j` — the `Q = q ^ d` clearing, as ℕ-arithmetic. -/
private theorem sum_range_mul_div (d : ℕ) (hd : 0 < d) (g : ℕ → ℕ) (a : ℕ) :
    ∑ i ∈ Finset.range (a * d), g (i / d) = d * ∑ j ∈ Finset.range a, g j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hsplit : (a + 1) * d = a * d + d := by ring
    rw [hsplit, Finset.sum_range_add, ih, Finset.sum_range_succ, Nat.mul_add]
    congr 1
    have hconst : ∀ i ∈ Finset.range d, g ((a * d + i) / d) = g a := by
      intro i hi
      have hi' : i < d := Finset.mem_range.1 hi
      have hdiv : (a * d + i) / d = a := by
        rw [Nat.mul_comm a d, Nat.mul_add_div hd, Nat.div_eq_of_lt hi', Nat.add_zero]
      rw [hdiv]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### NODE C.110, clause 1 — the conservative-cell count -/

-- The signed hypothesis `hk : 0 < k` is kept (frozen signature) but is not consumed: the count
-- is valuation bookkeeping and degenerates correctly at `k = 0` (every block bound is `1`).
set_option linter.unusedVariables false in
/-- **NODE C.110 (clause 1) — `#C_a(k) = Q ^ D_u(N)` at block degree `d`.**

The level-`N` coefficient classes admitting an integral lift that satisfies the conservative
bounds `v(b_j) ≥ (a−j)k + 1` (read blockwise through `i / d`) number exactly
`q ^ (d · ∑_{j<a} (N − ((a−j)k + 1)))`, the summand being ℕ-subtracted (the C.53 clip), so the
identity holds **at every finite window, including when conservative bounds lie beyond it**. -/
theorem ht_conservative_card (hπ : Irreducible π) [Finite (ResidueField O)]
    (d a k N : ℕ) (hd : 0 < d) (hk : 0 < k) :
    Nat.card {c : Coeff O (a * d) N //
        ∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), (((a - i.1 / d) * k + 1 : ℕ) : ℕ∞) ≤ addVal O (b i)}
      = residueCard O ^ (d * ∑ j ∈ Finset.range a, (N - ((a - j) * k + 1))) := by
  classical
  -- the coordinatewise bound, and the one-coordinate predicate it induces
  set M : Fin (a * d) → ℕ := fun i => (a - i.1 / d) * k + 1 with hM
  set R : Fin (a * d) → Res O N → Prop := fun i r =>
    ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((M i : ℕ) : ℕ∞) ≤ addVal O x with hR
  -- 1. the lift may be chosen coordinatewise
  have hiff : ∀ c : Coeff O (a * d) N,
      (∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), ((M i : ℕ) : ℕ∞) ≤ addVal O (b i))
        ↔ ∀ i : Fin (a * d), R i (c i) := by
    intro c
    constructor
    · rintro ⟨b, hb, hval⟩ i
      exact ⟨b i, congrFun hb i, hval i⟩
    · intro h
      choose x hx hval using h
      exact ⟨x, funext hx, hval⟩
  -- 2. the count is a product over coordinates
  have e2 : {c : Coeff O (a * d) N // ∀ i, R i (c i)}
      ≃ (∀ i : Fin (a * d), {r : Res O N // R i r}) := Equiv.subtypePiEquivPi
  have hstep : Nat.card {c : Coeff O (a * d) N //
        ∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), ((M i : ℕ) : ℕ∞) ≤ addVal O (b i)}
      = ∏ i : Fin (a * d), residueCard O ^ (N - M i) := by
    rw [Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans e2), Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => card_res_ge hπ N (M i)
  rw [hstep, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : ∑ i : Fin (a * d), (N - M i)
      = ∑ i ∈ Finset.range (a * d), (fun j => N - ((a - j) * k + 1)) (i / d) :=
    Fin.sum_univ_eq_sum_range (fun i => N - ((a - i / d) * k + 1)) (a * d)
  rw [hsum, sum_range_mul_div d hd (fun j => N - ((a - j) * k + 1)) a]

/-! ### NODE C.110, clause 2 — the translate-residual criterion

The helpers below are `private`; only `ht_transfer_residual_iff` is signed. -/

section Clause2

open Uniformity.Density.Leaf Polynomial

private theorem degree_C_lt_of_pos {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (c : O) :
    (Polynomial.C c : Polynomial O).degree < φ.degree := by
  refine lt_of_le_of_lt Polynomial.degree_C_le ?_
  rw [Polynomial.degree_eq_natDegree hφ.ne_zero]
  exact_mod_cast hd

private theorem monic_sub_C {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (c : O) :
    (φ - Polynomial.C c).Monic :=
  hφ.sub_of_left (degree_C_lt_of_pos hφ hd c)

private theorem degree_sub_C_eq {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (c : O) :
    (φ - Polynomial.C c).degree = φ.degree := by
  rw [sub_eq_add_neg]
  exact Polynomial.degree_add_eq_left_of_degree_lt
    (by rw [Polynomial.degree_neg]; exact degree_C_lt_of_pos hφ hd c)

private theorem natDegree_sub_C_eq {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (c : O) :
    (φ - Polynomial.C c).natDegree = φ.natDegree :=
  Polynomial.natDegree_eq_of_degree_eq (degree_sub_C_eq hφ hd c)

/-- the recentred development coefficient: the binomial rearrangement of the `φ`-adic
development when the key moves from `φ` to `φ − c`. -/
private noncomputable def shiftDev (φ : Polynomial O) (c : O) (f : Polynomial O) (n j : ℕ) :
    Polynomial O :=
  ∑ i ∈ Finset.Ico j n, Polynomial.C (c ^ (i - j) * (i.choose j : O)) * dev φ f i

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem degree_C_mul_le' (x : O) (p : Polynomial O) :
    (Polynomial.C x * p).degree ≤ p.degree := by
  refine le_trans (Polynomial.degree_mul_le _ _) ?_
  simpa using add_le_add_left (Polynomial.degree_C_le (a := x)) p.degree

private theorem degree_shiftDev_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (c : O)
    (f : Polynomial O) (n j : ℕ) : (shiftDev φ c f n j).degree < φ.degree := by
  have hbot : (⊥ : WithBot ℕ) < φ.degree := by
    rw [Polynomial.degree_eq_natDegree hφ.ne_zero]; exact WithBot.bot_lt_coe _
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff hbot).2 ?_)
  intro i _
  exact lt_of_le_of_lt (degree_C_mul_le' _ _) (degree_dev_lt hφ hd f i)

private theorem dev_sub_C {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (c : O)
    (f : Polynomial O) {n : ℕ} (hf : f.natDegree < n * φ.natDegree) (j : ℕ) (hj : j < n) :
    dev (φ - Polynomial.C c) f j = shiftDev φ c f n j := by
  classical
  set ψ : Polynomial O := φ - Polynomial.C c with hψdef
  have hψ : ψ.Monic := monic_sub_C hφ hd c
  have hψd : ψ.natDegree = φ.natDegree := natDegree_sub_C_eq hφ hd c
  have hψdeg : ψ.degree = φ.degree := degree_sub_C_eq hφ hd c
  have hφeq : ψ + Polynomial.C c = φ := by rw [hψdef]; ring
  have hdeg : ∀ t, (shiftDev φ c f n t).degree < ψ.degree := by
    intro t; rw [hψdeg]; exact degree_shiftDev_lt hφ hd c f n t
  have hsum : ∑ t ∈ Finset.range n, shiftDev φ c f n t * ψ ^ t = f := by
    have h1 : ∑ t ∈ Finset.range n, shiftDev φ c f n t * ψ ^ t
        = ∑ t ∈ Finset.Ico 0 n, ∑ i ∈ Finset.Ico t n,
            Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t := by
      rw [Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun t _ => by rw [shiftDev, Finset.sum_mul]
    have h2 : ∑ t ∈ Finset.Ico 0 n, ∑ i ∈ Finset.Ico t n,
          Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t
        = ∑ i ∈ Finset.Ico 0 n, ∑ t ∈ Finset.Ico 0 (i + 1),
            Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t :=
      Finset.sum_Ico_Ico_comm 0 n
        (fun t i => Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t)
    have h3 : ∀ i, ∑ t ∈ Finset.Ico 0 (i + 1),
          Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t
        = dev φ f i * φ ^ i := by
      intro i
      rw [← hφeq, add_pow, Finset.mul_sum, ← Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.C_mul, map_pow, Polynomial.C_eq_natCast]
      ring
    rw [h1, h2, Finset.sum_congr rfl fun i _ => h3 i, ← Finset.range_eq_Ico]
    exact sum_dev_eq hφ hd f hf
  exact (dev_unique hψ (by rw [hψd]; exact hd) hdeg hsum j hj).symm

section Digits

variable {π : O}

private theorem le_gaussVal_C (hπ : Irreducible π) {m : ℕ} {y : O} (h : π ^ m ∣ y) :
    ((m : ℕ) : ℕ∞) ≤ gaussVal (Polynomial.C y) := by
  refine (le_gaussVal_iff hπ).2 fun i => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · simpa using h
  · simp [Polynomial.coeff_C, hi]

private theorem le_gaussVal_C_mul (hπ : Irreducible π) (x : O) {K : ℕ} {P : Polynomial O}
    (h : ((K : ℕ) : ℕ∞) ≤ gaussVal P) : ((K : ℕ) : ℕ∞) ≤ gaussVal (Polynomial.C x * P) := by
  refine (le_gaussVal_iff hπ).2 fun i => ?_
  rw [Polynomial.coeff_C_mul]
  exact Dvd.dvd.mul_left ((le_gaussVal_iff hπ).1 h i) x

private theorem resMk_C (hπ : Irreducible π) (φ : Polynomial O) (w : O) :
    resMk π φ 0 (Polynomial.C w)
      = algebraMap (IsLocalRing.ResidueField O) (resField φ) (IsLocalRing.residue O w) := by
  rw [resMk, digPoly_eq_map hπ (a := Polynomial.C w) (b := Polynomial.C w) (by simp),
    Polynomial.map_C]
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.mk_C _


private theorem le_gaussVal_C_pow_mul' (hπ : Irreducible π) (m : ℕ) (y : O) {K : ℕ} {P : Polynomial O}
    (h : ((K : ℕ) : ℕ∞) ≤ gaussVal P) :
    (((m + K : ℕ)) : ℕ∞) ≤ gaussVal (Polynomial.C (π ^ m * y) * P) := by
  refine (le_gaussVal_iff hπ).2 fun i => ?_
  obtain ⟨u, hu⟩ := (le_gaussVal_iff hπ).1 h i
  refine ⟨y * u, ?_⟩
  rw [Polynomial.coeff_C_mul, hu, pow_add]
  ring

end Digits

section TaylorAlg

variable {K : Type*} [CommRing K]

/-- the coefficients of a Taylor shift, as the binomial sum. -/
private theorem coeff_taylor_sum (P : Polynomial K) (w : K) {n : ℕ} (hP : P.natDegree < n) (j : ℕ) :
    (Polynomial.taylor w P).coeff j
      = ∑ i ∈ Finset.range n, P.coeff i * (w ^ (i - j) * (i.choose j : K)) := by
  conv_lhs => rw [P.as_sum_range' n hP]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.taylor_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]

/-- a monic polynomial all of whose sub-leading coefficients vanish is `X ^ n`. -/
private theorem eq_X_pow_of_monic_of_coeff_eq_zero {P : Polynomial K} (hP : P.Monic) {n : ℕ}
    (hdeg : P.natDegree = n) (hlow : ∀ j, j < n → P.coeff j = 0) : P = Polynomial.X ^ n := by
  refine Polynomial.ext fun m => ?_
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy m n with hm | rfl | hm
  · rw [hlow m hm, if_neg (by omega)]
  · rw [if_pos rfl]
    have := hP.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega)]

/-- the Taylor shift by `w` of `(X − C w) ^ n` is `X ^ n`. -/
private theorem taylor_sub_C_pow (w : K) (n : ℕ) :
    Polynomial.taylor w ((Polynomial.X - Polynomial.C w) ^ n) = (Polynomial.X : Polynomial K) ^ n := by
  rw [Polynomial.taylor_pow]
  congr 1
  rw [map_sub, Polynomial.taylor_X, Polynomial.taylor_C]
  ring

end TaylorAlg

section Transfer

open Uniformity.Density.Leaf

variable {π : O}

-- The signed hypotheses `ha : 2 ≤ a` and `hk : 0 < k` are kept (frozen signature) but are not
-- consumed: the digit identity below holds at every `a` and `k`, the repeated-root reading of
-- `2 ≤ a` and the positive-slope reading of `0 < k` being what makes the STATEMENT's situation
-- the intended one rather than what makes the equivalence true.
set_option linter.unusedVariables false in
theorem ht_transfer_residual_iff (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) {a k : ℕ} (ha : 2 ≤ a) (hk : 0 < k)
    (z : O) {G : Polynomial O} (hG : G.Monic) (hGdeg : G.natDegree = a * Φ.natDegree)
    (hpure : IsPure Φ G k 1) (hne : (sideSet Φ G k 1).Nonempty) {H₀ : ℕ}
    (hp : npHgt Φ G (sideMin Φ G k 1 hne) = (H₀ : ℕ∞)) :
    (∀ j, j < a →
        (((a - j) * k + 1 : ℕ) : ℕ∞) ≤ npHgt (Φ - Polynomial.C (z * π ^ k)) G j)
      ↔ resPoly π Φ G k 1 hne H₀
          = (Polynomial.X - Polynomial.C (algebraMap (IsLocalRing.ResidueField O) (resField Φ)
              (digAt π 0 z))) ^ a := by
  classical
  have hd : 0 < Φ.natDegree := hΦ.pos
  have hmon : Φ.Monic := hΦ.monic
  have hone : (0 : ℕ) < 1 := Nat.one_pos
  have hcop : Nat.Coprime k 1 := Nat.coprime_one_right k
  set c : O := z * π ^ k with hcdef
  set ψ : Polynomial O := Φ - Polynomial.C c with hψdef
  have hψm : ψ.Monic := monic_sub_C hmon hd c
  have hψdeg : ψ.degree = Φ.degree := degree_sub_C_eq hmon hd c
  have hψnd : ψ.natDegree = Φ.natDegree := natDegree_sub_C_eq hmon hd c
  set w : resField Φ :=
    algebraMap (IsLocalRing.ResidueField O) (resField Φ) (digAt π 0 z) with hwdef
  set R : Polynomial (resField Φ) := resPoly π Φ G k 1 hne H₀ with hRdef
  -- (1) the pinned height is `k · a`
  have hsupp : suppVal Φ G k 1 = ((k * a : ℕ) : ℕ∞) := suppVal_of_pure hmon hd hG hGdeg hpure
  have hmin : sideMin Φ G k 1 hne = 0 := sideMin_of_pure hpure hne
  have hH : H₀ = k * a := by
    have h0 : (1 : ℕ) • npHgt Φ G 0 + ((k * 0 : ℕ) : ℕ∞) = suppVal Φ G k 1 := hpure.1
    rw [hsupp] at h0
    simp only [one_smul, Nat.mul_zero, Nat.cast_zero, add_zero] at h0
    rw [hmin] at hp
    rw [hp] at h0
    exact_mod_cast h0
  -- (2) the conservative bound on the ORIGINAL key
  have hgv : ∀ i, (((a - i) * k : ℕ) : ℕ∞) ≤ npHgt Φ G i := by
    intro i
    rcases le_or_gt i a with hia | hia
    · have hle := suppVal_le_weight hmon hd hone k G i
      rw [hsupp] at hle
      simp only [one_smul] at hle
      have hik : i * k ≤ a * k := Nat.mul_le_mul_right k hia
      have hsplit : (a - i) * k + k * i = k * a := by
        have h1 : k * i = i * k := Nat.mul_comm k i
        have h2 : k * a = a * k := Nat.mul_comm k a
        rw [Nat.sub_mul]
        omega
      have hfin : ((k * i : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
      rw [← hsplit, Nat.cast_add] at hle
      exact (WithTop.add_le_add_iff_right hfin).1 hle
    · rw [Nat.sub_eq_zero_of_le hia.le, Nat.zero_mul, Nat.cast_zero]
      simp
  -- (3) the residual coefficients
  have hRc : ∀ t, R.coeff t = resMk π Φ ((a - t) * k) (dev Φ G t) := by
    intro t
    have hc := resPoly_coeff_of_pure hπ hmon hd hG hGdeg hone hcop hpure hne H₀ t
    have harith : H₀ - k * t = (a - t) * k := by
      rw [hH, Nat.sub_mul, Nat.mul_comm a k, Nat.mul_comm t k]
    rw [hRdef, hc, harith, Nat.one_mul]
  -- (4) the residual polynomial is monic of degree `a`
  have htop : suppVal Φ G k 1 ≠ ⊤ := by rw [hsupp]; exact ENat.coe_ne_top _
  have hsd : sideDeg Φ G k 1 hne = a := by
    have hs := sideDeg_of_pure hmon hd hG hGdeg hone hcop hpure hne
    rwa [Nat.one_mul] at hs
  have hRdeg : R.natDegree = a := by
    have hn := (natDegree_resPoly hπ hΦ hone hcop htop hne hp).1
    rw [hRdef, hn, hsd]
  have hRmonic : R.Monic := by
    have hlead : R.coeff a = 1 := by
      rw [hRc a, Nat.sub_self, Nat.zero_mul, dev_top hmon hd hG hGdeg]
      exact resMk_one hπ Φ
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hRdeg]
    exact hlead
  -- (5) the recentred development
  have hGd : G.natDegree < (a + 1) * Φ.natDegree := by
    rw [hGdeg, Nat.succ_mul]; omega
  have hdevψ : ∀ j, j < a + 1 →
      dev ψ G j = ∑ i ∈ Finset.range (a + 1),
        Polynomial.C (c ^ (i - j) * (i.choose j : O)) * dev Φ G i := by
    intro j hj
    have hsub : Finset.Ico j (a + 1) ⊆ Finset.range (a + 1) := fun i hi =>
      Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
    rw [hψdef, dev_sub_C hmon hd c G hGd j hj, shiftDev]
    refine Finset.sum_subset hsub ?_
    intro i hi hni
    have hij : i < j := by
      rcases Nat.lt_or_ge i j with h | h
      · exact h
      · exact absurd (Finset.mem_Ico.2 ⟨h, Finset.mem_range.1 hi⟩) hni
    rw [Nat.choose_eq_zero_of_lt hij]
    simp
  -- (6) every recentred term clears the conservative height
  have harith : ∀ j i, j ≤ i → i ≤ a → k * (i - j) + (a - i) * k = (a - j) * k := by
    intro j i hji hia
    have h1 : k * (i - j) = (i - j) * k := Nat.mul_comm _ _
    have h2 : (i - j) + (a - i) = a - j := by omega
    rw [h1, ← Nat.add_mul, h2]
  have hcpow : ∀ j i : ℕ, c ^ (i - j) * (i.choose j : O)
      = π ^ (k * (i - j)) * (z ^ (i - j) * (i.choose j : O)) := by
    intro j i
    rw [hcdef, mul_pow, ← pow_mul, Nat.mul_comm k (i - j)]
    ring
  have htermall : ∀ j i, i < a + 1 →
      (((a - j) * k : ℕ) : ℕ∞)
        ≤ gaussVal (Polynomial.C (c ^ (i - j) * (i.choose j : O)) * dev Φ G i) := by
    intro j i hi
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Nat.choose_eq_zero_of_lt hij, Nat.cast_zero, mul_zero, map_zero, zero_mul,
        show gaussVal (0 : Polynomial O) = ⊤ from gaussVal_eq_top_iff.2 rfl]
      exact le_top
    · have hia : i ≤ a := by omega
      rw [hcpow j i, ← harith j i hij hia]
      exact le_gaussVal_C_pow_mul' hπ (k * (i - j)) _ (hgv i)
  have hlow : ∀ j, j < a + 1 → (((a - j) * k : ℕ) : ℕ∞) ≤ npHgt ψ G j := by
    intro j hj
    rw [npHgt, hdevψ j hj]
    exact le_gaussVal_finsetSum hπ _ _ fun i hi => htermall j i (Finset.mem_range.1 hi)
  -- (7) the recentred digit IS the Taylor coefficient of the residual polynomial
  have hdig : ∀ j, j < a + 1 →
      resMk π Φ ((a - j) * k) (dev ψ G j) = (Polynomial.taylor w R).coeff j := by
    intro j hj
    rw [hdevψ j hj,
      resMk_finsetSum hπ _ _ (fun i hi => htermall j i (Finset.mem_range.1 hi)),
      coeff_taylor_sum R w (n := a + 1) (by rw [hRdeg]; omega) j]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hia : i ≤ a := by have := Finset.mem_range.1 hi; omega
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Nat.choose_eq_zero_of_lt hij]
      simp [resMk_of_zero hπ]
    · have hA : ((k * (i - j) : ℕ) : ℕ∞)
          ≤ gaussVal (Polynomial.C (c ^ (i - j) * (i.choose j : O))) := by
        refine le_gaussVal_C hπ ?_
        rw [hcpow j i]
        exact Dvd.intro _ rfl
      rw [← harith j i hij hia, resMk_mul hπ hA (hgv i), ← hRc i]
      have hstep : resMk π Φ (k * (i - j)) (Polynomial.C (c ^ (i - j) * (i.choose j : O)))
          = w ^ (i - j) * (i.choose j : resField Φ) := by
        rw [hcpow j i, Polynomial.C_mul, resMk_C_pow_mul hπ, resMk_C hπ]
        rw [hwdef, digAt_zero]
        simp
      rw [hstep]
      ring
  -- (8) the criterion
  have hcrit : ∀ j, j < a →
      (((((a - j) * k + 1 : ℕ)) : ℕ∞) ≤ npHgt ψ G j ↔ (Polynomial.taylor w R).coeff j = 0) := by
    intro j hj
    have hj' : j < a + 1 := by omega
    have hdegj : (dev ψ G j).degree < Φ.degree := by
      rw [← hψdeg]
      exact degree_dev_lt hψm (by rw [hψnd]; exact hd) G j
    rw [← hdig j hj', resMk_eq_zero_iff hπ hΦ hdegj, digPoly_eq_zero_iff hπ (hlow j hj')]
    exact Iff.rfl
  -- (9) assembling
  constructor
  · intro hyp
    have hzero : ∀ j, j < a → (Polynomial.taylor w R).coeff j = 0 :=
      fun j hj => (hcrit j hj).1 (hyp j hj)
    have hTm : (Polynomial.taylor w R).Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_taylor]
      exact hRmonic
    have hTd : (Polynomial.taylor w R).natDegree = a := by
      rw [Polynomial.natDegree_taylor]; exact hRdeg
    have hT : Polynomial.taylor w R = Polynomial.X ^ a :=
      eq_X_pow_of_monic_of_coeff_eq_zero hTm hTd hzero
    have hback : Polynomial.taylor (-w) (Polynomial.taylor w R) = R := by
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    rw [← hback, hT, Polynomial.taylor_X_pow, map_neg, ← sub_eq_add_neg]
  · intro hyp j hj
    refine (hcrit j hj).2 ?_
    rw [hyp, taylor_sub_C_pow, Polynomial.coeff_X_pow, if_neg (by omega)]

end Transfer


end Clause2

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_conservative_card
#print axioms Uniformity.Density.Tower.ht_transfer_residual_iff

end AxCheck
