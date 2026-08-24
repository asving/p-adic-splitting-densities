/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C52
import Uniformity.ChapC.C127
import Uniformity.ChapC.C131d
import Uniformity.ChapC.C131f
import Uniformity.ChapC.C131u

/-!
# Uniformity.ChapC.C131ad — the box monomial coefficient floor and `dvAbove_boxMonomial`

**Chapter C, NODE C.131ad′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §2.3–§2.4, §3.7, and the §5 node table;
C.52's Step 0 as documented in `C52.lean`).

The box monomial is `C c · xᵃ · Φ′ᵇ · Φ₂ʲ` with `Φ′ = F.key` and `Φ₂ = composedKey T`.  The
node proves that all of its level-1 slots sit at or above the grid weight
`gridWeight T v a b j` whenever `v` is a certified valuation floor for `c` — the `DvAbove`
form consumed by C.52's Step 0.  Both statements are total in `a`, `b`, `j`: no box-range
hypothesis is needed.

## The proof route (the "two carries", made structural)

1. **Lift.**  The box monomial is the evaluation at `Y = F.key` of the two-variable lift
   `C (C c · xᵃ) · Yᵇ · (K_T T)ʲ`, whose two-index weight is at least the grid weight:
   the monomial factor prices to `wtCoeff c a b` and each `K_T` factor to `E₂`
   (C.131g′'s `WT_K_T`, C.131c′'s `WT_mul`).
2. **Carry down.**  A two-variable polynomial whose scalar weight clears `w` keeps that
   floor on every scalar coefficient of every canonical `F.key`-digit of its evaluation
   (`dev_coeff_floor`).  The proof descends on the inner-degree excess: one `carryStep`
   removes the top inner monomial `c·x^(D′+n)` of every outer coefficient by the x-carry
   split `x^(D′+n)·Yᵇ = (x^(D′) − Φ′)·xⁿ·Yᵇ + xⁿ·Y^(b+1)` — the tail branch is priced by
   the key's side (C.131d′–e′ `xCarry_tail_floor`), the paid branch by
   `u₂ ≥ e₂D′h` (C.131e′ `xCarry_branch_WT_exact` plus the node floor) — and once the lift
   is in-grid the digits ARE the coefficients (C.127's `dev_eval_eq_coeff`).
3. **Bridge.**  C.131u′'s `dvAbove_of_forall_coeff_floor` converts the per-coefficient
   floors into `DvAbove` (only the proved direction of §3.7 is used).

This is deliberately NOT the tagged census (C.131m′–o′): no tags, no `K_T`-coordinate
recarry — the box monomial needs only the value-blind carry-down, so the file stays inside
its declared dependencies C.131c′–j′ + C.131u′ (plus landed C.127 for the in-grid transfer).

## Status

Sorry-free, axiom-free (Lean core only; AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131ad

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131f
open Uniformity.Density.Tower.C131u

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Weight utilities -/

/-- A common floor on the two-index weight passes through a finite sum. -/
theorem le_WT_sum {ι : Type*} (T : TowerDatum F H₀ hpin) (s : Finset ι)
    (f : ι → Polynomial (Polynomial O)) {w : ℕ∞}
    (h : ∀ i ∈ s, w ≤ WT T (f i)) : w ≤ WT T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact le_trans (le_min (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))
        (WT_add T _ _)

/-- A coefficientwise floor at a fixed outer index bounds the weight of the corresponding
outer monomial. -/
theorem le_WT_C_mul_X_pow (T : TowerDatum F H₀ hpin) (g : Polynomial O) (b : ℕ) {w : ℕ∞}
    (h : ∀ a', w ≤ wtCoeff T (g.coeff a') a' b) :
    w ≤ WT T (Polynomial.C g * Polynomial.X ^ b) := by
  classical
  unfold WT
  refine Finset.le_inf fun b' hb' => ?_
  have hb : b' = b := by
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mem_support_iff,
      Polynomial.coeff_monomial] at hb'
    split at hb'
    · exact ‹b = b'›.symm
    · exact False.elim (hb' rfl)
  subst hb
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, if_pos rfl]
  exact Finset.le_inf fun a' _ => h a'

/-- The doubly constant polynomial has weight at least the origin coefficient weight. -/
theorem le_WT_C_C (T : TowerDatum F H₀ hpin) (c : O) :
    wtCoeff T c 0 0 ≤ WT T (Polynomial.C (Polynomial.C c)) := by
  have h0 : (Polynomial.C (Polynomial.C c) : Polynomial (Polynomial O))
      = Polynomial.C (Polynomial.C c) * Polynomial.X ^ 0 := by
    rw [pow_zero, mul_one]
  rw [h0]
  refine le_WT_C_mul_X_pow T _ 0 fun a' => ?_
  by_cases ha : a' = 0
  · subst ha
    rw [Polynomial.coeff_C_zero]
  · rw [Polynomial.coeff_C, if_neg ha, wtCoeff_zero]
    exact le_top

/-- Splitting the coefficient weight at the inner index `D′ + n` into its origin part and
the tail-branch price of C.131e′. -/
theorem wtCoeff_add_shift (T : TowerDatum F H₀ hpin) (x : O) (n b : ℕ) :
    wtCoeff T x (F.e₁ * F.f₁ + n) b =
      wtCoeff T x 0 0 +
        ((((F.e₁ * F.f₁) * T.e₂ * F.h + n * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)) := by
  unfold wtCoeff
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- The paid `Y` branch is at least as expensive as the inner monomial it replaces: the
x-carry trades `D′` inner degrees (price `D′e₂h`) for one outer degree (price `u₂`), and
`u₂ = e₂D′h + margin`. -/
theorem wtCoeff_le_paid (T : TowerDatum F H₀ hpin) (x : O) (n b : ℕ) :
    wtCoeff T x (F.e₁ * F.f₁ + n) b ≤
      wtCoeff T x 0 0 +
        (((n * (T.e₂ * F.h) + b * T.u₂ +
          (T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin) : ℕ) : ℕ∞)) := by
  rw [wtCoeff_add_shift T x n b]
  have hswap : (F.e₁ * F.f₁) * T.e₂ * F.h = T.e₂ * ((F.e₁ * F.f₁) * F.h) := by ring
  have hnat : (F.e₁ * F.f₁) * T.e₂ * F.h + n * (T.e₂ * F.h) + b * T.u₂ ≤
      n * (T.e₂ * F.h) + b * T.u₂ + (T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin) := by
    omega
  have hcast : ((((F.e₁ * F.f₁) * T.e₂ * F.h + n * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)) ≤
      (((n * (T.e₂ * F.h) + b * T.u₂ +
        (T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin) : ℕ) : ℕ∞)) := by
    exact_mod_cast hnat
  exact add_le_add le_rfl hcast

/-- The key's leading term cancels in the x-carry tail. -/
theorem natDegree_X_pow_sub_key_le (F : KeyFrame O π) :
    (Polynomial.X ^ (F.e₁ * F.f₁) - F.key).natDegree ≤ F.e₁ * F.f₁ - 1 := by
  have hd : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  have hN' : F.e₁ * F.f₁ ≤ N := by omega
  rcases Nat.eq_or_lt_of_le hN' with hEq | hLt
  · rw [← hEq, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl]
    have hlead : F.key.coeff (F.e₁ * F.f₁) = 1 := by
      have h1 := F.hmonic.coeff_natDegree
      rwa [F.hdeg] at h1
    rw [hlead, sub_self]
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [F.hdeg]; omega), sub_self]

/-! ## The carry step -/

/-- One x-carry applied to the top inner monomial `c·x^(D′+n)` of the inner polynomial `g`
placed at outer index `b`: the untouched low part, the tail branch `c·(x^(D′) − Φ′)·xⁿ·Yᵇ`,
and the paid branch `c·xⁿ·Y^(b+1)`. -/
noncomputable def carryTerm (F : KeyFrame O π) (n b : ℕ) (g : Polynomial O) :
    Polynomial (Polynomial O) :=
  Polynomial.C (g - Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
      Polynomial.X ^ (F.e₁ * F.f₁ + n)) * Polynomial.X ^ b
    + (Polynomial.C (Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
        ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ n)) * Polynomial.X ^ b
      + Polynomial.C (Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
          Polynomial.X ^ n) * Polynomial.X ^ (b + 1))

/-- The carry is invisible to evaluation at `Y = F.key`. -/
theorem eval_carryTerm (F : KeyFrame O π) (n b : ℕ) (g : Polynomial O) :
    Polynomial.eval F.key (carryTerm F n b g) = g * F.key ^ b := by
  unfold carryTerm
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- The carry preserves any coefficientwise weight floor: the low part is a coefficient
sub-selection, the tail branch is priced by the key's pure side, and the paid branch by
the node floor `u₂ ≥ e₂D′h`. -/
theorem le_WT_carryTerm (T : TowerDatum F H₀ hpin) (n b : ℕ) (g : Polynomial O) {w : ℕ∞}
    (h : ∀ a', w ≤ wtCoeff T (g.coeff a') a' b) :
    w ≤ WT T (carryTerm F n b g) := by
  have hbase : w ≤ wtCoeff T (g.coeff (F.e₁ * F.f₁ + n)) (F.e₁ * F.f₁ + n) b :=
    h (F.e₁ * F.f₁ + n)
  have h₁ : w ≤ WT T (Polynomial.C (g - Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
      Polynomial.X ^ (F.e₁ * F.f₁ + n)) * Polynomial.X ^ b) := by
    refine le_WT_C_mul_X_pow T _ b fun a' => ?_
    by_cases ha : a' = F.e₁ * F.f₁ + n
    · subst ha
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
        mul_one, sub_self, wtCoeff_zero]
      exact le_top
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ha,
        mul_zero, sub_zero]
      exact h a'
  have h₂ : w ≤ WT T (Polynomial.C (Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
      ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ n)) * Polynomial.X ^ b) := by
    rw [Polynomial.C_mul, mul_assoc]
    refine le_trans ?_ (le_trans (add_le_add (le_WT_C_C T _) (xCarry_tail_floor T n b))
      (WT_mul T _ _))
    rw [← wtCoeff_add_shift T _ n b]
    exact hbase
  have h₃ : w ≤ WT T (Polynomial.C (Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
      Polynomial.X ^ n) * Polynomial.X ^ (b + 1)) := by
    rw [Polynomial.C_mul, mul_assoc]
    exact le_trans (le_trans hbase (wtCoeff_le_paid T _ n b))
      (le_trans (add_le_add (le_WT_C_C T _)
        (le_of_eq (xCarry_branch_WT_exact T n b).symm)) (WT_mul T _ _))
  exact le_trans (le_min h₁ (le_trans (le_min h₂ h₃) (WT_add T _ _))) (WT_add T _ _)

/-- Every outer coefficient of the carry output has inner degree at most `D′ + n − 1`. -/
theorem carryTerm_coeff_natDegree_le (F : KeyFrame O π) (n b : ℕ) (g : Polynomial O)
    (hg : g.natDegree ≤ F.e₁ * F.f₁ + n) (b' : ℕ) :
    ((carryTerm F n b g).coeff b').natDegree ≤ F.e₁ * F.f₁ + n - 1 := by
  have hd : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hkey := natDegree_X_pow_sub_key_le F
  have h1 : (g - Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
      Polynomial.X ^ (F.e₁ * F.f₁ + n)).natDegree ≤ F.e₁ * F.f₁ + n - 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    have hN' : F.e₁ * F.f₁ + n ≤ N := by omega
    rcases Nat.eq_or_lt_of_le hN' with hEq | hLt
    · rw [← hEq, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl, mul_one, sub_self]
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by omega), mul_zero, sub_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h2 : (Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
      ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ n)).natDegree ≤
      F.e₁ * F.f₁ + n - 1 := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  have h3 : (Polynomial.C (g.coeff (F.e₁ * F.f₁ + n)) *
      Polynomial.X ^ n).natDegree ≤ F.e₁ * F.f₁ + n - 1 := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  unfold carryTerm
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_
    (le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)))
  all_goals simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  · split
    · exact h1
    · simp
  · split
    · exact h2
    · simp
  · split
    · exact h3
    · simp

/-- One full carry layer: apply `carryTerm` to every outer coefficient. -/
noncomputable def carryStep (F : KeyFrame O π) (n : ℕ)
    (Q : Polynomial (Polynomial O)) : Polynomial (Polynomial O) :=
  ∑ b ∈ Q.support, carryTerm F n b (Q.coeff b)

/-- The carry layer is invisible to evaluation at `Y = F.key`. -/
theorem eval_carryStep (F : KeyFrame O π) (n : ℕ) (Q : Polynomial (Polynomial O)) :
    Polynomial.eval F.key (carryStep F n Q) = Polynomial.eval F.key Q := by
  classical
  rw [carryStep, Polynomial.eval_finsetSum]
  conv_rhs => rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_congr rfl fun b _ => eval_carryTerm F n b (Q.coeff b)

/-- The carry layer preserves any weight floor. -/
theorem le_WT_carryStep (T : TowerDatum F H₀ hpin) (n : ℕ)
    (Q : Polynomial (Polynomial O)) {w : ℕ∞} (hw : w ≤ WT T Q) :
    w ≤ WT T (carryStep F n Q) := by
  classical
  refine le_WT_sum T Q.support _ fun b _ =>
    le_WT_carryTerm T n b (Q.coeff b) fun a' => ?_
  exact le_trans hw (WT_le_wtCoeff T Q a' b)

/-- The carry layer strictly lowers the inner-degree excess. -/
theorem carryStep_coeff_natDegree_lt (F : KeyFrame O π) (n : ℕ)
    (Q : Polynomial (Polynomial O))
    (hQ : ∀ b, (Q.coeff b).natDegree < F.e₁ * F.f₁ + n + 1) (b' : ℕ) :
    ((carryStep F n Q).coeff b').natDegree < F.e₁ * F.f₁ + n := by
  classical
  have hd : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hb : ((carryStep F n Q).coeff b').natDegree ≤ F.e₁ * F.f₁ + n - 1 := by
    rw [carryStep, Polynomial.finsetSum_coeff]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    exact carryTerm_coeff_natDegree_le F n b (Q.coeff b) (by have := hQ b; omega) b'
  omega

/-! ## The carry-down erasure: weight floors descend to digit coefficient floors -/

/-- **Bounded carry-down.**  If every outer coefficient of `Q` has inner degree below
`D′ + n` and the two-index weight of `Q` clears `w`, then every scalar coefficient of every
canonical `F.key`-digit of `Q(F.key)` clears `w` at its own grid position. -/
theorem dev_coeff_floor_of_WT_floor (T : TowerDatum F H₀ hpin) (n : ℕ) :
    ∀ Q : Polynomial (Polynomial O),
      (∀ b, (Q.coeff b).natDegree < F.e₁ * F.f₁ + n) →
      ∀ {w : ℕ∞}, w ≤ WT T Q → ∀ s a : ℕ,
        w ≤ wtCoeff T ((dev F.key (Polynomial.eval F.key Q) s).coeff a) a s := by
  induction n with
  | zero =>
      intro Q hQ w hw s a
      have hdeg : ∀ i, (Q.coeff i).degree < F.key.degree := by
        intro i
        apply Polynomial.degree_lt_degree
        rw [F.hdeg]
        simpa using hQ i
      rw [dev_eval_eq_coeff F hdeg]
      exact le_trans hw (WT_le_wtCoeff T Q a s)
  | succ n ih =>
      intro Q hQ w hw s a
      rw [← eval_carryStep F n Q]
      exact ih (carryStep F n Q)
        (carryStep_coeff_natDegree_lt F n Q fun b => by have := hQ b; omega)
        (le_WT_carryStep T n Q hw) s a

/-- **Carry-down erasure (unbounded).**  The same conclusion for an arbitrary two-variable
lift: the excess is finite, so the bounded form applies at the support's degree supremum. -/
theorem dev_coeff_floor (T : TowerDatum F H₀ hpin) (Q : Polynomial (Polynomial O))
    {w : ℕ∞} (hw : w ≤ WT T Q) (s a : ℕ) :
    w ≤ wtCoeff T ((dev F.key (Polynomial.eval F.key Q) s).coeff a) a s := by
  classical
  refine dev_coeff_floor_of_WT_floor T
    (Q.support.sup fun b => (Q.coeff b).natDegree) Q (fun b => ?_) hw s a
  have hd : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  by_cases hb : b ∈ Q.support
  · have hle := Finset.le_sup (f := fun b => (Q.coeff b).natDegree) hb
    omega
  · have hz : Q.coeff b = 0 := not_ne_iff.mp (mt Polynomial.mem_support_iff.mpr hb)
    rw [hz, Polynomial.natDegree_zero]
    omega

/-! ## The box monomial lift -/

/-- Iterated composed-key price: `WT (K_Tʲ) ≥ j·E₂`. -/
theorem le_WT_K_T_pow (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (j : ℕ) :
    ((j * T.E₂ : ℕ) : ℕ∞) ≤ WT T (K_T T ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      refine le_trans ?_ (WT_mul T (K_T T ^ j) (K_T T))
      rw [WT_K_T T hπ]
      calc (((j + 1) * T.E₂ : ℕ) : ℕ∞)
          = ((j * T.E₂ : ℕ) : ℕ∞) + (T.E₂ : ℕ∞) := by push_cast; ring
        _ ≤ WT T (K_T T ^ j) + (T.E₂ : ℕ∞) := add_le_add ih le_rfl

/-- The reduced two-variable image reconstructs the composed key at `Y = F.key`. -/
theorem eval_K_T (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    Polynomial.eval F.key (K_T T) = composedKey T := by
  classical
  have hdeg : (composedKey T).natDegree < (T.e₂ * T.f₂ + 1) * F.key.natDegree := by
    have hpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
    have hr : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
    have hℓ : (T.levelDatum hπ).ℓ = T.e₂ := rfl
    rw [composedKey_natDegree T hπ, LevelDatum.keyDeg₂, hℓ, hr, F.hdeg]
    calc F.e₁ * F.f₁ * T.e₂ * T.f₂ = T.e₂ * T.f₂ * (F.e₁ * F.f₁) := by ring
      _ < (T.e₂ * T.f₂ + 1) * (F.e₁ * F.f₁) :=
        (Nat.mul_lt_mul_right hpos).mpr (Nat.lt_succ_self _)
  rw [K_T, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  exact sum_dev_eq F.hmonic F.natDegree_key_pos (composedKey T) hdeg

/-- The monomial factor of the box lift prices to its coefficient weight. -/
theorem le_WT_box_monomial (T : TowerDatum F H₀ hpin) (c : O) (a b : ℕ) :
    wtCoeff T c a b ≤
      WT T (Polynomial.C (Polynomial.C c * Polynomial.X ^ a) * Polynomial.X ^ b) := by
  refine le_WT_C_mul_X_pow T _ b fun a' => ?_
  by_cases ha : a' = a
  · subst ha
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ha, mul_zero, wtCoeff_zero]
    exact le_top

/-- The two-variable box lift clears the grid weight whenever `v ≤ addVal c`. -/
theorem le_WT_boxLift (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (c : O)
    (v a b j : ℕ) (hv : (v : ℕ∞) ≤ addVal O c) :
    ((gridWeight T v a b j : ℕ) : ℕ∞) ≤
      WT T (Polynomial.C (Polynomial.C c * Polynomial.X ^ a) * Polynomial.X ^ b *
        K_T T ^ j) := by
  refine le_trans ?_ (le_trans (add_le_add (le_WT_box_monomial T c a b)
    (le_WT_K_T_pow T hπ j)) (WT_mul T _ _))
  unfold gridWeight slotOffset wtCoeff
  simp only [nsmul_eq_mul]
  push_cast
  exact add_le_add (add_le_add (mul_le_mul_right hv _) le_rfl) le_rfl

/-- The box lift evaluates to the box monomial. -/
theorem eval_boxLift (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (c : O)
    (a b j : ℕ) :
    Polynomial.eval F.key (Polynomial.C (Polynomial.C c * Polynomial.X ^ a) *
        Polynomial.X ^ b * K_T T ^ j) =
      Polynomial.C c * Polynomial.X ^ a * F.key ^ b * composedKey T ^ j := by
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_X, eval_K_T T hπ]

/-! ## NODE C.131ad′ -/

/-- **NODE C.131ad′, the box monomial coefficient floor.**  Every scalar coefficient of
every canonical `F.key`-digit of the box monomial `C c · xᵃ · Φ′ᵇ · Φ₂ʲ` clears the grid
weight `gridWeight T v a b j` at its own grid position, for any certified valuation floor
`v ≤ addVal c` — value-blind and total in `a`, `b`, `j`. -/
theorem boxMonomial_coeff_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (c : O)
    (v a b j : ℕ) (hv : (v : ℕ∞) ≤ addVal O c) (s a' : ℕ) :
    ((gridWeight T v a b j : ℕ) : ℕ∞) ≤
      wtCoeff T ((dev F.key (Polynomial.C c * Polynomial.X ^ a * F.key ^ b *
        composedKey T ^ j) s).coeff a') a' s := by
  rw [← eval_boxLift T hπ c a b j]
  exact dev_coeff_floor T _ (le_WT_boxLift T hπ c v a b j hv) s a'

/-- **NODE C.131ad′, `dvAbove_boxMonomial`** (C.52's Step 0 carrier): all level-1 slots of
the box monomial `C c · xᵃ · Φ′ᵇ · Φ₂ʲ` sit at or above `gridWeight T v a b j` on the
`(u₂, e₂)` grid, for any certified valuation floor `v ≤ addVal c`. -/
theorem dvAbove_boxMonomial (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (c : O)
    (v a b j : ℕ) (hv : (v : ℕ∞) ≤ addVal O c) :
    DvAbove F (Polynomial.C c * Polynomial.X ^ a * F.key ^ b * composedKey T ^ j)
      T.u₂ T.e₂ ((gridWeight T v a b j : ℕ) : ℕ∞) := by
  refine dvAbove_of_forall_coeff_floor F _ T.u₂ T.e₂ _ T.he₂ fun b' a' => ?_
  have h := boxMonomial_coeff_floor T hπ c v a b j hv b' a'
  simp only [wtCoeff, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul] at h
  simp only [nsmul_eq_mul, Nat.cast_mul]
  exact h

end Uniformity.Density.Tower.C131ad

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131ad.le_WT_sum
#print axioms Uniformity.Density.Tower.C131ad.le_WT_C_mul_X_pow
#print axioms Uniformity.Density.Tower.C131ad.le_WT_C_C
#print axioms Uniformity.Density.Tower.C131ad.wtCoeff_add_shift
#print axioms Uniformity.Density.Tower.C131ad.wtCoeff_le_paid
#print axioms Uniformity.Density.Tower.C131ad.natDegree_X_pow_sub_key_le
#print axioms Uniformity.Density.Tower.C131ad.carryTerm
#print axioms Uniformity.Density.Tower.C131ad.eval_carryTerm
#print axioms Uniformity.Density.Tower.C131ad.le_WT_carryTerm
#print axioms Uniformity.Density.Tower.C131ad.carryTerm_coeff_natDegree_le
#print axioms Uniformity.Density.Tower.C131ad.carryStep
#print axioms Uniformity.Density.Tower.C131ad.eval_carryStep
#print axioms Uniformity.Density.Tower.C131ad.le_WT_carryStep
#print axioms Uniformity.Density.Tower.C131ad.carryStep_coeff_natDegree_lt
#print axioms Uniformity.Density.Tower.C131ad.dev_coeff_floor_of_WT_floor
#print axioms Uniformity.Density.Tower.C131ad.dev_coeff_floor
#print axioms Uniformity.Density.Tower.C131ad.le_WT_K_T_pow
#print axioms Uniformity.Density.Tower.C131ad.eval_K_T
#print axioms Uniformity.Density.Tower.C131ad.le_WT_box_monomial
#print axioms Uniformity.Density.Tower.C131ad.le_WT_boxLift
#print axioms Uniformity.Density.Tower.C131ad.eval_boxLift
#print axioms Uniformity.Density.Tower.C131ad.boxMonomial_coeff_floor
#print axioms Uniformity.Density.Tower.C131ad.dvAbove_boxMonomial

end AxCheck
