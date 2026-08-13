import Mathlib
import UniformityCheck.FiniteFieldQuad

/-!
# Counting monic cubics over a finite field

A vector `c : Fin 3 → K` encodes the monic cubic `X ^ 3 + c 2 * X ^ 2 + c 1 * X + c 0`, so the
monic cubics over a finite field `K` with `q = Nat.card K` elements form a set of size `q ^ 3`.
This file counts two of the four factorisation shapes, both in subtraction-free form.

* `three_mul_card_noRootCubic`: `3 * #{c | NoRootCubic c} + q = q ^ 3`, i.e. there are
  `(q ^ 3 - q) / 3` monic cubics with no root in `K` — and over a field a cubic is irreducible
  exactly when it has no root, so this is the count of monic irreducible cubics.

  The proof is inclusion–exclusion over the root locus
  (`Finset.inclusion_exclusion_card_inf_compl`): with `cubicRootSet K r` the set of `c` vanishing
  at `r`, the intersection `⋂_{r ∈ t} cubicRootSet K r` has exactly `q ^ (3 - #t)` elements when
  `#t ≤ 3` and is empty when `#t ≥ 4` (`card_inf_cubicRootSet`). The three nonempty cases are
  explicit bijections onto `K × K`, `K` and a singleton, obtained by solving for the lower
  coefficients; emptiness for `#t ≥ 4` is `cubic_not_four_roots`. Grouping the alternating sum by
  `#t` (`Finset.sum_powerset_apply_card`) leaves
  `q ^ 3 - q * q ^ 2 + (q.choose 2) * q - q.choose 3 = (q ^ 3 - q) / 3`, and the ℕ-level
  bookkeeping is `choose_cubic_identity`.

* `two_mul_card_linAni`: `2 * #{c | LinAni c} + q ^ 2 = q ^ 3`, i.e. there are `q ^ 2 * (q - 1) / 2`
  monic cubics of the shape (linear) · (irreducible quadratic). The map
  `(ρ, p) ↦ linAniCoeff ρ p` from `K × {p // AniK p}` is a bijection onto this family
  (`linAniCoeff_inj`: the linear factor is the unique root, because the quadratic factor has none),
  so the count is `q` times the count of anisotropic pairs supplied by
  `UniformityCheck.two_mul_card_aniK` in `UniformityCheck.FiniteFieldQuad`.

Nothing here assumes anything about the characteristic of `K`: every step is a polynomial identity
valid over an arbitrary field, so the counts hold verbatim in characteristics 2 and 3. In
particular no argument divides by `2`, `3` or `6` — the statements are given in the
subtraction-free, division-free forms above precisely to keep that uniformity visible.
-/

namespace UniformityCheck

open Finset

/-- The monic cubic `X ^ 3 + c 2 * X ^ 2 + c 1 * X + c 0` has no root in `K`. -/
def NoRootCubic {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∀ y : K, y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 ≠ 0

section Algebra

variable {K : Type*} [Field K] {c : Fin 3 → K}

theorem cubic_two_root_rel {y z : K} (hyz : y ≠ z)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0) :
    y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1 = 0 := by
  have h : (y - z) * (y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1) = 0 := by
    linear_combination hy - hz
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hyz
  · exact h

theorem cubic_coeff_two {y z w : K} (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0) :
    c 2 = -(y + z + w) := by
  have hA := cubic_two_root_rel hyz hy hz
  have hB := cubic_two_root_rel hyw hy hw
  have h : (z - w) * (y + z + w + c 2) = 0 := by linear_combination hA - hB
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hzw
  · linear_combination h

theorem cubic_coeff_one {y z w : K} (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0) :
    c 1 = y * z + y * w + z * w := by
  have hA := cubic_two_root_rel hyz hy hz
  have h2 := cubic_coeff_two hyz hyw hzw hy hz hw
  linear_combination hA - (y + z) * h2

theorem cubic_coeff_zero {y z w : K} (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0) :
    c 0 = -(y * z * w) := by
  have h2 := cubic_coeff_two hyz hyw hzw hy hz hw
  have h1 := cubic_coeff_one hyz hyw hzw hy hz hw
  linear_combination hy - y ^ 2 * h2 - y * h1

theorem cubic_not_four_roots {y z w v : K} (hyz : y ≠ z) (hyw : y ≠ w) (hyv : y ≠ v)
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0)
    (hv : v ^ 3 + c 2 * v ^ 2 + c 1 * v + c 0 = 0) : False := by
  have h1 := cubic_coeff_two hyz hyw hzw hy hz hw
  have h2 := cubic_coeff_two hyz hyv hzv hy hz hv
  exact hwv (by linear_combination h1 - h2)

end Algebra

/-! ### The arithmetic identity -/

theorem choose_cubic_identity (n : ℕ) :
    3 * n.choose 2 * n + n = n ^ 3 + 3 * n.choose 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ]; simp
    have h3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
      rw [Nat.choose_succ_succ]
    rw [h2, h3]
    zify at ih ⊢
    linear_combination ih

/-! ### The counting -/

section Count

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- The set of monic cubics (as coefficient vectors) vanishing at `r`. -/
def cubicRootSet (r : K) : Finset (Fin 3 → K) :=
  univ.filter fun c : Fin 3 → K => r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 = 0

variable {K}

@[simp] theorem mem_cubicRootSet {r : K} {c : Fin 3 → K} :
    c ∈ cubicRootSet K r ↔ r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 = 0 := by
  simp [cubicRootSet]

theorem mem_inf_cubicRootSet {t : Finset K} {c : Fin 3 → K} :
    c ∈ t.inf (cubicRootSet K) ↔ ∀ r ∈ t, r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 = 0 := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih => simp [Finset.inf_eq_inter, ih]

theorem mem_inf_compl_cubicRootSet {t : Finset K} {c : Fin 3 → K} :
    c ∈ t.inf (fun r => (cubicRootSet K r)ᶜ) ↔
      ∀ r ∈ t, r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 ≠ 0 := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih => simp [Finset.inf_eq_inter, ih]

theorem card_cubicRootSet (y : K) : #(cubicRootSet K y) = Fintype.card K ^ 2 := by
  have h : #(cubicRootSet K y) = #(univ : Finset (K × K)) := by
    refine Finset.card_nbij' (fun c => (c 1, c 2))
      (fun u => ![-(y ^ 3 + u.2 * y ^ 2 + u.1 * y), u.1, u.2]) (by simp [Set.MapsTo]) ?_ ?_ ?_
    · intro u _
      simp only [Finset.mem_coe, mem_cubicRootSet]
      simp
    · intro c hc
      simp only [Finset.mem_coe, mem_cubicRootSet] at hc
      funext i
      fin_cases i <;> simp
      linear_combination -hc
    · intro u _
      simp
  rw [h]
  simp [Fintype.card_prod, sq]

theorem card_cubicRootSet_pair {y z : K} (hyz : y ≠ z) :
    #(cubicRootSet K y ⊓ cubicRootSet K z) = Fintype.card K := by
  have h : #(cubicRootSet K y ⊓ cubicRootSet K z) = #(univ : Finset K) := by
    refine Finset.card_nbij' (fun c => c 2)
      (fun v => ![y * z * (y + z + v), -(y ^ 2 + y * z + z ^ 2 + v * (y + z)), v])
      (by simp [Set.MapsTo]) ?_ ?_ ?_
    · intro v _
      simp only [Finset.mem_coe, Finset.inf_eq_inter,
        Finset.mem_inter, mem_cubicRootSet]
      constructor <;> · simp; ring
    · intro c hc
      simp only [Finset.mem_coe, Finset.inf_eq_inter, Finset.mem_inter,
        mem_cubicRootSet] at hc
      obtain ⟨hy, hz⟩ := hc
      have hA := cubic_two_root_rel hyz hy hz
      funext i
      fin_cases i <;> simp
      · linear_combination -hy + y * hA
      · linear_combination -hA
    · intro v _
      simp
  rw [h]
  simp

theorem card_inf_cubicRootSet (t : Finset K) :
    #(t.inf (cubicRootSet K)) = if #t ≤ 3 then Fintype.card K ^ (3 - #t) else 0 := by
  by_cases h : #t ≤ 3
  · rw [if_pos h]
    obtain hc | hc | hc | hc : #t = 0 ∨ #t = 1 ∨ #t = 2 ∨ #t = 3 := by omega
    · obtain rfl := Finset.card_eq_zero.mp hc
      simp
    · obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hc
      rw [Finset.inf_singleton, card_cubicRootSet]
      simp
    · obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hc
      rw [Finset.inf_insert, Finset.inf_singleton, card_cubicRootSet_pair hyz]
      rw [Finset.card_insert_of_notMem (by simpa using hyz)]
      simp
    · rw [hc]
      obtain ⟨y, z, w, hyz, hyw, hzw, rfl⟩ := Finset.card_eq_three.mp hc
      rw [Nat.sub_self, pow_zero, Finset.card_eq_one]
      refine ⟨![-(y * z * w), y * z + y * w + z * w, -(y + z + w)], ?_⟩
      ext c
      simp only [mem_inf_cubicRootSet, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hmem
        have hy := hmem y (by simp)
        have hz := hmem z (by simp)
        have hw := hmem w (by simp)
        funext i
        fin_cases i <;> simp
        · exact cubic_coeff_zero hyz hyw hzw hy hz hw
        · exact cubic_coeff_one hyz hyw hzw hy hz hw
        · linear_combination cubic_coeff_two hyz hyw hzw hy hz hw
      · rintro rfl r hr
        rcases hr with rfl | rfl | rfl <;> · simp; ring
  · rw [if_neg h]
    obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (show 4 ≤ #t by omega)
    obtain ⟨y, z, w, v, hyz, hyw, hyv, hzw, hzv, hwv, rfl⟩ := Finset.card_eq_four.mp hcard
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro c hmem
    rw [mem_inf_cubicRootSet] at hmem
    exact cubic_not_four_roots hyz hyw hyv hzw hzv hwv
      (hmem y (hu (by simp))) (hmem z (hu (by simp)))
      (hmem w (hu (by simp))) (hmem v (hu (by simp)))

end Count

theorem three_mul_card_noRootCubic (K : Type*) [Field K] [Finite K] :
    3 * Nat.card {c : Fin 3 → K // NoRootCubic c} + Nat.card K = Nat.card K ^ 3 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set q : ℕ := Fintype.card K with hqdef
  set F : ℕ → ℤ := fun k => (-1 : ℤ) ^ k * (if k ≤ 3 then (q : ℤ) ^ (3 - k) else 0) with hF
  -- The set of root-free cubics as an intersection of complements.
  have hN : Nat.card {c : Fin 3 → K // NoRootCubic c}
      = #((univ : Finset K).inf fun r => (cubicRootSet K r)ᶜ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext c
    simp [NoRootCubic, mem_inf_compl_cubicRootSet]
  -- Inclusion–exclusion over the root locus.
  have hIE := Finset.inclusion_exclusion_card_inf_compl (univ : Finset K) (cubicRootSet K)
  have hsum : ∀ t : Finset K,
      (-1 : ℤ) ^ #t * (#(t.inf (cubicRootSet K)) : ℤ) = F #t := by
    intro t
    rw [card_inf_cubicRootSet, hF]
    by_cases ht : #t ≤ 3 <;> simp [ht, hqdef]
  rw [Finset.sum_congr rfl (fun t _ => hsum t), Finset.sum_powerset_apply_card,
    Finset.card_univ, ← hqdef] at hIE
  -- Only the four terms `k ≤ 3` survive.
  have hA : ∑ m ∈ range (q + 1), q.choose m • F m
      = ∑ m ∈ range (max (q + 1) 4), q.choose m • F m := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    intro x _ hx
    rw [Finset.mem_range] at hx
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hB : ∑ m ∈ range 4, q.choose m • F m
      = ∑ m ∈ range (max (q + 1) 4), q.choose m • F m := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    intro x _ hx
    rw [Finset.mem_range] at hx
    simp [hF, show ¬ x ≤ 3 by omega]
  have hval : ∑ m ∈ range 4, q.choose m • F m = (q.choose 2 : ℤ) * q - (q.choose 3 : ℤ) := by
    simp [Finset.sum_range_succ, hF]
    ring
  rw [hA, ← hB, hval] at hIE
  -- Descend to `ℕ`.
  rw [hN, Nat.card_eq_fintype_card, ← hqdef]
  have hid := choose_cubic_identity q
  zify at hid ⊢
  linear_combination 3 * hIE + hid

/-- The coefficient vector of `(X - ρ) * (X ^ 2 - b₁ X + b₀)`, i.e.
`X ^ 3 - (b₁ + ρ) X ^ 2 + (b₀ + ρ b₁) X - ρ b₀`. -/
def linAniCoeff {K : Type*} [Field K] (ρ : K) (p : K × K) : Fin 3 → K :=
  ![-(ρ * p.1), p.1 + ρ * p.2, -(p.2 + ρ)]

/-- The level-0 family "linear factor times irreducible quadratic". -/
def LinAni {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ (ρ : K) (p : K × K), AniK p ∧ c = linAniCoeff ρ p

theorem linAniCoeff_inj {K : Type*} [Field K] {ρ ρ' : K} {p p' : K × K} (hp : AniK p)
    (h : linAniCoeff ρ p = linAniCoeff ρ' p') : ρ = ρ' ∧ p = p' := by
  have e0 : ρ * p.1 = ρ' * p'.1 := by
    have h0 := congrFun h 0
    simpa [linAniCoeff] using h0
  have e1 : p.1 + ρ * p.2 = p'.1 + ρ' * p'.2 := by
    have h1 := congrFun h 1
    simpa [linAniCoeff] using h1
  have e2 : p.2 + ρ = p'.2 + ρ' := by
    have h2 := congrFun h 2
    simp [linAniCoeff] at h2
    linear_combination -h2
  have hroot : (ρ' - ρ) * (ρ' ^ 2 - p.2 * ρ' + p.1) = 0 := by
    linear_combination (-(ρ' ^ 2)) * e2 + ρ' * e1 - e0
  have hρ : ρ = ρ' := by
    rcases mul_eq_zero.mp hroot with hk | hk
    · exact (sub_eq_zero.mp hk).symm
    · exact absurd hk (hp ρ')
  subst hρ
  refine ⟨rfl, Prod.ext ?_ ?_⟩
  · have h22 : p.2 = p'.2 := by linear_combination e2
    linear_combination e1 - ρ * h22
  · linear_combination e2

theorem two_mul_card_linAni (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {c : Fin 3 → K // LinAni c} + Nat.card K ^ 2 = Nat.card K ^ 3 := by
  have hbij : Function.Bijective
      (fun x : K × {p : K × K // AniK p} =>
        (⟨linAniCoeff x.1 x.2.1, ⟨x.1, x.2.1, x.2.2, rfl⟩⟩ : {c : Fin 3 → K // LinAni c})) := by
    constructor
    · rintro ⟨ρ, ⟨p, hp⟩⟩ ⟨ρ', ⟨p', hp'⟩⟩ hx
      simp only [Subtype.mk.injEq] at hx
      obtain ⟨h1, h2⟩ := linAniCoeff_inj hp hx
      simp [h1, h2]
    · rintro ⟨c, ρ, p, hp, rfl⟩
      exact ⟨(ρ, ⟨p, hp⟩), rfl⟩
  have hcard : Nat.card {c : Fin 3 → K // LinAni c}
      = Nat.card K * Nat.card {p : K × K // AniK p} := by
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod]
  rw [hcard]
  calc 2 * (Nat.card K * Nat.card {p : K × K // AniK p}) + Nat.card K ^ 2
      = Nat.card K * (2 * Nat.card {p : K × K // AniK p} + Nat.card K) := by ring
    _ = Nat.card K * (Nat.card K * Nat.card K) := by rw [two_mul_card_aniK]
    _ = Nat.card K ^ 3 := by ring

-- Numeric sanity checks (brute-force `#eval` over `ZMod q`, run 2026-08-13):
-- `#{c | NoRootCubic c}` is `2, 8, 40` for `q = 2, 3, 5`, matching
--   `3 * 2 + 2 = 8 = 2 ^ 3`, `3 * 8 + 3 = 27 = 3 ^ 3`, `3 * 40 + 5 = 125 = 5 ^ 3`;
-- `#{c | LinAni c}` is `2, 9, 50` for `q = 2, 3, 5`, matching
--   `2 * 2 + 2 ^ 2 = 8`, `2 * 9 + 3 ^ 2 = 27`, `2 * 50 + 5 ^ 2 = 125`.

#print axioms UniformityCheck.three_mul_card_noRootCubic
#print axioms UniformityCheck.two_mul_card_linAni

end UniformityCheck
