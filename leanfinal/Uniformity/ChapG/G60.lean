/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G38

/-!
# Uniformity.ChapG.G60 — the residue-field cubic census, subtraction-free

**Chapter G, NODE G.60** (`blueprint/CHAP-G_base_cases_menus.md` §8). *SPLIT MANDATED by the
blueprint into G.60a/G.60b/G.60c* (one per count); landed here as one node file, three public
theorems, following the established convention of this fleet (private helpers carry the split,
the node file carries the SIGNATURE verbatim — cf. `G67.lean`, `G69.lean`).

Three subtraction-free residue-field counts:
`3·#{no root} + q = q³`, `2·#{linear × irreducible quadratic} + q² = q³`,
`6·#{three distinct roots} + 3q² = q³ + 2q`.

DEPENDS: G.38 (`two_mul_card_aniForm`) · mathlib `Finset.inclusion_exclusion_card_inf_compl`,
`Finset.sum_powerset_apply_card`, `Nat.choose`.

**RE-DERIVATION TARGET** (blueprint H-9): `leancheck`'s `UniformityCheck.CubicCount` /
`UniformityCheck.SplitCount` land the same three counts verbatim, against `AniK` in place of
this file's `AniForm` (`G.38`'s counterpart). The proofs below are re-derived from scratch
against `leanfinal`'s own API, per the repo's non-import policy (`leancheck` imports
`leanfinal`, never the reverse) — only the mathlib lemma names are shared, and both projects
pin the same mathlib commit.

**TEETH.** `HM3-MENU` / `HM3-AGG` → executable regression.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

open Finset

/-! ## 1. `NoRootCubic` — the irreducible cubics -/

/-- The monic cubic `X³ + c 2 X² + c 1 X + c 0` has no root in `K`. -/
def NoRootCubic {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∀ y : K, y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 ≠ 0

section Algebra

variable {K : Type*} [Field K] {c : Fin 3 → K}

private theorem cubic_two_root_rel {y z : K} (hyz : y ≠ z)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0) :
    y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1 = 0 := by
  have h : (y - z) * (y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1) = 0 := by
    linear_combination hy - hz
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hyz
  · exact h

private theorem cubic_coeff_two {y z w : K} (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
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

private theorem cubic_coeff_one {y z w : K} (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0) :
    c 1 = y * z + y * w + z * w := by
  have hA := cubic_two_root_rel hyz hy hz
  have h2 := cubic_coeff_two hyz hyw hzw hy hz hw
  linear_combination hA - (y + z) * h2

private theorem cubic_coeff_zero {y z w : K} (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0) :
    c 0 = -(y * z * w) := by
  have h2 := cubic_coeff_two hyz hyw hzw hy hz hw
  have h1 := cubic_coeff_one hyz hyw hzw hy hz hw
  linear_combination hy - y ^ 2 * h2 - y * h1

private theorem cubic_not_four_roots {y z w v : K} (hyz : y ≠ z) (hyw : y ≠ w) (hyv : y ≠ v)
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0)
    (hv : v ^ 3 + c 2 * v ^ 2 + c 1 * v + c 0 = 0) : False := by
  have h1 := cubic_coeff_two hyz hyw hzw hy hz hw
  have h2 := cubic_coeff_two hyz hyv hzv hy hz hv
  exact hwv (by linear_combination h1 - h2)

end Algebra

private theorem choose_cubic_identity (n : ℕ) :
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

section Count

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- The set of monic cubics (as coefficient vectors) vanishing at `r`. -/
private def cubicRootSet (r : K) : Finset (Fin 3 → K) :=
  univ.filter fun c : Fin 3 → K => r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 = 0

variable {K}

@[simp] private theorem mem_cubicRootSet {r : K} {c : Fin 3 → K} :
    c ∈ cubicRootSet K r ↔ r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 = 0 := by
  simp [cubicRootSet]

private theorem mem_inf_cubicRootSet {t : Finset K} {c : Fin 3 → K} :
    c ∈ t.inf (cubicRootSet K) ↔ ∀ r ∈ t, r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 = 0 := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih => simp [Finset.inf_eq_inter, ih]

private theorem mem_inf_compl_cubicRootSet {t : Finset K} {c : Fin 3 → K} :
    c ∈ t.inf (fun r => (cubicRootSet K r)ᶜ) ↔
      ∀ r ∈ t, r ^ 3 + c 2 * r ^ 2 + c 1 * r + c 0 ≠ 0 := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih => simp [Finset.inf_eq_inter, ih]

private theorem card_cubicRootSet (y : K) : #(cubicRootSet K y) = Fintype.card K ^ 2 := by
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

private theorem card_cubicRootSet_pair {y z : K} (hyz : y ≠ z) :
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

private theorem card_inf_cubicRootSet (t : Finset K) :
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

/-- **G.60a.** `3·#{no root} + q = q³`, subtraction-free — the count of monic irreducible
cubics over a finite field. -/
theorem three_mul_card_noRootCubic (K : Type*) [Field K] [Finite K] :
    3 * Nat.card {c : Fin 3 → K // NoRootCubic c} + Nat.card K = Nat.card K ^ 3 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set q : ℕ := Fintype.card K with hqdef
  set F : ℕ → ℤ := fun k => (-1 : ℤ) ^ k * (if k ≤ 3 then (q : ℤ) ^ (3 - k) else 0) with hF
  have hN : Nat.card {c : Fin 3 → K // NoRootCubic c}
      = #((univ : Finset K).inf fun r => (cubicRootSet K r)ᶜ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext c
    simp [NoRootCubic, mem_inf_compl_cubicRootSet]
  have hIE := Finset.inclusion_exclusion_card_inf_compl (univ : Finset K) (cubicRootSet K)
  have hsum : ∀ t : Finset K,
      (-1 : ℤ) ^ #t * (#(t.inf (cubicRootSet K)) : ℤ) = F #t := by
    intro t
    rw [card_inf_cubicRootSet, hF]
    by_cases ht : #t ≤ 3 <;> simp [ht, hqdef]
  rw [Finset.sum_congr rfl (fun t _ => hsum t), Finset.sum_powerset_apply_card,
    Finset.card_univ, ← hqdef] at hIE
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
  rw [hN, Nat.card_eq_fintype_card, ← hqdef]
  have hid := choose_cubic_identity q
  zify at hid ⊢
  linear_combination 3 * hIE + hid

/-! ## 2. `LinAni` — linear times inert quadratic -/

/-- The coefficient vector of `(X - ρ) * (X² - p.2 X + p.1)`, matching the blueprint's inline
formula `![-(ρ p.1), p.1 + ρ p.2, -(p.2 + ρ)]` verbatim. -/
private def linAniCoeff {K : Type*} [Field K] (ρ : K) (p : K × K) : Fin 3 → K :=
  ![-(ρ * p.1), p.1 + ρ * p.2, -(p.2 + ρ)]

/-- The level-0 family "linear factor times irreducible quadratic". -/
def LinAni {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ (ρ : K) (p : K × K), AniForm p ∧ c = linAniCoeff ρ p

private theorem linAniCoeff_inj {K : Type*} [Field K] {ρ ρ' : K} {p p' : K × K} (hp : AniForm p)
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

/-- **G.60b.** `2·#{linear × irreducible quadratic} + q² = q³`, subtraction-free. -/
theorem two_mul_card_linAni (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {c : Fin 3 → K // LinAni c} + Nat.card K ^ 2 = Nat.card K ^ 3 := by
  have hbij : Function.Bijective
      (fun x : K × {p : K × K // AniForm p} =>
        (⟨linAniCoeff x.1 x.2.1, ⟨x.1, x.2.1, x.2.2, rfl⟩⟩ : {c : Fin 3 → K // LinAni c})) := by
    constructor
    · rintro ⟨ρ, ⟨p, hp⟩⟩ ⟨ρ', ⟨p', hp'⟩⟩ hx
      simp only [Subtype.mk.injEq] at hx
      obtain ⟨h1, h2⟩ := linAniCoeff_inj hp hx
      simp [h1, h2]
    · rintro ⟨c, ρ, p, hp, rfl⟩
      exact ⟨(ρ, ⟨p, hp⟩), rfl⟩
  have hcard : Nat.card {c : Fin 3 → K // LinAni c}
      = Nat.card K * Nat.card {p : K × K // AniForm p} := by
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod]
  rw [hcard]
  calc 2 * (Nat.card K * Nat.card {p : K × K // AniForm p}) + Nat.card K ^ 2
      = Nat.card K * (2 * Nat.card {p : K × K // AniForm p} + Nat.card K) := by ring
    _ = Nat.card K * (Nat.card K * Nat.card K) := by rw [two_mul_card_aniForm]
    _ = Nat.card K ^ 3 := by ring

/-! ## 3. `Split3` — three distinct linear factors -/

/-- The coefficient vector of `(X - r)(X - s)(X - t)`, matching the blueprint's inline formula
`![-(r s t), rs+rt+st, -(r+s+t)]` verbatim. -/
private def split3Coeff {K : Type*} [Field K] (r s t : K) : Fin 3 → K :=
  ![-(r * s * t), r * s + r * t + s * t, -(r + s + t)]

/-- The level-0 family "three DISTINCT linear factors". -/
def Split3 {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ r s t : K, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ c = split3Coeff r s t

private theorem eval_split3Coeff {K : Type*} [Field K] (r s t y : K) :
    y ^ 3 + split3Coeff r s t 2 * y ^ 2 + split3Coeff r s t 1 * y + split3Coeff r s t 0
      = (y - r) * (y - s) * (y - t) := by
  simp only [split3Coeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

private theorem split3_two_root_rel {K : Type*} [Field K] {c : Fin 3 → K} {y z : K} (hyz : y ≠ z)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0) :
    y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1 = 0 := by
  have h : (y - z) * (y ^ 2 + y * z + z ^ 2 + c 2 * (y + z) + c 1) = 0 := by
    linear_combination hy - hz
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hyz
  · exact h

private theorem eq_split3Coeff_of_roots {K : Type*} [Field K] {c : Fin 3 → K} {y z w : K}
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hy : y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0)
    (hz : z ^ 3 + c 2 * z ^ 2 + c 1 * z + c 0 = 0)
    (hw : w ^ 3 + c 2 * w ^ 2 + c 1 * w + c 0 = 0) :
    c = split3Coeff y z w := by
  have hA := split3_two_root_rel hyz hy hz
  have hB := split3_two_root_rel hyw hy hw
  have h2 : c 2 = -(y + z + w) := by
    have h : (z - w) * (y + z + w + c 2) = 0 := by linear_combination hA - hB
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hzw
    · linear_combination h
  have h1 : c 1 = y * z + y * w + z * w := by linear_combination hA - (y + z) * h2
  have h0 : c 0 = -(y * z * w) := by linear_combination hy - y ^ 2 * h2 - y * h1
  funext i
  fin_cases i
  · simpa [split3Coeff] using h0
  · simpa [split3Coeff] using h1
  · simpa [split3Coeff] using h2

section SplitCount

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The set of roots in `K` of the monic cubic `X³ + c 2 X² + c 1 X + c 0`. -/
private def cubicRoots (c : Fin 3 → K) : Finset K :=
  {y | y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0}

@[simp] private theorem mem_cubicRoots {c : Fin 3 → K} {y : K} :
    y ∈ cubicRoots c ↔ y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 = 0 := by
  simp [cubicRoots]

private theorem cubicRoots_split3Coeff (r s t : K) : cubicRoots (split3Coeff r s t) = {r, s, t} := by
  ext y
  simp only [mem_cubicRoots, eval_split3Coeff, mul_eq_zero, sub_eq_zero, Finset.mem_insert,
    Finset.mem_singleton, or_assoc]

private theorem card_split3 : Nat.card {c : Fin 3 → K // Split3 c} = (Fintype.card K).choose 3 := by
  have hmaps : ∀ x : {c : Fin 3 → K // Split3 c}, #(cubicRoots x.1) = 3 := by
    rintro ⟨c, r, s, t, hrs, hrt, hst, rfl⟩
    rw [cubicRoots_split3Coeff]
    exact Finset.card_eq_three.mpr ⟨r, s, t, hrs, hrt, hst, rfl⟩
  have hbij : Function.Bijective (fun x : {c : Fin 3 → K // Split3 c} =>
      (⟨cubicRoots x.1, hmaps x⟩ : {u : Finset K // #u = 3})) := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ hx
      simp only [Subtype.mk.injEq] at hx
      obtain ⟨r, s, t, hrs, hrt, hst, rfl⟩ := hc
      rw [cubicRoots_split3Coeff] at hx
      have hr : r ∈ cubicRoots c' := by rw [← hx]; simp
      have hs : s ∈ cubicRoots c' := by rw [← hx]; simp
      have ht : t ∈ cubicRoots c' := by rw [← hx]; simp
      rw [mem_cubicRoots] at hr hs ht
      exact Subtype.ext (eq_split3Coeff_of_roots hrs hrt hst hr hs ht).symm
    · rintro ⟨u, hu⟩
      obtain ⟨r, s, t, hrs, hrt, hst, rfl⟩ := Finset.card_eq_three.mp hu
      exact ⟨⟨split3Coeff r s t, ⟨r, s, t, hrs, hrt, hst, rfl⟩⟩,
        Subtype.ext (cubicRoots_split3Coeff r s t)⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_finset_len]

end SplitCount

private theorem two_mul_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (n + 1).choose 2 = n + n.choose 2 := by rw [Nat.choose_succ_succ]; simp
    rw [h2]
    zify at ih ⊢
    linear_combination ih

private theorem six_mul_choose_three (n : ℕ) : 6 * n.choose 3 + 3 * n ^ 2 = n ^ 3 + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by rw [Nat.choose_succ_succ]
    have h2 := two_mul_choose_two_add n
    rw [h3]
    zify at ih h2 ⊢
    linear_combination ih + 3 * h2

/-- **G.60c.** `6·#{three distinct roots} + 3q² = q³ + 2q`, subtraction-free. -/
theorem six_mul_card_split3 (K : Type*) [Field K] [Finite K] :
    6 * Nat.card {c : Fin 3 → K // Split3 c} + 3 * Nat.card K ^ 2
      = Nat.card K ^ 3 + 2 * Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [card_split3, Nat.card_eq_fintype_card]
  exact six_mul_choose_three _

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.three_mul_card_noRootCubic
#print axioms Uniformity.Density.Menu.two_mul_card_linAni
#print axioms Uniformity.Density.Menu.six_mul_card_split3

end AxCheck
