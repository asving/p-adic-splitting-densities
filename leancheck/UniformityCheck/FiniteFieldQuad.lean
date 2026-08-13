import Mathlib

/-!
# Counting anisotropic binary quadratic forms over a finite field

For a field `K`, a pair `p = (b₀, b₁) : K × K` encodes the monic quadratic
`X ^ 2 - b₁ * X + b₀`, equivalently the binary form `u ^ 2 - b₁ * u * v + b₀ * v ^ 2`.
The form is *anisotropic* (only the trivial zero) exactly when the monic quadratic has no
root in `K`; this is `AniK`.

The main result `two_mul_card_aniK` counts the anisotropic pairs over a finite field: with
`q = Nat.card K`, the non-anisotropic pairs are exactly the image of the injective map
`Sym2 K → K × K`, `s(r, s) ↦ (r * s, r + s)`, so there are `(q + 1).choose 2 = q * (q + 1) / 2`
of them and hence `q ^ 2 - q * (q + 1) / 2 = (q ^ 2 - q) / 2` anisotropic ones. The statement is
given in the subtraction-free form `2 * #Ani + q = q * q`.

Nothing here assumes `2 ≠ 0`; the proof works verbatim in characteristic two.
-/

namespace UniformityCheck

/-- The binary form `u² - b₁ u v + b₀ v²` (`p = (b₀, b₁)`) has only the trivial zero. -/
def AniK {K : Type*} [Field K] (p : K × K) : Prop := ∀ y : K, y ^ 2 - p.2 * y + p.1 ≠ 0

theorem aniK_iff {K : Type*} [Field K] (b₀ b₁ : K) :
    (∀ u v : K, u ^ 2 - b₁ * u * v + b₀ * v ^ 2 = 0 → u = 0 ∧ v = 0) ↔ AniK (b₀, b₁) := by
  simp only [AniK]
  constructor
  · intro h y hy
    exact one_ne_zero (h y 1 (by linear_combination hy)).2
  · intro h u v huv
    by_cases hv : v = 0
    · subst hv
      refine ⟨?_, rfl⟩
      have h2 : u ^ 2 = 0 := by linear_combination huv
      simpa using h2
    · exact absurd (by field_simp; linear_combination huv) (h (u / v))

section RootMap

variable (K : Type*) [Field K]

/-- The map sending an unordered pair of roots `s(r, s)` to the coefficient pair
`(r * s, r + s)` of the monic quadratic `X ^ 2 - (r + s) * X + r * s`. -/
def rootMap : Sym2 K → K × K :=
  Sym2.lift ⟨fun r s => (r * s, r + s), by intro a b; simp [mul_comm, add_comm]⟩

@[simp] theorem rootMap_mk (r s : K) : rootMap K s(r, s) = (r * s, r + s) := rfl

theorem rootMap_injective : Function.Injective (rootMap K) := by
  intro z w
  induction z using Sym2.ind with
  | _ r s =>
    induction w using Sym2.ind with
    | _ r' s' =>
      intro h
      rw [rootMap_mk, rootMap_mk, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have key : (r' - r) * (r' - s) = 0 := by linear_combination h1 - r' * h2
      rcases mul_eq_zero.mp key with hk | hk
      · have hr : r' = r := sub_eq_zero.mp hk
        have hs : s' = s := by linear_combination -h2 - hr
        rw [hr, hs]
      · have hr : r' = s := sub_eq_zero.mp hk
        have hs : s' = r := by linear_combination -h2 - hr
        rw [hr, hs]
        exact Sym2.eq_swap

/-- The image of `rootMap` is exactly the set of non-anisotropic pairs. -/
theorem exists_rootMap_iff (p : K × K) : (∃ z : Sym2 K, rootMap K z = p) ↔ ¬ AniK p := by
  obtain ⟨b₀, b₁⟩ := p
  simp only [AniK, ne_eq, not_forall, not_not]
  constructor
  · rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | _ r s =>
      rw [rootMap_mk, Prod.mk.injEq] at hz
      obtain ⟨h1, h2⟩ := hz
      exact ⟨r, by linear_combination r * h2 - h1⟩
  · rintro ⟨y, hy⟩
    refine ⟨s(y, b₁ - y), ?_⟩
    rw [rootMap_mk, Prod.mk.injEq]
    exact ⟨by linear_combination -hy, by ring⟩

end RootMap

theorem two_mul_choose_two (n : ℕ) : 2 * Nat.choose (n + 1) 2 = n * (n + 1) := by
  have hdvd : 2 ∣ (n + 1) * n := by
    rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' hdvd, Nat.mul_comm]

theorem card_not_aniK (K : Type*) [Field K] [Finite K] :
    Nat.card {p : K × K // ¬ AniK p} = Nat.choose (Nat.card K + 1) 2 := by
  have hbij : Function.Bijective
      (fun z : Sym2 K => (⟨rootMap K z, (exists_rootMap_iff K _).mp ⟨z, rfl⟩⟩ :
        {p : K × K // ¬ AniK p})) := by
    constructor
    · exact fun z w h => rootMap_injective K (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨z, hz⟩ := (exists_rootMap_iff K p).mpr hp
      exact ⟨z, Subtype.ext hz⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Sym2.natCard]

theorem two_mul_card_aniK (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // AniK p} + Nat.card K = Nat.card K * Nat.card K := by
  classical
  have hsplit : Nat.card {p : K × K // AniK p} + Nat.card {p : K × K // ¬ AniK p}
      = Nat.card K * Nat.card K := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (fun p : K × K => AniK p)),
      Nat.card_prod]
  have h2 : 2 * Nat.card {p : K × K // ¬ AniK p} = Nat.card K * (Nat.card K + 1) := by
    rw [card_not_aniK, two_mul_choose_two]
  have h3 : Nat.card K * (Nat.card K + 1) = Nat.card K * Nat.card K + Nat.card K := by ring
  omega

-- Numeric sanity check (brute-force `#eval` over `ZMod q`, run 2026-08-13):
-- the number of anisotropic pairs is 1, 3, 10 for q = 2, 3, 5 respectively,
-- matching `2 * 1 + 2 = 4`, `2 * 3 + 3 = 9`, `2 * 10 + 5 = 25`.

#print axioms UniformityCheck.two_mul_card_aniK

end UniformityCheck
