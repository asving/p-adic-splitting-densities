import Mathlib

/-!
# M2 — PadicValuation: coefficient valuations and the support `Finset`

For `f : ℤ_[p][X]` this module exposes the integer-valued coefficient valuations
`coeffVal f i := (f.coeff i).valuation : ℕ` (mathlib's normalized `PadicInt.valuation`,
with `v(0)=0`, `v(1)=0`, `v(p)=1`) and packages the *support* as a `Finset (ℕ × ℕ)` of lattice
points `(i, v_i)` for the coefficients `a_i ≠ 0`. These are the raw dots whose lower convex hull
is the Newton polygon built in M3. No geometry and no measure here.

This is blueprint module M2 ("Layer 0"). The only carried convention: coefficients equal to `0`
report valuation `0`, but are *excluded* from the support `Finset` (`def:val-support`); the "true"
value `+∞` is encoded by absence from the `Finset`, which is exactly what the lower Newton polygon
needs.
-/

namespace LeanUrat.OM.M2

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Coefficient valuation** (`def:coeff-val`).  For `f : ℤ_[p][X]` and `i : ℕ`,
`coeffVal f i := (f.coeff i).valuation : ℕ` using mathlib's normalized `PadicInt.valuation`.
Marked `noncomputable` because `PadicInt.valuation` is. -/
noncomputable def coeffVal (f : (PadicInt p)[X]) (i : ℕ) : ℕ := (f.coeff i).valuation

@[simp] theorem coeffVal_def (f : (PadicInt p)[X]) (i : ℕ) :
    coeffVal p f i = (f.coeff i).valuation := rfl

/-- A `PadicInt` unit has valuation `0`.  (`u * u⁻¹ = 1`, valuation is additive on nonzeros,
`valuation 1 = 0`, so `valuation u + valuation u⁻¹ = 0` in `ℕ`, forcing `valuation u = 0`.) -/
theorem valuation_eq_zero_of_isUnit {u : PadicInt p} (hu : IsUnit u) : u.valuation = 0 := by
  obtain ⟨v, rfl⟩ := hu
  have hv : (v : PadicInt p) ≠ 0 := v.ne_zero
  have hvi : ((v⁻¹ : (PadicInt p)ˣ) : PadicInt p) ≠ 0 := (v⁻¹).ne_zero
  have hmul : ((v : PadicInt p) * (v⁻¹ : (PadicInt p)ˣ)).valuation
      = (v : PadicInt p).valuation + ((v⁻¹ : (PadicInt p)ˣ) : PadicInt p).valuation :=
    PadicInt.valuation_mul hv hvi
  rw [Units.mul_inv, PadicInt.valuation_one] at hmul
  omega

/-- **Valuation arithmetic facts re-exported** (`lem:val-facts`).  Bundled as a conjunction so M3
imports a single node.  (i) `coeffVal f i = 0` whenever `f.coeff i` is a unit; (ii) multiplicativity
`v(xy) = v(x) + v(y)` on nonzero `x,y`; (iii) `v(p^k c) = k + v(c)` for nonzero `c`; (iv) the
ultrametric `min (v x) (v y) ≤ v (x + y)` for `x + y ≠ 0`. -/
theorem coeffVal_facts (f : (PadicInt p)[X]) :
    (∀ i, IsUnit (f.coeff i) → coeffVal p f i = 0) ∧
    (∀ x y : PadicInt p, x ≠ 0 → y ≠ 0 → (x * y).valuation = x.valuation + y.valuation) ∧
    (∀ (k : ℕ) (c : PadicInt p), c ≠ 0 →
      ((p : PadicInt p) ^ k * c).valuation = k + c.valuation) ∧
    (∀ x y : PadicInt p, x + y ≠ 0 → min x.valuation y.valuation ≤ (x + y).valuation) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [coeffVal_def]
    exact valuation_eq_zero_of_isUnit p hi
  · intro x y hx hy
    exact PadicInt.valuation_mul hx hy
  · intro k c hc
    exact PadicInt.valuation_p_pow_mul k c hc
  · intro x y hxy
    exact PadicInt.le_valuation_add hxy

/-- The valuation of the leading coefficient of a monic `f` is `0` (top coefficient is `1`). -/
theorem coeffVal_natDegree_of_monic {f : (PadicInt p)[X]} (hf : f.Monic) :
    coeffVal p f f.natDegree = 0 := by
  rw [coeffVal_def, ← leadingCoeff, hf.leadingCoeff, PadicInt.valuation_one]

/-- **The valuation support `Finset`** (`def:val-support`).  For `f : ℤ_[p][X]`,
`valSupport f := (f.support).image (fun i => (i, coeffVal f i)) : Finset (ℕ × ℕ)`.
The points are exactly the `(i, v_i)` with `a_i ≠ 0`.  Marked `noncomputable` (via `coeffVal`). -/
noncomputable def valSupport (f : (PadicInt p)[X]) : Finset (ℕ × ℕ) :=
  f.support.image (fun i => (i, coeffVal p f i))

/-- **Support membership / nonemptiness for monic `f`** (`lem:val-support-facts`).
(i) `(i, v) ∈ valSupport f ↔ f.coeff i ≠ 0 ∧ v = coeffVal f i`;
(ii) if `f` is monic of `natDegree n` then `(n, 0) ∈ valSupport f`, so the support is nonempty and
pins the right endpoint of the polygon at height `0`. -/
theorem valSupport_facts (f : (PadicInt p)[X]) :
    (∀ i v, (i, v) ∈ valSupport p f ↔ f.coeff i ≠ 0 ∧ v = coeffVal p f i) ∧
    (f.Monic → (f.natDegree, 0) ∈ valSupport p f) := by
  refine ⟨?_, ?_⟩
  · intro i v
    simp only [valSupport, Finset.mem_image, mem_support_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨j, hj, rfl, rfl⟩
      exact ⟨hj, rfl⟩
    · rintro ⟨hi, rfl⟩
      exact ⟨i, hi, rfl, rfl⟩
  · intro hf
    have hne : f.coeff f.natDegree ≠ 0 := by
      rw [← leadingCoeff, hf.leadingCoeff]; exact one_ne_zero
    have : (f.natDegree, coeffVal p f f.natDegree) ∈ valSupport p f := by
      simp only [valSupport, Finset.mem_image, mem_support_iff]
      exact ⟨f.natDegree, hne, rfl⟩
    rwa [coeffVal_natDegree_of_monic p hf] at this

/-- `valSupport f` is nonempty for monic `f`. -/
theorem valSupport_nonempty_of_monic {f : (PadicInt p)[X]} (hf : f.Monic) :
    (valSupport p f).Nonempty :=
  ⟨_, (valSupport_facts p f).2 hf⟩

end LeanUrat.OM.M2
