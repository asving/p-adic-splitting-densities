/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.Density.TypeOf — the splitting type of a monic polynomial, engine-free

For a monic `f ∈ O[X]` over a complete DVR `O` this file defines

  `typeOf f : FactorizationType`  =  the multiset of `(e, f)` pairs of the monic irreducible
  factors of `f`, **with multiplicity**,

using **only** unique factorization in `O[X]` and the norm form of the valuation. It imports
nothing from any Okutsu–Montes classifier: this independence is exactly what will give the main
theorem its content (the classifier must be proved to compute *this*, it does not define it).

## The two layers

1. **`monicFactors f`** — the multiset of monic irreducible factors of a monic `f`.
   `O[X]` is a UFD (`O` is a PID); the factorization into *monic* irreducibles exists
   (`monicFactorization_exists`) and is **unique as a multiset**
   (`monicFactorization_unique`), because two monic associates are equal.

2. **`inertiaDegOf g` / `ramIndexOf g`** — for a monic irreducible `g` of degree `d`, put
   `L = K[x]/(g)` (`K = Frac O`) and `A = O[x]/(g) = AdjoinRoot g`, a free `O`-module of rank
   `d`. Since `O` is **complete**, the valuation `v` of `O` has a *unique* extension `w` to `L`,
   and it is given by the norm form `w(x) = v(N_{L/K}(x)) / d`. Writing `e`, `f` for the
   ramification index and residue degree of `L/K` (so `e * f = d`), the value group of `w` is
   `(1/e)·ℤ`, hence

       { v(N_{L/K}(x)) : x ∈ L^×} = d · w(L^×) = (d/e) · ℤ = f · ℤ,

   and the values coming from the *integral* elements `x ∈ A \ {0}` are exactly `f · ℕ`.
   Therefore

       f  =  the least strictly positive `v(N(x))`, `x ∈ A \ {0}`,        (`inertiaDegOf`)
       e  =  d / f.                                                        (`ramIndexOf`)

   This is the definition below. It is manifestly intrinsic (no choice of uniformizer, no
   Newton polygon, no classifier), and it is *total*: `Algebra.norm` and `sInf` are total, so
   no instance obligations leak into the definition.

## Trust boundary (read before accepting)

`typeOf` is the definition the whole development rests on; §"Faithfulness" of
`notes/GENUINE_DENSITY_2026-08-13.md` argues, in mathematics, that it is the classical
factorization type. The **argument uses completeness of `O`** (uniqueness of the extension of
`v`); over a non-complete DVR `inertiaDegOf` would still be defined, but would not be the
residue degree. Nothing below *proves* `∑ eᵢ fᵢ = deg f` in general — that identity needs the
uniqueness-of-extension theorem, which mathlib v4.31.0 does not carry; it is recorded as an
open statement in the note and is **proved here in degree 1** (`typeOf_degree_one`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. Monic factorization in `O[X]` -/

section Factor

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Rescale a polynomial with unit leading coefficient to a monic one. -/
noncomputable def monicize (g : Polynomial O) : Polynomial O :=
  C (Ring.inverse g.leadingCoeff) * g

theorem isUnit_inverse_leadingCoeff {g : Polynomial O} (hg : IsUnit g.leadingCoeff) :
    IsUnit (Ring.inverse g.leadingCoeff) := isUnit_ringInverse.2 hg

theorem associated_monicize {g : Polynomial O} (hg : IsUnit g.leadingCoeff) :
    Associated g (monicize g) :=
  ⟨(isUnit_C.2 (isUnit_inverse_leadingCoeff hg)).unit, by simp [monicize, mul_comm]⟩

theorem monicize_monic {g : Polynomial O} (hg : IsUnit g.leadingCoeff) : (monicize g).Monic := by
  unfold Monic leadingCoeff monicize
  rw [natDegree_C_mul (isUnit_inverse_leadingCoeff hg).ne_zero, coeff_C_mul]
  exact Ring.inverse_mul_cancel _ hg

/-- Leading coefficients of divisors of a monic polynomial are units. -/
theorem isUnit_leadingCoeff_of_dvd_monic {f g : Polynomial O} (hf : f.Monic) (hg : g ∣ f) :
    IsUnit g.leadingCoeff := by
  obtain ⟨c, rfl⟩ := hg
  have h1 : g.leadingCoeff * c.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul]; exact hf
  exact ⟨⟨g.leadingCoeff, c.leadingCoeff, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

/-- **A monic factorization of `f`**: a multiset of monic irreducible polynomials with product
`f`. This is the object `typeOf` reads. -/
def IsMonicFactorization (f : Polynomial O) (F : Multiset (Polynomial O)) : Prop :=
  (∀ g ∈ F, g.Monic ∧ Irreducible g) ∧ F.prod = f

/-- **Existence**: every monic polynomial over a UFD has a monic factorization. -/
theorem monicFactorization_exists {f : Polynomial O} (hf : f.Monic) :
    ∃ F, IsMonicFactorization f F := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  obtain ⟨F, hFirr, hFassoc⟩ := WfDvdMonoid.exists_factors f hf0
  have hdvd : ∀ b ∈ F, IsUnit b.leadingCoeff := fun b hb =>
    isUnit_leadingCoeff_of_dvd_monic hf ((Multiset.dvd_prod hb).trans hFassoc.dvd)
  refine ⟨F.map monicize, ⟨?_, ?_⟩⟩
  · intro g hg
    obtain ⟨b, hbF, rfl⟩ := Multiset.mem_map.1 hg
    exact ⟨monicize_monic (hdvd b hbF), (associated_monicize (hdvd b hbF)).irreducible (hFirr b hbF)⟩
  · have hmonic : ((F.map monicize).prod).Monic :=
      monic_multiset_prod_of_monic _ _ (fun b hb => monicize_monic (hdvd b hb))
    refine eq_of_monic_of_associated hmonic hf (Associated.trans ?_ hFassoc)
    have hsplit : (F.map monicize).prod
        = (F.map (fun b => C (Ring.inverse b.leadingCoeff))).prod * (F.map id).prod := by
      rw [← Multiset.prod_map_mul]; rfl
    have hunit : IsUnit ((F.map (fun b => C (Ring.inverse b.leadingCoeff))).prod) := by
      refine Multiset.prod_induction _ _ (fun a b => IsUnit.mul) isUnit_one ?_
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
      exact isUnit_C.2 (isUnit_inverse_leadingCoeff (hdvd b hb))
    rw [hsplit, Multiset.map_id]
    exact (associated_unit_mul_left _ _ hunit)

/-- **Uniqueness**: the monic factorization is unique as a multiset (monic associates are
equal). -/
theorem monicFactorization_unique {f : Polynomial O} {F G : Multiset (Polynomial O)}
    (hF : IsMonicFactorization f F) (hG : IsMonicFactorization f G) : F = G := by
  have hrel : Multiset.Rel Associated F G :=
    UniqueFactorizationMonoid.factors_unique (fun g hg => (hF.1 g hg).2) (fun g hg => (hG.1 g hg).2)
      (by rw [hF.2, hG.2]; exact Associated.refl f)

  refine Multiset.rel_eq.1 (hrel.mono ?_)
  intro a ha b hb hab
  exact eq_of_monic_of_associated (hF.1 a ha).1 (hG.1 b hb).1 hab

/-- **`monicFactors f`** — the multiset of monic irreducible factors of `f`, with multiplicity.
(For non-monic `f` the junk value `0` is returned; every use site supplies `f.Monic`.) -/
noncomputable def monicFactors (f : Polynomial O) : Multiset (Polynomial O) :=
  open Classical in
  if h : ∃ F, IsMonicFactorization f F then h.choose else 0

theorem monicFactors_spec {f : Polynomial O} (hf : f.Monic) :
    IsMonicFactorization f (monicFactors f) := by
  classical
  have h : ∃ F, IsMonicFactorization f F := monicFactorization_exists hf
  rw [monicFactors, dif_pos h]
  exact h.choose_spec

theorem monicFactors_eq {f : Polynomial O} {F : Multiset (Polynomial O)}
    (hF : IsMonicFactorization f F) : monicFactors f = F := by
  have hid : (F.map id).prod.Monic := monic_multiset_prod_of_monic _ _ (fun g hg => (hF.1 g hg).1)
  rw [Multiset.map_id, hF.2] at hid
  exact monicFactorization_unique (monicFactors_spec hid) hF

end Factor

/-! ## 2. The `(e, f)` pair of a monic irreducible, via the norm form of the valuation -/

section EF

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The set of strictly positive valuations of norms of nonzero elements of `A = O[x]/(g)`.
For `O` complete and `g` monic irreducible this set is exactly `f · ℕ_{>0}`, `f` the residue
degree of `K[x]/(g)` over `K` — see the module docstring. -/
def normValues (g : Polynomial O) : Set ℕ :=
  {k : ℕ | 0 < k ∧ ∃ x : AdjoinRoot g, x ≠ 0 ∧
    IsDiscreteValuationRing.addVal O (Algebra.norm O x) = (k : ℕ∞)}

/-- **`f(g)` — the residue degree** of the extension `K[x]/(g)` of `K = Frac O`, read as the
least strictly positive valuation of a norm from `O[x]/(g)`. -/
noncomputable def inertiaDegOf (g : Polynomial O) : ℕ := sInf (normValues g)

/-- **`e(g)` — the ramification index** of `K[x]/(g)`: `deg g / f(g)`. -/
noncomputable def ramIndexOf (g : Polynomial O) : ℕ := g.natDegree / inertiaDegOf g

/-- The `(e, f)` pair of a monic irreducible factor. -/
noncomputable def efPair (g : Polynomial O) : ℕ × ℕ := (ramIndexOf g, inertiaDegOf g)

/-- `deg g` always belongs to `normValues g` when `g` is monic of positive degree: the image of
a uniformizer `π` has norm `π ^ deg g`. -/
theorem natDegree_mem_normValues {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    {π : O} (hπ : Irreducible π) : g.natDegree ∈ normValues g := by
  haveI hfin := (AdjoinRoot.powerBasis' hg).finite
  haveI hfree : Module.Free O (AdjoinRoot g) := Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  have hrank : Module.finrank O (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg).finrank]; rfl
  have hnorm : Algebra.norm O (algebraMap O (AdjoinRoot g) π) = π ^ g.natDegree := by
    rw [Algebra.norm_algebraMap, hrank]
  have hdeg : g.degree ≠ 0 := ne_of_gt (natDegree_pos_iff_degree_pos.1 hd)
  have hne : (algebraMap O (AdjoinRoot g) π : AdjoinRoot g) ≠ 0 := by
    intro h
    exact hπ.ne_zero (AdjoinRoot.of.injective_of_degree_ne_zero hdeg (by simpa using h))
  refine ⟨hd, _, hne, ?_⟩
  rw [hnorm, hπ.addVal_pow]

end EF

/-! ## 3. `typeOf` -/

section TypeOf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **THE SPLITTING TYPE.** `typeOf f` is the multiset of `(e, f)` pairs of the monic
irreducible factors of `f`, with multiplicity — the classical `p`-adic factorization type of a
monic polynomial over a complete DVR.

**Design choices flagged for review** (this is the trust boundary):
* *with multiplicity* — a repeated factor contributes its pair twice, matching the informal
  `σ = ∑ᵢ (eᵢ, fᵢ)` grain of `FactorizationType`;
* *`(e, f)` order* — first coordinate ramification, second residue degree, matching
  `FactorizationType.degree = ∑ eᵢ * fᵢ`;
* *no separability hypothesis* — inseparable/degenerate `f` (a perfect square, say) still get a
  value; they form a measure-zero set and are never `σ`-decided at any finite level;
* *junk for non-monic `f`* — `monicFactors` returns `0`, so `typeOf f = ⟨0⟩` there. Every
  statement below is about `monicPoly a`, which is monic by construction. -/
noncomputable def typeOf (f : Polynomial O) : FactorizationType :=
  ⟨(monicFactors f).map efPair⟩

theorem typeOf_data (f : Polynomial O) : (typeOf f).data = (monicFactors f).map efPair := rfl

/-! ### Degree 1: the fully proved case

Every monic linear polynomial is irreducible with `(e, f) = (1, 1)`, so its type is
`⟨{(1,1)}⟩`, of degree `1`. This is the exact-value gate of the unit (`Gates.lean`). -/

theorem isUnit_of_natDegree_zero {a : Polynomial O} (h : a.natDegree = 0)
    (hu : IsUnit a.leadingCoeff) : IsUnit a := by
  rw [eq_C_of_natDegree_eq_zero h]
  refine isUnit_C.2 ?_
  rwa [leadingCoeff, h] at hu

/-- A monic polynomial of degree 1 over a domain is irreducible. -/
theorem irreducible_of_monic_natDegree_one {g : Polynomial O} (hg : g.Monic)
    (hd : g.natDegree = 1) : Irreducible g := by
  constructor
  · intro hu
    have := natDegree_eq_zero_of_isUnit hu
    omega
  · intro a b hab
    have hg0 : g ≠ 0 := hg.ne_zero
    have ha0 : a ≠ 0 := by rintro rfl; exact hg0 (by simpa using hab)
    have hb0 : b ≠ 0 := by rintro rfl; exact hg0 (by simpa using hab)
    have hdeg : a.natDegree + b.natDegree = 1 := by
      rw [← natDegree_mul ha0 hb0, ← hab, hd]
    have hlead : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hab]; exact hg
    rcases Nat.eq_zero_or_pos a.natDegree with h | h
    · exact Or.inl (isUnit_of_natDegree_zero h
        ⟨⟨a.leadingCoeff, b.leadingCoeff, hlead, by rw [mul_comm]; exact hlead⟩, rfl⟩)
    · have hb : b.natDegree = 0 := by omega
      exact Or.inr (isUnit_of_natDegree_zero hb
        ⟨⟨b.leadingCoeff, a.leadingCoeff, by rw [mul_comm]; exact hlead, hlead⟩, rfl⟩)

/-- **`(e, f) = (1, 1)` for a monic linear polynomial.** The image of a uniformizer in
`O[x]/(g) ≅ O` has norm `π`, of valuation `1`, so the least positive norm-valuation is `1`. -/
theorem efPair_of_natDegree_one {g : Polynomial O} (hg : g.Monic) (hd : g.natDegree = 1) :
    efPair g = (1, 1) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmem : (1 : ℕ) ∈ normValues g := by
    have := natDegree_mem_normValues hg (by omega) hπ
    rwa [hd] at this
  have hne : (normValues g).Nonempty := ⟨1, hmem⟩
  have hpos : 0 < sInf (normValues g) := (Nat.sInf_mem hne).1
  have h1 : sInf (normValues g) = 1 := le_antisymm (Nat.sInf_le hmem) hpos
  simp [efPair, ramIndexOf, inertiaDegOf, h1, hd]

/-- **The type of a monic linear polynomial is `⟨{(1,1)}⟩`.** -/
theorem typeOf_of_natDegree_one {g : Polynomial O} (hg : g.Monic) (hd : g.natDegree = 1) :
    typeOf g = ⟨{(1, 1)}⟩ := by
  have hF : IsMonicFactorization g {g} := by
    refine ⟨?_, by simp⟩
    intro h hh
    rw [Multiset.mem_singleton.1 hh]
    exact ⟨hg, irreducible_of_monic_natDegree_one hg hd⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [efPair_of_natDegree_one hg hd]

/-- The degree of the type of a monic linear polynomial is `1` — the `n = 1` instance of the
(generally open) identity `(typeOf f).degree = deg f`. -/
theorem typeOf_degree_one {g : Polynomial O} (hg : g.Monic) (hd : g.natDegree = 1) :
    (typeOf g).degree = 1 := by
  rw [typeOf_of_natDegree_one hg hd]
  simp [FactorizationType.degree]

end TypeOf

end Uniformity.Density
