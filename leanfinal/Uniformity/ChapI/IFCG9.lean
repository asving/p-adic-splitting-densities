/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG8

/-!
# Uniformity.ChapI.IFCG9 — [GC 2026-08-29] the finite-genre-cover stop line

This file attempts nodes A0G-GC0--GC4.  It lands the unconditional schema-bank and decrease
parts, isolates the exact degree-exhaustion normalization which discharges IFCG8's `hbelow1`,
and records a formal obstruction to assembling GC2 from the current realization predicate:
`IFCG5.RealizesFaceAt` forgets the residual pattern and sees only its total degree.

Consequently this file deliberately does **not** declare `finiteGenreCoverAt_all`.  The exact
remaining coefficient-side theorem is stated as `recentredCluster_degreeExhaustion`; the exact
residual-fidelity repair is described next to the mass-two falsifier in §4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG9

open Uniformity (FactorizationType)
open Uniformity.Density.IFCG5 Uniformity.Density.IFCG6 Uniformity.Density.IFCG7
open Uniformity.Density.IFCG8

/-! ## §1 — the finite bank, literally the landed skeleton `Fintype` -/

/-- The finite list of all mass-`m` skeletons.  This list exists before an input polynomial is
supplied, as required by the no-pointwise-termination gate. -/
noncomputable def genreSkeletonFinset (m : ℕ) : Finset (ClusterSkeleton m) := Finset.univ

@[simp] theorem mem_genreSkeletonFinset {m : ℕ} (S : ClusterSkeleton m) :
    S ∈ genreSkeletonFinset m := Finset.mem_univ S

/-- Completeness of the finite bank at the raw valid-skeleton surface. -/
theorem exists_mem_genreSkeletonFinset_of_valid {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) :
    ∃ S ∈ genreSkeletonFinset m, S.1 = s := by
  exact ⟨ClusterSkeleton.ofValid hs, Finset.mem_univ _, rfl⟩

/-- GC0's finite-bank statement: the precomputed bank contains exactly all valid skeleton
lists. -/
def GC0FiniteBankAt (m : ℕ) : Prop :=
  ∀ s : List FaceShape,
    ValidSkeleton m s ↔ ∃ S ∈ genreSkeletonFinset m, S.1 = s

/-- **GC0 LANDED at the skeleton surface.** -/
theorem gc0_finiteBank_all : ∀ m : ℕ, GC0FiniteBankAt m := by
  intro m s
  constructor
  · exact exists_mem_genreSkeletonFinset_of_valid
  · rintro ⟨S, _, rfl⟩
    exact S.valid

/-! ## §2 — GC3: every non-loop recursive child decreases -/

/-- The decreasing-child property of the finite bank. -/
def DecreasingGenreBankAt (m : ℕ) : Prop :=
  ∀ S ∈ genreSkeletonFinset m, S.1 ≠ loopSkeleton m →
    ∀ μ ∈ childSizes S.1, μ < m

/-- **GC3 LANDED at the skeleton surface.**  Every non-loop member of the finite bank has only
strictly smaller recursive children. -/
theorem decreasingGenreBankAt_all : ∀ m : ℕ, DecreasingGenreBankAt m := by
  intro m S _ hne μ hμ
  exact childSizes_lt_mass_of_ne_loop S.valid hne μ hμ

/-- The loop is the sole possible same-mass child, in the sharp entry-indexed form. -/
theorem sameMass_child_is_loop {m : ℕ} {S : ClusterSkeleton m} {f : FaceShape}
    {p : ℕ × ℕ} (hc : IsChildEntry S.1 f p) (hpm : p.2 = m) :
    S.1 = loopSkeleton m ∧ f = loopFace m ∧ p = (1, m) :=
  eq_loopSkeleton_of_entry_snd_eq_mass S.valid hc.1 hc.2.1 hpm

/-! ## §3 — GC1's exact opening: degree exhaustion is precisely `below = 1` -/

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The normalized recentred-cluster condition at the dissection surface.**  Every C.33
dissection accounts for the whole degree in its above-floor factors.  The missing coefficient-
box theorem is that the recentring/cluster hypotheses imply this condition; see
`recentredCluster_degreeExhaustion` below. -/
def DissectionDegreeExhausted (F : KeyFrame O π) (f : Polynomial O) : Prop :=
  ∀ D : DvDissection F f,
    f.natDegree = ∑ p ∈ D.slopes, (D.factor p).natDegree

/-- Degree bookkeeping in a dissection: the degree of `f` is the degree of `below` plus the
degrees of all slope factors. -/
theorem natDegree_eq_below_add_factors {F : KeyFrame O π} {f : Polynomial O}
    (D : DvDissection F f) :
    f.natDegree = D.below.natDegree + ∑ p ∈ D.slopes, (D.factor p).natDegree := by
  have hprodmon : (∏ p ∈ D.slopes, D.factor p).Monic :=
    Polynomial.monic_prod_of_monic D.slopes D.factor (fun p hp => D.hmonic p hp)
  calc
    f.natDegree = (D.below * ∏ p ∈ D.slopes, D.factor p).natDegree :=
      congrArg Polynomial.natDegree D.hprod
    _ = D.below.natDegree + (∏ p ∈ D.slopes, D.factor p).natDegree :=
      D.hbelow_monic.natDegree_mul hprodmon
    _ = D.below.natDegree + ∑ p ∈ D.slopes, (D.factor p).natDegree := by
      rw [Polynomial.natDegree_prod_of_monic D.slopes D.factor
        (fun p hp => D.hmonic p hp)]

/-- Degree exhaustion forces the below-floor factor to be the monic constant `1`. -/
theorem below_eq_one_of_degreeExhausted {F : KeyFrame O π} {f : Polynomial O}
    (h : DissectionDegreeExhausted F f) (D : DvDissection F f) : D.below = 1 := by
  have hdeg := natDegree_eq_below_add_factors D
  have hex := h D
  have hzero : D.below.natDegree = 0 := by omega
  exact Polynomial.eq_one_of_monic_natDegree_zero D.hbelow_monic hzero

/-- Conversely, a trivial below-floor factor gives degree exhaustion. -/
theorem degreeExhausted_of_below_eq_one {F : KeyFrame O π} {f : Polynomial O}
    (h : ∀ D : DvDissection F f, D.below = 1) : DissectionDegreeExhausted F f := by
  intro D
  rw [natDegree_eq_below_add_factors D, h D]
  simp

/-- **Exact normalization dictionary.**  IFCG8's scoped `hbelow1` is equivalent to the
degree-exhaustion formulation which a recentred coefficient-box proof must establish. -/
theorem degreeExhausted_iff_below_eq_one {F : KeyFrame O π} {f : Polynomial O} :
    DissectionDegreeExhausted F f ↔ ∀ D : DvDissection F f, D.below = 1 := by
  constructor
  · exact fun h D => below_eq_one_of_degreeExhausted h D
  · exact degreeExhausted_of_below_eq_one

/-- **GC1, conditional only on the genuine normalization statement.**  Once the recentred
cluster's above-floor factors exhaust its degree, IFCG8 supplies a member of the finite bank
realized by the polynomial.  `hbelow1` no longer appears in this interface. -/
theorem exists_realizesSkeletonAt_of_degreeExhausted
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (H₀ : ℕ) (hpin : F.Pin H₀) {f : Polynomial O} (hf : f.Monic)
    (hkey : ¬ F.key ∣ f) (hnorm : DissectionDegreeExhausted F f)
    {m : ℕ} (hm : f.natDegree = (F.e₁ * F.f₁) * m) :
    ∃ (S : ClusterSkeleton m) (num : Fin S.1.length → ℕ)
      (blocks : Fin S.1.length → Polynomial O),
      S ∈ genreSkeletonFinset m ∧ RealizesSkeletonAt F S num blocks := by
  obtain ⟨S, num, blocks, hreal⟩ :=
    exists_realizesSkeletonAt_of_dissection hπ hh H₀ hpin hf hkey
      (fun D => below_eq_one_of_degreeExhausted hnorm D) hm
  exact ⟨S, num, blocks, Finset.mem_univ _, hreal⟩

/-! The exact coefficient-side theorem still missing from the corpus.  It is recorded as a
`def`-level proposition, not postulated as an axiom: a GC completion must construct a term of
this type from the raw recentred coefficient-box normalization. -/

/-- A coefficient-level recentred normalization relative to `F`: in the `F.key`-development,
every coefficient strictly left of the monic endpoint lies strictly above the continuation of
the frame-floor line.  This is the direct bounded-coefficient formulation of “every root of the
current cluster lies above the current frame floor”; it mentions no dissection and is therefore
not a disguised `hbelow1` hypothesis. -/
def StrictlyRecentredAboveFloor (F : KeyFrame O π) (f : Polynomial O) : Prop :=
  (F.e₁ * F.f₁) ∣ f.natDegree ∧
    ∀ j : ℕ, j < f.natDegree / (F.e₁ * F.f₁) →
      (((F.e₁ * F.f₁) * F.h * (f.natDegree / (F.e₁ * F.f₁) - j) : ℕ) : ℕ∞)
        < dvHgt F f j

/-- **BLOCKED-BECAUSE statement (GC1), exact form.**  The missing theorem is polygonal
exhaustion: strict coefficient-side recentring forces every C.33 dissection to spend the whole
degree above the floor.  Proving this needs the entire/principal-polygon comparison which no
current IFCG/C.33 declaration exports. -/
def RecentredClusterDegreeExhaustionStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (π : O) (_hπ : Irreducible π) (F : KeyFrame O π) (f : Polynomial O),
    f.Monic → ¬ F.key ∣ f → StrictlyRecentredAboveFloor F f →
      DissectionDegreeExhausted F f

/-! ## §4 — the exact type-sound realization surface which the current bridge does not export -/

/-- The residual-factorization witness consumed by IFCG6's `schema_split`: the face pattern
is literally the list of `(degree, multiplicity)` labels of pairwise-distinct monic irreducible
residual factors, and their powers multiply to the block's `dvResPoly`. -/
def ResidualPatternWitnessAt {F : KeyFrame O π} (H₀ : ℕ) (hpin : F.Pin H₀)
    (g : Polynomial O) (u : ℕ) (face : FaceShape) : Prop :=
  ∃ (hne : (dvSideSet F g u face.1).Nonempty) (M : ℕ)
    (hp : dvHgt F g (dvSideMin F g u face.1 hne) = (M : ℕ∞))
    (ers : List ((ℕ × ℕ) × Polynomial (F.stageField H₀ hpin))),
    (∀ x ∈ ers, x.2.Monic ∧ Irreducible x.2 ∧ x.2.natDegree = x.1.1 ∧
      1 ≤ x.1.1 ∧ 1 ≤ x.1.2) ∧
    ers.Pairwise (fun x y => x.2 ≠ y.2) ∧
    face.2.data = (↑(ers.map Prod.fst) : Multiset (ℕ × ℕ)) ∧
    dvResPoly F H₀ hpin g u face.1 hne M hp =
      (ers.map (fun x => x.2 ^ x.1.2)).prod

/-- The repaired face realization needed by GC2/GC3: geometric realization plus the residual
factorization data which certifies the face's full pattern. -/
def StrongRealizesFaceAt {F : KeyFrame O π} (H₀ : ℕ) (hpin : F.Pin H₀)
    (g : Polynomial O) (u : ℕ) (face : FaceShape) : Prop :=
  RealizesFaceAt F g u face ∧ ResidualPatternWitnessAt H₀ hpin g u face

theorem strongRealizesFaceAt_realizes {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {g : Polynomial O} {u : ℕ} {face : FaceShape}
    (h : StrongRealizesFaceAt H₀ hpin g u face) : RealizesFaceAt F g u face := h.1

/-- A strong realization exports exactly IFCG6 `schema_split`'s residual input package, with
the face pattern identified on the nose. -/
theorem strongRealizesFaceAt_schemaData {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {g : Polynomial O} {u : ℕ} {face : FaceShape}
    (h : StrongRealizesFaceAt H₀ hpin g u face) :
    ∃ (hne : (dvSideSet F g u face.1).Nonempty) (M : ℕ)
      (hp : dvHgt F g (dvSideMin F g u face.1 hne) = (M : ℕ∞))
      (ers : List ((ℕ × ℕ) × Polynomial (F.stageField H₀ hpin))),
      (∀ x ∈ ers, x.2.Monic ∧ Irreducible x.2 ∧ x.2.natDegree = x.1.1 ∧
        1 ≤ x.1.1 ∧ 1 ≤ x.1.2) ∧
      ers.Pairwise (fun x y => x.2 ≠ y.2) ∧
      face.2.data = (↑(ers.map Prod.fst) : Multiset (ℕ × ℕ)) ∧
      dvResPoly F H₀ hpin g u face.1 hne M hp =
        (ers.map (fun x => x.2 ^ x.1.2)).prod :=
  h.2

/-! ## §5 — GC2 falsifier: `RealizesFaceAt` forgets the residual pattern -/

/-- `RealizesFaceAt` is invariant under changing the residual pattern while preserving the
denominator and total residual degree. -/
theorem realizesFaceAt_iff_of_den_resDeg_eq {F : KeyFrame O π} {g : Polynomial O}
    {u : ℕ} {f f' : FaceShape} (hb : f.1 = f'.1)
    (hd : faceResDeg f = faceResDeg f') :
    RealizesFaceAt F g u f ↔ RealizesFaceAt F g u f' := by
  have hlen : faceLen f = faceLen f' := by simp [faceLen, hb, hd]
  constructor
  · rintro ⟨hu, hcop, hpure, hside⟩
    refine ⟨hu, ?_, ?_, ?_⟩
    · simpa [hb] using hcop
    · simpa [hb] using hpure
    · simpa [hb, hlen] using hside
  · rintro ⟨hu, hcop, hpure, hside⟩
    refine ⟨hu, ?_, ?_, ?_⟩
    · simpa [hb] using hcop
    · simpa [hb] using hpure
    · simpa [hb, hlen] using hside

/-- A repeated rational residual factor at mass two. -/
def repeatedLinearFace : FaceShape := (1, (⟨{(1, 2)}⟩ : FactorizationType))

/-- A simple quadratic residual factor at mass two. -/
def simpleQuadraticFace : FaceShape := (1, (⟨{(2, 1)}⟩ : FactorizationType))

theorem repeatedLinearFace_valid : ValidFace repeatedLinearFace :=
  validFace_singleton (le_refl 1) (le_refl 1) (by omega)

theorem simpleQuadraticFace_valid : ValidFace simpleQuadraticFace :=
  validFace_singleton (le_refl 1) (by omega) (le_refl 1)

theorem repeatedLinearFace_resDeg : faceResDeg repeatedLinearFace = 2 := by
  simp [repeatedLinearFace, faceResDeg, FactorizationType.degree]

theorem simpleQuadraticFace_resDeg : faceResDeg simpleQuadraticFace = 2 := by
  simp [simpleQuadraticFace, faceResDeg, FactorizationType.degree]

/-- The two mass-two residual patterns are genuinely distinct. -/
theorem repeatedLinearFace_ne_simpleQuadraticFace :
    repeatedLinearFace ≠ simpleQuadraticFace := by
  intro h
  have hdata := congrArg (fun f : FaceShape => f.2.data) h
  simp [repeatedLinearFace, simpleQuadraticFace] at hdata

/-- **Formal GC2 falsifier.**  Every block which realizes one of the two distinct mass-two
faces realizes the other.  Therefore IFCG7's read-off theorem cannot establish residual-pattern
uniqueness until the realization predicate is strengthened with the `dvResPoly` factorization
used internally by IFCG8 §3. -/
theorem realizes_repeatedLinear_iff_simpleQuadratic {F : KeyFrame O π}
    {g : Polynomial O} {u : ℕ} :
    RealizesFaceAt F g u repeatedLinearFace ↔
      RealizesFaceAt F g u simpleQuadraticFace :=
  realizesFaceAt_iff_of_den_resDeg_eq rfl
    (repeatedLinearFace_resDeg.trans simpleQuadraticFace_resDeg.symm)

end Uniformity.Density.IFCG9

end

/-! ## AXCHECK FOOTER

Lean core on the schema/decrease/dictionary/falsifier declarations; the conditional exhaustion
theorem additionally inherits exactly `Uniformity.Density.Tower.exists_dvDissection` through
IFCG8. -/

#print axioms Uniformity.Density.IFCG9.exists_mem_genreSkeletonFinset_of_valid
#print axioms Uniformity.Density.IFCG9.gc0_finiteBank_all
#print axioms Uniformity.Density.IFCG9.decreasingGenreBankAt_all
#print axioms Uniformity.Density.IFCG9.sameMass_child_is_loop
#print axioms Uniformity.Density.IFCG9.natDegree_eq_below_add_factors
#print axioms Uniformity.Density.IFCG9.below_eq_one_of_degreeExhausted
#print axioms Uniformity.Density.IFCG9.degreeExhausted_iff_below_eq_one
#print axioms Uniformity.Density.IFCG9.exists_realizesSkeletonAt_of_degreeExhausted
#print axioms Uniformity.Density.IFCG9.strongRealizesFaceAt_realizes
#print axioms Uniformity.Density.IFCG9.strongRealizesFaceAt_schemaData
#print axioms Uniformity.Density.IFCG9.realizesFaceAt_iff_of_den_resDeg_eq
#print axioms Uniformity.Density.IFCG9.repeatedLinearFace_ne_simpleQuadraticFace
#print axioms Uniformity.Density.IFCG9.realizes_repeatedLinear_iff_simpleQuadratic
