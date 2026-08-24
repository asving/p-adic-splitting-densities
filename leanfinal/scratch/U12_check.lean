import Uniformity.ChapC.C130fg
import Uniformity.ChapC.C105
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Elaboration authority for U12's proposed level-general carrier.  This file deliberately
contains only definitions, structures, and projection/transport theorems: no proof
placeholders, no extra logical assumptions, and no claimed instance of the source carrier.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.LevelGeneralCheck

open Uniformity.Density.Leaf

universe uKt uL uKv uOmega uRes

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {e' f' u' : ℕ}

/-! ## Small, actual source objects -/

/-- Cast the repository's cleared integer value (including `⊤`) to a rational value. -/
def intTopToRat : WithTop ℤ → WithTop ℚ := WithTop.map fun z => (z : ℚ)

/-- Cast the DVR's nonnegative additive value (including `⊤`) to a rational value. -/
def natTopToRat : WithTop ℕ → WithTop ℚ := WithTop.map fun n => (n : ℚ)

/-- An additive valuation on a polynomial ring, in exactly the laws used below. -/
structure PolynomialValuation (K : Type uKv) [Field K] where
  toFun : Polynomial K → WithTop ℚ
  map_zero : toFun 0 = ⊤
  map_one : toFun 1 = 0
  finite_iff : ∀ g, toFun g = ⊤ ↔ g = 0
  map_mul : ∀ g h, toFun (g * h) = toFun g + toFun h
  map_add_ge : ∀ g h, min (toFun g) (toFun h) ≤ toFun (g + h)
  map_add_eq : ∀ g h, toFun g ≠ toFun h →
    toFun (g + h) = min (toFun g) (toFun h)

/-- Initial-form equivalence, using FGMN Definition 1.2's explicit value criterion. -/
def MuEquiv {K : Type uKv} [Field K] (μ : PolynomialValuation K)
    (g h : Polynomial K) : Prop :=
  (μ.toFun (g - h) > μ.toFun g ∧ μ.toFun g = μ.toFun h) ∨ (g = 0 ∧ h = 0)

/-- `μ`-divisibility, using FGMN Definition 1.2's equivalent factor criterion. -/
def MuDivides {K : Type uKv} [Field K] (μ : PolynomialValuation K)
    (φ g : Polynomial K) : Prop :=
  ∃ q : Polynomial K, MuEquiv μ g (φ * q)

/-- A key polynomial without introducing an opaque predicate: monic, `μ`-minimal, and
`μ`-irreducible (the prime initial-form condition expressed through `MuDivides`). -/
def IsKeyPolynomial {K : Type uKv} [Field K] (μ : PolynomialValuation K)
    (φ : Polynomial K) : Prop :=
  φ.Monic ∧
    (∀ g : Polynomial K, g ≠ 0 → g.natDegree < φ.natDegree → ¬ MuDivides μ φ g) ∧
    ¬ MuDivides μ φ 1 ∧
    ∀ g h : Polynomial K, MuDivides μ φ (g * h) →
      MuDivides μ φ g ∨ MuDivides μ φ h

/-- Definition 1.6, literally as the minimum over the canonical `φ`-expansion. -/
noncomputable def IsAugmentation {K : Type uKv} [Field K]
    (μ μ' : PolynomialValuation K) (φ : Polynomial K) (ν : ℚ) : Prop :=
  ∀ g : Polynomial K,
    μ'.toFun g = (Finset.range (g.natDegree + 1)).inf fun s =>
      μ.toFun (dev φ g s) + s • (μ.toFun φ + (ν : WithTop ℚ))

/-- The actual ordinate cloud defining `N_{μ,φ}(g)`: ordinate at abscissa `s` is the value
of the `s`-th `φ`-term, not a freely chosen polygon. -/
noncomputable def newtonOrdinate {K : Type uKv} [Field K] (μ : PolynomialValuation K)
    (φ g : Polynomial K) (s : ℕ) : WithTop ℚ :=
  μ.toFun (dev φ g s) + s • μ.toFun φ

/-- “One-sided of slope `-ν` and length `ell`”, tied pointwise to the actual canonical
expansion.  Adding `s*ν` shears a side of slope `-ν` to a horizontal line. -/
noncomputable def NewtonOneSided {K : Type uKv} [Field K] (μ : PolynomialValuation K)
    (φ g : Polynomial K) (ν : ℚ) (ell : ℕ) : Prop :=
  0 < ell ∧ dev φ g 0 ≠ 0 ∧ dev φ g ell ≠ 0 ∧
    (∀ s, ell < s → dev φ g s = 0) ∧
    newtonOrdinate μ φ g 0 =
      newtonOrdinate μ φ g ell + ell • ((ν : WithTop ℚ)) ∧
    ∀ s, s ≤ ell →
      newtonOrdinate μ φ g 0 ≤
        newtonOrdinate μ φ g s + s • ((ν : WithTop ℚ))

/-! ## The genuinely new valued/completed root ambient -/

/-- A source model of `K_v` and an algebraic closure carrying an extension of `v`.

`Kv` is represented as the fraction field of the already adically complete DVR `O`; `Omega`
is algebraic and algebraically closed over it.  The explicit valuation and restriction law are
included because neither follows from the residual-field ambient `L` in `ChainRealization`. -/
structure CompletedRootAmbient where
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  Kv : Type uKv
  [kvField : Field Kv]
  [kvAlgebra : Algebra O Kv]
  [kvFraction : IsFractionRing O Kv]
  Omega : Type uOmega
  [omegaField : Field Omega]
  [omegaAlgebra : Algebra Kv Omega]
  [omegaAlgClosed : IsAlgClosed Omega]
  [omegaAlgebraic : Algebra.IsAlgebraic Kv Omega]
  coeffHom : O →+* Omega
  coeffHom_eq : coeffHom = (algebraMap Kv Omega).comp (algebraMap O Kv)
  value : Omega → WithTop ℚ
  value_zero : value 0 = ⊤
  value_one : value 1 = 0
  value_finite_iff : ∀ a, value a = ⊤ ↔ a = 0
  value_mul : ∀ a b, value (a * b) = value a + value b
  value_add_ge : ∀ a b, min (value a) (value b) ≤ value (a + b)
  value_add_eq : ∀ a b, value a ≠ value b → value (a + b) = min (value a) (value b)
  value_restricts : ∀ a : O,
    value (coeffHom a) = natTopToRat (IsDiscreteValuationRing.addVal O a)

attribute [instance] CompletedRootAmbient.kvField
attribute [instance] CompletedRootAmbient.kvAlgebra
attribute [instance] CompletedRootAmbient.kvFraction
attribute [instance] CompletedRootAmbient.omegaField
attribute [instance] CompletedRootAmbient.omegaAlgebra
attribute [instance] CompletedRootAmbient.omegaAlgClosed
attribute [instance] CompletedRootAmbient.omegaAlgebraic

/-- The family `F_i` of source residual fields. -/
structure ResidualFieldFamily where
  carrier : ℕ → Type uRes
  field : ∀ i, Field (carrier i)

attribute [instance] ResidualFieldFamily.field

/-! ## The full source MacLane chain and the CC dictionary -/

/-- The per-truncation source objects absent from CC: all `μ_i`, their keys and augmentations,
all Newton slopes/invariants, and every residual field/operator/minimal polynomial. -/
structure MacLaneChainSource (B : CompletedRootAmbient (O := O)) (r : ℕ) where
  mu : ℕ → PolynomialValuation B.Kv
  mu_restricts : ∀ i (a : B.Kv),
    (mu i).toFun (Polynomial.C a) = B.value (algebraMap B.Kv B.Omega a)
  mu_X_nonnegative : ∀ i, 0 ≤ (mu i).toFun Polynomial.X
  key : ℕ → Polynomial B.Kv
  nu : ℕ → ℚ
  nu_pos : ∀ i, StageLive r i → 0 < nu i
  key_is_key : ∀ i, StageLive r i → IsKeyPolynomial (mu (i - 1)) (key i)
  augmentation : ∀ i, StageLive r i → IsAugmentation (mu (i - 1)) (mu i) (key i) (nu i)
  macLane : ∀ i, GaugeLive r i → ¬ MuEquiv (mu i) (key (i + 1)) (key i)
  ramification : ℕ → ℕ
  residueDegree : ℕ → ℕ
  ramification_pos : ∀ i, StageLive r i → 0 < ramification i
  residueDegree_pos : ∀ i, StageLive r i → 0 < residueDegree i
  residualField : ResidualFieldFamily.{uRes}
  residual : (i : ℕ) → Polynomial B.Kv → Polynomial (residualField.carrier i)
  residueHom : (i : ℕ) → residualField.carrier i →+* residualField.carrier (i + 1)
  letter : (i : ℕ) → residualField.carrier (i + 1)
  psi : (i : ℕ) → Polynomial (residualField.carrier i)
  psi_spec : ∀ i, i < r →
    (psi i).Monic ∧ Irreducible (psi i) ∧ (psi i).coeff 0 ≠ 0
  psi_root : ∀ i, i < r →
    Polynomial.eval₂ (residueHom i) (letter i) (psi i) = 0
  psi_minimal : ∀ i, i < r → ∀ q : Polynomial (residualField.carrier i),
    q ≠ 0 → Polynomial.eval₂ (residueHom i) (letter i) q = 0 →
      (psi i).natDegree ≤ q.natDegree

/-- All identifications with the landed CC layer.  These are dictionaries, not Corollary 6.3
conclusions: keys, stage values/slopes/invariants, residual fields/operators, and twisted repo
letters are identified before the literature theorem is applied. -/
structure LevelGeneralDictionary
    (A : ChainRealization W Kt L e' f' u')
    (B : CompletedRootAmbient (O := O)) (M : MacLaneChainSource B r) where
  key_compat : ∀ i, StageLive r i →
    M.key i = (A.keys.keyAt i).map (algebraMap O B.Kv)
  stage_value_compat : ∀ i, StageLive r i → ∀ g : Polynomial O,
    (M.mu (i - 1)).toFun (g.map (algebraMap O B.Kv)) = intTopToRat (A.node.hgt i g)
  slope_compat : ∀ i, StageLive r i →
    M.nu i = (W.u i : ℚ) / W.ehat i
  ramification_compat : ∀ i, StageLive r i → M.ramification i = W.e i
  residueDegree_compat : ∀ i, StageLive r i → M.residueDegree i = W.f i
  residueEquiv : (i : ℕ) → StageLive r i →
    M.residualField.carrier (i - 1) ≃+* W.fld i
  repoResidual : (i : ℕ) → Polynomial O → Polynomial (W.fld i)
  repoPsi : (i : ℕ) → Polynomial (W.fld i)
  omega : (i : ℕ) → (W.fld i)ˣ
  repoPsi_twisted : ∀ i, GaugeLive r i →
    repoPsi i = wconj (omega i : W.fld i) (W.ψ i)
  residual_compat : ∀ i (hi : StageLive r i) (g : Polynomial O),
    (M.residual (i - 1) (g.map (algebraMap O B.Kv))).map (residueEquiv i hi).toRingHom =
      repoResidual i g
  psi_compat : ∀ i (hi : StageLive r i),
    (M.psi (i - 1)).map (residueEquiv i hi).toRingHom = repoPsi i

/-! ## Target-specific hypotheses, separate from the cited conclusion -/

/-- The exact hypotheses of Theorem 6.2/Corollary 6.3, on top of the realized chain.
No one-sidedness, root-value equality, residual power, or length recurrence is a field here. -/
structure LevelGeneralInput
    (A : ChainRealization W Kt L e' f' u')
    (B : CompletedRootAmbient (O := O)) (M : MacLaneChainSource B r)
    (D : LevelGeneralDictionary A B M) (G topKey : Polynomial O)
    (terminalPsi : Polynomial (W.fld r)) where
  depth_pos : 0 < r
  target_monic : G.Monic
  target_prime : Irreducible (G.map (algebraMap O B.Kv))
  theta : B.Omega
  target_root : Polynomial.eval₂ B.coeffHom theta G = 0
  topKey_is_key : IsKeyPolynomial (M.mu r) (topKey.map (algebraMap O B.Kv))
  topKey_divides_target :
    MuDivides (M.mu r) (topKey.map (algebraMap O B.Kv)) (G.map (algebraMap O B.Kv))
  topKey_not_equiv_last :
    ¬ MuEquiv (M.mu r) (topKey.map (algebraMap O B.Kv)) (M.key r)
  terminalPsi_compat : D.repoPsi r = terminalPsi

/-! ## The cited output, and its repository-facing projection -/

/-- The full, verbatim-clause output package of published Corollary 6.3.  This is a theorem
codomain, never a field of `LevelGeneralInput` or `ChainRealization`. -/
structure Cor63Conclusion
    {A : ChainRealization W Kt L e' f' u'}
    {B : CompletedRootAmbient (O := O)} {M : MacLaneChainSource B r}
    {D : LevelGeneralDictionary A B M} {G topKey : Polynomial O}
    {terminalPsi : Polynomial (W.fld r)}
    (X : LevelGeneralInput A B M D G topKey terminalPsi) where
  ell : ℕ → ℕ
  ell_pos : ∀ i, StageLive r i → 0 < ell i
  polygon_oneSided : ∀ i, StageLive r i →
    NewtonOneSided (M.mu (i - 1)) (M.key i)
      (G.map (algebraMap O B.Kv)) (M.nu i) (ell i)
  root_value : ∀ i, StageLive r i →
    B.value (Polynomial.eval₂ B.coeffHom X.theta (A.keys.keyAt i)) =
      (M.mu r).toFun (M.key i)
  initial_equiv : ∀ i, StageLive r i →
    MuEquiv (M.mu (i - 1)) (G.map (algebraMap O B.Kv)) (M.key i ^ ell i)
  degree_eq : ∀ i, StageLive r i →
    G.natDegree = (A.keys.keyAt i ^ ell i).natDegree
  residual_power : ∀ i, StageLive r i →
    M.residual (i - 1) (G.map (algebraMap O B.Kv)) = M.psi (i - 1) ^ ell i
  length_recurrence : ∀ i, GaugeLive r i →
    ell i = M.ramification i * M.residueDegree i * ell (i + 1)

/-- The package C.90(b) may expose after applying the cite and transporting through `D`.
It deliberately keeps all six clauses; a residual-only projection is not the C.90 package. -/
structure C90LevelGeneralPackage
    {A : ChainRealization W Kt L e' f' u'}
    {B : CompletedRootAmbient (O := O)} {M : MacLaneChainSource B r}
    {D : LevelGeneralDictionary A B M} {G topKey : Polynomial O}
    {terminalPsi : Polynomial (W.fld r)}
    (X : LevelGeneralInput A B M D G topKey terminalPsi) where
  ell : ℕ → ℕ
  ell_pos : ∀ i, StageLive r i → 0 < ell i
  polygon_oneSided : ∀ i, StageLive r i →
    NewtonOneSided (M.mu (i - 1)) (M.key i)
      (G.map (algebraMap O B.Kv)) (M.nu i) (ell i)
  root_value : ∀ i, StageLive r i →
    B.value (Polynomial.eval₂ B.coeffHom X.theta (A.keys.keyAt i)) =
      (M.mu r).toFun (M.key i)
  initial_equiv : ∀ i, StageLive r i →
    MuEquiv (M.mu (i - 1)) (G.map (algebraMap O B.Kv)) (M.key i ^ ell i)
  degree_eq : ∀ i, StageLive r i →
    G.natDegree = (A.keys.keyAt i ^ ell i).natDegree
  repo_residual_power : ∀ i (_hi : StageLive r i),
    D.repoResidual i G = D.repoPsi i ^ ell i
  length_recurrence : ∀ i, GaugeLive r i →
    ell i = W.e i * W.f i * ell (i + 1)

/-- C.90(b)'s discharge is transport/packaging once the published result is supplied. -/
def Cor63Conclusion.toC90
    {A : ChainRealization W Kt L e' f' u'}
    {B : CompletedRootAmbient (O := O)} {M : MacLaneChainSource B r}
    {D : LevelGeneralDictionary A B M} {G topKey : Polynomial O}
    {terminalPsi : Polynomial (W.fld r)}
    {X : LevelGeneralInput A B M D G topKey terminalPsi} (C : Cor63Conclusion X) :
    C90LevelGeneralPackage X where
  ell := C.ell
  ell_pos := C.ell_pos
  polygon_oneSided := C.polygon_oneSided
  root_value := C.root_value
  initial_equiv := C.initial_equiv
  degree_eq := C.degree_eq
  repo_residual_power := by
    intro i hi
    rw [← D.residual_compat i hi G, C.residual_power i hi, Polynomial.map_pow,
      D.psi_compat i hi]
  length_recurrence := by
    intro i hi
    rw [C.length_recurrence i hi, D.ramification_compat i hi.stageLive,
      D.residueDegree_compat i hi.stageLive]

end Uniformity.Density.Tower.LevelGeneralCheck

#print axioms Uniformity.Density.Tower.LevelGeneralCheck.Cor63Conclusion.toC90
