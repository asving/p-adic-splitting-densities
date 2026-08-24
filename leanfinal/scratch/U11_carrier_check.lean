import Uniformity.ChapC.C130f
import Uniformity.ChapC.C53b
import Uniformity.ChapC.C80
import Uniformity.ChapC.C97
import Uniformity.ChapI.I10FreezeV2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

/-!
Elaboration check for U11's proposed layered MacLane-chain realization carrier.
This is a scratch signature check, not a landed chapter declaration.
-/

namespace Uniformity.Density.Tower.U11

open Uniformity.Density.Leaf
open Uniformity.Density.Tower

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- OPEN-DICT-1 and C.130b: the polynomial keys are a layer over `DeepTower`. -/
structure KeyChain (W : DeepTower.{0, uKt} F H₀ hpin r) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_monic : ∀ i, StageLive r i → (keyAt i).Monic
  keyAt_degree : ∀ i, StageLive r i → (keyAt i).natDegree = W.Dcum i

/-- EFF.T2.07 and EFF.GENTOW5.15: an honest integer/Laurent normalizer.
It is intentionally not required to equal C.83's truncated-natural `towerNorm` on all
nonnegative inputs. -/
structure LaurentNormalizer (W : DeepTower.{0, uKt} F H₀ hpin r) where
  norm : (i : ℕ) → ℤ → LevelExponentLattice i
  norm_zero : ∀ i, norm i 0 = 1
  exact_height : ∀ i, StageLive r i → ∀ k : ℤ,
    levelExponentHeight W i (norm i k) = Multiplicative.ofAdd k

/-- EFF.T2.04/.05/.09/.11 and DEF GENTOW5-1's legal node-point data.
The pointwise reads witness that `hgt` and `dig` are not freely chosen tables.  The two
Laurent reads are deliberately separate; no field equates them. -/
structure NodePointSource
    (W : DeepTower.{0, uKt} F H₀ hpin r)
    {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
    (receiver : TerminalReceiver F H₀ hpin r W Kt) (K : KeyChain W) where
  Point : Type
  Pt : ℕ → Point → Prop
  point_exists : ∀ i, StageLive r i → Nonempty {x : Point // Pt i x}
  coeffHom : O →+* L
  coord : Point → L
  valueOn : ℕ → L → WithTop ℤ
  value_zero : ∀ i, StageLive r i → valueOn i 0 = ⊤
  value_mul : ∀ i, StageLive r i → ∀ a b,
    valueOn i (a * b) = valueOn i a + valueOn i b
  value_add_ge : ∀ i, StageLive r i → ∀ a b,
    min (valueOn i a) (valueOn i b) ≤ valueOn i (a + b)
  value_add_eq : ∀ i, StageLive r i → ∀ a b,
    valueOn i a ≠ valueOn i b →
      valueOn i (a + b) = min (valueOn i a) (valueOn i b)

  hgt : ℕ → Polynomial O → WithTop ℤ
  dig : (i : ℕ) → Polynomial O → W.fld i
  pointHgt : ℕ → Point → Polynomial O → WithTop ℤ
  pointDig : (i : ℕ) → Point → Polynomial O → W.fld i
  pointHgt_eval : ∀ i x A,
    pointHgt i x A = valueOn i (Polynomial.eval₂ coeffHom (coord x) A)
  slot_value : ∀ i (_hi : StageLive r i) (x : Point), Pt i x →
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < W.Dcum i → pointHgt i x A = hgt i A
  slot_digit : ∀ i (_hi : StageLive r i) (x : Point), Pt i x →
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < W.Dcum i → pointDig i x A = dig i A

  hgt_zero : ∀ i, StageLive r i → hgt i 0 = ⊤
  dig_zero : ∀ i, StageLive r i → dig i 0 = 0
  hgt_ne_top : ∀ i, StageLive r i → ∀ A : Polynomial O,
    A ≠ 0 → A.natDegree < W.Dcum i → hgt i A ≠ ⊤
  dig_ne_zero : ∀ i, StageLive r i → ∀ A : Polynomial O,
    A ≠ 0 → A.natDegree < W.Dcum i → dig i A ≠ 0
  hgt_add_ge : ∀ i, StageLive r i → ∀ A B,
    min (hgt i A) (hgt i B) ≤ hgt i (A + B)
  hgt_add_eq : ∀ i, StageLive r i → ∀ A B,
    hgt i A ≠ hgt i B → hgt i (A + B) = min (hgt i A) (hgt i B)
  dig_add : ∀ i, StageLive r i → ∀ A B : Polynomial O, ∀ k : ℤ,
    hgt i A = (k : WithTop ℤ) → hgt i B = (k : WithTop ℤ) →
    dig i A + dig i B ≠ 0 →
      hgt i (A + B) = (k : WithTop ℤ) ∧ dig i (A + B) = dig i A + dig i B
  Full : ℕ → ℤ → Prop
  lift : ∀ i, StageLive r i → ∀ k : ℤ, Full i k → ∀ c : W.fld i, c ≠ 0 →
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < W.Dcum i ∧
      hgt i A = (k : WithTop ℤ) ∧ dig i A = c

  /-- EFF.T2.04/.11: inherited integer input, not a function inferred from `(W,i,F₀)`. -/
  thresholdZ : ℕ → ℤ
  /-- Repo dictionary to E.11's current natural-valued `BlockData.T`. -/
  thresholdNat : ℕ → ℕ
  threshold_nonneg : ∀ i, StageLive r i → (thresholdNat i : ℤ) = thresholdZ i
  window : ∀ i, StageLive r i → ∀ x : Point, Pt i x →
    (thresholdZ i : WithTop ℤ) < pointHgt i x (K.keyAt i) ∧
      pointHgt i x (K.keyAt i) ≠ ⊤

  /-- EFF.GENTOW5 S2.1/S2.3: the ambient node-point letters. -/
  ambientLetter : ℕ → Lˣ
  key_value : ∀ i, GaugeLive r i → ∀ x : Point, Pt i x →
    pointHgt i x (K.keyAt i) = (W.u (i + 1) : WithTop ℤ)
  psi_root : ∀ i, GaugeLive r i →
    Polynomial.eval₂ ((algebraMap Kt L).comp (receiver.levelHom i))
      (ambientLetter i : L) (W.ψ i) = 0
  /-- EFF.T1.01 and EFF.GENTOW5 S2.3 step (3): the L-valued node read. -/
  canonicalRead : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Lˣ
  /-- D.07/D.08, D.44 and EFF.T3.21: the separate terminal-field W-leg read. -/
  arenaRead : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Ktˣ
  towerRead : (i : ℕ) → LevelExponentLattice i → Kt
  peelUnit : ℕ → Ktˣ

/-- The source-side next-augmentation objects behind A-C.11.  In particular the graded
residual is polynomial-valued; the scalar `Rgr` consumer will be its coefficient zero. -/
structure FGMNSourceData (W : DeepTower.{0, uKt} F H₀ hpin r)
    (K : KeyChain W) (e' f' u' : ℕ) where
  nextValue : Polynomial O → WithTop ℤ
  gradedResidual : ℕ → Polynomial O → Polynomial (W.fld r)
  normalizedResidual : Polynomial O → Polynomial (W.fld r)
  keyPolynomial : Polynomial O → Prop
  initialEquiv : Polynomial O → Polynomial O → Prop
  letter : ℕ → W.fld r

namespace FGMNSourceData

def ExactGrade {W : DeepTower.{0, uKt} F H₀ hpin r} {K : KeyChain W}
    {e' f' u' : ℕ} (S : FGMNSourceData W K e' f' u')
    (β : ℕ) (g : Polynomial O) : Prop :=
  S.nextValue g = (β : WithTop ℤ)

def AboveGrade {W : DeepTower.{0, uKt} F H₀ hpin r} {K : KeyChain W}
    {e' f' u' : ℕ} (S : FGMNSourceData W K e' f' u')
    (β : ℕ) (g : Polynomial O) : Prop :=
  (β : WithTop ℤ) < S.nextValue g

end FGMNSourceData

/-- The published FGMN obligations, stated on source objects rather than by copying the
scalar consumer interface.  Each field is discharged by the cited FGMN clause after the
OPEN-DICT transports are proved. -/
structure FGMNSourceLaws (W : DeepTower.{0, uKt} F H₀ hpin r)
    (K : KeyChain W) (e' f' u' : ℕ) (S : FGMNSourceData W K e' f' u') where
  graded_zero_of_above : ∀ β (g : Polynomial O),
    S.AboveGrade β g → S.gradedResidual β g = 0
  graded_add : ∀ β (g h : Polynomial O),
    S.ExactGrade β g → S.ExactGrade β h → S.ExactGrade β (g + h) →
      S.gradedResidual β (g + h) = S.gradedResidual β g + S.gradedResidual β h
  graded_mul : ∀ β β' (g h : Polynomial O),
    S.ExactGrade β g → S.ExactGrade β' h →
      S.ExactGrade (β + β') (g * h) ∧
      S.gradedResidual (β + β') (g * h) =
        S.gradedResidual β g * S.gradedResidual β' h
  graded_scalar_nonzero : ∀ β (g : Polynomial O),
    S.ExactGrade β g → g.natDegree < (K.keyAt r).natDegree → g ≠ 0 →
      (S.gradedResidual β g).coeff 0 ≠ 0
  normalized_mul : ∀ g h : Polynomial O,
    S.normalizedResidual (g * h) = S.normalizedResidual g * S.normalizedResidual h
  normalized_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → S.ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (K.keyAt r).natDegree) →
    S.normalizedResidual ((K.keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (K.keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
        Polynomial.C ((S.gradedResidual ((f' - t) * u') (khat t)).coeff 0) *
          Polynomial.X ^ t
  normalized_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → Irreducible ψ → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O, g.Monic ∧
        g.natDegree = e' * f' * (K.keyAt r).natDegree ∧
        S.normalizedResidual g = ψ
  key_criterion : ∀ g : Polynomial O, g.Monic →
    g.natDegree = e' * f' * (K.keyAt r).natDegree →
    Irreducible (S.normalizedResidual g) →
    (S.normalizedResidual g).natDegree = f' →
    (S.normalizedResidual g).coeff 0 ≠ 0 → S.keyPolynomial g
  key_irreducible : ∀ g : Polynomial O,
    S.keyPolynomial g → g.Monic → Irreducible g
  carried_key_is_key : 0 < r → S.keyPolynomial (K.keyAt r)
  carried_key_residual : 0 < r → S.normalizedResidual (K.keyAt r) = 1
  initial_iff_residual : ∀ g h : Polynomial O,
    S.keyPolynomial g → S.keyPolynomial h →
      (S.initialEquiv g h ↔ S.normalizedResidual g = S.normalizedResidual h)
  letter_ne_zero : ∀ i, 1 ≤ i → i ≤ r → S.letter i ≠ 0

/-- The decided carrier: a conservative layer over `DeepTower`, reusing the freeze's
`TerminalReceiver`. -/
structure ChainRealization
    (W : DeepTower.{0, uKt} F H₀ hpin r)
    (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L]
    (e' f' u' : ℕ) where
  receiver : TerminalReceiver F H₀ hpin r W Kt
  keys : KeyChain W
  normalizer : LaurentNormalizer W
  node : NodePointSource (L := L) W receiver keys
  fgmn : FGMNSourceData W keys e' f' u'
  fgmnLaws : FGMNSourceLaws W keys e' f' u' fgmn
  /-- OPEN-DICT-2: the cleared next-valuation convention agrees with the legal point read. -/
  grade_compat : ∀ x : node.Point, node.Pt r x → ∀ g : Polynomial O,
    fgmn.nextValue g = node.pointHgt r x g
  /-- OPEN-DICT-4: FGMN's transported `z_i` is the same ambient node letter. -/
  letter_compat : ∀ i, StageLive r i →
    algebraMap Kt L (receiver.topEquiv (fgmn.letter i)) = (node.ambientLetter i : L)

/-- Input-specific C.130j layer.  It reuses `ArisingCore`; the only new fields are
dictionary equalities and the selected legal point, never a socket conclusion. -/
structure RealizedInput
    {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
    {n e' f' u' : ℕ} (core : ArisingCore Kt L n)
    (A : ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin)
      core.T Kt L e' f' u') where
  receiver_eq : A.receiver = core.receiver
  stageKey_eq : core.stageKey = A.keys.keyAt core.i
  stageDeg_eq : core.stageDeg = core.T.Dcum core.i
  point : A.node.Point
  point_mem : A.node.Pt core.i point

/-! The following local class repeats A-C.11 solely so that the proposed projection map is
checked in this scratch file. -/

class FGMNCalculusCheck (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i
  ExactGrade : ℕ → Polynomial O → Prop
  AboveGrade : ℕ → Polynomial O → Prop
  Rgr : ℕ → Polynomial O → W.fld r
  Rres : Polynomial O → Polynomial (W.fld r)
  KP : Polynomial O → Prop
  nuEquiv : Polynomial O → Polynomial O → Prop
  letterZ : ℕ → W.fld r
  Rgr_zero_of_above : ∀ β g, AboveGrade β g → Rgr β g = 0
  Rgr_add : ∀ β g h, ExactGrade β g → ExactGrade β h → ExactGrade β (g + h) →
    Rgr β (g + h) = Rgr β g + Rgr β h
  Rgr_mul : ∀ β β' g h, ExactGrade β g → ExactGrade β' h →
    ExactGrade (β + β') (g * h) ∧ Rgr (β + β') (g * h) = Rgr β g * Rgr β' h
  Rgr_ne_zero : ∀ β g, ExactGrade β g → g.natDegree < (keyAt r).natDegree →
    g ≠ 0 → Rgr β g ≠ 0
  Rres_mul : ∀ g h, Rres (g * h) = Rres g * Rres h
  Rres_recipe : ∀ khat : ℕ → Polynomial O,
    (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
    Rres ((keyAt r) ^ (e' * f') - ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
        Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
  Rres_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → Irreducible ψ → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O, g.Monic ∧
        g.natDegree = e' * f' * (keyAt r).natDegree ∧ Rres g = ψ
  KP_criterion : ∀ g, g.Monic → g.natDegree = e' * f' * (keyAt r).natDegree →
    Irreducible (Rres g) → (Rres g).natDegree = f' → (Rres g).coeff 0 ≠ 0 → KP g
  KP_irred : ∀ g, KP g → g.Monic → Irreducible g
  KP_keyAt : 0 < r → KP (keyAt r)
  Rres_keyAt : 0 < r → Rres (keyAt r) = 1
  nuEquiv_iff_Rres : ∀ g h, KP g → KP h → (nuEquiv g h ↔ Rres g = Rres h)
  letterZ_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0

/-- The U9 bridge is packaging plus coefficient-zero projection; it is not a new cite. -/
@[implicit_reducible] def ChainRealization.toCalculus
    {W : DeepTower.{0, uKt} F H₀ hpin r}
    {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
    {e' f' u' : ℕ} (A : ChainRealization W Kt L e' f' u') :
    FGMNCalculusCheck W e' f' u' where
  keyAt := A.keys.keyAt
  keyAt_one := A.keys.keyAt_one
  keyAt_deg := fun i hi hir => A.keys.keyAt_degree i ⟨hi, hir⟩
  ExactGrade := A.fgmn.ExactGrade
  AboveGrade := A.fgmn.AboveGrade
  Rgr := fun β g => (A.fgmn.gradedResidual β g).coeff 0
  Rres := A.fgmn.normalizedResidual
  KP := A.fgmn.keyPolynomial
  nuEquiv := A.fgmn.initialEquiv
  letterZ := A.fgmn.letter
  Rgr_zero_of_above := fun β g hg => by rw [A.fgmnLaws.graded_zero_of_above β g hg]; simp
  Rgr_add := fun β g h hg hh hgh => by rw [A.fgmnLaws.graded_add β g h hg hh hgh]; simp
  Rgr_mul := fun β β' g h hg hh => by
    obtain ⟨hexact, hmul⟩ := A.fgmnLaws.graded_mul β β' g h hg hh
    refine ⟨hexact, ?_⟩
    rw [hmul]
    simp
  Rgr_ne_zero := A.fgmnLaws.graded_scalar_nonzero
  Rres_mul := A.fgmnLaws.normalized_mul
  Rres_recipe := A.fgmnLaws.normalized_recipe
  Rres_exists := A.fgmnLaws.normalized_exists
  KP_criterion := A.fgmnLaws.key_criterion
  KP_irred := A.fgmnLaws.key_irreducible
  KP_keyAt := A.fgmnLaws.carried_key_is_key
  Rres_keyAt := A.fgmnLaws.carried_key_residual
  nuEquiv_iff_Rres := A.fgmnLaws.initial_iff_residual
  letterZ_ne_zero := A.fgmnLaws.letter_ne_zero

theorem chainRealization_calculus_nonempty
    {W : DeepTower.{0, uKt} F H₀ hpin r}
    {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
    {e' f' u' : ℕ} (A : ChainRealization W Kt L e' f' u') :
    Nonempty (FGMNCalculusCheck W e' f' u') :=
  ⟨A.toCalculus⟩

/-! A real depth-two key-chain regression.  This does not fake the still-open node-point,
Laurent-normalizer, or FGMN source obligations; it checks that the landed `s2Tower` key and
the landed `s2Witness` truncation fit the structural layer exactly. -/

namespace DepthTwoCheck

open Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C80

variable [Finite (IsLocalRing.ResidueField O)]

noncomputable def s2DepthTwo (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2 :=
  (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 2 (by omega)

noncomputable def s2DepthTwoKeyAt (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (i : ℕ) : Polynomial O :=
  if i = 1 then (s2Frame h2 hq).key else composedKey (s2Tower h2 hq)

noncomputable def s2DepthTwoKeyChain (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) : KeyChain (s2DepthTwo h2 hq) where
  keyAt := s2DepthTwoKeyAt h2 hq
  keyAt_one := by simp [s2DepthTwoKeyAt]
  keyAt_monic := by
    intro i hi
    rcases hi with ⟨hi1, hi2⟩
    interval_cases i
    · simpa [s2DepthTwoKeyAt] using (s2Frame h2 hq).hmonic
    · simpa [s2DepthTwoKeyAt] using composedKey_monic (s2Tower h2 hq)
  keyAt_degree := by
    intro i hi
    rcases hi with ⟨hi1, hi2⟩
    interval_cases i
    · rw [show s2DepthTwoKeyAt h2 hq 1 = (s2Frame h2 hq).key by
        simp [s2DepthTwoKeyAt]]
      rw [(s2Frame h2 hq).hdeg, DeepTower.Dcum,
        show (Finset.Icc 1 1 : Finset ℕ) = {1} by decide, Finset.prod_singleton,
        (s2DepthTwo h2 hq).he1, (s2DepthTwo h2 hq).hf1]
    · rw [show s2DepthTwoKeyAt h2 hq 2 = composedKey (s2Tower h2 hq) by
        simp [s2DepthTwoKeyAt]]
      rw [composedKey_natDegree_D₂ (s2Tower h2 hq) h2]
      rw [DeepTower.Dcum, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
        Finset.prod_insert (by decide), Finset.prod_singleton,
        (s2DepthTwo h2 hq).he1, (s2DepthTwo h2 hq).hf1]
      rfl

end DepthTwoCheck

end Uniformity.Density.Tower.U11
