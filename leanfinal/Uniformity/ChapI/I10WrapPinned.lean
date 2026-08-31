/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Uniformity.ChapI.I10PinnedBoundary

/-!
# Uniformity.ChapI.I10WrapPinned — row R5 at pinned normalizers: SETTLED NEGATIVE
[R5P 2026-08-31]

## THE SETTLEMENT (charge 1): the normalizer pin does NOT rescue the wrap clause

Post-A-I.9 both capstone vartheta halves rest on `UniversalPinnedGeneratorDescent`
(row R5 at `NormalizerPinned` witnesses).  The unit charge conjectured that TAU's wrap
separation witness — the χ-twist — is EXCLUDED by the pin.  **It is not**: C130s18's
`twistRealization` moves ONLY `node.canonicalRead`; its `normalizer` field is
`rfl`-unchanged (`twistRealization_normalizer`), so the χ-twisted witness of a pinned
witness is STILL pinned (`twistRealization_normalizerPinned` below — the machine form of
the settlement).  TAU's ★ `wrapDescentAt_not_uniform` already quantified its `huniform`
over pinned realizations; what it left open was the existence of a character with an
unembedded wrap-class value.  §1 CLOSES that gap: the wrap generator
`W₀ = x^{e₁}·π^{−u₁}` is a PRIMITIVE lattice vector (frame coprimality
`gcd(e₁, u₁) = 1`), so a Bézout coordinate functional hits it at exponent exactly `1`,
and `DeepTower.exists_wrapChar` produces, for ANY target unit `g : Lˣ`, a character
family `χ` with `χ i (W₀-class) = g` — every tower, every stage-live level, uniform in `q`.

## THE REFUTATION (charge 2 is IMPOSSIBLE): ★★ `s2Four_not_universalPinnedGeneratorDescent`

Feeding an unembedded `g` (e.g. `RatFunc.X` over the keystone terminal field — the
`uL = 0` corollary discharges the existence) through `exists_wrapChar` into TAU's
`wrapDescentAt_not_uniform` at the landed depth-4 keystone refutes
`UniversalPinnedGeneratorDescent n` outright: **row R5 is FALSE at pinned witnesses**, at
every degree hosting a keystone occurrence.  This is the exact successor of TAU's
stop-line `s2Four_not_universalKernelSpan`, one guard deeper: after the normalizer pin
excluded the lattice twist, the READ freedom (`canonicalRead`, protected by the
non-swallowing fence) still defeats the universal wrap clause.  Conditionality: exactly
the landed keystone theorems' (S2 hypotheses + four thresholds + R8/R8r payload; if no
such instance existed the refutation would be vacuous — the standing wired-genre
disclosure).

**Consequence for the boundary**: I10PinnedBoundary's ★★
`deepTwistField_of_pinned_descent_site` and ★★
`ladderVarthetaSupplierLive_of_pinned_descent` remain valid implications but are provably
UNDISCHARGEABLE through their `UniversalPinnedGeneratorDescent` premise.  A further
structural guard is REQUIRED (owner-amendment territory, O-R5P below), exactly as TAU's
refutation forced A-I.9.

## THE REPAIR SHAPE (charge 3, the honest residue): the descent guard — O-R5P (flagged,
NOT enacted)

§3 lands the doubly-guarded boundary: `DescentPinned Aℛ` (row R5's content as a
per-realization GUARD: `CanonicalGeneratorDescent` at every deep-live level) and ★★
`universalDoublyPinnedTauSupply` — under {`NormalizerPinned`, `DescentPinned`} the WHOLE
per-witness tau supply is an UNCONDITIONAL THEOREM (zero residue: the span leg is free
under the normalizer pin, the descent leg IS the guard).  The keystone satisfies both
guards by construction (`s2Four_descentPinned` — the landed
`s2Four_canonicalGeneratorDescent`; the pin is TWD's `rfl`), and the χ-twist that defeats
the universal FAILS the descent guard at exactly the wrap clause
(`s2FourTwisted_not_descentPinned` — the new guard has teeth where the normalizer pin has
none).  **O-R5P** (the flagged amendment, the exact A-I.9 genre one field deeper): conjoin
`DescentPinned` into `DeepTwistRealizationData` and the ladder live guard; under it the
tau boundary of BOTH capstone vartheta halves VANISHES (the §3 theorem), the sockets
re-fire at every landed witness, and the χ-twist is excluded — as designed.  NOT enacted
here: socket-body changes are the owner/orchestrator's A-I.9-genre calls, not this
unit's.

## Honesty scope

Nothing here weakens any signed statement.  The refutation is supplier-side (the Prop
refuted is TAU's `UniversalPinnedGeneratorDescent`, below the signed surface) and carries
the standing keystone conditionality.  OPEN QUESTION (flagged, not settled): whether the
same χ mechanism reaches the vartheta ELEMENTS (not just the wrap class) at the keystone
— if it does, `IFC0.DeepTwistField` itself is refutable through G10U's landed converse
`universalPinnedVartheta_of_deepTwistField`, which would make the signed `deepTwist`
capstone hypothesis unsatisfiable pre-O-R5P.  That computation (the vartheta words'
digit vectors at the keystone heights) is a separate unit; O-R5P repairs both surfaces
either way.

Cite ledger: **empty** — Lean core over the landed corpus (the one Mathlib import,
`RatFunc`, is instance plumbing for the `uL = 0` witness).  `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_R5P.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

/-! ## §1 The wrap character: a Bézout functional hits the primitive wrap generator -/

namespace Uniformity.Density.Tower

open scoped BigOperators
open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {L : Type uL} [Field L]

/-- The `(c₁, c₂)` coordinate functional on the Laurent exponent lattice:
`z ↦ c₁·(π-exponent) + c₂·(x-exponent)`, multiplicatively.  Kills every letter
coordinate. -/
def coordFunctional (c₁ c₂ : ℤ) (i : ℕ) :
    LevelExponentLattice i →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd
    (c₁ * (Multiplicative.toAdd z).1 + c₂ * (Multiplicative.toAdd z).2.1)
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add]
    ring

/-- Anti-drift pin: the functional's value on an explicit exponent vector. -/
theorem coordFunctional_ofAdd (c₁ c₂ : ℤ) (i : ℕ) (a b : ℤ) (t : Fin (i - 1) → ℤ) :
    coordFunctional c₁ c₂ i (Multiplicative.ofAdd (a, b, t)) =
      Multiplicative.ofAdd (c₁ * a + c₂ * b) := rfl

/-- **The `(c₁, c₂, g)`-character on the level kernels**: the coordinate functional
restricted to the level-`i` kernel, followed by `g^·`.  A monoid-hom family of exactly
the shape `twistRealization` consumes — for EVERY tower, level by level. -/
def DeepTower.coordChar (T : DeepTower F H₀ hpin r) (c₁ c₂ : ℤ) (g : Lˣ) (i : ℕ) :
    MonoidHom.ker (levelExponentHeight T i) →* Lˣ :=
  (zpowersHom Lˣ g).comp
    ((coordFunctional c₁ c₂ i).comp (MonoidHom.ker (levelExponentHeight T i)).subtype)

/-- The character's value at the wrap class: the wrap generator's exponent vector is
`(−u₁, e₁, 0)`, so the value is `g^(c₁·(−u₁) + c₂·e₁)`. -/
theorem DeepTower.coordChar_wrapClass (T : DeepTower F H₀ hpin r) (c₁ c₂ : ℤ) (g : Lˣ)
    {i : ℕ} (hi : StageLive r i) :
    T.coordChar c₁ c₂ g i (T.wrapClass hi) =
      g ^ (c₁ * (-(T.u 1 : ℤ)) + c₂ * (T.e 1 : ℤ)) := rfl

/-- ★ **THE WRAP CHARACTER EXISTS** — for every tower, every stage-live level, and every
target unit `g : Lˣ`, a character family hitting the wrap class at exactly `g`.  The
mechanism: `W₀ = x^{e₁}·π^{−u₁}` is PRIMITIVE in the `(π, x)`-plane by the frame
coprimality `gcd(e₁, u₁) = 1` (the same pin that closes TWD's spanning base case), so a
Bézout pair `(a, b)` with `a·e₁ + b·u₁ = 1` yields the functional `(−b, a)` with value
`1` at `W₀`.  Uniform in `q` — no residue field, no read, no keystone numerics. -/
theorem DeepTower.exists_wrapChar (T : DeepTower F H₀ hpin r) {i : ℕ}
    (hi : StageLive r i) (g : Lˣ) :
    ∃ χ : (i' : ℕ) → (MonoidHom.ker (levelExponentHeight T i') →* Lˣ),
      χ i (T.wrapClass hi) = g := by
  have hcopZ : IsCoprime ((T.e 1 : ℤ)) ((T.u 1 : ℤ)) := by
    rw [T.he1, T.hu1]
    exact (Nat.isCoprime_iff_coprime.mpr F.hcop).symm
  obtain ⟨a, b, hab⟩ := hcopZ
  refine ⟨fun i' => T.coordChar (-b) a g i', ?_⟩
  rw [T.coordChar_wrapClass (-b) a g hi]
  have hexp : (-b) * (-(T.u 1 : ℤ)) + a * (T.e 1 : ℤ) = 1 := by linear_combination hab
  rw [hexp, zpow_one]

end Uniformity.Density.Tower

/-! ## §2 The settlement and the refutation -/

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

section Settlement

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}

/-- **[R5P settlement, machine form] The normalizer pin does NOT exclude the χ-twist**:
the χ-twisted witness of a pinned witness is still pinned (the twist moves only
`node.canonicalRead`; `twistRealization_normalizer` is `rfl`).  So A-I.9's amended
sockets RECEIVE the χ-twisted witness, and the unit charge's hoped-for exclusion fails
— the wrap clause stays per-realization supply behind the pin. -/
theorem twistRealization_normalizerPinned
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    (hN : NormalizerPinned Aℛ) :
    NormalizerPinned (C130s18.twistRealization Aℛ χ) := hN

end Settlement

section Wired

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130s18
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)
variable {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ)
  (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
  (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
    ((g16 h2 hq).map (algebraMap O (FractionRing O))))

include h2 hq w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop in
/-- ★★ **[R5P] THE REFUTATION — row R5 is FALSE at pinned witnesses**:
`UniversalPinnedGeneratorDescent n` (the single tau remainder of BOTH capstone vartheta
halves after A-I.9, `I10PinnedBoundary`) fails at every degree hosting a depth-4 keystone
occurrence, for any coefficient field `L` with a unit outside the embedded terminal
subfield.  Mechanism: the §1 wrap character hands TAU's `wrapDescentAt_not_uniform` the
unembedded wrap-class value it was parametric in, and the χ-twisted keystone witness is
PINNED (`twistRealization_normalizerPinned`), so the universal's own instance at it
yields the contradiction.  The exact successor of TAU's stop-line
`s2Four_not_universalKernelSpan`, one guard deeper.  Conditionality: exactly the landed
keystone theorems' (standing wired-genre disclosure). -/
theorem s2Four_not_universalPinnedGeneratorDescent
    (g : Lˣ) (hg : ∀ y : (s2DepthFour h2 hq).fld 4,
      ((g : Lˣ) : L) ≠ algebraMap ((s2DepthFour h2 hq).fld 4) L y) :
    ¬ UniversalPinnedGeneratorDescent.{0, uL} n := by
  intro h
  have hj : GaugeLive 4 3 := ⟨by omega, by omega⟩
  have hjd : DeepLive 4 3 := ⟨le_rfl, by omega⟩
  obtain ⟨χ, hχ⟩ := DeepTower.exists_wrapChar
    (T := (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop).T) hj.stageLive g
  exact wrapDescentAt_not_uniform
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) hj
    (s2Four_normalizer_eq_laurent h2 hq L w₁ w₂ w₃ w₄) χ
    (fun y => by rw [hχ]; exact hg y)
    (fun A' X' hN' =>
      (h O ((s2DepthFour h2 hq).fld 4) (FractionRing (Polynomial O)) L
        (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop) A' X' hN' 3 hjd).wrap)

include h2 hq w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop in
/-- ★★ **[R5P] The `uL = 0` instantiation — the unembedded-unit hypothesis is
DISCHARGEABLE**: over `L := RatFunc Kt` (the rational-function field of the keystone's
terminal residue field) the indeterminate `X` is a unit outside the embedded subfield, so
`UniversalPinnedGeneratorDescent` is refuted OUTRIGHT at the keystone conditionality —
no free choice of `L` remains in the statement. -/
theorem s2Four_not_universalPinnedGeneratorDescent₀ :
    ¬ UniversalPinnedGeneratorDescent.{0, 0} n :=
  s2Four_not_universalPinnedGeneratorDescent h2 hq
    (RatFunc ((s2DepthFour h2 hq).fld 4)) w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
    (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
    (fun y => by
      show (RatFunc.X : RatFunc ((s2DepthFour h2 hq).fld 4)) ≠ algebraMap _ _ y
      intro hxy
      have hX : (RatFunc.X : RatFunc ((s2DepthFour h2 hq).fld 4))
          = algebraMap (Polynomial ((s2DepthFour h2 hq).fld 4)) _ Polynomial.X := rfl
      have hC : algebraMap ((s2DepthFour h2 hq).fld 4)
            (RatFunc ((s2DepthFour h2 hq).fld 4)) y
          = algebraMap (Polynomial ((s2DepthFour h2 hq).fld 4)) _ (Polynomial.C y) := by
        rw [IsScalarTower.algebraMap_apply ((s2DepthFour h2 hq).fld 4)
          (Polynomial ((s2DepthFour h2 hq).fld 4))
          (RatFunc ((s2DepthFour h2 hq).fld 4)), Polynomial.algebraMap_eq]
      rw [hX, hC] at hxy
      exact Polynomial.X_ne_C y (RatFunc.algebraMap_injective _ hxy))

end Wired

/-! ## §3 The honest repair: the descent guard, and the ZERO-residue tau boundary under
it (O-R5P shape — flagged for the owner/orchestrator, NOT enacted) -/

section Repair

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}

/-- **[R5P repair] The descent guard** — row R5's content as a per-realization GUARD:
`CanonicalGeneratorDescent` at every deep-live level.  Refuted as a universal supply even
at pinned witnesses (★★ above), so — exactly like TAU's `NormalizerPinned` after
`s2Four_not_universalPinning` — it can only enter as a structural socket conjunct
(**O-R5P**, the A-I.9 genre one field deeper: conjoin into
`DeepTwistRealizationData` and `IFC5.CanonicalLadderLiveAt`).  True at every landed
witness by construction (`s2Four_descentPinned` below).  NEW STATEMENT (review). -/
def DescentPinned
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L) : Prop :=
  ∀ j, (hj : DeepLive core.r j) → CanonicalGeneratorDescent Aℛ j hj.gaugeLive

/-- Under BOTH guards the per-witness tau supply is a theorem (TAU's compilation,
restated at the guard pair). -/
theorem tauWordDescentSupply_of_guards
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hN : NormalizerPinned Aℛ) (hD : DescentPinned Aℛ) :
    TauWordDescentSupply.{uG, uKt, uL} X :=
  tauWordDescentSupply_of_pinned_descent X hN hD

end Repair

/-- **[R5P repair] The doubly-guarded universal tau supply** — the O-R5P analogue of
TAU's `UniversalPinnedTauWordDescentSupply`: the tau supply at every realization carrying
BOTH the normalizer pin and the descent guard.  NEW STATEMENT (review). -/
def UniversalDoublyPinnedTauWordDescentSupply (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ), NormalizerPinned Aℛ → DescentPinned Aℛ →
    TauWordDescentSupply.{uG, uKt, uL} X

/-- ★★ **[R5P] THE ZERO-RESIDUE BOUNDARY UNDER O-R5P** — the doubly-guarded universal
tau supply is an UNCONDITIONAL THEOREM: the kernel-span leg is free under the normalizer
pin (`kernelSpanAt_of_laurent`), and the descent leg IS the guard.  So after the
refutation above, the honest tau boundary of both capstone vartheta halves is exactly
the STRUCTURAL question of O-R5P (conjoin `DescentPinned` into the two A-I.9-amended
receive points) — no per-witness tau mathematics remains open behind the guards. -/
theorem universalDoublyPinnedTauSupply (n : ℕ) :
    UniversalDoublyPinnedTauWordDescentSupply.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X hN hD
  exact tauWordDescentSupply_of_pinned_descent X hN hD

/-! ## §4 Keystone teeth: the landed witness carries BOTH guards; the χ-twist fails
exactly the new one -/

section WiredTeeth

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130s18
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)
variable {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ)
  (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
  (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
    ((g16 h2 hq).map (algebraMap O (FractionRing O))))

/-- **[R5P tooth] The keystone witness carries the normalizer pin** (TWD's `rfl`,
restated at the guard `Prop`). -/
theorem s2Four_normalizerPinned :
    NormalizerPinned (core := s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) := rfl

/-- ★ **[R5P tooth] The keystone witness carries the descent guard** — O-R5P's socket
conjunct would RE-FIRE at the landed witness (the landed
`s2Four_canonicalGeneratorDescent` at the sole deep-live level).  Conditionality: exactly
the landed keystone theorems'. -/
theorem s2Four_descentPinned :
    DescentPinned (core := s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) :=
  fun j hj => s2Four_canonicalGeneratorDescent h2 hq L w₁ w₂ w₃ w₄
    F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive

include h2 hq w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop in
/-- ★ **[R5P tooth] The χ-twist FAILS the descent guard** (at an unembedded wrap-class
value) — the O-R5P conjunct excludes exactly the witness genre that defeats the
universal, where the normalizer pin (`twistRealization_normalizerPinned`) excludes
nothing.  The design tooth for the flagged amendment. -/
theorem s2FourTwisted_not_descentPinned (hj : DeepLive 4 3)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight
      (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop).T i) →* Lˣ)
    (hχ : ∀ y : (s2DepthFour h2 hq).fld 4,
      ((χ 3 ((s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock
          hcop).T.wrapClass hj.gaugeLive.stageLive) : Lˣ) : L)
        ≠ algebraMap ((s2DepthFour h2 hq).fld 4) L y) :
    ¬ DescentPinned (core := s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (twistRealization (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) χ) := by
  intro hD
  obtain ⟨u₂, hu₂⟩ := (hD 3 hj).wrap
  obtain ⟨u₁, hu₁⟩ := (s2Four_canonicalGeneratorDescent h2 hq L w₁ w₂ w₃ w₄
    F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive).wrap
  rw [twistRealization_wrapValue χ hj.gaugeLive.stageLive, hu₁] at hu₂
  refine hχ ((u₂ : (s2DepthFour h2 hq).fld 4) * (u₁ : (s2DepthFour h2 hq).fld 4)⁻¹) ?_
  have hval : ((χ 3 ((s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock
          hcop).T.wrapClass hj.gaugeLive.stageLive) : Lˣ) : L)
      = ((unitAlgebraMap u₂ * (unitAlgebraMap u₁)⁻¹ : Lˣ) : L) := by
    rw [← hu₂]
    simp [mul_comm]
  rw [hval]
  simp [unitAlgebraMap, map_mul, map_inv₀]

/-- **[R5P tooth, coherence] The keystone's tau supply re-derived through the REPAIR
chain** — the doubly-guarded route reproduces USUP/TWD's landed keystone supply from the
two guard teeth alone (the repair is non-vacuous exactly where the campaign needs it). -/
theorem s2Four_tauWordDescentSupply'' :
    TauWordDescentSupply.{uG, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  tauWordDescentSupply_of_guards
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2Four_normalizerPinned h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2Four_descentPinned h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)

end WiredTeeth

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core only. -/

section AxCheck1

#print axioms Uniformity.Density.Tower.coordFunctional
#print axioms Uniformity.Density.Tower.DeepTower.coordChar
#print axioms Uniformity.Density.Tower.DeepTower.coordChar_wrapClass
#print axioms Uniformity.Density.Tower.DeepTower.exists_wrapChar
#print axioms Uniformity.Density.DeepExport.twistRealization_normalizerPinned
#print axioms Uniformity.Density.DeepExport.s2Four_not_universalPinnedGeneratorDescent
#print axioms Uniformity.Density.DeepExport.s2Four_not_universalPinnedGeneratorDescent₀
#print axioms Uniformity.Density.DeepExport.DescentPinned
#print axioms Uniformity.Density.DeepExport.tauWordDescentSupply_of_guards
#print axioms Uniformity.Density.DeepExport.UniversalDoublyPinnedTauWordDescentSupply
#print axioms Uniformity.Density.DeepExport.universalDoublyPinnedTauSupply
#print axioms Uniformity.Density.DeepExport.s2Four_normalizerPinned
#print axioms Uniformity.Density.DeepExport.s2Four_descentPinned
#print axioms Uniformity.Density.DeepExport.s2FourTwisted_not_descentPinned
#print axioms Uniformity.Density.DeepExport.s2Four_tauWordDescentSupply''

end AxCheck1
