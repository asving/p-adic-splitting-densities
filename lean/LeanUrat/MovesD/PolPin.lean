/-
Unit PolPin  (MovesD campaign, ratification repair D2, 2026-07-28)
[Finding D2 ACCEPTED as seam typing: the corpus quantifies over every blind `CanonPolicy`
(STRONGER theorems — nothing false), but WHICH policy is the note's was only a comment
(POL-PIN). This unit is the TYPED consumer-side pin, W4-SYNC style: seam entry W4-5.]
moves_ref: "The canonical policy. The classifier is run with ONE lift rule: at every
recentering, the (S6b) OFFSET-P-LIFT realizer (§C C.0's named canonical choice; §B2-DEF
D.5 (S6b) with the pass-11 offset repair — the sum anchored at the forced slot class
j₀ ≡ h⁻¹·(target) mod e, slots j₀, …, j₀+(g−1)e, prescribed digits). All histories in this
note carry these lifts and no others." (note 4646–4651) + L1 (canonical-choice totality,
kernel part (a)): "the offset-P formula returns a realizer t with w(t) = ν and the
prescribed class … No node exists where the policy is partial." (note 4653–4667).
SEAM RESIDUE (documented, per the charge): the CONTENT of "t IS the (S6b) offset-P-lift
realizer at ν" needs weight and residue-reduction vocabulary (§B2-DEF/HC-1: w(t) = ν, the
prescribed residual class, the forced slot class j₀) — NOT constructible from
MovesD+MovesC exports. It is carried as the abstract predicate FIELD `Realizes`
(mirroring `TreeModel`'s mem/child style), accompanied by the two here-statable laws so
the pin is non-vacuous NOW: L1 TOTALITY at every recentering node, and GENUINENESS
(realizers carry the finite weight w(t) = ν, so they are nonzero — the zero polynomial
has no weight). The HC-1 wave instantiates `Realizes` with the (S6b) formula and
discharges both laws; owner = HC-1/§B2-DEF (POL-PIN, §2 ledger).
deps: Defs, D2a (CD_eq, for the pinned specialization).
sketch: structure + two one-line consequences.  difficulty: easy.
hypothesis_fields: none (the pin itself is the new hypothesis object).
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D2a_finite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open Polynomial LeanUrat.Moves LeanUrat.MovesC

/-- **W4-5 (POL-PIN, TYPED)** — the consumer-side pin for the note's ONE lift rule (note
4646–4651): `pol` is the (S6b) OFFSET-P-LIFT policy. `Realizes ν t` is the seam-residue
predicate "t is the (S6b) offset-P-lift realizer at ν" (§B2-DEF/HC-1 vocabulary — weight
w(t) = ν, prescribed residual class, forced slot class j₀; carried abstract here exactly
as `TreeModel` carries mem/child). The two laws are the here-statable content:
`total` = L1's kernel-(a) totality ("No node exists where the policy is partial", note
4665–4666) at Node granularity — recenterings are the ONLY lift-consuming reads (note
3455–3458: "for RECENTERINGS, the LIFT t_i itself"); `realizes_ne_zero` = L1's "returns a
realizer t with w(t) = ν" (note 4658): a realizer of finite weight is NONZERO. Together
they force `pol.liftOf ν ≠ 0` at every recentering (`OffsetPPin.lift_ne_zero`), so no
instantiation of the pin is vacuous. -/
structure OffsetPPin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (pol : CanonPolicy p F) where
  /-- SEAM RESIDUE (W4-5): "t IS the (S6b) offset-P-lift realizer at ν". Instantiated by
  the HC-1 wave with §B2-DEF D.5's formula (note 4648–4650). -/
  Realizes : Node p F → Polynomial ℤ_[p] → Prop
  /-- L1 TOTALITY (kernel part (a), note 4653–4667): at every recentering node the
  policy's output realizes. -/
  total : ∀ ν : Node p F, ν.species = ReadSpecies.recentering → Realizes ν (pol.liftOf ν)
  /-- Realizers are GENUINE (note 4658: "a realizer t with w(t) = ν" — finite weight, so
  nonzero; the zero polynomial has no weight). -/
  realizes_ne_zero : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]), Realizes ν t → t ≠ 0

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The pin's non-vacuity witness: a pinned policy emits a genuine (nonzero) lift at every
recentering node — the lawless/zero policies are excluded. (The blind structural layer
already excluded `Canon := fun _ => False`; this excludes `liftOf := fun _ => 0`.) -/
theorem OffsetPPin.lift_ne_zero {pol : CanonPolicy p F} (pin : OffsetPPin pol)
    (ν : Node p F) (hν : ν.species = ReadSpecies.recentering) : pol.liftOf ν ≠ 0 :=
  pin.realizes_ne_zero ν (pol.liftOf ν) (pin.total ν hν)

/-- `CD_canonical` — the D2a class-count identity, SPECIALIZED to a pinned policy: the
recorded consumer of W4-5. Content = `CD_eq`; the pin binder records that the note's C is
C at THE canonical policy (note 4646: "The classifier is run with ONE lift rule"). -/
theorem CD_canonical {n : ℕ} {pol : CanonPolicy p F} {P : Shape n}
    (pin : OffsetPPin pol) (hnorm : PresentNorm n pol P)
    (hne : (P : ShapePrefix).reads ≠ []) :
    P.CD pol = Nat.card (PrefIdx n pol P) :=
  CD_eq hnorm hne

end

end LeanUrat.MovesD
