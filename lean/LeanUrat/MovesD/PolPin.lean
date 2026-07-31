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
SEAM RESIDUE (documented, per the charge; NARROWED at D2″ 2026-07-29; NARROWED AGAIN at
D2‴/R3-A 2026-07-29, confirm-2's singleton-realizer bypass): FIVE here-statable laws now
make the pin non-vacuous and exclude the under-typed instantiations: L1 TOTALITY at every
recentering node; GENUINENESS (finite weight ⇒ nonzero); the SUPPORT LAW (monomial
support in ONE stride-e, length-g progression anchored in the forced class
j₀ ≡ bezT(e,h)·γ mod e — note 4648–4650's j₀ ≡ h⁻¹·(target) mod e in corpus vocabulary);
DETERMINISM (the digits are functions of the node data — ONE realizer per node); and
[D2‴] the DIGIT-VALUE LAW `digits_prescribed`: at a recentering, a realizer is a genuine
D.10 CENTER REALIZER through the node's OWN frame stage — inC σ.Φ t, w(t) = w(Φ), and
R(t) = C(center)·T(0) — the exact clauses of `IsRecentering`/`LandingKey` (MovesC 545–557),
so the weight equation AND the top digit VALUE are pinned HERE, in Stage-carrier
vocabulary (σ.w, σ.R, center, Φ — all node data). Confirm-2's bypass ("a policy emitting
any nonzero monomial in the forced congruence class … while the digit values and weight
are wrong") is excluded BY TYPE: `no_pin_of_wrong_value`/`no_pin_of_wrong_weight` — one
wrong-valued lift at one recentering node ⇒ NO pin exists for that policy.
`Realizes := (t ≠ 0)` FAILS determinism at every node (`not_realizes_bare_ne_zero`).
THE STRICTLY SMALLER RESIDUE (named, per the R3 charge): what stays inside `Realizes` is
ONLY the (S6b′) SUB-RESIDUAL SLOT SELECTION — WHICH center realizer among the
(w, R)-equal ones, i.e. the prescribed lower-stage digits t_k realizing P_k (P the unique
deg < g poly with z̄^m·P(z̄) = target, note 2446–2455) via the two-line mutual recursion
one stage down. That piece is genuinely §B2-DEF/HC-1 carry-algebra vocabulary: the Stage
exports ONLY the top graded residual R(t) (one graded piece); the lower-stage digit
expansion of a coefficient (D.3(e)(ii)'s unitriangular digit systems) is not a
MovesC/MovesD export. The HC-1 wave instantiates `Realizes` with the (S6b′) formula and
discharges all five laws; owner = HC-1/§B2-DEF (POL-PIN, §2 ledger).
[ITEM 13 RE-SCOPE, 2026-07-31 — Asvin sign-off queue item 13, preferred option (ii)]:
`total` is RE-KEYED from bare `Node` values to nodes of `HistoryCoherent` histories — the
exact quantifier of L1's totality (note 4665–4666 quantifies over nodes OF A RUN; the old
form widened "every node of the run" to "every value of the `Node` type", where the frame
is a free field). The old bare-Node form was REFUTED-COMPILED: `R7_pinProbe.lean` ((†R7)
parity — a pin for ANY policy forces EVERY Stage unramified) completed unconditionally by
`R7_ramifiedForge.lean` (one forged ramified Stage at (2, F4) empties the old pin type for
every policy). Both leaf modules stay compiled against the FROZEN old form
(`OffsetPPinBare`, M1 hygiene) with dated notes. Under the re-key, at INTERIOR recentering
nodes coherence's `IsRecenteringCore.base` (= `IsRecentering`, Moves/Defs.lean:271)
supplies `σ.e = 1` AND a center-realizer witness (the recorded lift), so the (†R7) forcing
argument no longer reaches arbitrary stages; ramified child frames are additionally
UNREACHABLE in the pre-HK-06 coherence vocabulary (`HC2/HK22_twoNodeGate`). NAMED OPEN
FLANK (recorded, not silent): a history's FINAL recentering node carries no
`IsRecenteringCore` record under bare `HistoryCoherent` — its landing law lives one
predicate up (`JetSetup.landing`/`LandingKey`); a future countermodel at that flank would
re-adjudicate the quantifier to the JetSetup carrier (record:
notes/QUEUE_EXECUTION_2026-07-31.md §Item-13).
deps: Defs (bezT), D2a (CD_eq, for the pinned specialization).
sketch: structure + one-line consequences + the negative witness.  difficulty: easy.
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
predicate "t is the (S6b) offset-P-lift realizer at ν" (carried abstract here exactly as
`TreeModel` carries mem/child; its remaining HC-1 content is ONLY the sub-residual slot
selection — see `digits_prescribed`). FIVE laws are the here-statable content:
`total` = L1's kernel-(a) totality ("No node exists where the policy is partial", note
4665–4666) at RUN-NODE granularity (nodes of `HistoryCoherent` histories — item 13
re-scope, 2026-07-31; the bare-Node granularity was the R7-refuted over-reach) —
recenterings are the ONLY lift-consuming reads (note
3455–3458: "for RECENTERINGS, the LIFT t_i itself"); `realizes_ne_zero` = L1's "returns a
realizer t with w(t) = ν" (note 4658): a realizer of finite weight is NONZERO;
`support_forced` = the (S6b′) slot geometry [D2″]; `realizes_unique` = L1's determinism
[D2″]; `digits_prescribed` = the D.10 value/weight prescription in Stage-carrier
vocabulary [D2‴]. Together they force `pol.liftOf ν ≠ 0` at every recentering node of a
coherent history (`OffsetPPin.lift_ne_zero`) and make it a genuine center realizer
(`OffsetPPin.lift_center_realizer`), so no instantiation of the pin is vacuous and no
wrong-valued policy has one (`no_pin_of_wrong_value`/`no_pin_of_wrong_weight`).
[ITEM 13, 2026-07-31: `total` re-keyed to `HistoryCoherent`-history nodes — see its
docstring; the bare-Node form is the R7-refuted historical form `OffsetPPinBare`
(frozen in `R7_pinProbe.lean`).] -/
structure OffsetPPin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (pol : CanonPolicy p F) where
  /-- SEAM RESIDUE (W4-5): "t IS the (S6b) offset-P-lift realizer at ν". Instantiated by
  the HC-1 wave with §B2-DEF D.5's formula (note 4648–4650). -/
  Realizes : Node p F → Polynomial ℤ_[p] → Prop
  /-- L1 TOTALITY (kernel part (a), note 4653–4667) — **RE-SCOPED, item 13 (2026-07-31)**:
  at every recentering node OF A `HistoryCoherent` HISTORY the policy's output realizes.
  This is note 4665–4666's exact quantifier ("No node exists where the policy is partial"
  ranges over nodes of a RUN). The pre-repair form quantified over every bare `Node` value
  (the frame a free field) and was REFUTED-COMPILED — `R7_pinProbe.lean`'s (†R7) parity
  argument forces every Stage unramified, emptied unconditionally at (2, F4) by
  `R7_ramifiedForge.lean`; both leaves keep the frozen old form (`OffsetPPinBare`). At
  interior recentering nodes coherence itself supplies the witness ingredients
  (`IsRecenteringCore.base`: `σ.e = 1` + the recorded lift's center-realizer clauses). -/
  total : ∀ (H : History p F), HistoryCoherent H →
    ∀ (i : ℕ) (hi : i < H.nodes.length),
      (H.nodes[i]'hi).species = ReadSpecies.recentering →
      Realizes (H.nodes[i]'hi) (pol.liftOf (H.nodes[i]'hi))
  /-- Realizers are GENUINE (note 4658: "a realizer t with w(t) = ν" — finite weight, so
  nonzero; the zero polynomial has no weight). -/
  realizes_ne_zero : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]), Realizes ν t → t ≠ 0
  /-- **SUPPORT LAW** [D2″, 2026-07-29]: the (S6b) OFFSET-P-LIFT is "the sum anchored at
  the forced slot class j₀ ≡ h⁻¹·(target) mod e, slots j₀, …, j₀+(g−1)e, prescribed
  digits" (note 4648–4650) — a realizer's monomial support lies in ONE arithmetic
  progression of stride e and length g, anchored in the FORCED congruence class mod e.
  The class, in MovesD/MovesC vocabulary: h⁻¹ mod e IS `bezT ν.e ν.h` (Node.hbez
  `e·s + h·t = 1` gives h·t ≡ 1 mod e; `hbezCanon` pins t ∈ [0,e) — rev 14's t^B, a
  function of (e,h) only), and the TARGET is the node's recorded total side weight
  `ν.gam` (γ, D.3(c)'s stride argument — the same γ the shape-side `anchorTie`
  normalizes by: e·a = s0 − bezT·γ). SEAM RESIDUE (documented): that the prescribed
  digit VALUES sit in those slots and that w(t) = ν — §B2-DEF/HC-1 vocabulary — stays
  inside `Realizes`; the SLOT GEOMETRY is pinned HERE. -/
  support_forced : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]), Realizes ν t →
    ∃ j₀ : ℕ, (j₀ : ℤ) % (ν.e : ℤ) = (bezT ν.e ν.h * ν.gam) % (ν.e : ℤ) ∧
      ∀ j ∈ t.support, ∃ k : ℕ, k < ν.g ∧ j = j₀ + k * ν.e
  /-- **DETERMINISM** [D2″, 2026-07-29]: "the digits t_k are FUNCTIONS of the node data …
  the policy is deterministic" (note 4653–4667, L1) — at each node the offset-P formula
  returns THE realizer, not a realizer. This is the law that kills the under-typed
  `Realizes ν t := t ≠ 0` instantiation (`not_realizes_bare_ne_zero` below). -/
  realizes_unique : ∀ (ν : Node p F) (t t' : Polynomial ℤ_[p]),
    Realizes ν t → Realizes ν t' → t = t'
  /-- **DIGIT-VALUE LAW** [D2‴/R3-A OPTION 1, 2026-07-29]: at a recentering, "the offset-P
  formula returns a realizer t with w(t) = ν and the prescribed class" (L1, note 4657–4658)
  — and D.10 pins the prescription in NODE DATA: the realizer lives in the frame's
  coefficient space, carries the KEY weight, and its top residual digit IS the recorded
  center at position 0 (`IsRecentering`'s lift clauses = `LandingKey`'s recentering leg,
  MovesC 545–557, verbatim). This types the VALUE + WEIGHT content confirm-2 found
  unconstrained; only the (S6b′) sub-residual slot selection (which (w,R)-equal realizer)
  stays inside `Realizes` — the named HC-1 residue. -/
  digits_prescribed : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]), Realizes ν t →
    ν.species = ReadSpecies.recentering →
    inC ν.σ.Φ t ∧ ν.σ.w t = ν.σ.w ν.σ.Φ ∧
      ν.σ.R t = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The pin's non-vacuity witness: a pinned policy emits a genuine (nonzero) lift at every
recentering node of a coherent history — the lawless/zero policies are excluded. (The blind
structural layer already excluded `Canon := fun _ => False`; this excludes
`liftOf := fun _ => 0` at every reachable recentering.) [Item 13 re-key, 2026-07-31:
history-keyed with `total`.] -/
theorem OffsetPPin.lift_ne_zero {pol : CanonPolicy p F} (pin : OffsetPPin pol)
    (H : History p F) (hH : HistoryCoherent H) (i : ℕ) (hi : i < H.nodes.length)
    (hν : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    pol.liftOf (H.nodes[i]'hi) ≠ 0 :=
  pin.realizes_ne_zero _ (pol.liftOf (H.nodes[i]'hi)) (pin.total H hH i hi hν)

/-- **NON-VACUITY RE-VERIFICATION** [D2″]: the Codex-confirm instantiation
`Realizes ν t := t ≠ 0` ("any policy producing nonzero recentering lifts can obtain an
OffsetPPin") now FAILS the laws: at EVERY node, no pin's `Realizes` fiber is the bare
nonzero predicate — `realizes_unique` would force `1 = X` in ℤ_[p][X] (both are nonzero,
i.e. both would "realize"). The support law independently over-constrains it: `1 + X^e`
is nonzero with support {0, e} in two stride-e slots of the same class only if the
progression admits both, and `realizes_unique` still separates it from `1`. -/
theorem OffsetPPin.not_realizes_bare_ne_zero {pol : CanonPolicy p F}
    (pin : OffsetPPin pol) (ν : Node p F) :
    pin.Realizes ν ≠ fun t : Polynomial ℤ_[p] => t ≠ 0 := by
  intro h
  have h1 : pin.Realizes ν 1 := by rw [h]; exact one_ne_zero
  have hX : pin.Realizes ν Polynomial.X := by rw [h]; exact Polynomial.X_ne_zero
  have heq := pin.realizes_unique ν 1 Polynomial.X h1 hX
  have hdeg := congrArg Polynomial.natDegree heq
  simp [Polynomial.natDegree_one, Polynomial.natDegree_X] at hdeg

/-- [D2‴] A pinned policy's recentering lift is a genuine D.10 CENTER REALIZER: coefficient
space, key weight, top digit = the recorded center — `total` + `digits_prescribed`. This is
exactly the lift datum `LandingKey`/`HistoryCoherent` consume at recenterings. [Item 13
re-key, 2026-07-31: stated at the recentering nodes of a coherent history — `total`'s new
granularity.] -/
theorem OffsetPPin.lift_center_realizer {pol : CanonPolicy p F} (pin : OffsetPPin pol)
    (H : History p F) (hH : HistoryCoherent H) (i : ℕ) (hi : i < H.nodes.length)
    (hν : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    inC (H.nodes[i]'hi).σ.Φ (pol.liftOf (H.nodes[i]'hi)) ∧
      (H.nodes[i]'hi).σ.w (pol.liftOf (H.nodes[i]'hi))
        = (H.nodes[i]'hi).σ.w (H.nodes[i]'hi).σ.Φ ∧
      (H.nodes[i]'hi).σ.R (pol.liftOf (H.nodes[i]'hi))
        = LaurentPolynomial.C (H.nodes[i]'hi).center * LaurentPolynomial.T 0 :=
  pin.digits_prescribed _ (pol.liftOf (H.nodes[i]'hi)) (pin.total H hH i hi hν) hν

/-- **BYPASS KILL, value leg** [D2‴]: confirm-2's singleton-realizer bypass ("`Realizes ν t
:= t = pol.liftOf ν` for a policy whose recentering lift is any nonzero monomial in the
forced congruence class … while the digit values … are wrong") admits NO pin: a policy whose
lift at ONE recentering node OF A COHERENT HISTORY has the WRONG top residual digit (≠ the
recorded center at position 0) has an EMPTY pin type. Wrong-valued policies are excluded by
type, not by prose. [Item 13 re-key, 2026-07-31: the offending node must now be exhibited
INSIDE a coherent history — exactly the reachable-node discipline the R7 probe demanded.] -/
theorem OffsetPPin.no_pin_of_wrong_value {pol : CanonPolicy p F}
    (H : History p F) (hH : HistoryCoherent H) (i : ℕ) (hi : i < H.nodes.length)
    (hν : (H.nodes[i]'hi).species = ReadSpecies.recentering)
    (hwrong : (H.nodes[i]'hi).σ.R (pol.liftOf (H.nodes[i]'hi))
      ≠ LaurentPolynomial.C (H.nodes[i]'hi).center * LaurentPolynomial.T 0) :
    IsEmpty (OffsetPPin pol) :=
  ⟨fun pin => hwrong (pin.lift_center_realizer H hH i hi hν).2.2⟩

/-- **BYPASS KILL, weight leg** [D2‴]: same at the weight equation w(t) = w(Φ) — the other
datum confirm-2 named as unconstrained ("the … weight equation … may all be wrong").
[Item 13 re-key, 2026-07-31: coherent-history-keyed, as the value leg.] -/
theorem OffsetPPin.no_pin_of_wrong_weight {pol : CanonPolicy p F}
    (H : History p F) (hH : HistoryCoherent H) (i : ℕ) (hi : i < H.nodes.length)
    (hν : (H.nodes[i]'hi).species = ReadSpecies.recentering)
    (hwrong : (H.nodes[i]'hi).σ.w (pol.liftOf (H.nodes[i]'hi))
      ≠ (H.nodes[i]'hi).σ.w (H.nodes[i]'hi).σ.Φ) :
    IsEmpty (OffsetPPin pol) :=
  ⟨fun pin => hwrong (pin.lift_center_realizer H hH i hi hν).2.1⟩

/-- `CD_canonical` — the D2a class-count identity, SPECIALIZED to a pinned policy: the
recorded consumer of W4-5. Content = `CD_eq`; the pin binder records that the note's C is
C at THE canonical policy (note 4646: "The classifier is run with ONE lift rule").
CANONICAL-UP-TO-THE-RESIDUE (confirm-3 adjudication, 2026-07-29): `OffsetPPin` pins
center-realizer COMPATIBILITY — the maximal content statable in exported `Node`/`Stage`
vocabulary (confirm-3: "the strongest faithful projection currently expressible"; the
per-slot recursive law needs the lower-stage expansion/realizer data). A pinned `pol`
is therefore "the note's policy" ONLY jointly with the W4-5 discharge duty (owner HC-1:
export the lower-stage realizer vocabulary + the (S6b') slot-selection law). Until that
discharge, a (w,R)-equal non-canonical center realizer can also carry this pin — the
NAMED open boundary, not a silent claim. -/
theorem CD_canonical {n : ℕ} {pol : CanonPolicy p F} {P : Shape n}
    (pin : OffsetPPin pol) (hnorm : PresentNorm n pol P)
    (hne : (P : ShapePrefix).reads ≠ []) :
    P.CD pol = Nat.card (PrefIdx n pol P) :=
  CD_eq hnorm hne

end

end LeanUrat.MovesD
