/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130k

/-!
# Uniformity.ChapC.C130fg — the FGMN source carrier (chain-carrier node CC-13)

**Chain-carrier node CC-13** of `CHAIN_CARRIER_DESIGN_2026-08-24.md` (§4.3 the source-side
FGMN data and law package, §7 consumer map A, §9 the honesty classification, §10 row CC-13):
land `FGMNSourceData` (the realized next valuation, the POLYNOMIAL-VALUED source residual
operators, the letter data), the exact-grade/above-grade DEFINITIONS from the realized next
valuation, the thirteen-field `FGMNSourceLaws` source-obligation package, and the assembled
`ChainRealization` layer whose fields are the four OPEN-DICT obligation SIGNATURES of
`FGMNCALCULUS_FIELDLIST_2026-08-24.md` (U7) §8.  The elaboration authority for every type
below is `leanfinal/scratch/U11_carrier_check.lean`; the types here are exactly the scratch
types.

## The U9 dictionary this transcribes (`FGMN_ADJUDICATION_2026-08-24.md` §2)

The fixed index convention is the **next-augmentation convention**: at repo depth `r`,
`keyAt r` is the augmentation key `φ_(r+1)`, `(e', f', u')` is the next augmentation data,
and every operator of `FGMNSourceData` belongs to `μ_(r+1) = [μ_r; (φ_(r+1), ν_(r+1))]`:

* `nextValue`           ↔ `μ_(r+1)`, in the repo's CLEARED integer grades (U9 Q3: after
  clearing by `e(μ_r)` every class grade is already in `Γ_r`; `PrevGrade` is removed)
  — [A-C.13, 2026-08-25]: U9 Q3's removal was WRONG at the graded level and `PrevGrade` is
  RESTORED as a field below, per U14's print-read adjudication
  (`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §4/§8.1): published Cor 4.12(2)
  carries the premise `β ∈ Γ_{r−1}` and its proof uses `s_r(β) = 0` verbatim; the plain
  graded product law at arbitrary grades is machine-refuted at the RP-1 operator
  (`C130rp2.tooth_graded_mul_plain_shape_refuted`);
* `PrevGrade β`         ↔ `β ∈ Γ_r` in cleared coordinates (published Cor 4.12(2)'s
  `β ∈ Γ_{r−1}` after the index shift) — [A-C.13] restored;
* `gradedResidual β g`  ↔ `R_(r+1,β)(g) ∈ F_(r+1)[y]` (FGMN published Def 3.13),
  POLYNOMIAL-valued — U9 Q2: the scalar consumer `Rgr` is its **degree-zero coefficient**,
  derived at CC-16, never a field here;
* `normalizedResidual g`↔ `R_(r+1)(g)` (published Def 3.15);
* `keyPolynomial g`     ↔ `g ∈ KP(μ_(r+1))` (published §1.2);
* `initialEquiv g h`    ↔ `g ∼_(μ_(r+1)) h` (published Def 1.2);
* `letter i`            ↔ `z_i` transported into `F_(r+1) ≃ W.fld r` (published §3.3);
* `ExactGrade β g`      ↔ `μ_(r+1)(g) = β/e(μ_r)`, `AboveGrade β g` ↔ `μ_(r+1)(g) > β/e(μ_r)`
  — both DEFINITIONS from the one `nextValue` field, never independent fields.

The coefficient codomain `W.fld r` is the depth-two consumer's checked identification
`F₃ = K₂` (U9 §4, `GENTOW2_PROOF` S5.1) read at general depth: `F_(r+1) ≃ W.fld r`.

## The four OPEN-DICT obligations as signatures (U7 §8)

Per design §4.4, each obligation is a structure field (or shared parameter) of
`ChainRealization`, with its U7 §8 citation on the field docstring:

* **OPEN-DICT-1** — the SHARED `keys : KeyChain W` parametrizes both `node` and `fgmn`; its
  `keyAt_one`/`keyAt_degree` fields (C130k) carry the index-shift and equation-(7) degree
  recurrence dictionary.  There is no second key chain to drift against.
* **OPEN-DICT-2** — `grade_compat`: the cleared next-valuation convention agrees with the
  legal point read.
* **OPEN-DICT-3** — the transport boundary: `receiver : TerminalReceiver …` (the repo side of
  `W.fld i ≃ F_i`) together with the `Polynomial (W.fld r)` residual codomains of `fgmn`.
* **OPEN-DICT-4** — `letter_compat`: FGMN's transported `z_i` is the same ambient node letter.

None of the four is a proof and none is a `True` body: `grade_compat`/`letter_compat` are
genuine equations, and OPEN-DICT-1 and OPEN-DICT-3 are carried by shared typed data whose laws
(`keyAt_one`, `keyAt_degree`, the receiver squares) are already non-trivial fields.

## Honesty classification (design §9)

Every field below is either a SOURCE OBLIGATION (the thirteen FGMN clauses, each named in its
docstring with the published locus from design §4.3's table) or a REPOSITORY DICTIONARY
(`grade_compat`, `letter_compat`).  The laws remain genuine source hypotheses until the cited
clauses and OPEN-DICT transports are transcribed (CC-14/CC-15); this carrier does not turn
them into Lean-core facts, and no existence axiom or instance is declared.  No field is a
socket conclusion, `FGMNCalculus`, `SlotCarrier`, `BlockData`, `HVarthetaRes`, `VarthetaRes`,
`WFrame`, or `Nonempty` of any consumer class.

## Deliberately NOT here (later CC nodes)

The coefficient-zero regressions and per-clause transcriptions (CC-14/CC-15); the packaging
into the actual A-C.11 `FGMNCalculus` class — that class lives in leanspec, read-only here
(CC-16); `RealizedInput`/`inputBlock` (CC-8); the full S2 `ChainRealization` instance
(CC-17); every socket application (CC-18).  Nothing here inhabits any carrier.

DEPENDS: C130k (CC-1 skeleton: `KeyChain`, `LaurentNormalizer`, `NodePointSource`, live
ranges), C130a via C130k (`TerminalReceiver`, `StageLive`), C83 (`DeepTower`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no `True`-bodied field.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-! ## The source-side FGMN data (U9 §2's next-augmentation objects) -/

/-- The source-side next-augmentation objects behind A-C.11 (design §4.3; U9 §2's fixed
dictionary).  In particular the graded residual is POLYNOMIAL-valued (published Def 3.13
defines `R_(r+1,β)(g)` as an element of `F_(r+1)[y]`); the scalar `Rgr` consumer will be its
coefficient zero (CC-16 packaging), and the `Polynomial (W.fld r)` codomains are half of the
OPEN-DICT-3 transport boundary (U7 §8.3, `F_(r+1) ≃ W.fld r`).  Sharing the parameter `K`
with `NodePointSource` is the OPEN-DICT-1 signature (U7 §8.1). -/
structure FGMNSourceData (W : DeepTower.{0, uKt} F H₀ hpin r)
    (K : KeyChain W) (e' f' u' : ℕ) where
  /-- U9 §2: the realized next augmented valuation `μ_(r+1)`, read in the repo's CLEARED
  integer grades (U9 Q3: clearing by `e(μ_r)` puts every class grade in `Γ_r`); `⊤` is the
  value of `0`.  The identification of this read with the legal point read is the
  OPEN-DICT-2 field `grade_compat` of `ChainRealization`, not a fact of this structure. -/
  nextValue : Polynomial O → WithTop ℤ
  /-- U9 Q2/§2: the polynomial-valued graded residual `R_(r+1,β)(g) ∈ F_(r+1)[y]` (published
  Def 3.13), transported along `F_(r+1) ≃ W.fld r` — the OPEN-DICT-3 codomain (U7 §8.3).
  The scalar A-C.11 `Rgr` is `(gradedResidual β g).coeff 0`; no scalar field exists here. -/
  gradedResidual : ℕ → Polynomial O → Polynomial (W.fld r)
  /-- U9 §2: the normalized residual operator `R_(r+1)(g)` (published Def 3.15), in the same
  OPEN-DICT-3 transported codomain. -/
  normalizedResidual : Polynomial O → Polynomial (W.fld r)
  /-- [A-C.13, 2026-08-25 — U14, `COR412_ADJUDICATION_2026-08-25.md` §8.1] Cleared grades
  coming from the preceding value group `Γ_r` (published Corollary 4.12(2)'s `β ∈ Γ_{r−1}`
  after the repo index shift).  RESTORED: U9 Q3 removed it as "automatic after clearing",
  which is incompatible with the full-current-group integer clearing actually used by the
  RP-1 operator (U14 §4).  The realization must identify it with membership in the preceding
  value group; under the full-current-group clearing this is `e' ∣ β` — at S2, evenness.
  The predicate form is carried until OPEN-DICT-2 formally proves that divisibility is the
  correct general cleared-group test (U14 §8.1). -/
  PrevGrade : ℕ → Prop
  /-- U9 §2: membership `g ∈ KP(μ_(r+1))` (published §1.2); the `Polynomial O` domain builds
  in published Cor 1.10's `KP(μ) ⊂ O[x]`. -/
  keyPolynomial : Polynomial O → Prop
  /-- U9 §2: FGMN's initial-form equivalence `g ∼_(μ_(r+1)) h` (published Def 1.2). -/
  initialEquiv : Polynomial O → Polynomial O → Prop
  /-- U9 §2: the residue letters `z_i` transported into `F_(r+1) ≃ W.fld r` (published §3.3,
  the `γ_i → y_i = H_(μ_i)(γ_i) → z_i` construction), live for `1 ≤ i ≤ r`; junk outside.
  Compatibility with the ambient node letters is the OPEN-DICT-4 field `letter_compat` of
  `ChainRealization` (U7 §8.4). -/
  letter : ℕ → W.fld r

namespace FGMNSourceData

/-- U9 §2: `ExactGrade β g ↔ μ_(r+1)(g) = β/e(μ_r)` — repo side, the clearing already lives
inside `nextValue`, so exact grade is the equation `nextValue g = β`.  This is membership in
FGMN's `P_β \ P_β⁺` (U7 §3.1) and is a DEFINITION from the realized next valuation, exactly
as U7 §8's OPEN-DICT-2 demands — not an independently choosable field. -/
def ExactGrade {W : DeepTower.{0, uKt} F H₀ hpin r} {K : KeyChain W}
    {e' f' u' : ℕ} (S : FGMNSourceData W K e' f' u')
    (β : ℕ) (g : Polynomial O) : Prop :=
  S.nextValue g = (β : WithTop ℤ)

/-- U9 §2: `AboveGrade β g ↔ μ_(r+1)(g) > β/e(μ_r)` — FGMN's `P_β⁺` (U7 §3.1).  Defined from
the SAME `nextValue` as `ExactGrade`, per U7 §3's demand that it must not be defined
independently of the exact grade. -/
def AboveGrade {W : DeepTower.{0, uKt} F H₀ hpin r} {K : KeyChain W}
    {e' f' u' : ℕ} (S : FGMNSourceData W K e' f' u')
    (β : ℕ) (g : Polynomial O) : Prop :=
  (β : WithTop ℤ) < S.nextValue g

end FGMNSourceData

/-! ## The thirteen named FGMN source obligations (design §4.3's table) -/

/-- The published FGMN obligations, stated on the SOURCE objects rather than by copying the
scalar consumer interface (design §4.3): `gradedResidual` is source-polynomial-valued, and
scalar `Rgr` is derived as its coefficient zero at CC-16.  Each field names its published
clause; all remain genuine source hypotheses until the cited clauses and OPEN-DICT transports
are transcribed (CC-14/CC-15) — the carrier does not turn them into Lean-core facts.  The
last-live-key laws are fenced by `0 < r` (U9 Q4: the class stays syntactically available at
`r = 0` with no base-case law). -/
structure FGMNSourceLaws (W : DeepTower.{0, uKt} F H₀ hpin r)
    (K : KeyChain W) (e' f' u' : ℕ) (S : FGMNSourceData W K e' f' u') where
  /-- FGMN published Lemma 3.14, polynomial-valued: the graded residual vanishes above the
  grade (`R_(r+1,β)` vanishes on `P_β⁺`). -/
  graded_zero_of_above : ∀ β (g : Polynomial O),
    S.AboveGrade β g → S.gradedResidual β g = 0
  /-- FGMN published Corollary 4.12(1), polynomial-valued: graded additivity on exact-grade
  inputs whose sum stays at exact grade. -/
  graded_add : ∀ β (g h : Polynomial O),
    S.ExactGrade β g → S.ExactGrade β h → S.ExactGrade β (g + h) →
      S.gradedResidual β (g + h) = S.gradedResidual β g + S.gradedResidual β h
  /-- FGMN published Corollary 4.12(2), polynomial-valued, with the exact-grade product
  conclusion, INCLUDING its printed `β ∈ Γ_{r−1}` premise (`PrevGrade β'`).
  [A-C.13, 2026-08-25]: premise RESTORED per U14's print-read adjudication
  (`COR412_ADJUDICATION_2026-08-25.md` §4/§8.1) — the printed proof uses `s_r(β) = 0`
  verbatim, and the PLAIN law at arbitrary grades is machine-refuted at the RP-1 operator
  (`C130rp2.tooth_graded_mul_plain_shape_refuted`: `R₁₀(Φ′²) = X ≠ 1 = R₅(Φ′)²`).  U9 Q3's
  "automatic after clearing" removal was wrong at the graded level.  The arbitrary-grade
  extension carries the carry twist `y^c` (U14 §5) and is deliberately NOT this field. -/
  graded_mul : ∀ β β' (g h : Polynomial O),
    S.ExactGrade β g → S.ExactGrade β' h →
    S.PrevGrade β' →
      S.ExactGrade (β + β') (g * h) ∧
      S.gradedResidual (β + β') (g * h) =
        S.gradedResidual β g * S.gradedResidual β' h
  /-- FGMN published Theorem 4.1 + Corollary 4.9(1), in the `deg g < deg (keyAt r)` scope:
  at exact grade and below the key degree the `φ_(r+1)`-expansion has only its `s = 0` term,
  so the degree-zero coefficient is nonzero.  U9 Q2: the degree fence is ESSENTIAL — exact
  grade alone would make this false. -/
  graded_scalar_nonzero : ∀ β (g : Polynomial O),
    S.ExactGrade β g → g.natDegree < (K.keyAt r).natDegree → g ≠ 0 →
      (S.gradedResidual β g).coeff 0 ≠ 0
  /-- FGMN published Corollary 4.12(3): multiplicativity of the normalized residual. -/
  normalized_mul : ∀ g h : Polynomial O,
    S.normalizedResidual (g * h) = S.normalizedResidual g * S.normalizedResidual h
  /-- FGMN published Definition 1.6 (expansion minimum), Definition 3.13, equation (11), and
  Corollary 4.12(1)/(2): the recipe expansion — the residual of the recipe key is the
  `y`-polynomial of the graded slot reads, with scalar slots as degree-zero coefficients. -/
  normalized_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → S.ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (K.keyAt r).natDegree) →
    S.normalizedResidual ((K.keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (K.keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
        Polynomial.C ((S.gradedResidual ((f' - t) * u') (khat t)).coeff 0) *
          Polynomial.X ^ t
  /-- FGMN published Theorem 5.7's construction, with MONIC IRREDUCIBLE residual input (U9
  §10: the printed proof starts from an irreducible `ψ`; the broader monic-only output was
  not justified). -/
  normalized_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → Irreducible ψ → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O, g.Monic ∧
        g.natDegree = e' * f' * (K.keyAt r).natDegree ∧
        S.normalizedResidual g = ψ
  /-- FGMN published Lemma 5.2(2), Corollary 4.9, and the degree-forcing display in the
  proof of Theorem 5.7: the key-polynomial criterion at the recipe degree.  The nonzero
  constant coefficient forces `s(g) = 0` in the Theorem 5.7 degree argument. -/
  key_criterion : ∀ g : Polynomial O, g.Monic →
    g.natDegree = e' * f' * (K.keyAt r).natDegree →
    Irreducible (S.normalizedResidual g) →
    (S.normalizedResidual g).natDegree = f' →
    (S.normalizedResidual g).coeff 0 ≠ 0 → S.keyPolynomial g
  /-- FGMN published Lemma 1.8 + Corollary 1.10 + the landed Gauss transport (U9 Q5:
  `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` in pinned mathlib): key
  polynomials are irreducible over `K_v[x]`, and monic + `KP(μ) ⊂ O[x]` transports the
  irreducibility to `Polynomial O`. -/
  key_irreducible : ∀ g : Polynomial O,
    S.keyPolynomial g → g.Monic → Irreducible g
  /-- FGMN published Proposition 1.7(4): the carried key `φ_(r+1) = keyAt r` is a key
  polynomial for `μ_(r+1)`; fenced by `0 < r` (U9 Q4). -/
  carried_key_is_key : 0 < r → S.keyPolynomial (K.keyAt r)
  /-- FGMN published equation (11): `R_(r+1)(φ_(r+1)) = 1`, fenced by `0 < r` (U9 Q4: the
  `r = 0` base behavior differs and is deliberately not asserted). -/
  carried_key_residual : 0 < r → S.normalizedResidual (K.keyAt r) = 1
  /-- FGMN published Proposition 5.6(2) iff (3): for key polynomials, initial-form
  equivalence is equality of normalized residuals; both `keyPolynomial` hypotheses are
  retained. -/
  initial_iff_residual : ∀ g h : Polynomial O,
    S.keyPolynomial g → S.keyPolynomial h →
      (S.initialEquiv g h ↔ S.normalizedResidual g = S.normalizedResidual h)
  /-- FGMN published §3.3 (following Lemma 3.11): `z_i ≠ 0` for the positive live letters. -/
  letter_ne_zero : ∀ i, 1 ≤ i → i ≤ r → S.letter i ≠ 0

/-! ## The assembled layer: the four OPEN-DICT obligations as signatures -/

/-- The decided carrier (design §4.4): a conservative layer over `DeepTower`, reusing the
freeze's `TerminalReceiver` and C130k's carrier skeleton.  The four OPEN-DICT obligations of
U7 §8 are signatures here: OPEN-DICT-1 is the shared `keys` (one `KeyChain` parametrizes both
`node` and `fgmn`), OPEN-DICT-2 is `grade_compat`, OPEN-DICT-3's transport boundary is
`receiver` together with `fgmn`'s `Polynomial (W.fld r)` residual codomains, and OPEN-DICT-4
is `letter_compat`.  No field is a socket conclusion or a consumer class, and the two residue
reads of `node` (`canonicalRead`/`arenaRead`) remain deliberately unrelated (design §8: the
OM-8 L3 descent goal stays open at the sockets). -/
structure ChainRealization
    (W : DeepTower.{0, uKt} F H₀ hpin r)
    (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L]
    (e' f' u' : ℕ) where
  /-- OPEN-DICT-3 (U7 §8.3): the coefficient-field transport boundary.  `topEquiv` and the
  chain-compatible `levelHom` family are the repo side of the equivalences `W.fld i ≃ F_i`
  and their truncation compatibility; with `fgmn`'s `Polynomial (W.fld r)` codomains they
  carry the scalar-coordinate specialization boundary of `R_(r+1,β)`.  The remaining
  OPEN-DICT-3 content (that `Rgr`, `Rres`, `KP`, `nuEquiv` ARE the transported FGMN objects)
  is exactly what an instance of this structure must supply through `fgmn` + `fgmnLaws`. -/
  receiver : TerminalReceiver F H₀ hpin r W Kt
  /-- OPEN-DICT-1 (U7 §8.1): the single MacLane key chain, SHARED between `node` and `fgmn`.
  Its `keyAt_one` (index shift/first key) and `keyAt_degree` (the equation-(7) degree
  recurrence identified with `W.Dcum`) fields are the key dictionary; sharing the parameter
  leaves no second chain to drift against. -/
  keys : KeyChain W
  /-- EFF.T2.07/GENTOW5.15: the integer/Laurent normalizer layer (C130k). -/
  normalizer : LaurentNormalizer W
  /-- The legal node-point source (C130k): points, stage tables, threshold/window, letters,
  and the two deliberately separate residue reads. -/
  node : NodePointSource (L := L) W receiver keys
  /-- This file's FGMN source data for the next augmentation `μ_(r+1)` (U9 §2). -/
  fgmn : FGMNSourceData W keys e' f' u'
  /-- This file's thirteen named FGMN source obligations (design §4.3). -/
  fgmnLaws : FGMNSourceLaws W keys e' f' u' fgmn
  /-- OPEN-DICT-2 (U7 §8.2): the cleared next-valuation convention agrees with the legal
  point read at the terminal stage — the source's rational grades and the corpus's natural
  grades are identified through an actual evaluation, so `ExactGrade`/`AboveGrade` are
  FGMN's `P_β \ P_β⁺`/`P_β⁺` and not freely chosen predicates. -/
  grade_compat : ∀ x : node.Point, node.Pt r x → ∀ g : Polynomial O,
    fgmn.nextValue g = node.pointHgt r x g
  /-- OPEN-DICT-4 (U7 §8.4): FGMN's transported `z_i` is the same ambient node letter — the
  `γ_i → y_i → z_i` construction is compatible with the repo letters; C.102's letter formula
  must be a theorem of this dictionary, not a consequence of a freely chosen `letter`. -/
  letter_compat : ∀ i, StageLive r i →
    algebraMap Kt L (receiver.topEquiv (fgmn.letter i)) = (node.ambientLetter i : L)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.FGMNSourceData
#print axioms Uniformity.Density.Tower.FGMNSourceData.ExactGrade
#print axioms Uniformity.Density.Tower.FGMNSourceData.AboveGrade
#print axioms Uniformity.Density.Tower.FGMNSourceLaws
#print axioms Uniformity.Density.Tower.ChainRealization

end AxCheck
