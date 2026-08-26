/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130la
import Uniformity.ChapC.C130lb

/-!
# Uniformity.ChapC.C130pk — FGMN packaging (chain-carrier node CC-16)

**Chain-carrier node CC-16** of `CHAIN_CARRIER_DESIGN_2026-08-24.md` (§7 consumer map A,
§10 row CC-16): replace the scratch `FGMNCalculusCheck` by the ACTUAL A-C.11 class — the
leanfinal `FGMNCalculus` twin, FIELD-FOR-FIELD identical to the enacted leanspec class
(`leanspec/Leanspec/ChapC.lean`, the A-C.11 re-sign of NODE C.92), types byte-equal modulo
the one design-§7 vocabulary substitution `DeepTower F H₀ hpin r ↦ DeepTower.{0, uKt} F H₀
hpin r` (leanfinal's explicit universes) — together with its two leanspec consumers
`FGMNCalculus.chainNorm` and `FGMNCalculus.thetaRatio` (byte-faithful signatures), and PROVE
the packaging theorem `FGMNSourceData + FGMNSourceLaws + KeyChain → Nonempty (FGMNCalculus W
e' f' u')` with NO new axiom: every class field is filled from the FGMN records (CC-13,
`C130fg`) and the CC-14/CC-15 law theorems (`C130la`/`C130lb`).

**[PK-2/U15, 2026-08-25]** — packaging route (`PACKAGING_ROUTE_2026-08-25.md` §4.2): the
carrier-typed pair `ChainRealization.toCalculus`/`chainRealization_calculus_nonempty` is
RETIRED and replaced by the factored `fgmnCalculusOf`/`fgmn_model_calculus_nonempty` —
field-for-field the same construction, minus the carrier, which the retired pair never
consumed beyond its `keys`/`fgmn`/`fgmnLaws` legs (U15 §1's machine verification).  The
PK-1-retyped `ChainRealization` (split node, no FGMN legs) no longer feeds this file.

## The adjudication documents this packages (cited per A-C.11)

The field list, per-field provenance, published-source print-reads, and the seven decided
design questions live in `docs/in-progress/FGMN_ADJUDICATION_2026-08-24.md` (U9) on top of
`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` (U7).  The elaboration authority for
the packaging map is `leanfinal/scratch/U11_carrier_check.lean` (`toCalculus` against the
local `FGMNCalculusCheck` repeat); this file retires that local repeat by landing the actual
class.

## The design-§7 projection map (packaging, not a new cite)

| A-C.11 field | construction here |
|---|---|
| `keyAt` | `A.keys.keyAt` |
| `keyAt_one`, `keyAt_deg` | `KeyChain.keyAt_one` / `keyAt_degree` (OPEN-DICT-1, C130k) |
| `ExactGrade` / `AboveGrade` | `A.fgmn.ExactGrade` / `A.fgmn.AboveGrade` (CC-13 definitions) |
| `PrevGrade` | `A.fgmn.PrevGrade` (CC-13 field, [A-C.13] restored per U14) |
| `Rgr β g` | `A.fgmn.Rgr` = `(A.fgmn.gradedResidual β g).coeff 0` (CC-14, U9 Q2) |
| `Rres` | `A.fgmn.normalizedResidual` |
| `KP` | `A.fgmn.keyPolynomial` |
| `nuEquiv` | `A.fgmn.initialEquiv` |
| `letterZ` | `A.fgmn.letter` |
| all thirteen law fields | the CC-14 scalar laws (`Rgr_zero_of_above`, `Rgr_add`, `Rgr_mul`, `Rgr_ne_zero`, `Rres_mul`) and CC-15 class-facing laws B (`Rres_recipe`, `Rres_exists`, `KP_criterion`, `KP_irred`, `KP_keyAt`, `Rres_keyAt`, `nuEquiv_iff_Rres`, `letterZ_ne_zero`), consumed point-free |

## Honesty classification

The class remains a HYPOTHESIS CARRIER exactly as adjudicated (C.92: `fgmn_calculus_exists`
stays UNDECLARED per `C92_VACUITY`; no faithful unconditional statement exists over a bare
`DeepTower`).  The packaging theorem is CONDITIONAL on an FGMN model (`FGMNSourceData` +
`FGMNSourceLaws` at a key chain) — the landed discharge is FD-0's `r = 1`-anchored S2
records, packaged at `C130sg.s2_calculus_discharge` ([PK-2/U15]); the law fields remain
genuine source hypotheses at any other instance.  NO instance is declared (globally or
scoped): the packaging is a def + theorem,
so no downstream `[FGMNCalculus …]` binder is silently satisfied.  No new axiom, no `sorry`,
no `unsafe`, no statement weakening.

## Deliberately NOT here (other CC nodes)

The full S2 `ChainRealization` instance and its `#print axioms`/cite ledger (CC-17); the
socket applications (CC-18); any `FGMNCalculus`-conditional §10 theorem (the GENTOW2 supply
layer stays in leanspec until its own transcription nodes).

DEPENDS: C130la (CC-14: `FGMNSourceData.Rgr`, scalar laws A), C130lb (CC-15: class-facing
laws B), C130fg via both (CC-13: `FGMNSourceData`, `FGMNSourceLaws`, `ChainRealization`),
C130k via C130fg (`KeyChain`, `StageLive`), C83 (`DeepTower`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no instance declared.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O}

/-! ## The A-C.11 class twin (leanspec `FGMNCalculus`, field-for-field) -/

/-- NODE C.92 — the MacLane-chain certificate interface, the leanfinal twin of the enacted
A-C.11 class (`leanspec/Leanspec/ChapC.lean`, 2026-08-24 RE-SIGN — recorded amendment):
field-for-field, types byte-equal modulo the design-§7 substitution
`DeepTower ↦ DeepTower.{0, uKt}`.  Per-field provenance, the published-source print-reads,
and the seven decided design questions (index convention = next augmentation `R_{r+1}`;
scalar `Rgr` = degree-zero coefficient; `PrevGrade` removed; `r = 0` syntactic only; Gauss
transport = `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`) live in
`docs/in-progress/FGMN_ADJUDICATION_2026-08-24.md` (U9) on top of
`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` (U7).  [A-C.13, 2026-08-25 —
correction, mirrored byte-parallel from the enacted leanspec class]: U9 Q3's `PrevGrade`
removal is REVERSED per U14 (`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md`) —
`PrevGrade` restored as a field and `Rgr_mul` regains the `PrevGrade β'` premise;
`Rres_mul` stays plain (Cor 4.12(3)).  The class remains a HYPOTHESIS
CARRIER: `fgmn_calculus_exists` stays undeclared (C92_VACUITY); the conditional discharge is
`fgmn_model_calculus_nonempty` below (this file — [PK-2/U15]: the factored replacement of
the retired `chainRealization_calculus_nonempty`), fed by FGMN records at a key chain. -/
class FGMNCalculus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i

  ExactGrade : ℕ → Polynomial O → Prop
  AboveGrade : ℕ → Polynomial O → Prop
  -- [A-C.13, 2026-08-25 — U14 §8.1] cleared grades from the PRECEDING value group `Γ_r`
  -- (published Cor 4.12(2)'s `β ∈ Γ_{r−1}` after the index shift); restored — U9 Q3's
  -- removal was wrong at the graded level. Realization obligation: identify it with
  -- preceding-group membership (under full-current-group clearing, `e' ∣ β`; at S2,
  -- evenness).
  PrevGrade : ℕ → Prop

  Rgr : ℕ → Polynomial O → W.fld r
  Rres : Polynomial O → Polynomial (W.fld r)
  KP : Polynomial O → Prop
  nuEquiv : Polynomial O → Polynomial O → Prop
  letterZ : ℕ → W.fld r

  Rgr_zero_of_above : ∀ β (g : Polynomial O),
    AboveGrade β g → Rgr β g = 0
  Rgr_add : ∀ β (g h : Polynomial O),
    ExactGrade β g → ExactGrade β h → ExactGrade β (g + h) →
      Rgr β (g + h) = Rgr β g + Rgr β h
  -- [A-C.13, 2026-08-25] `PrevGrade β'` premise RESTORED (U14: published Cor 4.12(2) states
  -- the law ONLY with `β ∈ Γ_{r−1}`; the proof uses `s_r(β) = 0`; the unrestricted scalar
  -- law FAILS under odd-odd carry — coeff₀ of `X·P·Q` is 0 while the constant coefficients
  -- multiply to 1 at RP23's tooth).
  Rgr_mul : ∀ β β' (g h : Polynomial O),
    ExactGrade β g → ExactGrade β' h →
    PrevGrade β' →
      ExactGrade (β + β') (g * h) ∧
      Rgr (β + β') (g * h) = Rgr β g * Rgr β' h
  Rgr_ne_zero : ∀ β (g : Polynomial O),
    ExactGrade β g → g.natDegree < (keyAt r).natDegree → g ≠ 0 → Rgr β g ≠ 0
  Rres_mul : ∀ g h : Polynomial O,
    Rres (g * h) = Rres g * Rres h
  Rres_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
    Rres ((keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' -
        ∑ t ∈ Finset.range f',
          Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
  Rres_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → Irreducible ψ → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O,
        g.Monic ∧
        g.natDegree = e' * f' * (keyAt r).natDegree ∧
        Rres g = ψ
  KP_criterion : ∀ g : Polynomial O,
    g.Monic →
    g.natDegree = e' * f' * (keyAt r).natDegree →
    Irreducible (Rres g) →
    (Rres g).natDegree = f' →
    (Rres g).coeff 0 ≠ 0 →
      KP g
  KP_irred : ∀ g : Polynomial O, KP g → g.Monic → Irreducible g
  KP_keyAt : 0 < r → KP (keyAt r)
  Rres_keyAt : 0 < r → Rres (keyAt r) = 1
  nuEquiv_iff_Rres : ∀ g h : Polynomial O,
    KP g → KP h → (nuEquiv g h ↔ Rres g = Rres h)
  letterZ_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0

/-! ## The two leanspec consumers (byte-faithful def twins) -/

/-- the chain-normalizer MONOMIAL realizer: `n̂_{i+1}(k)` as an `O[x]`-polynomial from the
`towerNorm` exponent solve and the interface's chain keys.  (Leanspec
`FGMNCalculus.chainNorm`, byte-faithful.) -/
noncomputable def FGMNCalculus.chainNorm {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (i k : ℕ) : Polynomial O :=
  Polynomial.C (π ^ (W.towerNorm i k).1) * Polynomial.X ^ (W.towerNorm i k).2.1
    * ∏ j : Fin i, (I.keyAt (j.1 + 1)) ^ ((W.towerNorm i k).2.2 j)

/-- the normalizer-RATIO `ϑ`-carrier (GC-14's ratio form; no orientation committed):
`res(n̂(u')^t / n̂(t·u'))` read through the interface at grade `t·u'`.  (Leanspec
`FGMNCalculus.thetaRatio`, byte-faithful.) -/
noncomputable def FGMNCalculus.thetaRatio {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (t : ℕ) : W.fld r :=
  I.Rgr (t * u') ((I.chainNorm r u') ^ t) * (I.Rgr (t * u') (I.chainNorm r (t * u')))⁻¹

/-! ## The packaging map (design §7, FACTORED at [PK-2/U15, 2026-08-25]):
`FGMNSourceData + FGMNSourceLaws + KeyChain → FGMNCalculus`, no new axiom

The carrier-typed pair `ChainRealization.toCalculus`/`chainRealization_calculus_nonempty`
is RETIRED (packaging route, `PACKAGING_ROUTE_2026-08-25.md` §4.2): it never consumed the
carrier's `node`/`receiver`/`normalizer` or either compat field — only `keys`/`fgmn`/
`fgmnLaws` — so with the PK-1 carrier retype (the FGMN legs and `(e' f' u')` parameters
factored OUT of `ChainRealization`) the packaging is stated at exactly the data it always
consumed.  The elaboration authority is `scratch/U15_check.lean` §2 (`fgmnCalculusOf`,
field-for-field the retired `toCalculus` minus the carrier). -/

/-- The design-§7 projection map, factored through the FGMN pair alone ([PK-2/U15]; every
A-C.11 field is filled from `FGMNSourceData` + `FGMNSourceLaws` + the key chain, exactly
the fields the retired `ChainRealization.toCalculus` consumed): packaging only — no new
axiom, no new cite.  `Rgr` is CC-14's coefficient-zero projection `FGMNSourceData.Rgr`
(U9 Q2); `keyAt_deg` unpacks C130k's `StageLive` (definitionally `1 ≤ i ∧ i ≤ r`).
Deliberately a `def`, NOT an `instance`: no `[FGMNCalculus …]` binder may be silently
satisfied (`@[implicit_reducible]` is the compiler-required marking for a def of class
type — the U11 scratch's marking — and registers NO instance). -/
@[implicit_reducible] def fgmnCalculusOf {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} (K : KeyChain W) {e' f' u' : ℕ}
    (S : FGMNSourceData W K e' f' u') (hL : FGMNSourceLaws W K e' f' u' S) :
    FGMNCalculus W e' f' u' where
  keyAt := K.keyAt
  keyAt_one := K.keyAt_one
  keyAt_deg := fun i hi hir => K.keyAt_degree i ⟨hi, hir⟩
  ExactGrade := S.ExactGrade
  AboveGrade := S.AboveGrade
  PrevGrade := S.PrevGrade
  Rgr := S.Rgr
  Rres := S.normalizedResidual
  KP := S.keyPolynomial
  nuEquiv := S.initialEquiv
  letterZ := S.letter
  Rgr_zero_of_above := hL.Rgr_zero_of_above
  Rgr_add := hL.Rgr_add
  Rgr_mul := hL.Rgr_mul
  Rgr_ne_zero := hL.Rgr_ne_zero
  Rres_mul := hL.Rres_mul
  Rres_recipe := hL.Rres_recipe
  Rres_exists := hL.Rres_exists
  KP_criterion := hL.KP_criterion
  KP_irred := hL.KP_irred
  KP_keyAt := hL.KP_keyAt
  Rres_keyAt := hL.Rres_keyAt
  nuEquiv_iff_Rres := hL.nuEquiv_iff_Rres
  letterZ_ne_zero := hL.letterZ_ne_zero

/-- **NODE CC-16, the packaging theorem** (design §7's elaborated scratch theorem, against
the ACTUAL A-C.11 class; FACTORED at [PK-2/U15] — the retired
`chainRealization_calculus_nonempty` re-points here): an FGMN model — source data
satisfying the thirteen source laws at a key chain — yields the FGMN calculus.  No new
axiom — `#print axioms` below is Lean core.  The numerical hypotheses `he'`, `hf'`,
`hcop`, `hfloor` of the retired `fgmn_calculus_exists` draft belong to CONSTRUCTION of a
model (the S2-source campaign), not to this record-packaging function; there is still no
faithful theorem from a bare `DeepTower` to `Nonempty (FGMNCalculus …)` (C92_VACUITY
adjudication). -/
theorem fgmn_model_calculus_nonempty
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} (K : KeyChain W) {e' f' u' : ℕ}
    (S : FGMNSourceData W K e' f' u') (hL : FGMNSourceLaws W K e' f' u' S) :
    Nonempty (FGMNCalculus W e' f' u') :=
  ⟨fgmnCalculusOf K S hL⟩

/-! ## Anti-drift teeth: the design-§7 table rows, definitionally

Each data field of `fgmnCalculusOf` IS its design-§7 construction, by `rfl` — zero
rewriting room.  In particular `Rgr` is definitionally the coefficient-zero read of the
polynomial-valued graded residual (U9 Q2), through CC-14's `FGMNSourceData.Rgr`.
([PK-2/U15]: the teeth are the retired `toCalculus` teeth, restated verbatim at the
factored map — same right-hand sides, `A.keys`/`A.fgmn` replaced by the direct `K`/`S`.) -/

section Teeth

variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {e' f' u' : ℕ} {K : KeyChain W}
variable {S : FGMNSourceData W K e' f' u'}

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).keyAt = K.keyAt := rfl

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).ExactGrade = S.ExactGrade := rfl

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).AboveGrade = S.AboveGrade := rfl

/-- [A-C.13] the restored preceding-group predicate passes through unrewritten. -/
example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).PrevGrade = S.PrevGrade := rfl

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).Rgr = fun β g => (S.gradedResidual β g).coeff 0 := rfl

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).Rres = S.normalizedResidual := rfl

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).KP = S.keyPolynomial := rfl

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).nuEquiv = S.initialEquiv := rfl

example (hL : FGMNSourceLaws W K e' f' u' S) :
    (fgmnCalculusOf K S hL).letterZ = S.letter := rfl

end Teeth

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.FGMNCalculus
#print axioms Uniformity.Density.Tower.FGMNCalculus.chainNorm
#print axioms Uniformity.Density.Tower.FGMNCalculus.thetaRatio
#print axioms Uniformity.Density.Tower.fgmnCalculusOf
#print axioms Uniformity.Density.Tower.fgmn_model_calculus_nonempty

end AxCheck
