/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130fg

/-!
# Uniformity.ChapC.C130lb — FGMN laws B, class-facing (chain-carrier node CC-15)

**Chain-carrier node CC-15** of `CHAIN_CARRIER_DESIGN_2026-08-24.md` (§4.3's law table, §7
consumer map A, §10 row CC-15): from CC-13's `FGMNSourceLaws` (C130fg), prove the
CLASS-FACING theorems for the B-side laws of A-C.11 (`FGMN_ADJUDICATION_2026-08-24.md` §11)
at U9's decided scopes — the recipe expansion, the existence law, the key-polynomial
criterion, irreducibility over `O[x]`, the carried key's own `KP`-membership and residual,
the ν-equivalence ↔ residual-equality law, and the letter nonvanishing.

Each theorem below is byte-shaped to its A-C.11 class field under §7's packaging dictionary
(`Rres := normalizedResidual`, `KP := keyPolynomial`, `nuEquiv := initialEquiv`,
`letterZ := letter`, `keyAt := K.keyAt`, scalar `Rgr β g := (gradedResidual β g).coeff 0` —
inlined here, never a new definition, so CC-16 stays the sole packaging site).  CC-16 fills
the actual leanspec `FGMNCalculus` record with these theorems.

## U9's decided scopes (transcribed, not weakened, not broadened)

* `Rres_exists` requires **`Irreducible ψ`** (U9 §10: the printed Theorem 5.7 proof starts
  from a monic irreducible `ψ`; the broader monic-only `O[x]` output was not justified) and
  is fenced by `0 < r` (U9 Q4).
* `KP_criterion` carries the **nonzero-constant leg** `(Rres g).coeff 0 ≠ 0` (U9 §4.1: it is
  what forces `s(g) = 0` in the Theorem 5.7 degree argument).
* `KP_keyAt` and `Rres_keyAt` are fenced by `0 < r` (U9 Q4: equation (11)'s `r = 0` base
  behavior differs — `R_0(φ) = y`, not `1` — and is deliberately not asserted).
* `nuEquiv_iff_Rres` keeps **both** `KP` hypotheses (U9 §4.1: published Prop 5.6(2)⇔(3) is a
  statement about key polynomials).
* `letterZ_ne_zero` is fenced by the live letter range `1 ≤ i ≤ r` (U9 §3: `z_i` is defined
  before the following augmentation and embeds into `F_(r+1)`); at `r = 0` the range is
  empty, which is Q4's fencing for the letters.

## The executed OPEN-GAUSS resolution (U9 Q5, §7)

Published Lemma 1.8 proves key polynomials irreducible **in `K_v[x]`**; published
Corollary 1.10 gives `KP(μ) ⊂ O[x]` (already built into the `Polynomial O` domain at CC-13).
The transport from `K_v[x]`-irreducibility to `O[x]`-irreducibility is Gauss's lemma, landed
in pinned mathlib as `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`
(`Mathlib/RingTheory/Polynomial/GaussLemma.lean`; name re-verified at HEAD, and the
`IsIntegrallyClosed O` instance resolves from the DVR hypotheses).  This file EXECUTES that
resolution: `irreducible_of_fraction_map_irreducible` is the proved Gauss leg, and
`FGMNSourceData.key_irreducible_of_fraction_map` derives the full `key_irreducible` source
field from Lemma 1.8's genuine fraction-field statement — so a future realization owes only
the `K_v`-to-fraction-field dictionary (U9 §7: "a realization transport, not a missing Gauss
lemma") plus Lemma 1.8 itself, never the Gauss step.

## Honesty classification

The theorems named after class fields are TRANSPORTS: they restate the CC-13 source
obligations in the class-facing vocabulary and are proved by projection, so any drift
between C130fg and A-C.11 surfaces here as a type error.  They do not discharge the source
obligations — those remain genuine hypotheses (fields of `FGMNSourceLaws`) until their
published clauses are transcribed against a realized instance.  The only newly PROVED
mathematical content is the Gauss transport (mathlib) and the derived corollary
`nuEquiv_ne_of_Rres` (the direction C.103 consumes, subsumed by the iff).  No `sorry`, no
new axiom, no `unsafe`, no statement weakening, no scalar-`Rgr` definition.

## Deliberately NOT here (other CC nodes)

Laws A — `Rgr_zero_of_above`, `Rgr_add`, `Rgr_mul`, `Rgr_ne_zero`, `Rres_mul` and their
coefficient-zero regressions (CC-14, parallel); the packaging into the actual leanspec
`FGMNCalculus` (CC-16); every instance and every socket application (CC-17/CC-18).

DEPENDS: C130fg (CC-13: `FGMNSourceData`, `FGMNSourceLaws`), C130k via C130fg (`KeyChain`),
C83 (`DeepTower`), mathlib `Mathlib/RingTheory/Polynomial/GaussLemma.lean`.

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uKv

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r} {K : KeyChain W} {e' f' u' : ℕ}
variable {S : FGMNSourceData W K e' f' u'}

/-! ## The executed Gauss transport (U9 Q5: `KP_irred` loses OPEN-GAUSS) -/

/-- The Gauss leg, EXECUTED (U9 Q5/§7): a monic `g ∈ O[x]` that is irreducible over a
fraction field of `O` is irreducible in `O[x]`.  This is pinned mathlib's
`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (Gauss's lemma for
integrally closed domains; the DVR `O` is a PID, hence a UFD, hence integrally closed, and
the instance chain resolves).  This is the transport that published Lemma 1.8 (irreducible
in `K_v[x]`) + Corollary 1.10 (`KP(μ) ⊂ O[x]`) need to reach A-C.11's `KP_irred`. -/
theorem irreducible_of_fraction_map_irreducible
    {Kv : Type uKv} [Field Kv] [Algebra O Kv] [IsFractionRing O Kv]
    {g : Polynomial O} (hg : g.Monic)
    (hirr : Irreducible (g.map (algebraMap O Kv))) : Irreducible g :=
  (hg.irreducible_iff_irreducible_map_fraction_map (K := Kv)).mpr hirr

/-- The OPEN-GAUSS resolution applied to the source package (U9 Q5, design §4.3's
`key_irreducible` row): from published Lemma 1.8's GENUINE fraction-field statement — every
key polynomial is irreducible over `K_v[x]` — the full `FGMNSourceLaws.key_irreducible`
obligation follows.  A realization therefore owes Lemma 1.8 (over its fraction-field model)
and the `K_v`-dictionary only; the `O[x]` upgrade is a theorem, not a source hypothesis.
The conclusion is verbatim the type of the `key_irreducible` field. -/
theorem FGMNSourceData.key_irreducible_of_fraction_map
    {Kv : Type uKv} [Field Kv] [Algebra O Kv] [IsFractionRing O Kv]
    (S : FGMNSourceData W K e' f' u')
    (hfrac : ∀ g : Polynomial O, S.keyPolynomial g → g.Monic →
      Irreducible (g.map (algebraMap O Kv))) :
    ∀ g : Polynomial O, S.keyPolynomial g → g.Monic → Irreducible g :=
  fun g hkp hm => irreducible_of_fraction_map_irreducible hm (hfrac g hkp hm)

/-! ## Class-facing laws B (A-C.11 §11 shapes under the §7 packaging dictionary)

Each theorem restates its `FGMNSourceLaws` field in the exact A-C.11 class-field shape, with
the scalar read spelled `(S.gradedResidual β g).coeff 0` (U9 Q2) — CC-16 fills the leanspec
record from these. -/

namespace FGMNSourceLaws

/-- Class-facing `Rres_recipe` (FGMN published Definition 1.6, Definition 3.13,
equation (11), Corollary 4.12(1)/(2)): the residual of the recipe key is the `y`-polynomial
of the graded slot reads, with the scalar slots as degree-zero coefficients (U9 Q2).  Every
slot is fenced below the carried key degree, where the graded residual is exactly its
constant coefficient (U9 §4.1). -/
theorem Rres_recipe (hL : FGMNSourceLaws W K e' f' u' S)
    (khat : ℕ → Polynomial O)
    (hgrade : ∀ t, t < f' → S.ExactGrade ((f' - t) * u') (khat t))
    (hdeg : ∀ t, t < f' → (khat t).natDegree < (K.keyAt r).natDegree) :
    S.normalizedResidual ((K.keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (K.keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
        Polynomial.C ((S.gradedResidual ((f' - t) * u') (khat t)).coeff 0) *
          Polynomial.X ^ t :=
  hL.normalized_recipe khat hgrade hdeg

/-- Class-facing `Rres_exists` (FGMN published Theorem 5.7's construction) at U9 §10's
decided scope: the residual input `ψ` is monic AND **irreducible** — the printed proof
constructs a key polynomial from an irreducible `ψ` and only then Corollary 1.10 supplies
`O[x]`; the broader monic-only output was not justified.  Fenced by `0 < r` (U9 Q4). -/
theorem Rres_exists (hL : FGMNSourceLaws W K e' f' u' S) (hr : 0 < r)
    (ψ : Polynomial (W.fld r)) (hmonic : ψ.Monic) (hirr : Irreducible ψ)
    (hdeg : ψ.natDegree = f') (hc0 : ψ.coeff 0 ≠ 0) :
    ∃ g : Polynomial O, g.Monic ∧
      g.natDegree = e' * f' * (K.keyAt r).natDegree ∧
      S.normalizedResidual g = ψ :=
  hL.normalized_exists hr ψ hmonic hirr hdeg hc0

/-- Class-facing `KP_criterion` (FGMN published Lemma 5.2(2), Corollary 4.9, and the
degree-forcing display in the proof of Theorem 5.7): the key-polynomial criterion at the
recipe degree, carrying U9's **nonzero-constant leg** `(Rres g).coeff 0 ≠ 0` — it is what
forces `s(g) = 0` in the Theorem 5.7 degree argument (U9 §4.1). -/
theorem KP_criterion (hL : FGMNSourceLaws W K e' f' u' S)
    (g : Polynomial O) (hmonic : g.Monic)
    (hdeg : g.natDegree = e' * f' * (K.keyAt r).natDegree)
    (hirr : Irreducible (S.normalizedResidual g))
    (hresdeg : (S.normalizedResidual g).natDegree = f')
    (hc0 : (S.normalizedResidual g).coeff 0 ≠ 0) :
    S.keyPolynomial g :=
  hL.key_criterion g hmonic hdeg hirr hresdeg hc0

/-- Class-facing `KP_irred` (FGMN published Lemma 1.8 + Corollary 1.10 + the Gauss
transport executed above): key polynomials are irreducible over `O[x]`.  The source field
already carries the `O[x]` conclusion; `FGMNSourceData.key_irreducible_of_fraction_map`
shows that field is dischargeable from Lemma 1.8's fraction-field statement alone. -/
theorem KP_irred (hL : FGMNSourceLaws W K e' f' u' S)
    (g : Polynomial O) (hkp : S.keyPolynomial g) (hmonic : g.Monic) :
    Irreducible g :=
  hL.key_irreducible g hkp hmonic

/-- Class-facing `KP_keyAt` (FGMN published Proposition 1.7(4)): the carried key
`φ_(r+1) = keyAt r` is a key polynomial for `μ_(r+1)`; fenced by `0 < r` (U9 Q4). -/
theorem KP_keyAt (hL : FGMNSourceLaws W K e' f' u' S) (hr : 0 < r) :
    S.keyPolynomial (K.keyAt r) :=
  hL.carried_key_is_key hr

/-- Class-facing `Rres_keyAt` (FGMN published equation (11)): the carried key's own
normalized residual is trivial, `R_(r+1)(φ_(r+1)) = 1` — the non-equivalence pivot C.103
reads.  Fenced by `0 < r` (U9 Q4: at `r = 0` equation (11) gives `y`, not `1`, and the base
convention is deliberately not asserted). -/
theorem Rres_keyAt (hL : FGMNSourceLaws W K e' f' u' S) (hr : 0 < r) :
    S.normalizedResidual (K.keyAt r) = 1 :=
  hL.carried_key_residual hr

/-- Class-facing `nuEquiv_iff_Rres` (FGMN published Proposition 5.6(2) iff (3)): for KEY
polynomials — both `KP` hypotheses retained per U9 §4.1 — initial-form equivalence is
equality of normalized residuals. -/
theorem nuEquiv_iff_Rres (hL : FGMNSourceLaws W K e' f' u' S)
    (g h : Polynomial O) (hg : S.keyPolynomial g) (hh : S.keyPolynomial h) :
    S.initialEquiv g h ↔ S.normalizedResidual g = S.normalizedResidual h :=
  hL.initial_iff_residual g h hg hh

/-- The consumed direction (the pre-A-C.11 class field shape, derived here as a corollary
of the iff): distinct normalized residuals of key polynomials are never ν-equivalent —
published Proposition 5.6's contrapositive, the direction C.103's non-equivalence pivot
reads. -/
theorem nuEquiv_ne_of_Rres (hL : FGMNSourceLaws W K e' f' u' S)
    (g h : Polynomial O) (hg : S.keyPolynomial g) (hh : S.keyPolynomial h)
    (hne : S.normalizedResidual g ≠ S.normalizedResidual h) :
    ¬ S.initialEquiv g h :=
  fun heq => hne ((hL.initial_iff_residual g h hg hh).mp heq)

/-- Class-facing `letterZ_ne_zero` (FGMN published §3.3, following Lemma 3.11): the residue
letters `z_i` are nonzero on the live range `1 ≤ i ≤ r` (U9 §3: `z_i` is defined before the
following augmentation and embeds into `F_(r+1)`); at `r = 0` the range is empty — Q4's
letter fencing. -/
theorem letterZ_ne_zero (hL : FGMNSourceLaws W K e' f' u' S)
    (i : ℕ) (h1 : 1 ≤ i) (hr : i ≤ r) : S.letter i ≠ 0 :=
  hL.letter_ne_zero i h1 hr

end FGMNSourceLaws

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.irreducible_of_fraction_map_irreducible
#print axioms Uniformity.Density.Tower.FGMNSourceData.key_irreducible_of_fraction_map
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rres_recipe
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rres_exists
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.KP_criterion
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.KP_irred
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.KP_keyAt
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rres_keyAt
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.nuEquiv_iff_Rres
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.nuEquiv_ne_of_Rres
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.letterZ_ne_zero

end AxCheck
