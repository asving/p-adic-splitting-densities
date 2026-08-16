/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E11
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Squarefree.Basic

/-!
# Uniformity.ChapE.E18 — the mid-chain peel `(MID-PEEL)`/`(MID-MASS)`

**Chapter E, NODE E.18** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §5 — HE7.A clause 5's
identity layer), ENV-E2 (+ `[IsDomain O]`).

Dividing a squarefree monic `G` of degree `D·ν` by a monic divisor `Φ` of degree `D` peels off
exactly one unit of mass:

* `(MID-MASS)`: the quotient `G′` is monic of degree `D·(ν − 1)` — the represented degree drops
  by exactly `D`, the mass by exactly one;
* key-freeness of the quotient: `G′` and `Φ` are coprime over the fraction field, by
  `EFF.T2.23`'s derivation verbatim — *"a common irreducible divisor of `G′` and `Φ` would
  square-divide `G`"*. Landed in the mathlib-native form: a common divisor `d` of `G′` and `Φ`
  gives `d * d ∣ Φ * G′ = G`, which is literally the `Squarefree` hypothesis applied to `d`
  (`IsRelPrime`), and over the field `FractionRing O` — where `Polynomial` is a euclidean, hence
  principal-ideal, domain — `IsRelPrime.isCoprime` upgrades that to `IsCoprime`. No `gcd`
  spelling and no irreducible-factor case split is needed; the "irreducible" in the source's
  sentence is an expository choice, the argument runs for an arbitrary common divisor.

⚠ **THE SIGNED CONTRACT IS (i)+(ii) ONLY** (blueprint SIGNATURE NOTE, A-E.1/E-D13). STATEMENT
clause (iii) — `ν = 1 ⟹ G′ = 1`, the degenerate guard "no successor exists" — has NO conjunct
in the signed signature and none is added here. It follows from the signed conclusion in one
line: at `ν = 1` the quotient is monic of `natDegree D * (1 − 1) = 0`, so
`Polynomial.Monic.natDegree_eq_zero` (`.mp`) gives `G′ = 1`. Recorded so the missing conjunct is
not read as a transcription loss.

⚠ **`(MP1)` FENCE — the clause's conditionality is NOT this node's** (blueprint, verbatim in
force). This file proves the PEEL IDENTITY layer only. Items 2–5 of the `(MID-PEEL)` input suite
— `(WINDOW)` for `G′`, its full development with `(ACCOUNT)` and the S1.7 test assertions, and
the peeled key's certified orbit/`(e,f)` decomposition — are supplied elsewhere: at the original
level-one key by the level-1 instance (E.22), at a RECENTERED level-one key by `(MP1)`, which is
OPEN and carried at E.40, and at level two by S1.8B = E.42. Nothing in this file states or
licenses any of them.

The `hD : 0 < D` hypothesis of the frozen signature is carried but unconsumed: the degree
identity `D·ν − D = D·(ν − 1)` is exact in `ℕ` for every `D` once `1 ≤ ν`, and the coprimality
half never looks at degrees (see the `linter.unusedVariables` note at the declaration). No
strength is lost — the landed statement is the signed one verbatim.

DEPENDS: E.11 (the `IsCoprime`-over-`FractionRing O` key-freeness spelling, adopted here
unchanged) · mathlib `Polynomial.Monic.of_mul_monic_left`, `Polynomial.Monic.natDegree_mul`,
`Polynomial.map_mul`, `IsRelPrime.isCoprime`.

SOURCE: `EFF.T2.23` (the `(MID-PEEL)`/`(MID-MASS)` displays; the separability ⟹ key-freeness
derivation, verbatim; "If ν = 1, G′ = 1 and no successor exists"; "The peel occurs before
`(WINDOW)` so +∞ is never fed to Newton accounting"); `EFF.T2.31` clause 5 ("The quotient is
key-free, its mass is smaller by one, and its represented degree is smaller by D; the peeled
boundary roots are discharged by their certified boundary/orbit decomposition, which is item 5
of the `(MID-PEEL)` input suite and is a HYPOTHESIS of this clause, not a consequence of the
peel identity").

TEETH: S7 reducible/recentered-key boundary attacks; Pass 2's several-boundary-factor tooth —
the identity layer is a Lean theorem here, and the input suite stays split by level exactly as
the ledger has it (nothing in this file closes it).

ENVIRONMENT: ENV-E2 + `[IsDomain O]`.

## Status

Sorry-free. `midPeel` reports exactly the Lean-core triple
`{propext, Classical.choice, Quot.sound}` — `Classical.choice` arrives through the
`FractionRing`/`Field`/`EuclideanDomain` instance graph, not through any project axiom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- The signed hypothesis `hD : 0 < D` is kept (frozen signature) but unconsumed: `ℕ`-subtraction
-- never enters — the degree is read off `D + G'.natDegree = D * ν` by cancellation, which is
-- exact at every `D`.
set_option linter.unusedVariables false in
/-- **E.18 — the mid-chain peel** (`(MID-PEEL)`/`(MID-MASS)`, `EFF.T2.23`). Peeling a monic
degree-`D` divisor `Φ` off a squarefree monic `G` of degree `D * ν` (`ν ≥ 1`) leaves a monic
quotient of degree `D * (ν − 1)` — mass down by exactly one, represented degree down by exactly
`D` — which is key-free against `Φ`: coprime over the fraction field. -/
theorem midPeel {O : Type*} [CommRing O] [IsDomain O] {G Φ : Polynomial O} {D ν : ℕ}
    (hΦ : Φ.Monic) (hΦd : Φ.natDegree = D) (hG : G.Monic) (hGd : G.natDegree = D * ν)
    (hν : 1 ≤ ν) (hD : 0 < D)
    (hsq : Squarefree (G.map (algebraMap O (FractionRing O)))) (hdvd : Φ ∣ G) :
    ∃ G' : Polynomial O, G = Φ * G' ∧ G'.Monic ∧ G'.natDegree = D * (ν - 1) ∧
      IsCoprime (G'.map (algebraMap O (FractionRing O)))
        (Φ.map (algebraMap O (FractionRing O))) := by
  obtain ⟨G', rfl⟩ := hdvd
  -- (MID-MASS), first half: the quotient of two monics is monic
  have hG'monic : G'.Monic := hΦ.of_mul_monic_left hG
  refine ⟨G', rfl, hG'monic, ?_, ?_⟩
  · -- (MID-MASS), second half: degrees add, so `deg G' = Dν − D = D(ν−1)`
    have hadd : Φ.natDegree + G'.natDegree = D * ν := by
      rw [← hΦ.natDegree_mul hG'monic]; exact hGd
    obtain ⟨n, rfl⟩ : ∃ n, ν = n + 1 := ⟨ν - 1, by omega⟩
    have hcancel : D + G'.natDegree = D + D * n := by
      rw [hΦd] at hadd; rw [hadd]; ring
    simpa using Nat.add_left_cancel hcancel
  · -- key-freeness: a common divisor squares into `G`, which is squarefree
    have hrel : IsRelPrime (G'.map (algebraMap O (FractionRing O)))
        (Φ.map (algebraMap O (FractionRing O))) := by
      intro d hdG' hdΦ
      refine hsq d ?_
      rw [Polynomial.map_mul]
      exact mul_dvd_mul hdΦ hdG'
    exact hrel.isCoprime

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.midPeel

end AxCheck
