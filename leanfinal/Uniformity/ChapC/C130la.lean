/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130fg

/-!
# Uniformity.ChapC.C130la — the FGMN scalar laws A (chain-carrier node CC-14)

**Chain-carrier node CC-14** of `CHAIN_CARRIER_DESIGN_2026-08-24.md` (§7 consumer map A,
§10 row CC-14): from the POLYNOMIAL-VALUED source laws of CC-13's `FGMNSourceLaws`
(`C130fg.lean`), PROVE the scalar-coordinate theorems the A-C.11 `FGMNCalculus` class will
consume — the coefficient-zero reads of published Lemma 3.14, Corollary 4.12(1)–(3), and
Theorem 4.1/Corollary 4.9(1) in the scalar scope with the U9 degree fence.

## The U9 Q2 convention this implements (`FGMN_ADJUDICATION_2026-08-24.md` §4)

The scalar `Rgr β g` is the **degree-zero coefficient** of the polynomial-valued
`R_(r+1,β)(g)` transported to `W.fld r` — NOT evaluation at a letter, and NOT an assertion
that every exact-grade residual polynomial is constant.  Here that projection is landed as
the DEF `FGMNSourceData.Rgr` (design §7's table row `Rgr β g ↦ (fgmn.gradedResidual β g).coeff 0`)
— a derived packaging projection, deliberately NOT a field of `FGMNSourceData` (CC-13's
fields are unchanged; this file only adds defs/theorems in its namespaces).

## The five scalar laws (each named exactly as its A-C.11 consumer field)

Each theorem is CONDITIONAL on the source-law package `hL : FGMNSourceLaws W K e' f' u' S` —
the published clauses stay genuine source hypotheses (design §9); what is PROVED here, in
Lean core, is that the scalar coordinate follows from the polynomial-valued law:

* `FGMNSourceLaws.Rgr_zero_of_above` — published **Lemma 3.14** scalar coordinate: the
  graded residual vanishes on `P_β⁺` as a polynomial (U9 §4.1), so its coefficient zero is
  zero (`Polynomial.coeff_zero`).
* `FGMNSourceLaws.Rgr_add` — published **Corollary 4.12(1)** scalar coordinate: the graded
  additivity polynomial identity, read at coefficient zero (`Polynomial.coeff_add`).
* `FGMNSourceLaws.Rgr_mul` — published **Corollary 4.12(2)** scalar coordinate, WITH the
  exact-grade product conjunct: constant coefficients multiply
  (`Polynomial.mul_coeff_zero`); U9 Q3 removed the `PrevGrade` premise (after clearing,
  every class grade is already in `Γ_r`).  Components also exposed separately as
  `exactGrade_mul` and `Rgr_mul_eq`.
* `FGMNSourceLaws.Rres_mul` — published **Corollary 4.12(3)**: normalized multiplicativity,
  a direct transport (the A-C.11 `Rres` IS `normalizedResidual`, design §7); its own
  coefficient-zero read is `Rres_coeff_zero_mul`.
* `FGMNSourceLaws.Rgr_ne_zero` — published **Theorem 4.1 + Corollary 4.9(1)** in the scalar
  scope: nonvanishing at exact grade UNDER the U9 degree fence
  `g.natDegree < (K.keyAt r).natDegree` (U9 Q2: below the key degree the
  `φ_(r+1)`-expansion has only its `s = 0` term; exact grade alone would be FALSE — the
  fence is essential and is carried verbatim from the source law).

Bonus iterate (pure Lean-core corollary of `Rgr_mul`, no new source content):
`FGMNSourceLaws.Rgr_pow` — for `0 < n`, `g^n` has exact grade `n·β` and
`Rgr (n·β) (g^n) = (Rgr β g)^n` — the scalar shape the §10 recipe consumers read on key
powers.

## Coefficient-zero regressions (design §10 row CC-14: "coefficient-zero regressions pass")

The `Regressions` section carries `example`-teeth of three kinds: (i) SHAPE-FIT teeth — each
scalar law re-stated with the raw `(… ).coeff 0` read in place of `Rgr` and closed by the
theorem term itself, so the derived scalar laws are DEFINITIONALLY the coefficient-zero
reads of the polynomial-valued laws (e.g. the scalar of a product = product of scalars
under exact grades); (ii) the three generic coefficient-zero reads that carry the
projection (`coeff_zero`/`coeff_add`/`mul_coeff_zero`), pinned to their mathlib names;
(iii) a concrete numeric tooth over `ℤ` (degree-zero coefficient of a product = product of
the constant terms, `2 · 4 = 8`).

## Honesty classification

No new axiom, no `sorry`, no `unsafe`, no `True`-bodied statement, no instance of any
carrier, and no field added to CC-13's structures.  Every theorem is conditional on the
CC-13 law package exactly as the A-C.11 class fields are conditional on an instance; the
published clauses are NOT turned into Lean-core facts here — only their scalar-coordinate
projections are proved from them.

## Deliberately NOT here (later CC nodes)

Laws B — recipe/existence/key criterion/irreducibility/key residual/equivalence/letters
(CC-15, `C130lb.lean`); the packaging into the actual A-C.11 `FGMNCalculus` class and
`ChainRealization → Nonempty FGMNCalculus` (CC-16); any instance (CC-17).

DEPENDS: C130fg (CC-13: `FGMNSourceData`, `FGMNSourceLaws`), C130k via C130fg (`KeyChain`),
C83 via C130k (`DeepTower`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r} {K : KeyChain W} {e' f' u' : ℕ}

/-! ## The scalar projection (U9 Q2; design §7's `Rgr` row) -/

namespace FGMNSourceData

/-- U9 Q2: the A-C.11 scalar residual `Rgr β g` is the DEGREE-ZERO COEFFICIENT of the
polynomial-valued `R_(r+1,β)(g)` (published Def 3.13, transported to `W.fld r`).  A derived
packaging DEF (design §7), not a field: CC-13's source carrier stays polynomial-valued. -/
def Rgr (S : FGMNSourceData W K e' f' u') (β : ℕ) (g : Polynomial O) : W.fld r :=
  (S.gradedResidual β g).coeff 0

/-- `rfl` anti-drift pin: `Rgr` IS the coefficient-zero read of the polynomial-valued
graded residual — byte-for-byte design §7's table row, definitionally. -/
theorem Rgr_eq_coeff_zero (S : FGMNSourceData W K e' f' u') (β : ℕ) (g : Polynomial O) :
    S.Rgr β g = (S.gradedResidual β g).coeff 0 := rfl

end FGMNSourceData

/-! ## The scalar laws A (CC-14): Lemma 3.14, Cor 4.12(1)–(3), Thm 4.1/Cor 4.9 scalar -/

namespace FGMNSourceLaws

variable {S : FGMNSourceData W K e' f' u'}

/-- CC-14 scalar law — FGMN published **Lemma 3.14**, scalar coordinate (A-C.11 field shape
`Rgr_zero_of_above`): `R_(r+1,β)` vanishes on `P_β⁺` as a POLYNOMIAL (source law
`graded_zero_of_above`), hence its degree-zero coefficient vanishes (U9 §4.1 row 1). -/
theorem Rgr_zero_of_above (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β (g : Polynomial O), S.AboveGrade β g → S.Rgr β g = 0 := by
  intro β g hg
  simp only [FGMNSourceData.Rgr]
  rw [hL.graded_zero_of_above β g hg]
  exact Polynomial.coeff_zero 0

/-- CC-14 scalar law — FGMN published **Corollary 4.12(1)**, scalar coordinate (A-C.11
field shape `Rgr_add`): the polynomial additivity identity (source law `graded_add`) read
at coefficient zero via `Polynomial.coeff_add` (U9 §4.1 row 2; the exact-grade sum
hypothesis avoids asserting a nonzero-grade conclusion after cancellation). -/
theorem Rgr_add (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β h → S.ExactGrade β (g + h) →
        S.Rgr β (g + h) = S.Rgr β g + S.Rgr β h := by
  intro β g h hg hh hgh
  simp only [FGMNSourceData.Rgr]
  rw [hL.graded_add β g h hg hh hgh, Polynomial.coeff_add]

/-- CC-14 component — FGMN published **Corollary 4.12(2)**, the exact-grade product
conjunct alone: exact grades add on products (U9 Q3: no `PrevGrade` premise — after
clearing by `e(μ_r)` every class grade is already in `Γ_r`). -/
theorem exactGrade_mul (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β β' (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β' h → S.ExactGrade (β + β') (g * h) :=
  fun β β' g h hg hh => (hL.graded_mul β β' g h hg hh).1

/-- CC-14 scalar law — FGMN published **Corollary 4.12(2)**, scalar coordinate WITH the
exact-grade product conjunct (A-C.11 field shape `Rgr_mul`): the polynomial product
identity (source law `graded_mul`) read at coefficient zero — constant coefficients
multiply (`Polynomial.mul_coeff_zero`; U9 §4.1 row 3). -/
theorem Rgr_mul (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β β' (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β' h →
        S.ExactGrade (β + β') (g * h) ∧
          S.Rgr (β + β') (g * h) = S.Rgr β g * S.Rgr β' h := by
  intro β β' g h hg hh
  obtain ⟨hgrade, hres⟩ := hL.graded_mul β β' g h hg hh
  refine ⟨hgrade, ?_⟩
  simp only [FGMNSourceData.Rgr]
  rw [hres, Polynomial.mul_coeff_zero]

/-- CC-14 component — the scalar product identity of `Rgr_mul` alone: the scalar of a
product is the product of the scalars, under exact grades. -/
theorem Rgr_mul_eq (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β β' (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β' h →
        S.Rgr (β + β') (g * h) = S.Rgr β g * S.Rgr β' h :=
  fun β β' g h hg hh => (hL.Rgr_mul β β' g h hg hh).2

/-- CC-14 scalar law — FGMN published **Theorem 4.1 + Corollary 4.9(1)** in the scalar
scope (A-C.11 field shape `Rgr_ne_zero`), WITH the U9 degree fence
`g.natDegree < (K.keyAt r).natDegree`: below the key degree the `φ_(r+1)`-expansion has
only its `s = 0` term, so at exact grade the degree-zero coefficient is nonzero.  U9 Q2:
the fence is ESSENTIAL — exact grade alone would make this false; it is carried verbatim
from the source law `graded_scalar_nonzero`, which is already scalar-shaped in CC-13. -/
theorem Rgr_ne_zero (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β (g : Polynomial O),
      S.ExactGrade β g → g.natDegree < (K.keyAt r).natDegree → g ≠ 0 →
        S.Rgr β g ≠ 0 :=
  fun β g hg hdeg hne => hL.graded_scalar_nonzero β g hg hdeg hne

/-- CC-14 law — FGMN published **Corollary 4.12(3)** (A-C.11 field shape `Rres_mul`):
multiplicativity of the normalized residual.  A direct transport of the source law
`normalized_mul` — the A-C.11 `Rres` IS `normalizedResidual` (design §7), no coefficient
projection intervenes. -/
theorem Rres_mul (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ g h : Polynomial O,
      S.normalizedResidual (g * h) =
        S.normalizedResidual g * S.normalizedResidual h :=
  hL.normalized_mul

/-- CC-14 scalar corollary — the coefficient-zero read of Corollary 4.12(3): the constant
term of the normalized residual is multiplicative. -/
theorem Rres_coeff_zero_mul (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ g h : Polynomial O,
      (S.normalizedResidual (g * h)).coeff 0 =
        (S.normalizedResidual g).coeff 0 * (S.normalizedResidual h).coeff 0 := by
  intro g h
  rw [hL.normalized_mul g h, Polynomial.mul_coeff_zero]

/-- CC-14 iterate — pure Lean-core corollary of `Rgr_mul` (no new source content): for
`0 < n`, the `n`-th power of an exact-grade-`β` polynomial has exact grade `n·β` and its
scalar residual is the `n`-th power of the scalar — the shape the §10 recipe consumers
read on key powers.  Fenced by `0 < n`: grade-0 behavior of `g^0 = 1` is deliberately not
asserted (no source law values `1`). -/
theorem Rgr_pow (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ (β : ℕ) (g : Polynomial O), S.ExactGrade β g → ∀ n : ℕ, 0 < n →
      S.ExactGrade (n * β) (g ^ n) ∧ S.Rgr (n * β) (g ^ n) = S.Rgr β g ^ n := by
  intro β g hg n
  induction n with
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simpa using hg
    · obtain ⟨hgrade, hval⟩ := ih hm
      obtain ⟨hgrade', hres'⟩ := hL.graded_mul (m * β) β (g ^ m) g hgrade hg
      have hidx : (m + 1) * β = m * β + β := by ring
      have hpow : g ^ (m + 1) = g ^ m * g := pow_succ g m
      constructor
      · rw [hidx, hpow]
        exact hgrade'
      · rw [hidx, hpow]
        have hstep : S.Rgr (m * β + β) (g ^ m * g) =
            S.Rgr (m * β) (g ^ m) * S.Rgr β g := by
          simp only [FGMNSourceData.Rgr]
          rw [hres', Polynomial.mul_coeff_zero]
        rw [hstep, hval, pow_succ]

end FGMNSourceLaws

/-! ## Coefficient-zero regressions (design §10 row CC-14)

(i) SHAPE-FIT teeth: each scalar law re-stated with the raw `(…).coeff 0` read in place of
`Rgr`, closed by the theorem term ITSELF — so the derived scalar laws are definitionally
the coefficient-zero reads of the polynomial-valued laws, with zero rewriting room. -/

section Regressions

variable {S : FGMNSourceData W K e' f' u'}

/-- Tooth (i).1 — Lemma 3.14: the scalar vanishing IS the coefficient-zero read of the
polynomial vanishing. -/
example (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β (g : Polynomial O), S.AboveGrade β g → (S.gradedResidual β g).coeff 0 = 0 :=
  hL.Rgr_zero_of_above

/-- Tooth (i).2 — Cor 4.12(1): the scalar additivity IS the coefficient-zero read. -/
example (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β h → S.ExactGrade β (g + h) →
        (S.gradedResidual β (g + h)).coeff 0 =
          (S.gradedResidual β g).coeff 0 + (S.gradedResidual β h).coeff 0 :=
  hL.Rgr_add

/-- Tooth (i).3 — Cor 4.12(2): the scalar of a product = product of scalars under exact
grades, WITH the exact-grade product conjunct — the coefficient-zero read verbatim. -/
example (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β β' (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β' h →
        S.ExactGrade (β + β') (g * h) ∧
          (S.gradedResidual (β + β') (g * h)).coeff 0 =
            (S.gradedResidual β g).coeff 0 * (S.gradedResidual β' h).coeff 0 :=
  hL.Rgr_mul

/-- Tooth (i).4 — Thm 4.1/Cor 4.9(1) scalar scope: the fenced nonvanishing IS CC-13's
source field, with `Rgr` in place of the raw read. -/
example (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ β (g : Polynomial O),
      S.ExactGrade β g → g.natDegree < (K.keyAt r).natDegree → g ≠ 0 →
        (S.gradedResidual β g).coeff 0 ≠ 0 :=
  hL.Rgr_ne_zero

/-- Tooth (i).5 — Cor 4.12(3): the transported `Rres_mul` IS the source law. -/
example (hL : FGMNSourceLaws W K e' f' u' S) :
    ∀ g h : Polynomial O,
      S.normalizedResidual (g * h) =
        S.normalizedResidual g * S.normalizedResidual h :=
  hL.Rres_mul

/-- Tooth (i).6 — the `n = 2` power read: the scalar of `g²` at doubled grade is the
square of the scalar. -/
example (hL : FGMNSourceLaws W K e' f' u' S) (β : ℕ) (g : Polynomial O)
    (hg : S.ExactGrade β g) :
    (S.gradedResidual (2 * β) (g ^ 2)).coeff 0 =
      (S.gradedResidual β g).coeff 0 * (S.gradedResidual β g).coeff 0 := by
  simpa [sq, FGMNSourceData.Rgr] using (hL.Rgr_pow β g hg 2 (by norm_num)).2

/- (ii) The three generic coefficient-zero reads carrying the projection, pinned to their
mathlib names. -/

/-- Tooth (ii).1 — the zero read (`Rgr_zero_of_above`'s leg). -/
example : (0 : Polynomial ℤ).coeff 0 = 0 := Polynomial.coeff_zero 0

/-- Tooth (ii).2 — the additive read (`Rgr_add`'s leg). -/
example (p q : Polynomial ℤ) : (p + q).coeff 0 = p.coeff 0 + q.coeff 0 :=
  Polynomial.coeff_add p q 0

/-- Tooth (ii).3 — the multiplicative read (`Rgr_mul`'s leg): constant coefficients
multiply, in ANY commutative (semi)ring — the coefficient-zero projection is a ring map on
products with no exactness hypothesis needed at this generic level. -/
example (p q : Polynomial ℤ) : (p * q).coeff 0 = p.coeff 0 * q.coeff 0 :=
  Polynomial.mul_coeff_zero p q

/-- Tooth (iii) — concrete numeric read over `ℤ`: the degree-zero coefficient of
`(X + 2)(3X + 4)` is `2 · 4 = 8`, the product of the constant terms. -/
example :
    ((Polynomial.X + Polynomial.C 2) * (Polynomial.C 3 * Polynomial.X + Polynomial.C 4) :
        Polynomial ℤ).coeff 0 = 8 := by
  simp [Polynomial.mul_coeff_zero]

end Regressions

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.FGMNSourceData.Rgr
#print axioms Uniformity.Density.Tower.FGMNSourceData.Rgr_eq_coeff_zero
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rgr_zero_of_above
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rgr_add
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.exactGrade_mul
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rgr_mul
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rgr_mul_eq
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rgr_ne_zero
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rres_mul
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rres_coeff_zero_mul
#print axioms Uniformity.Density.Tower.FGMNSourceLaws.Rgr_pow

end AxCheck
