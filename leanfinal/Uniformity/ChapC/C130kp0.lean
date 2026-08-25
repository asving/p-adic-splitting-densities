/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp8

/-!
# Uniformity.ChapC.C130kp0 — S2-source plan node KP-0

**S2-source plan node KP-0** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 row KP-0
"initial-form predicates", dependencies NV-5, RP-8, U12 `MuEquiv`/`MuDivides` prototypes):
define honest `initialEquiv`, μ-divisibility, μ-minimality, and key-polynomialhood in the
concrete model — the value-equation forms of FGMN published Definition 1.2 and Definition
1.4 (§1.2), instantiated at the LANDED level-two value.

## The anchoring (the RP chain's decided realization)

Per C130rp0's module docstring and C130rp11's recorded course correction, the landed
concrete operators realize `FGMNSourceData.nextValue := μ₂` at `r = 1` with development key
`Φ′ = keyAt 1 = x² − 2` (`(s2Frame h2 hq).key`; FGMN's `φ₂`).  The predicates below
therefore anchor at

* μ = μ₂ = `s2Hgt₂ h2 hq` (C130s6/C130nv3/C130nv5's landed cleared value, a genuine
  `AddValuation` by NV-5), and
* initial forms are read through the graded residual `s2GradedRes` at the input's own exact
  grade `s2GradeOf` (C130rp1/C130rp8) — see the graded-piece characterization below.

## The FGMN meanings transcribed (published Definition 1.2 / Definition 1.4, print-read)

Published Definition 1.2 (verbatim genre, `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`
lines 196–204):

* "`g ∼µ h` … if and only if `µ(g − h) > µ(g) = µ(h)` or `g = h = 0`" — ★ `S2InitialEquiv`,
  the explicit VALUE criterion (no graded-algebra carrier is smuggled in), exactly U12's
  `MuEquiv` prototype shape at the concrete μ₂.
* "`h |µ g` … if and only if `g ∼µ hf` for some `f ∈ K[x]`" — ★ `S2MuDvd`, U12's
  `MuDivides` prototype shape (the initial-form divisibility of published Prop 1.7's genre,
  through Definition 1.2's own equivalent factor criterion).
* "`φ` is `µ-minimal` if `deg φ > 0` and `φ ∤µ g` for any non-zero `g ∈ K[x]` with
  `deg g < deg φ`" — ★ `S2MuMinimal` (the `deg φ > 0` clause is kept, unlike U12's
  prototype which derived it from monicity; this file is the literal Def 1.2 form).
* "`φ` is `µ-irreducible` if `Hµ(φ)Gr(µ)` is a non-zero prime ideal" — ★ `S2MuIrreducible`,
  rendered through `S2MuDvd` as in U12's prototype: `φ ≠ 0` (the ideal is nonzero iff
  `Hµ(φ) ≠ 0` iff `φ ≠ 0`), properness `¬ φ ∣µ 1` (the ideal is the whole ring iff `Hµ(φ)`
  is a unit iff `1 = Hµ(φ)Hµ(q) = Hµ(φq)` for some `q`, i.e. `φ ∣µ 1` — nonzero
  homogeneous elements of `Gr(µ)` are exactly the `Hµ(f)`), and homogeneous primality
  `φ ∣µ gh → φ ∣µ g ∨ φ ∣µ h` (for the principal homogeneous ideal `Hµ(φ)Gr(µ)`,
  primality is tested on homogeneous elements, which are the `Hµ(g)`; membership
  `Hµ(g) ∈ Hµ(φ)Gr(µ)` reduces to `φ ∣µ g` by taking the complementary-degree homogeneous
  component of the cofactor).
* Published Definition 1.4: "A key polynomial for the valuation `µ` is a monic polynomial
  `φ ∈ K[x]` which is `µ-minimal` and `µ-irreducible`" — ★ `S2KeyPoly` = monic ∧
  `S2MuMinimal` ∧ `S2MuIrreducible`.

`S2InitialEquiv`/`S2KeyPoly` have byte-for-byte the C130fg field shapes
`FGMNSourceData.initialEquiv : Polynomial O → Polynomial O → Prop` /
`keyPolynomial : Polynomial O → Prop` (shape pins below); the `Polynomial O` domain builds
in published Cor 1.10's `KP(µ) ⊂ O[x]` exactly as the C130fg field docstring demands.

## What lands beyond the definitions

* **the equivalence bank**: `S2InitialEquiv` is reflexive, symmetric, transitive
  (`S2InitialEquiv_equivalence`), preserves the value (`S2InitialEquiv_hgt_eq`), the exact
  grade, and the extracted grade `s2GradeOf`; zero laws both sides.
* ★ **the graded-piece characterization** (`S2InitialEquiv_iff_gradedRes`): at a COMMON
  exact grade β, `g ∼µ₂ h ↔ R_β(g) = R_β(h)` — a genuine iff, both directions through
  RP-2's strong add law (`s2GradedRes_add_of_le`), RP-1's vanishing law
  (`s2GradedRes_zero_of_above`), and RP-5/RP-6's nonvanishing at exact grade
  (`s2GradedRes_ne_zero_of_exact`).  This is the honest concrete content of "equal initial
  forms `Hµ(g) = Hµ(h)`" at the landed operators: the graded residual IS the coordinate of
  the initial form.
* **the `s2NormRes` tie** (`s2NormRes_eq_of_initialEquiv`): `g ∼µ₂ h → R₃(g) = R₃(h)` —
  the KP-7 genre's forward direction, falling out of the characterization plus RP-8's
  grade-extraction pins.  (The converse for key polynomials is KP-8/KP-9's core, published
  Prop 5.6, NOT claimed here.)
* **`S2MuDvd` basics**: ordinary divisibility implies μ-divisibility, everything μ-divides
  `0`, congruence along `S2InitialEquiv`.
* **teeth** (increment 3): the odd-carry engine `not_S2MuDvd_key_of_even_grade`
  (an even-grade input with nonzero residual scalar is NOT μ₂-divisible by `Φ′` — the carry
  `y` of RP-4's twisted product law forces a zero scalar on every `Φ′·q` at even grade);
  short digits have even grade (`S2ExactGrade_even_of_natDegree_lt_two`, the same parity
  computation as C130rp11's recorded vacuity finding); ★ **`Φ′` is μ₂-minimal**
  (`s2MuMinimal_key`, also spelled at `x² − 2`) — published Prop 1.7's minimality clause
  for the carried key, machine-proved from the landed banks, so `S2KeyPoly Φ′` reduces to
  the primality conjunct (`s2KeyPoly_key_of_muIrreducible`; the primality core is KP-2's
  row, NOT claimed here); `Φ′ ∣µ₂ Φ′²`; and the two lift teeth at RP-12's landed
  degree-four witness `Φ′² + 4x` (grade 10, residual `X + 1`): it is NOT initial-equivalent
  to `Φ′²` (the proper-augmentation/MacLane genre: `R₁₀(Φ′²) = X ≠ X + 1`) and NOT
  μ₂-divisible by `Φ′` (the engine at grade 10).

## What this node does NOT claim (honesty scope)

* No `S2MuIrreducible Φ′` / `S2KeyPoly Φ′` outright: the primality of the initial form is
  KP-2's CORE row (published Lemma 5.2/Theorem 5.7 substance).  Here only the reduction
  `S2MuIrreducible Φ′ → S2KeyPoly Φ′` and the minimality half are proved.
* No `key_criterion`/`key_irreducible`/`initial_iff_residual` field instances (KP-1..KP-9,
  FD-0).  No `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` instance.
* The literal carried-key field instance at `keyAt 2 = composedKey` (KP-6's row) is not
  touched: the composed key's grade/residual teeth are not landed; the degree-four lift
  `Φ′² + 4x` used in the teeth is RP-12's landed witness of the same genre at `r = 1`.
* The graded-piece characterization is stated at a COMMON exact grade; for distinct grades
  `S2InitialEquiv` simply fails on the value clause (`S2InitialEquiv_hgt_eq`).
* The `Gr(µ)` prose above (units/homogeneous primality) justifies the FIDELITY of the
  `S2MuDvd` rendering of Definition 1.2's ideal clauses; no graded algebra is constructed,
  exactly as in U12's adjudicated prototype.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements): the four
predicate definitions (`S2InitialEquiv`, `S2MuDvd`, `S2MuMinimal`, `S2MuIrreducible`,
`S2KeyPoly` — the Def 1.2/1.4 transcriptions and the prime-ideal-through-divisibility
rendering), `S2InitialEquiv_iff_gradedRes`, and the odd-carry engine
`not_S2MuDvd_key_of_even_grade`.

**DEPENDS.** C130rp8 (`s2GradeOf`, `s2NormRes`, `s2NormRes_of_exact`,
`s2GradedRes_coeff_zero_ne_zero_of_exact`, `S2ExactGrade_s2GradeOf`) · C130rp6
(`s2GradedRes_ne_zero_of_exact`) · C130rp4 (`s2GradedRes_mul_of_exact`) · C130rp2
(`s2GradedRes_add_of_le`, `le_dvSupp_of_exact`, `tooth_C4X_grade`, `tooth_sum_exact`,
`tooth_gradedRes_add_exact`) · C130rp1 (`s2GradedRes`, `s2GradedRes_zero`,
`s2GradedRes_zero_of_above`, `tooth_gradedRes_key`, `tooth_gradedRes_key_sq`) · C130rp0
(`S2ExactGrade`/`S2AboveGrade` + normal forms + `S2ExactGrade_mul`/`_exists`/`_unique`/
`_not_zero`, `tooth_key`, `tooth_key_sq`) · C130s6 (`s2Hgt₂` bank, `dvSupp_neg`,
`dvSupp_eq_inf_range`, `toZ_inj`) · C130nv (`s2Hgt₂_eq_top_iff`) · C35b (`key_eq`,
`s2Key_natDegree`) · C97 (`s2Key`) · C127 (`KeyFrame.natDegree_key_pos`,
`KeyFrame.stageHeight_zero`) · C118a (`smul_top_pos`) · B.04 (`dev_eq_zero_of_lt`) ·
mathlib (`Polynomial` coefficient bank, `WithTop` order bank).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130kp0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp2 Uniformity.Density.Tower.C130rp4
open Uniformity.Density.Tower.C130rp6 Uniformity.Density.Tower.C130rp8

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — ★ NODE KP-0: the four honest predicates (published Def 1.2 / Def 1.4)

All four anchor at μ = μ₂ = `s2Hgt₂ h2 hq` (the RP chain's decided `nextValue` realization
at `r = 1`, key `Φ′`); value-equation forms, U12's prototype shapes at the concrete value. -/

/-- ★ **`S2InitialEquiv g h` — FGMN published Definition 1.2's `g ∼µ h` at μ₂** (the
explicit value criterion: "`µ(g − h) > µ(g) = µ(h)` or `g = h = 0`"; U12's `MuEquiv`
prototype shape at `s2Hgt₂`).  Byte-shape of the C130fg field
`FGMNSourceData.initialEquiv`. -/
def S2InitialEquiv (g h : Polynomial O) : Prop :=
  (s2Hgt₂ h2 hq (g - h) > s2Hgt₂ h2 hq g ∧ s2Hgt₂ h2 hq g = s2Hgt₂ h2 hq h)
    ∨ (g = 0 ∧ h = 0)

/-- ★ **`S2MuDvd φ g` — FGMN published Definition 1.2's `φ ∣µ g` at μ₂** (the equivalent
factor criterion: "`h |µ g` if and only if `g ∼µ hf` for some `f`"; U12's `MuDivides`
prototype shape). -/
def S2MuDvd (φ g : Polynomial O) : Prop :=
  ∃ q : Polynomial O, S2InitialEquiv h2 hq g (φ * q)

/-- ★ **`S2MuMinimal φ` — FGMN published Definition 1.2's `µ-minimality` at μ₂**, with the
printed `deg φ > 0` clause kept: `φ ∤µ g` for every nonzero `g` of strictly smaller
degree. -/
def S2MuMinimal (φ : Polynomial O) : Prop :=
  0 < φ.natDegree ∧
    ∀ g : Polynomial O, g ≠ 0 → g.natDegree < φ.natDegree → ¬ S2MuDvd h2 hq φ g

/-- ★ **`S2MuIrreducible φ` — FGMN published Definition 1.2's `µ-irreducibility` at μ₂**
("`Hµ(φ)Gr(µ)` is a non-zero prime ideal"), rendered through `S2MuDvd` as in U12's
prototype: nonzero (`φ ≠ 0` ↔ `Hµ(φ) ≠ 0`), proper (`¬ φ ∣µ 1` ↔ `Hµ(φ)` is not a unit),
and prime on homogeneous elements (`φ ∣µ gh → φ ∣µ g ∨ φ ∣µ h`); see the module docstring
for the fidelity argument. -/
def S2MuIrreducible (φ : Polynomial O) : Prop :=
  φ ≠ 0 ∧ ¬ S2MuDvd h2 hq φ 1 ∧
    ∀ g h : Polynomial O, S2MuDvd h2 hq φ (g * h) → S2MuDvd h2 hq φ g ∨ S2MuDvd h2 hq φ h

/-- ★ **`S2KeyPoly φ` — FGMN published Definition 1.4's key-polynomialhood at μ₂**: "a
monic polynomial which is µ-minimal and µ-irreducible" (membership `φ ∈ KP(µ₂)`).
Byte-shape of the C130fg field `FGMNSourceData.keyPolynomial`. -/
def S2KeyPoly (φ : Polynomial O) : Prop :=
  φ.Monic ∧ S2MuMinimal h2 hq φ ∧ S2MuIrreducible h2 hq φ

/-- shape pin: `S2InitialEquiv` has EXACTLY the abstract `FGMNSourceData.initialEquiv`
field shape (C130fg). -/
example : Polynomial O → Polynomial O → Prop := S2InitialEquiv h2 hq

/-- shape pin: `S2KeyPoly` has EXACTLY the abstract `FGMNSourceData.keyPolynomial` field
shape (C130fg). -/
example : Polynomial O → Prop := S2KeyPoly h2 hq

/-! ## Part 2 — the value-side helper: μ₂ is negation-invariant -/

/-- `s2Hgt₂` is negation-invariant (C130s6's `dvSupp_neg` read through the `toZ` carrier). -/
theorem s2Hgt₂_neg (A : Polynomial O) : s2Hgt₂ h2 hq (-A) = s2Hgt₂ h2 hq A := by
  rw [s2Hgt₂_eq_dvSupp, s2Hgt₂_eq_dvSupp, dvSupp_neg]

/-! ## Part 3 — the equivalence bank (published Def 1.2's `∼µ` IS an equivalence) -/

/-- `∼µ₂` is reflexive: `µ(g − g) = µ(0) = ⊤ > µ(g)` for `g ≠ 0`; the printed zero clause
covers `g = 0`. -/
theorem S2InitialEquiv_refl (g : Polynomial O) : S2InitialEquiv h2 hq g g := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact Or.inr ⟨rfl, rfl⟩
  · refine Or.inl ⟨?_, rfl⟩
    rw [sub_self, s2Hgt₂_zero h2 hq]
    exact lt_top_iff_ne_top.mpr (s2Hgt₂_ne_top h2 hq hg)

/-- `∼µ₂` is symmetric: `h − g = −(g − h)` and `µ₂` is negation-invariant. -/
theorem S2InitialEquiv_symm {g h : Polynomial O} (hgh : S2InitialEquiv h2 hq g h) :
    S2InitialEquiv h2 hq h g := by
  rcases hgh with ⟨hlt, heq⟩ | ⟨hg0, hh0⟩
  · refine Or.inl ⟨?_, heq.symm⟩
    rw [show h - g = -(g - h) from (neg_sub g h).symm, s2Hgt₂_neg h2 hq, ← heq]
    exact hlt
  · exact Or.inr ⟨hh0, hg0⟩

/-- `∼µ₂` is transitive: `g − k = (g − h) + (h − k)` and the ultrametric inequality keeps
the difference strictly above the common value; zero clauses propagate through
`s2Hgt₂_eq_top_iff`. -/
theorem S2InitialEquiv_trans {g h k : Polynomial O} (hgh : S2InitialEquiv h2 hq g h)
    (hhk : S2InitialEquiv h2 hq h k) : S2InitialEquiv h2 hq g k := by
  rcases hgh with ⟨hlt1, heq1⟩ | ⟨hg0, hh0⟩
  · rcases hhk with ⟨hlt2, heq2⟩ | ⟨hh0, hk0⟩
    · refine Or.inl ⟨?_, heq1.trans heq2⟩
      have hdecomp : g - k = (g - h) + (h - k) := by ring
      have hmin := s2Hgt₂_add_ge h2 hq (g - h) (h - k)
      rw [← hdecomp] at hmin
      refine lt_of_lt_of_le (lt_min hlt1 ?_) hmin
      rw [heq1]
      exact hlt2
    · -- `h = 0` forces `µ(g) = ⊤`, hence `g = 0`
      have hg0 : g = 0 := by
        rw [← s2Hgt₂_eq_top_iff h2 hq (A := g), heq1, hh0, s2Hgt₂_zero h2 hq]
      exact Or.inr ⟨hg0, hk0⟩
  · subst hh0
    rcases hhk with ⟨hlt2, -⟩ | ⟨-, hk0⟩
    · rw [s2Hgt₂_zero h2 hq] at hlt2
      exact absurd hlt2 not_top_lt
    · exact Or.inr ⟨hg0, hk0⟩

/-- the packaged equivalence (`Equivalence` in mathlib's sense). -/
theorem S2InitialEquiv_equivalence :
    Equivalence (S2InitialEquiv h2 hq (O := O)) :=
  ⟨S2InitialEquiv_refl h2 hq, S2InitialEquiv_symm h2 hq, S2InitialEquiv_trans h2 hq⟩

/-- `∼µ₂` preserves the value: `S2InitialEquiv g h → µ₂(g) = µ₂(h)` (the printed
`µ(g) = µ(h)` clause; on the zero clause both values are `⊤`). -/
theorem S2InitialEquiv_hgt_eq {g h : Polynomial O} (hgh : S2InitialEquiv h2 hq g h) :
    s2Hgt₂ h2 hq g = s2Hgt₂ h2 hq h := by
  rcases hgh with ⟨-, heq⟩ | ⟨rfl, rfl⟩
  · exact heq
  · rfl

/-- **zero law, left**: `0 ∼µ₂ h ↔ h = 0` (nothing sits strictly above `⊤`, so only the
printed zero clause can fire). -/
theorem S2InitialEquiv_zero_left {h : Polynomial O} :
    S2InitialEquiv h2 hq 0 h ↔ h = 0 := by
  constructor
  · intro hh
    rcases hh with ⟨hlt, -⟩ | ⟨-, hh0⟩
    · rw [s2Hgt₂_zero h2 hq] at hlt
      exact absurd hlt not_top_lt
    · exact hh0
  · rintro rfl
    exact S2InitialEquiv_refl h2 hq 0

/-- **zero law, right**: `g ∼µ₂ 0 ↔ g = 0`. -/
theorem S2InitialEquiv_zero_right {g : Polynomial O} :
    S2InitialEquiv h2 hq g 0 ↔ g = 0 := by
  constructor
  · intro hg
    exact (S2InitialEquiv_zero_left h2 hq).mp (S2InitialEquiv_symm h2 hq hg)
  · rintro rfl
    exact S2InitialEquiv_refl h2 hq 0

/-- `∼µ₂` transports exact grades (RP-0's predicates are `∼µ₂`-invariant). -/
theorem S2ExactGrade_of_initialEquiv {β : ℕ} {g h : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hgh : S2InitialEquiv h2 hq g h) :
    S2ExactGrade h2 hq β h := by
  have hvg : s2Hgt₂ h2 hq g = (β : WithTop ℤ) := hg
  show s2Hgt₂ h2 hq h = (β : WithTop ℤ)
  rw [← S2InitialEquiv_hgt_eq h2 hq hgh]
  exact hvg

/-- `∼µ₂` preserves the extracted grade `s2GradeOf` (RP-8's total grade read), with no
nonzeroness hypothesis. -/
theorem s2GradeOf_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2InitialEquiv h2 hq g h) : s2GradeOf h2 hq g = s2GradeOf h2 hq h := by
  have heq := S2InitialEquiv_hgt_eq h2 hq hgh
  rw [s2Hgt₂_eq_dvSupp, s2Hgt₂_eq_dvSupp] at heq
  unfold s2GradeOf
  rw [toZ_inj heq]

/-! ## Part 4 — ★ the graded-piece characterization

At a COMMON exact grade β, published Def 1.2's `Hµ(g) = Hµ(h)` reads, at the landed
operators, as EQUALITY OF GRADED RESIDUALS: `g ∼µ₂ h ↔ R_β(g) = R_β(h)`.  Forward through
RP-2's strong add law + RP-1's vanishing above the grade; backward through the exact-grade
nonvanishing (RP-5/RP-6) and the negation trick. -/

/-- the graded residual negates (the "sum to zero" trick through RP-2's strong add law —
C130rp11's pattern, extracted). -/
theorem s2GradedRes_neg_of_le {β : ℕ} {g : Polynomial O}
    (hg : (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) g 5 2) :
    s2GradedRes h2 hq β (-g) = - s2GradedRes h2 hq β g := by
  have hneg : (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) (-g) 5 2 := by
    rw [dvSupp_neg]
    exact hg
  have hsum := s2GradedRes_add_of_le h2 hq hg hneg
  rw [add_neg_cancel, s2GradedRes_zero] at hsum
  linear_combination hsum.symm

/-- ★ **the graded-piece characterization** (published Def 1.2's `Hµ(g) = Hµ(h)`, read at
the landed operators): at a common exact grade β, initial-form equivalence IS equality of
grade-β graded residuals — a genuine iff. -/
theorem S2InitialEquiv_iff_gradedRes {β : ℕ} {g h : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hh : S2ExactGrade h2 hq β h) :
    S2InitialEquiv h2 hq g h ↔ s2GradedRes h2 hq β g = s2GradedRes h2 hq β h := by
  have hvg : s2Hgt₂ h2 hq g = (β : WithTop ℤ) := hg
  have hvh : s2Hgt₂ h2 hq h = (β : WithTop ℤ) := hh
  constructor
  · intro hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hg0, -⟩
    · have habove : S2AboveGrade h2 hq β (g - h) := by
        show (β : WithTop ℤ) < s2Hgt₂ h2 hq (g - h)
        rw [← hvg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2GradedRes_add_of_le h2 hq (le_dvSupp_of_exact h2 hq hh)
        (le_dvSupp_of_above h2 hq habove)
      rw [← hdecomp, s2GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      exact hadd
    · exact absurd hg0 (S2ExactGrade_not_zero h2 hq hg)
  · intro hres
    rcases eq_or_ne (g - h) 0 with hgh0 | hgh0
    · rw [sub_eq_zero.mp hgh0]
      exact S2InitialEquiv_refl h2 hq h
    · have hnegh : S2ExactGrade h2 hq β (-h) := by
        rw [S2ExactGrade_iff_dvSupp, dvSupp_neg]
        exact (S2ExactGrade_iff_dvSupp h2 hq).mp hh
      have hvneg : s2Hgt₂ h2 hq (-h) = (β : WithTop ℤ) := hnegh
      have hge : (β : WithTop ℤ) ≤ s2Hgt₂ h2 hq (g - h) := by
        have hmin := s2Hgt₂_add_ge h2 hq g (-h)
        rw [← sub_eq_add_neg, hvg, hvneg, min_self] at hmin
        exact hmin
      rcases hge.lt_or_eq with hlt | heqv
      · refine Or.inl ⟨?_, hvg.trans hvh.symm⟩
        rw [hvg]
        exact hlt
      · -- the difference would sit at EXACT grade β, with a NONZERO residual — but the
        -- residuals cancel, contradiction
        have hexact : S2ExactGrade h2 hq β (g - h) := heqv.symm
        have hne := s2GradedRes_ne_zero_of_exact h2 hq hexact
        have hadd := s2GradedRes_add_of_le h2 hq (le_dvSupp_of_exact h2 hq hg)
          (le_dvSupp_of_exact h2 hq hnegh)
        rw [← sub_eq_add_neg, s2GradedRes_neg_of_le h2 hq (le_dvSupp_of_exact h2 hq hh),
          hres, add_neg_cancel] at hadd
        exact absurd hadd hne

/-! ## Part 5 — the `s2NormRes` tie (the KP-7 genre's forward direction) -/

/-- ★ **the normalized-residual tie**: `g ∼µ₂ h → R₃(g) = R₃(h)` — the forward direction of
the KP-7 genre (published Prop 5.6's easy half at the landed operators, with NO
key-polynomial hypothesis needed).  The converse for key polynomials is KP-8/KP-9's core,
not claimed here. -/
theorem s2NormRes_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2InitialEquiv h2 hq g h) : s2NormRes h2 hq g = s2NormRes h2 hq h := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [(S2InitialEquiv_zero_left h2 hq).mp hgh]
  · have hg := S2ExactGrade_s2GradeOf h2 hq hg0
    have hh := S2ExactGrade_of_initialEquiv h2 hq hg hgh
    have hres := (S2InitialEquiv_iff_gradedRes h2 hq hg hh).mp hgh
    rw [s2NormRes_of_exact h2 hq hg, s2NormRes_of_exact h2 hq hh, hres]

/-! ## Part 6 — `S2MuDvd` basics -/

/-- ordinary divisibility implies μ₂-divisibility (`g = φq` is `∼µ₂`-equivalent to itself). -/
theorem S2MuDvd_of_dvd {φ g : Polynomial O} (hdvd : φ ∣ g) : S2MuDvd h2 hq φ g := by
  obtain ⟨q, rfl⟩ := hdvd
  exact ⟨q, S2InitialEquiv_refl h2 hq _⟩

/-- `φ ∣µ₂ φ`. -/
theorem S2MuDvd_self (φ : Polynomial O) : S2MuDvd h2 hq φ φ :=
  S2MuDvd_of_dvd h2 hq dvd_rfl

/-- everything μ₂-divides `0` (`Hµ(0) = 0` is in every ideal; take `q = 0` and the printed
zero clause). -/
theorem S2MuDvd_zero (φ : Polynomial O) : S2MuDvd h2 hq φ 0 :=
  S2MuDvd_of_dvd h2 hq (dvd_zero φ)

/-- μ₂-divisibility is `∼µ₂`-invariant in the dividend (initial forms only see the class). -/
theorem S2MuDvd_congr_right {φ g g' : Polynomial O}
    (hgg' : S2InitialEquiv h2 hq g g') :
    S2MuDvd h2 hq φ g ↔ S2MuDvd h2 hq φ g' := by
  constructor
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2InitialEquiv_trans h2 hq (S2InitialEquiv_symm h2 hq hgg') hq'⟩
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2InitialEquiv_trans h2 hq hgg' hq'⟩

/-! ## Part 7 — teeth: `Φ′`'s status under the new predicates

The shared engine: at an EVEN grade, nothing with a nonzero residual scalar is μ₂-divisible
by `Φ′` — any candidate factorization `Φ′·q` has odd cofactor grade (`5` is odd), so RP-4's
twisted product law contributes the carry `y¹`, killing the scalar.  Feeding it: short
digits (`deg < 2`) always sit at EVEN grade (the same parity computation as C130rp11's
recorded vacuity finding), which yields `Φ′`'s μ₂-MINIMALITY outright; and RP-12's landed
degree-four lift `Φ′² + 4x` (grade `10`, residual `X + 1`) is NOT μ₂-divisible by `Φ′`. -/

/-- private copy of the S2 key-degree numeral: `deg Φ′ = 2` (the private-copy pattern). -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- **short digits sit at EVEN grade**: a polynomial of degree `< 2 = deg Φ′` has cleared
grade `2·dvHgt(g, 0)` — its development stops at slot `0`, so the grade is twice a slot
height.  (The general-β form of C130rp11's `s2_recipe_naive_numeral_vacuous` parity
computation.) -/
theorem S2ExactGrade_even_of_natDegree_lt_two {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hdeg : g.natDegree < 2) : 2 ∣ β := by
  have hdv : dvSupp (s2Frame h2 hq) g 5 2 = (β : ℕ∞) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mp hg
  have hrange := dvSupp_eq_inf_range (s2Frame h2 hq) (u := 5) (ℓ := 2) (by norm_num) g
    (M := 2) hdeg
  rw [hrange, show Finset.range 2 = {0, 1} from rfl, Finset.inf_insert, Finset.inf_singleton]
    at hdv
  have hdev1 : dev (s2Frame h2 hq).key g 1 = 0 :=
    dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos g 1
      (by rw [key_natDegree_two h2 hq]; omega)
  have hhgt1 : dvHgt (s2Frame h2 hq) g 1 = ⊤ := by
    rw [dvHgt, hdev1]
    exact (s2Frame h2 hq).stageHeight_zero
  rw [hhgt1, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add,
    min_eq_left (le_top), Nat.cast_zero, mul_zero, add_zero] at hdv
  have hfin : dvHgt (s2Frame h2 hq) g 0 ≠ ⊤ := by
    intro htop
    rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2)] at hdv
    exact WithTop.top_ne_coe hdv
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hm, nsmul_eq_mul] at hdv
  have h2m : (2 * m : ℕ) = β := by exact_mod_cast hdv
  exact ⟨m, h2m.symm⟩

/-- ★ **the odd-carry engine**: at an EVEN exact grade, an input with NONZERO residual
scalar is NOT μ₂-divisible by `Φ′`.  Any candidate `Φ′·q` has `µ₂(q) = β − 5` ODD, so
RP-4's twisted product law reads `R_β(Φ′·q) = y^{1·1}·(R₅(Φ′)·R(q)) = y·R(q)` — scalar `0`,
while the graded-piece characterization forces the scalars to agree. -/
theorem not_S2MuDvd_key_of_even_grade {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (heven : 2 ∣ β)
    (hc : (s2GradedRes h2 hq β g).coeff 0 ≠ 0) :
    ¬ S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) g := by
  rintro ⟨q, hq'⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero] at hq'
    exact S2ExactGrade_not_zero h2 hq hg ((S2InitialEquiv_zero_right h2 hq).mp hq')
  · obtain ⟨β', hβ'⟩ := S2ExactGrade_exists h2 hq hq0
    have hkq : S2ExactGrade h2 hq (5 + β') (((s2Frame h2 hq).key : Polynomial O) * q) :=
      S2ExactGrade_mul h2 hq (tooth_key h2 hq) hβ'
    have hgkq : S2ExactGrade h2 hq β (((s2Frame h2 hq).key : Polynomial O) * q) :=
      S2ExactGrade_of_initialEquiv h2 hq hg hq'
    have hβeq : β = 5 + β' := S2ExactGrade_unique h2 hq hgkq hkq
    subst hβeq
    have hres := (S2InitialEquiv_iff_gradedRes h2 hq hg hgkq).mp hq'
    have hmul := s2GradedRes_mul_of_exact h2 hq (tooth_key h2 hq) hβ'
    rw [tooth_gradedRes_key h2 hq, one_mul,
      show 5 % 2 * (β' % 2) = 1 from by omega, pow_one] at hmul
    rw [hmul] at hres
    apply hc
    rw [hres, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]

/-- ★ **`Φ′` IS μ₂-minimal** (published Definition 1.2's µ-minimality at μ₂, machine-proved
— the minimality clause of published Prop 1.7(4)'s `φ₂ ∈ KP(µ₂)` for the carried key at
`r = 1`): every nonzero `g` of degree `< 2` sits at even grade with nonzero residual scalar
(RP-7's worker at `deg < 2 < 4`), so the odd-carry engine forbids `Φ′ ∣µ₂ g`. -/
theorem s2MuMinimal_key : S2MuMinimal h2 hq ((s2Frame h2 hq).key : Polynomial O) := by
  refine ⟨by rw [key_natDegree_two h2 hq]; omega, fun g hg0 hdeg hdvd => ?_⟩
  rw [key_natDegree_two h2 hq] at hdeg
  obtain ⟨β, hβ⟩ := S2ExactGrade_exists h2 hq hg0
  exact not_S2MuDvd_key_of_even_grade h2 hq hβ
    (S2ExactGrade_even_of_natDegree_lt_two h2 hq hβ hdeg)
    (s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hβ (by omega)) hdvd

/-- `Φ′`'s μ₂-minimality, spelled at the explicit polynomial `x² − 2` (C97's `s2Key`). -/
theorem s2MuMinimal_X_sq_sub_two :
    S2MuMinimal h2 hq (Polynomial.X ^ 2 - Polynomial.C (2 : O)) := by
  have h := s2MuMinimal_key h2 hq
  rwa [key_eq h2 hq,
    show s2Key O = Polynomial.X ^ 2 - Polynomial.C (2 : O) from rfl] at h

/-- `Φ′ ∤µ₂ 1` — the properness clause of μ₂-irreducibility holds for `Φ′` (a corollary of
minimality at the nonzero degree-0 input `1`). -/
theorem not_S2MuDvd_key_one :
    ¬ S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) 1 :=
  (s2MuMinimal_key h2 hq).2 1 one_ne_zero
    (by rw [Polynomial.natDegree_one, key_natDegree_two h2 hq]; omega)

/-- **`Φ′`'s remaining status gap, named**: key-polynomialhood of `Φ′` (published Prop
1.7(4)) reduces to the PRIMALITY conjunct of μ₂-irreducibility — monicity is the frame's,
minimality is proved above.  Discharging `S2MuIrreducible Φ′` is KP-2's CORE row (published
Lemma 5.2/Theorem 5.7 substance), deliberately NOT claimed here. -/
theorem s2KeyPoly_key_of_muIrreducible
    (hirr : S2MuIrreducible h2 hq ((s2Frame h2 hq).key : Polynomial O)) :
    S2KeyPoly h2 hq ((s2Frame h2 hq).key : Polynomial O) :=
  ⟨(s2Frame h2 hq).hmonic, s2MuMinimal_key h2 hq, hirr⟩

/-! ## Part 8 — teeth: `Φ′²` vs the degree-four lift, at the landed values

`Φ′² + 4x` is RP-12's landed degree-four witness (grade `10`, `R₁₀ = X + 1`,
`R₃ = X + 1`) — the composed-key GENRE at the landed values (the literal
`keyAt 2 = composedKey` instance is KP-6's row; its grade/residual teeth are not landed). -/

/-- **tooth**: `Φ′ ∣µ₂ Φ′²` — plain divisibility already witnesses μ₂-divisibility. -/
theorem S2MuDvd_key_key_sq :
    S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) :=
  S2MuDvd_of_dvd h2 hq (dvd_mul_right _ _)

/-- ★ **tooth (the proper-augmentation/MacLane genre)**: the degree-four lift is NOT
initial-equivalent to `Φ′²`, despite the exact grade TIE at `10` — their graded residuals
differ (`R₁₀(Φ′²) = X` vs `R₁₀(Φ′² + 4x) = X + 1`), so the graded-piece characterization
refutes the equivalence.  The lift genuinely deepens the chain. -/
theorem tooth_not_initialEquiv_key_sq_lift :
    ¬ S2InitialEquiv h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X) := by
  intro hEq
  have hres := (S2InitialEquiv_iff_gradedRes h2 hq (tooth_key_sq h2 hq)
    (tooth_sum_exact h2 hq)).mp hEq
  rw [tooth_gradedRes_key_sq h2 hq, tooth_gradedRes_add_exact h2 hq] at hres
  have h10 : (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = 0 := by linear_combination -hres
  exact one_ne_zero h10

/-- ★ **tooth (the engine fires at the lift)**: `Φ′ ∤µ₂ Φ′² + 4x` — the lift's grade `10`
is even and its residual scalar is `(X + 1)(0) = 1 ≠ 0`, so no `Φ′·q` can match its initial
form.  (Consistent with the lift's role as a NEW key candidate: a µ-minimal degree-four
polynomial not divisible by the old key.) -/
theorem tooth_not_S2MuDvd_key_lift :
    ¬ S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X) := by
  refine not_S2MuDvd_key_of_even_grade h2 hq (tooth_sum_exact h2 hq) (by norm_num) ?_
  rw [tooth_gradedRes_add_exact h2 hq, Polynomial.coeff_add, Polynomial.coeff_X_zero,
    Polynomial.coeff_one_zero, zero_add]
  exact one_ne_zero

/-- **tooth (the equivalence fires positively)**: perturbing `Φ′²` at STRICTLY higher grade
(`4x·Φ′` has grade `15 > 10`) does NOT change the initial form: `Φ′² ∼µ₂ Φ′² + 4x·Φ′` — the
value criterion holds through the off-tie addition law. -/
theorem tooth_initialEquiv_key_sq_perturb :
    S2InitialEquiv h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) := by
  have h15 : S2ExactGrade h2 hq 15
      (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) :=
    S2ExactGrade_mul h2 hq (tooth_C4X_grade h2 hq) (tooth_key h2 hq)
  have hv15 : s2Hgt₂ h2 hq (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key)
      = ((15 : ℕ) : WithTop ℤ) := h15
  have hv10 : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      = ((10 : ℕ) : WithTop ℤ) := tooth_key_sq h2 hq
  have hlt : ((10 : ℕ) : WithTop ℤ) < ((15 : ℕ) : WithTop ℤ) := by
    exact_mod_cast (by norm_num : (10 : ℕ) < 15)
  refine Or.inl ⟨?_, ?_⟩
  · rw [show (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
        - (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key)
        = -(Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) from by ring,
      s2Hgt₂_neg h2 hq, hv15, hv10]
    exact hlt
  · have hne : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
        ≠ s2Hgt₂ h2 hq (Polynomial.C (4 : O) * Polynomial.X * (s2Frame h2 hq).key) := by
      rw [hv10, hv15]
      exact hlt.ne
    rw [s2Hgt₂_add_eq h2 hq _ _ hne, hv10, hv15]
    exact (min_eq_left hlt.le).symm

end S2

end Uniformity.Density.Tower.C130kp0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv
#print axioms Uniformity.Density.Tower.C130kp0.S2MuDvd
#print axioms Uniformity.Density.Tower.C130kp0.S2MuMinimal
#print axioms Uniformity.Density.Tower.C130kp0.S2MuIrreducible
#print axioms Uniformity.Density.Tower.C130kp0.S2KeyPoly
#print axioms Uniformity.Density.Tower.C130kp0.s2Hgt₂_neg
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_refl
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_symm
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_trans
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_equivalence
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_hgt_eq
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_zero_left
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_zero_right
#print axioms Uniformity.Density.Tower.C130kp0.S2ExactGrade_of_initialEquiv
#print axioms Uniformity.Density.Tower.C130kp0.s2GradeOf_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C130kp0.s2GradedRes_neg_of_le
#print axioms Uniformity.Density.Tower.C130kp0.S2InitialEquiv_iff_gradedRes
#print axioms Uniformity.Density.Tower.C130kp0.s2NormRes_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C130kp0.S2MuDvd_of_dvd
#print axioms Uniformity.Density.Tower.C130kp0.S2MuDvd_self
#print axioms Uniformity.Density.Tower.C130kp0.S2MuDvd_zero
#print axioms Uniformity.Density.Tower.C130kp0.S2MuDvd_congr_right
#print axioms Uniformity.Density.Tower.C130kp0.S2ExactGrade_even_of_natDegree_lt_two
#print axioms Uniformity.Density.Tower.C130kp0.not_S2MuDvd_key_of_even_grade
#print axioms Uniformity.Density.Tower.C130kp0.s2MuMinimal_key
#print axioms Uniformity.Density.Tower.C130kp0.s2MuMinimal_X_sq_sub_two
#print axioms Uniformity.Density.Tower.C130kp0.not_S2MuDvd_key_one
#print axioms Uniformity.Density.Tower.C130kp0.s2KeyPoly_key_of_muIrreducible
#print axioms Uniformity.Density.Tower.C130kp0.S2MuDvd_key_key_sq
#print axioms Uniformity.Density.Tower.C130kp0.tooth_not_initialEquiv_key_sq_lift
#print axioms Uniformity.Density.Tower.C130kp0.tooth_not_S2MuDvd_key_lift
#print axioms Uniformity.Density.Tower.C130kp0.tooth_initialEquiv_key_sq_perturb

end AxCheck
