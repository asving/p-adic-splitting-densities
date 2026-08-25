/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp0
import Uniformity.ChapC.C35b

/-!
# Uniformity.ChapC.C130rp1 — S2-source plan node RP-1

**S2-source plan node RP-1** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 row RP-1:
"graded residual definition", dependencies RP-0, `dev`, `twistRead`, terminal receiver): the
TOTAL S2 graded residual `s2GradedRes : ℕ → Polynomial O → Polynomial ((s2DepthTwo h2 hq).fld 2)`
— the CONCRETE depth-two instance of `C130fg.lean`'s abstract field shape
`FGMNSourceData.gradedResidual : ℕ → Polynomial O → Polynomial (W.fld r)` at `r = 2` — with the
finite-support pins, the proof-independence pins, the zero law at above-grade inputs (the RP-2
shape, landed here because it falls out), and computation teeth at the landed table values.

## The FGMN dictionary (published Def 3.12/3.13, at the S2 numerals)

Published Definition 3.13 defines the graded residual `R_β(g) ∈ F[y]` from the key
development of `g`: the `j`-th `y`-coefficient is the (previous-level) residual read of the
development coefficient sitting at the `j`-th abscissa of the grade-`β` line, and coefficients
off the line contribute `0`.  At S2 (the `(e', f', u') = (2, 1, 5)` augmentation whose cleared
value is the LANDED `s2Hgt₂ = toZ (dvSupp (s2Frame …) · 5 2)`, RP-0's `nextValue` read) this is
concrete:

* the development is the `Φ′`-development `dev (s2Frame h2 hq).key g` — the SAME development
  `s2Hgt₂`/`dvSupp · 5 2` minimizes over, so the operator is graded by the SAME value whose
  level sets are RP-0's `S2ExactGrade`/`S2AboveGrade` (the design constraint RP-2..RP-6 need);
* the grade-`β` line is `2·dv(A_s) + 5·s = β` (`dvSupp`'s own term shape at `(u, ℓ) = (5, 2)`)
  — the predicate `S2SlotOnGrade` below;
* published Def 3.12's line parameterization: the abscissae on the `β`-line are
  `s_t = s₂(β) + t·e₂` with `s₂(β)` the unique `0 ≤ s < e₂ = 2` solving `2u + 5s = β`, i.e.
  `s₂(β) = β % 2`; the `t`-th abscissa carries the `y^t` monomial, so a slot at abscissa `s`
  lands at `y`-power `⌊s/2⌋` (published eq (11)'s `R(φ^s) = y^{⌊s/e⌋}`, checked by the teeth);
* the on-line height at abscissa `s` is `(β − 5s)/2` (the line equation solved for `dv`), and
  the coefficient read is the C.22 ϖ-read `twistRead` at that height — EXACTLY the read C.25's
  `dvResPoly` uses for its side coefficients (`twistRead (M₀ − tu) (dev F.key f (j₁ + tℓ))`).
  The identification of this ϖ-read with published Def 3.13's twisted evaluation
  `ε(α_j)·R_{α_j}(a_{s_j})(z)` is the standing `EFF.HE6.58`/C.22/C.25 dictionary (a recorded
  definition-side trust boundary there), inherited here, not re-derived.

## Totality, and where the junk lives

`s2GradedRes β g` is total in both arguments (junk-total outside exact grades per corpus
convention): each candidate coefficient is gated by the DECIDED line membership
`S2SlotOnGrade β g s`, off-line slots contribute a literal `0`, and the `ℕ`-truncated height
`(β − 5s)/2` is pinned to the TRUE height by the gate (`s2GradedCoeff_eq_twistRead`).  On
`P_β⁺` (RP-0's `S2AboveGrade`) every gate is false and the operator vanishes — published
Lemma 3.14, landed as `s2GradedRes_zero_of_above`.  For `β` BELOW the exact grade the operator
may read honest on-line slots; FGMN's `R_β` is only specified on `P_β`, so those values are
junk by convention and no law reads them.

## The pins

* **finite support** (from natDegree bounds of the development): past the development length
  the gate is false (`s2GradedCoeff_eq_zero_of_natDegree_lt`, via C118a's `dvHgt_top_of_gt`),
  and past grade `β` the line is exhausted (`s2GradedCoeff_eq_zero_of_grade_lt`); hence
  `s2GradedRes_natDegree_le : natDegree ≤ β`.
* **the master coefficient law** `s2GradedRes_coeff`: `(s2GradedRes β g).coeff t =
  s2GradedCoeff β g t` for ALL `t` — the polynomial is determined by the total coefficient
  function, so no choice made in assembling it is visible.
* **range independence** `s2GradedRes_eq_sum_range`: the assembling sum may be read over any
  range `M ≥ β + 1`.
* **true-height pin** `s2GradedCoeff_eq_twistRead`: whatever the `ℕ`-truncated arithmetic
  `(β − 5s)/2` does off the gate, ON the gate the read height is the coefficient's actual
  `dvHgt` — the `dv2Res_pinned` genre (C78adj), for the one arithmetic choice this definition
  makes.
* **pin independence** `s2GradedCoeff_pin_irrel`: the frame-pin proof is irrelevant (`rfl`,
  by definitional proof irrelevance), and `H₀ = 1` is not a choice — C.97's
  `s2Frame_pin_unique` forces it.
* **slot completeness** `s2GradedCoeff_slot` + `s2SlotOnGrade_parity`: every on-line slot `s`
  satisfies `s ≡ β (mod 2)` and IS read, at `y`-power `s / 2` — the `β % 2 + 2t` encoding
  drops nothing.

## Teeth (published eq (11) instances at the landed RP-0 grades)

`R_5(Φ′) = 1` (`= y^{⌊1/2⌋}`), `R_7(x·Φ′) = 1` (through C35b's landed ϖ-read value
`twistRead 1 x = 1`), `R_10(Φ′²) = X` (`= y^{⌊2/2⌋}` — the `y`-power is live, the operator is
genuinely polynomial-valued per U9 Q2), `R_3(Φ′) = 0` (the zero law at an above-grade input,
`3 < 5`), and `R_7(x·Φ′) ≠ 0` (the operator is not the zero operator).  Grades 5, 7 = 2+5,
10 = 5+5 are exactly RP-0's landed exact-grade teeth.

## What this node does NOT claim (honesty scope)

* No additivity or multiplicativity: `graded_add` (published Cor 4.12(1)) is RP-2's;
  the product chain (published Cor 4.12(2)) is RP-3–RP-6's CORE work.
* No exact-grade nonvanishing (`graded_scalar_nonzero`, published Thm 4.1/Cor 4.9(1)): RP-7.
* No normalization (published Def 3.15's initial-`y`-power strip, `normalizedResidual`): RP-8,
  where the tie to C.25's side-anchored `dvResPoly` belongs.
* No `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` instance: FD-0.
* The ϖ-read ↔ `ε·R(z)` evaluation dictionary is consumed from C.22/C.25's recorded
  faithfulness boundary, not proved.

**DEPENDS.** C130rp0 (RP-0: `S2ExactGrade`/`S2AboveGrade` + `dvSupp` normal forms;
transitively C130nv5/nv3/nv, C130s6's `dvSupp` law bank + `s2Hgt₂` teeth, C130s2's
`s2DepthTwo`) · C35b (`e1_eq`/`f1_eq`/`h_eq`/`key_eq`/`s2Key_deg`, `sh_C`/`sh_X`/`sh_zero`,
`slotIdx_one`, `twistRead_one_X`) · C.22 (`twistRead`) · C.21/C.17/C.15 (`slotRes`,
`slotWindow`, `slotIdx`, `twistExp`) · B.22 (`digAt_zero`) · B.02/B35a (`dev`,
`dev_mul_pow`, `dev_mul_pow_of_lt`) · C118a (`dvHgt_top_of_gt`, `smul_top_pos`) · C.06
(`dvHgt`, `dvSupp`) · C.97 (`s2Frame`, `s2Frame_pin`, `s2Frame_pin_unique`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the grade-line gate `S2SlotOnGrade`

The `s`-th `Φ′`-development slot of `g` sits EXACTLY on the grade-`β` line: the equation is
`dvSupp`'s own term shape at the S2 side `(u, ℓ) = (5, 2)` (C.06), so line membership is
literally "this slot's term attains the value `β`". -/

/-- **the grade-line gate**: `2·dv(A_s) + 5·s = β` — slot `s` of the `Φ′`-development of `g`
sits exactly on the grade-`β` line (published Def 3.13's `Q_s ∈ L_β` membership, in the
repo's cleared `ℕ∞` reads). -/
def S2SlotOnGrade (β : ℕ) (g : Polynomial O) (s : ℕ) : Prop :=
  2 • dvHgt (s2Frame h2 hq) g s + ((5 * s : ℕ) : ℕ∞) = (β : ℕ∞)

/-- **the gate normal form**: line membership is a finite height plus a NATURAL line
equation `2m + 5s = β` — no `ℕ∞` arithmetic survives.  (RP-2..RP-6's consumable shape.) -/
theorem s2SlotOnGrade_iff {β s : ℕ} {g : Polynomial O} :
    S2SlotOnGrade h2 hq β g s ↔
      ∃ m : ℕ, dvHgt (s2Frame h2 hq) g s = (m : ℕ∞) ∧ 2 * m + 5 * s = β := by
  unfold S2SlotOnGrade
  constructor
  · intro h
    have hne : dvHgt (s2Frame h2 hq) g s ≠ ⊤ := by
      intro htop
      rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add] at h
      exact WithTop.top_ne_coe h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    refine ⟨m, hm.symm, ?_⟩
    rw [← hm, nsmul_eq_mul] at h
    exact_mod_cast h
  · rintro ⟨m, hm, hβ⟩
    rw [hm, nsmul_eq_mul, ← hβ]
    push_cast
    ring

/-- **parity of on-line slots** (published Def 3.12's `s₂(β) = β % 2` at `(e₂, h₂) = (2, 5)`):
every slot on the grade-`β` line has the grade's parity.  With `s2GradedCoeff_slot` below this
pins that the `β % 2 + 2t` abscissa encoding drops no on-line slot. -/
theorem s2SlotOnGrade_parity {β s : ℕ} {g : Polynomial O}
    (h : S2SlotOnGrade h2 hq β g s) : s % 2 = β % 2 := by
  obtain ⟨m, -, hβ⟩ := (s2SlotOnGrade_iff h2 hq).mp h
  omega

/-- an on-line slot bounds the cleared support: `dvSupp` is the inf of the very terms the
gate equates to `β`.  (The bridge from the gate to RP-0's `S2AboveGrade` normal form.) -/
theorem dvSupp_le_of_slotOnGrade {β s : ℕ} {g : Polynomial O}
    (h : S2SlotOnGrade h2 hq β g s) :
    dvSupp (s2Frame h2 hq) g 5 2 ≤ (β : ℕ∞) := by
  obtain ⟨m, hm, hβ⟩ := (s2SlotOnGrade_iff h2 hq).mp h
  have hs : s ≤ g.natDegree := by
    by_contra hs
    rw [C118a.dvHgt_top_of_gt (s2Frame h2 hq) g (not_le.mp hs)] at hm
    exact WithTop.top_ne_coe hm
  have hle : dvSupp (s2Frame h2 hq) g 5 2
      ≤ 2 • dvHgt (s2Frame h2 hq) g s + ((5 : ℕ∞) * (s : ℕ∞)) := by
    rw [dvSupp]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  have heq : 2 • dvHgt (s2Frame h2 hq) g s + ((5 : ℕ∞) * (s : ℕ∞)) = (β : ℕ∞) := by
    rw [hm, nsmul_eq_mul, ← hβ]
    push_cast
    ring
  rw [heq] at hle
  exact hle

/-! ## Part 2 — the graded coefficient read, and its pins

The `t`-th `y`-coefficient reads the slot at abscissa `β % 2 + 2t` (Def 3.12's line
parameterization): the C.22 ϖ-read at the on-line height `(β − 5s)/2`, gated by line
membership, junk-`0` off the line. -/

open Classical in
/-- **the `t`-th graded coefficient**: the ϖ-read (`twistRead`, C.22 — the same read C.25's
`dvResPoly` coefficients use) of the `Φ′`-development slot at the `t`-th abscissa
`β % 2 + 2t` of the grade-`β` line, at the on-line height `(β − 5s)/2`, if the slot is on
the line; `0` otherwise.  Total; the truncated arithmetic is pinned by
`s2GradedCoeff_eq_twistRead`. -/
noncomputable def s2GradedCoeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2DepthTwo h2 hq).fld 2 :=
  if S2SlotOnGrade h2 hq β g (β % 2 + 2 * t) then
    ((s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq)
      ((β - 5 * (β % 2 + 2 * t)) / 2) (dev (s2Frame h2 hq).key g (β % 2 + 2 * t)))
  else 0

open Classical in
/-- **pin independence** (proof-independence pin 1): the frame-pin proof is a choice
artifact only definitionally — reading through ANY pin proof gives the same coefficient,
by definitional proof irrelevance (`rfl`).  The numeral `H₀ = 1` is not a choice either:
C.97's `s2Frame_pin_unique` forces every pin of `s2Frame` to `1`. -/
theorem s2GradedCoeff_pin_irrel (hpin' : (s2Frame h2 hq).Pin 1) (β : ℕ) (g : Polynomial O)
    (t : ℕ) :
    s2GradedCoeff h2 hq β g t =
      if S2SlotOnGrade h2 hq β g (β % 2 + 2 * t) then
        ((s2Frame h2 hq).twistRead 1 hpin'
          ((β - 5 * (β % 2 + 2 * t)) / 2) (dev (s2Frame h2 hq).key g (β % 2 + 2 * t)))
      else 0 := rfl

/-- **the true-height pin** (proof-independence pin 2, the `dv2Res_pinned` genre): on the
gate, the `ℕ`-truncated height `(β − 5s)/2` IS the slot's actual height — the coefficient
may be read at any caller-supplied height pin. -/
theorem s2GradedCoeff_eq_twistRead {β t m : ℕ} {g : Polynomial O}
    (hgate : S2SlotOnGrade h2 hq β g (β % 2 + 2 * t))
    (hm : dvHgt (s2Frame h2 hq) g (β % 2 + 2 * t) = (m : ℕ∞)) :
    s2GradedCoeff h2 hq β g t =
      (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m
        (dev (s2Frame h2 hq).key g (β % 2 + 2 * t)) := by
  obtain ⟨m', hm', hβ⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  have hmm : m = m' := by
    rw [hm] at hm'
    exact_mod_cast hm'
  subst hmm
  have hk : (β - 5 * (β % 2 + 2 * t)) / 2 = m := by omega
  unfold s2GradedCoeff
  rw [if_pos hgate, hk]

/-- **slot completeness** (proof-independence pin 3): every on-line slot `s` IS read, at
`y`-power `s / 2` (published eq (11)'s `⌊s/e₂⌋`), with the on-line height — the abscissa
encoding `β % 2 + 2t` is exhaustive on the line. -/
theorem s2GradedCoeff_slot {β s : ℕ} {g : Polynomial O}
    (h : S2SlotOnGrade h2 hq β g s) :
    s2GradedCoeff h2 hq β g (s / 2) =
      (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) ((β - 5 * s) / 2)
        (dev (s2Frame h2 hq).key g s) := by
  have hpar := s2SlotOnGrade_parity h2 hq h
  have hs : β % 2 + 2 * (s / 2) = s := by omega
  unfold s2GradedCoeff
  rw [hs, if_pos h]

/-- vanishing off finite heights: a `⊤`-height slot (in particular any slot past the
development) is never on a line, so its coefficient is `0`. -/
theorem s2GradedCoeff_eq_zero_of_dvHgt_top {β t : ℕ} {g : Polynomial O}
    (h : dvHgt (s2Frame h2 hq) g (β % 2 + 2 * t) = ⊤) :
    s2GradedCoeff h2 hq β g t = 0 := by
  unfold s2GradedCoeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, hm, -⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  rw [h] at hm
  exact WithTop.top_ne_coe hm

/-- **finite support, the natDegree bound** (the development is finite): coefficients whose
abscissa passes `natDegree g` vanish — C118a's `dvHgt_top_of_gt` makes the slot height `⊤`. -/
theorem s2GradedCoeff_eq_zero_of_natDegree_lt {β t : ℕ} {g : Polynomial O}
    (h : g.natDegree < β % 2 + 2 * t) :
    s2GradedCoeff h2 hq β g t = 0 :=
  s2GradedCoeff_eq_zero_of_dvHgt_top h2 hq (C118a.dvHgt_top_of_gt (s2Frame h2 hq) g h)

/-- **finite support, the grade bound**: the grade-`β` line meets only abscissae with
`5s ≤ β`, so coefficients past `t = β` (indeed past `β/10`) vanish. -/
theorem s2GradedCoeff_eq_zero_of_grade_lt {β t : ℕ} {g : Polynomial O}
    (h : β < 5 * (β % 2 + 2 * t)) :
    s2GradedCoeff h2 hq β g t = 0 := by
  unfold s2GradedCoeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, -, hβ⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  omega

/-! ## Part 3 — ★ the TOTAL S2 graded residual `s2GradedRes`

The C130fg shape `ℕ → Polynomial O → Polynomial (W.fld r)` at the S2 occurrence `r = 2`
(`(s2DepthTwo h2 hq).fld 2` is definitionally the frame stage field `K₁`, C.97's constant
residue tower, so the ϖ-read coefficients land in it on the nose). -/

/-- ★ **NODE RP-1 — the total S2 graded residual** `R_β(g) ∈ K₂[y]` (published Def 3.13 at
the S2 numerals): the polynomial whose `t`-th coefficient is the gated ϖ-read of the
`t`-th grade-line slot.  Junk-total outside exact grades; determined by its total
coefficient function via `s2GradedRes_coeff`. -/
noncomputable def s2GradedRes (β : ℕ) (g : Polynomial O) :
    Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  ∑ t ∈ Finset.range (β + 1), Polynomial.C (s2GradedCoeff h2 hq β g t) * Polynomial.X ^ t

/-- shape pin: the operator has EXACTLY the abstract `FGMNSourceData.gradedResidual` field
shape at `r = 2` (C130fg, U9 Q2's polynomial-valued ruling). -/
noncomputable example : ℕ → Polynomial O → Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  s2GradedRes h2 hq

/-- ★ **the master coefficient law** (proof-independence + finite-support pin): for EVERY
`t`, the `t`-th coefficient of `s2GradedRes β g` is `s2GradedCoeff β g t` — the polynomial
is determined by the total coefficient function, so no assembly choice is visible. -/
theorem s2GradedRes_coeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2GradedRes h2 hq β g).coeff t = s2GradedCoeff h2 hq β g t := by
  unfold s2GradedRes
  rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  split_ifs with ht
  · rfl
  · exact (s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega)).symm

/-- **range independence** (proof-independence pin for the assembling sum): the sum may be
read over any range `M ≥ β + 1`. -/
theorem s2GradedRes_eq_sum_range (β : ℕ) (g : Polynomial O) {M : ℕ} (hM : β + 1 ≤ M) :
    s2GradedRes h2 hq β g
      = ∑ t ∈ Finset.range M, Polynomial.C (s2GradedCoeff h2 hq β g t) * Polynomial.X ^ t := by
  unfold s2GradedRes
  refine Finset.sum_subset (fun x hx => ?_) fun t _ hts => ?_
  · rw [Finset.mem_range] at hx ⊢
    omega
  · rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq
      (by rw [Finset.mem_range, not_lt] at hts; omega), Polynomial.C_0, zero_mul]

/-- **finite support, packaged**: `natDegree (s2GradedRes β g) ≤ β`. -/
theorem s2GradedRes_natDegree_le (β : ℕ) (g : Polynomial O) :
    (s2GradedRes h2 hq β g).natDegree ≤ β := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [s2GradedRes_coeff]
  exact s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega)

/-- **finite support, the natDegree form on the polynomial**: coefficients whose abscissa
passes the development length vanish. -/
theorem s2GradedRes_coeff_eq_zero_of_natDegree_lt {β t : ℕ} (g : Polynomial O)
    (h : g.natDegree < β % 2 + 2 * t) :
    (s2GradedRes h2 hq β g).coeff t = 0 := by
  rw [s2GradedRes_coeff]
  exact s2GradedCoeff_eq_zero_of_natDegree_lt h2 hq h

/-! ## Part 4 — the zero law at above-grade inputs (published Lemma 3.14; the RP-2 shape)

On `P_β⁺` — RP-0's `S2AboveGrade`, `β < s2Hgt₂ g` — every slot term strictly exceeds `β`
(the support is their inf), so every gate is false and the operator vanishes.  This is the
`FGMNSourceLaws.graded_zero_of_above` field shape at the S2 occurrence, landed at RP-1
because it falls out of the definition. -/

/-- **the zero law at above-grade inputs** (published Lemma 3.14, the
`graded_zero_of_above` field shape): `S2AboveGrade β g → s2GradedRes β g = 0`. -/
theorem s2GradedRes_zero_of_above {β : ℕ} {g : Polynomial O}
    (h : S2AboveGrade h2 hq β g) : s2GradedRes h2 hq β g = 0 := by
  have hdv := (S2AboveGrade_iff_dvSupp h2 hq).mp h
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff, Polynomial.coeff_zero]
  unfold s2GradedCoeff
  rw [if_neg]
  intro hgate
  exact absurd (dvSupp_le_of_slotOnGrade h2 hq hgate) (not_le.mpr hdv)

/-- the zero polynomial has zero graded residual at every grade (`0 ∈ P_β⁺` always,
RP-0's `S2AboveGrade_zero`). -/
theorem s2GradedRes_zero (β : ℕ) : s2GradedRes h2 hq β (0 : Polynomial O) = 0 :=
  s2GradedRes_zero_of_above h2 hq (S2AboveGrade_zero h2 hq β)

/-! ## Part 5 — the S2-frame ϖ-read value `twistRead 0 1 = 1`

C35b landed `twistRead 1 x = 1` (the height-1 read of the digit `x`); the teeth below also
need the height-0 read of the digit `1`.  Same computation pattern, at `k = 0`. -/

/-- `i(0) = 0` at the S2 frame (C35b's `slotIdx_one` pattern at `k = 0`). -/
theorem slotIdx_zero : (s2Frame h2 hq).slotIdx 0 = 0 := by
  change ((List.range 2).find? (fun i => (i * 1) % 2 == 0 % 2)).getD 0 = 0
  rfl

/-- `q(0) = 0` at the S2 frame. -/
theorem twistExp_zero : (s2Frame h2 hq).twistExp 0 = 0 := by
  rw [KeyFrame.twistExp, slotIdx_zero h2 hq]
  simp

/-- the height-0 slot window is `{0}` at the S2 frame. -/
theorem slotWindow_zero : (s2Frame h2 hq).slotWindow 0 = {0} := by
  rw [KeyFrame.slotWindow]
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
    f1_eq h2 hq, e1_eq h2 hq, h_eq h2 hq, slotIdx_zero h2 hq]
  omega

/-- the normalized slot residue of the digit `1` at height `0` is `1`. -/
theorem slotRes_zero_one :
    (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) 0 (1 : Polynomial O) = 1 := by
  rw [KeyFrame.slotRes, slotWindow_zero h2 hq, Finset.sum_singleton]
  have hidx : (s2Frame h2 hq).slotIdx 0 + (s2Frame h2 hq).e₁ * 0 = 0 := by
    rw [slotIdx_zero h2 hq, e1_eq h2 hq]
  rw [hidx]
  have hdig : (0 - 0 * (s2Frame h2 hq).h) / (s2Frame h2 hq).e₁ = 0 := by
    rw [h_eq h2 hq, e1_eq h2 hq]
  rw [hdig, Polynomial.coeff_one_zero, digAt_zero, map_one, map_one, map_one, pow_zero,
    mul_one]

/-- **the ϖ-read of the digit `1` at height `0` is `1`** — the height-0 companion of C35b's
`twistRead_one_X`. -/
theorem twistRead_zero_one :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) 0 (1 : Polynomial O) = 1 := by
  simp only [KeyFrame.twistRead, twistExp_zero h2 hq, pow_zero, one_mul]
  exact slotRes_zero_one h2 hq

/-! ## Part 6 — development and height teeth at the S2 frame

The slot data of `Φ′`, `x·Φ′`, `Φ′²` (private copies of C130s6's private helpers where
needed; the `dev`/`dvHgt` teeth are public — RP-8's key-power computations reuse them). -/

private theorem one_mod_key : (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_one, key_eq h2 hq, s2Key_deg]; norm_num)

private theorem sh_one : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], sh_C h2 hq]
  simp

/-- `dev` tooth: the `Φ′`-development of `Φ′` has slot 1 equal to `1`. -/
theorem dev_key_one :
    dev (s2Frame h2 hq).key ((s2Frame h2 hq).key : Polynomial O) 1 = 1 := by
  have h := dev_mul_pow (s2Frame h2 hq).hmonic 1 (1 : Polynomial O) 0
  rw [Nat.add_zero, one_mul, pow_one] at h
  rw [h]
  exact one_mod_key h2 hq

/-- `dev` tooth: the `Φ′`-development of `x·Φ′` has slot 1 equal to `x`. -/
theorem dev_X_mul_key_one :
    dev (s2Frame h2 hq).key (Polynomial.X * (s2Frame h2 hq).key : Polynomial O) 1
      = Polynomial.X := by
  have h := dev_mul_pow (s2Frame h2 hq).hmonic 1 (Polynomial.X : Polynomial O) 0
  rw [Nat.add_zero, pow_one] at h
  rw [h]
  exact (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_X, key_eq h2 hq, s2Key_deg]; norm_num)

/-- `dev` tooth: the `Φ′`-development of `Φ′²` has slot 0 equal to `0`. -/
theorem dev_key_sq_zero :
    dev (s2Frame h2 hq).key
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 0 = 0 := by
  show (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) %ₘ (s2Frame h2 hq).key = 0
  rw [Polynomial.modByMonic_eq_zero_iff_dvd (s2Frame h2 hq).hmonic]
  exact dvd_mul_left _ _

/-- `dev` tooth: the `Φ′`-development of `Φ′²` has slot 2 equal to `1`. -/
theorem dev_key_sq_two :
    dev (s2Frame h2 hq).key
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 2 = 1 := by
  have h := dev_mul_pow (s2Frame h2 hq).hmonic 2 (1 : Polynomial O) 0
  rw [Nat.add_zero, one_mul] at h
  rw [show ((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      = (s2Frame h2 hq).key ^ 2 by ring, h]
  exact one_mod_key h2 hq

/-- `dvHgt` tooth: `dv((Φ′)₁) = 0` at `Φ′`. -/
theorem dvHgt_key_one :
    dvHgt (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 1 = 0 := by
  rw [dvHgt, dev_key_one h2 hq, sh_one h2 hq]

/-- `dvHgt` tooth: `dv((x·Φ′)₁) = 1` at `x·Φ′`. -/
theorem dvHgt_X_mul_key_one :
    dvHgt (s2Frame h2 hq) (Polynomial.X * (s2Frame h2 hq).key : Polynomial O) 1 = 1 := by
  rw [dvHgt, dev_X_mul_key_one h2 hq, sh_X h2 hq]

/-- `dvHgt` tooth: `dv((Φ′²)₀) = ⊤` at `Φ′²`. -/
theorem dvHgt_key_sq_zero :
    dvHgt (s2Frame h2 hq)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 0 = ⊤ := by
  rw [dvHgt, dev_key_sq_zero h2 hq, sh_zero h2 hq]

/-- `dvHgt` tooth: `dv((Φ′²)₂) = 0` at `Φ′²`. -/
theorem dvHgt_key_sq_two :
    dvHgt (s2Frame h2 hq)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 2 = 0 := by
  rw [dvHgt, dev_key_sq_two h2 hq, sh_one h2 hq]

/-! ## Part 7 — computation teeth (published eq (11) instances, at RP-0's landed grades) -/

/-- **tooth (eq (11), `s = 1`)**: `R_5(Φ′) = 1 = y^{⌊1/2⌋}` — the graded residual of the
key at its own landed grade `5 = u₂` (RP-0's `tooth_key` grade). -/
theorem tooth_gradedRes_key :
    s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) = 1 := by
  have hgate : S2SlotOnGrade h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) (5 % 2 + 2 * 0) :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨0, dvHgt_key_one h2 hq, by norm_num⟩
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff]
  match t with
  | 0 =>
    rw [Polynomial.coeff_one_zero]
    unfold s2GradedCoeff
    rw [if_pos hgate, show (5 - 5 * (5 % 2 + 2 * 0)) / 2 = 0 by norm_num,
      show 5 % 2 + 2 * 0 = 1 by norm_num, dev_key_one h2 hq]
    exact twistRead_zero_one h2 hq
  | (t + 1) =>
    rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega), Polynomial.coeff_one]
    simp

/-- **tooth (mixed read)**: `R_7(x·Φ′) = 1` — the graded residual at the landed composite
grade `7 = 2 + 5` (RP-0's `tooth_X_mul_key` grade), through C35b's landed ϖ-read value
`twistRead 1 x = 1`. -/
theorem tooth_gradedRes_X_mul_key :
    s2GradedRes h2 hq 7 (Polynomial.X * (s2Frame h2 hq).key : Polynomial O) = 1 := by
  have hgate : S2SlotOnGrade h2 hq 7
      (Polynomial.X * (s2Frame h2 hq).key : Polynomial O) (7 % 2 + 2 * 0) :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨1, dvHgt_X_mul_key_one h2 hq, by norm_num⟩
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff]
  match t with
  | 0 =>
    rw [Polynomial.coeff_one_zero]
    unfold s2GradedCoeff
    rw [if_pos hgate, show (7 - 5 * (7 % 2 + 2 * 0)) / 2 = 1 by norm_num,
      show 7 % 2 + 2 * 0 = 1 by norm_num, dev_X_mul_key_one h2 hq]
    exact twistRead_one_X h2 hq
  | (t + 1) =>
    rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega), Polynomial.coeff_one]
    simp

/-- **tooth (eq (11), `s = 2` — the `y`-power is live)**: `R_10(Φ′²) = y = y^{⌊2/2⌋}` — the
graded residual at the landed grade `10 = 5 + 5` (RP-0's `tooth_key_sq` grade) is genuinely
polynomial-valued: slot 0 is off-line (height `⊤`), slot 2 reads `1` at `y`-power 1. -/
theorem tooth_gradedRes_key_sq :
    s2GradedRes h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      = Polynomial.X := by
  have hgate : S2SlotOnGrade h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) (10 % 2 + 2 * 1) :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨0, dvHgt_key_sq_two h2 hq, by norm_num⟩
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff]
  match t with
  | 0 =>
    rw [Polynomial.coeff_X_zero]
    exact s2GradedCoeff_eq_zero_of_dvHgt_top h2 hq (dvHgt_key_sq_zero h2 hq)
  | 1 =>
    rw [Polynomial.coeff_X_one]
    unfold s2GradedCoeff
    rw [if_pos hgate, show (10 - 5 * (10 % 2 + 2 * 1)) / 2 = 0 by norm_num,
      show 10 % 2 + 2 * 1 = 2 by norm_num, dev_key_sq_two h2 hq]
    exact twistRead_zero_one h2 hq
  | (t + 2) =>
    rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega), Polynomial.coeff_X]
    simp

/-- **tooth (the zero law fires)**: `R_3(Φ′) = 0` — grade `3` is strictly below the key's
grade `5`, i.e. `Φ′ ∈ P_3⁺`, and the operator vanishes there (published Lemma 3.14 at a
concrete input). -/
theorem tooth_gradedRes_above :
    s2GradedRes h2 hq 3 ((s2Frame h2 hq).key : Polynomial O) = 0 :=
  s2GradedRes_zero_of_above h2 hq (by
    unfold S2AboveGrade
    have h3 : ((3 : ℕ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) := by norm_cast
    rw [s2Hgt₂_key h2 hq, h3]
    exact_mod_cast (by norm_num : (3 : ℤ) < 5))

/-- **tooth (non-vacuity)**: the operator is NOT the zero operator — at RP-0's landed exact
grade `7` of `x·Φ′` it returns `1 ≠ 0`. -/
theorem tooth_gradedRes_ne_zero :
    s2GradedRes h2 hq 7 (Polynomial.X * (s2Frame h2 hq).key : Polynomial O) ≠ 0 := by
  rw [tooth_gradedRes_X_mul_key h2 hq]
  exact one_ne_zero

end S2

end Uniformity.Density.Tower.C130rp1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp1.S2SlotOnGrade
#print axioms Uniformity.Density.Tower.C130rp1.s2SlotOnGrade_iff
#print axioms Uniformity.Density.Tower.C130rp1.s2SlotOnGrade_parity
#print axioms Uniformity.Density.Tower.C130rp1.dvSupp_le_of_slotOnGrade
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedCoeff
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedCoeff_pin_irrel
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedCoeff_eq_twistRead
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedCoeff_slot
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedCoeff_eq_zero_of_dvHgt_top
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedCoeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedCoeff_eq_zero_of_grade_lt
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedRes
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedRes_coeff
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedRes_eq_sum_range
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedRes_natDegree_le
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedRes_coeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedRes_zero_of_above
#print axioms Uniformity.Density.Tower.C130rp1.s2GradedRes_zero
#print axioms Uniformity.Density.Tower.C130rp1.slotIdx_zero
#print axioms Uniformity.Density.Tower.C130rp1.twistExp_zero
#print axioms Uniformity.Density.Tower.C130rp1.slotWindow_zero
#print axioms Uniformity.Density.Tower.C130rp1.slotRes_zero_one
#print axioms Uniformity.Density.Tower.C130rp1.twistRead_zero_one
#print axioms Uniformity.Density.Tower.C130rp1.dev_key_one
#print axioms Uniformity.Density.Tower.C130rp1.dev_X_mul_key_one
#print axioms Uniformity.Density.Tower.C130rp1.dev_key_sq_zero
#print axioms Uniformity.Density.Tower.C130rp1.dev_key_sq_two
#print axioms Uniformity.Density.Tower.C130rp1.dvHgt_key_one
#print axioms Uniformity.Density.Tower.C130rp1.dvHgt_X_mul_key_one
#print axioms Uniformity.Density.Tower.C130rp1.dvHgt_key_sq_zero
#print axioms Uniformity.Density.Tower.C130rp1.dvHgt_key_sq_two
#print axioms Uniformity.Density.Tower.C130rp1.tooth_gradedRes_key
#print axioms Uniformity.Density.Tower.C130rp1.tooth_gradedRes_X_mul_key
#print axioms Uniformity.Density.Tower.C130rp1.tooth_gradedRes_key_sq
#print axioms Uniformity.Density.Tower.C130rp1.tooth_gradedRes_above
#print axioms Uniformity.Density.Tower.C130rp1.tooth_gradedRes_ne_zero

end AxCheck
