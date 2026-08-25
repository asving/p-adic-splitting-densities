/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp4
import Uniformity.ChapC.C130fg

/-!
# Uniformity.ChapC.C130rp6 — S2-source plan nodes RP-5/RP-6 (CORES 3-4/4) — graded_mul CLOSED

**S2-source plan nodes RP-5 + RP-6 (CORES 3/4 and 4/4 of `graded_mul`)**
(`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 rows RP-5 "Discharge the inner residual
product and twist normalization" and RP-6 "Assemble exact-grade product plus polynomial
identity for arbitrary inputs"), on RP-4's convolution engine (C130rp4), RP-0's grade bank
(C130rp0), and the A-C.13-amended C130fg field shape (U14,
`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §8.1: the `PrevGrade β'` premise is
RESTORED; its S2 realization is evenness, `e₂ ∣ β = 2 ∣ β`).

## The RP-5 audit (row mandate: B39a `resPoly_mul_gen`) — recorded

The plan row anticipated discharging the inner residual product through B39a's general
level-one law `resPoly_mul_gen`.  The audit finding, against RP-4's landed engine:

* **Inner residual product — DISCHARGED, B39a not needed.**  At the S2 frame the inner
  (level-one) residual of a depth-two slot is a SINGLE ϖ-digit (`s2_twistRead_eq_digAt`:
  window `{0}`, twist letter `η = 1`), so the inner product is the reduced two-digit product
  `(a·b) %ₘ Φ′` — discharged by RP-3's survival core `s2_twistRead_mul_modByMonic` (value
  half) with NV-3's `≤` and RP-4's `≥` height halves.  B39a's `resPoly_mul_gen` (which needs
  side-set nonemptiness/coprimality data and produces the general side polynomial) has no
  remaining S2 work: every surviving convolution term in `s2GradedCoeff_mul_aux` factors
  through the survival core at exact on-line heights.
* **Twist normalization — DISCHARGED at the coefficient and polynomial levels** by RP-4
  (`s2GradedCoeff_mul` reads slot `T + c`; `s2GradedCoeff_mul_zero_of_odd` kills the one
  below-twist coefficient; `s2GradedRes_mul_of_exact` assembles `X^c·(R·R)`).
* **The one genuinely missing residual-normalization fact — LANDED here**: the twist is
  honest at the `y`-ORDER level only against a NONZERO product, and no landed row gives
  nonvanishing of the graded residual at exact grade (RP-7's `graded_scalar_nonzero` is the
  `coeff 0` statement under the `deg < deg φ₂` fence; RP-8's is about the normalized
  residual).  On B39a's route this was `natDegree_resPoly`'s nonzero half — the analogue is
  ★ `s2GradedRes_ne_zero_of_exact` below, via the new inf-attainment gate witness
  `exists_slotOnGrade_of_exact` (every exact-grade polynomial has an on-line slot) and
  C.23's attained-height nonvanishing `KeyFrame.slotRes_ne_zero`.  RP-9's "including all
  zero cases" collapses against it: at exact grades there are no zero cases.

## The RP-6 assembly (this file's ★ headline)

* `S2PrevGrade β := 2 ∣ β` — the S2 realization of the restored C130fg `PrevGrade` field
  (U14 §8.1: preceding-value-group membership; under the full-current-group clearing this is
  `e' ∣ β`, and `e' = e₂ = 2` at S2 — evenness).  Shape-pinned to `ℕ → Prop`.
* ★ `s2_graded_mul` — the A-C.13-amended `FGMNSourceLaws.graded_mul` field shape VERBATIM at
  the S2 operators: `∀ β β' g h, ExactGrade β g → ExactGrade β' h → PrevGrade β' →
  ExactGrade (β+β') (g·h) ∧ R_{β+β'}(g·h) = R_β(g)·R_{β'}(h)`, with
  `ExactGrade := S2ExactGrade` (RP-0), `R := s2GradedRes` (RP-1), `PrevGrade := S2PrevGrade`.
  Junk-input handling is exactly the field's: the statement is TOTAL in `g, h` (the S2
  operators are total; RP-1's junk-total residual, RP-0's totally-defined grade `Prop`s) and
  arbitrary inputs are fenced by the hypotheses alone — the zero polynomial, e.g., satisfies
  no `S2ExactGrade` (RP-0's `S2ExactGrade_zero_false`), so it never reaches the conclusion.
* ★ `s2_graded_mul_twisted` — the S2 BONUS law (the repo's OWN arbitrary-grade
  generalization, U14 §5/§8.2 — NOT published Cor 4.12(2)): no `PrevGrade` premise, carry
  twist `X^{(β%2)·(β'%2)}`, exact-grade conjunct bundled — RP-4's `s2GradedRes_mul_of_exact`
  re-exported in the FD-0-ready conjunction shape.
* `s2_graded_mul_fills` — the FD-0 pin: for ANY `FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5`
  whose `nextValue`/`gradedResidual`/`PrevGrade` fields are the S2 operators, this file's
  theorem IS its `graded_mul` field (typed against the actual C130fg structure, so FD-0's
  record plumbing has nothing left to prove for this clause).

## Teeth

`tooth_prevGrade_two`/`tooth_prevGrade_fence`: `S2PrevGrade 2` holds and `S2PrevGrade 5`
FAILS — the assembled law's premise correctly fences out the odd-odd genre whose plain
conclusion is machine-refuted (`C130rp2.tooth_graded_mul_plain_shape_refuted`,
`R₁₀(Φ′²) = X ≠ 1`).  `tooth_graded_mul_fires`/`tooth_graded_mul_value`: the assembled law
fires at `(5,2)` on `(Φ′, x)` and re-derives the landed `R₇ = 1` (both conjuncts).
`tooth_twisted_fires`: the bonus law at `(5,5)` delivers grade 10 AND re-derives
`R₁₀(Φ′²) = X`.  `tooth_ne_zero_key`: RP-5's nonvanishing fires on the landed grade-5 key.

## What this node does NOT claim (honesty scope)

* No `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` INSTANCE — `s2_graded_mul_fills`
  is conditional on a record FD-0 will build (`normalizedResidual` etc. do not exist yet).
* No `graded_scalar_nonzero` (RP-7), no normalized residual or its twist absorption (RP-8),
  no `y`-order addition law (RP-9 — this file lands only its missing nonvanishing input).
* Only the `PrevGrade`-fenced conjunction may be read as published Cor 4.12(2); the twisted
  law is the repo's own generalization (U14 §5).  The ϖ-read ↔ `ε(α)·R(a)(z)` dictionary
  stays on C.22/C.25's recorded faithfulness boundary.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`S2PrevGrade` (the evenness realization of the restored field — U14 §8.1's divisibility
test, carried as a definition until OPEN-DICT-2 proves it), `exists_slotOnGrade_of_exact`,
`s2GradedRes_ne_zero_of_exact`, and the three assembly statements.

**DEPENDS.** C130rp4 (`s2GradedRes_mul_of_prevGrade`, `s2GradedRes_mul_of_exact`) · C130rp2
(`s2_twistRead_eq_slotRes`) · C130rp1 (`s2GradedRes`/`s2GradedCoeff` + `s2GradedRes_coeff`,
`S2SlotOnGrade` + `s2SlotOnGrade_iff` + `s2GradedCoeff_slot`, teeth) · C130rp0
(`S2ExactGrade` + normal forms + `S2ExactGrade_mul`, grade teeth) · C130fg (the field
shapes, READ; `FGMNSourceData` for the conditional pin) · C130s2 (`s2DepthTwo`) · C.23
(`KeyFrame.slotRes_ne_zero`) · C.06 (`dvHgt`/`dvSupp`) · B.03 (`degree_dev_lt`) · C35b/C.97
(`key_eq`, `s2Key_natDegree`, `s2Frame`, `s2Frame_pin`) · mathlib
(`Finset.exists_mem_eq_inf`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp6

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130rp4

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — NODE RP-5: the audit residue

The audit record is in the module docstring.  What lands: the inf-attainment gate witness
(every exact-grade polynomial HAS an on-line slot — `dvSupp` is a finite `Finset.inf`, so
the exact value is attained) and the nonvanishing of the graded residual at exact grade —
the `y`-order honesty of RP-4's twist that RP-9/RP-10 consume, and the S2 analogue of the
nonzero half B39a's `resPoly_mul_gen` route would have supplied via `natDegree_resPoly`. -/

/-- private copy of RP-4's short-digit degree bound (the private-copy pattern): S2
development digits have `natDegree < 2` (the key has degree 2, B.03). -/
private theorem natDegree_dev_lt_two (f : Polynomial O) (j : ℕ) :
    (dev (s2Frame h2 hq).key f j).natDegree < 2 := by
  rcases eq_or_ne (dev (s2Frame h2 hq).key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    omega
  · have h := Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos f j)
    have hk : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
      rw [key_eq h2 hq]
      exact s2Key_natDegree
    omega

/-- **the gate witness (inf attainment)**: an exact-grade polynomial has an on-line slot —
`dvSupp` is a `Finset.inf` over finitely many slots, so the attained value `β` is some
slot's own line term.  (RP-1's gate `S2SlotOnGrade` was consumed only under caller-supplied
witnesses until now; this closes the existence side at exact grades.) -/
theorem exists_slotOnGrade_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) :
    ∃ s : ℕ, S2SlotOnGrade h2 hq β g s := by
  have hsupp : dvSupp (s2Frame h2 hq) g 5 2 = (β : ℕ∞) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mp hg
  rw [dvSupp] at hsupp
  obtain ⟨j, hjmem, hjeq⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (g.natDegree + 1))
      Finset.nonempty_range_add_one
      (fun j => 2 • dvHgt (s2Frame h2 hq) g j + ((5 : ℕ) : ℕ∞) * (j : ℕ∞))
  rw [hjeq] at hsupp
  refine ⟨j, ?_⟩
  unfold S2SlotOnGrade
  rw [← hsupp]
  congr 1

/-- ★ **NODE RP-5 — the graded residual at exact grade is NONZERO**: `S2ExactGrade β g`
forces `R_β(g) ≠ 0` — the attained on-line slot (gate witness above) is read at its EXACT
height, and an attained-height ϖ-read never vanishes (C.23's `slotRes_ne_zero`; the S2
twist letter is invisible, `s2_twistRead_eq_slotRes`).  This is the `y`-order honesty of
RP-4's twist law: `X^c` shifts orders only against a nonzero product, so with this lemma
RP-9's "zero cases" are empty at exact grades.  No degree fence (contrast RP-7's scalar
`coeff 0` statement, which is FALSE without its fence). -/
theorem s2GradedRes_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) :
    s2GradedRes h2 hq β g ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_slotOnGrade_of_exact h2 hq hg
  obtain ⟨m, hm, hline⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  intro h0
  -- the coefficient at the witness slot, read through the master law
  have hcoeff := s2GradedRes_coeff h2 hq β g (s / 2)
  rw [h0, Polynomial.coeff_zero] at hcoeff
  have hslot := s2GradedCoeff_slot h2 hq hgate
  rw [← hcoeff, show (β - 5 * s) / 2 = m from by omega] at hslot
  -- the attained-height read is nonzero
  have hne : (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m
      (dev (s2Frame h2 hq).key g s) ≠ 0 := by
    rw [s2_twistRead_eq_slotRes h2 hq]
    refine (s2Frame h2 hq).slotRes_ne_zero h2 1 (s2Frame_pin h2 hq) ?_ hm
    have h := natDegree_dev_lt_two h2 hq g s
    simpa [e1_eq h2 hq, f1_eq h2 hq] using h
  exact hne hslot.symm

/-! ## Part 2 — the S2 `PrevGrade` realization (the A-C.13 restored field)

U14 §8.1's realization obligation: `PrevGrade β` must be membership of the cleared grade in
the PRECEDING value group `Γ_r`; under the full-current-group integer clearing this is the
divisibility test `e' ∣ β`, and `e' = e₂ = 2` at S2 — evenness.  Carried as a definition
(exactly as the C130fg field docstring mandates) until OPEN-DICT-2 proves the divisibility
test general. -/

/-- **the S2 `PrevGrade`**: `β` lies in the preceding value group `Γ₁` in cleared
coordinates — `e₂ ∣ β`, i.e. evenness (U14 §8.1; C130fg's restored `PrevGrade` field at the
S2 numerals `(e₂, f₂, u₂) = (2, 1, 5)`). -/
def S2PrevGrade (β : ℕ) : Prop := 2 ∣ β

/-- shape pin: `S2PrevGrade` has EXACTLY the C130fg `PrevGrade` field shape `ℕ → Prop`. -/
example : ℕ → Prop := S2PrevGrade

/-- **the evenness normal form**: `S2PrevGrade β ↔ β % 2 = 0` — the consumable arithmetic
shape (RP-4's `s2GradedCoeff_mul_of_prevGrade` speaks `β' % 2 = 0`). -/
theorem S2PrevGrade_iff_mod (β : ℕ) : S2PrevGrade β ↔ β % 2 = 0 := by
  unfold S2PrevGrade
  omega

/-! ## Part 3 — ★ NODE RP-6: `graded_mul` ASSEMBLED, the amended C130fg field shape

The statement below is BYTE-PARALLEL to the A-C.13-amended `FGMNSourceLaws.graded_mul`
(`∀ β β' (g h : Polynomial O), S.ExactGrade β g → S.ExactGrade β' h → S.PrevGrade β' →
S.ExactGrade (β + β') (g * h) ∧ S.gradedResidual (β + β') (g * h) = …`), with the S2
operator readings `ExactGrade := S2ExactGrade` (RP-0), `gradedResidual := s2GradedRes`
(RP-1), `PrevGrade := S2PrevGrade` (Part 2).  Totality in `g, h` — the field's arbitrary
(junk) inputs — is inherited from the total S2 operators; the hypotheses alone fence. -/

/-- ★ **NODE RP-6 — the S2 `graded_mul`** (published Cor 4.12(2) at the S2 occurrence,
INCLUDING its printed `β' ∈ Γ_{r-1}` premise as restored by A-C.13): at exact grades with
an even second grade, the product sits at exact grade `β + β'` AND the graded residual is
plainly multiplicative.  The grade conjunct is RP-0's `S2ExactGrade_mul`; the polynomial
conjunct is RP-4's `s2GradedRes_mul_of_prevGrade`.  This is the theorem FD-0 plugs into the
`FGMNSourceLaws` record (see `s2_graded_mul_fills`). -/
theorem s2_graded_mul :
    ∀ β β' (g h : Polynomial O),
      S2ExactGrade h2 hq β g → S2ExactGrade h2 hq β' h →
      S2PrevGrade β' →
        S2ExactGrade h2 hq (β + β') (g * h) ∧
        s2GradedRes h2 hq (β + β') (g * h)
          = s2GradedRes h2 hq β g * s2GradedRes h2 hq β' h :=
  fun _ β' _ _ hg hh hprev =>
    ⟨S2ExactGrade_mul h2 hq hg hh,
     s2GradedRes_mul_of_prevGrade h2 hq hg hh ((S2PrevGrade_iff_mod β').mp hprev)⟩

/-- ★ **the S2 BONUS law — the arbitrary-grade twisted product** (the repo's OWN
generalization of published Cor 4.12(2), U14 §5/§8.2 — NOT a transcription): no `PrevGrade`
premise, carry twist `X^{(β%2)·(β'%2)}`, exact-grade conjunct bundled.  RP-4's
`s2GradedRes_mul_of_exact` in the FD-0-ready conjunction shape (the shapes differ only by
the bundled grade conjunct, added here from RP-0's `S2ExactGrade_mul`). -/
theorem s2_graded_mul_twisted :
    ∀ β β' (g h : Polynomial O),
      S2ExactGrade h2 hq β g → S2ExactGrade h2 hq β' h →
        S2ExactGrade h2 hq (β + β') (g * h) ∧
        s2GradedRes h2 hq (β + β') (g * h)
          = Polynomial.X ^ (β % 2 * (β' % 2))
            * (s2GradedRes h2 hq β g * s2GradedRes h2 hq β' h) :=
  fun _ _ _ _ hg hh =>
    ⟨S2ExactGrade_mul h2 hq hg hh, s2GradedRes_mul_of_exact h2 hq hg hh⟩

/-! ## Part 4 — the FD-0 pin: the theorem IS the field, typed

Conditional on the record FD-0 will build (no instance exists yet — `normalizedResidual`
etc. are RP-8+): for ANY `FGMNSourceData` over the landed S2 tower whose three relevant
fields are the S2 operators, `s2_graded_mul` discharges the `graded_mul` field VERBATIM. -/

/-- **the FD-0 pin**: if `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` reads
`nextValue := s2Hgt₂`, `gradedResidual := s2GradedRes`, `PrevGrade := S2PrevGrade`, then
the A-C.13-amended `FGMNSourceLaws.graded_mul` field for `S` holds — byte-identical binder
shape, so FD-0's record assembly consumes `s2_graded_mul` with no residual proof work. -/
theorem s2_graded_mul_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5)
    (hval : S.nextValue = s2Hgt₂ h2 hq)
    (hres : S.gradedResidual = s2GradedRes h2 hq)
    (hprev : S.PrevGrade = S2PrevGrade) :
    ∀ β β' (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β' h →
      S.PrevGrade β' →
        S.ExactGrade (β + β') (g * h) ∧
        S.gradedResidual (β + β') (g * h)
          = S.gradedResidual β g * S.gradedResidual β' h := by
  intro β β' g h hg hh hp
  have hg' : S2ExactGrade h2 hq β g := by
    have hx : S.nextValue g = (β : WithTop ℤ) := hg
    rw [hval] at hx
    exact hx
  have hh' : S2ExactGrade h2 hq β' h := by
    have hx : S.nextValue h = (β' : WithTop ℤ) := hh
    rw [hval] at hx
    exact hx
  rw [hprev] at hp
  obtain ⟨hexact, hpoly⟩ := s2_graded_mul h2 hq β β' g h hg' hh' hp
  refine ⟨?_, ?_⟩
  · show S.nextValue (g * h) = ((β + β' : ℕ) : WithTop ℤ)
    rw [hval]
    exact hexact
  · rw [hres]
    exact hpoly

/-! ## Part 5 — teeth (regressions against the landed RP-0/RP-1/RP-4 values) -/

/-- **tooth**: `S2PrevGrade 2` — the grade of `x` is in the preceding group (even). -/
theorem tooth_prevGrade_two : S2PrevGrade 2 := ⟨1, rfl⟩

/-- **tooth (the fence)**: `¬ S2PrevGrade 5` — the odd key grade is OUTSIDE the restored
premise, so the assembled law cannot fire on the odd×odd pair `(5,5)` whose PLAIN conclusion
is machine-refuted (`C130rp2.tooth_graded_mul_plain_shape_refuted`: `R₁₀(Φ′²) = X ≠ 1`).
The fence is exactly as strong as the refutation demands. -/
theorem tooth_prevGrade_fence : ¬ S2PrevGrade 5 := by
  unfold S2PrevGrade
  omega

/-- **tooth (the assembled law fires)**: at `(5,2)` on `(Φ′, x)` both conjuncts land —
grade 7 exactly, and the plain product identity. -/
theorem tooth_graded_mul_fires :
    S2ExactGrade h2 hq 7 (((s2Frame h2 hq).key : Polynomial O) * Polynomial.X) ∧
    s2GradedRes h2 hq 7 (((s2Frame h2 hq).key : Polynomial O) * Polynomial.X)
      = s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O)
        * s2GradedRes h2 hq 2 (Polynomial.X : Polynomial O) := by
  have h := s2_graded_mul h2 hq 5 2 ((s2Frame h2 hq).key : Polynomial O) Polynomial.X
    (tooth_key h2 hq) (tooth_X h2 hq) tooth_prevGrade_two
  rwa [show (5 : ℕ) + 2 = 7 from rfl] at h

/-- **tooth (value regression)**: the assembled law re-derives the landed `R₇ = 1` — the
right side evaluates against RP-1's teeth to `1·1 = 1`, matching RP-1's hand-computed
`tooth_gradedRes_X_mul_key` (via `tooth_conv_prevGrade_matches`). -/
theorem tooth_graded_mul_value :
    s2GradedRes h2 hq 7 (((s2Frame h2 hq).key : Polynomial O) * Polynomial.X) = 1 := by
  rw [(tooth_graded_mul_fires h2 hq).2, tooth_gradedRes_key h2 hq, tooth_gradedRes_X h2 hq,
    mul_one]

/-- **tooth (the bonus law fires on the fenced-out pair)**: at `(5,5)` on `(Φ′, Φ′)` the
TWISTED law delivers grade 10 AND re-derives the landed `R₁₀(Φ′²) = X` — the arbitrary-grade
genre the `PrevGrade` fence excludes is carried by the twist, not lost. -/
theorem tooth_twisted_fires :
    S2ExactGrade h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) ∧
    s2GradedRes h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      = (Polynomial.X : Polynomial ((s2DepthTwo h2 hq).fld 2)) := by
  have h := s2_graded_mul_twisted h2 hq 5 5 ((s2Frame h2 hq).key : Polynomial O)
    (s2Frame h2 hq).key (tooth_key h2 hq) (tooth_key h2 hq)
  rw [show (5 : ℕ) + 5 = 10 from rfl] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, tooth_gradedRes_key h2 hq, mul_one, show 5 % 2 * (5 % 2) = 1 from rfl, pow_one,
    mul_one]

/-- **tooth (RP-5's nonvanishing fires)**: the landed grade-5 key has nonzero graded
residual through the general law alone (consistent with RP-1's `R₅(Φ′) = 1`). -/
theorem tooth_ne_zero_key :
    s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) ≠ 0 :=
  s2GradedRes_ne_zero_of_exact h2 hq (tooth_key h2 hq)

end S2

end Uniformity.Density.Tower.C130rp6

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp6.exists_slotOnGrade_of_exact
#print axioms Uniformity.Density.Tower.C130rp6.s2GradedRes_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C130rp6.S2PrevGrade
#print axioms Uniformity.Density.Tower.C130rp6.S2PrevGrade_iff_mod
#print axioms Uniformity.Density.Tower.C130rp6.s2_graded_mul
#print axioms Uniformity.Density.Tower.C130rp6.s2_graded_mul_twisted
#print axioms Uniformity.Density.Tower.C130rp6.s2_graded_mul_fills
#print axioms Uniformity.Density.Tower.C130rp6.tooth_prevGrade_two
#print axioms Uniformity.Density.Tower.C130rp6.tooth_prevGrade_fence
#print axioms Uniformity.Density.Tower.C130rp6.tooth_graded_mul_fires
#print axioms Uniformity.Density.Tower.C130rp6.tooth_graded_mul_value
#print axioms Uniformity.Density.Tower.C130rp6.tooth_twisted_fires
#print axioms Uniformity.Density.Tower.C130rp6.tooth_ne_zero_key

end AxCheck
