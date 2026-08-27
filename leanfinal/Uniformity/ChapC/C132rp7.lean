/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp2

/-!
# Uniformity.ChapC.C132rp7 — the μ₃ `graded_scalar_nonzero` law under the exact `< 4` fence (μ₃ campaign, node M3-RP7)

**[M3-RP7, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP7): a
mechanical port of the μ₂ scalar-nonvanishing bank (`C130rp8.lean:213-296`, published Thm 4.1 +
Cor 4.9(1)) to the just-assembled μ₃ total operator `s2Mu3GradedRes` (C132rp2): at exact μ₃
grade and `g.natDegree < deg Φ₂ = 4`, the `y⁰`-coefficient of the μ₃ graded residual is
nonzero, and the exact `FGMNSourceLaws.graded_scalar_nonzero` field shape at the μ₃ occurrence
`(e', f', u') = (2, 1, 21)`.

## The fence numeral: SHARED with μ₂, not re-derived

`FGMNSourceLaws.graded_scalar_nonzero`'s fence is `g.natDegree < (K.keyAt r).natDegree`, where
`r` is the AMBIENT `DeepTower` stage baked into `W`'s own type (`C130fg.lean:130-131,223-224`).
Both the μ₂ and μ₃ occurrences share the SAME ambient tower `W := s2DepthTwo h2 hq`, hence the
SAME `r = 2` and the SAME fence numeral `(K.keyAt 2).natDegree = 4` — this is exactly why the
row cites `s2KeyChain_keyAt_two_natDegree` (`C130rp8.lean:263-265`) as a landed input rather
than re-deriving the numeral from C132nv1's `s2Φ₂_natDegree` (used only where the CURRENT μ₃
recursion key `Φ₂ := s2DepthTwoKeyAt h2 hq 2` itself is manipulated, e.g. the `dev`/`dvHgt`
arguments below): the field-shape theorems here cite `s2KeyChain_keyAt_two_natDegree` verbatim,
matching the μ₂ `s2_graded_scalar_nonzero`/`_fills` pair byte-for-byte modulo the operator names.

## The one genuinely new step: the eval-1 collapse under the degree fence

At μ₂ the scalar lives directly in the graded residual's own `coeff 0`.  At μ₃ the recursive
coefficient `s2Mu3Coeff` reads the μ₂ operator through `Polynomial.eval 1 (s2GradedRes ...)`
(C132rp1's collapsed evaluation), so RP-7's engine must additionally show that this evaluation
EQUALS the μ₂ operator's own `coeff 0` under the SAME `< 4` fence — Part 2 below, which is
genuinely new content (not present in `C130rp8.lean:213-296`, since μ₂ never needed to
evaluate its own graded residual at a point): a low-degree input has an on-line slot ONLY at
abscissa `0` (every abscissa `≥ 1` is ruled out by the exact `hs1`-genre contradiction the old
RP-7 core already uses for `s ≥ 2`, ported here to EVERY `t ≥ 1`), so `s2GradedRes h2 hq m A`
is literally the constant polynomial `C ((s2GradedRes h2 hq m A).coeff 0)` and evaluation at
any point returns that same scalar.  BLOCKED-BECAUSE (over invention): nothing else new — every
other step is the μ₂ Part 2/3 argument with `s2Frame`'s key/`dvHgt`/`dvSupp` numerals ported to
`Φ₂`/`dv2Pin`/`dv2Supp`, or a direct citation of the already-landed C132rp0/rp1/rp2 pins.

## What lands

* `exists_mu3SlotOnGrade_of_exact`: the μ₃ inf-attainment gate witness (RP-5's engine,
  `C130rp6.lean:149-164`, ported from `dvSupp` to `dv2Supp`) — every μ₃-exact-grade polynomial
  has an on-line slot.  Not previously landed for μ₃ (M3-RP5 is a later row); self-contained
  here off `dv2Supp`'s own `Finset.inf` shape (C.11), no RP-5/RP-6 dependency.
* the private eval-collapse bridge (Part 2): `s2GradedRes_coeff_eq_zero_of_pos`,
  `s2GradedRes_eq_C_coeff_zero`, `eval_one_s2GradedRes_eq_coeff_zero`.
* ★ `s2Mu3GradedRes_coeff_zero_ne_zero_of_exact`: the μ₃ analogue of
  `s2GradedRes_coeff_zero_ne_zero_of_exact` (`C130rp8.lean:241-259`).
* ★ `s2Mu3_graded_scalar_nonzero`: the field-shape statement at the CONCRETE chain
  `s2DepthTwoKeyChain h2 hq`, citing `s2KeyChain_keyAt_two_natDegree` verbatim
  (`C130rp8.lean:273-281`'s exact shape).
* ★ `s2Mu3_graded_scalar_nonzero_fills`: the FD-0 pin for ANY `FGMNSourceData
  (s2DepthTwo h2 hq) K 2 1 21` (`C130rp8.lean:287-301`'s exact shape, `u' = 21` in place of `5`).
* `tooth_mu3_scalar_fires`: non-vacuity at the constant `1` (exact μ₃ grade `0`, degree
  `0 < 4`) — `Φ₂` itself CANNOT serve as this node's tooth (unlike μ₂'s `s2Frame` key `Φ′`,
  which has degree `2 < 4`): `deg Φ₂ = 4` fails the fence it is itself used to state.

## What this node does NOT claim (honesty scope)

No `ChainRealization`/socket instance (M3-FD0/M3-SG); no additivity/multiplicativity/
normalization of the μ₃ operator (M3-RP3/RP5/RP6/RP8); no recipe or key-existence content
(M3-RP9/RP10).  The OPEN-RP1-TRANSPORT faithfulness split stays exactly as C132rp1 left it; no
theorem here touches it — every statement here is about the repo's own `s2Mu3GradedRes` and
`s2GradedRes` operators, at the SAME already-landed dictionary.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2Mu3GradedRes_coeff_zero_ne_zero_of_exact`, `s2Mu3_graded_scalar_nonzero` (+ `_fills`), and
the two private bridging facts (Part 2).

**DEPENDS.** C132rp2 (`s2Mu3GradedRes`, `s2Mu3GradedRes_coeff`) · C132rp1
(`S2Mu3SlotOnGrade` + `s2Mu3SlotOnGrade_iff` + `s2Mu3SlotOnGrade_inner_exact`, `s2Mu3Coeff` +
`s2Mu3Coeff_slot`, `s2Mu3Eps_eq_one`) · C132rp0 (`S2Mu3ExactGrade` + `_iff_dv2Supp`) · C132nv1
(`s2Φ₂_monic`, `s2Φ₂_natDegree`) · C132nv5 (`s2Hgt₃_one_eq_zero`, for the tooth) · C130rp8
(`s2GradedRes_coeff_zero_ne_zero_of_exact`, `s2KeyChain_keyAt_two_natDegree`) · C130rp1
(`s2GradedRes` + `s2GradedRes_coeff`, `S2SlotOnGrade` + `s2SlotOnGrade_iff`,
`s2GradedCoeff_eq_zero_of_not_slotOnGrade`) · C130fg (`FGMNSourceData`, the field shapes) ·
C130s2 (`s2DepthTwo`, `s2DepthTwoKeyChain`, `s2DepthTwo_Dcum_two`, `s2DepthTwoKeyAt`) · C130s6/
C35b (`s2Frame`, `key_natDegree_two`) · C27 (`dv2Hgt_zero`) · C11 (`dv2Hgt`, `dv2Pin`,
`dv2Supp`) · B.04 (`dev_eq_zero_of_lt`) · mathlib (`Finset.exists_mem_eq_inf`,
`Polynomial.modByMonic_eq_self_iff`, `Polynomial.degree_lt_degree`, `Polynomial.coeff_C`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch and the μ₂ porting pattern.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp7

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the μ₃ inf-attainment gate witness (RP-5's engine, ported to `dv2Supp`)

Self-contained: `dv2Supp` is a `Finset.inf`, so the attained value `β` is some slot's own line
term — no RP-5/RP-6 dependency (those rows land only their own `S2ExactGrade`-level engine). -/

/-- **the μ₃ gate witness (inf attainment)**: an exact-μ₃-grade polynomial has an on-line
slot — the μ₃ analogue of `C130rp6.exists_slotOnGrade_of_exact`, off `dv2Supp`'s own
`Finset.inf` shape (C.11) rather than `dvSupp`'s. -/
theorem exists_mu3SlotOnGrade_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) :
    ∃ s : ℕ, S2Mu3SlotOnGrade h2 hq β g s := by
  have hsupp : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
      = (β : ℕ∞) := (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hg
  rw [dv2Supp] at hsupp
  obtain ⟨j, -, hjeq⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (g.natDegree + 1))
      Finset.nonempty_range_add_one
      (fun j => 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g j
        + ((21 : ℕ) : ℕ∞) * (j : ℕ∞))
  rw [hjeq] at hsupp
  refine ⟨j, ?_⟩
  unfold S2Mu3SlotOnGrade
  rw [← hsupp]
  congr 1

/-! ## Part 2 — the eval-1 collapse under the degree fence (genuinely new content)

`s2GradedRes h2 hq m A` at `A.natDegree < 4` is supported only at `y⁰`: every abscissa
`t ≥ 1` is off-line by the SAME contradiction the old RP-7 core uses to rule out `s ≥ 2`
(`C130rp8.lean:245-255`), so the polynomial equals `C (coeff 0)` and evaluation at `1`
collapses to that same scalar. -/

/-- private copy of the corpus's private-copy pattern (`C130rp8`/`C130kp0`/`C130kp5` each keep
their own): `deg (s2Frame's key) = 2`. -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- private bridge: past abscissa `0`, every μ₂ graded coefficient of a `< 4`-degree input
vanishes — the SAME `dev_eq_zero_of_lt`/`stageHeight_zero` contradiction as the old RP-7
core's `hs1` block, generalized from ruling out one witness slot to every `t ≥ 1`. -/
private theorem s2GradedRes_coeff_eq_zero_of_pos {m t : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 4) (ht : 0 < t) :
    (s2GradedRes h2 hq m A).coeff t = 0 := by
  rw [s2GradedRes_coeff]
  refine s2GradedCoeff_eq_zero_of_not_slotOnGrade h2 hq ?_
  intro hgate
  obtain ⟨m', hm', -⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  have hdev : dev (s2Frame h2 hq).key A (m % 2 + 2 * t) = 0 :=
    dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos A _
      (by rw [key_natDegree_two h2 hq]; omega)
  have htop : dvHgt (s2Frame h2 hq) A (m % 2 + 2 * t) = ⊤ := by
    rw [dvHgt, hdev]
    exact (s2Frame h2 hq).stageHeight_zero
  rw [htop] at hm'
  exact WithTop.top_ne_coe hm'

/-- private bridge: under the `< 4` fence the μ₂ graded residual IS its own degree-zero
term, displayed as a constant polynomial. -/
private theorem s2GradedRes_eq_C_coeff_zero {m : ℕ} {A : Polynomial O} (hA : A.natDegree < 4) :
    s2GradedRes h2 hq m A = Polynomial.C ((s2GradedRes h2 hq m A).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => simp
  | (t + 1) =>
    rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero t)]
    exact s2GradedRes_coeff_eq_zero_of_pos h2 hq hA (Nat.succ_pos t)

/-- private bridge: evaluation of the (constant, under the fence) μ₂ graded residual at ANY
point — in particular the collapsed letter `1` — returns its `coeff 0`. -/
private theorem eval_one_s2GradedRes_eq_coeff_zero {m : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 4) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m A)
      = (s2GradedRes h2 hq m A).coeff 0 := by
  conv_lhs => rw [s2GradedRes_eq_C_coeff_zero h2 hq hA]
  exact Polynomial.eval_C

/-! ## Part 3 — ★ NODE RP-7: `graded_scalar_nonzero` at the μ₃ occurrence -/

/-- ★ **the RP-7 worker (μ₃, numeric fence)**: at exact μ₃ grade with `deg g < 4`, the
`y⁰`-coefficient of the μ₃ graded residual is nonzero.  The gate witness's abscissa is forced
to `0` (any `s ≥ 1` gives a zero digit, hence `⊤` height, hence sits on no line — the fence is
`deg g < deg Φ₂` itself here, unlike μ₂'s `deg g < deg(\text{next key})`, so a SINGLE abscissa
survives), the inner development at slot `0` is `g` itself, and its inner exact μ₂ grade
inherits the ALREADY-LANDED μ₂ scalar-nonvanishing law (`s2GradedRes_coeff_zero_ne_zero_of_exact`,
`C130rp8.lean:241-259`) through the Part 2 eval-1 collapse. -/
theorem s2Mu3GradedRes_coeff_zero_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hdeg : g.natDegree < 4) :
    (s2Mu3GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_mu3SlotOnGrade_of_exact h2 hq hg
  have hs0 : s = 0 := by
    by_contra hs
    obtain ⟨m, hm, -⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
    have hdev : dev (s2DepthTwoKeyAt h2 hq 2) g s = 0 :=
      dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) g s
        (by rw [s2Φ₂_natDegree h2 hq]; omega)
    have htop : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g s = ⊤ := by
      rw [dv2Pin, hdev]
      exact Uniformity.Density.Tower.dv2Hgt_zero _
    rw [htop] at hm
    exact WithTop.top_ne_coe hm
  subst hs0
  have hdevg : dev (s2DepthTwoKeyAt h2 hq 2) g 0 = g := by
    show g %ₘ (s2DepthTwoKeyAt h2 hq 2) = g
    exact (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [s2Φ₂_natDegree h2 hq]; omega))
  have hinner : S2ExactGrade h2 hq (β / 2) g := by
    have h := s2Mu3SlotOnGrade_inner_exact h2 hq hgate
    rw [show (β - 21 * 0) / 2 = β / 2 by omega, hdevg] at h
    exact h
  have hslot := s2Mu3Coeff_slot h2 hq hgate
  rw [show (0 : ℕ) / 2 = 0 by norm_num] at hslot
  rw [show (β - 21 * 0) / 2 = β / 2 by omega, hdevg, s2Mu3Eps_eq_one, one_mul] at hslot
  rw [s2Mu3GradedRes_coeff, hslot, eval_one_s2GradedRes_eq_coeff_zero h2 hq hdeg]
  exact s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hinner hdeg

/-- **the concrete chain's next-key degree numeral, re-cited**: `deg (keyAt 2) = 4`
(`s2KeyChain_keyAt_two_natDegree`, `C130rp8.lean:263-266`) — SHARED with μ₂ since both
occurrences fix the same ambient `r = 2` (module docstring). -/
theorem s2Mu3KeyChain_keyAt_two_natDegree :
    ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree = 4 :=
  s2KeyChain_keyAt_two_natDegree h2 hq

/-- ★ **NODE RP-7 — the μ₃ `graded_scalar_nonzero`** (published Thm 4.1 + Cor 4.9(1); the
C130fg `FGMNSourceLaws.graded_scalar_nonzero` field shape VERBATIM at the μ₃ operators, with
the fence spelled against the concrete chain `s2DepthTwoKeyChain`): at exact μ₃ grade below
the shared next-key degree, the scalar of the μ₃ graded residual is nonzero. -/
theorem s2Mu3_graded_scalar_nonzero :
    ∀ β (g : Polynomial O),
      S2Mu3ExactGrade h2 hq β g →
      g.natDegree < ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree →
      g ≠ 0 →
      (s2Mu3GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  intro β g hg hdeg _
  rw [s2KeyChain_keyAt_two_natDegree h2 hq] at hdeg
  exact s2Mu3GradedRes_coeff_zero_ne_zero_of_exact h2 hq hg hdeg

/-- **the FD-0 pin (μ₃ occurrence, `(e', f', u') = (2, 1, 21)`)**: if `S : FGMNSourceData
(s2DepthTwo h2 hq) K 2 1 21` reads `nextValue := s2Hgt₃` and `gradedResidual := s2Mu3GradedRes`,
then the `FGMNSourceLaws.graded_scalar_nonzero` field for `S` holds — byte-identical binder
shape to μ₂'s `s2_graded_scalar_nonzero_fills` (`C130rp8.lean:287-301`), `u' = 21` in place of
`5`. -/
theorem s2Mu3_graded_scalar_nonzero_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 21)
    (hval : S.nextValue = s2Hgt₃ h2 hq)
    (hres : S.gradedResidual = s2Mu3GradedRes h2 hq) :
    ∀ β (g : Polynomial O),
      S.ExactGrade β g → g.natDegree < (K.keyAt 2).natDegree → g ≠ 0 →
        (S.gradedResidual β g).coeff 0 ≠ 0 := by
  intro β g hg hdeg _
  have hg' : S2Mu3ExactGrade h2 hq β g := by
    have hx : S.nextValue g = (β : WithTop ℤ) := hg
    rw [hval] at hx
    exact hx
  have hk := (K.keyAt_degree 2 ⟨by omega, le_rfl⟩).trans (s2DepthTwo_Dcum_two h2 hq)
  rw [hres]
  exact s2Mu3GradedRes_coeff_zero_ne_zero_of_exact h2 hq hg' (by omega)

/-! ## Part 4 — non-vacuity tooth -/

/-- **tooth (the law fires)**: the constant `1` has exact μ₃ grade `0` and degree `0 < 4`, so
its `y⁰`-coefficient is nonzero.  `Φ₂` itself cannot serve here (unlike μ₂'s frame key `Φ′`,
degree `2 < 4`): `deg Φ₂ = 4` fails the very fence stated in terms of `deg Φ₂`. -/
theorem tooth_mu3_scalar_fires :
    (s2Mu3GradedRes h2 hq 0 (1 : Polynomial O)).coeff 0 ≠ 0 := by
  refine s2Mu3GradedRes_coeff_zero_ne_zero_of_exact h2 hq ?_
    (by norm_num [Polynomial.natDegree_one])
  unfold S2Mu3ExactGrade
  rw [Uniformity.Density.Tower.C132nv5.s2Hgt₃_one_eq_zero]
  norm_num

end S2

end Uniformity.Density.Tower.C132rp7

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp7.exists_mu3SlotOnGrade_of_exact
#print axioms Uniformity.Density.Tower.C132rp7.s2Mu3GradedRes_coeff_zero_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C132rp7.s2Mu3KeyChain_keyAt_two_natDegree
#print axioms Uniformity.Density.Tower.C132rp7.s2Mu3_graded_scalar_nonzero
#print axioms Uniformity.Density.Tower.C132rp7.s2Mu3_graded_scalar_nonzero_fills
#print axioms Uniformity.Density.Tower.C132rp7.tooth_mu3_scalar_fires

end AxCheck
