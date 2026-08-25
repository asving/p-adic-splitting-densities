/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp6

/-!
# Uniformity.ChapC.C130rp8 — S2-source plan nodes RP-7/RP-8

**S2-source plan nodes RP-7 + RP-8** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 rows
RP-7 "Prove `graded_scalar_nonzero` under the exact `< 4` fence" and RP-8 "Define total `R₃`,
prove constant-term nonzero for nonzero inputs, and compute key powers"), on RP-1's graded
residual (C130rp1), RP-5/RP-6's nonvanishing inputs (C130rp6: `exists_slotOnGrade_of_exact`,
`s2GradedRes_ne_zero_of_exact`), RP-4's product identities (C130rp4), and C.07/C130nv2's
endpoint/side API — the setup layer for the `normalized_mul` core (RP-9/RP-10).

## NODE RP-7 — the scalar nonvanishing under the `< 4` fence

The C130fg field (`FGMNSourceLaws.graded_scalar_nonzero`, published Thm 4.1 + Cor 4.9(1)):
at exact grade, BELOW the next-key degree `deg (keyAt 2) = Dcum 2 = 4`, the degree-zero
coefficient of the graded residual is nonzero.  **How the fence enters** (the row's "work it
out honestly" charge): the proof consumes the fence ONLY as `deg g < 2·deg Φ′` — the
`Φ′`-development of `g` stops at slot 1, so the one on-line slot supplied by RP-5's gate
witness sits at abscissa `s ≤ 1`, hence at `y`-power `⌊s/2⌋ = 0`, and its exact-height ϖ-read
is nonzero (C.23's `slotRes_ne_zero`).  No differently-shaped fence is needed: at S2 the two
readings coincide, `deg (keyAt 2) = e₂f₂·deg Φ′ = 2·deg Φ′ = 4`.  The fence is SHARP: at
degree exactly 4 the law fails (`tooth_scalar_fence_sharp` — `Φ′²` has exact grade 10 and
`R₁₀(Φ′²) = X`, so its scalar is `0`; U9 Q2's "the degree fence is ESSENTIAL" ruling,
machine-witnessed).  Landed as the numeric-fence worker
(`s2GradedRes_coeff_zero_ne_zero_of_exact`), the field-shaped headline against the concrete
chain (★ `s2_graded_scalar_nonzero`, fence spelled `(s2DepthTwoKeyChain h2 hq).keyAt 2`), and
the FD-0 pin (`s2_graded_scalar_nonzero_fills`) for ANY `FGMNSourceData` whose
`nextValue`/`gradedResidual` fields are the S2 operators — the fence numeral there is
DERIVED from the chain's own `keyAt_degree` law, not assumed.

## NODE RP-8 — the total normalized residual `s2NormRes` (published Def 3.15)

Published Definition 3.15 (print-read verbatim in
`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §3): for nonzero `g` with `α = μ(g)`,
`R_r(g) := R_{r,α}(g)/y^{j₀}` where `j₀ = ⌊s(g)/e_r⌋`, and `R_r(0) = 0`.  The S2 realization:

* **the input's own exact grade** is extracted totally by `s2GradeOf g := (dvSupp … g 5 2).toNat`
  — for `g ≠ 0` this IS the unique exact grade (`S2ExactGrade_s2GradeOf`,
  `s2GradeOf_eq_of_exact`; RP-0's existence/uniqueness), so `s2GradedRes (s2GradeOf g) g` is
  exactly Def 3.15's operand `R_{r,α}(g)` at `α = μ(g)`;
* ★ **`s2NormRes g`** strips the minimal `y`-power: `divX`-iterated
  `natTrailingDegree (s2GradedRes (s2GradeOf g) g)` times.  **The strip pin**
  (`s2GradedRes_natTrailingDegree_eq`) certifies this is Def 3.15's strip amount, not a
  convenient variant: at exact grade the trailing degree IS `dvSideMin g / 2 = ⌊s(g)/e₂⌋` —
  every on-line slot reads nonzero at its exact height (`s2GradedCoeff_ne_zero_of_slotOnGrade`,
  the shared RP-7 core) and every abscissa left of the side's left endpoint is off-line, so
  the lowest nonzero `y`-power is the left endpoint's.
* **junk totality**: the only input with no exact grade is `0` (RP-0's `S2ExactGrade_exists`),
  and there `s2NormRes 0 = 0` — which is not junk but published Def 3.15's OWN clause
  `R_r(0) = 0` (`s2NormRes_zero`, `s2NormRes_eq_zero_iff`).

The RP-8 laws:

* ★ **constant-term nonzero** (`s2NormRes_coeff_zero_ne_zero`, the published Cor 4.9(3)
  genre): `g ≠ 0 → (s2NormRes g).coeff 0 ≠ 0` — RP-6's `s2GradedRes_ne_zero_of_exact` plus
  the strip (the stripped constant term is the trailing coefficient).
* **reconstruction** (`s2NormRes_mul_X_pow_of_exact`, Def 3.15's display read backwards,
  RP-9's consumable): `R_{β}(g) = R₃(g)·y^{j₀}` at the exact grade — the shape from which
  RP-9/RP-10 will derive that `y`-orders add and the twist is absorbed (U14 §7).
* **the degree law** (`s2NormRes_natDegree_of_exact`, published Cor 4.9(3)'s
  `deg = (s′−s)/e`): `natDegree (s2NormRes g) = (dvSideMax g − dvSideMin g)/2` — it falls
  out of the reconstruction plus the two endpoint pins (`s2GradedRes_natDegree_eq`,
  `s2GradedRes_natTrailingDegree_eq`).
* ★ **key powers** (`s2NormRes_key_pow`, published eq (11) at all `k`, via RP-4's product
  identities): `R_{5k}(Φ′^k) = y^{⌊k/2⌋}` (`s2GradedRes_key_pow`, by induction through RP-4's
  `s2GradedRes_mul_of_exact` — the carry twist `y^{k%2}` composes the floor), hence
  `s2NormRes (Φ′^k) = 1`; in particular `s2NormRes Φ′ = 1` (`s2NormRes_key`) — the
  `Rres_keyAt`/`carried_key_residual` GENRE (A-C.11's `Rres (keyAt r) = 1`), realized at the
  DEVELOPMENT key `Φ′ = keyAt 1` (FGMN's `φ₂`), and `s2NormRes 1 = 1`.
* **twist absorption, witnessed** (`tooth_normalized_mul_absorbs`): on the odd×odd pair
  `(Φ′, Φ′)` — the very pair whose PLAIN graded product law is machine-refuted
  (`C130rp2.tooth_graded_mul_plain_shape_refuted`) — the NORMALIZED law holds on the nose:
  `R₃(Φ′²) = 1 = R₃(Φ′)·R₃(Φ′)`.  The general `normalized_mul` is RP-9/RP-10, not here.

## What this node does NOT claim (honesty scope)

* No `normalized_mul` (published Cor 4.12(3), RP-9/RP-10): only its single-pair tooth above.
  No `y`-order addition law (RP-9's row).
* No `carried_key_residual`/`Rres_keyAt` FIELD instance: the literal S2 field is about
  `keyAt 2 = composedKey (s2Tower …)` (C130s2's "Φ₂", FGMN's `φ₃`, degree 4) and is KP-6's
  row.  `s2NormRes Φ′ = 1` is the same genre at the development key `keyAt 1`, per eq (11).
* No `FGMNSourceData`/`FGMNSourceLaws` instance (FD-0); the two `_fills`/field-shape
  statements are conditional pins/shape checks only.
* The ϖ-read ↔ `ε(α)·R(a)(z)` evaluation dictionary stays on C.22/C.25's recorded
  faithfulness boundary, inherited through RP-1, not re-derived.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2GradeOf` (the total grade extraction), `s2NormRes` (the Def 3.15 realization — the strip
is by trailing degree, certified equal to `⌊s(g)/e₂⌋` by `s2GradedRes_natTrailingDegree_eq`),
`s2_graded_scalar_nonzero` (+ worker/fills), the two endpoint pins, and the degree law.

**DEPENDS.** C130rp6 (`exists_slotOnGrade_of_exact`, `s2GradedRes_ne_zero_of_exact`) ·
C130rp4 (`s2GradedRes_mul_of_exact`, `tooth_conv_low`) · C130rp2
(`s2_twistRead_eq_slotRes`, `s2SlotOnGrade_iff_dvOnSide`, `tooth_gradedRes_X`) · C130rp1
(`s2GradedRes`/`s2GradedCoeff` + master law + `s2GradedCoeff_slot` + `s2SlotOnGrade_iff` +
`s2SlotOnGrade_parity` + zero laws + `twistRead_zero_one` + teeth) · C130rp0
(`S2ExactGrade` + normal forms + `S2ExactGrade_mul`/`_exists`/`_unique`/`_not_zero`, grade
teeth) · C130fg (`FGMNSourceData`/field shapes, for the pins) · C130s2 (`s2DepthTwo`,
`s2DepthTwoKeyChain`, `s2DepthTwo_Dcum_two`) · C130s6 (`s2Hgt₂_one`,
`dvSupp_ne_top_of_ne_zero`) · C130nv2 (`dev_zero_pin`, `dvOnSide_dvSideMin`,
`dvSideMin_le_of_dvOnSide`, `mem_dvSideSet_of_dvOnSide`, `dvOnSide_of_mem_dvSideSet`) ·
C.07 (`DvOnSide`, `dvSideSet`, `dvSideMin`, `dvSideMax`) · C.23
(`KeyFrame.slotRes_ne_zero`) · C.06 (`dvHgt`, `dvSupp`) · C127
(`KeyFrame.stageHeight_zero`) · B.03/B.04 (`degree_dev_lt`, `dev_eq_zero_of_lt`) ·
C35b/C.97 (`key_eq`, `s2Key_deg`, `s2Key_natDegree`, `sh_C`, `e1_eq`, `f1_eq`, `s2Frame`,
`s2Frame_pin`) · mathlib (`Polynomial.divX`/`coeff_divX`, the `natTrailingDegree` bank,
`coeff_mul_X_pow'`, `natDegree_mul`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp8

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C130rp4
open Uniformity.Density.Tower.C130rp6

/-! ## Part 0 — generic `divX`-iterate strip toolkit (any semiring)

The minimal-`y`-power strip is `Polynomial.divX` iterated: total, with a one-line
coefficient law.  Nothing here is S2-specific. -/

section Generic

variable {R : Type*} [Semiring R]

/-- **the iterated-`divX` coefficient law**: stripping `k` low coefficients shifts every
read by `k`. -/
theorem coeff_divX_iterate (k : ℕ) (p : Polynomial R) (n : ℕ) :
    (Polynomial.divX^[k] p).coeff n = p.coeff (n + k) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih p.divX, Polynomial.coeff_divX, Nat.add_assoc]

/-- **the strip reconstruction**: stripping at most the trailing degree loses nothing —
`(divX^[k] p)·X^k = p` for `k ≤ natTrailingDegree p` (the coefficients below `k` were `0`). -/
theorem divX_iterate_mul_X_pow {p : Polynomial R} {k : ℕ} (hk : k ≤ p.natTrailingDegree) :
    Polynomial.divX^[k] p * Polynomial.X ^ k = p := by
  ext n
  rw [Polynomial.coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_divX_iterate, Nat.sub_add_cancel h]
  · exact (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      (lt_of_lt_of_le (not_le.mp h) hk)).symm

/-- the full strip of a monomial is `1`: `divX^[n] (X^n) = 1`. -/
theorem divX_iterate_X_pow (n : ℕ) :
    Polynomial.divX^[n] ((Polynomial.X : Polynomial R) ^ n) = 1 := by
  ext t
  rw [coeff_divX_iterate, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  by_cases ht : t = 0
  · subst ht
    simp
  · rw [if_neg (by omega), if_neg ht]

end Generic

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — private copies (the private-copy pattern) -/

/-- private copy of the S2 key-degree numeral: `deg Φ′ = 2`. -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- private copy of RP-4/RP-6's short-digit degree bound: S2 development digits have
`natDegree < 2` (B.03 against the degree-2 key). -/
private theorem natDegree_dev_lt_two (f : Polynomial O) (j : ℕ) :
    (dev (s2Frame h2 hq).key f j).natDegree < 2 := by
  rcases eq_or_ne (dev (s2Frame h2 hq).key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    omega
  · have h := Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos f j)
    have hk := key_natDegree_two h2 hq
    omega

/-- private copy of RP-1's `one_mod_key`: `1 %ₘ Φ′ = 1`. -/
private theorem one_mod_key : (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_one, key_eq h2 hq, s2Key_deg]; norm_num)

/-! ## Part 2 — the on/off-line coefficient core

The shared engine of RP-7 and both RP-8 pins: an ON-line slot always reads a NONZERO
coefficient at its `y`-power `⌊s/2⌋` (the gate pins the exact height, and an attained-height
ϖ-read never vanishes — C.23), and an OFF-line abscissa always reads `0`. -/

/-- ★ **the on-line read is nonzero**: `S2SlotOnGrade β g s → Rgc_β(g)(s/2) ≠ 0` — the gate
gives the slot's exact height (RP-1's `s2SlotOnGrade_iff`), the slot IS read at that height
(`s2GradedCoeff_slot`), the S2 twist letter is invisible (`s2_twistRead_eq_slotRes`), and an
attained-height slot read of a short digit never vanishes (C.23's `slotRes_ne_zero`).
The coefficientwise form of RP-5's `s2GradedRes_ne_zero_of_exact`. -/
theorem s2GradedCoeff_ne_zero_of_slotOnGrade {β s : ℕ} {g : Polynomial O}
    (hgate : S2SlotOnGrade h2 hq β g s) :
    s2GradedCoeff h2 hq β g (s / 2) ≠ 0 := by
  obtain ⟨m, hm, hline⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  rw [s2GradedCoeff_slot h2 hq hgate, show (β - 5 * s) / 2 = m from by omega,
    s2_twistRead_eq_slotRes h2 hq]
  refine (s2Frame h2 hq).slotRes_ne_zero h2 1 (s2Frame_pin h2 hq) ?_ hm
  have h := natDegree_dev_lt_two h2 hq g s
  simpa [e1_eq h2 hq, f1_eq h2 hq] using h

/-- **the off-line read is zero**: the general-`t` gate-failure form of RP-1's vanishing
laws (`if_neg` on the definition). -/
theorem s2GradedCoeff_eq_zero_of_not_slotOnGrade {β t : ℕ} {g : Polynomial O}
    (h : ¬ S2SlotOnGrade h2 hq β g (β % 2 + 2 * t)) :
    s2GradedCoeff h2 hq β g t = 0 := by
  unfold s2GradedCoeff
  rw [if_neg h]

/-! ## Part 3 — ★ NODE RP-7: `graded_scalar_nonzero` under the exact `< 4` fence

Published Thm 4.1 + Cor 4.9(1) (the C130fg field's cited locus).  The fence enters ONLY as
`deg g < 2·deg Φ′ = 4`: the development stops at slot 1, so RP-5's gate witness sits at
abscissa `s ≤ 1`, i.e. at `y`-power `0`. -/

/-- **the RP-7 worker (numeric fence)**: at exact grade with `deg g < 4`, the scalar (the
`y⁰`-coefficient) of the graded residual is nonzero.  The gate witness's abscissa is `≤ 1`
(slots `≥ 2` have zero digit, hence `⊤` height, hence sit on no line), so it is read at
`y`-power `0` and reads nonzero by the Part-2 core. -/
theorem s2GradedRes_coeff_zero_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hdeg : g.natDegree < 4) :
    (s2GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_slotOnGrade_of_exact h2 hq hg
  have hs1 : s ≤ 1 := by
    by_contra hs
    obtain ⟨m, hm, -⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
    have hdev : dev (s2Frame h2 hq).key g s = 0 :=
      dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos g s
        (by rw [key_natDegree_two h2 hq]; omega)
    have htop : dvHgt (s2Frame h2 hq) g s = ⊤ := by
      rw [dvHgt, hdev]
      exact (s2Frame h2 hq).stageHeight_zero
    rw [htop] at hm
    exact WithTop.top_ne_coe hm
  have h := s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq hgate
  rw [show s / 2 = 0 from by omega] at h
  rw [s2GradedRes_coeff]
  exact h

/-- the concrete chain's next-key degree numeral: `deg (keyAt 2) = Dcum 2 = 4` (through the
chain's OWN `keyAt_degree` law — the fence numeral is derived, not chosen). -/
theorem s2KeyChain_keyAt_two_natDegree :
    ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree = 4 :=
  ((s2DepthTwoKeyChain h2 hq).keyAt_degree 2 ⟨by omega, le_rfl⟩).trans
    (s2DepthTwo_Dcum_two h2 hq)

/-- ★ **NODE RP-7 — the S2 `graded_scalar_nonzero`** (published Thm 4.1 + Cor 4.9(1); the
C130fg `FGMNSourceLaws.graded_scalar_nonzero` field shape VERBATIM at the S2 operators, with
the fence spelled against the concrete chain `s2DepthTwoKeyChain`): at exact grade below the
next-key degree, the scalar of the graded residual is nonzero.  The `g ≠ 0` premise is the
field's (redundant at S2: exact grade already forces it, RP-0). -/
theorem s2_graded_scalar_nonzero :
    ∀ β (g : Polynomial O),
      S2ExactGrade h2 hq β g →
      g.natDegree < ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree →
      g ≠ 0 →
      (s2GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  intro β g hg hdeg _
  rw [s2KeyChain_keyAt_two_natDegree h2 hq] at hdeg
  exact s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hg hdeg

/-- **the FD-0 pin**: if `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` reads
`nextValue := s2Hgt₂` and `gradedResidual := s2GradedRes`, then the
`FGMNSourceLaws.graded_scalar_nonzero` field for `S` holds — byte-identical binder shape
(the fence numeral `4` comes out of `K`'s own `keyAt_degree` law at the live stage 2). -/
theorem s2_graded_scalar_nonzero_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5)
    (hval : S.nextValue = s2Hgt₂ h2 hq)
    (hres : S.gradedResidual = s2GradedRes h2 hq) :
    ∀ β (g : Polynomial O),
      S.ExactGrade β g → g.natDegree < (K.keyAt 2).natDegree → g ≠ 0 →
        (S.gradedResidual β g).coeff 0 ≠ 0 := by
  intro β g hg hdeg _
  have hg' : S2ExactGrade h2 hq β g := by
    have hx : S.nextValue g = (β : WithTop ℤ) := hg
    rw [hval] at hx
    exact hx
  have hk := (K.keyAt_degree 2 ⟨by omega, le_rfl⟩).trans (s2DepthTwo_Dcum_two h2 hq)
  rw [hres]
  exact s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hg' (by omega)

/-- **tooth (the law fires)**: the key `Φ′` (degree `2 < 4`, exact grade `5`) has nonzero
scalar — consistent with RP-1's landed `R₅(Φ′) = 1`. -/
theorem tooth_scalar_fires :
    (s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O)).coeff 0 ≠ 0 :=
  s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq (tooth_key h2 hq)
    (by rw [key_natDegree_two h2 hq]; omega)

/-- `Φ′²` has degree exactly `4` — the first degree the fence excludes. -/
theorem tooth_key_sq_natDegree :
    (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key).natDegree = 4 := by
  rw [Polynomial.natDegree_mul (s2Frame h2 hq).hmonic.ne_zero (s2Frame h2 hq).hmonic.ne_zero,
    key_natDegree_two h2 hq]

/-- **tooth (the fence is SHARP)**: at degree exactly `4` the scalar law FAILS — `Φ′²` is
nonzero, at exact grade `10` (RP-0's tooth), yet its scalar is `0` (`R₁₀(Φ′²) = X`; RP-4's
`tooth_conv_low`).  U9 Q2's "the degree fence is ESSENTIAL" ruling, machine-witnessed. -/
theorem tooth_scalar_fence_sharp :
    (s2GradedRes h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)).coeff 0 = 0 := by
  rw [s2GradedRes_coeff]
  exact tooth_conv_low h2 hq

/-! ## Part 4 — the total grade extraction `s2GradeOf`

Def 3.15 normalizes "at `α = μ(g)`" — the input's OWN exact grade.  RP-0 gives existence
(nonzero inputs) and uniqueness; `ENat.toNat` totalizes the read (junk `0` at `g = 0`,
where no law reads it — `s2NormRes 0 = 0` holds for every β anyway). -/

/-- **the total S2 grade read**: `s2GradeOf g` is the cleared exact grade `μ₂(g)` as a
natural number (`ℕ∞`-untop of the corpus support; junk `0` at `g = 0`). -/
noncomputable def s2GradeOf (g : Polynomial O) : ℕ :=
  (dvSupp (s2Frame h2 hq) g 5 2).toNat

/-- for nonzero `g`, `s2GradeOf g` IS an exact grade of `g` (RP-0's grade existence, made
canonical). -/
theorem S2ExactGrade_s2GradeOf {g : Polynomial O} (hg : g ≠ 0) :
    S2ExactGrade h2 hq (s2GradeOf h2 hq g) g :=
  (S2ExactGrade_iff_dvSupp h2 hq).mpr
    (ENat.coe_toNat (dvSupp_ne_top_of_ne_zero (s2Frame h2 hq) 5 2 hg)).symm

/-- `s2GradeOf` agrees with EVERY exact-grade witness (RP-0's uniqueness, in extraction
form — the pin every `s2NormRes` law rides on). -/
theorem s2GradeOf_eq_of_exact {β : ℕ} {g : Polynomial O} (hg : S2ExactGrade h2 hq β g) :
    s2GradeOf h2 hq g = β := by
  unfold s2GradeOf
  rw [(S2ExactGrade_iff_dvSupp h2 hq).mp hg]
  exact ENat.toNat_coe β

/-! ## Part 5 — ★ NODE RP-8: the total normalized residual `s2NormRes`

Published Def 3.15: `R₃(g) = R_{3,α}(g)/y^{j₀}`, `α = μ(g)`, `j₀ = ⌊s(g)/e₂⌋`; `R₃(0) = 0`.
The strip is by the trailing degree — certified equal to `⌊s(g)/e₂⌋` at Part 7's strip pin. -/

/-- ★ **NODE RP-8 — the total normalized S2 residual** `R₃(g)` (published Def 3.15 at the S2
numerals): strip the minimal `y`-power from the graded residual at the input's own exact
grade.  Total in `g`; the zero polynomial lands on Def 3.15's own `R₃(0) = 0` clause. -/
noncomputable def s2NormRes (g : Polynomial O) : Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  Polynomial.divX^[(s2GradedRes h2 hq (s2GradeOf h2 hq g) g).natTrailingDegree]
    (s2GradedRes h2 hq (s2GradeOf h2 hq g) g)

/-- shape pin: the operator has EXACTLY the abstract `FGMNSourceData.normalizedResidual`
field shape at `r = 2` (C130fg). -/
noncomputable example : Polynomial O → Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  s2NormRes h2 hq

/-- `s2NormRes` read at a caller-supplied exact-grade witness (the consumable form: the
grade argument is proof-independent by RP-0's uniqueness). -/
theorem s2NormRes_of_exact {β : ℕ} {g : Polynomial O} (hg : S2ExactGrade h2 hq β g) :
    s2NormRes h2 hq g
      = Polynomial.divX^[(s2GradedRes h2 hq β g).natTrailingDegree]
          (s2GradedRes h2 hq β g) := by
  unfold s2NormRes
  rw [s2GradeOf_eq_of_exact h2 hq hg]

/-- **the master coefficient law** for `s2NormRes` (total form): every coefficient is a
shifted read of the graded residual at the extracted grade. -/
theorem s2NormRes_coeff (g : Polynomial O) (t : ℕ) :
    (s2NormRes h2 hq g).coeff t
      = (s2GradedRes h2 hq (s2GradeOf h2 hq g) g).coeff
          (t + (s2GradedRes h2 hq (s2GradeOf h2 hq g) g).natTrailingDegree) := by
  unfold s2NormRes
  exact coeff_divX_iterate _ _ _

/-- the master coefficient law at a caller-supplied exact grade. -/
theorem s2NormRes_coeff_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (t : ℕ) :
    (s2NormRes h2 hq g).coeff t
      = (s2GradedRes h2 hq β g).coeff (t + (s2GradedRes h2 hq β g).natTrailingDegree) := by
  rw [s2NormRes_of_exact h2 hq hg]
  exact coeff_divX_iterate _ _ _

/-- **published Def 3.15's zero clause**: `R₃(0) = 0`. -/
theorem s2NormRes_zero : s2NormRes h2 hq (0 : Polynomial O) = 0 := by
  unfold s2NormRes
  rw [s2GradedRes_zero h2 hq]
  simp

/-- ★ **the reconstruction** (published Def 3.15's display `R_{r,α}(g) = y^{j₀}·R_r(g)`,
read backwards — RP-9's consumable): at the exact grade, the graded residual is the
normalized residual times the stripped `y`-power. -/
theorem s2NormRes_mul_X_pow_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) :
    s2NormRes h2 hq g * Polynomial.X ^ (s2GradedRes h2 hq β g).natTrailingDegree
      = s2GradedRes h2 hq β g := by
  rw [s2NormRes_of_exact h2 hq hg]
  exact divX_iterate_mul_X_pow le_rfl

/-! ## Part 6 — ★ the constant-term nonvanishing (published Cor 4.9(3)'s shape) -/

/-- ★ **NODE RP-8 — constant term NONZERO for nonzero inputs** (published Cor 4.9(3)'s
genre): `g ≠ 0 → (R₃(g))(0) ≠ 0` — the stripped constant term is the trailing coefficient
of the graded residual, which is nonzero because the graded residual itself is (RP-5's
`s2GradedRes_ne_zero_of_exact` at the extracted exact grade). -/
theorem s2NormRes_coeff_zero_ne_zero {g : Polynomial O} (hg : g ≠ 0) :
    (s2NormRes h2 hq g).coeff 0 ≠ 0 := by
  have hne : s2GradedRes h2 hq (s2GradeOf h2 hq g) g ≠ 0 :=
    s2GradedRes_ne_zero_of_exact h2 hq (S2ExactGrade_s2GradeOf h2 hq hg)
  rw [s2NormRes_coeff, zero_add]
  exact fun h0 => hne (Polynomial.coeff_natTrailingDegree_eq_zero.mp h0)

/-- the normalized residual of a nonzero input is nonzero (the polynomial-level corollary). -/
theorem s2NormRes_ne_zero {g : Polynomial O} (hg : g ≠ 0) : s2NormRes h2 hq g ≠ 0 :=
  fun h0 => s2NormRes_coeff_zero_ne_zero h2 hq hg (by rw [h0, Polynomial.coeff_zero])

/-- **the vanishing locus is exactly the zero polynomial** (Def 3.15's zero clause is
sharp): `R₃(g) = 0 ↔ g = 0`. -/
theorem s2NormRes_eq_zero_iff {g : Polynomial O} : s2NormRes h2 hq g = 0 ↔ g = 0 := by
  constructor
  · intro h0
    by_contra hg
    exact s2NormRes_ne_zero h2 hq hg h0
  · rintro rfl
    exact s2NormRes_zero h2 hq

/-! ## Part 7 — the endpoint pins and the degree law (published Cor 4.9(3))

The strip pin certifies that `s2NormRes`'s trailing-degree strip IS published Def 3.15's
`j₀ = ⌊s(g)/e₂⌋` — the left endpoint `s(g)` of the side is C.07's `dvSideMin`.  The right
endpoint gives the graded degree, and their difference the Cor 4.9(3) degree law. -/

/-- ★ **the strip pin** (Def 3.15's `j₀ = ⌊s(g)/e₂⌋`, certified): at the exact grade the
trailing degree of the graded residual is the side's left endpoint over `e₂ = 2` — the
left-endpoint slot is on-line and reads nonzero (Part 2), and every abscissa strictly left
of it is off-line (C.07's minimality). -/
theorem s2GradedRes_natTrailingDegree_eq {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g)
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty) :
    (s2GradedRes h2 hq β g).natTrailingDegree
      = dvSideMin (s2Frame h2 hq) g 5 2 hng / 2 := by
  have hon : DvOnSide (s2Frame h2 hq) g 5 2 (dvSideMin (s2Frame h2 hq) g 5 2 hng) :=
    dvOnSide_dvSideMin (s2Frame h2 hq) g 5 2 hng
  have hgate : S2SlotOnGrade h2 hq β g (dvSideMin (s2Frame h2 hq) g 5 2 hng) :=
    (s2SlotOnGrade_iff_dvOnSide h2 hq hg).mpr hon
  have hpar := s2SlotOnGrade_parity h2 hq hgate
  refine le_antisymm ?_ ?_
  · refine Polynomial.natTrailingDegree_le_of_ne_zero ?_
    rw [s2GradedRes_coeff]
    exact s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq hgate
  · refine Polynomial.le_natTrailingDegree (s2GradedRes_ne_zero_of_exact h2 hq hg)
      fun t ht => ?_
    rw [s2GradedRes_coeff]
    refine s2GradedCoeff_eq_zero_of_not_slotOnGrade h2 hq fun hgt => ?_
    have hside := (s2SlotOnGrade_iff_dvOnSide h2 hq hg).mp hgt
    have hle := dvSideMin_le_of_dvOnSide hng hside
    omega

/-- **the right-endpoint pin**: the degree of the graded residual is the side's right
endpoint over `e₂ = 2` (symmetric to the strip pin, against C.07's `dvSideMax`). -/
theorem s2GradedRes_natDegree_eq {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g)
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty) :
    (s2GradedRes h2 hq β g).natDegree = dvSideMax (s2Frame h2 hq) g 5 2 hng / 2 := by
  have hon : DvOnSide (s2Frame h2 hq) g 5 2 (dvSideMax (s2Frame h2 hq) g 5 2 hng) :=
    dvOnSide_of_mem_dvSideSet (Finset.max'_mem _ hng)
  have hgate : S2SlotOnGrade h2 hq β g (dvSideMax (s2Frame h2 hq) g 5 2 hng) :=
    (s2SlotOnGrade_iff_dvOnSide h2 hq hg).mpr hon
  have hpar := s2SlotOnGrade_parity h2 hq hgate
  refine le_antisymm ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [s2GradedRes_coeff]
    refine s2GradedCoeff_eq_zero_of_not_slotOnGrade h2 hq fun hgt => ?_
    have hside := (s2SlotOnGrade_iff_dvOnSide h2 hq hg).mp hgt
    have hle : β % 2 + 2 * N ≤ dvSideMax (s2Frame h2 hq) g 5 2 hng :=
      Finset.le_max' _ _ (mem_dvSideSet_of_dvOnSide hside)
    omega
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [s2GradedRes_coeff]
    exact s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq hgate

/-- the degree bookkeeping of the strip: `deg R₃(g) + j₀ = deg R_{3,β}(g)` at the exact
grade (from the reconstruction; the `y`-power is degree-exact over a field). -/
theorem s2NormRes_natDegree_add_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) :
    (s2NormRes h2 hq g).natDegree + (s2GradedRes h2 hq β g).natTrailingDegree
      = (s2GradedRes h2 hq β g).natDegree := by
  have hnn : s2NormRes h2 hq g ≠ 0 :=
    s2NormRes_ne_zero h2 hq (S2ExactGrade_not_zero h2 hq hg)
  calc (s2NormRes h2 hq g).natDegree + (s2GradedRes h2 hq β g).natTrailingDegree
      = (s2NormRes h2 hq g
          * Polynomial.X ^ (s2GradedRes h2 hq β g).natTrailingDegree).natDegree := by
        rw [Polynomial.natDegree_mul hnn (pow_ne_zero _ Polynomial.X_ne_zero),
          Polynomial.natDegree_X_pow]
    _ = (s2GradedRes h2 hq β g).natDegree := by
        rw [s2NormRes_mul_X_pow_of_exact h2 hq hg]

/-- ★ **the degree law** (published Cor 4.9(3)'s `deg R_r(g) = (s′ − s)/e_r`): the degree of
the normalized residual is the side's horizontal length over `e₂ = 2`. -/
theorem s2NormRes_natDegree_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g)
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty) :
    (s2NormRes h2 hq g).natDegree
      = (dvSideMax (s2Frame h2 hq) g 5 2 hng - dvSideMin (s2Frame h2 hq) g 5 2 hng) / 2 := by
  have hadd := s2NormRes_natDegree_add_of_exact h2 hq hg
  have hntd := s2GradedRes_natTrailingDegree_eq h2 hq hg hng
  have hnd := s2GradedRes_natDegree_eq h2 hq hg hng
  have honmin : DvOnSide (s2Frame h2 hq) g 5 2 (dvSideMin (s2Frame h2 hq) g 5 2 hng) :=
    dvOnSide_dvSideMin (s2Frame h2 hq) g 5 2 hng
  have honmax : DvOnSide (s2Frame h2 hq) g 5 2 (dvSideMax (s2Frame h2 hq) g 5 2 hng) :=
    dvOnSide_of_mem_dvSideSet (Finset.max'_mem _ hng)
  have hparmin := s2SlotOnGrade_parity h2 hq
    ((s2SlotOnGrade_iff_dvOnSide h2 hq hg).mpr honmin)
  have hparmax := s2SlotOnGrade_parity h2 hq
    ((s2SlotOnGrade_iff_dvOnSide h2 hq hg).mpr honmax)
  have hle : dvSideMin (s2Frame h2 hq) g 5 2 hng ≤ dvSideMax (s2Frame h2 hq) g 5 2 hng :=
    Finset.min'_le _ _ (Finset.max'_mem _ hng)
  omega

/-! ## Part 8 — ★ the key powers (published eq (11), via RP-4's product identities)

`R_{5k}(Φ′^k) = y^{⌊k/2⌋}` by induction through RP-4's twisted product law (the carry
`y^{k%2}` composes the floor), hence `R₃(Φ′^k) = 1` — the `Rres_keyAt` genre at the
development key `Φ′ = keyAt 1`. -/

/-- **tooth (eq (11), `s = 0`)**: `R_0(1) = 1` — the graded residual of `1` at its exact
grade `0` (the induction's base). -/
theorem tooth_gradedRes_one : s2GradedRes h2 hq 0 (1 : Polynomial O) = 1 := by
  have hone : dev (s2Frame h2 hq).key (1 : Polynomial O) 0 = 1 := by
    rw [dev_zero_pin]
    exact one_mod_key h2 hq
  have hdv : dvHgt (s2Frame h2 hq) (1 : Polynomial O) 0 = 0 := by
    rw [dvHgt, hone, show (1 : Polynomial O) = Polynomial.C 1 from (map_one _).symm,
      sh_C h2 hq]
    simp
  have hgate : S2SlotOnGrade h2 hq 0 (1 : Polynomial O) 0 :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨0, hdv, by norm_num⟩
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff]
  match t with
  | 0 =>
    rw [Polynomial.coeff_one_zero]
    unfold s2GradedCoeff
    rw [show 0 % 2 + 2 * 0 = 0 from by norm_num, if_pos hgate,
      show (0 - 5 * 0) / 2 = 0 from by norm_num, hone]
    exact twistRead_zero_one h2 hq
  | (t + 1) =>
    rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega), Polynomial.coeff_one]
    simp

/-- `1` sits at exact grade `0` (`μ₂(1) = 0`, C130s6's `s2Hgt₂_one`). -/
theorem S2ExactGrade_one : S2ExactGrade h2 hq 0 (1 : Polynomial O) := by
  unfold S2ExactGrade
  rw [s2Hgt₂_one h2 hq]
  norm_cast

/-- **the key-power grades**: `μ₂(Φ′^k) = 5k` (RP-0's `S2ExactGrade_mul`, iterated from the
landed grade-5 tooth). -/
theorem S2ExactGrade_key_pow (k : ℕ) :
    S2ExactGrade h2 hq (5 * k) (((s2Frame h2 hq).key : Polynomial O) ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.mul_zero]
    exact S2ExactGrade_one h2 hq
  | succ k ih =>
    rw [show 5 * (k + 1) = 5 * k + 5 from by ring, pow_succ]
    exact S2ExactGrade_mul h2 hq ih (tooth_key h2 hq)

/-- ★ **the graded key powers** (published eq (11) at every `k`): `R_{5k}(Φ′^k) = y^{⌊k/2⌋}`
— by induction through RP-4's twisted product law `s2GradedRes_mul_of_exact`; the odd×odd
carry `y^{k%2}` is exactly what composes the floor (`⌊(k+1)/2⌋ = ⌊k/2⌋ + k%2`).  Extends
RP-1's landed teeth `R₅(Φ′) = 1`, `R₁₀(Φ′²) = X` to all `k`. -/
theorem s2GradedRes_key_pow (k : ℕ) :
    s2GradedRes h2 hq (5 * k) (((s2Frame h2 hq).key : Polynomial O) ^ k)
      = Polynomial.X ^ (k / 2) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.mul_zero, tooth_gradedRes_one h2 hq]
    norm_num
  | succ k ih =>
    have h := s2GradedRes_mul_of_exact h2 hq (S2ExactGrade_key_pow h2 hq k)
      (tooth_key h2 hq)
    rw [ih, tooth_gradedRes_key h2 hq, mul_one, show (5 : ℕ) % 2 = 1 from by norm_num,
      mul_one, show 5 * k % 2 = k % 2 from by omega, ← pow_add] at h
    rw [show 5 * (k + 1) = 5 * k + 5 from by ring, pow_succ, h]
    congr 1
    omega

/-- ★ **NODE RP-8 — the normalized key powers**: `R₃(Φ′^k) = 1` for EVERY `k` — the strip
removes the whole `y^{⌊k/2⌋}` (published eq (11) + Def 3.15). -/
theorem s2NormRes_key_pow (k : ℕ) :
    s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) ^ k) = 1 := by
  rw [s2NormRes_of_exact h2 hq (S2ExactGrade_key_pow h2 hq k), s2GradedRes_key_pow h2 hq k,
    Polynomial.natTrailingDegree_X_pow]
  exact divX_iterate_X_pow (k / 2)

/-- **`R₃(Φ′) = 1`** — the `Rres_keyAt`/`carried_key_residual` GENRE (A-C.11's
`Rres (keyAt r) = 1`; published eq (11)), realized at the development key `Φ′ = keyAt 1`.
The literal S2 `keyAt 2 = composedKey` field instance is KP-6's row, not claimed here. -/
theorem s2NormRes_key : s2NormRes h2 hq ((s2Frame h2 hq).key : Polynomial O) = 1 := by
  have h := s2NormRes_key_pow h2 hq 1
  rwa [pow_one] at h

/-- `R₃(1) = 1` (the `k = 0` instance). -/
theorem s2NormRes_one : s2NormRes h2 hq (1 : Polynomial O) = 1 := by
  have h := s2NormRes_key_pow h2 hq 0
  rwa [pow_zero] at h

/-- **tooth**: `R₃(Φ′²) = 1` — the normalization strips the LIVE `y`-power of the landed
`R₁₀(Φ′²) = X` (the `k = 2` instance, in RP-1's `Φ′·Φ′` spelling). -/
theorem tooth_normRes_key_sq :
    s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) = 1 := by
  have h := s2NormRes_key_pow h2 hq 2
  rwa [pow_two] at h

/-- **tooth (normalization absorbs the twist — U14 §7, witnessed)**: on the odd×odd pair
`(Φ′, Φ′)`, whose PLAIN graded product law is machine-refuted
(`C130rp2.tooth_graded_mul_plain_shape_refuted`: `R₁₀(Φ′²) = X ≠ 1 = R₅(Φ′)²`), the
NORMALIZED product law holds on the nose: `R₃(Φ′²) = R₃(Φ′)·R₃(Φ′)`.  The single-pair
witness of `normalized_mul` (published Cor 4.12(3)) — the general law is RP-9/RP-10. -/
theorem tooth_normalized_mul_absorbs :
    s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      = s2NormRes h2 hq ((s2Frame h2 hq).key : Polynomial O)
        * s2NormRes h2 hq ((s2Frame h2 hq).key : Polynomial O) := by
  rw [tooth_normRes_key_sq h2 hq, s2NormRes_key h2 hq, mul_one]

/-- **tooth (a non-key input)**: `R₃(x) = 1` — grade `2`, landed `R₂(x) = 1` (RP-3's tooth),
trailing degree `0`, so the strip is the identity. -/
theorem tooth_normRes_X : s2NormRes h2 hq (Polynomial.X : Polynomial O) = 1 := by
  rw [s2NormRes_of_exact h2 hq (tooth_X h2 hq), tooth_gradedRes_X h2 hq,
    Polynomial.natTrailingDegree_one]
  rfl

end S2

end Uniformity.Density.Tower.C130rp8

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp8.coeff_divX_iterate
#print axioms Uniformity.Density.Tower.C130rp8.divX_iterate_mul_X_pow
#print axioms Uniformity.Density.Tower.C130rp8.divX_iterate_X_pow
#print axioms Uniformity.Density.Tower.C130rp8.s2GradedCoeff_ne_zero_of_slotOnGrade
#print axioms Uniformity.Density.Tower.C130rp8.s2GradedCoeff_eq_zero_of_not_slotOnGrade
#print axioms Uniformity.Density.Tower.C130rp8.s2GradedRes_coeff_zero_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C130rp8.s2KeyChain_keyAt_two_natDegree
#print axioms Uniformity.Density.Tower.C130rp8.s2_graded_scalar_nonzero
#print axioms Uniformity.Density.Tower.C130rp8.s2_graded_scalar_nonzero_fills
#print axioms Uniformity.Density.Tower.C130rp8.tooth_scalar_fires
#print axioms Uniformity.Density.Tower.C130rp8.tooth_key_sq_natDegree
#print axioms Uniformity.Density.Tower.C130rp8.tooth_scalar_fence_sharp
#print axioms Uniformity.Density.Tower.C130rp8.s2GradeOf
#print axioms Uniformity.Density.Tower.C130rp8.S2ExactGrade_s2GradeOf
#print axioms Uniformity.Density.Tower.C130rp8.s2GradeOf_eq_of_exact
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_of_exact
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_coeff
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_coeff_of_exact
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_zero
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_mul_X_pow_of_exact
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_ne_zero
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_eq_zero_iff
#print axioms Uniformity.Density.Tower.C130rp8.s2GradedRes_natTrailingDegree_eq
#print axioms Uniformity.Density.Tower.C130rp8.s2GradedRes_natDegree_eq
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_natDegree_add_of_exact
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_natDegree_of_exact
#print axioms Uniformity.Density.Tower.C130rp8.tooth_gradedRes_one
#print axioms Uniformity.Density.Tower.C130rp8.S2ExactGrade_one
#print axioms Uniformity.Density.Tower.C130rp8.S2ExactGrade_key_pow
#print axioms Uniformity.Density.Tower.C130rp8.s2GradedRes_key_pow
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_key_pow
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_key
#print axioms Uniformity.Density.Tower.C130rp8.s2NormRes_one
#print axioms Uniformity.Density.Tower.C130rp8.tooth_normRes_key_sq
#print axioms Uniformity.Density.Tower.C130rp8.tooth_normalized_mul_absorbs
#print axioms Uniformity.Density.Tower.C130rp8.tooth_normRes_X

end AxCheck
