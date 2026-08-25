/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp1

/-!
# Uniformity.ChapC.C130rp2 — S2-source plan nodes RP-2(add)/RP-3 (CORE 1/4)

**S2-source plan nodes RP-2 (remainder: the graded ADD law) and RP-3 (graded product
endpoints, CORE 1/4 of `graded_mul`)** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6
rows RP-2/RP-3), on RP-1's landed graded residual `s2GradedRes` (C130rp1).

## RP-2 remainder — the graded ADD law (published Cor 4.12(1))

The zero law `graded_zero_of_above` landed at RP-1; this file lands the additive law, in two
strengths:

* ★ **the STRONG form** `s2GradedRes_add_of_le`: `R_β(g + h) = R_β(g) + R_β(h)` whenever both
  `g` and `h` have cleared value `≥ β` (exact OR above — `(β : ℕ∞) ≤ dvSupp`); no hypothesis
  on the sum.  Coefficientwise (`s2GradedCoeff_add`): at each grade-line slot both summands'
  heights clear the line (`le_dvHgt_of_le_dvSupp`), so each of the three gated reads is THE
  ϖ-read at the on-line height — a slot whose height sits strictly above the line reads `0`
  through the SAME formula (`twistRead_eq_zero_of_lt`), which is exactly why cancellation
  (the sum's gate failing while both summands' gates fire) is not a case split but an
  instance of ϖ-read additivity (`twistRead_add_of_le`, from B.22's `digAt_add` at the
  common valuation floor) plus `dev` additivity (B32a's `dev_add_of_monic`).
* ★ **the FIELD shape** `s2GradedRes_add` (C130fg's `graded_add` binder pattern verbatim at
  the S2 occurrence): exact + exact + exact-sum inputs.  The exact-sum hypothesis is carried
  for shape fidelity; the strong form shows it is not needed.

Teeth: `tooth_gradedRes_add_cancel` (the char-2 cancellation genre: `R₅(Φ′ + Φ′) = 1 + 1`),
`tooth_char_two` (`1 + 1 = 0` in `K₂` DERIVED from the operator laws alone: the zero law
prices `Φ′ + Φ′ = C 2 · Φ′` above grade 5, so the additive law forces `1 + 1 = 0` — the
machine check that the two laws cohere), and the NON-VACUOUS exact-sum instance
`tooth_gradedRes_add_field_shape` / `tooth_gradedRes_add_exact` at grade 10:
`R₁₀(Φ′² + 4x) = X + 1 = R₁₀(Φ′²) + R₁₀(4x)` — two grade-10 inputs whose line slots are
DISJOINT (abscissae 2 vs 0), so the sum stays at exact grade even in residue characteristic 2.

## RP-3 — graded product endpoints (CORE 1/4 of `graded_mul`)

At exact grades `β` (of `g`) and `β′` (of `z`), the chosen minimizers `jg = dvSideMin g`,
`jz = dvSideMin z` (NV-2's leftmost-minimizer ruling) are on-line slots of their own grade
lines, and NV-3's unique-lowest-convolution machinery puts `jg + jz` on the `(β + β′)`-line
of `g·z`.  This file proves the ENDPOINT-COEFFICIENT relation RP-4's convolution recursion
consumes:

* ★ `s2_twistRead_mul_modByMonic` — **the survival core at the residual-read level** (the
  ϖ-read of the surviving term IS the product of the ϖ-reads): for `a, b` of degree `≤ 1`
  with cleared-height floors `Ha ≤ dv(a)`, `Hb ≤ dv(b)`,
  `twistRead (Ha+Hb) ((a·b) %ₘ Φ′) = twistRead Ha a · twistRead Hb b`.  This is C130nv3's
  four-genre parity computation (even×even / mixed / odd×odd through the `x² ≡ 2` carry)
  redone at the DIGIT level: B.22's `digAt_eq`/`digAt_add` and C109's `digAt_congr` replace
  the height reads, and the carry case transfers the digit through
  `2·a₁b₁ = 2^(m+n+1)·(a₁/2^m)(b₁/2^n)`.
* ★ `dev_mul_endpoint_split` (generic) — the unique-lowest-term SPLIT exported from NV-3's
  internals: `dev (g·z) (jg+jz) = (dev g jg · dev z jz) %ₘ Φ′ + R` with EVERY other
  convolution term priced strictly above (`Hg + Hz + 1 ≤ dv(R)`), unconditionally (the
  survival hypothesis is only needed to READ the split, not to have it).
* ★ `s2_twistRead_dev_mul_endpoint` — the two combined through C131y's `twistRead_add_deep`
  (the read at height `Hg + Hz` cannot see `R`): the endpoint read of the product is the
  product of the endpoint reads.
* ★ **the headline** `s2GradedCoeff_mul_endpoint`:
  `Rgc_{β+β′}(g·z)((jg+jz)/2) = Rgc_β(g)(jg/2) · Rgc_{β′}(z)(jz/2)` — the graded coefficient
  of the product at the endpoint `y`-power is the product of the factors' endpoint
  coefficients.  The `y`-power arithmetic `(jg+jz)/2 = jg/2 + jz/2 + (β%2)·(β′%2)` carries
  the PARITY CARRY visibly (teeth below).

## ⚠ Recorded finding: the plain-product `graded_mul` field shape is REFUTED at RP-1's operator

`tooth_graded_mul_plain_shape_refuted` machine-checks
`R₁₀(Φ′·Φ′) ≠ R₅(Φ′) · R₅(Φ′)` (landed teeth: `X ≠ 1·1`).  So C130fg's `graded_mul` field
AS TYPED — `gradedResidual (β+β′) (g·h) = gradedResidual β g * gradedResidual β′ h` — is NOT
satisfiable by the RP-1 concrete operator: the grade-anchored line parameterization
(Def 3.12's `s₂(β) = β % 2` offset, RP-1's landed eq (11) teeth) makes the product law carry
the parity factor `y^{(β%2)·(β′%2)}` (both grades odd: the two `s₂ = 1` offsets merge into
one extra `y`).  The CORRECTED S2 target for RP-4/RP-6 is
`R_{β+β′}(g·h) = X^{(β%2)·(β′%2)} · R_β(g) · R_{β′}(h)`, whose endpoint instance is exactly
the headline here (`tooth_endpoint_carry`: `y`-power `1 = 0 + 0 + 1` at `(5,5)`).  Whether
published Cor 4.12(2)'s own wording anchors the operator per-polynomial (making the plain
form true THERE) is a cite-review question deliberately NOT adjudicated here; the finding is
about the C130fg field shape at the RP-1 operator, and it is machine-checked.

## What this file does NOT claim (honesty scope)

* No full product law (`graded_mul`'s polynomial identity): the convolution over NON-endpoint
  line slots is RP-4 (CORE 2/4); the inner residual product/twist normalization beyond the
  `f₁ = 1` monomial case is RP-5; assembly is RP-6.
* No exact-grade nonvanishing (RP-7), no normalization (RP-8), no
  `FGMNSourceData`/`FGMNSourceLaws` instance (FD-0).
* The ϖ-read ↔ `ε(α)·R(a)(z)` evaluation dictionary is consumed from C.22/C.25's recorded
  faithfulness boundary, not re-derived.
* The S2 read normal form (`s2_twistRead_eq_digAt`) and the trivial twist
  (`s2_stageLetter_eq_one`, from `|K₁| = 2`) are S2-frame facts, not claims about general
  frames — at `f₁ > 1` the twist and the slot window are genuinely non-trivial.

**Flagged for human review** (parent CLAUDE.md trust boundary — new general statements):
`twistRead_add_of_le`/`slotRes_add_of_le` (ϖ-read additivity at a common height floor),
`twistRead_eq_zero_of_lt`, and `dev_mul_endpoint_split` are asserted for ANY corpus frame
(the split under the same strict-admissibility hypotheses as NV-3's generic half); the S2
teeth regression-test the chain against hand computation.

**DEPENDS.** C130rp1 (`s2GradedRes`/`s2GradedCoeff` + master law + gates + teeth) · C130rp0
(`S2ExactGrade`/`S2AboveGrade` + normal forms + `S2ExactGrade_mul` + teeth) · C130nv3
(`s2_mul_modByMonic`, `s2_stageHeight_linear`, `s2_dvOnSide_mul_endpoint`, `s2_dvSupp_mul`,
`dvSideMin_le_natDegree`, teeth) · C130nv2 (`weight_read`, `dvOnSide_dvSideMin`,
`dvSideMin_le_of_dvOnSide`, `dvOnSide_endpoint_unique`, `exists_dvSideMin_height`,
`dvSupp_eq_of_dvOnSide`, `lt_line_dev_term`, `le_weight_stageHeight_sum`,
`succ_le_of_weight_succ_le`, `dev_zero_pin`, S2 gates) · C131y (`twistRead_add_deep`,
`dvSupp_le_term`, `dvHgt_add_min`) · C.06/C.07 (`dvHgt`, `dvSupp`, `DvOnSide`, `dvSideMin`) ·
C.34 (`dvSideSet_nonempty`) · C.21/C.22 (`slotRes`, `twistRead`) · C.19
(`stageLetter_ne_zero`) · C.15/C.17 (`slotIdx`, `twistExp`, `slotWindow`) · C.14a
(`KeyFrame.Pin`) · C.80 (`card_K₁`) · C.97 (`s2Frame`, `s2Frame_pin`, `s2StageFieldInst`,
`s2Key_natDegree`) · C35b (frame numerals, `sh_X`, `sh_C_pow`, `twistRead_one_X`,
`slotIdx_one`, `addVal_two_pow`, `s2Key_deg`) · C130s6 (`dvSupp` bank,
`min_dvSupp_le_dvSupp_add`, `s2Hgt₂` dictionary) · B.22 (`digAt_eq`, `digAt_add`) · C109
(`digAt_congr`) · B32a (`dev_add_of_monic`) · B35a (`dev_mul_pow`, `dev_mul_pow_of_lt`,
`dev_finsetSum`) · B.05 (`sum_dev_eq`) · B.03 (`degree_dev_lt`) · B83Kit
(`GateKit.gaussVal_C`) · C118a (`smul_top_pos`) · C.02 (`stageHeight_eq_inf`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv3 Uniformity.Density.Tower.C131y

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 1 — ℕ∞ floor extraction, and the slot floor from a cleared-support floor -/

/-- an even-side parity floor: `a ≤ 2x` forces `⌈a/2⌉ ≤ x` (the strict parity gap is free). -/
private theorem coe_le_of_le_two_smul {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) ≤ 2 • x) :
    (((a + 1) / 2 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hx
  rw [← hc] at h ⊢
  rw [show (2 : ℕ) • ((c : ℕ) : ℕ∞) = ((2 * c : ℕ) : ℕ∞) by rw [nsmul_eq_mul]; push_cast; ring]
    at h
  have hnat : a ≤ 2 * c := by exact_mod_cast h
  exact_mod_cast (by omega : (a + 1) / 2 ≤ c)

/-- an odd-side parity floor: `a ≤ 2x + 1` forces `⌊a/2⌋ ≤ x`. -/
private theorem coe_le_of_le_two_smul_add_one {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) ≤ 2 • x + 1) :
    ((a / 2 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hx
  rw [← hc] at h ⊢
  rw [show (2 : ℕ) • ((c : ℕ) : ℕ∞) + 1 = ((2 * c + 1 : ℕ) : ℕ∞) by
    rw [nsmul_eq_mul]; push_cast; ring] at h
  have hnat : a ≤ 2 * c + 1 := by exact_mod_cast h
  exact_mod_cast (by omega : a / 2 ≤ c)

/-- **the slot floor from a cleared-support floor**: if the whole cleared support sits at or
above `β` and slot `j` is a grade-`β` line abscissa (`ℓ·m + u·j = β`), then the slot's height
clears the on-line height `m`.  (The RP-2 per-slot input; also RP-4's.) -/
theorem le_dvHgt_of_le_dvSupp {F : KeyFrame O π} {f : Polynomial O} {u ℓ β m j : ℕ}
    (hℓ : 0 < ℓ) (hβ : (β : ℕ∞) ≤ dvSupp F f u ℓ) (hm : ℓ * m + u * j = β) :
    (m : ℕ∞) ≤ dvHgt F f j := by
  have hterm := C131y.dvSupp_le_term F f u hℓ j
  have h : (β : ℕ∞) ≤ ℓ • dvHgt F f j + (u * j : ℕ∞) := le_trans hβ hterm
  rcases eq_or_ne (dvHgt F f j) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc, weight_read] at h
  rw [← hc]
  have hnat : β ≤ ℓ * c + u * j := by exact_mod_cast h
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : ℓ * m ≤ ℓ * c) hℓ

/-! ## Part 2 — the ϖ-read additivity bank (RP-2's engine)

C.22's `twistRead` is `η^{−q(k)}·slotRes k`, and `slotRes k` is a window sum of B.21 digit
reads `digAt π q_t (A.coeff pos_t)` at the exact levels `e₁·q_t + pos_t·h = k`.  When BOTH
arguments have stage height `≥ k`, every consulted coefficient is `π^{q_t}`-divisible, so
B.22's `digAt_add` makes the whole read additive.  (C131y/C131ae's landed one-sided laws
`twistRead_add_deep`/`twistRead_add_eq_left_of_lt` are the `>` degenerations of this.) -/

/-- the window-position/digit-index arithmetic identity (private-copy pattern: C131y, C131ae,
C.21, C.26 each carry the same fact `private`). -/
private theorem digAt_index_spec (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) + (F.slotIdx k + F.e₁ * t) * F.h
      = k := by
  have hle : (F.slotIdx k + F.e₁ * t) * F.h ≤ k := by
    have hmem := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    exact hmem.2
  have hdvd : F.e₁ ∣ k - (F.slotIdx k + F.e₁ * t) * F.h := by
    refine (Nat.modEq_iff_dvd' hle).mp ?_
    calc
      (F.slotIdx k + F.e₁ * t) * F.h
          = F.slotIdx k * F.h + F.e₁ * (t * F.h) := by ring
      _ ≡ F.slotIdx k * F.h + 0 [MOD F.e₁] :=
        Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr ⟨t * F.h, rfl⟩)
      _ = F.slotIdx k * F.h := by ring
      _ ≡ k [MOD F.e₁] := (F.slotIdx_spec k).2
  rw [Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hle]

/-- `π^k ∣ x` from a valuation floor (private-copy pattern: C131y/C131ae/C.26). -/
private theorem dvd_of_le_addVal (hπ : Irreducible π) {k : ℕ} {x : O}
    (h : (k : ℕ∞) ≤ addVal O x) : π ^ k ∣ x := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]
  exact h

/-- **the NON-strict companion of C131y's `addVal_coeff_of_stageHeight_lt`**: a coefficient
consulted at a digit level ON a stage-height floor is divisible exactly to that level —
`e₁·q + pos·h = k ≤ dv(B)` gives `q ≤ v(b_pos)`. -/
private theorem addVal_coeff_of_le_stageHeight (F : KeyFrame O π) {B : Polynomial O}
    {k pos q : ℕ} (hspec : F.e₁ * q + pos * F.h = k)
    (hk : (k : ℕ∞) ≤ F.stageHeight B) :
    (q : ℕ∞) ≤ addVal O (B.coeff pos) := by
  have hstep : F.stageHeight B ≤ F.e₁ • addVal O (B.coeff pos) + (F.h * pos : ℕ∞) := by
    rw [F.stageHeight_eq_inf]
    by_cases hposle : pos ≤ B.natDegree
    · have hle := Finset.inf_le
          (f := fun i => F.e₁ • gaussVal (Polynomial.C (B.coeff i)) + (F.h * i : ℕ∞))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hposle))
      rwa [GateKit.gaussVal_C] at hle
    · have hz : B.coeff pos = 0 := B.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, addVal_zero, C118a.smul_top_pos F.he₁, top_add]
      exact le_top
  rcases eq_or_ne (addVal O (B.coeff pos)) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  have hle : (k : ℕ∞) ≤ ((F.e₁ * c + F.h * pos : ℕ) : ℕ∞) := by
    refine le_trans (le_trans hk hstep) (le_of_eq ?_)
    rw [← hc, weight_read]
  rw [← hc]
  have hnat : k ≤ F.e₁ * c + F.h * pos := by exact_mod_cast hle
  rw [Nat.mul_comm F.h pos] at hnat
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : F.e₁ * q ≤ F.e₁ * c) F.he₁

/-- the normalized slot residue of the zero polynomial vanishes at every height. -/
theorem slotRes_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (k : ℕ) : F.slotRes H₀ hpin k (0 : Polynomial O) = 0 := by
  rw [KeyFrame.slotRes]
  refine Finset.sum_eq_zero fun t ht => ?_
  rw [Polynomial.coeff_zero,
    digAt_eq hπ (show (0 : O) = π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * 0 by
      rw [mul_zero]),
    map_zero, map_zero, map_zero, zero_mul]

/-- the ϖ-read of the zero polynomial vanishes at every height. -/
theorem twistRead_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (k : ℕ) : F.twistRead H₀ hpin k (0 : Polynomial O) = 0 := by
  rw [KeyFrame.twistRead, slotRes_zero F hπ H₀ hpin k, mul_zero]

/-- **slot-read additivity at a common height floor**: if both `A` and `B` have stage height
`≥ k`, every digit the height-`k` window consults is read at a `π`-divisible coefficient, so
the slot read is additive (B.22's `digAt_add`). -/
theorem slotRes_add_of_le (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {A B : Polynomial O} {k : ℕ}
    (hA : (k : ℕ∞) ≤ F.stageHeight A) (hB : (k : ℕ∞) ≤ F.stageHeight B) :
    F.slotRes H₀ hpin k (A + B) = F.slotRes H₀ hpin k A + F.slotRes H₀ hpin k B := by
  rw [KeyFrame.slotRes, KeyFrame.slotRes, KeyFrame.slotRes, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hspec := digAt_index_spec F k t ht
  have hdA : π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
      ∣ A.coeff (F.slotIdx k + F.e₁ * t) :=
    dvd_of_le_addVal hπ (addVal_coeff_of_le_stageHeight F hspec hA)
  have hdB : π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
      ∣ B.coeff (F.slotIdx k + F.e₁ * t) :=
    dvd_of_le_addVal hπ (addVal_coeff_of_le_stageHeight F hspec hB)
  rw [Polynomial.coeff_add, digAt_add hπ hdA hdB, map_add, map_add, add_mul]

/-- ★ **ϖ-read additivity at a common height floor** (RP-2's engine; the two-sided law whose
`>` degenerations are C131y's `twistRead_add_deep`). -/
theorem twistRead_add_of_le (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {A B : Polynomial O} {k : ℕ}
    (hA : (k : ℕ∞) ≤ F.stageHeight A) (hB : (k : ℕ∞) ≤ F.stageHeight B) :
    F.twistRead H₀ hpin k (A + B) = F.twistRead H₀ hpin k A + F.twistRead H₀ hpin k B := by
  rw [KeyFrame.twistRead, KeyFrame.twistRead, KeyFrame.twistRead,
    slotRes_add_of_le F hπ H₀ hpin hA hB, mul_add]

/-- **the read of a strictly-above slot is `0`**: the ϖ-read at height `k` of anything of
stage height `> k` vanishes — why an off-line (above-line) slot reads `0` through the same
formula as an on-line one. -/
theorem twistRead_eq_zero_of_lt (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {A : Polynomial O} {k : ℕ} (hk : (k : ℕ∞) < F.stageHeight A) :
    F.twistRead H₀ hpin k A = 0 := by
  have h := C131y.twistRead_add_deep F hπ H₀ hpin (A := 0) (B := A) hk
  rw [zero_add] at h
  rw [h]
  exact twistRead_zero F hπ H₀ hpin k

/-! ## Part 3 — the generic endpoint split (NV-3's unique lowest term, exported)

NV-3's `stageHeight_dev_endpoint_le_of_surv` proves the split internally and exports only the
height bound; RP-3's read-level relation needs the SPLIT itself, so it is re-derived here as
a standalone: the endpoint development coefficient of `g·z` is the surviving term
`(dev g jg · dev z jz) %ₘ Φ′` plus a tail priced strictly above — UNCONDITIONALLY (survival
is only needed to READ the split, not to have it). -/

/-- ★ **the unique-lowest-term split** (generic, under NV-2/NV-3's strict admissibility): at
the endpoint slot `jg + jz`, `dev (g·z) = (dev g jg · dev z jz) %ₘ Φ′ + R` with
`Hg + Hz + 1 ≤ dv(R)` — every non-endpoint convolution term is strictly above the line
(`lt_line_dev_term` + the endpoint-pair uniqueness), and the finite-sum ultrametric prices
their sum. -/
theorem dev_mul_endpoint_split (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm' : ℓ * V < u) {g z : Polynomial O}
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt F g (dvSideMin F g u ℓ hng) = (Hg : ℕ∞))
    (hHz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Hz : ℕ∞)) :
    ∃ R : Polynomial O,
      dev F.key (g * z) (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz)
        = (dev F.key g (dvSideMin F g u ℓ hng) * dev F.key z (dvSideMin F z u ℓ hnz))
            %ₘ F.key + R
      ∧ ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ F.stageHeight R := by
  classical
  set jg := dvSideMin F g u ℓ hng with hjg
  set jz := dvSideMin F z u ℓ hnz with hjz
  have hSg : dvSupp F g u ℓ = ((ℓ * Hg + u * jg : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHg (dvOnSide_dvSideMin F g u ℓ hng)
  have hSz : dvSupp F z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHz (dvOnSide_dvSideMin F z u ℓ hnz)
  -- the double development of the product (NV-2/NV-3's convolution pattern)
  have hkeypos := F.natDegree_key_pos
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * F.key.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hkeypos)
  have hzN : z.natDegree < N * F.key.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hkeypos)
  have hgrep : ∑ j ∈ Finset.range N, dev F.key g j * F.key ^ j = g :=
    sum_dev_eq F.hmonic hkeypos g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev F.key z i * F.key ^ i = z :=
    sum_dev_eq F.hmonic hkeypos z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev F.key g j * F.key ^ j)
        * (∑ i ∈ Finset.range N, dev F.key z i * F.key ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  have hdev : dev F.key (g * z) (jg + jz)
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) (jg + jz) := by
    conv_lhs => rw [hrep]
    exact dev_finsetSum F.hmonic _ _ (jg + jz)
  -- the endpoint pair sits inside the convolution square
  have hp0 : ((jg, jz) : ℕ × ℕ) ∈ Finset.range N ×ˢ Finset.range N := by
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
    · have := dvSideMin_le_natDegree F g u ℓ hng
      omega
    · have := dvSideMin_le_natDegree F z u ℓ hnz
      omega
  -- split off the endpoint term, and identify it as the reduced remainder
  have hT0 : dev F.key (dev F.key g jg * dev F.key z jz * F.key ^ (jg + jz)) (jg + jz)
      = (dev F.key g jg * dev F.key z jz) %ₘ F.key := by
    have h := dev_mul_pow F.hmonic (jg + jz) (dev F.key g jg * dev F.key z jz) 0
    rw [Nat.add_zero] at h
    rw [h, dev_zero_pin]
  have hsplit : dev F.key (g * z) (jg + jz)
      = (dev F.key g jg * dev F.key z jz) %ₘ F.key
        + ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
            dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) (jg + jz) := by
    rw [hdev, ← hT0]
    exact (Finset.add_sum_erase _ _ hp0).symm
  -- every non-endpoint term prices strictly above the line (weight form)
  have hallR : ∀ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      ((ℓ * (Hg + Hz) + u * (jg + jz) + 1 : ℕ) : ℕ∞)
        ≤ ℓ • F.stageHeight
            (dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) (jg + jz))
          + (u * (jg + jz) : ℕ∞) := by
    intro p hp
    have hbad : ¬ (p.1 + p.2 = jg + jz ∧ DvOnSide F g u ℓ p.1 ∧ DvOnSide F z u ℓ p.2) := by
      rintro ⟨hsum, h1, h2⟩
      obtain ⟨e1, e2⟩ := dvOnSide_endpoint_unique hng hnz hsum h1 h2
      exact (Finset.mem_erase.1 hp).1 (Prod.ext_iff.2 ⟨e1, e2⟩)
    refine le_trans (le_of_eq ?_) (lt_line_dev_term hπ F hh hℓ hV hadm' hSg hSz hbad)
    push_cast
    ring
  have hRw := le_weight_stageHeight_sum F hℓ _ _ hallR
  have hR : ((Hg + Hz : ℕ) : ℕ∞) + 1
      ≤ F.stageHeight (∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
          dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) (jg + jz)) :=
    succ_le_of_weight_succ_le hRw
  exact ⟨_, hsplit, hR⟩

end Generic

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 4 — the S2 grade/side dictionary, and the value-floor converters -/

/-- an exact grade is a cleared-support floor (the strong add law's hypothesis converter). -/
theorem le_dvSupp_of_exact {β : ℕ} {g : Polynomial O} (hg : S2ExactGrade h2 hq β g) :
    (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) g 5 2 :=
  le_of_eq ((S2ExactGrade_iff_dvSupp h2 hq).mp hg).symm

/-- an above grade is a cleared-support floor. -/
theorem le_dvSupp_of_above {β : ℕ} {g : Polynomial O} (hg : S2AboveGrade h2 hq β g) :
    (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) g 5 2 :=
  le_of_lt ((S2AboveGrade_iff_dvSupp h2 hq).mp hg)

/-- **at an exact grade, the grade line IS the side**: `S2SlotOnGrade β g s ↔ DvOnSide g s`
whenever `β` is `g`'s exact grade — RP-1's line gate and C.07's minimizing-slot predicate
name the same slots.  (RP-4's slot dictionary.) -/
theorem s2SlotOnGrade_iff_dvOnSide {β s : ℕ} {g : Polynomial O}
    (hβ : S2ExactGrade h2 hq β g) :
    S2SlotOnGrade h2 hq β g s ↔ DvOnSide (s2Frame h2 hq) g 5 2 s := by
  have hsupp := (S2ExactGrade_iff_dvSupp h2 hq).mp hβ
  constructor
  · intro hgate
    obtain ⟨m, hm, hlin⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
    refine ⟨?_, by rw [hm]; exact ENat.coe_ne_top m⟩
    rw [hsupp, hm, weight_read]
    exact_mod_cast hlin.symm
  · intro hside
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hside.2
    refine (s2SlotOnGrade_iff h2 hq).mpr ⟨c, hc.symm, ?_⟩
    have h1 := hside.1
    rw [hsupp, ← hc, weight_read] at h1
    exact_mod_cast h1.symm

/-! ## Part 5 — RP-2's remainder: the graded ADD law

The bridge below is the pointwise heart: on a cleared-value floor, the gated coefficient IS
the ϖ-read at the on-line height whether or not the gate fires — an above-line slot reads
`0` through the same formula (`twistRead_eq_zero_of_lt`).  Additivity is then `dev`
additivity plus ϖ-read additivity, with cancellation (both summands on-line, the sum above)
absorbed rather than case-split. -/

/-- **the floor bridge**: if slot `β % 2 + 2t` of the `β`-line has its height AT OR ABOVE the
on-line height `m` (`2m + 5s = β`), the gated coefficient equals the ϖ-read at `m` — on the
gate by RP-1's true-height pin, above it as `0 = 0`. -/
theorem s2GradedCoeff_eq_twistRead_of_le {β t m : ℕ} {g : Polynomial O}
    (hm : 2 * m + 5 * (β % 2 + 2 * t) = β)
    (hge : (m : ℕ∞) ≤ dvHgt (s2Frame h2 hq) g (β % 2 + 2 * t)) :
    s2GradedCoeff h2 hq β g t
      = (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m
          (dev (s2Frame h2 hq).key g (β % 2 + 2 * t)) := by
  rcases eq_or_lt_of_le hge with heq | hlt
  · exact s2GradedCoeff_eq_twistRead h2 hq
      ((s2SlotOnGrade_iff h2 hq).mpr ⟨m, heq.symm, hm⟩) heq.symm
  · rw [twistRead_eq_zero_of_lt (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) hlt]
    have hgate : ¬ S2SlotOnGrade h2 hq β g (β % 2 + 2 * t) := by
      intro hgate
      obtain ⟨m', hm', hβ'⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
      rw [hm'] at hlt
      have : m < m' := by exact_mod_cast hlt
      omega
    unfold s2GradedCoeff
    rw [if_neg hgate]
    exact rfl

/-- ★ **RP-2, the coefficientwise ADD law (strong form)**: on a common cleared-value floor
`β ≤ dvSupp g, dvSupp h`, every graded coefficient is additive — including the cancellation
slots, where both summands read on-line and the sum reads `0` above the line. -/
theorem s2GradedCoeff_add {β t : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) g 5 2)
    (hh : (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) h 5 2) :
    s2GradedCoeff h2 hq β (g + h) t
      = s2GradedCoeff h2 hq β g t + s2GradedCoeff h2 hq β h t := by
  rcases Nat.lt_or_ge β (5 * (β % 2 + 2 * t)) with hlt | hge5
  · rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq hlt,
      s2GradedCoeff_eq_zero_of_grade_lt h2 hq hlt,
      s2GradedCoeff_eq_zero_of_grade_lt h2 hq hlt, add_zero]
  · have hm : 2 * ((β - 5 * (β % 2 + 2 * t)) / 2) + 5 * (β % 2 + 2 * t) = β := by omega
    have hgeg : (((β - 5 * (β % 2 + 2 * t)) / 2 : ℕ) : ℕ∞)
        ≤ dvHgt (s2Frame h2 hq) g (β % 2 + 2 * t) :=
      le_dvHgt_of_le_dvSupp (by norm_num) hg hm
    have hgeh : (((β - 5 * (β % 2 + 2 * t)) / 2 : ℕ) : ℕ∞)
        ≤ dvHgt (s2Frame h2 hq) h (β % 2 + 2 * t) :=
      le_dvHgt_of_le_dvSupp (by norm_num) hh hm
    have hgegh : (((β - 5 * (β % 2 + 2 * t)) / 2 : ℕ) : ℕ∞)
        ≤ dvHgt (s2Frame h2 hq) (g + h) (β % 2 + 2 * t) :=
      le_trans (le_min hgeg hgeh) (C131y.dvHgt_add_min (s2Frame h2 hq) g h (β % 2 + 2 * t))
    rw [s2GradedCoeff_eq_twistRead_of_le h2 hq hm hgegh,
      s2GradedCoeff_eq_twistRead_of_le h2 hq hm hgeg,
      s2GradedCoeff_eq_twistRead_of_le h2 hq hm hgeh,
      dev_add_of_monic (s2Frame h2 hq).hmonic]
    exact twistRead_add_of_le (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) hgeg hgeh

/-- ★ **RP-2, the graded ADD law (strong form)**: `R_β(g + h) = R_β(g) + R_β(h)` whenever
both inputs have cleared value `≥ β` — no hypothesis on the sum (cancellation included). -/
theorem s2GradedRes_add_of_le {β : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) g 5 2)
    (hh : (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) h 5 2) :
    s2GradedRes h2 hq β (g + h) = s2GradedRes h2 hq β g + s2GradedRes h2 hq β h := by
  refine Polynomial.ext fun t => ?_
  rw [Polynomial.coeff_add, s2GradedRes_coeff, s2GradedRes_coeff, s2GradedRes_coeff,
    s2GradedCoeff_add h2 hq hg hh]

set_option linter.unusedVariables false in
/-- ★ **NODE RP-2, the graded ADD law** (published Cor 4.12(1), C130fg's `graded_add` binder
pattern verbatim at the S2 occurrence): exact + exact + exact-sum inputs give
`R_β(g + h) = R_β(g) + R_β(h)`.  The exact-sum hypothesis `hgh` is carried for field-shape
fidelity only — `s2GradedRes_add_of_le` proves the law without it. -/
theorem s2GradedRes_add {β : ℕ} {g h : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hh : S2ExactGrade h2 hq β h)
    (hgh : S2ExactGrade h2 hq β (g + h)) :
    s2GradedRes h2 hq β (g + h) = s2GradedRes h2 hq β g + s2GradedRes h2 hq β h :=
  s2GradedRes_add_of_le h2 hq (le_dvSupp_of_exact h2 hq hg) (le_dvSupp_of_exact h2 hq hh)

/-! ## Part 6 — the S2 ϖ-read normal form

At the S2 frame `(e₁, f₁, h) = (2, 1, 1)`: the window is always `{0}`, the slot index is the
parity `k % 2`, the twist exponent is `k / 2` — and the letter `η` is `1` because `|K₁| = 2`
(C.80), so the ϖ-read collapses to a single digit read.  These generalize RP-1's `k = 0` and
C35b's `k = 1` computations to every height. -/

/-- private copy of C.80's `eq_one_of_card_two` (the private-copy pattern). -/
private theorem eq_one_of_card_two {K : Type} [Field K] (hcard : Nat.card K = 2)
    {z : K} (hz : z ≠ 0) : z = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hz.isUnit.unit = 1 := Subsingleton.elim _ _
  calc z = ((hz.isUnit.unit : Kˣ) : K) := (hz.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- **the S2 letter is `1`**: `η ≠ 0` (C.19) in the 2-element stage field (C.80's
`card_K₁`), so `η = 1` — the ϖ-twist is invisible at S2.  (NOT a general-frame fact.) -/
theorem s2_stageLetter_eq_one :
    (s2Frame h2 hq).stageLetter 1 (s2Frame_pin h2 hq) = 1 := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  exact eq_one_of_card_two (C80.card_K₁ h2 hq)
    ((s2Frame h2 hq).stageLetter_ne_zero h2 1 (s2Frame_pin h2 hq))

/-- `i(k) = k % 2` at the S2 frame (C35b's `slotIdx_one`/RP-1's `slotIdx_zero`, at every
height). -/
theorem slotIdx_eq (k : ℕ) : (s2Frame h2 hq).slotIdx k = k % 2 := by
  change ((List.range 2).find? (fun i => (i * 1) % 2 == k % 2)).getD 0 = k % 2
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp only [h] <;> rfl

/-- `q(k) = k / 2` at the S2 frame. -/
theorem twistExp_eq (k : ℕ) : (s2Frame h2 hq).twistExp k = k / 2 := by
  rw [KeyFrame.twistExp, slotIdx_one h2 hq, slotIdx_eq h2 hq k, e1_eq h2 hq, one_mul]
  omega

/-- the slot window is `{0}` at the S2 frame, at every height (`f₁ = 1`). -/
theorem slotWindow_eq (k : ℕ) : (s2Frame h2 hq).slotWindow k = {0} := by
  rw [KeyFrame.slotWindow]
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
    f1_eq h2 hq, e1_eq h2 hq, h_eq h2 hq, slotIdx_eq h2 hq k]
  omega

/-- **the S2 slot-read normal form**: the height-`k` slot read is the single digit read
`digAt 2 (k/2) (A.coeff (k%2))`, transported into the stage field. -/
theorem s2_slotRes_eq_digAt (k : ℕ) (A : Polynomial O) :
    (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A
      = algebraMap (resField (Polynomial.X : Polynomial O))
          ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))
          (algebraMap (IsLocalRing.ResidueField O) (resField (Polynomial.X : Polynomial O))
            (digAt (2 : O) (k / 2) (A.coeff (k % 2)))) := by
  rw [KeyFrame.slotRes, slotWindow_eq h2 hq k, Finset.sum_singleton]
  have hidx : (s2Frame h2 hq).slotIdx k + (s2Frame h2 hq).e₁ * 0 = k % 2 := by
    rw [slotIdx_eq h2 hq k, e1_eq h2 hq]
    omega
  rw [hidx]
  have hdig : (k - k % 2 * (s2Frame h2 hq).h) / (s2Frame h2 hq).e₁ = k / 2 := by
    rw [h_eq h2 hq, e1_eq h2 hq]
    omega
  rw [hdig, pow_zero, mul_one]

/-- **the twist is trivial at S2**: `twistRead k = slotRes k` (`η = 1`). -/
theorem s2_twistRead_eq_slotRes (k : ℕ) (A : Polynomial O) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) k A
      = (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  show ((s2Frame h2 hq).stageLetter 1 (s2Frame_pin h2 hq))⁻¹ ^ ((s2Frame h2 hq).twistExp k)
      * (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A
    = (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A
  rw [s2_stageLetter_eq_one h2 hq, inv_one, one_pow, one_mul]

/-- ★ **the S2 ϖ-read normal form**: `twistRead k A = digAt 2 (k/2) (A.coeff (k%2))`,
transported — every corpus ϖ-read at S2 is one digit of one coefficient.  (RP-4's
computational vocabulary.) -/
theorem s2_twistRead_eq_digAt (k : ℕ) (A : Polynomial O) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) k A
      = algebraMap (resField (Polynomial.X : Polynomial O))
          ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))
          (algebraMap (IsLocalRing.ResidueField O) (resField (Polynomial.X : Polynomial O))
            (digAt (2 : O) (k / 2) (A.coeff (k % 2)))) := by
  rw [s2_twistRead_eq_slotRes h2 hq k A]
  exact s2_slotRes_eq_digAt h2 hq k A

/-! ## Part 7 — ★ NODE RP-3: the survival core at the residual-read level

FGMN's `ψ ∤ R(a)·R(b)` non-cancellation, concretized at S2 and read at the DIGIT level: the
ϖ-read of the reduced remainder of a product of two short digits is the PRODUCT of their
ϖ-reads, at added heights.  C130nv3 proved the HEIGHT half (`s2_stageHeight_mul_modByMonic_le`);
this is the VALUE half, by the same four parity genres — the odd×odd genre is the genuine
carry: `x² ≡ 2` transfers the digit through `2·a₁b₁ = 2^{m+n+1}·(a₁/2^m)(b₁/2^n)`. -/

/-- ★ **the S2 survival core at the read level**: for `a, b` of degree `≤ 1` with cleared
height floors `Ha ≤ dv(a)`, `Hb ≤ dv(b)`,
`twistRead (Ha + Hb) ((a·b) %ₘ Φ′) = twistRead Ha a · twistRead Hb b`.  FLOOR hypotheses
only — at a strictly-above input both sides vanish, so the law is uniform. -/
theorem s2_twistRead_mul_modByMonic {a b : Polynomial O} (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 1) {Ha Hb : ℕ}
    (hA : (Ha : ℕ∞) ≤ (s2Frame h2 hq).stageHeight a)
    (hB : (Hb : ℕ∞) ≤ (s2Frame h2 hq).stageHeight b) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) (Ha + Hb)
        ((a * b) %ₘ (s2Frame h2 hq).key)
      = (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) Ha a
        * (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) Hb b := by
  -- the four coefficient valuation floors
  rw [s2_stageHeight_linear h2 hq ha] at hA
  rw [s2_stageHeight_linear h2 hq hb] at hB
  have hA0 : (((Ha + 1) / 2 : ℕ) : ℕ∞) ≤ addVal O (a.coeff 0) :=
    coe_le_of_le_two_smul (le_trans hA (min_le_left _ _))
  have hA1 : ((Ha / 2 : ℕ) : ℕ∞) ≤ addVal O (a.coeff 1) :=
    coe_le_of_le_two_smul_add_one (le_trans hA (min_le_right _ _))
  have hB0 : (((Hb + 1) / 2 : ℕ) : ℕ∞) ≤ addVal O (b.coeff 0) :=
    coe_le_of_le_two_smul (le_trans hB (min_le_left _ _))
  have hB1 : ((Hb / 2 : ℕ) : ℕ∞) ≤ addVal O (b.coeff 1) :=
    coe_le_of_le_two_smul_add_one (le_trans hB (min_le_right _ _))
  -- the explicit remainder (NV-3) and the three read normal forms
  rw [key_eq h2 hq, s2_mul_modByMonic a b ha hb, s2_twistRead_eq_digAt h2 hq,
    s2_twistRead_eq_digAt h2 hq, s2_twistRead_eq_digAt h2 hq, ← map_mul, ← map_mul]
  refine congrArg _ (congrArg _ ?_)
  -- the remainder's two coefficients
  have hc0 : (Polynomial.C (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0) * Polynomial.X
      + Polynomial.C (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1))).coeff 0
      = a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1) := by
    simp
  have hc1 : (Polynomial.C (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0) * Polynomial.X
      + Polynomial.C (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1))).coeff 1
      = a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0 := by
    simp
  -- the four parity genres
  rcases Nat.mod_two_eq_zero_or_one Ha with hpa | hpa <;>
    rcases Nat.mod_two_eq_zero_or_one Hb with hpb | hpb
  · -- even × even: survival at the constant slot, no carry
    rw [show (Ha + 1) / 2 = Ha / 2 by omega] at hA0
    rw [show (Hb + 1) / 2 = Hb / 2 by omega] at hB0
    obtain ⟨a0', ha0'⟩ := dvd_of_le_addVal h2 hA0
    obtain ⟨b0', hb0'⟩ := dvd_of_le_addVal h2 hB0
    obtain ⟨a1', ha1'⟩ := dvd_of_le_addVal h2 hA1
    obtain ⟨b1', hb1'⟩ := dvd_of_le_addVal h2 hB1
    rw [hpa, hpb, show (Ha + Hb) % 2 = 0 by omega,
      show (Ha + Hb) / 2 = Ha / 2 + Hb / 2 by omega, hc0]
    have hcongr : digAt (2 : O) (Ha / 2 + Hb / 2)
        (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1))
        = digAt (2 : O) (Ha / 2 + Hb / 2) (a.coeff 0 * b.coeff 0) :=
      (C109asm.digAt_congr h2 ⟨a1' * b1', by rw [ha1', hb1']; ring⟩).symm
    rw [hcongr,
      digAt_eq h2 (show a.coeff 0 * b.coeff 0 = (2 : O) ^ (Ha / 2 + Hb / 2) * (a0' * b0') by
        rw [ha0', hb0']; ring),
      digAt_eq h2 ha0', digAt_eq h2 hb0', ← map_mul]
  · -- even × odd: survival at the linear slot, cross term above
    rw [show (Ha + 1) / 2 = Ha / 2 by omega] at hA0
    rw [show (Hb + 1) / 2 = Hb / 2 + 1 by omega] at hB0
    obtain ⟨a0', ha0'⟩ := dvd_of_le_addVal h2 hA0
    obtain ⟨b0', hb0'⟩ := dvd_of_le_addVal h2 hB0
    obtain ⟨a1', ha1'⟩ := dvd_of_le_addVal h2 hA1
    obtain ⟨b1', hb1'⟩ := dvd_of_le_addVal h2 hB1
    rw [hpa, hpb, show (Ha + Hb) % 2 = 1 by omega,
      show (Ha + Hb) / 2 = Ha / 2 + Hb / 2 by omega, hc1]
    have hcongr : digAt (2 : O) (Ha / 2 + Hb / 2)
        (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0)
        = digAt (2 : O) (Ha / 2 + Hb / 2) (a.coeff 0 * b.coeff 1) :=
      (C109asm.digAt_congr h2 ⟨a1' * b0', by rw [ha1', hb0']; ring⟩).symm
    rw [hcongr,
      digAt_eq h2 (show a.coeff 0 * b.coeff 1 = (2 : O) ^ (Ha / 2 + Hb / 2) * (a0' * b1') by
        rw [ha0', hb1']; ring),
      digAt_eq h2 ha0', digAt_eq h2 hb1', ← map_mul]
  · -- odd × even: survival at the linear slot, mirror
    rw [show (Ha + 1) / 2 = Ha / 2 + 1 by omega] at hA0
    rw [show (Hb + 1) / 2 = Hb / 2 by omega] at hB0
    obtain ⟨a0', ha0'⟩ := dvd_of_le_addVal h2 hA0
    obtain ⟨b0', hb0'⟩ := dvd_of_le_addVal h2 hB0
    obtain ⟨a1', ha1'⟩ := dvd_of_le_addVal h2 hA1
    obtain ⟨b1', hb1'⟩ := dvd_of_le_addVal h2 hB1
    rw [hpa, hpb, show (Ha + Hb) % 2 = 1 by omega,
      show (Ha + Hb) / 2 = Ha / 2 + Hb / 2 by omega, hc1]
    have hcongr : digAt (2 : O) (Ha / 2 + Hb / 2)
        (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0)
        = digAt (2 : O) (Ha / 2 + Hb / 2) (a.coeff 1 * b.coeff 0) := by
      refine (C109asm.digAt_congr h2 ⟨a0' * b1', ?_⟩).symm
      rw [ha0', hb1']
      ring
    rw [hcongr,
      digAt_eq h2 (show a.coeff 1 * b.coeff 0 = (2 : O) ^ (Ha / 2 + Hb / 2) * (a1' * b0') by
        rw [ha1', hb0']; ring),
      digAt_eq h2 ha1', digAt_eq h2 hb0', ← map_mul]
  · -- odd × odd: the carry genre — `x² ≡ 2` transfers the digit
    rw [show (Ha + 1) / 2 = Ha / 2 + 1 by omega] at hA0
    rw [show (Hb + 1) / 2 = Hb / 2 + 1 by omega] at hB0
    obtain ⟨a0', ha0'⟩ := dvd_of_le_addVal h2 hA0
    obtain ⟨b0', hb0'⟩ := dvd_of_le_addVal h2 hB0
    obtain ⟨a1', ha1'⟩ := dvd_of_le_addVal h2 hA1
    obtain ⟨b1', hb1'⟩ := dvd_of_le_addVal h2 hB1
    rw [hpa, hpb, show (Ha + Hb) % 2 = 0 by omega,
      show (Ha + Hb) / 2 = Ha / 2 + Hb / 2 + 1 by omega, hc0]
    have hcongr : digAt (2 : O) (Ha / 2 + Hb / 2 + 1)
        (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1))
        = digAt (2 : O) (Ha / 2 + Hb / 2 + 1) (2 * (a.coeff 1 * b.coeff 1)) := by
      refine C109asm.digAt_congr h2 ⟨-(a0' * b0'), ?_⟩
      rw [ha0', hb0']
      ring
    rw [hcongr,
      digAt_eq h2 (show 2 * (a.coeff 1 * b.coeff 1)
          = (2 : O) ^ (Ha / 2 + Hb / 2 + 1) * (a1' * b1') by
        rw [ha1', hb1']; ring),
      digAt_eq h2 ha1', digAt_eq h2 hb1', ← map_mul]

/-! ## Part 8 — ★ NODE RP-3: the endpoint read, and the endpoint-coefficient relation -/

/-- ★ **the endpoint read is the product of the reads**: at the chosen minimizers, the
ϖ-read of `dev (g·z) (jg + jz)` at height `Hg + Hz` is
`twistRead Hg (dev g jg) · twistRead Hz (dev z jz)` — the split (`dev_mul_endpoint_split`)
plus C131y's `twistRead_add_deep` (the tail is priced strictly above, hence invisible) plus
the survival core. -/
theorem s2_twistRead_dev_mul_endpoint {g z : Polynomial O}
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt (s2Frame h2 hq) g (dvSideMin (s2Frame h2 hq) g 5 2 hng) = (Hg : ℕ∞))
    (hHz : dvHgt (s2Frame h2 hq) z (dvSideMin (s2Frame h2 hq) z 5 2 hnz) = (Hz : ℕ∞)) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) (Hg + Hz)
        (dev (s2Frame h2 hq).key (g * z)
          (dvSideMin (s2Frame h2 hq) g 5 2 hng + dvSideMin (s2Frame h2 hq) z 5 2 hnz))
      = (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) Hg
          (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 2 hng))
        * (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) Hz
            (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 2 hnz)) := by
  obtain ⟨R, hsplit, hR⟩ := dev_mul_endpoint_split h2 (s2Frame h2 hq) (s2_h_pos h2 hq)
    (by norm_num) (s2_stageHeight_key h2 hq) (by norm_num) hng hnz hHg hHz
  have hR' : ((Hg + Hz + 1 : ℕ) : ℕ∞) ≤ (s2Frame h2 hq).stageHeight R := by
    refine le_trans (le_of_eq ?_) hR
    push_cast
    ring
  have hlt : ((Hg + Hz : ℕ) : ℕ∞) < (s2Frame h2 hq).stageHeight R :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : Hg + Hz < Hg + Hz + 1)) hR'
  rw [hsplit, C131y.twistRead_add_deep (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) hlt]
  -- the surviving digits are nonzero (finite height) and short (degree < deg Φ′ = 2)
  have hg0 : dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 2 hng) ≠ 0 := by
    intro h0
    have htop : dvHgt (s2Frame h2 hq) g (dvSideMin (s2Frame h2 hq) g 5 2 hng) = ⊤ := by
      show (s2Frame h2 hq).stageHeight
        (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 2 hng)) = ⊤
      rw [h0, (s2Frame h2 hq).stageHeight_zero]
    rw [hHg] at htop
    exact ENat.coe_ne_top Hg htop
  have hz0 : dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 2 hnz) ≠ 0 := by
    intro h0
    have htop : dvHgt (s2Frame h2 hq) z (dvSideMin (s2Frame h2 hq) z 5 2 hnz) = ⊤ := by
      show (s2Frame h2 hq).stageHeight
        (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 2 hnz)) = ⊤
      rw [h0, (s2Frame h2 hq).stageHeight_zero]
    rw [hHz] at htop
    exact ENat.coe_ne_top Hz htop
  have hkd : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [key_eq h2 hq]
    exact s2Key_natDegree
  have hdg : (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 2 hng)).natDegree
      ≤ 1 := by
    have h := natDegree_lt_natDegree hg0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos g _)
    rw [hkd] at h
    omega
  have hdz : (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 2 hnz)).natDegree
      ≤ 1 := by
    have h := natDegree_lt_natDegree hz0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos z _)
    rw [hkd] at h
    omega
  exact s2_twistRead_mul_modByMonic h2 hq hdg hdz (le_of_eq hHg.symm) (le_of_eq hHz.symm)

/-- ★ **NODE RP-3, the headline — the endpoint-coefficient relation** (the endpoint instance
of the corrected `graded_mul`, which RP-4's convolution recursion consumes): at exact grades
`β`, `β′`, the product's graded coefficient at the endpoint `y`-power `(jg + jz)/2` is the
product of the factors' endpoint coefficients at `jg/2` and `jz/2`.  The `y`-power arithmetic
`(jg + jz)/2 = jg/2 + jz/2 + (β % 2)·(β′ % 2)` carries the parity CARRY: both grades odd
shifts the product's `y`-power up by one (`tooth_endpoint_carry`). -/
theorem s2GradedCoeff_mul_endpoint {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 2).Nonempty) :
    s2GradedCoeff h2 hq (β + β') (g * z)
        ((dvSideMin (s2Frame h2 hq) g 5 2 hng + dvSideMin (s2Frame h2 hq) z 5 2 hnz) / 2)
      = s2GradedCoeff h2 hq β g (dvSideMin (s2Frame h2 hq) g 5 2 hng / 2)
        * s2GradedCoeff h2 hq β' z (dvSideMin (s2Frame h2 hq) z 5 2 hnz / 2) := by
  obtain ⟨Hg, hHg⟩ := exists_dvSideMin_height (s2Frame h2 hq) g 5 2 hng
  obtain ⟨Hz, hHz⟩ := exists_dvSideMin_height (s2Frame h2 hq) z 5 2 hnz
  set jg := dvSideMin (s2Frame h2 hq) g 5 2 hng with hjg
  set jz := dvSideMin (s2Frame h2 hq) z 5 2 hnz with hjz
  -- the two line equations at the chosen minimizers
  have hβg : β = 2 * Hg + 5 * jg := by
    have h1 := (S2ExactGrade_iff_dvSupp h2 hq).mp hg
    rw [dvSupp_eq_of_dvOnSide hHg (dvOnSide_dvSideMin (s2Frame h2 hq) g 5 2 hng)] at h1
    exact_mod_cast h1.symm
  have hβz : β' = 2 * Hz + 5 * jz := by
    have h1 := (S2ExactGrade_iff_dvSupp h2 hq).mp hz
    rw [dvSupp_eq_of_dvOnSide hHz (dvOnSide_dvSideMin (s2Frame h2 hq) z 5 2 hnz)] at h1
    exact_mod_cast h1.symm
  -- the product's endpoint slot: on-side (NV-3) with height exactly Hg + Hz
  have hOgz : DvOnSide (s2Frame h2 hq) (g * z) 5 2 (jg + jz) :=
    s2_dvOnSide_mul_endpoint h2 hq hng hnz hHg hHz
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hOgz.2
  have hsuppm : dvSupp (s2Frame h2 hq) (g * z) 5 2 = ((β + β' : ℕ) : ℕ∞) := by
    rw [s2_dvSupp_mul h2 hq, (S2ExactGrade_iff_dvSupp h2 hq).mp hg,
      (S2ExactGrade_iff_dvSupp h2 hq).mp hz]
    push_cast
    ring
  have hceq : c = Hg + Hz := by
    have h1 := hOgz.1
    rw [hsuppm, ← hc, weight_read] at h1
    have h2' : β + β' = 2 * c + 5 * (jg + jz) := by exact_mod_cast h1
    omega
  have hHgz : dvHgt (s2Frame h2 hq) (g * z) (jg + jz) = ((Hg + Hz : ℕ) : ℕ∞) := by
    rw [← hc, hceq]
  -- the three gates
  have hgateg : S2SlotOnGrade h2 hq β g jg :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨Hg, hHg, by omega⟩
  have hgatez : S2SlotOnGrade h2 hq β' z jz :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨Hz, hHz, by omega⟩
  have hgategz : S2SlotOnGrade h2 hq (β + β') (g * z) (jg + jz) :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨Hg + Hz, hHgz, by omega⟩
  -- read the three coefficients at their slots, pin the on-line heights, and conclude
  rw [s2GradedCoeff_slot h2 hq hgategz, s2GradedCoeff_slot h2 hq hgateg,
    s2GradedCoeff_slot h2 hq hgatez,
    show (β + β' - 5 * (jg + jz)) / 2 = Hg + Hz by omega,
    show (β - 5 * jg) / 2 = Hg by omega, show (β' - 5 * jz) / 2 = Hz by omega]
  exact s2_twistRead_dev_mul_endpoint h2 hq hng hnz hHg hHz

/-! ## Part 9 — endpoint teeth: minimizer computations for `x` and `Φ′` -/

/-- slot 0 of the `Φ′`-development of `x` is `x` itself (degree below the key). -/
theorem dev_X_zero : dev (s2Frame h2 hq).key (Polynomial.X : Polynomial O) 0
    = Polynomial.X := by
  rw [dev_zero_pin]
  exact (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_X, key_eq h2 hq, s2Key_deg]; norm_num)

/-- `dv(x₀) = 1` at the S2 frame. -/
theorem dvHgt_X_zero : dvHgt (s2Frame h2 hq) (Polynomial.X : Polynomial O) 0
    = ((1 : ℕ) : ℕ∞) := by
  rw [dvHgt, dev_X_zero h2 hq, sh_X h2 hq]
  exact Nat.cast_one.symm

/-- slot 0 is on `x`'s side: `dvSupp x = 2 = 2·1 + 5·0`. -/
theorem dvOnSide_X_zero : DvOnSide (s2Frame h2 hq) (Polynomial.X : Polynomial O) 5 2 0 := by
  constructor
  · rw [s2_dvSupp_X h2 hq, dvHgt_X_zero h2 hq, weight_read]
  · rw [dvHgt_X_zero h2 hq]
    exact ENat.coe_ne_top 1

/-- the chosen minimizer of `x` is slot `0`. -/
theorem dvSideMin_X (hng : (dvSideSet (s2Frame h2 hq) (Polynomial.X : Polynomial O) 5 2).Nonempty) :
    dvSideMin (s2Frame h2 hq) (Polynomial.X : Polynomial O) 5 2 hng = 0 :=
  Nat.le_zero.mp (dvSideMin_le_of_dvOnSide hng (dvOnSide_X_zero h2 hq))

/-- `dv((Φ′)₀) = ⊤` — the key's own development has no slot-0 digit. -/
theorem dvHgt_key_zero :
    dvHgt (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 0 = ⊤ := by
  rw [dvHgt, dev_zero_pin,
    show ((s2Frame h2 hq).key : Polynomial O) %ₘ (s2Frame h2 hq).key = 0 from
      (Polynomial.modByMonic_eq_zero_iff_dvd (s2Frame h2 hq).hmonic).mpr dvd_rfl]
  exact (s2Frame h2 hq).stageHeight_zero

/-- slot 1 is on `Φ′`'s side: `dvSupp Φ′ = 5 = 2·0 + 5·1`. -/
theorem dvOnSide_key_one :
    DvOnSide (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2 1 := by
  constructor
  · rw [s2_dvSupp_key h2 hq, dvHgt_key_one h2 hq]
    simp
  · rw [dvHgt_key_one h2 hq]
    simp

/-- the chosen minimizer of `Φ′` is slot `1` (slot 0 is off-side: height `⊤`). -/
theorem dvSideMin_key
    (hnz : (dvSideSet (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2).Nonempty) :
    dvSideMin (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2 hnz = 1 := by
  have h1 : dvSideMin (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2 hnz ≤ 1 :=
    dvSideMin_le_of_dvOnSide hnz (dvOnSide_key_one h2 hq)
  have h0 : dvSideMin (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2 hnz ≠ 0 := by
    intro h
    have hside := (dvOnSide_dvSideMin (s2Frame h2 hq)
      ((s2Frame h2 hq).key : Polynomial O) 5 2 hnz).2
    rw [h, dvHgt_key_zero h2 hq] at hside
    exact hside rfl
  omega

/-- **tooth (eq (11), `s = 0`)**: `R_2(x) = 1 = y^{⌊0/2⌋}` — the graded residual of `x` at
its landed exact grade `2` (RP-0's `tooth_X`). -/
theorem tooth_gradedRes_X : s2GradedRes h2 hq 2 (Polynomial.X : Polynomial O) = 1 := by
  have hgate : S2SlotOnGrade h2 hq 2 (Polynomial.X : Polynomial O) (2 % 2 + 2 * 0) :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨1, dvHgt_X_zero h2 hq, by norm_num⟩
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff]
  match t with
  | 0 =>
    rw [Polynomial.coeff_one_zero]
    unfold s2GradedCoeff
    rw [if_pos hgate, show (2 - 5 * (2 % 2 + 2 * 0)) / 2 = 1 by norm_num,
      show 2 % 2 + 2 * 0 = 0 by norm_num, dev_X_zero h2 hq]
    exact twistRead_one_X h2 hq
  | (t + 1) =>
    rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega), Polynomial.coeff_one]
    simp

/-- **tooth (endpoint relation, mixed parity)**: at `(β, β′) = (2, 5)`, `g = x`, `z = Φ′`,
the headline reads `Rgc_7(x·Φ′)(0) = Rgc_2(x)(0) · Rgc_5(Φ′)(0)` — no carry
(`(0+1)/2 = 0/2 + 1/2 + 0`); the landed values make it `1 = 1·1`. -/
theorem tooth_endpoint_mixed :
    s2GradedCoeff h2 hq 7 ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) 0
      = s2GradedCoeff h2 hq 2 (Polynomial.X : Polynomial O) 0
        * s2GradedCoeff h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) 0 := by
  have hng : (dvSideSet (s2Frame h2 hq) (Polynomial.X : Polynomial O) 5 2).Nonempty :=
    dvSideSet_nonempty (s2Frame h2 hq) Polynomial.X_ne_zero 5 (by norm_num)
  have hnz : (dvSideSet (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2).Nonempty :=
    dvSideSet_nonempty (s2Frame h2 hq) (s2Frame h2 hq).hmonic.ne_zero 5 (by norm_num)
  have h := s2GradedCoeff_mul_endpoint h2 hq (tooth_X h2 hq) (tooth_key h2 hq) hng hnz
  rw [dvSideMin_X h2 hq hng, dvSideMin_key h2 hq hnz] at h
  exact h

/-- **tooth (endpoint relation, the odd×odd CARRY)**: at `(β, β′) = (5, 5)`, `g = z = Φ′`,
the headline reads `Rgc_10(Φ′²)(1) = Rgc_5(Φ′)(0) · Rgc_5(Φ′)(0)` — the product's endpoint
`y`-power is `(1+1)/2 = 1 = 0 + 0 + 1`: one full carry from the two odd line offsets.  The
landed values make it `1 = 1·1` — read against `R₁₀(Φ′²) = X`, this is exactly why the
PLAIN product shape fails (`tooth_graded_mul_plain_shape_refuted`). -/
theorem tooth_endpoint_carry :
    s2GradedCoeff h2 hq 10
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 1
      = s2GradedCoeff h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) 0
        * s2GradedCoeff h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) 0 := by
  have hnz : (dvSideSet (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2).Nonempty :=
    dvSideSet_nonempty (s2Frame h2 hq) (s2Frame h2 hq).hmonic.ne_zero 5 (by norm_num)
  have h := s2GradedCoeff_mul_endpoint h2 hq (tooth_key h2 hq) (tooth_key h2 hq) hnz hnz
  rw [dvSideMin_key h2 hq hnz] at h
  exact h

/-- ⚠ **the recorded finding, machine-checked**: the PLAIN-product `graded_mul` field shape
(C130fg) is FALSE at the RP-1 operator — `R₁₀(Φ′·Φ′) = X ≠ 1 = R₅(Φ′)·R₅(Φ′)`.  The
corrected S2 target (RP-4/RP-6) carries the parity factor `X^{(β%2)·(β′%2)}`. -/
theorem tooth_graded_mul_plain_shape_refuted :
    s2GradedRes h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      ≠ s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O)
        * s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) := by
  letI : Field ((s2DepthTwo h2 hq).fld 2) := (s2DepthTwo h2 hq).fldField 2
  rw [tooth_gradedRes_key_sq h2 hq, tooth_gradedRes_key h2 hq, mul_one]
  intro hcontra
  have h := congrArg (fun p => Polynomial.coeff p 1) hcontra
  simp only [Polynomial.coeff_X_one, Polynomial.coeff_one] at h
  norm_num at h

/-! ## Part 10 — RP-2 teeth: cancellation, the derived characteristic, and a NON-VACUOUS
exact-sum instance -/

/-- `dv((C 2)₀) = 2` at the S2 frame. -/
theorem dvHgt_C_two_zero : dvHgt (s2Frame h2 hq) (Polynomial.C (2 : O)) 0
    = ((2 : ℕ) : ℕ∞) := by
  rw [dvHgt, dev_zero_pin,
    show Polynomial.C (2 : O) %ₘ (s2Frame h2 hq).key = Polynomial.C (2 : O) from
      (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
        (by rw [key_eq h2 hq, s2Key_deg]
            exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)),
    show Polynomial.C (2 : O) = Polynomial.C ((2 : O) ^ 1) by rw [pow_one],
    sh_C_pow h2 hq 1]

/-- `h₂(C 2) = 4` in the cleared `ℕ∞` read. -/
theorem dvSupp_C_two : dvSupp (s2Frame h2 hq) (Polynomial.C (2 : O)) 5 2
    = ((4 : ℕ) : ℕ∞) := by
  simp only [dvSupp, Polynomial.natDegree_C, show Finset.range (0 + 1) = {0} from rfl,
    Finset.inf_singleton]
  rw [dvHgt_C_two_zero h2 hq, weight_read]

/-- `Φ′ + Φ′ = C 2 · Φ′` sits at grade `9 = 4 + 5 > 5`: the sum of two exact-grade-5 inputs
is ABOVE grade 5 — the cancellation genre. -/
theorem above_key_add_key :
    S2AboveGrade h2 hq 5 (((s2Frame h2 hq).key : Polynomial O) + (s2Frame h2 hq).key) := by
  have h2key : ((s2Frame h2 hq).key : Polynomial O) + (s2Frame h2 hq).key
      = Polynomial.C (2 : O) * (s2Frame h2 hq).key := by
    have hC2 : Polynomial.C (2 : O) = 1 + 1 := by
      rw [show (2 : O) = 1 + 1 by norm_num, map_add, map_one]
    rw [hC2]
    ring
  refine (S2AboveGrade_iff_dvSupp h2 hq).mpr ?_
  rw [h2key, s2_dvSupp_mul h2 hq, dvSupp_C_two h2 hq, s2_dvSupp_key h2 hq, ← Nat.cast_add]
  exact_mod_cast (by norm_num : (5 : ℕ) < 4 + 5)

/-- **tooth (the cancellation genre fires)**: `R₅(Φ′ + Φ′) = R₅(Φ′) + R₅(Φ′)` through the
STRONG add law — the sum is above grade 5, so its every gate is closed, and additivity holds
because the two on-line reads cancel in `K₂`. -/
theorem tooth_gradedRes_add_cancel :
    s2GradedRes h2 hq 5 (((s2Frame h2 hq).key : Polynomial O) + (s2Frame h2 hq).key)
      = s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O)
        + s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) :=
  s2GradedRes_add_of_le h2 hq (le_dvSupp_of_exact h2 hq (tooth_key h2 hq))
    (le_dvSupp_of_exact h2 hq (tooth_key h2 hq))

/-- **tooth (the derived characteristic)**: `1 + 1 = 0` in `K₂`, DERIVED from the operator
laws alone — the zero law prices `R₅(Φ′ + Φ′) = 0` (grade `9 > 5`), the additive law makes
it `1 + 1` — the machine check that RP-1's zero law and RP-2's add law cohere, and the
operator-level shadow of C130s6's card-2 collapse. -/
theorem tooth_char_two : (1 : (s2DepthTwo h2 hq).fld 2) + 1 = 0 := by
  have h0 : s2GradedRes h2 hq 5
      (((s2Frame h2 hq).key : Polynomial O) + (s2Frame h2 hq).key) = 0 :=
    s2GradedRes_zero_of_above h2 hq (above_key_add_key h2 hq)
  have h1 := tooth_gradedRes_add_cancel h2 hq
  rw [h0, tooth_gradedRes_key h2 hq] at h1
  have h2' := congrArg (fun p => Polynomial.coeff p 0) h1
  simp only [Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_one_zero] at h2'
  exact h2'.symm

omit [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
include h2 in
private theorem four_ne_zero' : (4 : O) ≠ 0 := by
  rw [show (4 : O) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 h2.ne_zero

/-- `dv(4x) = 5` at the S2 frame (`2·v(4) + 1 = 5`, the odd branch). -/
theorem sh_C4X : (s2Frame h2 hq).stageHeight (Polynomial.C (4 : O) * Polynomial.X)
    = ((5 : ℕ) : ℕ∞) := by
  rw [s2_stageHeight_linear h2 hq
    (le_of_eq (Polynomial.natDegree_C_mul_X (4 : O) (four_ne_zero' h2)))]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    mul_zero, mul_one, AddValuation.map_zero]
  rw [show (4 : O) = 2 ^ 2 by norm_num, addVal_two_pow h2,
    C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), min_eq_right le_top, nsmul_eq_mul]
  norm_cast

/-- slot 0 of the `Φ′`-development of `4x` is `4x` itself. -/
theorem dev_C4X_zero : dev (s2Frame h2 hq).key (Polynomial.C (4 : O) * Polynomial.X) 0
    = Polynomial.C (4 : O) * Polynomial.X := by
  rw [dev_zero_pin]
  exact (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [key_eq h2 hq, s2Key_deg]
        exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le (4 : O)) (by norm_num))

/-- `dv((4x)₀) = 5`. -/
theorem dvHgt_C4X_zero : dvHgt (s2Frame h2 hq) (Polynomial.C (4 : O) * Polynomial.X) 0
    = ((5 : ℕ) : ℕ∞) := by
  rw [dvHgt, dev_C4X_zero h2 hq]
  exact sh_C4X h2 hq

/-- `dv((4x)₁) = ⊤` — the development of `4x` stops at slot 0. -/
theorem dvHgt_C4X_one : dvHgt (s2Frame h2 hq) (Polynomial.C (4 : O) * Polynomial.X) 1
    = ⊤ := by
  have hdev : dev (s2Frame h2 hq).key (Polynomial.C (4 : O) * Polynomial.X) 1 = 0 := by
    show ((Polynomial.C (4 : O) * Polynomial.X) /ₘ (s2Frame h2 hq).key)
        %ₘ (s2Frame h2 hq).key = 0
    rw [(Polynomial.divByMonic_eq_zero_iff (s2Frame h2 hq).hmonic).mpr
        (by rw [key_eq h2 hq, s2Key_deg]
            exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le (4 : O)) (by norm_num)),
      Polynomial.zero_modByMonic]
  rw [dvHgt, hdev]
  exact (s2Frame h2 hq).stageHeight_zero

/-- `h₂(4x) = 10` in the cleared `ℕ∞` read: a SECOND grade-10 input, with its line slot at
abscissa `0` — disjoint from `Φ′²`'s slot at abscissa `2`. -/
theorem dvSupp_C4X : dvSupp (s2Frame h2 hq) (Polynomial.C (4 : O) * Polynomial.X) 5 2
    = ((10 : ℕ) : ℕ∞) := by
  simp only [dvSupp, Polynomial.natDegree_C_mul_X (4 : O) (four_ne_zero' h2),
    show Finset.range (1 + 1) = {0, 1} from rfl, Finset.inf_insert, Finset.inf_singleton]
  rw [dvHgt_C4X_zero h2 hq, dvHgt_C4X_one h2 hq,
    C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add, min_eq_left le_top, weight_read]

/-- **tooth**: `h₂(4x) = 10` as an exact grade. -/
theorem tooth_C4X_grade :
    S2ExactGrade h2 hq 10 (Polynomial.C (4 : O) * Polynomial.X) :=
  (S2ExactGrade_iff_dvSupp h2 hq).mpr (dvSupp_C4X h2 hq)

/-- the ϖ-read of `4x` at height 5 is `1` (`digAt 2 2 4 = res 1`). -/
theorem twistRead_five_C4X :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) 5 (Polynomial.C (4 : O) * Polynomial.X)
      = 1 := by
  have hcoeff : (Polynomial.C (4 : O) * Polynomial.X).coeff (5 % 2) = (4 : O) := by
    simp
  rw [s2_twistRead_eq_digAt h2 hq, hcoeff,
    digAt_eq h2 (show (4 : O) = 2 ^ (5 / 2) * 1 by norm_num), map_one, map_one, map_one]

/-- **tooth (eq (11) genre at abscissa 0)**: `R₁₀(4x) = 1` — the grade-10 line's slot-0 read
of `4x`. -/
theorem tooth_gradedRes_C4X :
    s2GradedRes h2 hq 10 (Polynomial.C (4 : O) * Polynomial.X) = 1 := by
  have hgate : S2SlotOnGrade h2 hq 10 (Polynomial.C (4 : O) * Polynomial.X)
      (10 % 2 + 2 * 0) :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨5, dvHgt_C4X_zero h2 hq, by norm_num⟩
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff]
  match t with
  | 0 =>
    rw [Polynomial.coeff_one_zero]
    unfold s2GradedCoeff
    rw [if_pos hgate, show (10 - 5 * (10 % 2 + 2 * 0)) / 2 = 5 by norm_num,
      show 10 % 2 + 2 * 0 = 0 by norm_num, dev_C4X_zero h2 hq]
    exact twistRead_five_C4X h2 hq
  | (t + 1) =>
    rw [s2GradedCoeff_eq_zero_of_natDegree_lt h2 hq
        (by rw [Polynomial.natDegree_C_mul_X (4 : O) (four_ne_zero' h2)]; omega),
      Polynomial.coeff_one]
    simp

/-- **tooth (the exact-sum grade)**: `h₂(Φ′² + 4x) = 10` — the two summands' line slots are
DISJOINT (abscissae 2 and 0), so no residue cancellation is possible and the sum stays at
exact grade 10 even in characteristic 2. -/
theorem tooth_sum_exact :
    S2ExactGrade h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X) := by
  refine (S2ExactGrade_iff_dvSupp h2 hq).mpr (le_antisymm ?_ ?_)
  · -- ≤ 10: the slot-0 weight of the sum
    have hdev0 : dev (s2Frame h2 hq).key
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X) 0
        = Polynomial.C (4 : O) * Polynomial.X := by
      rw [dev_add_of_monic (s2Frame h2 hq).hmonic, dev_key_sq_zero h2 hq, zero_add,
        dev_C4X_zero h2 hq]
    have hhgt : dvHgt (s2Frame h2 hq)
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X) 0 = ((5 : ℕ) : ℕ∞) := by
      rw [dvHgt, hdev0]
      exact sh_C4X h2 hq
    have hterm := C131y.dvSupp_le_term (s2Frame h2 hq)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X) 5 (by norm_num : (0 : ℕ) < 2) 0
    rw [hhgt, weight_read] at hterm
    exact le_trans hterm (le_of_eq (by norm_num))
  · -- 10 ≤: the ultrametric at equal branch values
    have hmin := min_dvSupp_le_dvSupp_add (s2Frame h2 hq) (u := 5)
      (by norm_num : (0 : ℕ) < 2)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      (Polynomial.C (4 : O) * Polynomial.X)
    rw [s2_dvSupp_key_sq h2 hq, dvSupp_C4X h2 hq, min_self] at hmin
    exact hmin

/-- **tooth (the FIELD-shape add law fires non-vacuously, with the values live)**:
`R₁₀(Φ′² + 4x) = X + 1 = R₁₀(Φ′²) + R₁₀(4x)` — an exact + exact + exact-sum instance
(disjoint line slots, so characteristic 2 cannot cancel it), through the published-shape
`s2GradedRes_add` itself. -/
theorem tooth_gradedRes_add_exact :
    s2GradedRes h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)
      = Polynomial.X + 1 := by
  rw [s2GradedRes_add h2 hq (tooth_key_sq h2 hq) (tooth_C4X_grade h2 hq)
      (tooth_sum_exact h2 hq),
    tooth_gradedRes_key_sq h2 hq, tooth_gradedRes_C4X h2 hq]

end S2

end Uniformity.Density.Tower.C130rp2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp2.le_dvHgt_of_le_dvSupp
#print axioms Uniformity.Density.Tower.C130rp2.slotRes_zero
#print axioms Uniformity.Density.Tower.C130rp2.twistRead_zero
#print axioms Uniformity.Density.Tower.C130rp2.slotRes_add_of_le
#print axioms Uniformity.Density.Tower.C130rp2.twistRead_add_of_le
#print axioms Uniformity.Density.Tower.C130rp2.twistRead_eq_zero_of_lt
#print axioms Uniformity.Density.Tower.C130rp2.dev_mul_endpoint_split
#print axioms Uniformity.Density.Tower.C130rp2.le_dvSupp_of_exact
#print axioms Uniformity.Density.Tower.C130rp2.le_dvSupp_of_above
#print axioms Uniformity.Density.Tower.C130rp2.s2SlotOnGrade_iff_dvOnSide
#print axioms Uniformity.Density.Tower.C130rp2.s2GradedCoeff_eq_twistRead_of_le
#print axioms Uniformity.Density.Tower.C130rp2.s2GradedCoeff_add
#print axioms Uniformity.Density.Tower.C130rp2.s2GradedRes_add_of_le
#print axioms Uniformity.Density.Tower.C130rp2.s2GradedRes_add
#print axioms Uniformity.Density.Tower.C130rp2.s2_stageLetter_eq_one
#print axioms Uniformity.Density.Tower.C130rp2.slotIdx_eq
#print axioms Uniformity.Density.Tower.C130rp2.twistExp_eq
#print axioms Uniformity.Density.Tower.C130rp2.slotWindow_eq
#print axioms Uniformity.Density.Tower.C130rp2.s2_slotRes_eq_digAt
#print axioms Uniformity.Density.Tower.C130rp2.s2_twistRead_eq_slotRes
#print axioms Uniformity.Density.Tower.C130rp2.s2_twistRead_eq_digAt
#print axioms Uniformity.Density.Tower.C130rp2.s2_twistRead_mul_modByMonic
#print axioms Uniformity.Density.Tower.C130rp2.s2_twistRead_dev_mul_endpoint
#print axioms Uniformity.Density.Tower.C130rp2.s2GradedCoeff_mul_endpoint
#print axioms Uniformity.Density.Tower.C130rp2.dev_X_zero
#print axioms Uniformity.Density.Tower.C130rp2.dvHgt_X_zero
#print axioms Uniformity.Density.Tower.C130rp2.dvOnSide_X_zero
#print axioms Uniformity.Density.Tower.C130rp2.dvSideMin_X
#print axioms Uniformity.Density.Tower.C130rp2.dvHgt_key_zero
#print axioms Uniformity.Density.Tower.C130rp2.dvOnSide_key_one
#print axioms Uniformity.Density.Tower.C130rp2.dvSideMin_key
#print axioms Uniformity.Density.Tower.C130rp2.tooth_gradedRes_X
#print axioms Uniformity.Density.Tower.C130rp2.tooth_endpoint_mixed
#print axioms Uniformity.Density.Tower.C130rp2.tooth_endpoint_carry
#print axioms Uniformity.Density.Tower.C130rp2.tooth_graded_mul_plain_shape_refuted
#print axioms Uniformity.Density.Tower.C130rp2.dvHgt_C_two_zero
#print axioms Uniformity.Density.Tower.C130rp2.dvSupp_C_two
#print axioms Uniformity.Density.Tower.C130rp2.above_key_add_key
#print axioms Uniformity.Density.Tower.C130rp2.tooth_gradedRes_add_cancel
#print axioms Uniformity.Density.Tower.C130rp2.tooth_char_two
#print axioms Uniformity.Density.Tower.C130rp2.sh_C4X
#print axioms Uniformity.Density.Tower.C130rp2.dev_C4X_zero
#print axioms Uniformity.Density.Tower.C130rp2.dvHgt_C4X_zero
#print axioms Uniformity.Density.Tower.C130rp2.dvHgt_C4X_one
#print axioms Uniformity.Density.Tower.C130rp2.dvSupp_C4X
#print axioms Uniformity.Density.Tower.C130rp2.tooth_C4X_grade
#print axioms Uniformity.Density.Tower.C130rp2.twistRead_five_C4X
#print axioms Uniformity.Density.Tower.C130rp2.tooth_gradedRes_C4X
#print axioms Uniformity.Density.Tower.C130rp2.tooth_sum_exact
#print axioms Uniformity.Density.Tower.C130rp2.tooth_gradedRes_add_exact

end AxCheck
