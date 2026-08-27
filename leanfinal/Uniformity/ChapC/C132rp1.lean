/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp0
import Uniformity.ChapC.C130rp8

/-!
# Uniformity.ChapC.C132rp1 — the μ₃ grade-line gate and recursive coefficient (μ₃ campaign, node M3-RP1)

**[M3-RP1, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP1):
the grade-line gate `2·μ₂(A_s) + 21·s = β` and the μ₃ coefficient read — the campaign's
GENUINELY-NEW μ₂/`composedKey` interface: the coefficient of the (future, M3-RP2) μ₃ graded
residual is a RECURSIVE read through the LANDED μ₂ graded/normalized operators
(`s2GradedRes`, C130rp1; `s2NormRes`, C130rp8), not a frame-level ϖ-read.  This node lands
the gate, the FGMN ε-factor, the coefficient, and the proof-independence pins; the assembled
polynomial operator, its master law and its zero-above law are M3-RP2's.

## The FGMN dictionary (published Def 3.12/3.13 at the μ₃ numerals)

Published Definition 3.13 (`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`, p. 16)
defines, for `r > 0` and `α ∈ Γ(μ)`, the `j`-th coefficient of `R_{r,α}(g)` as

`ε_{r−1}(α_j) · R_{r−1,α_j}(a_{s_j})(z_{r−1})`,   `s_j = s_r(α) + j·e_r`,  `α_j = α − s_j μ(φ_r)`,

read off the `φ_r`-expansion `g = Σ a_s φ_r^s`; eq (10) (ibid.) pins that the slot `s`
contributes iff `s = s_j` AND `μ_{r−1}(a_s) = α_j` — i.e. iff the point `Q_s` sits ON the
grade-`α` line.  At the μ₃ occurrence (paper `r = 3`, repo depth `2`) with the S2 numerals
`(e₃, h₃) = (2, 21)` and the DEC3R full-current clearing `β = e(μ₃)α` (campaign §2, the
OPEN-DICT-2 decision), the line membership becomes the NATURAL equation

* **the gate** `S2Mu3SlotOnGrade β g s`: `2·μ₂(A_s) + 21·s = β`, where `A_s = dev Φ₂ g s`
  is the `Φ₂`-development coefficient and `μ₂(A_s)` is the LANDED cleared μ₂ value — the
  term shape of `dv2Supp … 21 2`, the very support `s2Hgt₃` (C132nv1) minimizes, so the
  gate's level sets are M3-RP0's `S2Mu3ExactGrade`/`S2Mu3AboveGrade` (the design constraint
  RP-2..RP-6 need).  Per the MADJ layering verdict (`runs/wave-b/verdict_MADJ.md`): the
  OUTER weights are `(u₃, ℓ₃) = (21, 2)`; the INNER value `μ₂(A_s)` is `dv2Pin L Φ₂ g s`,
  whose own `(5, 2)` structure is sealed inside the level datum `L` — the two must not be
  conflated, and are not: `s2Mu3SlotOnGrade_iff_hgt₂` displays the inner read as the landed
  `s2Hgt₂` itself.
* published Def 3.12's line parameterization at `i = 3`: the abscissae on the `β`-line are
  `s_t = s₃(β) + t·e₃` with `s₃(β)` the unique `0 ≤ s < e₃ = 2` solving
  `u·2 + s·21 = β`, i.e. `s₃(β) = β % 2` (certified: `s2Mu3_def312_level3`); the `t`-th
  abscissa carries the `y^t` monomial, so a slot at abscissa `s` lands at `y`-power `⌊s/2⌋`
  (`s2Mu3Coeff_slot`).
* the on-line inner grade at abscissa `s` is `m = (β − 21·s)/2` (the line equation solved
  for `μ₂(A_s)`; `ℕ`-truncated in the definition, pinned to the true value by the gate,
  `s2Mu3Coeff_eq_eval`) — the cleared level-2 integer coordinate of Def 3.13's
  `α_j ∈ Γ₂`, and on the gate the development coefficient has EXACTLY that μ₂ grade
  (`s2Mu3SlotOnGrade_inner_exact` — eq (10)'s second conjunct, so the inner operator is
  read precisely on its FGMN-specified domain `𝒫_{α_j}`).

## The ε-factor, and the S2 collapse (the derivation this node DOES make)

Published Definition 3.12 (ibid., p. 16) defines `ε_i(α) = (z_i)^{ℓ_i′·s_i(α) − ℓ_i·u_i(α)}
∈ 𝔽_{i+1}^*`, with `ℓ_i·h_i + ℓ_i′·e_i = 1`, `0 ≤ ℓ_i < e_i` (§3.3, p. 15).  At the μ₃
coefficient the relevant index is `i = 2` with `(e₂, h₂) = (2, 5)`, so `(ℓ₂, ℓ₂′) = (1, −2)`
(`s2Mu3_bezout_level2`), `s₂(m) = m % 2`, `u₂(m) = (m − 5·(m % 2))/2` in the cleared
coordinate `m = e(μ₂)α_j` (`s2Mu3_def312_level2`), and the transcribed exponent is
`s2Mu3EpsExp m = −2·(m % 2) − u₂(m)` (`s2Mu3EpsExp_eq`).

**The collapse.**  At S2 every stage has `f = 1` over the 2-element residue field, so
`𝔽₃ = (s2DepthTwo h2 hq).fld 2` has exactly two elements (`C130s6.s2Fld₂_card`) and its
unit group is trivial: every nonzero scalar equals `1` (`s2Fld₂_eq_one_of_ne_zero`).
Published p. 15 remarks `z_i ≠ 0` for `i > 0`; here `i = 2 > 0`, so `z₂ ∈ 𝔽₃^*` and
therefore `z₂ = 1` is FORCED — whatever the (not-landed, OPEN-LETTERS) concrete letter is.
Consequently, and PROVED here for every nonzero letter `z`:

* every ε-value is `1` (`s2Mu3EpsOf_eq_one`: `z^k = 1` for all `k : ℤ`),
* the Def 3.13 evaluation at `z₂` is evaluation at `1` (`s2Mu3_eval_letter_pinned`), and
* evaluation at `z₂ = 1` cannot distinguish the μ₂ GRADED read from the NORMALIZED one:
  the strip `R_{2,α} = y^{j₀}·R₂` (C130rp8's reconstruction) is invisible at `y = 1`
  (`s2Mu3Coeff_eq_eval_normRes`) — the row's "graded/normalized" two-read collapse.

So the definition `s2Mu3Coeff` displays Def 3.13's coefficient with the collapsed values
(`ε = 1`, evaluation at `1`), and `s2Mu3Coeff_letter_display` re-expands it to the literal
`ε₂(α_j)·R_{2,α_j}(A_s)(z₂)` shape for EVERY candidate nonzero letter — the choice of `z₂`
is provably invisible.

## Faithfulness note — OPEN-RP1-TRANSPORT (review queue; campaign §8)

The transport claim "repo coefficient = published Def 3.13 coefficient" splits into legs
with DIFFERENT statuses; only the honest split is claimed:

1. **DERIVED HERE (Lean theorems):** the μ₃-level ε-factor and the `z₂`-evaluation collapse
   to `1` at S2 for every nonzero letter, and graded-vs-normalized inner reads agree after
   that evaluation.  The ONE un-formalized leg of this derivation is the paper's own p. 15
   remark `z₂ ≠ 0` (`i = 2 > 0`) — consumed as the `hz : z ≠ 0` hypothesis of the display
   pins, never silently.
2. **INHERITED, NOT RE-DERIVED:** the identification of the landed μ₂ operator
   `s2GradedRes` with the published `R_{2,α}` is C130rp1's standing recorded trust boundary
   (the `EFF.HE6.58`/C.22/C.25 ϖ-read dictionary).  Whether the LANDED μ₂ normalized read
   already carries the paper's level-2 ε₁-normalization is EXACTLY the two-read question of
   `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:489-523` (LEMMA GENTOW2-B′'s per-grade
   unit `u(β)`); this node does NOT assert it — per the campaign's OPEN-RP1-TRANSPORT
   discipline, that remains the flagged open for the review queue.
3. **NOT LANDED:** a concrete `z₂` (OPEN-LETTERS) and the abstract field identification
   `F₃ ≅ fld 2` (OPEN-DICT-3-MU3).  Neither is needed by any theorem here, BECAUSE of the
   collapse in leg 1.

## What this node does NOT claim (honesty scope)

* No assembled polynomial operator `s2Mu3GradedRes`, no master coefficient law, no
  zero-above law at the polynomial level: M3-RP2 (the coefficient-level zero laws below are
  RP-2's inputs, not its outputs).
* No additivity/multiplicativity (published Cor 4.12): M3-RP3/RP5/RP6; the carry arithmetic
  is M3-RP4.
* No normalization of the μ₃ operator itself (published Def 3.15): M3-RP8.
* The μ₂-level read faithfulness stays an OPEN (leg 2 above), and no theorem below
  quietly consumes it: every statement is about the repo operators.

**DEPENDS.** C132rp0 (`S2Mu3AboveGrade`, `S2Mu3AboveGrade_iff_dv2Supp`) · C132nv1
(`s2Φ₂_monic`, `s2Φ₂_natDegree`, `s2Hgt₃_Φ₂`) · C132nv0 (`dv2Pin_top_of_gt`) · C.11
(`dv2Hgt`, `dv2Pin`, `dv2Supp`) · C130rp8 (`s2NormRes`, `s2NormRes_mul_X_pow_of_exact`) ·
C130rp1 (`s2GradedRes`, `s2GradedRes_coeff`, `s2GradedCoeff_eq_twistRead`,
`s2GradedCoeff_eq_zero_of_grade_lt`, `S2SlotOnGrade`, `s2SlotOnGrade_iff`,
`twistRead_zero_one`) · C130rp0 (`S2ExactGrade`, `S2ExactGrade_iff_dvSupp`) · C130s6
(`s2Hgt₂` + `s2Hgt₂_eq_dvSupp`/`s2Hgt₂_eq_dv2Hgt`/`s2Hgt₂_one`, `s2Fld₂_card`, `toZ` laws)
· C35b (`key_eq`, `s2Key_deg`, `sh_C`) · C118a (`smul_top_pos`) · B.02/B35a (`dev`,
`dev_mul_pow`) · C.06 (`dvHgt`) · C83 (`DeepTower.fldField` instance).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch; the transport OPEN is documented above, not silently consumed.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — published Def 3.12's grade-line arithmetic, certified (pure `ℤ`)

The unique-solution pins for Def 3.12's `u_i(α)·e_i + s_i(α)·h_i = e(μ_i)α`, `0 ≤ s_i < e_i`
at both S2 levels: `i = 3` (`(e₃, h₃) = (2, 21)`, the gate's abscissa encoding) and `i = 2`
(`(e₂, h₂) = (2, 5)`, the ε-exponent's data), plus §3.3's Bézout pair at `i = 2`. -/

/-- **Def 3.12 at `i = 3`, uniqueness** (`(e₃, h₃) = (2, 21)`): the unique solution of
`u·2 + s·21 = β`, `0 ≤ s < 2` is `s₃(β) = β % 2`, `u₃(β) = (β − 21·(β % 2))/2` — the
abscissa parameterization `β % 2 + 2t` below drops nothing and invents nothing. -/
theorem s2Mu3_def312_level3 (β : ℕ) (u s : ℤ) (h : u * 2 + s * 21 = (β : ℤ))
    (hs0 : 0 ≤ s) (hs2 : s < 2) :
    s = ((β % 2 : ℕ) : ℤ) ∧ u = ((β : ℤ) - 21 * ((β % 2 : ℕ) : ℤ)) / 2 := by omega

/-- **Def 3.12 at `i = 2`, uniqueness** (`(e₂, h₂) = (2, 5)`): the unique solution of
`u·2 + s·5 = m`, `0 ≤ s < 2` is `s₂(m) = m % 2`, `u₂(m) = (m − 5·(m % 2))/2` — the data
entering the ε-exponent. -/
theorem s2Mu3_def312_level2 (m : ℕ) (u s : ℤ) (h : u * 2 + s * 5 = (m : ℤ))
    (hs0 : 0 ≤ s) (hs2 : s < 2) :
    s = ((m % 2 : ℕ) : ℤ) ∧ u = ((m : ℤ) - 5 * ((m % 2 : ℕ) : ℤ)) / 2 := by omega

/-- **Def 3.12 at `i = 2`, existence**: the displayed pair does solve the equation with the
required range constraint (so `s2Mu3_def312_level2` is not vacuous). -/
theorem s2Mu3_def312_level2_exists (m : ℕ) :
    (((m : ℤ) - 5 * ((m % 2 : ℕ) : ℤ)) / 2) * 2 + ((m % 2 : ℕ) : ℤ) * 5 = (m : ℤ)
      ∧ 0 ≤ ((m % 2 : ℕ) : ℤ) ∧ ((m % 2 : ℕ) : ℤ) < 2 := by omega

/-- **§3.3's Bézout pair at `i = 2`**: `(ℓ₂, ℓ₂′) = (1, −2)` solves `ℓ₂·h₂ + ℓ₂′·e₂ = 1`
with `0 ≤ ℓ₂ < e₂` at `(e₂, h₂) = (2, 5)` — the pair the ε-exponent transcribes. -/
theorem s2Mu3_bezout_level2 :
    (1 : ℤ) * 5 + (-2) * 2 = 1 ∧ (0 : ℤ) ≤ 1 ∧ (1 : ℤ) < 2 := by norm_num

/-! ## Part 1 — ★ the μ₃ grade-line gate `S2Mu3SlotOnGrade`

The `s`-th `Φ₂`-development slot of `g` sits EXACTLY on the μ₃ grade-`β` line: the equation
is `dv2Supp`'s own term shape at the S2 outer side `(u₃, ℓ₃) = (21, 2)` (C.11), so line
membership is literally "this slot's term attains the value `β`".  The inner value
`dv2Pin L Φ₂ g s` IS the landed μ₂ read of the development coefficient (the MADJ layering:
its `(5, 2)` structure lives inside `L`, never as an outer argument). -/

/-- ★ **the μ₃ grade-line gate**: `2·μ₂(A_s) + 21·s = β` — slot `s` of the
`Φ₂`-development of `g` sits exactly on the μ₃ grade-`β` line (published Def 3.13's
`Q_s ∈ L_α` membership, eq (10), in the repo's cleared `ℕ∞` reads at the DEC3R
full-current coordinate). -/
def S2Mu3SlotOnGrade (β : ℕ) (g : Polynomial O) (s : ℕ) : Prop :=
  2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g s
    + ((21 * s : ℕ) : ℕ∞) = (β : ℕ∞)

/-- **the gate normal form**: line membership is a finite inner value plus a NATURAL line
equation `2m + 21s = β` — no `ℕ∞` arithmetic survives.  (The RP-2..RP-6 consumable
shape, mirroring μ₂'s `s2SlotOnGrade_iff`.) -/
theorem s2Mu3SlotOnGrade_iff {β s : ℕ} {g : Polynomial O} :
    S2Mu3SlotOnGrade h2 hq β g s ↔
      ∃ m : ℕ, dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g s
          = (m : ℕ∞) ∧ 2 * m + 21 * s = β := by
  unfold S2Mu3SlotOnGrade
  constructor
  · intro h
    have hne : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g s ≠ ⊤ := by
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

/-- the anti-drift tie between the two level-2 spellings: C.11's `dv2Hgt` at the landed S2
level datum IS the raw μ₂ support `dvSupp … 5 2` — both are `rfl`-pinned to `s2Hgt₂`
(C130s6), so the equality is inherited, not re-derived. -/
theorem dv2Hgt_eq_dvSupp (A : Polynomial O) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) A = dvSupp (s2Frame h2 hq) A 5 2 :=
  C130s6.toZ_inj (by rw [← s2Hgt₂_eq_dv2Hgt h2 hq, s2Hgt₂_eq_dvSupp h2 hq])

/-- **the campaign display form** (`MU3_CAMPAIGN` §2.3's "outer coefficients valued by the
landed μ₂ operator"): the gate reads the INNER value through the LANDED μ₂ table `s2Hgt₂`
itself — `2·μ₂(A_s) + 21·s = β` verbatim, with `μ₂ = s2Hgt₂`. -/
theorem s2Mu3SlotOnGrade_iff_hgt₂ {β s : ℕ} {g : Polynomial O} :
    S2Mu3SlotOnGrade h2 hq β g s ↔
      ∃ m : ℕ, s2Hgt₂ h2 hq (dev (s2DepthTwoKeyAt h2 hq 2) g s) = ((m : ℤ) : WithTop ℤ)
        ∧ 2 * m + 21 * s = β := by
  rw [s2Mu3SlotOnGrade_iff h2 hq]
  constructor
  · rintro ⟨m, hm, hβ⟩
    refine ⟨m, ?_, hβ⟩
    rw [dv2Pin] at hm
    rw [s2Hgt₂_eq_dv2Hgt h2 hq, hm]
    exact C130s6.toZ_coe m
  · rintro ⟨m, hm, hβ⟩
    refine ⟨m, ?_, hβ⟩
    rw [dv2Pin]
    apply C130s6.toZ_inj
    rw [← s2Hgt₂_eq_dv2Hgt h2 hq, hm]
    exact (C130s6.toZ_coe m).symm

/-- **parity of on-line slots** (published Def 3.12's `s₃(β) = β % 2` at
`(e₃, h₃) = (2, 21)`): every slot on the μ₃ grade-`β` line has the grade's parity.  With
`s2Mu3Coeff_slot` below this pins that the `β % 2 + 2t` abscissa encoding drops no on-line
slot. -/
theorem s2Mu3SlotOnGrade_parity {β s : ℕ} {g : Polynomial O}
    (h : S2Mu3SlotOnGrade h2 hq β g s) : s % 2 = β % 2 := by
  obtain ⟨m, -, hβ⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp h
  omega

/-- ★ **the inner exact-grade pin** (eq (10)'s second conjunct `μ₂(a_s) = α_j`): on the
gate, the development coefficient `A_s` has EXACTLY the on-line inner μ₂ grade
`(β − 21s)/2` — the inner operator below is read precisely on its FGMN-specified domain
`𝒫_{α_j}` (M3-RP5's consumable). -/
theorem s2Mu3SlotOnGrade_inner_exact {β s : ℕ} {g : Polynomial O}
    (h : S2Mu3SlotOnGrade h2 hq β g s) :
    S2ExactGrade h2 hq ((β - 21 * s) / 2) (dev (s2DepthTwoKeyAt h2 hq 2) g s) := by
  obtain ⟨m, hm, hβ⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp h
  have hdiv : (β - 21 * s) / 2 = m := by omega
  rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq] at hm
  rw [hdiv]
  exact (S2ExactGrade_iff_dvSupp h2 hq).mpr hm

/-- an on-line slot bounds the cleared μ₃ support: `dv2Supp … 21 2` is the inf of the very
terms the gate equates to `β`.  (The bridge from the gate to M3-RP0's `S2Mu3AboveGrade`
normal form — M3-RP2's zero-above input.) -/
theorem dv2Supp_le_of_mu3SlotOnGrade {β s : ℕ} {g : Polynomial O}
    (h : S2Mu3SlotOnGrade h2 hq β g s) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 ≤ (β : ℕ∞) := by
  obtain ⟨m, hm, hβ⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp h
  have hs : s ≤ g.natDegree := by
    by_contra hs
    rw [dv2Pin_top_of_gt ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) g (not_le.mp hs)] at hm
    exact absurd hm (by exact WithTop.top_ne_coe)
  have hle : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
      ≤ 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g s
        + ((21 : ℕ∞) * (s : ℕ∞)) := by
    rw [dv2Supp]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  have heq : 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g s
      + ((21 : ℕ∞) * (s : ℕ∞)) = (β : ℕ∞) := by
    rw [hm, nsmul_eq_mul, ← hβ]
    push_cast
    ring
  rw [heq] at hle
  exact hle

/-! ## Part 2 — the FGMN ε-factor, and its S2 collapse

Published Def 3.12's `ε₂(α) = z₂^{ℓ₂′·s₂(α) − ℓ₂·u₂(α)} ∈ 𝔽₃^*`, transcribed at the S2
numerals in the cleared coordinate `m = e(μ₂)α`, PARAMETRIC in the letter `z₂` (the repo
lands no concrete `z₂` — OPEN-LETTERS); then the two-element-field collapse proving the
letter invisible. -/

/-- **Def 3.12's ε-exponent at the S2 level-2 numerals**: `ℓ₂′·s₂(m) − ℓ₂·u₂(m)` with
`(ℓ₂, ℓ₂′) = (1, −2)` (`s2Mu3_bezout_level2`), `s₂(m) = m % 2`, `u₂(m) = (m − 5·(m % 2))/2`
(`s2Mu3_def312_level2`). -/
def s2Mu3EpsExp (m : ℕ) : ℤ :=
  (-2) * ((m % 2 : ℕ) : ℤ) - ((m : ℤ) - 5 * ((m % 2 : ℕ) : ℤ)) / 2

/-- display pin: the exponent is LITERALLY `ℓ₂′·s₂(m) − ℓ₂·u₂(m)` at `(ℓ₂, ℓ₂′) = (1, −2)`
— the transcription makes no simplification. -/
theorem s2Mu3EpsExp_eq (m : ℕ) :
    s2Mu3EpsExp m
      = (-2) * ((m % 2 : ℕ) : ℤ) - 1 * (((m : ℤ) - 5 * ((m % 2 : ℕ) : ℤ)) / 2) := by
  unfold s2Mu3EpsExp
  ring

/-- **the ε-factor, parametric in the letter**: `ε₂(m) = z^{s2Mu3EpsExp m}` for a candidate
letter `z` (published Def 3.12 verbatim; the collapse below shows every nonzero choice
gives `1`). -/
noncomputable def s2Mu3EpsOf (z : (s2DepthTwo h2 hq).fld 2) (m : ℕ) :
    (s2DepthTwo h2 hq).fld 2 :=
  z ^ s2Mu3EpsExp m

/-- **the two-element collapse** (public copy of the corpus's private-copy pattern —
`C130s6.fld₂_eq_one_of_ne_zero`, `C130rp11.s2Fld2_eq_one_of_ne_zero` are `private`): in the
2-element field `K₂ = fld 2` (`s2Fld₂_card`), every nonzero scalar is `1`. -/
theorem s2Fld₂_eq_one_of_ne_zero {c : (s2DepthTwo h2 hq).fld 2} (hc : c ≠ 0) : c = 1 := by
  haveI : Finite ((s2DepthTwo h2 hq).fld 2) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₂_card h2 hq]; norm_num)
  have hu : Nat.card ((s2DepthTwo h2 hq).fld 2)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₂_card h2 hq]
  haveI : Subsingleton ((s2DepthTwo h2 hq).fld 2)ˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : ((s2DepthTwo h2 hq).fld 2)ˣ) : (s2DepthTwo h2 hq).fld 2) :=
        (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- ★ **the ε-collapse** (the derivation): for EVERY nonzero letter `z` (published p. 15:
`z_i ≠ 0` for `i > 0`; here `i = 2`) and every grade, the ε-factor is `1` — the letter and
the exponent are both provably invisible at S2. -/
theorem s2Mu3EpsOf_eq_one {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0) (m : ℕ) :
    s2Mu3EpsOf h2 hq z m = 1 := by
  unfold s2Mu3EpsOf
  rw [s2Fld₂_eq_one_of_ne_zero h2 hq hz, one_zpow]

/-- **the collapsed ε-operator** used by the coefficient definition: the common value `1`
of `s2Mu3EpsOf z ·` over all admissible letters (`s2Mu3Eps_eq_epsOf`). -/
noncomputable def s2Mu3Eps (_ : ℕ) : (s2DepthTwo h2 hq).fld 2 := 1

/-- the collapsed operator computes. -/
theorem s2Mu3Eps_eq_one (m : ℕ) : s2Mu3Eps h2 hq m = 1 := rfl

/-- **letter independence of the collapsed operator**: `s2Mu3Eps` IS `s2Mu3EpsOf z` for
every nonzero letter `z` — using the collapsed value in the definition makes no choice. -/
theorem s2Mu3Eps_eq_epsOf {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0) (m : ℕ) :
    s2Mu3Eps h2 hq m = s2Mu3EpsOf h2 hq z m :=
  (s2Mu3EpsOf_eq_one h2 hq hz m).symm

/-- published Def 3.12's codomain pin: the ε-factor is a UNIT (`ε₂(α) ∈ 𝔽₃^*`). -/
theorem s2Mu3Eps_ne_zero (m : ℕ) : s2Mu3Eps h2 hq m ≠ 0 :=
  one_ne_zero

/-- **the evaluation-point pin**: evaluation of ANY polynomial over `K₂` at any nonzero
scalar (in particular at whatever `z₂` is) equals evaluation at `1` — Def 3.13's
`(z_{r−1})`-evaluation is forced onto `1` at S2. -/
theorem s2Mu3_eval_letter_pinned {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0)
    (p : Polynomial ((s2DepthTwo h2 hq).fld 2)) :
    Polynomial.eval z p = Polynomial.eval 1 p := by
  rw [s2Fld₂_eq_one_of_ne_zero h2 hq hz]

/-! ## Part 3 — ★ the μ₃ recursive coefficient `s2Mu3Coeff`, and its pins

The `t`-th `y`-coefficient of the (future, M3-RP2) μ₃ graded residual: at the `t`-th
abscissa `β % 2 + 2t` of the grade-`β` line, published Def 3.13's
`ε₂(α_j)·R_{2,α_j}(A_s)(z₂)` — with the collapsed values `ε = 1`, `z₂ = 1` (Part 2), and
the landed μ₂ operator `s2GradedRes` at the on-line inner grade `(β − 21s)/2` as
`R_{2,α_j}`; gated by line membership, junk-`0` off the line. -/

open Classical in
/-- ★ **the μ₃ recursive coefficient** (published Def 3.13's `r > 0` coefficient at the μ₃
numerals): the landed μ₂ graded read of the `Φ₂`-development slot at the `t`-th abscissa
`β % 2 + 2t` of the grade-`β` line, at the on-line inner grade `(β − 21s)/2`, evaluated at
the collapsed letter and multiplied by the collapsed ε-factor, if the slot is on the line;
`0` otherwise.  Total; every collapsed/truncated choice is pinned by the Part 2/3 pins. -/
noncomputable def s2Mu3Coeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2DepthTwo h2 hq).fld 2 :=
  if S2Mu3SlotOnGrade h2 hq β g (β % 2 + 2 * t) then
    s2Mu3Eps h2 hq ((β - 21 * (β % 2 + 2 * t)) / 2)
      * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2GradedRes h2 hq ((β - 21 * (β % 2 + 2 * t)) / 2)
            (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)))
  else 0

open Classical in
/-- ★ **the letter-display pin** (proof-independence pin 1 — the Def 3.13 shape): for
EVERY nonzero candidate letter `z`, the coefficient equals the LITERAL published display
`ε₂(α_j) · R_{2,α_j}(A_s)(z₂)` with `z₂ := z` — the collapsed values in the definition
are not a choice. -/
theorem s2Mu3Coeff_letter_display {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0)
    (β : ℕ) (g : Polynomial O) (t : ℕ) :
    s2Mu3Coeff h2 hq β g t =
      if S2Mu3SlotOnGrade h2 hq β g (β % 2 + 2 * t) then
        s2Mu3EpsOf h2 hq z ((β - 21 * (β % 2 + 2 * t)) / 2)
          * Polynomial.eval z
              (s2GradedRes h2 hq ((β - 21 * (β % 2 + 2 * t)) / 2)
                (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)))
      else 0 := by
  unfold s2Mu3Coeff
  rw [s2Mu3EpsOf_eq_one h2 hq hz, s2Mu3Eps_eq_one, s2Mu3_eval_letter_pinned h2 hq hz]

/-- **the true-height pin** (proof-independence pin 2, the `dv2Res_pinned` genre): on the
gate, the `ℕ`-truncated inner grade `(β − 21s)/2` IS the slot's actual μ₂ value — the
coefficient may be read at any caller-supplied inner-value pin (and the collapsed `ε = 1`
strips). -/
theorem s2Mu3Coeff_eq_eval {β t m : ℕ} {g : Polynomial O}
    (hgate : S2Mu3SlotOnGrade h2 hq β g (β % 2 + 2 * t))
    (hm : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (β % 2 + 2 * t) = (m : ℕ∞)) :
    s2Mu3Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2GradedRes h2 hq m (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t))) := by
  obtain ⟨m', hm', hβ⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
  have hmm : m = m' := by
    rw [hm] at hm'
    exact_mod_cast hm'
  subst hmm
  have hk : (β - 21 * (β % 2 + 2 * t)) / 2 = m := by omega
  unfold s2Mu3Coeff
  rw [if_pos hgate, hk, s2Mu3Eps_eq_one, one_mul]

/-- ★ **the graded/normalized two-read collapse** (proof-independence pin 3 — the row's
"graded/normalized read"): on the gate, reading the inner slot through the landed μ₂
NORMALIZED operator `s2NormRes` (C130rp8) gives the SAME coefficient — the strip
`R_{2,α} = y^{j₀}·R₂` (C130rp8's reconstruction at the inner exact grade, supplied by
`s2Mu3SlotOnGrade_inner_exact`) is invisible at the collapsed evaluation point `1`. -/
theorem s2Mu3Coeff_eq_eval_normRes {β t m : ℕ} {g : Polynomial O}
    (hgate : S2Mu3SlotOnGrade h2 hq β g (β % 2 + 2 * t))
    (hm : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (β % 2 + 2 * t) = (m : ℕ∞)) :
    s2Mu3Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2NormRes h2 hq (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t))) := by
  rw [s2Mu3Coeff_eq_eval h2 hq hgate hm]
  have hex : S2ExactGrade h2 hq m (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)) := by
    have h := s2Mu3SlotOnGrade_inner_exact h2 hq hgate
    obtain ⟨m', hm', hβ⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
    have hmm : m = m' := by
      rw [hm] at hm'
      exact_mod_cast hm'
    have hk : (β - 21 * (β % 2 + 2 * t)) / 2 = m := by omega
    rwa [hk] at h
  rw [← s2NormRes_mul_X_pow_of_exact h2 hq hex, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, mul_one]

/-- **slot completeness** (proof-independence pin 4): every on-line slot `s` IS read, at
`y`-power `s / 2` (published eq (11)'s `⌊s/e₃⌋`), with the on-line inner grade — the
abscissa encoding `β % 2 + 2t` is exhaustive on the line. -/
theorem s2Mu3Coeff_slot {β s : ℕ} {g : Polynomial O}
    (h : S2Mu3SlotOnGrade h2 hq β g s) :
    s2Mu3Coeff h2 hq β g (s / 2) =
      s2Mu3Eps h2 hq ((β - 21 * s) / 2)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
            (s2GradedRes h2 hq ((β - 21 * s) / 2)
              (dev (s2DepthTwoKeyAt h2 hq 2) g s)) := by
  have hpar := s2Mu3SlotOnGrade_parity h2 hq h
  have hs : β % 2 + 2 * (s / 2) = s := by omega
  unfold s2Mu3Coeff
  rw [hs, if_pos h]

/-- vanishing off finite inner values: a `⊤`-valued slot (in particular any slot past the
`Φ₂`-development) is never on a line, so its coefficient is `0`. -/
theorem s2Mu3Coeff_eq_zero_of_dv2Pin_top {β t : ℕ} {g : Polynomial O}
    (h : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (β % 2 + 2 * t) = ⊤) :
    s2Mu3Coeff h2 hq β g t = 0 := by
  unfold s2Mu3Coeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, hm, -⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
  rw [h] at hm
  exact WithTop.top_ne_coe hm

/-- **finite support, the natDegree bound** (the `Φ₂`-development is finite): coefficients
whose abscissa passes `natDegree g` vanish — nv0's `dv2Pin_top_of_gt` makes the slot value
`⊤`. -/
theorem s2Mu3Coeff_eq_zero_of_natDegree_lt {β t : ℕ} {g : Polynomial O}
    (h : g.natDegree < β % 2 + 2 * t) :
    s2Mu3Coeff h2 hq β g t = 0 :=
  s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq
    (dv2Pin_top_of_gt ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) g h)

/-- **finite support, the grade bound**: the grade-`β` line meets only abscissae with
`21s ≤ β`, so coefficients past `t = β` (indeed past `β/42`) vanish. -/
theorem s2Mu3Coeff_eq_zero_of_grade_lt {β t : ℕ} {g : Polynomial O}
    (h : β < 21 * (β % 2 + 2 * t)) :
    s2Mu3Coeff h2 hq β g t = 0 := by
  unfold s2Mu3Coeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, -, hβ⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
  omega

/-- **the coefficient-level zero law at above-grade inputs** (published Lemma 3.14's
engine; M3-RP2 lifts it to the assembled polynomial): on `P_β⁺` — M3-RP0's
`S2Mu3AboveGrade` — every gate is false and every coefficient vanishes. -/
theorem s2Mu3Coeff_eq_zero_of_above {β : ℕ} {g : Polynomial O}
    (h : S2Mu3AboveGrade h2 hq β g) (t : ℕ) :
    s2Mu3Coeff h2 hq β g t = 0 := by
  have hdv := (S2Mu3AboveGrade_iff_dv2Supp h2 hq).mp h
  unfold s2Mu3Coeff
  rw [if_neg]
  intro hgate
  exact absurd (dv2Supp_le_of_mu3SlotOnGrade h2 hq hgate) (not_le.mpr hdv)

/-! ## Part 4 — computation teeth at the landed μ₃ numerals

The key's own coefficient: `Φ₂` at its landed grade `21 = u₃` (C132nv1's `s2Hgt₃_Φ₂`,
M3-RP0's `tooth_Φ₂`) has the single on-line slot `s = 1`, inner grade `0`, inner read
`R₂-graded of the constant 1` — published eq (11)'s `R_{3,21}(Φ₂) = y^{⌊1/2⌋} = 1` at the
coefficient level.  Private copies of C130rp1/C132nv1 helpers per the corpus's
private-copy pattern. -/

private theorem one_mod_key : (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_one, key_eq h2 hq, s2Key_deg]; norm_num)

private theorem sh_one : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], sh_C h2 hq]
  simp

/-- `dev` tooth: the `Φ′`-development of the constant `1` has slot 0 equal to `1`. -/
private theorem dev_one_zero : dev (s2Frame h2 hq).key (1 : Polynomial O) 0 = 1 := by
  show (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1
  exact one_mod_key h2 hq

/-- `dvHgt` tooth: `dv(1₀) = 0` at the constant `1`. -/
private theorem dvHgt_one_zero : dvHgt (s2Frame h2 hq) (1 : Polynomial O) 0 = 0 := by
  rw [dvHgt, dev_one_zero h2 hq, sh_one h2 hq]

/-- **inner-read tooth**: the μ₂ graded residual of the constant `1` at grade `0` is `1` —
the inner value `s2Mu3Coeff` reads at the key's own on-line slot (a fresh C130rp1-genre
tooth at the grade RP-1's table did not need). -/
theorem s2GradedRes_zero_one : s2GradedRes h2 hq 0 (1 : Polynomial O) = 1 := by
  have hgate : S2SlotOnGrade h2 hq 0 (1 : Polynomial O) (0 % 2 + 2 * 0) :=
    (s2SlotOnGrade_iff h2 hq).mpr ⟨0, dvHgt_one_zero h2 hq, by norm_num⟩
  refine Polynomial.ext fun t => ?_
  rw [s2GradedRes_coeff]
  match t with
  | 0 =>
    rw [Polynomial.coeff_one_zero,
      s2GradedCoeff_eq_twistRead h2 hq hgate (dvHgt_one_zero h2 hq),
      show 0 % 2 + 2 * 0 = 0 by norm_num, dev_one_zero h2 hq]
    exact twistRead_zero_one h2 hq
  | (t + 1) =>
    rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq (by omega), Polynomial.coeff_one]
    simp

private theorem Φ₂_one_mod : (1 : Polynomial O) %ₘ (s2DepthTwoKeyAt h2 hq 2) = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, s2Φ₂_natDegree h2 hq]; norm_num))

/-- `dev` tooth: the `Φ₂`-development of `Φ₂` has slot 1 equal to `1`. -/
private theorem Φ₂_dev1 :
    dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2) 1 = 1 := by
  have h := dev_mul_pow (s2Φ₂_monic h2 hq) 1 (1 : Polynomial O) 0
  rw [Nat.add_zero, one_mul, pow_one] at h
  rw [h]
  exact Φ₂_one_mod h2 hq

/-- inner-value tooth: `μ₂((Φ₂)₁) = μ₂(1) = 0` — literally `s2Hgt₂`'s `h(1) = 0` tooth,
transported across the anti-drift pins (no fresh frame-level computation). -/
private theorem Φ₂_dv2Pin_one :
    dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (s2DepthTwoKeyAt h2 hq 2) 1 = (0 : ℕ∞) := by
  rw [dv2Pin, Φ₂_dev1 h2 hq]
  apply C130s6.toZ_inj
  rw [← s2Hgt₂_eq_dv2Hgt h2 hq, s2Hgt₂_one h2 hq]
  exact (C130s6.toZ_coe 0).symm

/-- **gate tooth**: `Φ₂`'s slot `1` sits on its own grade-`21` line — `2·0 + 21·1 = 21`
(the single on-line slot of the key at its landed grade `u₃ = 21`). -/
theorem tooth_mu3_gate_Φ₂ :
    S2Mu3SlotOnGrade h2 hq 21 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) (21 % 2 + 2 * 0) :=
  (s2Mu3SlotOnGrade_iff h2 hq).mpr ⟨0, Φ₂_dv2Pin_one h2 hq, by norm_num⟩

/-- **inner exact-grade tooth**: at the key's on-line slot the inner exact-grade pin fires
concretely — `(Φ₂)₁ = 1` has exact μ₂ grade `0`. -/
theorem tooth_inner_exact_Φ₂ :
    S2ExactGrade h2 hq 0
      (dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) 1) := by
  have h := s2Mu3SlotOnGrade_inner_exact h2 hq (tooth_mu3_gate_Φ₂ h2 hq)
  rwa [show (21 - 21 * (21 % 2 + 2 * 0)) / 2 = 0 by norm_num,
    show 21 % 2 + 2 * 0 = 1 by norm_num] at h

/-- ★ **tooth (published eq (11) at the μ₃ numerals, coefficient level)**:
`R_{3,21}(Φ₂)`'s `y⁰`-coefficient is `1` — the recursive read fires through TWO landed
levels (`dev Φ₂`, then `s2GradedRes` at the inner grade `0`, then the collapsed
evaluation), and computes. -/
theorem tooth_mu3Coeff_Φ₂ :
    s2Mu3Coeff h2 hq 21 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) 0 = 1 := by
  rw [s2Mu3Coeff_eq_eval h2 hq (tooth_mu3_gate_Φ₂ h2 hq) (Φ₂_dv2Pin_one h2 hq),
    show 21 % 2 + 2 * 0 = 1 by norm_num, Φ₂_dev1 h2 hq, s2GradedRes_zero_one h2 hq,
    Polynomial.eval_one]

/-- **tooth (non-vacuity)**: the coefficient read is NOT the zero function. -/
theorem tooth_mu3Coeff_ne_zero :
    s2Mu3Coeff h2 hq 21 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) 0 ≠ 0 := by
  rw [tooth_mu3Coeff_Φ₂ h2 hq]
  exact one_ne_zero

/-- **tooth (the zero law fires)**: every coefficient of `Φ₂` at grade `20 < 21 = μ₃(Φ₂)`
vanishes (`Φ₂ ∈ P₂₀⁺`, published Lemma 3.14's engine at a concrete input). -/
theorem tooth_mu3Coeff_above (t : ℕ) :
    s2Mu3Coeff h2 hq 20 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) t = 0 := by
  refine s2Mu3Coeff_eq_zero_of_above h2 hq ?_ t
  unfold S2Mu3AboveGrade
  have h20 : ((20 : ℕ) : WithTop ℤ) = ((20 : ℤ) : WithTop ℤ) := by norm_cast
  rw [s2Hgt₃_Φ₂ h2 hq, h20]
  exact_mod_cast (by norm_num : (20 : ℤ) < 21)

end S2

end Uniformity.Density.Tower.C132rp1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3_def312_level3
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3_def312_level2
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3_def312_level2_exists
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3_bezout_level2
#print axioms Uniformity.Density.Tower.C132rp1.S2Mu3SlotOnGrade
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_iff
#print axioms Uniformity.Density.Tower.C132rp1.dv2Hgt_eq_dvSupp
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_iff_hgt₂
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_parity
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_inner_exact
#print axioms Uniformity.Density.Tower.C132rp1.dv2Supp_le_of_mu3SlotOnGrade
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3EpsExp
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3EpsExp_eq
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3EpsOf
#print axioms Uniformity.Density.Tower.C132rp1.s2Fld₂_eq_one_of_ne_zero
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3EpsOf_eq_one
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Eps
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Eps_eq_one
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Eps_eq_epsOf
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Eps_ne_zero
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3_eval_letter_pinned
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_letter_display
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_eval
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_eval_normRes
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_slot
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_dv2Pin_top
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_grade_lt
#print axioms Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_above
#print axioms Uniformity.Density.Tower.C132rp1.s2GradedRes_zero_one
#print axioms Uniformity.Density.Tower.C132rp1.tooth_mu3_gate_Φ₂
#print axioms Uniformity.Density.Tower.C132rp1.tooth_inner_exact_Φ₂
#print axioms Uniformity.Density.Tower.C132rp1.tooth_mu3Coeff_Φ₂
#print axioms Uniformity.Density.Tower.C132rp1.tooth_mu3Coeff_ne_zero
#print axioms Uniformity.Density.Tower.C132rp1.tooth_mu3Coeff_above

end AxCheck
