/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130nv2

/-!
# Uniformity.ChapC.C130nv3 — S2-source plan node NV-3 (CORE 2/4)

**S2-source plan node NV-3 (CORE 2/4 of the level-two product law)**
(`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §4, §6 row NV-3): the unique lowest
convolution term SURVIVES — NV-2's one owed input, the endpoint height upper bound
`dv(dev (g·z) (jg+jz)) ≤ Hg + Hz`, is PROVED at the S2 frame, and NV-2's conditional
assembly bank fires unconditionally.  **NV-4's row lands here too**: the level-two product
law `dvSupp (g·z) 5 2 = dvSupp g 5 2 + dvSupp z 5 2` at the S2 frame, with no monic/pure/
degree fences and all zero cases.

## The mechanism (two halves)

* **The generic half** (`stageHeight_dev_endpoint_le_of_surv`): expand `g·z` through the
  double `Φ′`-development (B39a/B35a's convolution pattern, exactly as NV-2's
  `dvSupp_add_le_dvSupp_mul`), split off the endpoint pair `(jg, jz)` — the UNIQUE on-side
  decomposition of `jg + jz` (NV-2's `dvOnSide_endpoint_unique`).  Its term is
  `(dev g jg · dev z jz) %ₘ Φ′` (`dev_mul_pow` at carry `0` + `dev_zero_pin`).  Every OTHER
  term prices at weight `≥ Sg + Sz + 1` (NV-2's `lt_line_dev_term`, carries included, under
  the strict admissibility `ℓ·dv(Φ′) < u`), so the finite-sum ultrametric
  (`le_weight_stageHeight_sum` + `succ_le_of_weight_succ_le`) puts the whole remainder at
  height `≥ Hg + Hz + 1`.  Given the SURVIVAL of the endpoint term — height `≤ Hg + Hz`,
  the theorem's one hypothesis `hsurv` — the ultrametric equality-off-ties
  (`suppVal_add_eq`) reads the digit's height off the endpoint term: `≤ Hg + Hz`.

* **The S2 survival core** (`s2_stageHeight_mul_modByMonic_le`): at the S2 frame
  (`Φ′ = x² − 2`, `(e₁, h) = (2, 1)`), for `a, b` of degree `≤ 1`,
  `dv((a·b) %ₘ Φ′) ≤ dv(a) + dv(b)`.  This is FGMN's residual non-vanishing
  `ψ ∤ R(a)·R(b)` concretized: `e₁ = 2` makes every residual polynomial a MONOMIAL
  (`f₁ = 1`), so non-cancellation is pinned at a single COEFFICIENT of the remainder,
  and the ψ-argument collapses to PARITY.  `dv(a) = min(2v(a₀), 2v(a₁)+1)` has one even
  and one odd branch, hence a unique attaining slot; in each of the four (parity × parity)
  cases the surviving coefficient of
  `(a·b) %ₘ Φ′ = (a₀b₁ + a₁b₀)·x + (a₀b₀ + 2a₁b₁)` is computed exactly:
  - even × even: slot 0, value `v(a₀) + v(b₀)` (the carry `2a₁b₁` sits strictly above);
  - odd × odd: slot 0, value `1 + v(a₁) + v(b₁)` — the CARRY `x² ≡ 2` transfers the value
    (`a₀b₀` sits strictly above); this is the genuine cancellation case, compensated;
  - mixed: slot 1, value `v(a₁) + v(b₀)` resp. `v(a₀) + v(b₁)` (cross term strictly above).

## What lands (the assembly discharge)

`s2_endpoint_dev_le` (NV-2's `hup`, unconditional at S2) → NV-2's bank fires:
`s2_dvSupp_mul` (★ NV-4's row: the unfenced S2 level-two product law), `s2Hgt₂_mul`
(carrier form), `s2_dvOnSide_mul_endpoint` (the sum of the chosen minimizers IS a product
minimizer), `s2_dvSideMin_mul_le`.  Teeth: all three parity genres regression-tested
against hand computation through the NEW law — `h₂(x·x) = 4` (odd×odd, the carry-transfer
case: `x² = Φ′ + 2`), `h₂(Φ′·Φ′) = 10` (even×even), `h₂(x·Φ′) = 7` (mixed; independently
reproduces NV-2's tooth through the product law).

## What this node does NOT claim (honesty scope)

* The GENERIC survival core (arbitrary frames, residual degree `f₁ > 1`) needs the
  residual-polynomial product law (B35c/B43's `resPoly_mul_*` + the frame's `hresirr`);
  here it enters only as the generic theorem's `hsurv` hypothesis and is DISCHARGED at S2
  by the parity argument.  Survival is genuinely frame-specific: for a reducible residual
  (e.g. slope-1 side with key `x² + 4`, `a = b = x + 2`) the endpoint term CANCELS —
  so no fence weaker than a residual hypothesis can make the generic form unconditional.
* Everything else per NV-2's scope note: corpus frames `0 < F.h`, strict admissibility
  `ℓ·dv(Φ′) < u` for the strict bank — both discharged at S2 (`4 < 5`).

**Flagged for human review** (parent CLAUDE.md trust boundary): `s2_mul_modByMonic` (the
explicit remainder of a quadratic product mod `x² − 2`) and `s2_stageHeight_linear` (the
two-slot stage-height read) are new S2-model statements; the three teeth regression-test
them against hand computation.

**DEPENDS.** C130nv2 (the NV-2 bank: `dvOnSide_endpoint_unique`, `lt_line_dev_term`,
`le_weight_stageHeight_sum`, `succ_le_of_weight_succ_le`, `dev_zero_pin`,
`dvSupp_eq_of_dvOnSide`, `dvOnSide_dvSideMin`, `exists_dvSideMin_height`, the endpoint
assembly `dvSupp_mul_eq_add_of_endpoint_le`/`dvOnSide_mul_endpoint`/`dvSideMin_mul_le`,
S2 gates `s2_h_pos`/`s2_stageHeight_key`, teeth reads `s2_dvSupp_X`/`s2_dvSupp_key`) ·
C130nv (`suppVal_add_eq`, `toZ_add`) · C130s6 (`dvSupp_zero_eq_top`,
`dvSupp_ne_top_of_ne_zero`, `s2Hgt₂`, `toZ` dictionary) · C.34 (`dvSideSet_nonempty`) ·
C.127 (`KeyFrame.stageHeight_zero`, `natDegree_key_pos`, `stageHeight_eq_inf_range`) ·
C35b (`e1_eq`, `h_eq`, `key_eq`, `s2Key_deg`) · C.97 (`s2Key`, `s2Key_monic`,
`s2Key_natDegree`) · B35a (`dev_mul_pow`, `dev_finsetSum`) · B.05 (`sum_dev_eq`) · B.03
(`degree_dev_lt`) · B83Kit (`gaussVal_C`) · C131y (`addVal_neg`) · mathlib
(`IsDiscreteValuationRing.addVal_mul`/`addVal_add`/`addVal_uniformizer`,
`Polynomial.div_modByMonic_unique`, `Polynomial.eq_X_add_C_of_natDegree_le_one`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130nv3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Leaf.GateKit
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130nv2

/-! ## Part 0 — parity and ultrametric helpers -/

/-- Clearing a doubled cast (the parity engine's normal form). -/
private theorem nsmul_coe (ℓ n : ℕ) : ℓ • ((n : ℕ) : ℕ∞) = ((ℓ * n : ℕ) : ℕ∞) := by
  rw [nsmul_eq_mul]; push_cast; ring

/-- **Parity read, even side**: if the even weight `2n` is at most the odd weight `2x + 1`,
then `n ≤ x` — the strict gap is free because `2n = 2x + 1` is impossible. -/
theorem coe_le_of_two_nsmul_le {n : ℕ} {x : ℕ∞}
    (h : (2 : ℕ) • (n : ℕ∞) ≤ (2 : ℕ) • x + 1) : (n : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hx
  rw [nsmul_coe, nsmul_coe,
    show ((2 * m : ℕ) : ℕ∞) + 1 = ((2 * m + 1 : ℕ) : ℕ∞) by push_cast; ring] at h
  have hnat : 2 * n ≤ 2 * m + 1 := by exact_mod_cast h
  exact_mod_cast (by omega : n ≤ m)

/-- **Parity read, odd side**: if the odd weight `2n + 1` is at most the even weight `2x`,
then `n + 1 ≤ x` — again the parity gap is free. -/
theorem coe_succ_le_of_two_nsmul_le {n : ℕ} {x : ℕ∞}
    (h : (2 : ℕ) • (n : ℕ∞) + 1 ≤ (2 : ℕ) • x) : ((n + 1 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hx
  rw [nsmul_coe, nsmul_coe,
    show ((2 * n : ℕ) : ℕ∞) + 1 = ((2 * n + 1 : ℕ) : ℕ∞) by push_cast; ring] at h
  have hnat : 2 * n + 1 ≤ 2 * m := by exact_mod_cast h
  exact_mod_cast (by omega : n + 1 ≤ m)

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **Ultrametric upper read, left**: adding a strictly higher-valued element cannot raise
the valuation — `v(x + y) ≤ v(x)` when `v(x) < v(y)`. -/
theorem addVal_add_le_left {x y : O} (h : addVal O x < addVal O y) :
    addVal O (x + y) ≤ addVal O x := by
  have hmin : min (addVal O (x + y)) (addVal O (-y)) ≤ addVal O (x + y + -y) :=
    IsDiscreteValuationRing.addVal_add
  rw [add_neg_cancel_right, C131y.addVal_neg] at hmin
  by_contra hc
  rw [not_le] at hc
  exact absurd hmin (not_le.mpr (lt_min hc h))

/-- **Ultrametric upper read, right**: the mirrored form. -/
theorem addVal_add_le_right {x y : O} (h : addVal O y < addVal O x) :
    addVal O (x + y) ≤ addVal O y := by
  rw [add_comm]
  exact addVal_add_le_left h

/-! ## Part 1 — the generic endpoint theorem (survival ⟹ NV-2's `hup`)

Everything except the survival of the endpoint term itself is frame-generic: the double
development, the uniqueness of the lowest convolution pair, the strict pricing of every
other term, and the equality-off-ties read. -/

/-- Every on-side abscissa lies within the development range (the range half of C.07's
filter, made public — mirrors `C130nv2.dvOnSide_of_mem_dvSideSet`). -/
theorem dvSideMin_le_natDegree (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (hne : (dvSideSet F f u ℓ).Nonempty) : dvSideMin F f u ℓ hne ≤ f.natDegree := by
  classical
  have hmem := Finset.min'_mem (dvSideSet F f u ℓ) hne
  have h := (Finset.mem_filter.mp (show dvSideMin F f u ℓ hne ∈
    (Finset.range (f.natDegree + 1)).filter (fun j => DvOnSide F f u ℓ j) from hmem)).1
  rw [Finset.mem_range] at h
  omega

/-- ★ **NODE NV-3, the generic half**: under strict admissibility, if the endpoint term of
the outer convolution SURVIVES — `dv((dev g jg · dev z jz) %ₘ Φ′) ≤ Hg + Hz`, the `hsurv`
hypothesis — then the product's development coefficient at the endpoint slot `jg + jz` has
stage value at most `Hg + Hz`.  This is exactly NV-2's owed input `hup`. -/
theorem stageHeight_dev_endpoint_le_of_surv (hπ : Irreducible π) (F : KeyFrame O π)
    (hh : 0 < F.h) {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ}
    (hV : F.stageHeight F.key = (V : ℕ∞)) (hadm' : ℓ * V < u)
    {g z : Polynomial O}
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt F g (dvSideMin F g u ℓ hng) = (Hg : ℕ∞))
    (hHz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Hz : ℕ∞))
    (hsurv : F.stageHeight ((dev F.key g (dvSideMin F g u ℓ hng)
        * dev F.key z (dvSideMin F z u ℓ hnz)) %ₘ F.key) ≤ ((Hg + Hz : ℕ) : ℕ∞)) :
    F.stageHeight (dev F.key (g * z)
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz)) ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
  classical
  set jg := dvSideMin F g u ℓ hng with hjg
  set jz := dvSideMin F z u ℓ hnz with hjz
  -- the support reads at the chosen minimizers
  have hSg : dvSupp F g u ℓ = ((ℓ * Hg + u * jg : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHg (dvOnSide_dvSideMin F g u ℓ hng)
  have hSz : dvSupp F z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHz (dvOnSide_dvSideMin F z u ℓ hnz)
  -- the double development of the product (NV-2's convolution pattern)
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
  -- assemble: the endpoint term survives, everything else sits strictly above
  rw [hsplit]
  set T := (dev F.key g jg * dev F.key z jz) %ₘ F.key with hT
  set R := ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) (jg + jz) with hRdef
  rcases eq_or_ne (F.stageHeight T) (F.stageHeight R) with heq | hne
  · exfalso
    have h1 : ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ ((Hg + Hz : ℕ) : ℕ∞) :=
      le_trans (le_trans hR (le_of_eq heq.symm)) hsurv
    rw [show ((Hg + Hz : ℕ) : ℕ∞) + 1 = ((Hg + Hz + 1 : ℕ) : ℕ∞) by push_cast; ring] at h1
    exact absurd (by exact_mod_cast h1 : Hg + Hz + 1 ≤ Hg + Hz) (by omega)
  · have hd : 0 < (X : Polynomial O).natDegree := by rw [natDegree_X]; exact Nat.one_pos
    have hne' : suppVal X T F.h F.e₁ ≠ suppVal X R F.h F.e₁ := hne
    have hmin : F.stageHeight (T + R) = min (F.stageHeight T) (F.stageHeight R) :=
      suppVal_add_eq monic_X hd F.he₁ F.h hne'
    rw [hmin]
    exact le_trans (min_le_left _ _) hsurv

end Generic

/-! ## Part 2 — the S2 survival core (the parity argument) -/

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- **The two-slot stage-height read**: at the S2 frame, the stage value of a polynomial of
degree `≤ 1` is `min(2·v(a₀), 2·v(a₁) + 1)` — one even branch, one odd branch, so the
attaining slot is always unique (the parity engine's entry point). -/
theorem s2_stageHeight_linear {w : Polynomial O} (hw : w.natDegree ≤ 1) :
    (s2Frame h2 hq).stageHeight w
      = min ((2 : ℕ) • addVal O (w.coeff 0)) ((2 : ℕ) • addVal O (w.coeff 1) + 1) := by
  rw [(s2Frame h2 hq).stageHeight_eq_inf_range w hw,
    show Finset.range (1 + 1) = {0, 1} by decide, Finset.inf_insert, Finset.inf_singleton]
  simp only [C35b.e1_eq h2 hq, C35b.h_eq h2 hq, gaussVal_C, Nat.cast_zero, Nat.cast_one,
    mul_zero, mul_one, add_zero]

/-- **The explicit remainder**: for `a, b` of degree `≤ 1`,
`(a·b) %ₘ (x² − 2) = (a₀b₁ + a₁b₀)·x + (a₀b₀ + 2·a₁b₁)` — the carry `x² ≡ 2` lands in the
constant slot with an exact factor `2`. -/
theorem s2_mul_modByMonic (a b : Polynomial O) (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
    (a * b) %ₘ s2Key O
      = Polynomial.C (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0) * X
        + Polynomial.C (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1)) := by
  refine (Polynomial.div_modByMonic_unique (Polynomial.C (a.coeff 1 * b.coeff 1)) _
    s2Key_monic ⟨?_, ?_⟩).2
  · conv_rhs => rw [eq_X_add_C_of_natDegree_le_one ha, eq_X_add_C_of_natDegree_le_one hb]
    simp only [s2Key, Polynomial.C_add, Polynomial.C_mul]
    ring
  · refine lt_of_le_of_lt degree_linear_le ?_
    rw [C35b.s2Key_deg]
    decide

/-- ★ **The S2 survival core** (FGMN's `ψ ∤ R(a)·R(b)`, collapsed to parity): at the S2
frame, for `a, b` of degree `≤ 1`, the REDUCED remainder of `a·b` keeps the product value —
`dv((a·b) %ₘ Φ′) ≤ dv(a) + dv(b)`.  Universal in `a, b` (zero cases ride the `⊤`
conventions); the four parity cases each pin the surviving coefficient exactly. -/
theorem s2_stageHeight_mul_modByMonic_le (a b : Polynomial O)
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
    (s2Frame h2 hq).stageHeight ((a * b) %ₘ (s2Frame h2 hq).key)
      ≤ (s2Frame h2 hq).stageHeight a + (s2Frame h2 hq).stageHeight b := by
  rw [C35b.key_eq h2 hq, s2_mul_modByMonic a b ha hb,
    s2_stageHeight_linear h2 hq natDegree_linear_le,
    s2_stageHeight_linear h2 hq ha, s2_stageHeight_linear h2 hq hb]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
    Polynomial.coeff_X_one, mul_zero, mul_one, Polynomial.coeff_C,
    one_ne_zero, if_false, zero_add, add_zero]
  rcases le_total ((2 : ℕ) • addVal O (a.coeff 0)) ((2 : ℕ) • addVal O (a.coeff 1) + 1)
    with hA | hA
  <;> rcases le_total ((2 : ℕ) • addVal O (b.coeff 0)) ((2 : ℕ) • addVal O (b.coeff 1) + 1)
    with hB | hB
  · -- even × even: survival at slot 0, value v(a₀) + v(b₀)
    rw [min_eq_left hA, min_eq_left hB]
    rcases eq_or_ne (addVal O (a.coeff 0)) ⊤ with h0 | h0
    · rw [h0, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add]
      exact le_top
    rcases eq_or_ne (addVal O (b.coeff 0)) ⊤ with h1 | h1
    · rw [h1, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), add_top]
      exact le_top
    obtain ⟨a0, ha0⟩ := ENat.ne_top_iff_exists.1 h0
    obtain ⟨b0, hb0⟩ := ENat.ne_top_iff_exists.1 h1
    have hva1 : (a0 : ℕ∞) ≤ addVal O (a.coeff 1) := by
      refine coe_le_of_two_nsmul_le ?_
      rw [ha0]
      exact hA
    have hvb1 : (b0 : ℕ∞) ≤ addVal O (b.coeff 1) := by
      refine coe_le_of_two_nsmul_le ?_
      rw [hb0]
      exact hB
    have hlt : addVal O (a.coeff 0 * b.coeff 0) < addVal O (2 * (a.coeff 1 * b.coeff 1)) := by
      rw [addVal_mul, addVal_mul, addVal_mul, addVal_uniformizer h2, ← ha0, ← hb0]
      refine lt_of_lt_of_le ?_ (add_le_add le_rfl (add_le_add hva1 hvb1))
      rw [show ((a0 : ℕ∞) + (b0 : ℕ∞)) = ((a0 + b0 : ℕ) : ℕ∞) by push_cast; ring]
      rw [show ((1 : ℕ∞) + ((a0 + b0 : ℕ) : ℕ∞)) = ((1 + (a0 + b0) : ℕ) : ℕ∞) by
        push_cast; ring]
      exact_mod_cast (by omega : a0 + b0 < 1 + (a0 + b0))
    refine le_trans (min_le_left _ _) ?_
    refine le_trans (nsmul_le_nsmul_right (addVal_add_le_left hlt) 2) ?_
    rw [addVal_mul, smul_add]
  · -- even × odd: survival at slot 1, value v(a₀) + v(b₁)
    rw [min_eq_left hA, min_eq_right hB]
    rcases eq_or_ne (addVal O (a.coeff 0)) ⊤ with h0 | h0
    · rw [h0, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add]
      exact le_top
    rcases eq_or_ne (addVal O (b.coeff 1)) ⊤ with h1 | h1
    · rw [h1, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add, add_top]
      exact le_top
    obtain ⟨a0, ha0⟩ := ENat.ne_top_iff_exists.1 h0
    obtain ⟨b1, hb1⟩ := ENat.ne_top_iff_exists.1 h1
    have hva1 : (a0 : ℕ∞) ≤ addVal O (a.coeff 1) := by
      refine coe_le_of_two_nsmul_le ?_
      rw [ha0]
      exact hA
    have hvb0 : ((b1 + 1 : ℕ) : ℕ∞) ≤ addVal O (b.coeff 0) := by
      refine coe_succ_le_of_two_nsmul_le ?_
      rw [hb1]
      exact hB
    have hlt : addVal O (a.coeff 0 * b.coeff 1) < addVal O (a.coeff 1 * b.coeff 0) := by
      rw [addVal_mul, addVal_mul, ← ha0, ← hb1]
      refine lt_of_lt_of_le ?_ (add_le_add hva1 hvb0)
      rw [show ((a0 : ℕ∞) + (b1 : ℕ∞)) = ((a0 + b1 : ℕ) : ℕ∞) by push_cast; ring]
      rw [show ((a0 : ℕ∞) + ((b1 + 1 : ℕ) : ℕ∞)) = ((a0 + (b1 + 1) : ℕ) : ℕ∞) by
        push_cast; ring]
      exact_mod_cast (by omega : a0 + b1 < a0 + (b1 + 1))
    have hr1 : addVal O (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0)
        ≤ ((a0 + b1 : ℕ) : ℕ∞) := by
      refine le_trans (addVal_add_le_left hlt) (le_of_eq ?_)
      rw [addVal_mul, ← ha0, ← hb1]
      push_cast
      ring
    refine le_trans (min_le_right _ _) ?_
    calc (2 : ℕ) • addVal O (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0) + 1
        ≤ (2 : ℕ) • ((a0 + b1 : ℕ) : ℕ∞) + 1 :=
          add_le_add (nsmul_le_nsmul_right hr1 2) le_rfl
      _ = (2 : ℕ) • ((a0 : ℕ) : ℕ∞) + ((2 : ℕ) • ((b1 : ℕ) : ℕ∞) + 1) := by
          push_cast [nsmul_eq_mul]
          ring
      _ = (2 : ℕ) • addVal O (a.coeff 0) + ((2 : ℕ) • addVal O (b.coeff 1) + 1) := by
          rw [ha0, hb1]
  · -- odd × even: survival at slot 1, value v(a₁) + v(b₀)
    rw [min_eq_right hA, min_eq_left hB]
    rcases eq_or_ne (addVal O (a.coeff 1)) ⊤ with h0 | h0
    · rw [h0, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add, top_add]
      exact le_top
    rcases eq_or_ne (addVal O (b.coeff 0)) ⊤ with h1 | h1
    · rw [h1, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), add_top]
      exact le_top
    obtain ⟨a1, ha1⟩ := ENat.ne_top_iff_exists.1 h0
    obtain ⟨b0, hb0⟩ := ENat.ne_top_iff_exists.1 h1
    have hva0 : ((a1 + 1 : ℕ) : ℕ∞) ≤ addVal O (a.coeff 0) := by
      refine coe_succ_le_of_two_nsmul_le ?_
      rw [ha1]
      exact hA
    have hvb1 : (b0 : ℕ∞) ≤ addVal O (b.coeff 1) := by
      refine coe_le_of_two_nsmul_le ?_
      rw [hb0]
      exact hB
    have hlt : addVal O (a.coeff 1 * b.coeff 0) < addVal O (a.coeff 0 * b.coeff 1) := by
      rw [addVal_mul, addVal_mul, ← ha1, ← hb0]
      refine lt_of_lt_of_le ?_ (add_le_add hva0 hvb1)
      rw [show ((a1 : ℕ∞) + (b0 : ℕ∞)) = ((a1 + b0 : ℕ) : ℕ∞) by push_cast; ring]
      rw [show (((a1 + 1 : ℕ) : ℕ∞) + (b0 : ℕ∞)) = (((a1 + 1) + b0 : ℕ) : ℕ∞) by
        push_cast; ring]
      exact_mod_cast (by omega : a1 + b0 < (a1 + 1) + b0)
    have hr1 : addVal O (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0)
        ≤ ((a1 + b0 : ℕ) : ℕ∞) := by
      refine le_trans (addVal_add_le_right hlt) (le_of_eq ?_)
      rw [addVal_mul, ← ha1, ← hb0]
      push_cast
      ring
    refine le_trans (min_le_right _ _) ?_
    calc (2 : ℕ) • addVal O (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0) + 1
        ≤ (2 : ℕ) • ((a1 + b0 : ℕ) : ℕ∞) + 1 :=
          add_le_add (nsmul_le_nsmul_right hr1 2) le_rfl
      _ = ((2 : ℕ) • ((a1 : ℕ) : ℕ∞) + 1) + (2 : ℕ) • ((b0 : ℕ) : ℕ∞) := by
          push_cast [nsmul_eq_mul]
          ring
      _ = ((2 : ℕ) • addVal O (a.coeff 1) + 1) + (2 : ℕ) • addVal O (b.coeff 0) := by
          rw [ha1, hb0]
  · -- odd × odd: survival at slot 0 through the CARRY — `x² ≡ 2` transfers the value
    rw [min_eq_right hA, min_eq_right hB]
    rcases eq_or_ne (addVal O (a.coeff 1)) ⊤ with h0 | h0
    · rw [h0, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add, top_add]
      exact le_top
    rcases eq_or_ne (addVal O (b.coeff 1)) ⊤ with h1 | h1
    · rw [h1, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add, add_top]
      exact le_top
    obtain ⟨a1, ha1⟩ := ENat.ne_top_iff_exists.1 h0
    obtain ⟨b1, hb1⟩ := ENat.ne_top_iff_exists.1 h1
    have hva0 : ((a1 + 1 : ℕ) : ℕ∞) ≤ addVal O (a.coeff 0) := by
      refine coe_succ_le_of_two_nsmul_le ?_
      rw [ha1]
      exact hA
    have hvb0 : ((b1 + 1 : ℕ) : ℕ∞) ≤ addVal O (b.coeff 0) := by
      refine coe_succ_le_of_two_nsmul_le ?_
      rw [hb1]
      exact hB
    have hlt : addVal O (2 * (a.coeff 1 * b.coeff 1)) < addVal O (a.coeff 0 * b.coeff 0) := by
      rw [addVal_mul, addVal_mul, addVal_mul, addVal_uniformizer h2, ← ha1, ← hb1]
      refine lt_of_lt_of_le ?_ (add_le_add hva0 hvb0)
      rw [show ((1 : ℕ∞) + ((a1 : ℕ∞) + (b1 : ℕ∞))) = ((1 + (a1 + b1) : ℕ) : ℕ∞) by
        push_cast; ring]
      rw [show (((a1 + 1 : ℕ) : ℕ∞) + ((b1 + 1 : ℕ) : ℕ∞))
          = (((a1 + 1) + (b1 + 1) : ℕ) : ℕ∞) by push_cast; ring]
      exact_mod_cast (by omega : 1 + (a1 + b1) < (a1 + 1) + (b1 + 1))
    have hr0 : addVal O (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1))
        ≤ ((1 + (a1 + b1) : ℕ) : ℕ∞) := by
      refine le_trans (addVal_add_le_right hlt) (le_of_eq ?_)
      rw [addVal_mul, addVal_mul, addVal_uniformizer h2, ← ha1, ← hb1]
      push_cast
      ring
    refine le_trans (min_le_left _ _) ?_
    calc (2 : ℕ) • addVal O (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1))
        ≤ (2 : ℕ) • ((1 + (a1 + b1) : ℕ) : ℕ∞) := nsmul_le_nsmul_right hr0 2
      _ = ((2 : ℕ) • ((a1 : ℕ) : ℕ∞) + 1) + ((2 : ℕ) • ((b1 : ℕ) : ℕ∞) + 1) := by
          push_cast [nsmul_eq_mul]
          ring
      _ = ((2 : ℕ) • addVal O (a.coeff 1) + 1) + ((2 : ℕ) • addVal O (b.coeff 1) + 1) := by
          rw [ha1, hb1]

/-! ## Part 3 — NV-2's owed input, DISCHARGED at S2 -/

/-- ★ **NODE NV-3 (the row's charge)**: at the S2 frame and level-two side `(5, 2)`, the
unique lowest convolution term SURVIVES — the development coefficient of `g·z` at the
endpoint slot `jg + jz` has stage value at most `Hg + Hz`.  This is EXACTLY the `hup`
hypothesis of NV-2's assembly bank, now unconditional. -/
theorem s2_endpoint_dev_le {g z : Polynomial O}
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt (s2Frame h2 hq) g (dvSideMin (s2Frame h2 hq) g 5 2 hng) = (Hg : ℕ∞))
    (hHz : dvHgt (s2Frame h2 hq) z (dvSideMin (s2Frame h2 hq) z 5 2 hnz) = (Hz : ℕ∞)) :
    (s2Frame h2 hq).stageHeight (dev (s2Frame h2 hq).key (g * z)
        (dvSideMin (s2Frame h2 hq) g 5 2 hng + dvSideMin (s2Frame h2 hq) z 5 2 hnz))
      ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
  refine stageHeight_dev_endpoint_le_of_surv h2 (s2Frame h2 hq) (s2_h_pos h2 hq)
    (by norm_num) (s2_stageHeight_key h2 hq) (by norm_num) hng hnz hHg hHz ?_
  -- the survival core, fed with the digits at the chosen minimizers
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
    rw [C35b.key_eq h2 hq]
    exact s2Key_natDegree
  have hdg : (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 2 hng)).natDegree ≤ 1 := by
    have h := natDegree_lt_natDegree hg0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos g _)
    rw [hkd] at h
    omega
  have hdz : (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 2 hnz)).natDegree ≤ 1 := by
    have h := natDegree_lt_natDegree hz0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos z _)
    rw [hkd] at h
    omega
  have hcore := s2_stageHeight_mul_modByMonic_le h2 hq _ _ hdg hdz
  have hg' : (s2Frame h2 hq).stageHeight
      (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 2 hng)) = (Hg : ℕ∞) := hHg
  have hz' : (s2Frame h2 hq).stageHeight
      (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 2 hnz)) = (Hz : ℕ∞) := hHz
  rw [hg', hz', ← Nat.cast_add] at hcore
  exact hcore

/-! ## Part 4 — the assembly discharge: NV-2's bank fires unconditionally at S2 -/

/-- ★ **NODE NV-4's row, LANDED**: the S2 level-two product law
`dvSupp (g·z) 5 2 = dvSupp g 5 2 + dvSupp z 5 2` — UNIVERSAL: no monic, pure, or degree
fence, all zero cases included. -/
theorem s2_dvSupp_mul (g z : Polynomial O) :
    dvSupp (s2Frame h2 hq) (g * z) 5 2
      = dvSupp (s2Frame h2 hq) g 5 2 + dvSupp (s2Frame h2 hq) z 5 2 := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dvSupp_zero_eq_top (s2Frame h2 hq) 5 (by norm_num), top_add]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dvSupp_zero_eq_top (s2Frame h2 hq) 5 (by norm_num), add_top]
  have hng := dvSideSet_nonempty (s2Frame h2 hq) hg 5 (by norm_num : (0 : ℕ) < 2)
  have hnz := dvSideSet_nonempty (s2Frame h2 hq) hz 5 (by norm_num : (0 : ℕ) < 2)
  obtain ⟨Hg, hHg⟩ := exists_dvSideMin_height (s2Frame h2 hq) g 5 2 hng
  obtain ⟨Hz, hHz⟩ := exists_dvSideMin_height (s2Frame h2 hq) z 5 2 hnz
  exact dvSupp_mul_eq_add_of_endpoint_le h2 (s2_h_pos h2 hq) (by norm_num)
    (s2_stageHeight_key h2 hq) (by norm_num) hng hnz hHg hHz
    (s2_endpoint_dev_le h2 hq hng hnz hHg hHz)

/-- ★ The product law in the CARRIER (E.10's `WithTop ℤ`, the `s2Hgt₂` table):
`h₂(g·z) = h₂(g) + h₂(z)` for ALL `g, z`. -/
theorem s2Hgt₂_mul (g z : Polynomial O) :
    s2Hgt₂ h2 hq (g * z) = s2Hgt₂ h2 hq g + s2Hgt₂ h2 hq z := by
  rw [s2Hgt₂, s2Hgt₂, s2Hgt₂, ← toZ_add, s2_dvSupp_mul h2 hq]

/-- **The endpoint is a product minimizer** (NV-2's minimizer form, unconditional at S2):
the sum of the chosen minimizers of `g` and `z` is on the side of `g·z`. -/
theorem s2_dvOnSide_mul_endpoint {g z : Polynomial O}
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt (s2Frame h2 hq) g (dvSideMin (s2Frame h2 hq) g 5 2 hng) = (Hg : ℕ∞))
    (hHz : dvHgt (s2Frame h2 hq) z (dvSideMin (s2Frame h2 hq) z 5 2 hnz) = (Hz : ℕ∞)) :
    DvOnSide (s2Frame h2 hq) (g * z) 5 2
      (dvSideMin (s2Frame h2 hq) g 5 2 hng + dvSideMin (s2Frame h2 hq) z 5 2 hnz) :=
  dvOnSide_mul_endpoint h2 (s2_h_pos h2 hq) (by norm_num) (s2_stageHeight_key h2 hq)
    (by norm_num) hng hnz hHg hHz (s2_endpoint_dev_le h2 hq hng hnz hHg hHz)

/-- **The product's chosen minimizer is bounded by the sum of the factors' minimizers**
(NV-2's `dvSideMin_mul_le`, unconditional at S2). -/
theorem s2_dvSideMin_mul_le {g z : Polynomial O}
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt (s2Frame h2 hq) g (dvSideMin (s2Frame h2 hq) g 5 2 hng) = (Hg : ℕ∞))
    (hHz : dvHgt (s2Frame h2 hq) z (dvSideMin (s2Frame h2 hq) z 5 2 hnz) = (Hz : ℕ∞))
    (hne : (dvSideSet (s2Frame h2 hq) (g * z) 5 2).Nonempty) :
    dvSideMin (s2Frame h2 hq) (g * z) 5 2 hne
      ≤ dvSideMin (s2Frame h2 hq) g 5 2 hng + dvSideMin (s2Frame h2 hq) z 5 2 hnz :=
  dvSideMin_mul_le h2 (s2_h_pos h2 hq) (by norm_num) (s2_stageHeight_key h2 hq)
    (by norm_num) hng hnz hHg hHz (s2_endpoint_dev_le h2 hq hng hnz hHg hHz) hne

/-! ## Part 5 — teeth: the three parity genres, end to end

Each tooth reads a NEW table value through the product law alone and matches hand
computation.  `x·x` is the genuine cancellation-threat case (`x² = Φ′ + 2`: the naive
remainder loses the head, the carry `2` receives the value). -/

/-- **tooth (odd × odd, the carry-transfer case)**: `h₂(x²) = 4 = 2 + 2`. -/
theorem s2_dvSupp_X_sq :
    dvSupp (s2Frame h2 hq) ((Polynomial.X : Polynomial O) * Polynomial.X) 5 2
      = ((4 : ℕ) : ℕ∞) := by
  rw [s2_dvSupp_mul h2 hq, s2_dvSupp_X h2 hq, ← Nat.cast_add]

/-- **tooth (even × even)**: `h₂(Φ′²) = 10 = 5 + 5`. -/
theorem s2_dvSupp_key_sq :
    dvSupp (s2Frame h2 hq)
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 5 2
      = ((10 : ℕ) : ℕ∞) := by
  rw [s2_dvSupp_mul h2 hq, s2_dvSupp_key h2 hq, ← Nat.cast_add]

/-- **tooth (mixed parity)**: `h₂(x·Φ′) = 7 = 2 + 5` — NV-2's regression value, now
reproduced through the product LAW rather than the endpoint estimate. -/
theorem s2_dvSupp_X_mul_key' :
    dvSupp (s2Frame h2 hq) ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) 5 2
      = ((7 : ℕ) : ℕ∞) := by
  rw [s2_dvSupp_mul h2 hq, s2_dvSupp_X h2 hq, s2_dvSupp_key h2 hq, ← Nat.cast_add]

/-- **tooth (carrier form)**: `h₂(x·x) = 4` in the `s2Hgt₂` table. -/
theorem s2Hgt₂_X_sq :
    s2Hgt₂ h2 hq ((Polynomial.X : Polynomial O) * Polynomial.X) = ((4 : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₂, s2_dvSupp_X_sq h2 hq, toZ_coe]
  norm_num

end S2

end Uniformity.Density.Tower.C130nv3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130nv3.coe_le_of_two_nsmul_le
#print axioms Uniformity.Density.Tower.C130nv3.coe_succ_le_of_two_nsmul_le
#print axioms Uniformity.Density.Tower.C130nv3.addVal_add_le_left
#print axioms Uniformity.Density.Tower.C130nv3.addVal_add_le_right
#print axioms Uniformity.Density.Tower.C130nv3.dvSideMin_le_natDegree
#print axioms Uniformity.Density.Tower.C130nv3.stageHeight_dev_endpoint_le_of_surv
#print axioms Uniformity.Density.Tower.C130nv3.s2_stageHeight_linear
#print axioms Uniformity.Density.Tower.C130nv3.s2_mul_modByMonic
#print axioms Uniformity.Density.Tower.C130nv3.s2_stageHeight_mul_modByMonic_le
#print axioms Uniformity.Density.Tower.C130nv3.s2_endpoint_dev_le
#print axioms Uniformity.Density.Tower.C130nv3.s2_dvSupp_mul
#print axioms Uniformity.Density.Tower.C130nv3.s2Hgt₂_mul
#print axioms Uniformity.Density.Tower.C130nv3.s2_dvOnSide_mul_endpoint
#print axioms Uniformity.Density.Tower.C130nv3.s2_dvSideMin_mul_le
#print axioms Uniformity.Density.Tower.C130nv3.s2_dvSupp_X_sq
#print axioms Uniformity.Density.Tower.C130nv3.s2_dvSupp_key_sq
#print axioms Uniformity.Density.Tower.C130nv3.s2_dvSupp_X_mul_key'
#print axioms Uniformity.Density.Tower.C130nv3.s2Hgt₂_X_sq

end AxCheck
