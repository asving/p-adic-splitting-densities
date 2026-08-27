/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C34
import Uniformity.ChapC.C132nv4
import Uniformity.ChapC.C132nv5

/-!
# Uniformity.ChapC.C132nv6 — the `dv2SideSet` nonemptiness gap, closed (μ₃ campaign, node M3-NV6)

**[M3-NV6, 2026-08-27]** (gap-born from M3-NV5's finding, `runs/wave-b/verdict_MNV5.md`):
proves the μ₃ analogue of C.34's `dvSideSet_nonempty` at the TWO-LEVEL `dv2SideSet` carrier
(`dv2SideSet_nonempty` below), instantiates it at the S2 numerals `Φ₂, (u₂,ℓ₂) = (21,2)`, pairs
it with the ALREADY-LANDED finite-pin existence `C132nv2.exists_dv2SideMin_height`, and fires
C132nv4's conditional `s2Hgt₃_mul` unconditionally on every pair of NONZERO polynomials
(`s2Hgt₃_mul_unconditional`). Folding in C132nv4's zero cases gives the fully unconditional
`hmul` shape `AddValuation.of` needs, which fires C132nv5's `s2AddVal₃_of_unconditional_mul` to
land the genuine (no longer conditional) `AddValuation (Polynomial O) (WithTop ℤ)` instance
`s2AddVal₃`, with its `_apply` anti-drift pin.

## Why the gap closes with NO new mathematics (honesty check, per the charge's fence)

C132nv5 identified the blocking hypothesis precisely: an unconditional
`∀ {g}, g ≠ 0 → (dv2SideSet L Φ₂ g 21 2).Nonempty`. Its own honesty note worried this might be
blocked by the SAME obstruction that makes `Dv2ResSurv` (C132nv2) a genuine extra hypothesis
(the μ₂-residual-survival content, `Dv2ResSurv`'s "reduction modulo `Φ₂` preserves the product
... value", scoped to degree-`<4` coefficients at M3-NV3). It is NOT: `Dv2ResSurv` is a fact
about the EXACT VALUE of a digit PRODUCT's `Ψ`-reduced development (needed only when multiplying
two already-located side digits together), whereas mere NONEMPTINESS of `dv2SideSet L Ψ f u₂ ℓ₂`
only needs that `f` itself (not a digit product) has *some* nonzero `Ψ`-development digit of
*finite* level-2 height. Finiteness of `dv2Pin L Ψ f j` for `dev Ψ f j ≠ 0` is `dv2Pin`'s
definitional unfold to `dv2Hgt L (dev Ψ f j) = dvSupp F (dev Ψ f j) L.u L.ℓ`, finite by
`C130s6.dvSupp_ne_top_of_ne_zero` — a fact with NO degree restriction whatsoever (it holds for
every nonzero polynomial over `O`, of any degree). So the audit-leg-2 mechanism of C.34
(`dvSideSet_nonempty`: a nonzero polynomial has a nonzero development digit, that digit has
finite height, the finite-range infimum is attained, and `0 < ℓ` excludes the `⊤`-height escape)
transcribes verbatim one level up, with `F.key`/`dvHgt F`/`F.stageHeight_ne_top` replaced by
`Ψ`/`dv2Pin L Ψ`/(the direct unfold above) — no new hypothesis, no restriction to low-degree
digits, nothing borrowed from `Dv2ResSurv` or M3-NV3. The finite-pin half (b) needs nothing new
at all: `C132nv2.exists_dv2SideMin_height` is already fully generic (no `Dv2ResSurv` premise) and
is simply cited here at the S2 instantiation.

## What lands

* `dv2SideSet_nonempty` — the μ₃ (two-level) analogue of C.34's `dvSideSet_nonempty`, generic
  over any level datum `L`, monic positive-degree level-2 key `Ψ`, and side `(u₂, ℓ₂)` with
  `0 < ℓ₂`: every NONZERO `f` has `(dv2SideSet L Ψ f u₂ ℓ₂).Nonempty`.
* `s2_dv2SideSet_nonempty_at_21` — the S2 instantiation at `Φ₂ = s2DepthTwoKeyAt h2 hq 2`,
  `(u₂,ℓ₂) = (21,2)`.
* `s2Hgt₃_mul_unconditional` — the row's target: `s2Hgt₃ (g·z) = s2Hgt₃ g + s2Hgt₃ z` for every
  NONZERO `g, z`, firing C132nv4's `s2Hgt₃_mul` through the two facts above.
* `s2Hgt₃_mul_all` — folds in C132nv4's `s2Hgt₃_zero_mul`/`s2Hgt₃_mul_zero` to get the fully
  unconditional `∀ x y, s2Hgt₃ (x*y) = s2Hgt₃ x + s2Hgt₃ y`, i.e. exactly `AddValuation.of`'s
  `hmul` shape.
* `s2AddVal₃` — the genuine (UNCONDITIONAL) `AddValuation (Polynomial O) (WithTop ℤ)` instance,
  `s2AddVal₃_of_unconditional_mul` fired at `s2Hgt₃_mul_all`.
* `s2AddVal₃_apply` — the anti-drift restriction pin (mirror of `s2AddVal₂_apply`/
  `s2AddVal₃_of_unconditional_mul_apply`): `s2AddVal₃ A = s2Hgt₃ A`.

**DEPENDS.** C.34 (`dvSideSet_nonempty`'s proof shape, read as the one-level precedent;
`C130s6.dvSupp_ne_top_of_ne_zero` via C34's import chain) · C132nv0 (`dv2Pin_top_of_gt`) ·
C132nv2 (`Dv2OnSide`, `dv2SideSet`, `dv2SideMin`, `exists_dv2SideMin_height`) · C132nv4
(`s2Φ₂_monic`, `s2Φ₂_natDegree`, `s2Hgt₃_mul`, `s2Hgt₃_zero_mul`, `s2Hgt₃_mul_zero`) · C132nv5
(`s2AddVal₃_of_unconditional_mul`, `s2AddVal₃_of_unconditional_mul_apply`) · B.05 (`sum_dev_eq`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no statement invented beyond the row's
sketch; no roll-up, leanspec, or existing file touched.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`dv2SideSet_nonempty`, `s2_dv2SideSet_nonempty_at_21`, `s2Hgt₃_mul_unconditional`,
`s2Hgt₃_mul_all`, `s2AddVal₃`, `s2AddVal₃_apply`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv6

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C132nv4 Uniformity.Density.Tower.C132nv5
open Uniformity.Density.Tower.C80

/-! ## Part 1 — the generic μ₃ analogue of C.34's `dvSideSet_nonempty` -/

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- ★ **The μ₃ (two-level) analogue of C.34's `dvSideSet_nonempty`.** Transcribed verbatim
from that proof's mechanism, one level up: a nonzero `f` has a nonzero `Ψ`-development digit
(else `f` would reconstruct to `0`), that digit has finite level-2 height (`dv2Pin`'s unfold to
`dvSupp F (dev Ψ f j) L.u L.ℓ`, finite by `C130s6.dvSupp_ne_top_of_ne_zero` — no degree
restriction), the finite-range infimum defining `dv2Supp` is attained, and `0 < ℓ₂` excludes the
`⊤`-height abscissa (`ℓ₂ • ⊤ = ⊤`) from being the attaining one. -/
theorem dv2SideSet_nonempty {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {f : Polynomial O} (hf : f ≠ 0)
    (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty := by
  classical
  -- a nonzero `Ψ`-development digit exists within the support range
  have hblock : ∃ j ∈ Finset.range (f.natDegree + 1), dev Ψ f j ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hf ?_
    have hrep : ∑ j ∈ Finset.range (f.natDegree + 1), dev Ψ f j * Ψ ^ j = f :=
      sum_dev_eq hΨ hΨd f
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hΨd))
    rw [← hrep]
    exact Finset.sum_eq_zero fun j hj => by rw [hall j hj, zero_mul]
  obtain ⟨j₀, hj₀mem, hj₀⟩ := hblock
  have hhgt₀ : dv2Pin L Ψ f j₀ ≠ ⊤ := by
    rw [dv2Pin, dv2Hgt]
    exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ hj₀
  -- hence the cleared level-2 support is finite
  have hfin : dv2Supp L Ψ f u₂ ℓ₂ ≠ ⊤ := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hhgt₀
    have hle : dv2Supp L Ψ f u₂ ℓ₂ ≤ ((ℓ₂ * m + u₂ * j₀ : ℕ) : ℕ∞) := by
      simp only [dv2Supp]
      refine le_trans (Finset.inf_le hj₀mem) ?_
      rw [← hm, nsmul_eq_mul]
      push_cast
      exact le_refl _
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  -- the inf is attained; the attaining abscissa's height is finite since `0 < ℓ₂`
  obtain ⟨j₁, hj₁mem, hj₁⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      (fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞))
  have hside : dv2Supp L Ψ f u₂ ℓ₂ = ℓ₂ • dv2Pin L Ψ f j₁ + (u₂ * j₁ : ℕ∞) := hj₁
  have hhgt₁ : dv2Pin L Ψ f j₁ ≠ ⊤ := by
    intro htop
    apply hfin
    rw [hside, htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ₂.ne'), top_add]
  refine ⟨j₁, ?_⟩
  show j₁ ∈ Finset.filter (Dv2OnSide L Ψ f u₂ ℓ₂) (Finset.range (f.natDegree + 1))
  exact Finset.mem_filter.mpr ⟨hj₁mem, hside, hhgt₁⟩

end Generic

/-! ## Part 2 — the S2 instantiation at `Φ₂, (21,2)`, and the unconditional product law -/

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- **The nonemptiness fact, instantiated at S2's `Φ₂, (21,2)`.** -/
theorem s2_dv2SideSet_nonempty_at_21 {g : Polynomial O} (hg : g ≠ 0) :
    (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2).Nonempty :=
  dv2SideSet_nonempty ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) hg 21 (by norm_num)

/-- ★ **NODE NV-6's row: the UNCONDITIONAL μ₃ product law on nonzero factors.**
`s2Hgt₃ (g·z) = s2Hgt₃ g + s2Hgt₃ z` for every `g, z ≠ 0` — C132nv4's conditional `s2Hgt₃_mul`
fired through the nonemptiness fact above and the already-generic finite-pin existence
`C132nv2.exists_dv2SideMin_height`. -/
theorem s2Hgt₃_mul_unconditional {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    s2Hgt₃ h2 hq (g * z) = s2Hgt₃ h2 hq g + s2Hgt₃ h2 hq z := by
  obtain ⟨Hg, hHg⟩ :=
    exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) g 21 2
      (s2_dv2SideSet_nonempty_at_21 h2 hq hg)
  obtain ⟨Hz, hHz⟩ :=
    exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) z 21 2
      (s2_dv2SideSet_nonempty_at_21 h2 hq hz)
  exact s2Hgt₃_mul h2 hq (s2_dv2SideSet_nonempty_at_21 h2 hq hg)
    (s2_dv2SideSet_nonempty_at_21 h2 hq hz) hHg hHz

/-- **The fully unconditional product law, zero cases folded in** — exactly
`AddValuation.of`'s `hmul` shape (`∀ x y, f (x*y) = f x + f y`). -/
theorem s2Hgt₃_mul_all (x y : Polynomial O) :
    s2Hgt₃ h2 hq (x * y) = s2Hgt₃ h2 hq x + s2Hgt₃ h2 hq y := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact s2Hgt₃_zero_mul h2 hq y
  rcases eq_or_ne y 0 with rfl | hy
  · exact s2Hgt₃_mul_zero h2 hq x
  exact s2Hgt₃_mul_unconditional h2 hq hx hy

/-! ## Part 3 — the genuine `AddValuation` instance, at last unconditional -/

/-- ★ **The genuine (UNCONDITIONAL) `AddValuation` instance for `s2Hgt₃`.** C132nv5's
conditional packaging `s2AddVal₃_of_unconditional_mul`, fired at `s2Hgt₃_mul_all` — the gap
C132nv5 recorded as blocking is closed. -/
noncomputable def s2AddVal₃ : AddValuation (Polynomial O) (WithTop ℤ) :=
  s2AddVal₃_of_unconditional_mul h2 hq (s2Hgt₃_mul_all h2 hq)

/-- Anti-drift restriction pin: `s2AddVal₃` evaluates to exactly `s2Hgt₃`, mirroring
`s2AddVal₂_apply`/`s2AddVal₃_of_unconditional_mul_apply`. -/
theorem s2AddVal₃_apply (A : Polynomial O) : s2AddVal₃ h2 hq A = s2Hgt₃ h2 hq A :=
  s2AddVal₃_of_unconditional_mul_apply h2 hq (s2Hgt₃_mul_all h2 hq) A

end S2

end Uniformity.Density.Tower.C132nv6

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132nv6.dv2SideSet_nonempty
#print axioms Uniformity.Density.Tower.C132nv6.s2_dv2SideSet_nonempty_at_21
#print axioms Uniformity.Density.Tower.C132nv6.s2Hgt₃_mul_unconditional
#print axioms Uniformity.Density.Tower.C132nv6.s2Hgt₃_mul_all
#print axioms Uniformity.Density.Tower.C132nv6.s2AddVal₃
#print axioms Uniformity.Density.Tower.C132nv6.s2AddVal₃_apply

end AxCheck
