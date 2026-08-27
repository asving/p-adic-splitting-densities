/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.RingTheory.Valuation.Basic
import Uniformity.ChapC.C132nv1

/-!
# Uniformity.ChapC.C132nv5 — `s2Hgt₃` valuation packaging (μ₃ campaign, node M3-NV5)

**[M3-NV5, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-NV5):
package `s2Hgt₃` (C132nv1) as a mathlib `AddValuation (Polynomial O) (WithTop ℤ)`, mirroring
the μ₂ precedent `s2AddVal₂` (`C130nv5.lean:124-235`, NV-5/NV-6 of the S2-source plan).

## The finding: the μ₂ packaging pattern does NOT port unconditionally

Mathlib's constructor (`Mathlib.RingTheory.Valuation.Basic`) is

```
AddValuation.of (f : R → Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)
  (hadd : ∀ x y, min (f x) (f y) ≤ f (x + y)) (hmul : ∀ x y, f (x * y) = f x + f y) :
  AddValuation R Γ₀
```

— `hmul` is a **fully unconditional** universal statement, no side hypothesis on `x, y`. At
μ₂, `s2AddVal₂` supplied this from C130nv3's `s2Hgt₂_mul (g z : Polynomial O) : s2Hgt₂ (g*z) =
s2Hgt₂ g + s2Hgt₂ z` — proved for ALL `g, z`, because its proof discharges the needed
side-set-nonemptiness/pin data ITSELF, unconditionally, via C.34's `dvSideSet_nonempty`
(`C130nv3.lean:543-544`: `have hng := dvSideSet_nonempty (s2Frame h2 hq) hg 5 (by norm_num);
have hnz := dvSideSet_nonempty (s2Frame h2 hq) hz 5 (by norm_num)`).

At μ₃, the landed product law is C132nv4's `s2Hgt₃_mul`:

```
theorem s2Hgt₃_mul {g z : Polynomial O}
    (hng : (dv2SideSet L Φ₂ g 21 2).Nonempty) (hnz : (dv2SideSet L Φ₂ z 21 2).Nonempty)
    {Hg Hz : ℕ} (hHg : dv2Pin L Φ₂ g (dv2SideMin L Φ₂ g 21 2 hng) = (Hg : ℕ∞))
    (hHz : dv2Pin L Φ₂ z (dv2SideMin L Φ₂ z 21 2 hnz) = (Hz : ℕ∞)) :
    s2Hgt₃ (g * z) = s2Hgt₃ g + s2Hgt₃ z
```

which is **conditional** on `hng, hnz, hHg, hHz` — the wrong shape for `hmul`. This is not a
gap this node can close by more transcription: as C132nv4's own honesty note records, "no
`dv2SideSet_nonempty`-style unconditional existence fact is derived here" at the two-level
`dv2SideSet`/`dv2Pin` construction (M3-NV0/C132nv0), unlike μ₂'s single-level `dvSideSet`,
whose unconditional nonemptiness (C.34) rests on `KeyFrame.stageHeight_ne_top` — a fact about
the FIRST development layer only. The μ₃ layer nests a second `dev`/`dvSupp` reduction inside
each block (M3-NV3's row is explicitly scoped to "coefficients of degree `< 4`"), so an
unconditional `dv2SideSet_nonempty` at arbitrary `(g, u₂, ℓ₂)` is not yet available and is NOT
manufactured here.

**THE BLOCKING HYPOTHESIS, PRECISELY**: an unconditional
`∀ {g : Polynomial O}, g ≠ 0 → (dv2SideSet L Φ₂ g 21 2).Nonempty`-style theorem at the μ₃
`dv2SideSet` level (the μ₃ analogue of C.34's `dvSideSet_nonempty`). Until it lands, no
unconditional `hmul` for `s2Hgt₃` exists, and `AddValuation.of` cannot be discharged.

## What lands here instead (honest partial, per the orchestrator's brief)

* `s2Hgt₃_one_eq_zero` — the `h1`-shape bridging tooth (mirror of C130nv5's
  `s2Hgt₁_one_eq_zero`/`s2Hgt₂_one_eq_zero`); genuinely new since no `s2Hgt₃_one` was landed
  by M3-NV1 (unlike `s2Hgt₂_one`, which M3-NV1 reuses as an input, not restates).
* `s2AddVal₃_of_unconditional_mul` — the **conditional packaging**: a function taking the
  missing unconditional multiplicativity law as an explicit hypothesis and producing the
  genuine `AddValuation (Polynomial O) (WithTop ℤ)` from it plus the four already-landed
  unconditional fields (`s2Hgt₃_zero`, `s2Hgt₃_one_eq_zero`, `s2Hgt₃_add_ge`). This is NOT an
  instance of `s2Hgt₃` actually being an `AddValuation` — it precisely records, in the type of
  its hypothesis, the single remaining gap. No axiom, no forcing: an honest partial over a
  false unconditional claim.
* `s2AddVal₃_of_unconditional_mul_apply` — the anti-drift restriction pin (mirror of
  `s2AddVal₂_apply`): whenever the packaging IS discharged (by supplying `hmul`), it evaluates
  to exactly `s2Hgt₃`, nothing new invented in the packaging step itself.

## NV-6 (fraction-field extension): DEFERRED

Per the row's own scope ("extend to `FractionRing (Polynomial O)` only if a later point
consumer needs it"): (1) no consumer in the M3-RP0 row inputs needs it — RP0's own μ₂
precedent (`C130rp0.lean:115-248`, Part 7) ties `S2ExactGrade`/`S2AboveGrade` to the packaged
`AddValuation` ONLY through the `_apply` restriction identity (`S2ExactGrade_eq_addVal`), never
through `Valuation.extendToLocalization` or any fraction-field object; (2) more fundamentally,
`Valuation.extendToLocalization` needs an actual (unconditional) `Valuation`/`AddValuation` to
extend, and `s2AddVal₃_of_unconditional_mul` only produces one CONDITIONALLY on the still-open
`hmul` — there is no unconditional level-one object to extend yet. NV-6 is recorded as an open
follow-on once the blocking hypothesis above is discharged, not attempted here.

**DEPENDS.** C132nv1 (`s2Hgt₃`, `s2Hgt₃_zero`, `s2Hgt₃_add_ge`, `s2Φ₂_monic`,
`s2Φ₂_natDegree`) · C130s6 (`s2Hgt₂_one`, `s2Hgt₂_eq_dv2Hgt`, `toZ_inj`, `toZ_coe`) · C80
(`s2Tower`) · `Mathlib.RingTheory.Valuation.Basic` (`AddValuation`, `AddValuation.of`).
`C132nv4`'s `s2Hgt₃_mul` is READ (in this docstring, to state the finding precisely) but not
imported/invoked — no code in this file depends on it.

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no statement forced; the conditional
packaging is exactly the honest partial the blocking hypothesis permits.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2Hgt₃_one_eq_zero`, `s2AddVal₃_of_unconditional_mul` (a new definition, conditional on an
explicit unproved-here hypothesis), `s2AddVal₃_of_unconditional_mul_apply`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the `h1`-shape bridging tooth: `s2Hgt₃ 1 = 0` -/

/-- `Φ₂`'s degree-0-competitor reduction: `1 %ₘ Φ₂ = 1` (same computation as C132nv1's
private `Φ₂_one_mod`, reproved here since `private` declarations do not cross files). -/
private theorem one_mod_Φ₂ :
    (1 : Polynomial O) %ₘ (s2DepthTwoKeyAt h2 hq 2) = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, s2Φ₂_natDegree h2 hq]; norm_num))

/-- `Φ₂`'s own μ₂ read at `1` is `0` — literally `s2Hgt₂`'s `h(1) = 0` tooth, transported
across `s2Hgt₂_eq_dv2Hgt` (same computation as C132nv1's private `Φ₂_dv2Hgt_one`, reproved
here for the same reason). -/
private theorem dv2Hgt_one_eq_zero :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) (1 : Polynomial O) = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [← s2Hgt₂_eq_dv2Hgt h2 hq, s2Hgt₂_one h2 hq]
  exact (C130s6.toZ_coe 0).symm

/-- ★ **the `h1`-shape bridging tooth**: `s2Hgt₃ 1 = 0` in `AddValuation.of`'s exact `h1`
shape (`f 1 = 0`, not the cast literal). Genuinely new: unlike `s2Hgt₂_one`, no `s2Hgt₃_one`
was landed by M3-NV1. -/
theorem s2Hgt₃_one_eq_zero : s2Hgt₃ h2 hq (1 : Polynomial O) = 0 := by
  have hdev0 : dev (s2DepthTwoKeyAt h2 hq 2) (1 : Polynomial O) 0 = 1 := one_mod_Φ₂ h2 hq
  have hval : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (1 : Polynomial O) 21 2 = ((0 : ℕ) : ℕ∞) := by
    rw [dv2Supp, Polynomial.natDegree_one, show Finset.range (0 + 1) = {0} by decide,
      Finset.inf_singleton, dv2Pin, hdev0, dv2Hgt_one_eq_zero h2 hq]
    simp
  rw [s2Hgt₃, hval, C130s6.toZ_coe]
  rfl

/-! ## Part 2 — the blocked field: `s2Hgt₃_mul` is conditional, not `AddValuation.of`'s `hmul`

See the module docstring for the full finding. No code below invokes C132nv4's `s2Hgt₃_mul` —
the point of this part is that its SHAPE (four extra hypotheses `hng, hnz, hHg, hHz`, per
`C132nv4.lean:117-127`) is not `∀ x y, f (x*y) = f x + f y`, so it cannot instantiate `hmul`
directly, unlike μ₂'s fully unconditional `s2Hgt₂_mul`. -/

/-! ## Part 3 — the conditional packaging: honest partial over forcing -/

/-- ★ **NODE NV-5, conditional packaging**: IF `s2Hgt₃`'s multiplicativity law is supplied in
`AddValuation.of`'s exact unconditional `hmul` shape, THEN `s2Hgt₃` packages into a genuine
`AddValuation (Polynomial O) (WithTop ℤ)`, from the four fields already landed unconditionally
(`s2Hgt₃_zero`, `s2Hgt₃_one_eq_zero`, `s2Hgt₃_add_ge`) plus the supplied `hmul`. This is a
CONDITIONAL packaging, not an unconditional `AddValuation` instance: the hypothesis `hmul` is
exactly the still-open blocking gap (an unconditional μ₃ `dv2SideSet_nonempty`, see above),
not discharged by this node. -/
noncomputable def s2AddVal₃_of_unconditional_mul
    (hmul : ∀ x y : Polynomial O,
      s2Hgt₃ h2 hq (x * y) = s2Hgt₃ h2 hq x + s2Hgt₃ h2 hq y) :
    AddValuation (Polynomial O) (WithTop ℤ) :=
  AddValuation.of (s2Hgt₃ h2 hq) (s2Hgt₃_zero h2 hq) (s2Hgt₃_one_eq_zero h2 hq)
    (s2Hgt₃_add_ge h2 hq) hmul

/-- Anti-drift restriction pin: whenever the conditional packaging above IS discharged, it
evaluates to exactly `s2Hgt₃` — nothing fresh invented in the packaging step, mirroring
`s2AddVal₂_apply` (`C130nv5.lean:140`). -/
theorem s2AddVal₃_of_unconditional_mul_apply
    (hmul : ∀ x y : Polynomial O,
      s2Hgt₃ h2 hq (x * y) = s2Hgt₃ h2 hq x + s2Hgt₃ h2 hq y)
    (A : Polynomial O) :
    s2AddVal₃_of_unconditional_mul h2 hq hmul A = s2Hgt₃ h2 hq A := rfl

end Uniformity.Density.Tower.C132nv5

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132nv5.s2Hgt₃_one_eq_zero
#print axioms Uniformity.Density.Tower.C132nv5.s2AddVal₃_of_unconditional_mul
#print axioms Uniformity.Density.Tower.C132nv5.s2AddVal₃_of_unconditional_mul_apply

end AxCheck
