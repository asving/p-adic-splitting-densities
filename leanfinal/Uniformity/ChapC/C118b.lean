/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C26
import Uniformity.ChapC.C118a

/-!
# Uniformity.ChapC.C118b — the A-C.7 repair, clause 2: the guarded residual transport

**Amendment A-C.7's repair unit for NODE C.118, clause 2** (the frozen `dv2_read_congr_res`
is machine-refuted — `C118_REFUTATION.lean.txt` section 2, the degree-jump counterexample).
One public theorem, `dv2_read_congr_res_guarded`: the frozen binder list PLUS the two guards
that make the statement true.

## ⚠ Guard design — a CORRECTION to the drafted A-C.7 addendum (recorded for certification)

The addendum drafts the re-sign with the single guard `hsupp : dv2Supp < ℓ₂·W`
(`W = (F.e₁ * L.ℓ) * N`).  **That single guard is NOT sufficient**, by the same ⊤-slot
mechanism one layer down: `dv2ResPoly` consults every slot `min + t·ℓ₂`, `t ≤ deg` —
including INTERIOR slots that are off-side — and `dv2Res` reads each consulted block at the
block's OWN level-1 side data, not at the level-2 side line.  An interior slot whose block
is `0` in the member `a` (read `0`, the junk branch) can carry a `π^N`-perturbation block in
`a'` whose own pin is finite (`≥ W`, unseen by `hsupp`) and whose read is NONZERO — C.26's
`natDegree_dvResPoly` forces every pinned block's residual constant term to be nonzero, so
the perturbed read cannot vanish.  Designed instance (same carrier as the refutation file):
`a = X³ + X² + π^M·X` vs `a' = a + π^N` at `(u₂, ℓ₂)` with `u₂ < e₁ℓN`... interior slot 1;
the polynomials differ at coefficient 1 (`0` vs a nonzero read).  Hence the second guard
`hslots`, bounding the pin of EVERY consulted slot of the visible member strictly below `W`:
it excludes both the `⊤`-hole and the above-window reads.  At the section-2 counterexample
`hslots` fails at `t = 0` (the slot-`0` pin of `X²` is `⊤`), and at the interior-slot
instance it fails at `t = 1`; both exclusions are sharp.

`hvis` and `hseam` of the frozen list are RETAINED for binder compatibility but are not
consumed by the proof (B77a's unused-`hd` precedent); the honest minimal form is the
orchestrator's re-sign decision.

## Route

1. `dv2Supp` capped congruence at `(u₂, ℓ₂)` (the C118a capped-pin law rides up the second
   `inf`-layer), then raw equality under `hsupp`.
2. Side-set transfer: per abscissa, an on-side term sits at the support (`< ℓ₂·W`, so its
   pin is `< W` and transports raw); an off-side term either transports raw or both sides
   sit `≥ ℓ₂·W > supp`.  Hence `dv2SideSet`, `dv2SideMin`, `dv2SideMax`, `dv2SideDeg` all
   transfer.
3. Per-slot read transfer under `hslots`: each consulted block has pin `< W = L.ℓ·(e₁N)`,
   i.e. its own level-1 support sits below the level-1 cap; the C118a capped chain gives its
   side set / `M₀` / degree transfer, and the reads bottom out in `digAt` digits at
   positions `< N` (C109's class-level digit calculus), so `twistRead`, `dvResPoly`, and
   `dv2Res` all transport.
4. Assemble `dv2ResPoly` coefficientwise.

## Status

SKELETON (sorry bodies) — the fill is this unit's work.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C118b

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- the capped `dv2Supp` congruence at an arbitrary side `(u₂, ℓ₂)`: the C118a capped-pin
law rides up the second `inf` layer. -/
theorem dv2Supp_min_congr {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') (u₂ ℓ₂ : ℕ) (hℓ₂ : 0 < ℓ₂) :
    min (dv2Supp L Ψ (monicPoly a) u₂ ℓ₂) ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞)
      = min (dv2Supp L Ψ (monicPoly a') u₂ ℓ₂) ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞) := by
  sorry

/-- raw `dv2Supp` equality under the support guard. -/
theorem dv2Supp_congr_of_lt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hsupp : dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ < ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞)) :
    dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ = dv2Supp L Ψ (monicPoly a') u₂ ℓ₂ := by
  sorry

/-- side-set transfer under the support guard. -/
theorem dv2SideSet_congr {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hsupp : dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ < ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞)) :
    dv2SideSet L Ψ (monicPoly a) u₂ ℓ₂ = dv2SideSet L Ψ (monicPoly a') u₂ ℓ₂ := by
  sorry

/-- block-level read transfer: a consulted block whose pin sits below the window has the
same `dv2Res` read on both members. -/
theorem dv2Res_congr_of_lt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {N : ℕ} {A A' : Polynomial O} (h : ∀ i, π ^ N ∣ (A - A').coeff i)
    (hlt : dvSupp F A L.u L.ℓ < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)) :
    dv2Res L A = dv2Res L A' := by
  sorry

end Uniformity.Density.Tower.C118b

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **A-C.7, clause 2′ — the guarded residual transport.**  The frozen clause-2 binders,
PLUS the support guard `hsupp` (side sets transfer) and the consulted-slot guard `hslots`
(every read the residual polynomial consults sits below the window).  Both guards are
sharp at the two machine/designed counterexamples — see the module docstring. -/
theorem dv2_read_congr_res_guarded {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ (monicPoly a) u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (monicPoly a') u₂ ℓ₂).Nonempty)
    (hsupp : dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ < ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞))
    (hslots : ∀ t, t ≤ dv2SideDeg L Ψ (monicPoly a) u₂ ℓ₂ hne →
      dv2Pin L Ψ (monicPoly a) (dv2SideMin L Ψ (monicPoly a) u₂ ℓ₂ hne + t * ℓ₂)
        < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)) :
    dv2ResPoly L Ψ (monicPoly a) u₂ ℓ₂ hne = dv2ResPoly L Ψ (monicPoly a') u₂ ℓ₂ hne' := by
  sorry

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dv2_read_congr_res_guarded

end AxCheck
