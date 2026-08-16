/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H100

/-!
# Uniformity.ChapH.H101 — `mulClass`, class multiplication

**Chapter H, NODE H.101** (`blueprint/CHAP-H_general_induction.md` §17.1, the dated extension of
2026-08-16, unit T-1 / provenance OM-2). The second node of **N-1, the level-0 class transport**.

`mulClass c₁ c₂` is the coefficient class of the product of the monic polynomials the two classes
present, computed ENTIRELY inside `(Res O N)[X]` — **no lift is consulted**, which is what makes it
usable as the inverse of the Hensel factor extraction at H.102. The lemma half is the roundtrip:
multiplying lifts and then truncating agrees with truncating and then `mulClass`-ing.

* `mulClass : Coeff O n₁ N → Coeff O n₂ N → Coeff O (n₁ + n₂) N`;
* `mulClass_proj : proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff i)
   = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)`.

DEPENDS: H.100 (for `map_monicPoly`) · landed `Uniformity.Density.Coeff`, `proj`, `monicPoly`
(`Density/LocalData.lean`) · mathlib `Polynomial.coeff_map`, `Polynomial.map_mul`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0): all binders inline, no section variables; **no
`Finite`, no `IsAdicComplete`** — the definition and its roundtrip are pure truncation algebra.
Hensel (and with it the bijectivity of `mulClass` on strata) enters only at H.102.

## Why the body is written out rather than `monicPoly c₁ * monicPoly c₂`

The two displays are the SAME TERM — `mulClass_apply` below is `rfl` — but the blueprint's
SIGNATURE is frozen at the expanded form and is transcribed verbatim. (The landed `monicPoly`
does apply over the truncation ring: `Density/LocalData.lean`'s `section Poly` carries
`[IsDomain O]` as a section variable, but the elaborated `monicPoly` needs only `[CommRing]`, and
`Res O N = O ⧸ 𝔪 ^ N` is not a domain for `N ≥ 2`.) `mulClass_apply` is exported so downstream
nodes can move between the two displays for free.

SOURCE: OM-2 §3.1 N-1a (*"realized by (lift, factor, reduce) and inverted by multiplication"*);
`EFF.GENIND.54`.

**TEETH** (`verification/openmath/OM2_genindb_battery.py`, RESULTS run 2026-08-16, 612/612):
`P2(i,ii)`'s **roundtrip assert** — the Codex-pass finding-4 repair, `OM2_genindb_battery.py:758`,
*"the product of the extracted factor classes must reproduce the frame class mod pi^N"*,
`assert all(RB.trunc(x, N) == RB.trunc(y, N) for x, y in zip(prod, f))`, executed inside
`frame_read` at every class of all 12 cells × 2 rings. GC-8 disposition: **Lean theorem at this
node** — `mulClass_proj` IS that assert, universally quantified and with the `q ∈ {2,3}` /
finite-`N` scope removed; the battery's executable form is retained as regression. §2 records the
battery's own phrasing (arbitrary lifts of given classes) as an `example`.

## Status

Sorry-free, axiom-free (Lean core only: `propext`, `Classical.choice`, `Quot.sound`). The B.42
axiom does not enter §17 before H.123.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The node -/

/-- **H.101 (def half). Class multiplication.** The coefficient class of the product of the monic
polynomials `c₁` and `c₂` present, computed entirely in `(Res O N)[X]` — no lift consulted. -/
noncomputable def mulClass {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) : Coeff O (n₁ + n₂) N :=
  fun i =>
    ((X ^ n₁ + ∑ j : Fin n₁, Polynomial.C (c₁ j) * X ^ (j : ℕ)) *
      (X ^ n₂ + ∑ j : Fin n₂, Polynomial.C (c₂ j) * X ^ (j : ℕ))).coeff (i : ℕ)

/-- The frozen body of `mulClass`, redisplayed through the landed `monicPoly` (over the truncation
ring `Res O N`). Definitionally the same term — the proof is `rfl`. Non-blueprint auxiliary,
exported so downstream nodes never have to re-expand the sum. -/
theorem mulClass_apply {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    mulClass c₁ c₂ = fun i : Fin (n₁ + n₂) => (monicPoly c₁ * monicPoly c₂).coeff (i : ℕ) := rfl

/-- **H.101 (lemma half).** `mulClass` computes the class of a product of monic lifts: multiply in
`O[X]` then truncate = truncate then `mulClass`. -/
theorem mulClass_proj {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n₁ n₂ N : ℕ} (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) := by
  funext i
  change Ideal.Quotient.mk ((maximalIdeal O) ^ N) ((monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = (monicPoly (proj O n₁ N a₁) * monicPoly (proj O n₂ N a₂)).coeff (i : ℕ)
  rw [← Polynomial.coeff_map, Polynomial.map_mul, map_monicPoly, map_monicPoly]
  rfl

end Uniformity.Density.Induction

/-! ## 2. TEETH — the battery's roundtrip, in its own phrasing

`OM2_genindb_battery.py:758` (the Codex-pass finding-4 repair) reads: given the factor classes
extracted from a frame class, *the product of the extracted factor classes must reproduce the
frame class mod `π ^ N`*. `mulClass_proj` is that statement with the lifts named; the `example`
below is the battery's phrasing verbatim — arbitrary lifts of two GIVEN classes, product taken in
`O[X]`, compared to `mulClass` of the classes. -/

section Teeth

open Uniformity.Density Uniformity.Density.Induction IsLocalRing Polynomial

/-- TEETH — the roundtrip at given classes: any lifts whatsoever reproduce `mulClass`. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n₁ n₂ N : ℕ}
    {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N} (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O)
    (h₁ : proj O n₁ N a₁ = c₁) (h₂ : proj O n₂ N a₂ = c₂) :
    proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) = mulClass c₁ c₂ := by
  subst h₁; subst h₂; exact mulClass_proj a₁ a₂

/-- TEETH, corollary — lift-independence of the product class, which is what the battery's
`RB.trunc(x, N) == RB.trunc(y, N)` comparison actually exercises across its two rings. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n₁ n₂ N : ℕ}
    (a₁ b₁ : Fin n₁ → O) (a₂ b₂ : Fin n₂ → O)
    (h₁ : proj O n₁ N a₁ = proj O n₁ N b₁) (h₂ : proj O n₂ N a₂ = proj O n₂ N b₂) :
    proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = proj O (n₁ + n₂) N (fun i => (monicPoly b₁ * monicPoly b₂).coeff (i : ℕ)) := by
  rw [mulClass_proj, mulClass_proj, h₁, h₂]

end Teeth

/-! ## 3. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.mulClass
#print axioms Uniformity.Density.Induction.mulClass_apply
#print axioms Uniformity.Density.Induction.mulClass_proj

end AxCheck
