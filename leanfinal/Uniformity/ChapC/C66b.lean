/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C29
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C133h0leg

/-!
# Uniformity.ChapC.C66b — `[cite:FGMN]` gate (b): EXACT dv-purity closure and residual
multiplicativity (`fgmn_dv_exact_mul`)

**A NEW gate-(b) literature cite**, authored 2026-08-24 under the owner's
autonomous-until-proved protocol (owner SECONDARY review: `docs/CITE_REVIEW_LIST.md` row 2).
It COEXISTS with C.66's `fgmn_residual_mul` and does NOT replace or silently strengthen it
(C.66's signed type is untouched); the new name makes the stronger normalization commitment
explicit, exactly as the adjudication (`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md`
§4) mandates.  This is the EXACT HALF of the dv-graded engine: the floor engine proves
lower bounds only; purity closure and exact residual identities are imported here.

## FAITHFULNESS ENTRY (the print-read, executed 2026-08-24 against the author-posted PDF)

**Source.** J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane
valuations*, J. Algebra 427 (2015) 30–75, DOI `10.1016/j.jalgebra.2014.12.022`.
Print-read against the author-posted version (UPCommons, `handle/2117/28203`); page numbers
below are that PDF's.  ⚠ VERSION-NUMBERING CAUTION: the engine-v2 document cited "published
Def 3.15/Cor 4.12(3)"; in the author-posted version read here the normalization content
sits at **Corollary 4.9(3) + Corollary 4.11** (there is no Def 3.15); Cor 4.12 carries the
product formula in BOTH the postprint read here and (per the v2 determination) the
published text.  The verbatim quotes below are version-robust anchors; the owner's
secondary review should spot-check them against the journal text.

* **Theorem 2.8 (p. 10), verbatim:** "Let φ be a key polynomial for the valuation μ. Then,
  for any non-zero g, h ∈ K[x] we have N⁻_{μ,φ}(gh) = N⁻_{μ,φ}(g) + N⁻_{μ,φ}(h)."
  ⚠ The paper states IMMEDIATELY BELOW that the analogue for ENTIRE Newton polygons is
  FALSE — the cite is pinned to the PRINCIPAL polygon, which is what the corpus's
  side/`dvSideSet` reads use (heights at the polygon's principal part).
* **Corollary 4.12 (p. 20), verbatim, item (3):** "R_r(gh) = R_r(g)R_r(h) for all
  g, h ∈ K[x]."  (Items (1)–(2) give additivity on `𝒫_α` and the graded product rule.)
* **Corollary 4.9 (pp. 19–20), items (2)–(3), verbatim:** "deg R_{r,α}(g) = ⌊s′(g)/e_r⌋ and
  ord_y(R_{r,α}(g)) = ⌊s(g)/e_r⌋" and "deg R_r(g) = (s′(g) − s(g))/e_r and R_r(g)(0) ≠ 0" —
  the NORMALIZATION: `R_r` is the y-power-stripped operator with nonzero constant term
  (the same normalization shape as the corpus's `dvResPoly`, whose `coeff 0 ≠ 0` is C.26's
  `natDegree_dvResPoly`).
* **Definition 5.4 (p. 22), verbatim:** "For a non-zero g ∈ K[x], we say that N_{μ,φ}(g)
  is one-sided of slope −ν if N_{μ,φ}(g) = S_ν(g), s(g) = 0 and s′(g) > 0."

**The dictionary (the owner-review surface).**  The corpus's `IsDvPure F g u ℓ` (C.29: the
abscissae `0` and `⌊deg g/D′⌋` both on the `(u, ℓ)`-side of the `dv`-polygon) is the paper's
one-sidedness (Def 5.4: `s(g) = 0`, `s′(g) > 0`, polygon = its ν-component) at the
augmented valuation the frame's key defines, with slope `ν = u/ℓ` in lowest terms
(`hcop`), read at the `ê`-cleared integer heights.  The corpus's `dvResPoly` at the
`dvSideMin` pin is the paper's normalized `R_r` up to the frame's twist normalization
(C.25/C.26's `twistRead` packaging) — the twist is a fixed unit rescaling per slot, under
which multiplicativity is preserved slotwise.  The mathematical content imported:
(i) one-sided × one-sided (same slope) = one-sided of that slope on the product — Thm 2.8's
segment Minkowski sum specialized to equal slopes; (ii) the normalized residual of the
product is the product of the normalized residuals — Cor 4.12(3).  Both are imported at the
corpus's degree fences (`D′ ∣ deg`, positive degrees, above-floor slope), which SHRINK the
quantifier against the paper's `∀ g, h ∈ K[x]` — the import is weaker than the source, the
safe direction.

## Consumption

The exact half of the dv-graded engine (v2 §4): `IsDvPure` closure under products (hence
powers, by induction — the induction is a THEOREM, `fgmn_dv_exact_pow` (landed in C131ac),
not part of the axiom), and exact residual power laws.  Primary consumers: C.52's
`composedKey_pow_mem_towerLocus`/`towerLocus_iff_budget` legs, C.34-adjacent purity
propagation, C.80/C.67's re-signed floor conjuncts' eventual proofs.

## Status

ZERO axioms.  `fgmn_dv_exact_mul` is now a THEOREM (see the `[UNT 2026-08-28]` note
below) — its `#print axioms` footprint is exactly Lean core.  Census/C.126 note: the
declared-cite allowlist is back to SIX.

## [H0LEG 2026-08-28] the machine certificate — [UNT 2026-08-28] PHYSICALLY RETIRED

The axiom's statement was PROVED, byte-identically (binders and conclusion verbatim, no
`h` hypothesis), as `Uniformity.Density.Tower.C133h0leg.fgmn_dv_exact_mul_full`
(`C133h0leg.lean`), whose AxCheck footer prints exactly
`[propext, Classical.choice, Quot.sound]`.  Route: C133mh3's landed
`fgmn_dv_exact_mul_thm` (Theorem M, at `0 < F.h`) glued with the degenerate leg
`C133h0leg.fgmn_dv_exact_mul_h0` (at `F.h = 0` coprimality forces `e₁ = 1`, the twist
dies, and C.05's degenerate dictionary collapses the dv-calculus to chapter B's order-1
exact chain at the key — B39a/B43).

H0LEG found the physical removal blocked by a textual import cycle: the axiom's sole
proof consumer (`C131ac.lean:120`) sat inside the theorem's own import foundation
(`C133mh3 → C133mh1 → C130nv3 → C130nv2 → C130nv → C131ae → C131ac`).  **UNT (2026-08-28)
untangled it**: `C130nv`'s ENTIRE use of `C131ae` was one lemma
(`suppVal_add_eq_left_of_lt`) whose proof never touches `C131ac` — chapter B only
(`B32a`/`B32b`).  That lemma (+ its self-contained prerequisite chain) was split out
VERBATIM, same namespace, into `C131ae0.lean` (no `C131ac` import), and `C130nv` now
imports `C131ae0` instead of `C131ae`.  This removes `C131ac`/`C66b` from every
`C130nv`-descendant's import closure (machine-checked: `C133h0leg`'s transitive imports
no longer contain `C131ac` or `C66b`), so `C66b` can safely import `C133h0leg` and
convert the axiom to a theorem below, in place, statement bytes unchanged.  Full route +
verification: `runs/wave-c/verdict_UNT.md`.  Faithfulness record with the retirement
entry: `docs/AXIOM_FAITHFULNESS.md` (RETIRED-AS-THEOREM, 2026-08-28; PHYSICALLY RETIRED,
UNT 2026-08-28).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **`[cite:FGMN]` — exact dv-purity closure and normalized residual multiplicativity**
(J. Algebra 427 (2015), Thm 2.8 (principal-polygon additivity, equal-slope one-sided case)
+ Cor 4.12(3) (normalized residual multiplicativity), under the corpus↔paper dictionary in
the module docstring).  Fences follow C.66's landed `fgmn_residual_mul`: positive coprime
slope above the frame floor, monic full-degree factors.

**[UNT 2026-08-28] PHYSICALLY RETIRED**: was `axiom fgmn_dv_exact_mul`; now a THEOREM,
statement bytes UNCHANGED (binders + conclusion byte-identical to the retired axiom text,
machine-diffed), proved by `C133h0leg.fgmn_dv_exact_mul_full` (the `F.h = 0`/`0 < F.h`
case split — see the module docstring's `[H0LEG 2026-08-28]`/`[UNT 2026-08-28]` note). -/
theorem fgmn_dv_exact_mul {F : KeyFrame O π} (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ) :
    IsDvPure F (g * g') u ℓ ∧
      ∀ (hne : (dvSideSet F g u ℓ).Nonempty)
        (hne' : (dvSideSet F g' u ℓ).Nonempty)
        (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
        (M₀ M₀' M₀'' : ℕ)
        (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
        (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
        (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)),
        dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
          = dvResPoly F H₀ hpin g u ℓ hne M₀ hp
            * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp' :=
  C133h0leg.fgmn_dv_exact_mul_full hπ H₀ hpin hg hg' hℓ hcop hfloor hdg hdg' hpos hpos' hpg hpg'

end Uniformity.Density.Tower

/-! ## Footprint — `[UNT 2026-08-28]` now Lean-core; retained as the retirement's own
machine certificate (formerly "the axiom prints itself; consumers inherit it visibly") -/

section AxCheck

#print axioms Uniformity.Density.Tower.fgmn_dv_exact_mul

end AxCheck
