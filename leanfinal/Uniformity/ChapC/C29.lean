/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C09
import Uniformity.ChapC.C25

/-!
# Uniformity.ChapC.C29 — `IsDvPure`, `HasLabel`: level purity and the label predicate

**Chapter C, NODE C.29** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §5, the descent
grammar; the A-C.1 amendment set governs, which **hoists this node into §4** — defect D12(iii):
C.27 takes `hg : HasLabel L g`, so the §5 predicate must land above the §4 value law, and the
blueprint's own C.27 text records the forward reference as "the two nodes land together").
**ENV-C1**. Two signed declarations, both definitional.

## What the two predicates say

`IsDvPure F g u ℓ` — **level purity**, B.34's `IsPure` replayed one level up at the `dv`-carrier.
The `Φ′`-polygon of `g` (C.06's `dvHgt`/`dvSupp`, C.07's `DvOnSide`) is the single side of slope
`−u/ℓ` spanning the whole abscissa range: both extreme abscissae, `0` and `μ = deg g / D′` with
`D′ = e₁f₁` (C.01's `KeyFrame.hdeg`), lie in `dvSideSet F g u ℓ`. There is no second slope to
split off.

`HasLabel L g` — `g` **carries the level-1 label** `L = (λ = u/ℓ, r)` (C.09's `LevelDatum`): `g`
is monic of positive degree, is `(L.u, L.ℓ)`-pure at the `dv`-carrier, and its level residual
polynomial (C.25's `dvResPoly`, the `R_λ` of `EFF.HE6.11`) is a **positive power of `L.r`**.
The existentials `hne₂`, `M₀`, `hpin₂` are the side-nonemptiness and the pinned level height
that `dvResPoly` needs as arguments; `m` is the multiplicity of `r` in the residual.

## Three shape decisions, all load-bearing

* **Endpoints, not the whole range** (B.34's convention, inherited). Purity is stated at the two
  extreme abscissae only. The intermediate abscissae sit weakly above the side and need not be on
  it — C.08's `ℓ`-spacing law says only one residue class mod `ℓ` can be on it at all — so "both
  endpoints on one line of slope `−u/ℓ`" is exactly "the polygon is that one side".
* **The right endpoint is `g.natDegree / (F.e₁ * F.f₁)`, not `g.natDegree`.** The `Φ′`-development
  index runs to `μ = deg g / deg Φ′` (B.13 one level down), and `deg Φ′ = e₁f₁`. The wider range
  `g.natDegree + 1` is only the uniform window C.06's `dvSupp` takes its `inf` over; asserting
  on-sideness at `g.natDegree` would assert it where the height is `⊤` as soon as `D′ > 1`.
* **The residual clause is existential in `(hne₂, M₀, hpin₂, m)`, not universal.** `dvResPoly`'s
  dependent binders are proof-and-numeral plumbing, and the numeral `M₀` is *determined* by
  `hpin₂` (`dvHgt … = (M₀ : ℕ∞)` has at most one `ℕ` solution), so the existential is not weaker
  than the ∀-form in the intended sense. Consumers that need the stronger EXACT residual — `R_λ`
  equal to `L.r` on the nose, i.e. `m = 1` — take it as a separate ∀-pinned hypothesis rather than
  reshaping this predicate; that is the A-C.1 resolution of the `hm1` design hole at C.61
  (blueprint §11: "the multiplicity-1 clause is signed as the EXACT-RESIDUAL hypothesis … without
  reshaping C.29's committed `HasLabel`") and the same reading behind D13's note at C.35.

## ⚠ FAITHFULNESS (trust boundary)

Carried verbatim from the blueprint node, and **flagged for human review** (parent CLAUDE.md
trust boundary: Lean checks proofs, not statements).

The corpus's `S_{λ,r}` is a **set of roots in `K̄₀`**; `HasLabel` is the **factor-level
surrogate** (DECISION C-D1's recast: root count → factor degree, orbit → factor). The tie "every
root of a `HasLabel` factor is a `(λ, r)`-point" is **not stated** here and must not be assumed —
no points exist in this development. What downstream consumes is exactly this predicate plus the
value laws of C.27 (`slot2_exact`) and C.37. C.29's faithfulness note is one of the two target
texts flagged for the codex cross-read at blueprint §16.2(2).

## Binder notes

The `{H₀ hpin}` binder group of `HasLabel` is C.09's landed pattern (`LevelDatum.keyDeg₂`,
`LevelDatum.seam`): the two are implicit binders with omitted types, inferred from
`LevelDatum F H₀ hpin`, and `hpin` is the C.03/C.19/C.21/C.22/C.25 stage pin
`npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)`.

Both declarations are `Prop`-valued, so neither needs `noncomputable` even though `dvSideSet`
(a `Classical`-filtered `Finset`) and `dvResPoly` are.

**DEPENDS.** C.06 (`dvHgt`) · C.07 (`DvOnSide`, `dvSideSet`, `dvSideMin`) · C.09 (`LevelDatum`,
its `u`/`ℓ`/`r`) · C.25 (`dvResPoly`) · B.34 (`IsPure`, the shape template) · C.01
(`KeyFrame.e₁`, `.f₁`) — by committed node ID (GC-13(b)). The two imports are
`Uniformity.ChapC.C09` (pulling C.03, C.01) and `Uniformity.ChapC.C25` (pulling C.07, C.06,
C.22 and the B chain).

**PROOF.** Definitional. The bodies are the gate-verified `leanspec/Leanspec/ChapC.lean` stub
bodies verbatim (the NODE C.29 block hoisted into §4 there).

SOURCE: `EFF.HE6.10` (sides and labels); `EFF.HE6R1.13` ("let `(λ, r)` be a level-1 label of
`f`, `S = S_{λ,r}`, `f_S` the block factor"); DECISION C-D1.

**TEETH.** Signed **non-applicable** (definitions).

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declarations -/

/-- **C.29 (a) — level purity.** `IsDvPure F g u ℓ` : `g`'s level polygon is one-sided of slope
`u/ℓ`, i.e. both extreme abscissae `0` and `deg g / D′` (`D′ = e₁f₁`) lie on the side. B.34's
`IsPure` at the `dv`-carrier of C.06/C.07. -/
def IsDvPure (F : KeyFrame O π) (g : Polynomial O) (u ℓ : ℕ) : Prop :=
  0 ∈ dvSideSet F g u ℓ ∧ g.natDegree / (F.e₁ * F.f₁) ∈ dvSideSet F g u ℓ

/-- **C.29 (b) — the label predicate.** `HasLabel L g` : `g` is monic of positive degree,
`(L.u, L.ℓ)`-pure at the level, and its level residual `R_λ` (C.25) is a positive power of the
level datum's residual factor `L.r`. This is the closure-free surrogate for "every root of `g`
is a level-2 point with level-1 label `(λ, r)`" (DECISION C-D1; see the FAITHFULNESS note in the
file docstring — the root-side reading is NOT stated). -/
def HasLabel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : Prop :=
  g.Monic ∧ 0 < g.natDegree ∧ IsDvPure F g L.u L.ℓ ∧
  ∃ (hne₂ : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hpin₂ : dvHgt F g (dvSideMin F g L.u L.ℓ hne₂) = (M₀ : ℕ∞)) (m : ℕ),
    0 < m ∧ dvResPoly F H₀ hpin g L.u L.ℓ hne₂ M₀ hpin₂ = L.r ^ m

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.IsDvPure
#print axioms Uniformity.Density.Tower.HasLabel

end AxCheck
