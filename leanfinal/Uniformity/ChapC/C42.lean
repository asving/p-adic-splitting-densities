/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C03

/-!
# Uniformity.ChapC.C42 — `TowerDatum`, `D₂`, `E₂`: the composed frame (tower) datum

**Chapter C, NODE C.42** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed keys and
the tower bridges; the A-C.1 amendment set governs). **ENV-C1**. Three signed declarations, all
definitional. This is the level-2 analogue of C.01's `KeyFrame`: the packet of *inner-stage* data
that every §6 node quantifies over.

Over a frame `F` (C.01) with a correct pin `H₀` (C.03's convention):

* `TowerDatum F H₀ hpin` — the **inner side data** `(e₂, f₂, u₂, ψ₂)` of `EFF.GENTOW5.413`'s
  depth-2 tower: an inner slope `κ₂ = u₂/e₂` in lowest terms, an inner residual `ψ₂` monic
  irreducible of degree `f₂` with `ψ₂(0) ≠ 0`, living over the **stage field**
  `F.stageField H₀ hpin = K` (C.03) — not over `O`'s residue field, which is the whole point of
  the tower: the level-2 residual is read in `K = F_{Q^{f₁}}`, and `K[Z]/(ψ₂) ≅ F_{Q^{f₁f₂}}` is
  the corpus's `K₂`.
* `TowerDatum.D₂ T` — the **composed degree** `D₂ = D′·e₂f₂ = (e₁f₁)(e₂f₂)`, the degree of the
  composed key `Φ₂` that C.43 builds.
* `TowerDatum.E₂ T` — `EFF.GENTOW1.07`'s **ONE NEW CONSTANT** `E₂ = e₂f₂u₂`, the `dv₂`-height of
  every side term of `Φ₂`.

## Why `E₂` gets a name of its own (the SPLIT)

At level 1 the key's side height and `dv(x^{D′})` coincide, both `D′h`; at level 2 they
**separate**, and `E₂` — not `dv₂(x^{D₂}) = D₂e₂h` — is the true floor. `EFF.GENTOW1.07` states
the gap and its cause verbatim: *"here they SPLIT: `E₂ > dv₂(x^{D₂}) = D₂e₂h = e₂f₂·(e₂D′h)`, by
`u₂ > e₂D′h`"*. That inequality is a **lemma about this datum, and it is C.50's, not this
node's** — here only the hypothesis `hfloor` that makes it true is recorded. Consumers needing
`E₂ > D₂·e₂·h` must cite C.50 (`E₂_gt_xfloor`), never re-derive it inline.

The arithmetic, for the record: `E₂ = e₂f₂u₂ > e₂f₂·(e₂·e₁f₁·h) = (e₁f₁e₂f₂)·e₂h = D₂·e₂h`,
using `hfloor` once and `0 < e₂f₂` (from `hcomp`) once. So `hfloor` is exactly load-bearing for
the SPLIT and is not decorative.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (a structure of hypotheses; parent CLAUDE.md trust
boundary). Field-by-field against `EFF.GENTOW5.413`'s datum list — *"inner side data
`(u2, e2, psi2, mu2)` with `gcd(u2, e2) = 1`, `f2 = deg psi2`, `e2f2mu2 = mu1`; … `E2 := e2f2u2`;
node floor `u2 > e2D'h`"* — and `EFF.HETOW.15` (LEMMA HETOW-1's opening datum):

* `hcop : Nat.Coprime u₂ e₂` ⟷ `gcd(u2, e2) = 1` ✓ (the slope in lowest terms).
* `hψdeg : ψ₂.natDegree = f₂` ⟷ `f2 = deg psi2` ✓ — `f₂` is a *field* of the structure and
  `hψdeg` pins it, rather than `f₂` being defined as the degree. Equivalent, and it is the twin's
  reading; the effect is that `f₂` is available as a numeral in the other fields' types.
* `hfloor : e₂ * (F.e₁ * F.f₁) * F.h < u₂` ⟷ the `[r1]` node floor `u2 > e2D'h` with
  `D′ = e₁f₁` ✓ (`EFF.GENTOW1.242`: *"imported from GENHN-1's [r1] erratum and … consumed at four
  separate places"*). The corpus writes `>`; Lean writes the same relation as `<` with the sides
  swapped, which is `Nat.lt` in both cases.
* `hψmonic`, `hψirr`, `hψ0` ⟷ HETOW-1(a)'s *"monic irreducible of degree `f₂` with `r̃(0) ≠ 0`"*
  transported back to `ψ₂` (HETOW-1 states it for the translated label `r̃ = η^{−Qf₂}ψ₂(η^Q Z)`;
  the properties are equivalent under that invertible substitution, which is C.44's business).
* `hcomp : 2 ≤ e₂ * f₂` — the blueprint's own nondegeneracy fence (STATEMENT: *"a composite
  inner stage"*). It is what makes level 2 a genuine extension: `D₂ = D′·e₂f₂ > D′`. **Not
  sourced to a corpus display**; flagged here as chapter-added.

**Two things the corpus datum carries that this structure does NOT**, and which therefore must
be supplied by consuming nodes rather than assumed available from a `TowerDatum`:

1. **`μ₂`, and the full-inner-side condition `e₂f₂μ₂ = μ₁`.** `EFF.GENTOW1.14` fences the
   tower-entry locus `𝒯` to FULL inner sides and repeats the fence at `.46` (*"partial inner
   sides (`e2f2mu2 < mu1`) … every S2–S4 statement is scoped to it"*). `μ₂` is not a field here;
   §6's later nodes take it as a separate explicit argument (`… (μ₂ : ℕ)`), and the full-side
   condition appears nowhere in this node. **A `TowerDatum` alone does not place anything on
   `𝒯`.**
2. **The locus itself** — `Φ₂`, the composed key, and the genre-G opening conditions. This node
   is data only; the key is C.43.

`he₂ : 0 < e₂` and `hf₂ : 0 < f₂` are **derivable from `hcomp`** (`2 ≤ e₂ * f₂` forces both
factors nonzero). The redundancy is in the signed field list and is kept verbatim: extra
*provable* fields cannot make a structure unsound, only more tedious to build, and the signatures
are frozen.

The constraint set is jointly satisfiable — nothing here is vacuous by arithmetic. Witness
schema: `e₂ = 1`, `f₂ = 2`, `u₂ = F.e₁ * F.f₁ * F.h + 1` (so `hcop` is `Nat.Coprime _ 1`, trivial;
`hfloor` is `e₁f₁h < e₁f₁h + 1`; `hcomp` is `2 ≤ 2`), with `ψ₂` any monic irreducible quadratic
over `K` with nonzero constant term. This is an arithmetic sanity check on the ℕ-fields only, NOT
a Lean-verified inhabitance theorem: producing `ψ₂` needs `K` to be a field, which at this node's
binders it is not (C.03's rider — `stageField` gets its `Field` instance only at C.22).

## Divergence from the blueprint SIGNATURE (twin authoritative)

Two, both from the leanspec gate's defect list, both binder-level:

* **D4** — the blueprint writes the pin binder as `(hpin : _)`. A `_` binder type has nothing to
  infer from in a `structure` header, so it is written out in full as
  `npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)`, exactly as
  C.03 already does at `frameRes`/`stageField`. Same proposition, spelled.
* **D2** — the blueprint writes `def TowerDatum.D₂ … : ℕ` and `def TowerDatum.E₂ … : ℕ` with a
  literal ellipsis for the binder list. C.42 is one of the four nodes the gate classifies as
  *"the surrounding prose forces a unique reading of the omitted binders"*, and the twin
  completes it as `{F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin)`. That is the only
  reading under which the signed bodies `(F.e₁ * F.f₁) * (T.e₂ * T.f₂)` and `T.e₂ * T.f₂ * T.u₂`
  typecheck.

**DEPENDS.** C.01 (`KeyFrame` and its `e₁`, `f₁`, `h`) · C.03 (`stageField`, and the pin
convention its signature fixes) — by committed node ID (GC-13(b)). The single import is
`Uniformity.ChapC.C03`, which pulls C.01 and the whole B chain.

**PROOF.** Definitional. The structure and both derived numerals are the gate-verified twin
`leanspec/Leanspec/ChapC.lean` verbatim.

SOURCE: `EFF.HETOW.15` (the datum LEMMA HETOW-1 opens with); `EFF.GENTOW1.07` (`E₂ := e₂f₂u₂`,
the two-family height verification, and the SPLIT `E₂ > dv₂(x^{D₂}) = D₂e₂h` — the lemma half
lands at C.50); `EFF.GENTOW1.14` (the genre data list, and the FULL-inner-side fence quoted
above); `EFF.GENTOW5.413` (the depth-2 tower datum in one display).

**TEETH.** `EFF.GENTOW1.07`'s five-family arithmetic audit (`E₂ = 10/14/6/21/6` against
`dv₂(x^{D₂}) = D₂e₂h = 8/8/4/18/4`) → **§13 regression rows**; not dischargeable at this node's
binders, since a `TowerDatum` over an abstract `KeyFrame O π` supplies no numeral to `#guard`.
Three of the five rows display their `(e₂, f₂, u₂)` in the audit text and are checked here against
the two bodies that land, including the node floor this structure imposes:

| family | `(e₂,f₂,u₂)` | `E₂ = e₂f₂u₂` | `D₂e₂h` | `e₂·D′h` floor vs `u₂` |
|---|---|---|---|---|
| A5 | `(2,1,5)` | `10` | `8` | `4 < 5` ✓ |
| B  | `(1,2,3)` | `6`  | `4` | `2 < 3` ✓ |
| C  | `(3,1,7)` | `21` | `18`| `6 < 7` ✓ |

(the floor column reads `D′h = e₁f₁h = 2` back off the companion `D₂e₂h` value in each row, since
the families' `(e₁, f₁, h)` are not displayed in `.07`'s audit text). All three satisfy `hfloor`
and all three exhibit the SPLIT, as they must.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The **composed frame (tower) datum**: the inner side data `(e₂, f₂, u₂, ψ₂)` of the depth-2
tower over the frame `F` at the pinned height `H₀` (`EFF.HETOW.15`, `EFF.GENTOW5.413`).  The
inner slope is `κ₂ = u₂/e₂` in lowest terms (`hcop`); `ψ₂` is the inner residual, read over the
STAGE field `K = F.stageField H₀ hpin` (C.03), not over `O`'s residue field.

**Not carried here** (see the module docstring): `μ₂` and the full-inner-side scope
`e₂f₂μ₂ = μ₁`, and the tower-entry locus `𝒯` itself.  A `TowerDatum` is data, not a locus.
[A-C.1/D4: the pin binder is written out, as at C.03.] -/
structure TowerDatum (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    where
  /-- The inner ramification index; denominator of the inner slope `κ₂ = u₂/e₂`. -/
  e₂ : ℕ
  /-- The inner residual degree; pinned to `ψ₂.natDegree` by `hψdeg`. -/
  f₂ : ℕ
  /-- The inner slope numerator, subject to the `[r1]` node floor `hfloor`. -/
  u₂ : ℕ
  /-- The inner residual, over the stage field `K` (C.03). -/
  ψ₂ : Polynomial (F.stageField H₀ hpin)
  he₂ : 0 < e₂
  hf₂ : 0 < f₂
  /-- A composite inner stage: `D₂ = D′·e₂f₂` is a genuine enlargement of `D′`.
  Chapter-added nondegeneracy fence; it also implies `he₂` and `hf₂`. -/
  hcomp : 2 ≤ e₂ * f₂
  hcop : Nat.Coprime u₂ e₂
  /-- The `[r1]` **node floor** `u₂ > e₂D′h` with `D′ = e₁f₁` (`EFF.GENTOW1.242`), the hypothesis
  behind C.50's SPLIT `E₂ > dv₂(x^{D₂})`. -/
  hfloor : e₂ * (F.e₁ * F.f₁) * F.h < u₂
  hψmonic : ψ₂.Monic
  hψirr : Irreducible ψ₂
  hψdeg : ψ₂.natDegree = f₂
  hψ0 : ψ₂.coeff 0 ≠ 0

/-- The composed degree `D₂ = D′·e₂f₂ = (e₁f₁)(e₂f₂)` — the degree of C.43's composed key `Φ₂`.
[A-C.1/D2: the blueprint's `def TowerDatum.D₂ … : ℕ` ellipsis is completed by the twin's binder
list, the only one under which the signed body typechecks.] -/
def TowerDatum.D₂ {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) : ℕ :=
  (F.e₁ * F.f₁) * (T.e₂ * T.f₂)

/-- `EFF.GENTOW1.07`'s ONE NEW CONSTANT `E₂ = e₂f₂u₂`: the `dv₂`-height of every side term of
`Φ₂`.  The SPLIT `E₂ > dv₂(x^{D₂}) = D₂·e₂h` — the reason this needs its own name — is a LEMMA
about the datum and belongs to C.50, not to this node. -/
def TowerDatum.E₂ {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) : ℕ :=
  T.e₂ * T.f₂ * T.u₂

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.TowerDatum
#print axioms Uniformity.Density.Tower.TowerDatum.mk
#print axioms Uniformity.Density.Tower.TowerDatum.D₂
#print axioms Uniformity.Density.Tower.TowerDatum.E₂

end AxCheck
