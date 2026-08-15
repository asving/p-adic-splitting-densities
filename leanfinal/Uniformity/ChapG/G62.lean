/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G62 — `CubicFamilyIndex`, the ANNEX-B 53-family index

**Chapter G, NODE G.62** (`blueprint/CHAP-G_base_cases_menus.md` §9). *The cubic family index
(ANNEX B).* HMENU3's menu, after ANNEX B's fixed-`λ` and `b(m)`-regime refinements, consists of
**53 formal families** organised as `3` SEP + `4` DBL + `11` tier-I + `11` tier-II + `24` B-tier,
refining `33` shape schemas (`3 + 4 + 7 + 7 + 12`).

DEPENDS: none (a finite index type).

**⚠ WHAT THIS NODE IS.** ANNEX B is a **counter re-reading**, not a mathematical correction: its
own closing sentence fences it — "This annex repairs a formal indexing gap. It changes no
raw-key law, density, complement, splitting-type formula, machine result or conditionality"
(`EFF.HMENU3` resolution rule 3). This node formalises *the index arithmetic only*, and
`card = 53` (G.63, out of this node's scope) is the entire Lean content of ANNEX B. Nobody may
read this node as the cubic menu.

## Disposition

* **`CubicFamilyIndex` — LANDED AS STATED.** The five-tier inductive, verbatim against the
  blueprint SIGNATURE.
* **`CubicFamilyIndex.schema` — LANDED (blueprint defect **D2 CURED**, AMENDMENT 2026-08-15
  §A-5).** The blueprint SIGNATURE declared `def CubicFamilyIndex.schema : CubicFamilyIndex →
  Fin 33` with **no body**; the body was underdetermined by the blueprint's prose, which asserts
  the shape of the assignment ("`3 + 4 + 7 + 7 + 12` targets … each pair `(m = 0, m ≥ 1)` or
  `(λ = (1,1), λ = (2))` collapsing to one schema") but never tabulated it. Rather than
  manufacture an assignment here, the table was **derived from the primary source**
  (`spec/EFF-HMENU3.md`, ANNEX B) and the blueprint was amended with the derivation and the
  displayed table; this file lands that body **at the unchanged signature**. The nine derivation
  steps, with their EFF citations, are in the blueprint amendment; the summary is:

  * `Fin 33` is the five consecutive blocks `0–2` SEP, `3–6` DBL, `7–13` tier I, `14–20` tier II,
    `21–32` B-tier — `EFF.HMENU3.69`'s schema column (`3 + 4 + 7 + 7 + 12`), in the constructor
    order the blueprint STATEMENT itself uses;
  * SEP and DBL are **unrefined** (`EFF.HMENU3.69`, both rows' refinement cell empty), so those
    seven fibers are singletons; members named at `EFF.HMENU3.14` (`{SEP3, SEPLQ, SEPC}`,
    `{DBL-RAM, DBL-2SIDED, DBL-SPLITEQ, DBL-INERTDEEP}`);
  * inside a TRP tier exactly three of the seven schemas retain `λ` — `('VERT1', u₀, k, λ)`,
    `('VERT2', u₀, t, λ)`, `('FULL', k, λ)` (`EFF.HMENU3.67`) — so the four λ-free schemas
    (RAM3, 3LIN, LINRAM2, RAM2LIN, `EFF.HMENU3.69`) are singletons and the three λ-retaining ones
    carry fibers of size `#Λ₂ = 2`, `#Λ₂ = 2`, `#Λ₃ = 3` with `Λ₂ = {(1,1), (2)}`,
    `Λ₃ = {(1,1,1), (1,2), (3)}` (`EFF.HMENU3.68`); `4 + 2 + 2 + 3 = 11` ✓;
  * tier II is the same seven schemas under the `DEEP-` prefix bracket (`EFF.HMENU3.11`) with "the
    same fixed-λ refinement" (`EFF.HMENU3.69`), so its pattern is forced equal to tier I's;
  * the twelve B-schemas (`B1/B2/B3` × `{RAM, 2SIDED, SPLITEQ, INERTDEEP}`, `EFF.HMENU3.11`) each
    split into their `m = 0` / `m ≥ 1` regimes (`EFF.HMENU3.69`, `EFF.HMENU3.37`) — **not** by `λ`,
    which the dictionary already fixes on the β side (`EFF.HMENU3.09`) — giving twelve fibers of
    size 2, i.e. `bTier i ↦ 21 + i / 2`.

  **What is derived and what is convention.** The *fiber partition* is forced by the source and is
  the entire content of a map into an unlabelled `Fin 33`. The enumeration order inside each `Fin`
  is the sources' own list order; any other choice differs by a relabelling, under which G.63's
  `schema_surjective` — the sole declared consumer — is invariant. No family is left ambiguous.

## Status

`CubicFamilyIndex`, `CubicFamilyIndex.schema`: sorry-free, axiom-free (Lean core only). Checked
against the landed body: `Fintype.card CubicFamilyIndex = 53` by `decide`, and
`Function.Surjective CubicFamilyIndex.schema` by `decide` (at `maxRecDepth 8000`) — so G.63 is
fireable. Fiber-size profile over the 33 schemas:
`[1,1,1, 1,1,1,1, 1,1,1,1,2,2,3, 1,1,1,1,2,2,3, 2,2,2,2,2,2,2,2,2,2,2,2]`, sum `53` ✓.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- The ANNEX-B index of the cubic core menu: 53 formal families in five tiers. This is an
INDEX, not a family: it carries no counts and no certificates. See the chapter honesty block
H-3. -/
inductive CubicFamilyIndex
  | sep    : Fin 3  → CubicFamilyIndex
  | dbl    : Fin 4  → CubicFamilyIndex
  | tierI  : Fin 11 → CubicFamilyIndex
  | tierII : Fin 11 → CubicFamilyIndex
  | bTier  : Fin 24 → CubicFamilyIndex
  deriving DecidableEq, Fintype

/-- The shape schema underlying each formal family (ANNEX B's "33 shape schemas").

The table is the one derived at blueprint AMENDMENT 2026-08-15 §A-5 from `spec/EFF-HMENU3.md`
(ANNEX B), curing defect D2. Reading the rows: `sep`/`dbl` are unrefined, one schema each
(`EFF.HMENU3.69`); each TRP tier's four λ-free families RAM3, 3LIN, LINRAM2, RAM2LIN take one
schema each, then `VERT1` (`λ ∈ Λ₂`, two families) and `VERT2` (`λ ∈ Λ₂`, two) and `FULL`
(`λ ∈ Λ₃`, three) collapse onto one schema apiece (`EFF.HMENU3.67`, `.68`, `.69`); each of the
twelve B-schemas `B1/B2/B3 × {RAM, 2SIDED, SPLITEQ, INERTDEEP}` carries its `m = 0` and `m ≥ 1`
regime as two families (`EFF.HMENU3.11`, `.37`, `.69`). -/
def CubicFamilyIndex.schema : CubicFamilyIndex → Fin 33
  | .sep i    => ![0, 1, 2] i
  | .dbl i    => ![3, 4, 5, 6] i
  | .tierI i  => ![7, 8, 9, 10, 11, 11, 12, 12, 13, 13, 13] i
  | .tierII i => ![14, 15, 16, 17, 18, 18, 19, 19, 20, 20, 20] i
  | .bTier i  => ![21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26,
                   27, 27, 28, 28, 29, 29, 30, 30, 31, 31, 32, 32] i

end Uniformity.Density.Menu
