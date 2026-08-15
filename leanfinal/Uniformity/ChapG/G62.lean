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
* **`CubicFamilyIndex.schema` — BLOCKED (pre-existing blueprint defect D2, not introduced
  here).** The blueprint SIGNATURE declares `def CubicFamilyIndex.schema : CubicFamilyIndex →
  Fin 33` with **no body**, and the body is underdetermined by the blueprint's prose: which of
  the 53 formal families collapse onto which of the 33 shape schemas is asserted
  ("`3 + 4 + 7 + 7 + 12` targets … each pair `(m = 0, m ≥ 1)` or `(λ = (1,1), λ = (2))` collapsing
  to one schema") but never tabulated. This is exactly the defect already caught at the stage-0e
  leanspec gate (`leanspec/Leanspec/ChapG.lean`, item D2: "DEF WITH NO BODY … a blueprint
  amendment owes the table"), landed there as an `axiom`-typed placeholder for the same reason.
  Per the honesty invariant (definitions are where errors hide; never invent an unfaithful body
  to force a green build), this node does not manufacture an arbitrary 53→33 assignment: doing
  so would be a *silent* choice masquerading as the ANNEX-B table, exactly the failure mode the
  trust boundary warns against. The obstruction is BLOCKED-on-blueprint-amendment, not a Lean
  proof gap: `schema` is not landed by this file, and no downstream node of this chapter's
  layer-0 batch consumes it (`G.63`'s `card_cubicFamilyIndex`/`schema_surjective` are a
  different, non-fireable node).

## Status

`CubicFamilyIndex`: sorry-free, axiom-free (Lean core only). `CubicFamilyIndex.schema`: BLOCKED,
obstruction D2 (blueprint amendment owed — the 53→33 assignment table).
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

/- **BLOCKED — obstruction D2.** The shape schema underlying each formal family (ANNEX B's
"33 shape schemas") has no body determined by the blueprint's prose; landing a `def` here would
require inventing the 53→33 assignment table, which is not stated anywhere in the source. A
blueprint amendment owes the table (matching the stage-0e leanspec disposition verbatim):

    def CubicFamilyIndex.schema : CubicFamilyIndex → Fin 33

Not landed. -/

end Uniformity.Density.Menu
