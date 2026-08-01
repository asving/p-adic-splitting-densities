/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesRBase.Defs

/-!
# Scaffold/HDischarge/H4/Defs — units H4-L1, H4-L2, H4-L7

Statements VERBATIM from `lean/blueprints/HDISCHARGE_H4.md` §L.1 (compile-probed
text; probe record §L.0). Defs/structures only — no proof obligations.

REUSED carriers (§L.0, never duplicated here): `MovesRBase.SpeciesSyntax` /
`AlphabetData` / `AlphabetData.Stable` (base-index convention: δ ABSOLUTE).

FAITHFULNESS NOTES (§L.1, binding):
(i) `LedgerSkel.tree_stable` bundles M14 Lemma 1 + (R3) + (R4) INTO the carrier —
a CONFORMANCE ROW to be supplied by the eventual instance (fenced H4-F6), never
proved abstractly; until then H4-L2's rows are honest named assumptions, not
discharge. (ii) `dim_conf`'s `dbase δ x` at δ = 1 must read `[F₁ : F_p] = d`
(M14 Lemma 3); instances violating M14 §7.2 (prefix-stability encoding in
`posLetter`) are NOT covered. (iii) `RealizedLedger` types the INTERFACE SHAPE
only (positions, indices, membership) — no β-leg, residue-degree, or clause-(R)
semantics; value-side fields land at fenced H4-F2. L7 types the CURRENT
(Route-A-shaped) rows; Route B's face is fenced H4-F5.

§L.0 probe repair (do NOT undo): `SlotTree` as a `List`-nested inductive broke
`induction`; the `(m : ℕ) (children : Fin m → SlotTree)` form is the working one.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H4

open MovesRBase

/-- One OM read's numerical stage tuple `(e, h, g)` with Bézout companion `t`
(`h·t ≡ 1 mod e`). Shape data only — no residue field. -/
structure StageTuple where
  e : ℕ+
  h : ℤ
  t : ℤ
  g : ℕ+
deriving DecidableEq

/-- The Bézout invariant `h·t ≡ 1 (mod e)` — legality predicate for stage
tuples (finding 11 of the blueprint's Codex review: `anchorSlot` is intended
ONLY at legal tuples; instances must supply `Bez` alongside the raw data). -/
def StageTuple.Bez (s : StageTuple) : Prop :=
  (s.h * s.t) % (s.e : ℤ) = 1 % (s.e : ℤ)

/-- D.9(a) weight sets as a FUNCTION of the shape history (top stage first):
`𝒲₁ = e₁·ℤ≥0`; `𝒲_{k+1} = e_{k+1}·⋃_{0≤j<e_k g_k} (𝒲_k + j·h_k)`.
M14 Lemma 1(a) is thereby definitional; the per-base content is the
CONFORMANCE row (R3) of `LedgerSkel`. -/
def wSet : List StageTuple → Set ℤ
  | [] => ∅
  | [s] => Set.range fun v : ℕ => (s.e : ℤ) * v
  | s :: sk :: prior =>
      (fun w => (s.e : ℤ) * w) ''
        (⋃ j ∈ Finset.range ((sk.e : ℕ) * (sk.g : ℕ)),
          (· + (j : ℤ) * sk.h) '' wSet (sk :: prior))

/-- Anchor slot `j₀ ≡ t_k·γ* (mod e_k)` (D.3(e)(ii) skeleton). -/
def anchorSlot (sk : StageTuple) (γs : ℤ) : ℤ := (sk.t * γs) % (sk.e : ℤ)

/-- Slot heights `γ_i = γ* − (j₀ + i·e_k)·h_k`. -/
def slotHeight (sk : StageTuple) (γs : ℤ) (i : ℕ) : ℤ :=
  γs - (anchorSlot sk γs + (i : ℤ) * (sk.e : ℤ)) * sk.h

/-- Attainable index set `I(γ) = {i < g_k : γ_i ∈ 𝒲_k}`. -/
def attainIdx (sk : StageTuple) (W : Set ℤ) (γs : ℤ) : Set ℕ :=
  {i : ℕ | i < (sk.g : ℕ) ∧ slotHeight sk γs i ∈ W}

/-- The finite slot tree below one ledger position: leaves = base-stage reads,
nodes = the `I(γ)`-indexed slot recursion (D.3(e)(ii)); `m` = the attainable
index count `|I(γ)|` at the node. -/
inductive SlotTree where
  | base : SlotTree
  | node (m : ℕ) (children : Fin m → SlotTree)

/-- Alphabet `F_p`-dimension along a slot tree with base-leaf dimension `dbase`
(the product display `|𝔸(γ)| = Π_{i∈I(γ)} |𝔸_k(γ_i)|` read at exponents:
`a(k+1, γ) = Σ_{i∈I(γ)} a(k, γ_i)`). -/
def SlotTree.dimOf (dbase : ℕ) : SlotTree → ℕ
  | .base => dbase
  | .node m cs => ∑ i : Fin m, (cs i).dimOf dbase

variable (p : ℕ) [Fact p.Prime]

/-- **H4-L2 (`LedgerSkel`)** — the DIMENSION-LEVEL conformance carrier: the
typed face of the NUMERICAL slice of what M14's Theorem consumes from
(R1)–(R4) — and ONLY that slice (Codex review finding 7: the stage axioms,
digit maps, alphabet-product bijection, weight-set conformance, and (R4)
irreducibility data are NOT typed here; they are exactly the content the
eventual instance's rows must be PROVED from, at the H4-F6 carriers).
`tree δ x` = the realized height-lattice skeleton of position `x` over `O_δ`;
`dbase δ x` = the realized base dimension `[F₁^{(δ)} : F_p]`. Rows: the (R2)
product display read at dimensions (`dim_conf`), Lemma 1 + (R3) + (R4)
read at skeletons (`tree_stable`), Lemma 3's base scaling (`dbase_stable`) —
CONFORMANCE ROWS to be supplied by the instance, never proved abstractly. -/
structure LedgerSkel (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) where
  tree : ℕ+ → AD.Pos → SlotTree
  dbase : ℕ+ → AD.Pos → ℕ
  dim_conf : ∀ (δ : ℕ+) (x : AD.Pos),
    AD.aDim δ x = (tree δ x).dimOf (dbase δ x)
  tree_stable : ∀ (δ : ℕ+) (x : AD.Pos),
    AlphabetData.Stable p AD δ x → tree δ x = tree 1 x
  dbase_stable : ∀ (δ : ℕ+) (x : AD.Pos),
    AlphabetData.Stable p AD δ x → dbase δ x = (δ : ℕ) * dbase 1 x

/-- **H4-L7 (`RealizedLedger`)** — the realized-ledger carrier: `realized δ` is
the set of position classes the re-based classifier realizes over `O_δ`;
`Pool` indexes Step-18 K3-c's realized δ > 1 pools (the base-changed β-legs),
each riding a realized position (`pool_realized`) at pool index > 1. -/
structure RealizedLedger {Sp : SpeciesSyntax} (AD : AlphabetData p Sp) where
  realized : ℕ+ → Set AD.Pos
  Pool : Type
  poolIdx : Pool → ℕ+
  poolPos : Pool → AD.Pos
  pool_gt_one : ∀ P : Pool, 1 < (poolIdx P : ℕ)
  pool_realized : ∀ P : Pool, poolPos P ∈ realized (poolIdx P)

end LeanUrat.Scaffold.HDischarge.H4
