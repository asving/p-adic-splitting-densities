/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E10
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Uniformity.ChapE.E11 — `BlockData`, `ladderSuppVal`, `onLadderSide`, `devHgt`

**Chapter E, NODE E.11** [def] (`blueprint/CHAP-E_sigma_ladder.md` §4), ENV-E2 (the carrier
arena: the standing bundle `O`, the label field `K`, and a slot carrier `C : SlotCarrier O K`
from E.10).

T2's block layer S1.5–S1.6 as fields, plus the polygon-free support function §5 reads them
through:

* **`BlockData C`** — a σ-block over the slot carrier: the monic key `Φ` of degree `C.D`, the
  polynomial `F` with its `Φ`-development `(DEV)` `F = Φ^μ + Σ_{j<μ} A_j Φ^j` with
  `deg A_j < C.D`, key-freeness `(KEY-FREE)` and its consumed polygon shadow `A₀ ≠ 0`, and the
  inherited threshold `T`;
* **`ladderSuppVal hgt u ℓ μ = inf_{j ≤ μ} (ℓ • hgt j + j·u)`** — the cleared support value of a
  development, D-1/GC-2's support-function representation one abstraction level up: an `inf` of
  `ℤ`-linear forms on abstract heights, not a polygon;
* **`onLadderSide`** — its argmin predicate, from which sides, slopes and lengths are derived
  predicates. **No polygon type is declared in chapter E**, by design: E consumes the shape, and
  the geometry that produces it is owned below E (chapter B's D-1) and, for the ladder's own
  sides, supplied as `RungInterface` fields at E.12.
* **`BlockData.devHgt`** — the block's development heights `j ↦ C.hgt (A j)`, with the two
  boundary conventions the corpus uses: `0` at the monic top `j = μ` (the top coefficient is
  `1`, height `0`), and `⊤` above `μ` (the development stops).

`(NO-IRR)` FENCE (`EFF.T2.02`, boxed REDLINE; `EFF.T2.43`/`.44`): **`Φ` is monic and nothing
more** — there is no irreducibility field on `BlockData`, so an HE7 argument that needs the
current key to be irreducible cannot even be stated against this interface. This is the S7
reducible-key boundary gate discharged structurally rather than by hypothesis.

⚠ **KEY-FREENESS SPELLING** (blueprint DECISION, taken at the stub gate and re-affirmed here,
never silent). `EFF.T2.11`'s `(KEY-FREE)` reads `gcd_{K₀[x]}(F, Φ) = 1`. The landed spelling is
the mathlib-native, gcd-free `IsCoprime` over `FractionRing O` — the primary spelling of the
blueprint, NOT the pre-authorized `∀ g, g ∣ F → g ∣ Φ → IsUnit (g.map …)` fallback: the
`FractionRing` elaboration is cheap at this signature, so the fallback was not taken. `hA0` is
`(KEY-FREE)`'s consumed polygon shadow ("(KEY-FREE) implies A₀ ≠ 0", `EFF.T2.11`'s own
derivation), carried as a separate field so that E.13 consumes it without re-deriving field
theory inside the polygon argument. Note `FractionRing O` is only a `CommRing` here — no
`IsDomain O` is assumed, so this is the localization at `nonZeroDivisors O` and nothing stronger.

⚠ **WINDOW/CAP is NOT here.** `(WINDOW)` (`T < d(Φ(ρ)) < ∞`) and the `WindowSafe`/`CapSafe`
proxy assertions (`EFF.T2.11`) are ROOT-side and enter as E.12 continuation fields. The corpus's
own fence: proxy agreement is "not inferred merely from the phrase 'arising from a label'".

`ladderSuppVal` takes `hgt : ℕ → WithTop ℤ` as a bare function rather than a block, so that §5
can apply it to `devHgt`, to shifted developments, and to the abstract heights of E.14's
`SepSide` without a block in scope; `BlockData.devHgt` is the one intended argument at this
node. Values live in `WithTop ℤ` (D-E1, inherited from E.10): `⊤` is the height of `0`, and the
`inf` over `Finset.range (μ+1)` is `⊤` exactly when every abscissa `j ≤ μ` is `⊤` — which
`hΦ`/the `j = μ` convention rules out on a real block, since `devHgt μ = 0`.

Definitional, no proof obligation. Bodies reused verbatim from the gate-verified leanspec stub
(`leanspec/Leanspec/ChapE.lean`; E.11 is the second of §12(a)'s FRAGILE signatures). The
blueprint's SPLIT CANDIDATE (`ladderSuppVal`/`onLadderSide` into an `E11a`) was NOT taken: both
are three-line definitions over `WithTop ℤ`, elaboration is cheap, and splitting would separate
the support value from the development it is defined to read.

DEPENDS: E.10 (`SlotCarrier`) · mathlib `IsCoprime`, `FractionRing`, `Finset.inf`.

SOURCE: `EFF.T2.11` (`(DEV)`, `(KEY-FREE)`, `(WINDOW)`, the proxy fence, and the `A₀ ≠ 0`
derivation); `EFF.T2.02` (`(NO-IRR)`, boxed REDLINE); `EFF.HE7.09` (the standing `Ψ ∤ f_S`
convention, `hA0`'s analogue one level up: "equivalently the Ψ-development's constant
coefficient `A₀^{(2)} ≠ 0`"); CHAP-B D-1/GC-2 (the support-function representation reused in
shape here).

TEETH: S7 reducible-key boundary gate (`EFF.T2.02`) — structural, no irreducibility field
exists to consume. S7 Pass 2 dangerous-collected-term tooth (`EFF.T2.11`) — the proxy fence is
an instance obligation (C-side), recorded in §13, and deliberately absent from this structure.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free. Every declaration reports exactly the Lean-core triple
`{propext, Classical.choice, Quot.sound}` — `Classical.choice` arrives through the
`FractionRing`/`WithTop` instance graph, not through any project axiom (in particular not
B.42). Types checked against the signed SIGNATURE declaration by declaration (0e type diff).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- The cleared support value of a ladder development (D-1's shape on abstract heights):
`inf over j ≤ μ of (ℓ·hgt j + j·u)`. An `inf` of `ℤ`-linear forms in `WithTop ℤ`; no polygon
type is involved. -/
noncomputable def ladderSuppVal (hgt : ℕ → WithTop ℤ) (u ℓ μ : ℕ) : WithTop ℤ :=
  (Finset.range (μ + 1)).inf fun j => ℓ • hgt j + ((j * u : ℕ) : WithTop ℤ)

/-- Abscissa `j` lies on the `(u, ℓ)`-side of the ladder polygon: `j ≤ μ` and `j` attains the
support value `ladderSuppVal hgt u ℓ μ` (the argmin predicate). -/
def onLadderSide (hgt : ℕ → WithTop ℤ) (u ℓ μ : ℕ) (j : ℕ) : Prop :=
  j ≤ μ ∧ ℓ • hgt j + ((j * u : ℕ) : WithTop ℤ) = ladderSuppVal hgt u ℓ μ

/-- A **σ-block** over a slot carrier (T2 S1.5–S1.6, `EFF.T2.11`): a monic key `Φ` of the
carrier's degree, a polynomial `F` given by its `Φ`-development, key-freeness, and the
inherited threshold. Irreducibility of `Φ` is NEVER assumed (`(NO-IRR)`, `EFF.T2.02`). -/
structure BlockData {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) where
  /-- the current key; monic, of degree `C.D`, NOT assumed irreducible. -/
  Φ : Polynomial O
  /-- the polynomial being developed. -/
  F : Polynomial O
  /-- the development length (`deg F = μ · C.D`). -/
  μ : ℕ
  hμ : 1 ≤ μ
  hΦ : Φ.Monic
  hΦdeg : Φ.natDegree = C.D
  /-- the development coefficients; `A j = 0` for `j ≥ μ` by convention. -/
  A : ℕ → Polynomial O
  hdev : F = Φ ^ μ + ∑ j ∈ Finset.range μ, A j * Φ ^ j          -- (DEV)
  hdegA : ∀ j < μ, (A j).natDegree < C.D
  /-- `(KEY-FREE)`: `gcd_{K₀[x]}(F, Φ) = 1`, spelled `IsCoprime` over `FractionRing O`. -/
  hkeyfree : IsCoprime (F.map (algebraMap O (FractionRing O)))
      (Φ.map (algebraMap O (FractionRing O)))
  /-- `(KEY-FREE)`'s consumed polygon shadow, carried so E.13 need not re-derive it. -/
  hA0 : A 0 ≠ 0
  /-- the inherited threshold. -/
  T : ℕ

/-- The block's development heights: `devHgt j = hgt (A j)` for `j < μ`, `0` at the monic top
`j = μ`, `⊤` above. -/
noncomputable def BlockData.devHgt {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} (B : BlockData C) : ℕ → WithTop ℤ :=
  fun j => if j = B.μ then (0 : WithTop ℤ) else if j < B.μ then C.hgt (B.A j) else ⊤

end Uniformity.Density.Ladder

/-! ## Axiom footprint

Definitional node. The structure former asserts nothing about its fields, so the two fragile
fields — `(KEY-FREE)` in its `FractionRing` spelling and `(DEV)` — are printed too, together
with the three support/height definitions. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.ladderSuppVal
#print axioms Uniformity.Density.Ladder.onLadderSide
#print axioms Uniformity.Density.Ladder.BlockData
#print axioms Uniformity.Density.Ladder.BlockData.mk
#print axioms Uniformity.Density.Ladder.BlockData.hkeyfree
#print axioms Uniformity.Density.Ladder.BlockData.hdev
#print axioms Uniformity.Density.Ladder.BlockData.devHgt

end AxCheck
