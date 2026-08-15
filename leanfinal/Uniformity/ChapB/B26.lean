/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B25
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapB.B26 — the residual field is finite of the right size

**Chapter B, NODE B.26** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual
layer), ENV-C.

For an order-1 key `φ` (B.01's `IsKey`) with `m := φ.natDegree`, B.25's residual field
`resField φ = F[y]/(φ̄)` (`F = ResidueField O`) is an `F`-vector space of dimension `m`, it is
finite, and its cardinality is `q ^ m` where `q = residueCard O = Nat.card F`.

Three declarations:

* `finrank_resField` — `Module.finrank F (resField φ) = φ.natDegree`;
* `instFiniteResField` — `Finite (resField φ)`;
* `card_resField` — `Nat.card (resField φ) = residueCard O ^ φ.natDegree`.

## The repaired form (blueprint `[repaired: A-F.3/B-D2+B-D3]`)

The stage-0e stub gate (`leanspec/Leanspec/ChapB.lean`) found the blueprint's middle row doubly
mis-signed, and both repairs are transcribed here.

* **B-D2 (kind).** `instFiniteResField` was signed as a `noncomputable instance` **with no
  body**: `Finite (resField φ)` is a proof obligation, not a definitional body, so the row is
  `[lemma]`-kind like the rest of this node and lands as a `theorem`.
* **B-D3 (declaration class).** An `instance` carrying the explicit non-class hypothesis
  `(hφ : IsKey φ)` is a HARD ERROR at our pin (*"This instance has 1 argument that cannot be
  inferred using typeclass synthesis"*), exactly as for B.25's `instFieldResField`.
  **Consumers bring finiteness into scope explicitly**, by `haveI := instFiniteResField hφ`;
  nothing here is found by typeclass synthesis.

Note that none of the three needs B.25's `instFieldResField`: `AdjoinRoot.powerBasis` asks only
that the *base* `F` be a field and that `φ̄ ≠ 0`, so the whole node runs over the plain
`CommRing` structure of `AdjoinRoot φ̄` and no `letI` is required.

## Type diff against the stage-0e stub — a known `axiom`-vs-`theorem` inclusion artifact

The three rows are declared here in ENV-C exactly as the blueprint's ENVIRONMENT field says, and
Lean's use-driven section-variable inclusion then trims each signature. It trims a `theorem`
(statement **and** proof) less than it trims an `axiom` (statement only), so two rows land with
an instance the stub's `axiom` shed:

| row | stub (`LeanspecB`, `axiom`) | here (`theorem`) |
|---|---|---|
| `finrank_resField` | `[IsAdicComplete]` | identical (`Finite` `omit`ted — genuinely unused) |
| `instFiniteResField` | neither instance | `[IsAdicComplete] [Finite (ResidueField O)]` |
| `card_resField` | neither instance | `[IsAdicComplete]` (`Finite` `omit`ted) |

Rows (a) and (c) reproduce the stub's elaborated type. The extra `[Finite (ResidueField O)]` on
row (b) is **not** a weakening introduced here: it is the ENV-C hypothesis the blueprint already
carries, which the stub's `axiom` form silently dropped because the *statement* never names it.
Without it row (b) is outright **false** — over `O = ℚ⟦t⟧` (a DVR with infinite residue field
`ℚ`) and `φ = X`, `resField φ ≅ ℚ` is infinite, so `Finite (resField φ)` fails while every other
hypothesis of the stub's elaborated form holds.  **Recorded for the 0e type diff**: on row (b)
the mismatch is the stub's, not the transcription's.

DEPENDS: B.01 (`IsKey`) · B.25 (`resField`) · landed `Uniformity.Density.residueCard`
(`Density/LocalData.lean:72`) · mathlib `AdjoinRoot.powerBasis`, `AdjoinRoot.powerBasis_dim`,
`PowerBasis.finrank`, `Polynomial.Monic.natDegree_map`, `Module.Finite.of_basis`,
`Module.finite_of_finite`, `Module.natCard_eq_pow_finrank`.

**PROOF.**
1. `(φ.map (residue O)).natDegree = φ.natDegree` by `Monic.natDegree_map hφ.monic`.
2. `AdjoinRoot.powerBasis` (needs `φ̄ ≠ 0`, from `hφ.irred.ne_zero`) has dimension
   `(φ.map (residue O)).natDegree`; `PowerBasis.finrank` gives `finrank_resField`.
3. `Finite`: the power basis makes `resField φ` a finite `F`-module (`Module.Finite.of_basis`),
   and `F` is finite by the bundle's `[Finite (ResidueField O)]`; `Module.finite_of_finite`.
4. `card_resField`: `Module.natCard_eq_pow_finrank` with steps 2 and 3, and
   `residueCard O = Nat.card (ResidueField O)` definitionally.

The blueprint's DEPENDS line flagged `Module.card_eq_pow_finrank` as needing confirmation at the
pin. Confirmed: that name exists but is the `Fintype.card` form
(`Mathlib/FieldTheory/Finiteness.lean:92`); the `Nat.card` form this node's statement wants is its
neighbour `Module.natCard_eq_pow_finrank` (same file, line 97), which takes `[Module.Finite K V]`
rather than `[Fintype V]` and so needs no `Fintype` transport. The blueprint's stated fallback
(`Nat.card_congr … .equivFun.toEquiv` then `Nat.card_fun`) is exactly that lemma's own proof, so
it is not needed separately.

## Faithfulness

`docs/GMN_citations.md` fact (I), NS-4, at order 1; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`
NS-4 gives verdict `COVERS-ALL-O` with the note "**Finiteness** is then immediate and
characteristic-free — it follows from `F` finite, which is our hypothesis, not theirs", which is
steps 3–4 above. `EFF.W12.25`'s residual censuses are stated over `Q = q^d`; `card_resField` is
the identification `Q = q^m` that lets `W12-CENSUS4` (`EFF.W12.57`) be read over
`card (resField φ)`.

SOURCE: `docs/GMN_citations.md` fact (I), NS-4; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-4;
`EFF.W12.25`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open IsLocalRing

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The power basis of the residual field over `F = ResidueField O`, available for any key.
Private: only the three public rows below are signed. -/
private noncomputable def keyPowerBasis {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {φ : Polynomial O} (hφ : IsKey φ) :
    PowerBasis (ResidueField O) (resField φ) :=
  AdjoinRoot.powerBasis hφ.irred.ne_zero

omit [Finite (ResidueField O)] in
/-- **B.26 (a) — the residual field has the right dimension.** `[resField φ : F] = φ.natDegree`
for an order-1 key `φ`.  Residue finiteness is `omit`ted: the dimension count is
characteristic- and cardinality-free, and dropping it reproduces the stub gate's own elaborated
type for this row exactly (see the type-diff note in the module docstring). -/
theorem finrank_resField {φ : Polynomial O} (hφ : IsKey φ) :
    Module.finrank (ResidueField O) (resField φ) = φ.natDegree := by
  have hne : φ.map (residue O) ≠ 0 := hφ.irred.ne_zero
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne,
    hφ.monic.natDegree_map (residue O)]

/-- **B.26 (b) — the residual field is finite.** Blueprint `[repaired: A-F.3/B-D2+B-D3]`: a
`theorem`, not a body-less `instance` — consumers write `haveI := instFiniteResField hφ`. -/
theorem instFiniteResField {φ : Polynomial O} (hφ : IsKey φ) : Finite (resField φ) := by
  haveI : Module.Finite (ResidueField O) (resField φ) :=
    Module.Finite.of_basis (keyPowerBasis hφ).basis
  exact Module.finite_of_finite (ResidueField O)

omit [Finite (ResidueField O)] in
/-- **B.26 (c) — the residual field has `q ^ m` elements.** `q = residueCard O` is the residue
cardinality of the local base and `m = φ.natDegree`.  Residue finiteness is `omit`ted here too:
`Module.natCard_eq_pow_finrank` needs only `Module.Finite F (resField φ)`, which the power basis
supplies, and the identity degenerates correctly (`0 = 0 ^ m`, `m > 0`) when `F` is infinite —
so this row also lands on the stub gate's elaborated type exactly. -/
theorem card_resField {φ : Polynomial O} (hφ : IsKey φ) :
    Nat.card (resField φ) = residueCard O ^ φ.natDegree := by
  haveI : Module.Finite (ResidueField O) (resField φ) :=
    Module.Finite.of_basis (keyPowerBasis hφ).basis
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O), finrank_resField hφ]
  rfl

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.finrank_resField
#print axioms Uniformity.Density.Leaf.instFiniteResField
#print axioms Uniformity.Density.Leaf.card_resField
end AxCheck
