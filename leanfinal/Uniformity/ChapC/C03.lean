/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C01
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C03 — `frameRes`, `stageField`, `stageCard`: the stage residual and its field

**Chapter C, NODE C.03** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C1, with ENV-C3's
`[Finite (ResidueField O)]` bound on the `stageCard` clause ALONE (GC-6.4, minimal binding).
Three signed declarations, all definitional. **This is a TERMINAL SUPPLY node** (chapter E's
ladder and chapter D's telescope consume the level dictionary from here).

For a frame `F` (C.01) with a correct pin `H₀`:

* `KeyFrame.frameRes F H₀ hpin` — the **frame residual** `ψ`, i.e. B.29's `resPoly` of the key
  read at the frame's own side `(h, e₁)` under the GC-1 `sideMin` pin. It is irreducible of
  degree `f₁` by the frame's own field `F.hresirr` (C.01), which is exactly the hypothesis
  `ψ ∈ F_Q[T]` irreducible of `EFF.HE6.08`.
* `KeyFrame.stageField F H₀ hpin` — the **stage residue field** `K = F_Q(η_θ)`, realised as
  `AdjoinRoot (frameRes …)`: chapter B's `resField` pattern (B.25) iterated once. This is
  GC-7's mandated carrier — an explicit quotient, never an `IntermediateField`.
* `KeyFrame.stageCard F` — the **stage residue cardinality** `Q^{f₁}` as a number. The identity
  `Nat.card (stageField …) = stageCard F` is C.04's business, not this node's.

## The pin argument, and why it is written out

`hpin` is the GC-1 pin proposition `npHgt X F.key (sideMin X F.key F.h F.e₁ F.hne) = H₀` — the
statement that `H₀` is the numeral naming the side's line height. The blueprint SIGNATURE writes
it out at `frameRes` and abbreviates it as `F.Pin H₀` at `stageField`; the gate-verified twin
(`leanspec/Leanspec/ChapC.lean`, defect **D4**) writes it out at BOTH sites, and the twin is
authoritative on divergence, so it is written out here. `KeyFrame.Pin` itself is C.14a's
declaration (A-C.1(c)) and is deliberately NOT introduced by this node: introducing it here
would put a chapter-C abbreviation between `frameRes`'s type and every §4 consumer of it before
its own node has landed.

`hpin` does not occur in `frameRes`'s BODY — `resPoly` takes the height numeral `H₀` directly.
It is carried in the signature because it is what makes `H₀` the *correct* numeral: without it
`frameRes` would be a family of junk polynomials indexed by an arbitrary `H₀`. The unused-binder
linter is silenced for exactly that declaration, with this as the reason.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (three definitions, no proof obligation; parent
CLAUDE.md trust boundary). Two recasts against `EFF.HE6.08`'s verbatim frame:

* *"`K := F_Q(η_θ) ≅ F_{Q^{f₁}}`"* is split into a CARRIER (`stageField`, the `AdjoinRoot`
  quotient) and a NUMBER (`stageCard`, the literal `Q^{f₁}`). The isomorphism asserted by the
  corpus's `≅` is not definitional here — it is C.04's `card_stageField`, and until C.04 lands
  the two clauses of `EFF.HE6.08`'s display are formally independent objects.
* The generator `η_θ = res(θ^{e₁}π^{−h})` is NOT constructed at this node. `stageField`'s
  generator is `AdjoinRoot.root`, introduced at C.19 as `stageLetter`; the identification with
  the corpus's `η_θ` is carried by the residual read, not by a closure-side root.

`stageField` is an `abbrev` on purpose: mathlib's `Field`/`Algebra` instances for `AdjoinRoot`
must apply to it unchanged, exactly as B.25 made `resField` an `abbrev` for the same reason.
Note that the `Field` instance is NOT available at this node's binders — it needs
`Fact (Irreducible (frameRes …))` (from `F.hresirr`) AND a `Field` structure on the base
`resField X` (defect **D9**'s `isKey_X` helper). Both are supplied at their consuming nodes
(C.22), never silently here.

**DEPENDS.** C.01 (`KeyFrame`, and its `hresirr` field for the irreducibility that makes
`stageField` a field downstream) · B.21 (`digAt`) / B.25 (`resField`, `resMk`) · B.28/B.29
(`resPoly`) · landed `residueCard` (`Uniformity/Density/LocalData.lean`) — all by committed node
ID (GC-13(b)). The imports are `Uniformity.ChapC.C01`, which pulls the whole B chain, and
`Uniformity.Density.LocalData` for `residueCard`.

**PROOF.** Definitional. The bodies are the gate-verified `leanspec/Leanspec/ChapC.lean` stub
bodies (the §3 A-C.1 layer) verbatim, including the **D18** cure (`stageCard` is
`noncomputable` — `residueCard` is).

SOURCE: `EFF.HE6.08` (“`K := F_Q(η_θ) ≅ F_{Q^{f₁}}`”); GC-7 (the `resField`-iterate mandate,
verbatim: *"iterated at level `r` over the previous level's residual key"*); GC-1 (the `sideMin`
pin convention).

**TEETH.** Signed non-applicable (definitions; the residue-field audits fire at C.04 and at
§13's gates).

ENVIRONMENT: ENV-C1; the `stageCard` clause adds `[Finite (ResidueField O)]` (ENV-C3, binding on
that declaration only).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

-- `hpin` is a correctness side condition on the numeral `H₀`, not an ingredient of the body
-- (`resPoly` takes `H₀` directly).  Dropping it from the signature is not an option: the
-- signature is A-C.1-signed and frozen, and without `hpin` the definition would be a family of
-- junk polynomials indexed by an arbitrary `H₀`.
set_option linter.unusedVariables false in
/-- The frame residual `ψ` — B.29's `resPoly` at the frame's side, under the GC-1 pin. -/
noncomputable def KeyFrame.frameRes (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Polynomial (resField (Polynomial.X : Polynomial O)) :=
  resPoly π Polynomial.X F.key F.h F.e₁ F.hne H₀

/-- The stage residue field `K = F_Q(η_θ) ≅ F_{Q^{f₁}}`, as an iterated `AdjoinRoot` (GC-7).
An `abbrev`, so that mathlib's `AdjoinRoot` instances apply to it unchanged (B.25's precedent
for `resField`). -/
abbrev KeyFrame.stageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Type _ :=
  AdjoinRoot (F.frameRes H₀ hpin)

/-- `|K| = Q^{f₁}` as a number (the lemma-level identity is C.04).
**D18 (cured):** the blueprint signs a plain `def`; `residueCard` is `noncomputable`, so it
must be. -/
noncomputable def KeyFrame.stageCard (F : KeyFrame O π) [Finite (ResidueField O)] : ℕ :=
  residueCard O ^ F.f₁

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.frameRes
#print axioms Uniformity.Density.Tower.KeyFrame.stageField
#print axioms Uniformity.Density.Tower.KeyFrame.stageCard

end AxCheck
