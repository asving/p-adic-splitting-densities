/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F07
import Uniformity.ChapF.F14
import Uniformity.ChapF.F17

/-!
# Uniformity.ChapF.F27 — `WeldSupply`: the weld layer's proved supply, as one record

**Chapter F, NODE F.27** [def] (`blueprint/CHAP-F_weld_layer.md` §9), ENV-F1 + `[Field K]`.
The terminal supply of the weld layer, packaged the way a consuming chapter instantiates it
(chapter D's gauge layer, chapter H's landed count layer, chapter I's assembly) — the CHAP-E
`LadderSupply`/`LadderObligations` pattern, noting with the E precedent's own care that these
are plain structures, with **no** claim of mirroring H.95's `def`-`Prop` kind.

**What the three fields buy.** Together they carry every PROVED thing chapter F offers, and
nothing else:

* `cc : CarryCocycle E K` (F.07) — the carry 2-cocycle with its integer shadow. It brings its
  twisted algebra `TwistedAlgebra cc` (F.08) and that algebra's proved laws for free, because
  those are theorems ABOUT `cc`, not extra data: F.09 (the algebra structure), F.10(a)
  (`finrank = E`), F.10(b) (`(single 1 1)^E` is the orbit-product scalar), F.13
  (`Nat.card = card K ^ E`).
* `J : LedgerJunction K ι α` (F.14) — the `(Σ-LEDGER)` junction: the coordinate map
  `J.sigmaMap`, the slot-constant family `J.u`, the print/read pair, and the ledger identity
  `J.hledger` as a field of the structure.
* `hSigma : SigmaLedgerLaw J` (F.17) — the three Σ-properties (injective, fixes `1`,
  multiplicative) that SL-1 supplies and that F.15/F.16's corollaries consume.

**Nothing is hidden.** Every member is either proved inside chapter F or is a NAMED carried
field; there is no unnamed hypothesis in this record. The one carried field is `hSigma`: SL-1's
corpus-scope junction instance is chapter C's tower data (`EFF.SIGMALAW.03/.04
[supplied-by: chapter C]`) and is **BLOCKED: GC-13**, so a consumer supplies it rather than
finding it proved here. The rest instantiates from proved nodes. Consumers that need the two
criterion lemmas — F.23's WM-FENCE (fixed `(z, A)` data) and F.25's gauge-torsor lemma — apply
those theorems directly to their own data; they are not fields, because the criteria quantify
over inputs a supply record has no business fixing (F.23's F-4 scoping: the criterion supplies
no freedom or existence content).

*[repaired: A-W.1/F-D1]* the signed field name `hΣ` is not a legal Lean identifier (`Σ` is the
Sigma-type token, excluded from `isLetterLike` at Lean 4.31), so the field is `hSigma`. This is
a FIELD name, hence contract content: consumers write `W.hSigma`, exactly as they write
`W.J.sigmaMap` for F.14's respelled `Σmap`.

**DEPENDS.** F.07 (`CarryCocycle`), F.14 (`LedgerJunction`), F.17 (`SigmaLedgerLaw`).

**PROOF.** definitional (assembly node — the record packages §§5–7's named supply; no corpus
unit of its own).

**FAITHFULNESS.** `hSigma` *[repaired: A-W.1/F-D1 — was `hΣ`]* is the one carried field (F.17's
C-side discharge pending GC-13); the rest instantiates from proved nodes.

**TEETH.** None of its own — packaging; each member's teeth are its own (F.07's cocycle
battery, F.13/F.10's instances at F.29, F.17's SIGMALAW battery).

**ENVIRONMENT.** ENV-F1.

## Status

Sorry-free, axiom-free (a structure declaration). Signature byte-identical to the stage-0e
gate (`leanspec/Leanspec/ChapF.lean`, LeanspecF) modulo the blueprint-signed
`namespace Uniformity.Density.Weld`.
-/

namespace Uniformity.Density.Weld

/-- The weld layer's proved supply, as one record (chapter-I/D consumption surface). -/
structure WeldSupply (E : ℕ) [NeZero E] (K : Type*) [Field K] (ι α : Type*) where
  cc : CarryCocycle E K
  J : LedgerJunction K ι α
  hSigma : SigmaLedgerLaw J

end Uniformity.Density.Weld
