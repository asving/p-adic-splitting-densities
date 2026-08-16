/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F14 — `LedgerJunction`: the abstract ledger junction

**Chapter F, NODE F.14** [def] (`blueprint/CHAP-F_weld_layer.md` §6), ENV-F1 + `[Field K]`.
THEOREM SL-1's `(Σ-LEDGER)` display as a structure, at the abstraction level where its
corollaries are provable (`EFF.SIGMALAW.05`: "Prnt_j(A) = u_j · Σ_m(R_m v(A)), u_j =
z_m^{−k_j·A_m}·ε_m(β_j)·U_m(β_j) — slot-constant"):

* `sigmaMap : K → K` — the coordinate map `Σ_m` on the level-`m` residue algebra;
* `u : ι → Kˣ` — the slot-constant family (slot-constancy is the point of SL-1);
* `Prnt, read : ι → α → K` — the per-slot print and read maps;
* `hledger` — the ledger identity itself.

Properties of `Σ` (multiplicativity = the `(EC-q)` automorphism law; injectivity + `Σ 1 = 1`
for the SL-C2 economy) enter as hypotheses of the consuming lemmas (F.15/F.16) or as the
F.17 carrier, **never as fields** — matching the source's own care that SL-C2 needs strictly
less than SL-C1. The corpus-scope quantifier ("every on-line level-`m` object at every
shared-below junction, every `m ≥ 1`") is F.17's, not this structure's.

*[repaired: A-W.1/F-D1]* the signed field name `Σmap` is not a legal Lean identifier
(`Σ` is the Sigma-type token, excluded from `isLetterLike` at Lean 4.31), so the field is
`sigmaMap`; that respelling is part of the type and is what every consumer projects
(`J.sigmaMap`). The `Σ` of the source's `(Σ-LEDGER)` display stays `Σ` in prose.

Signature byte-identical to the stage-0e gate (`leanspec/Leanspec/ChapF.lean`, LeanspecF).
-/

namespace Uniformity.Density.Weld

/-- An abstract ledger junction (`EFF.SIGMALAW.05`'s `(Σ-LEDGER)` as a structure):
prints = slot constant × Σ of reads. -/
structure LedgerJunction (K : Type*) [Field K] (ι α : Type*) where
  sigmaMap : K → K
  u : ι → Kˣ
  Prnt : ι → α → K
  read : ι → α → K
  hledger : ∀ j a, Prnt j a = (u j : K) * sigmaMap (read j a)

end Uniformity.Density.Weld
