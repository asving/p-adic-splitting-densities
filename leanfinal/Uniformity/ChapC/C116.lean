/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C108

/-!
# Uniformity.ChapC.C116 — the §11 disposition and the Phase-B consumer spec

**Chapter C, NODE C.116** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C1**.  `[signed: A-C.1]`, `[UPDATED: A-C.2]`.  Documentation node: the
`#check` manifest below is transcribed from the `C116Manifest` section of
`leanspec/Leanspec/ChapC.lean`, including the A-C.2 update (it GAINS `HTNode.WF` —
well-formedness is now MANDATORY on every count law — and LOSES `ht_branch` / `ht_global`,
whose axioms are WITHDRAWN at C.114's block).  It carries no new `Prop`.

## (i) The thin-verification disposition — what the machine certificate is, and is not

The corpus's machine certificate for the HT count law is **CORROBORATION, not the warrant**
(`EFF.W12.87`, verbatim: *"the proof above supplies the all-degree warrant"*).  Its scope is
the disclosed grid

    n ∈ {3, 4},   q ∈ {2, 3},   N ≤ 6,   and NO hostile-arc pass (`EFF.W12.87` OPEN-CALL 6).

The Lean proofs of C.109–C.114 are meant to be the first warrant-grade check beyond that grid,
and §13's gates re-fire the certificate's spot values at BOTH primes (GC-11's extra force).

**Honest status of that sentence at this landing (2026-08-16).**  The §11 chain is only
partly in the tree, so the "first warrant-grade check" is only partly delivered:

* C.107, the residual censuses — LANDED (`C107.lean`).
* C.108, the tree carrier and the node quantities — LANDED (`C108.lean`).
* C.109, step 1, the exact node cell count — **not landed**.  Re-signed at A-C.2; the frozen
  form (no `v.WF`) is machine-refuted, `C109_REFUTATION.lean.txt`.
* C.109a, the level-`N` development ↔ coefficient-box bridge — LANDED (`C109a.lean`).
* C.110, step 2, transfer at one repeated linear root — LANDED (`C110.lean`).
* C.111, step 3, the fiber exponent — LANDED (`C111.lean`), in the re-signed arithmetic-shadow
  form carrying the per-node hypothesis `hnode`.
* C.112, step 4, `(HT-rec)` division-free — LANDED (`C112.lean`).
* C.113, step 5, termination and Ore certification — **not landed**.
* C.114, the count law `ht_branch` / `ht_global` — **BLOCKED**.  Both axioms are machine-refuted
  as frozen (`C111_C114_REFUTATION.lean.txt`); the node awaits the realizes-refinement re-sign.
* C.115, depth zero and the obstruction row — LANDED (`C115.lean`).

So the corroboration disclosure above is still the operative scope statement for the count law
as a whole: nothing in this chapter yet certifies `(HT-branch)`/`(HT-global)` off the grid.

## (ii) The Phase-B consumer contract, verbatim

> a history-resolved order-1 menu entry **"must implement (HT-rec), retaining complete
> child-history multisets, side tags, `D_v`, `κ_v`, and `κ₀`"**

The `#check` manifest below IS that contract, transcribed onto C.108's fields, so that no
downstream menu can quietly drop a tag: `HTNode.kappa` and `HTNode.sideType` are MANDATORY
(the A-C.2 refutation showed exactly what goes wrong when a count reads neither — one-node
κ-separated trees give equinumerous strata with formula values `1` vs `2`), `HTNode.D` carries
the clipped history (the C.53 `max(·,0)` discipline), `HTNode.B` the digit budget, and
`HTNode.WF` is mandatory on every count law.  `κ₀` lives on `HTShape` and is read by
`htGlobalCount`, which is why both count carriers are in the manifest.

## (iii) The boxes that DO NOT MOVE

`[W12-H]` (the order-≥ 2 fence: a repeated factor of residual degree `> 1`, or one on an
`e > 1` side, opens a composite stage and is NEVER certified here), W12-BOX-1's inputs
`(H-a)–(H-e)`, W-12.B, and the tail problems — all unchanged, and all chapter I's rows.  §11
neither discharges nor enlarges any of them.  Two further conditionality facts belong with
them: `B-BOX-1` is inherited at terminal side factors of residual degree `d ≥ 2` exactly
through B.55/B.58 (C.113 — the HT chain's conditionality is exactly B's, no more), and the
corpus's `GENIND-1`/fracture-permanence consumption (`HYP.121`) is **NOT inherited**, because
the Lean recast works on factors where the sibling-independence is factorization uniqueness
(landed `monic_factorization_unique`) — a genuine simplification, flagged for the §16
cross-read.

## (iv) Provenance (`EFF.W12.88`) — the audit trail

The law was **N1-conjectured → machine-certified → P1-composed → orchestrator-verified**.
Carried here as the docstring audit trail per the SIGNATURE, together with the two A-C.2
machine refutations that the audit added on top of it
(`leanfinal/Uniformity/ChapC/C109_REFUTATION.lean.txt`,
`leanfinal/Uniformity/ChapC/C111_C114_REFUTATION.lean.txt`) and the A-C.2 certification
`verification/c109_ac2_cell_check.py` (127 checks).

**DEPENDS.** C.108 (every manifest name).  The blueprint also lists C.114; its two names were
REMOVED from the manifest at A-C.2, so this node does not wait on it.

**SOURCE.** `EFF.W12.87` / `.88` (verbatim); PA-5 (the assignment and its trap clause).

**TEETH.** the four DROP-teeth at their exact kill counts (DROP-HISTORY-CENSUS 302,
DROP-SIDETAG 22, DROP-KAPPA0 370, DROP-L 1,136) → retained as regressions; the manifest is
what keeps their targets (`sideType`, `kappa`, `L` via `B`, `κ₀` via `htGlobalCount`) named and
machine-checked at one place.

**ENVIRONMENT.** ENV-C1.

## Status

Documentation node: no new `Prop`, no proof obligation.  Sorry-free, axiom-free (Lean core
only — the manifest elaborates C.108's declarations, whose footprints are printed in
`C108.lean`'s own `AxCheck` section).
-/

namespace Uniformity.Density.Tower

/-! ## The manifest

Transcribed from `leanspec/Leanspec/ChapC.lean`, section `C116Manifest`, with the A-C.2
update applied. -/

section C116Manifest

#check @HTNode.B          -- the digit-budget quantity
#check @HTNode.D          -- the clipped history quantity (the C.53 discipline)
#check @HTNode.kappa      -- the side-tagged orbit factor: A MANDATORY TAG (Phase-B contract)
#check @HTNode.sideType   -- side tags: MANDATORY (roots on different sides never permute)
#check @HTNode.WF         -- [A-C.2] node well-formedness: MANDATORY on every count law
#check @htBranchCount
#check @htGlobalCount
-- [A-C.2] `#check @ht_branch` / `#check @ht_global` removed: the two axioms are WITHDRAWN
-- (machine-refuted as frozen); see NODE C.114's note and C111_C114_REFUTATION.lean.txt.

end C116Manifest

end Uniformity.Density.Tower
