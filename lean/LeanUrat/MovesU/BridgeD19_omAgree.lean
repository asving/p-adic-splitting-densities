/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.OM.Classifier
import LeanUrat.OM.ChainMenu

/-!
# IB-D19 — OPTIONAL OM-AGREEMENT ENRICHMENT (bridge campaign BP1, cluster c9;
gated, Q1 Architecture B; NOT on the default path)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.1 (OM
dictionary) / §3.4 Architecture B / §4 group D (IB-D19, re-scoped post-Codex
finding 9: "the agreement statement is PARAMETRIC in a SUPPLIED decoder …
decoder + covering proof are BINDERS, never an assumed global interface").

INFORMAL STATEMENT: under Architecture B the OM engine ties in as an AGREEMENT
enrichment: for a SUPPLIED decoder `dec : ClusterShape → Option
FactorizationType` covering `OM.classify`'s range at (n, p), wherever the bridge
classifier decides σ, the decoded OM verdict on the corresponding monic box
polynomial is `sigmaToFT σ` (= `⟨σ.1⟩`, §3.1's trivial dictionary — IB-A1's
def, INLINED here as the anonymous constructor since IB-A1 is another cluster's
unit).  The n = 2 sanity instance supplies `dec` from the built Wave-5 menu
decoder `OM.ChainMenu.typeOf5 2`, with `UniformModelN2.cluster_coveringP` the
discharge raw material for the covering claim.

DEPS: D7 (`bridgeCanonical`), A9 (`boxPolyEquiv`), A1 (`sigmaToFT`) — all other
clusters' units.  TRANSCRIPTION RESOLUTIONS (recorded):
* `canonical` and the box→monic map are BINDERS (`canonical` with the
  `ClassifierSpec.canonical` field type; `toMonic` = A9's equiv forward, guarded
  to 0 < N per (†2) — at N = 0 `monicBox` is EMPTY);
* the blueprint's `(bridgeCanonical N f).isSome →` trigger is transcribed as
  `canonical N f = some σ →` (the isSome witness named — same clause);
* HONEST-SORRY DISCIPLINE: the agreement is formulated as a NAMED Prop
  (`OmClassifyAgree`), NOT a sorried ∀-theorem — over a FREE `canonical` binder
  the sorried universal would be FALSE (adversarial canonical), violating the
  honesty invariant.  The enrichment CLAIM is owed at the instantiated
  arguments by the consumer (IB-F7 asserts `OmClassifyAgree n p bridgeCanonical
  (boxPolyEquiv forward) dec` at n = 2), exactly the "gated, ADJ,
  statement-only" scope;
* the n = 2 instance half is the sorried COVERING claim for the built decoder
  (`decCovers_typeOf5_n2` below) — the hcov-discharge slot the blueprint
  assigns to `UniformModelN2.cluster_coveringP`.

PROOF SKETCH (ADJ, statement-only + n = 2 instance): the covering claim at
n = 2 rides `cluster_coveringP` (OM/UniformModelN2.lean:439 — every cluster
pair realizes a menu stratum) + `typeOf5`'s menu-keying (`typeOf5_chainLit`);
the agreement claim itself is discharged at n = 2 through IB-F7 from
`UniformModelN2`'s decided-count/covering results.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- THE COVERING HYPOTHESIS (post-Codex finding 9's binder shape): `dec` decodes
    `OM.classify`'s range at (n, p) — on every positive-level monic box
    polynomial the decoded verdict exists. -/
def DecCoversClassify (n p : ℕ) [Fact p.Prime]
    (dec : ClusterShape → Option FactorizationType) : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ g : OM.QuotientBox.monicBox p N n,
    ∃ σft : FactorizationType, dec (OM.B.classify p n N g) = some σft

/-- THE AGREEMENT STATEMENT (†-D19, Architecture B's enrichment seam), a NAMED
    Prop (file header — honest-sorry discipline): wherever `canonical` decides
    σ at a positive level, the decoded OM verdict on the corresponding monic
    polynomial (`toMonic` = IB-A9's `boxPolyEquiv` forward at consumption) is
    `sigmaToFT σ = ⟨σ.1⟩` (IB-A1's dictionary, inlined).  Consumers: IB-F7
    asserts this at (`bridgeCanonical`, `boxPolyEquiv`, the n = 2 menu
    decoder). -/
def OmClassifyAgree (n p : ℕ) [Fact p.Prime]
    (canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n))
    (toMonic : ∀ (N : ℕ), 0 < N → Box p n N → OM.QuotientBox.monicBox p N n)
    (dec : ClusterShape → Option FactorizationType) : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (f : Box p n N) (σ : SplittingType n),
    canonical N f = some σ →
    dec (OM.B.classify p n N (toMonic N hN f)) = some ⟨σ.1⟩

/-- THE n = 2 INSTANCE, covering half: the built Wave-5 menu decoder
    `OM.ChainMenu.typeOf5 2` covers `OM.classify`'s range at (2, p) — the
    hcov-discharge slot; raw material `UniformModelN2.cluster_coveringP`
    (OM/UniformModelN2.lean:439) + `typeOf5`'s menu keying. -/
theorem decCovers_typeOf5_n2 (p : ℕ) [Fact p.Prime] :
    DecCoversClassify 2 p (OM.ChainMenu.typeOf5 2) := by
  sorry

end LeanUrat.MovesU
