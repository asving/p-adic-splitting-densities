# Verdict TAU — source-faithful canonical tau export

**Date:** 2026-08-28  
**Unit:** TAU / LVS-CANONICAL-TAU-EXPORT  
**Overall verdict:** **MECHANISM PROVED; GENERAL-DEPTH SOURCE SUPPLIER OPEN.**

The chosen route is a no-ripple, owner-attached strengthening of route (b): a companion
`CanonicalTauLiveSource` supplied with the explicit `core/Aℛ/X`, rather than a new field on
every landed `ChainRealization`.  It combines the general tau-to-canonical-generator-word
theorem with the minimal new source dictionary `CanonicalGeneratorDescent`.  The conversion
to LVS's exact export and onward to `VarthetaRes` is proved, with the original owner, family
view, index, and liveness quantifiers unchanged.

Statement/proof authority: `leanfinal/scratch/TAU_probe.lean` (new scratch, zero `sorry`).
Mathematical record: appended `[TAU 2026-08-28]` section in
`docs/in-progress/LADDER_SUPPLY_2026-08-27.md`.

## Route decision

| Candidate | Verdict | Exact reason |
|---|---|---|
| (a) `FGMNCalculus` at level `j` | **BLOCKED-BECAUSE / REJECTED ALONE** | The class carries `letterZ : ℕ → W.fld r`, `letterZ_ne_zero`, and polynomial residual operators, but no equality to `SplitNodePointSource.canonicalRead` (`C130pk.lean:110-175`). Packaging is factored from FGMN source records plus a key chain and does not consume the realization node (`:222-268`). Hence a calculus can remain fixed under C130s18's canonical-read twist. |
| (b) strengthen realization source | **CHOSEN, AS A COMPANION PACKAGE** | `CanonicalTauLiveSource` is attached to the exact `core/Aℛ/X` and exact `GaugeFamilyViewEq`, only for `3 ≤ j` and `GaugeLive core.r j` (`TAU_probe.lean:159-175`). A companion avoids changing every existing `ChainRealization` constructor and preserves depth-two vacuity, while requiring future deep witnesses to supply the missing source dictionary. |
| (c) IFC4 `SplitNodeWired` | **BLOCKED-BECAUSE / REJECTED** | IFC4 changes only the separate Kt-valued `towerRead` field (`IFC4.lean:105-143`); `GC13Wiring` constrains that read at normalizer points (`IFC3.lean:108-126`). LVS consumes the L-valued `canonicalResAt`/`canonicalRead`. The wired witness has `r=2`, and IFC4 proves its signed deep range empty (`IFC4.lean:384-398`). |

## Claim ledger

| Claim | Status | Machine/source anchor |
|---|---|---|
| Exact source mechanism stated in landed vocabulary | **PROVED** | `CanonicalTauLetterSource` (`TAU_probe.lean:102-123`) fixes `X`, the exact external family view, the same live `j`, a tau word in the realization's own C130cr canonical values, and the generator-descent dictionary. |
| Minimal new per-level field isolated | **PROVED (statement)** | `CanonicalGeneratorDescent` (`TAU_probe.lean:79-94`): the exact `Aℛ.node.wrapValue` and every exact `Aℛ.node.letterValue Aℛ.normalizer` are images of `Ktˣ` under the specified `Kt → L`. It contains no tau, vartheta, or socket conclusion. |
| Tau kernel membership is existing mathematics | **PROVED** | `canonical_tau_mem` (`TAU_probe.lean:33-54`) expands `NormSection.tau` and uses `LaurentNormalizer.exact_height`. No new residue hypothesis is used. |
| C130cr gives the generators and their canonical read product | **PROVED** | `wrapClass`, `letterClass`, `generatorWord`, `wrapValue`, `letterValue`, and `canonicalRead_generatorWord` (`C130cr.lean:223-330`); synchronized form `canonicalRes0_generatorWordSync` (`:537-544`). |
| General tau word in those generators | **OPEN** | `CanonicalTauLetterSource.tau_word` is the exact obligation (`TAU_probe.lean:119-122`). C130cr explicitly declines a spanning claim and names the triangular-basis bridge open (`C130cr.lean:223-227`). D62w proves only fixed depth: depth 3 at `D62w.lean:228-265`, depth 2 at `:319-360`. Named open: `LVS-TAU-WORD`. |
| Canonical generator values descend to `Kt` | **OPEN** | No landed field ties `canonicalRead(letterClass)` to FGMN `letterZ`, the receiver images, or `ambientLetter`. C130s17's S2 `letter_compat` stops at `ambientLetter` (`C130s17.lean:246-251`). Named open: `LVS-CANONICAL-GENERATOR-DESCENT`. |
| Source mechanism discharges LVS's exact per-level tau export | **PROVED** | `varthetaTauLevelExport_of_canonicalTauLetterSource` (`TAU_probe.lean:128-157`). The embedded unit is explicitly `u₀^m * ∏ a, u(a)^(t a)`; proof uses multiplicativity, integer powers, and finite products. |
| Universal owner source discharges the universal LVS exporter | **PROVED** | `CanonicalTauLiveSource`, local exact mirror `VarthetaTauLiveExporter`, and `varthetaTauLiveExporter_of_canonicalTauLiveSource` (`TAU_probe.lean:159-202`). No realization, view, or index is exchanged. |
| Export discharges `VarthetaRes` | **PROVED** | `varthetaRes_of_canonicalTauLetterSource` (`TAU_probe.lean:206-221`) calls landed `Gauge.hvarthetaRes_of_tau_letters` and the one-field `VarthetaRes` constructor. |
| Bare realization/calculus can supply descent uniformly | **BLOCKED-BECAUSE** | `twistNode`/`twistRealization` preserve the present carrier while changing only `canonicalRead` (`C130s18.lean:407-465`); `canonicalResAt_twist` gives the exact change (`:467-474`); `embeddedValue_not_uniform` refutes uniform embedded descent (`:527-543`). |
| First landed deep witness validates supplier | **BLOCKED-BECAUSE / NO INSTANCE** | All landed explicit witnesses have depth two on this route. The first nonempty signed site is `r=4,j=3`; no arising witness of depth at least four is landed. This is absence of a supplier instance, not a proof failure in the conversion mechanism. |

## Supplier obligation ledger

For each future arising witness and each exact site `3 ≤ j` with
`GaugeLive core.r j`, its construction must provide the following, attached to the same
`Aℛ.node`, `Aℛ.normalizer`, `X`, embedding, and family view.

| Supplier obligation | New data? | Status / discharge route |
|---|---:|---|
| Exact-height tau kernel membership | No | **PROVED** by `canonical_tau_mem`; transport along the exact view is dependent bookkeeping. |
| Exponent-lattice spanning of each tau by `wrapClass` and `letterClass` | No new chosen datum; new theorem | **OPEN** general-depth triangular descent (`LVS-TAU-WORD`). |
| Read of the resulting generator word | No | **PROVED** by C130cr's canonical-read homomorphism theorems. |
| `wrapValue` is an embedded `Kt`-unit | Yes: source dictionary proof | **OPEN**, field `CanonicalGeneratorDescent.wrap`. |
| Every `letterValue` at `a : Fin (j-1)` is an embedded `Kt`-unit | Yes: source dictionary proof | **OPEN**, field `CanonicalGeneratorDescent.letter`. |
| Assemble an embedded tau value | No | **PROVED** in TAU probe. |
| Apply D62w and E.61 | No | **PROVED** in TAU/LVS probes. |

The minimal new field must be supplied at witness construction, where `canonicalRead` is
chosen.  It must not be offered as an axiom for arbitrary existing `ChainRealization`s; the
twist audit proves that statement false.  A production design can use a wrapper such as
`TauFaithfulRealization Aℛ` whose only signed field is
`∀ j, 3 ≤ j → (hj : GaugeLive core.r j) → CanonicalGeneratorDescent Aℛ j hj`; the tau-word
part should be proved from the tower normalizer rather than stored as free data.  This gives
zero obligations at `r=2` and avoids ripple through landed record constructors.

## FGMN faithfulness check

The mathematical demand is source-faithful, not an invented consumer assumption.  The
repository's FGMN print-read records the §3.3 `γ_i → y_i → z_i` recursion and says the
missing carrier consists of fraction-field rational functions, homogeneous initial forms,
and embeddings of the intermediate `F_i` into the terminal field; `letterZ` contains only
the final scalar after that transport (`FGMNCALCULUS_FIELDLIST_2026-08-24.md:372-386`).
The Def-3.12 exponent-lattice spanning content is recorded explicitly in
`GENTOW2_ADJUDICATION_2026-08-24.md:104-108`.  These are precisely the two TAU obligations:
tau-word spanning and identification of the canonical generator read with the terminal-field
image.

What the literature apparatus provides mathematically is therefore adequate when an arising
witness builds `canonicalRead` from that apparatus.  What the landed Lean surface provides is
not: `FGMNCalculus` erased the evaluation/embedding dictionary, `ChainRealization` factored
out the FGMN legs, and `SplitNodePointSource.canonicalRead` remains freely twistable.  The new
field restores only this erased source tie.  It does not assume the final tau/vartheta result.

The landed depth-two μ3 route does not change the conclusion.  `C132fd0.s2SourceDataTwo`
packages `letter := s2Letter`, and `C132kp6b.s2Mu3_calculus_nonempty` closes the scalar
calculus, but neither theorem connects that scalar to `canonicalRead(letterClass)`.  At depth
two the TAU signed range is empty, so no false positive is hidden.

## Verification

Required command, run from `leanfinal/`:

```text
timeout 580 ~/.elan/bin/lake env lean scratch/TAU_probe.lean
```

Result: exit `0`; zero warnings, zero `sorry`.  Every footer declaration reports only
`[propext, Classical.choice, Quot.sound]`.

Repository-scope audit: no landed `.lean`, leanspec file, or existing scratch file was
edited; `scratch/TAU_probe.lean` is new.  No git commit was made.
