# verdict_USUP — UNIT USUP: the two universal suppliers at general witnesses

**Status: COMPLETE.**  `leanfinal/Uniformity/ChapI/I10Suppliers.lean` — 0 errors, 0
`sorry`, all 17 printed footprints Lean core `{propext, Classical.choice, Quot.sound}`.
Verified per-file: `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10Suppliers.lean`
(clean, footprints printed).  Registered in the chapter aggregator `Uniformity/ChapI.lean`
(one import line — the standing landing plumbing; only landed-file edit).  Cite ledger:
**empty**.  Repo footprint: the new module + the aggregator line + this verdict, nothing
else.

## Charge 1 — SCOPE: what a general arising realization's own data derives (settled,

machine-checked where "derivable")

Question: can the C3 tau-letter source and the G3 site package be CONSTRUCTED from an
arbitrary arising realization's fields (`receiver`/`keys`/`normalizer`/`node` + the
`RealizedInput` view equalities), the way the keystone instances were built?

* **Vartheta leg** (`CanonicalTauLetterSource`, four fields) — **2 of 4 fields ARE
  derivable**, and now derived:
  - `view` — DERIVABLE: `X.gaugeFamilyViewEq` (C130vw's producing equality, carried by
    EVERY `RealizedInput`) is definitionally the demanded view at the canonical socket
    (`eG = MulEquiv.refl`).  Consumed inside the §2 reduction.
  - `tau_mem` — DERIVABLE: landed as ★ `canonical_tau_mem_family` — tau membership at
    the witness's own exported height family, every gauge-live level, every realization
    (`canonical_tau_mem` + the `gaugeHeightFamily` live-index `dif_pos` collapse; the
    keystone's `s2Four_tau_mem` was generic in shape, witness-specific only in binders).
  - `tau_word` — NOT derivable: keystone-proved only by the card-2 collapse
    (`s2CanonicalReadFour3_eq_one`, read constantly `1`, `m = 0, t = 0`); generally the
    triangular-spanning research row **C3** (DWR §11.5: research, 5–12 days).
  - `generator_descent` — NOT derivable: nothing ties a general realization's
    `wrapValue`/`letterValue : Lˣ` to the image of `Ktˣ`; row **R5** (OPEN-LETTERS).
* **`GentowW` leg** (G3 site package + three dictionaries) — **NOT derivable,
  STRUCTURALLY**: the post-PK/U15 `ChainRealization` carries
  `receiver`/`keys`/`normalizer`/`node` ONLY (the FGMN legs and `(e',f',u')` were
  factored into the standalone `fgmnCalculusOf`), so no general realization field
  supplies the site calculus, the `GENTOW5WCleared` law (rows **C0/C1**), the GC-13
  wiring, or the theta/peel/range dictionaries (row **C2** = GCW-4/GCW-5 at general
  residue cardinality).  At the keystone ALL of these came from the landed μ₄ operator
  bank (D3 stack) + card-2 collapses.  No strictly smaller per-realization datum exists
  to reduce to.

## Charge 2/3 — what landed (namespace `Uniformity.Density.DeepExport`)

* **§1 the generic legs**: `canonical_tau_mem_family` (above) — C3's `tau_mem` field is
  FREE at every arising realization.
* **§2 the vartheta reduction** (the unit's new theorem content):
  - `CanonicalTauWordAt X j hj` — row C3's exact remaining content as a per-realization
    `Prop` (the canonical read of every tau class is a word in the realization's own
    canonical generator values).  NEW STATEMENT (review).
  - ★ `canonicalTauLetterSource_of_word_descent` — the FULL C3 record at the canonical
    socket from `tau_word` + `CanonicalGeneratorDescent` ALONE (`view`/`tau_mem`
    supplied generically).  The landed compiler demanded all four fields; the vartheta
    supplier's open boundary is now exactly rows C3 + R5.
  - `TauWordDescentSupply X` (NEW STATEMENT) + `varthetaPerWitnessExporter_of_tauWordDescent`
    + shallow vacuity tooth.
* **§3 the `GentowW` boundary named**: `WiredSiteSupply X` (NEW STATEMENT — verbatim the
  landed compiler's hypothesis shape, per the structural finding) +
  `gentowPerWitnessExporter_of_wiredSiteSupply` + shallow tooth.
* **§4 the universal forms + the capstone reduction**:
  `UniversalTauWordDescentSupply n` / `UniversalWiredSiteSupply n` (NEW STATEMENTS),
  their supplier compilations (`universalVarthetaSupplier_of_tauSupply`,
  `universalGentowSupplier_of_siteSupply`), and
  ★ `deepTwistField_of_supplies : UniversalTauWordDescentSupply n →
     UniversalWiredSiteSupply n → IFC0.DeepTwistField n`
  — the capstone `deepTwist` field from the two named supply `Prop`s, fully
  universe-polymorphic, through G10U's assembly direction
  (`deepTwistField_of_universalPerWitness`).  **SUFFICIENT ONLY — no converse claimed**;
  the exact boundary remains `deepTwistField_iff_universalPerWitness`.
* **§5 keystone nonvacuity**: the supply `Prop`s are inhabited at EVERY depth-4 keystone
  witness, full parametric payload — `s2Four_canonicalTauWordAt`,
  `s2Four_tauWordDescentSupply`, `s2Four_wiredSiteSupply` — plus the coherence pin (an
  `example`: the supply route re-derives both per-witness exporters at the wired genre).
  Conditionality inherited exactly from the keystone (`w₁ w₂ w₃ w₄` + `IsAdicComplete` +
  the parametric R8r payload); nothing new assumed.

## Honesty — the field does NOT close; the remaining leg, named exactly

Per the landed iff, the gap IS the field.  Open, per arising realization and deep-live
level, at the now-minimal boundary:

| missing datum (Lean `Prop`) | blueprint row | discharging math | character |
|---|---|---|---|
| `CanonicalTauWordAt` | C3 | triangular spanning of the level kernel's tau classes by canonical generator words | genuinely new (research 5–12 d); the keystone's card-2 collapse does not generalize |
| `CanonicalGeneratorDescent` (landed shape, reused) | R5 | OPEN-LETTERS / same-receiver descent of canonical generator values to `Ktˣ` | parametric in FORM (per-level descent datum), research in content |
| `WiredSiteSupply` | C0/C1/C2 | per-level FGMN operator banks at general towers (L2E-genre engine) + GCW-4/GCW-5 at general residue cardinality | genuinely new; structurally not carried by `ChainRealization` |

None is keystone-threshold-like in the sense of a datum one could carry as a genre
hypothesis field and discharge later by a numeral: each demands general-depth
mathematics per the DWR §11.5 grading.

## Notes for the orchestrator

* One landed-file edit: the ChapI aggregator import line (standing convention).
* `?? leanfinal/Uniformity/ChapI/IFCG18.lean` in git status is NOT this unit's file
  (present before this unit started; not in the aggregator) — another unit's in-flight
  work, untouched.
* Flagged NEW statements for the standing review: `CanonicalTauWordAt`,
  `TauWordDescentSupply`, `WiredSiteSupply`, `UniversalTauWordDescentSupply`,
  `UniversalWiredSiteSupply` (supplier-side interface `Prop`s below the signed surface;
  no leanspec name touched).
* Universe finding: `canonicalResFamily`'s universe order is `{uE, uKt, uL, uG}`
  (pinned explicitly in `CanonicalTauWordAt`); this unit's own supplier `Prop`s all land
  at `{uG, uKt, uL}` matching G10U's convention; the keystone site instance is pinned to
  `.{0, 0, uL}` (inherits C136c0's `GaugeLattice.{0}` pin), the tau instances stay
  `uG`-polymorphic.
