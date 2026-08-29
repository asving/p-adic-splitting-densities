# verdict_G10U — UNIT G10U: the deepTwist universal-supplier boundary (G10 family)

**Status: COMPLETE.**  `leanfinal/Uniformity/ChapI/I10Universal.lean` — 0 errors, 0
`sorry`, all 26 printed footprints Lean core `{propext, Classical.choice, Quot.sound}`
(several statement-only carriers print without `Classical.choice`).  Verified per-file:
`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10Universal.lean` (clean).
Registered in the chapter aggregator `Uniformity/ChapI.lean` (one import line — the
standing landing plumbing, same convention as I10DeepExport/C136c0/C136c5; no other
landed file touched).  Cite ledger: empty.

## Charge 1 — the G10 family (occurrence→universal), LANDED

Namespace `Uniformity.Density.DeepExport` throughout.

* **The per-witness exporter shapes** (DWR §11.4 quantifier discipline, deep-live range,
  witness's OWN exports; NEW STATEMENTS, review):
  - `VarthetaPerWitnessExporter X` — ∀ deep-live `j`, `Ladder.VarthetaRes` at
    `(N₀, gaugeHeightFamily X, canonicalResFamily X, useHeightFamily X)`;
  - `GentowPerWitnessExporter X` — ∀ deep-live `j`, `Gauge.GentowW` at
    `(arenaFamily X, useHeightFamily X, towerReadFamily X, peelUnitFamily)`.
* **Generic compilers (universally quantified theorems, every witness)**:
  - `varthetaPerWitnessExporter_of_tauSources` — per-level `CanonicalTauLetterSource`
    (C3's shape) → the vartheta exporter (engine: C0123's
    `varthetaRes_of_canonicalTauLetterSource`);
  - `gentowPerWitnessExporter_of_sites` — per-level G3 site package + the three WLE
    consumer dictionaries → the `GentowW` exporter (engine: G345's
    `wiredDemand_of_level_export`, `gentowW` leg);
  - `gentowPerWitnessExporter_of_deepExports` — the LANDED G4
    `DeepLevelPerWitnessExporter` + all-site dictionaries → the `GentowW` exporter (the
    G4 record's `site` projection feeds the signed demand).
  - Shallow-witness vacuity teeth for both shapes (`r ≤ 3` ⇒ vacuous — the honesty twin
    of `deepLevelPerWitnessExporter_of_shallow`).
* **The wired-genre instances (every SplitNodeWired/keystone witness — full parametric
  payload `(F₀,hF₀,μ,hμ,hdeg,hblock,hcop)` + four thresholds + `L`)**:
  - `s2Four_varthetaPerWitnessExporter`, `s2Four_gentowPerWitnessExporter` — both
    exporters inhabited at EVERY depth-4 keystone witness (`DeepLive 4 j` forces
    `j = 3`, where C0123's `s2Four_varthetaRes` / `s2Four_wiredGentowDemand` fire);
  - ★ `s2Four_deepTwistConjunctLive` — the full own-export `DeepTwistConjunctLive 4` at
    EVERY keystone witness: **generalizes C56R's one-payload tooth
    (`s2C6_deepTwistTooth`, `F₀ = leaf·(g16+1)`) to the whole parametric genre.**
  - Conditionality inherited exactly from the keystone: `w₁ w₂ w₃ w₄` +
    `IsAdicComplete` + the parametric R8r payload.  Nothing new assumed.
* **The "every same-witness exported recenter step" quantifier** (the §12.5-DELETED MP1
  half): recorded as `mp1PerWitnessEmission`, a one-line projection of the generic A-I.8
  compiler `midPeelEmission_of_recenterStepDirect` at the witness's own exported
  carrier/block — held by supersession, no new statement shape introduced.

## Charge 2 — what the capstone `deepTwist` field demands beyond G10: EXACTLY the two
universal suppliers (machine-checked), and it does NOT close today

* **The transport engine** (`hvarthetaRes_of_view`, `gentowW_of_view`,
  `varthetaRes_of_perWitness_view`, `gentowW_of_perWitness_view`,
  `deepTwistConjunctLive_of_perWitness_views`): the own-export exporters transport to
  the EXTERNAL socket data `(v, ρ, q, A, R, w)` of any `CanonicalDeepTwistConfig` bound
  to the same witness through the I.10b `GaugeFamilyViewEq`/`ArenaFamilyViewEq` views
  along an arbitrary `eG` — exact bookkeeping (`varthetaEl`/`thetaEl` are normalizer
  words; the views pin the `KernelRead` pairs, the read, the use-height, and the peel
  unit at live indices).
* **The named boundary** (NEW STATEMENTS, review): `UniversalVarthetaSupplier n` /
  `UniversalGentowSupplier n` — the per-witness exporters quantified over EVERY arising
  realization of degree `n` (all `O/Kt/E/L`, every `ChainRealization`, every
  `RealizedInput`).
* ★ **The exactness** (the G10 exit gate):
  `deepTwistField_iff_universalPerWitness : IFC0.DeepTwistField n ↔
   UniversalVarthetaSupplier n ∧ UniversalGentowSupplier n`
  — at the ARISING universe profile `uKt = 0` (the signed socket's `K` binder is `Type`;
  A-I.3's "0 is the universe of every arising instance" disclosure).  The assembly
  direction `deepTwistField_of_universalPerWitness` is fully universe-polymorphic;
  also landed as the IFC0-facing halves `deepVarthetaSupplier_of_universal` /
  `deepGentowSupplier_of_universal` (feeding IFC0's DT0 split directly).  Converse via
  C130s18's CC-18 socket application `realizedInput_deepTwistConfigData` + IFC0's
  per-live projections.
* **Honest answer: the deepTwist supplier can NOT be assembled today.**  The field's
  guard quantifies over every realization, not only wired ones; the occurrence teeth +
  §7 close the per-witness exporters ONLY at the S2 depth-4 keystone genre.  The
  remaining leg, named exactly (now as a Lean Prop pair): the two universal suppliers at
  general (non-wired) witnesses — i.e. the site-package/dictionary supply (rows C1/C2 at
  general residue cardinality) and the tau-word/letters supply (rows C3/R5) for every
  arising realization.  Per the iff this leg is not an approximation: it IS the field.

## Charge 3 — `package`/`lb1`: untouched, per the charge.

## Notes for the orchestrator

* One landed-file edit: the ChapI aggregator import line (pure import list; the standing
  convention for every landed module — flagged here since the unit brief fenced landed
  files; revert is one line if the interpretation is unwanted).
* Universe finding worth recording: theorems consuming C136c0's
  `s2Four_wiredGentowDemand` are silently pinned to `GaugeLattice.{0}` (that landed
  statement fixes `uG := 0`); the §7 gentow/conjunct instances are therefore stated at
  explicit `.{0,0,0,uL}` arena universes, matching C56R's tooth.
* Flagged NEW statements for the standing review: `VarthetaPerWitnessExporter`,
  `GentowPerWitnessExporter`, `UniversalVarthetaSupplier`, `UniversalGentowSupplier`
  (supplier-side interfaces below the signed surface; no leanspec name touched, no
  A-I.9 amendment forced).
