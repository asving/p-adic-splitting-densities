# verdict_SCS — UNIT SCS: the site-calculus supply vs the frame-generic L2E engine (2026-08-30)

**Status: COMPLETE (hypothesis adjudicated per-field with TWO corrections; the exact
bank/wiring factorization landed as an IFF; `UniversalSiteCalculusSupply n` does NOT
close — the named remainder is strictly smaller on both halves).**

`leanfinal/Uniformity/ChapI/I10SiteCalc.lean` — 0 errors, 0 `sorry`, all **20** printed
footprints Lean core `{propext, Classical.choice, Quot.sound}`.  Verified per-file
(`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10SiteCalc.lean`, exit 0) AND
per-target (`lake build Uniformity.ChapI.I10SiteCalc` — Build completed successfully,
8970 jobs); the chapter aggregator `Uniformity/ChapI.lean` re-verified (exit 0) after the
one standing import-line edit.  Cite ledger: **empty**.  Repo footprint: the new module +
the aggregator line + this verdict, nothing else.

## Charge 1 — the per-field dissection (VERDICT on WSS's working hypothesis)

WSS's hypothesis: "`SiteCalculusSupply` is exactly what the frame-generic L2E engine
produces."  **Adjudication: TRUE IN FORM for the bank half (machine-pinned by
`LevelSiteBank.cleared` — the supply's clauses are verbatim the cleared engine's input),
but it needs TWO substantive corrections.**  Per field, with the exact S2 entry points
(provenance audit of `C136c0.s2SiteSourceData`/`s2SiteSourceLaws` + the L2E chain,
2026-08-30):

| field of `SiteCalculusSupply` | generic producer? | exact S2/card-2 entry at the keystone |
|---|---|---|
| triple `(e',f',u')`, `0 < f'` | no landed assignment; natural candidate = the tower's own rung data (`DeepTower.e/f/u` are data fields, C83) | the S2 depth-4 rung pin `(2,1,85)` |
| `I : FGMNCalculus (trunc j)` | **NO — C92_VACUITY stands** (C130pk: no theorem bare `DeepTower` → `Nonempty (FGMNCalculus …)`; structurally, `KeyChain` demands monic keys but NOT irreducibility, while `KP_keyAt`+`KP_irred` force the top key irreducible — arithmetic content a bare tower lacks) | the seven μ₄ operators of `s2SiteSourceData`; of the 13 source laws, FIVE (`s2Mu4_graded_mul`, `s2Mu4NormRes_mul`, `s2Mu4_hex`, `s2Mu4_key_criterion`, `s2Mu4KeyPoly_g8`) consume L2E and **every path funnels through the single S2-pinned lemma `C136l2e4.s2Mu4Coeff_mul`** (the (85,2) fixed-grade convolution via the μ₃ mirror `s2Mu3GradedRes`); its generic counterpart (`hconv`) is REFUTED at the bare normalized carrier (`fixedGrade_unweighted_add_forces_letter_one`); the D3-03 `LevelDatum` depth adapter is absent (L2E3 RED); `s2Mu4_normalized_recipe` is discharged by grade-PARITY VACUITY (85 odd vs even μ₄ grades — genuine content at general frames); `letter_ne_zero := one_ne_zero` reads the card-2 constant-1 letter |
| four B-1 supplies | generic IN FORM (per-calculus; verbatim the cleared engine's input) — no landed generic supplier | the numeral solve `s2Trunc_towerNorm_two_eighty_five` (`towerNorm 2 85 = (8,0,![0,1])`), the grade-170 tooth, `4 < 8`, `PrevGrade` vacuous at `f' = 1` |
| `GC13Wiring` leg | **NOT a tower-side product AT ALL** — couples the realization's OWN exports to the calculus (per-realization BY DESIGN: IFC3's D-D12 signing; module fence: no universal wired supplier statable; `s2_wiring_refuted_at_landed_exports` pins that the law is FALSE at the landed zero-read witness) | `s2Four_gc13Wiring` (both sides `1`; full witness payload) |

**Correction 1**: the LANDED generic L2E layer (`C136l2e0–l2e3`, verified 100%
`LevelDatum`-rooted, zero S2 mention — and NOT imported by the D3 stack except through
the S2 specialization file `l2e4`) supplies the level-2 multiplicative *vocabulary* but
does not yet produce a calculus at a general tower; the remaining program work (weighted
absolute-read convolution carrier, D3-03 depth adapter, key lifting, B-1 grade
computation) is mathematics, not transcription.
**Correction 2**: the wiring leg is not an L2E/tower-side product; it belongs with
`LadderReadSupply`'s per-realization export-coherence character.  The supply's fault
line is bank ⊗ wiring, and this unit makes that split EXACT.

## Charges 2/3 — what landed (namespace `Uniformity.Density.DeepExport`)

* **§1 `LevelSiteBank`** (NEW STATEMENT, review) — the tower-side bank DATUM (triple +
  calculus + four B-1 supplies at a bare `DeepTower`; no realization, no `q`).  Teeth:
  ★ `LevelSiteBank.cleared` (bank ⟹ `GENTOW5WCleared`, the genre pin),
  `baseRead_ne_zero`, `thetaRatioCleared_one` (WSS §1's general-`q` lemma at the bank),
  `levelSiteBank_of_inertia_trivial` (the `f' = 1` keystone-genre constructor),
  `TowerBankSupply` (the tower-side research Prop) + shallow-vacuity tooth + family
  direction.
* **§2 ★ THE FACTORIZATION IFF** (the unit's theorem content):
  `siteCalculusSupply_iff_wiredBank : SiteCalculusSupply X ↔ ∀ j hj, ∃ B : LevelSiteBank
  (core.T.trunc j hj.2.le), BankWiredAt X j hj B` — an **equivalence** (unlike the
  WSS/USUP sufficient-only reductions, nothing is lost in this split).  `BankWiredAt`
  (NEW) is the per-realization residue: ONE `GC13Wiring` read law at the bank's calculus
  — no calculus datum, no B-1 clause.  ★ `siteCalculusSupply_of_bankFamily` — the
  factored normal form (bank FAMILY as data + `BankWiringSupply`); the `Nonempty`-form
  composition subtlety is recorded.  `LevelSiteBank.toWleExport`: bank + wiring alone
  already assembles the full `WleClearedLevelExport` — the "`WleCleared` truncation
  exporter" of IFC3's fence, realized at the bank interface.
* **§3 wrappers**: `wleSiteExists_of_bank` (WSS §3's nine bank-side hypotheses folded
  into the bank), `wiredSiteSupply_of_bankFamily`,
  `gentowPerWitnessExporter_of_bankFamily`.
* **§4 ★ the universal factorization**: `UniversalWiredBankSupply n` (NEW) +
  `universalSiteCalculusSupply_iff_wiredBank` — the fault line is exact at the universal
  level too, so HALF of WSS's remaining site boundary is now the pair (universal bank
  family, universal wiring), each strictly smaller.
* **§5 keystone nonvacuity + ★ THE CONDITIONALITY SPLIT**: `s2FourSiteBank :
  LevelSiteBank (s2TruncThree h2 hq)` — the keystone bank as a STANDALONE tower-side
  datum needing `(h2, hq)` ALONE (no thresholds `w₁…w₄`, no `IsAdicComplete`, no R8r
  payload, no realized input) — machine-visible evidence that the bank half is FRAME
  data while the wiring half is WITNESS data.  `s2Four_siteCalculusSupply_of_bank`
  re-derives WSS's keystone supply through the factored route (bank + `s2Four_gc13Wiring`
  through the §2 iff), and the coherence example re-derives the landed `WiredSiteSupply`
  instance.

## Honesty — what does NOT close, named exactly

**`UniversalSiteCalculusSupply n` is NOT proved** (charge 2's all-fields case did not
occur), and by Correction 2 it CANNOT be closed by any tower-side engine alone.  The
remaining boundary, jointly EXACTLY the supply (the §2/§4 iffs — no sufficiency gap):

| leftover | side | discharging math | character |
|---|---|---|---|
| `LevelSiteBank` family at every deep-live truncation | tower | the L2E program's remaining generic mathematics: the WEIGHTED absolute-read convolution carrier (L2E4's adjudication — the unweighted law is refuted), the D3-03 depth adapter, key lifting (`Rres_exists` genre) at general frames, the B-1 normalizer-grade computation, and the `PrevGrade` leg at `f' ≥ 2` | research (DWR §11.7); parametric in FORM |
| `BankWiringSupply` at that family | realization | GC-13 read law on the realization's own exports at the bank's calculus | per-realization export coherence (the same character as `LadderReadSupply`); ONE equation family per level |

Strict progress vs the pre-SCS boundary: the per-realization demand no longer mentions
the calculus's existence, the B-1 clauses, or any FGMN construction — those now live
in a realization-free tower-side datum with a named research program; and the two halves
are tied by an iff, so future work on either half composes losslessly.

## Notes for the orchestrator

* First-attempt compile on BOTH increments (skeleton §§1–4, then §5) — no repair rounds.
  The anticipated defeq risk at the keystone (`LevelSiteBank (core.T.trunc 3 _)` vs
  `LevelSiteBank (s2TruncThree h2 hq)`; structure-literal projection
  `(s2FourSiteBank …).calculus ≡ s2SiteMu4Calculus`) did not bite: `exact` unified both.
* Provenance audit method: subagent sweep over the 13 suppliers of `s2SiteSourceLaws`
  (proof sites + one level down + import graph).  Key structural fact worth reusing:
  **only `C136d2.lean` imports any L2E file, and only `l2e4`** — the D3 stack's entire
  L2E dependence funnels through `s2Mu4Coeff_mul`.
* Flagged NEW statements for the standing review: `LevelSiteBank`, `BankWiredAt`,
  `BankWiringSupply`, `TowerBankSupply`, `UniversalWiredBankSupply` (supplier-side
  interface shapes below the signed surface; no leanspec name touched; `SiteCalculusSupply`
  consumed verbatim on both sides of an iff — nothing weakened).
* AxCheck: 20/20 declarations print `[propext, Classical.choice, Quot.sound]` — no cite,
  no new axiom, nothing added to the trusted base.
* Universe note: `LevelSiteBank.{uKt}` at `DeepTower.{0, uKt}`; supplier Props follow
  WSS's `{uG, uKt, uL}`; keystone pinned `.{0}` / `.{0, 0, uL}`.
