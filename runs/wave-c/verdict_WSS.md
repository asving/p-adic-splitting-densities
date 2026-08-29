# verdict_WSS — UNIT WSS: the wired-site supply at general residue cardinality (rows C0/C1/C2)

**Status: COMPLETE (reduction landed; the supply does NOT close — the named remainder is
strictly smaller than `WiredSiteSupply`).**
`leanfinal/Uniformity/ChapI/I10SiteSupply.lean` — 0 errors, 0 `sorry`, all **15** printed
footprints Lean core `{propext, Classical.choice, Quot.sound}`.  Verified per-file
(`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10SiteSupply.lean`, clean) AND
per-target (`lake build Uniformity.ChapI.I10SiteSupply` — Build completed successfully,
8969 jobs); the chapter aggregator `Uniformity/ChapI.lean` re-verified after the one
standing import-line edit.  Cite ledger: **empty**.  Repo footprint: the new module + the
aggregator line + this verdict, nothing else.

## Charge 1 — SCOPE: card-2 convenience vs essence, per demanded law (settled)

Target (USUP §3): `WiredSiteSupply X` = at every deep-live level, ∃ site
`WleClearedLevelExport` (triple `(e',f',u')`, `0 < f'`, `FGMNCalculus` on the truncated
tower, `GENTOW5WCleared` top law, `GC13Wiring` leg) + `ThetaCompatibleAt` ∧
`PeelCompatibleAt` ∧ `RangeCompleteAt`.  Dissection of the keystone constructions
(C136c0) + the L2E bank (C136l2e0–4) + GCW-4/5:

| demanded law | keystone proof | verdict |
|---|---|---|
| `cleared : GENTOW5WCleared` (row C1) | `gentow5w_cleared_of_B1` at the B-1 supplies | **card-2 never used** — the landed engine (`C132sg3.ratio_power_law_cleared`) is depth- and q-generic; the law is DERIVED here, no longer demanded |
| `thetaRatioCleared 1 = 1` | card-2 value collapse `Rgr = 1` | **convenience** — essence is `a·a⁻¹ = 1` at `a ≠ 0`; promoted to general q (§1) |
| `ThetaCompatibleAt` (C2, GCW-4) | "nonzero in the 2-element field ⇒ 1" | **convenience in its calculus coupling** — given B-1 + wiring, `φ(thetaRatioCleared s)` is FORCED to `R(n̂ q)^s / R(n̂(s·q))` (cleared power law + `Rgr_ne_zero` + receiver injectivity between fields); the residue is calculus-free |
| `PeelCompatibleAt` (C2) | both sides `1` | **splits** — the `∃wC` power-law clause IS the cleared engine's conclusion at the canonical witness `wC = Rgr(e'u')(n̂(u'))` (derived); residue = ONE calculus-free tie `(peelUnit : Kt) = R(n̂ q)` |
| `RangeCompleteAt` (C2, GCW-5) | card-2 collapses | already calculus-free except through `S.f'`; both clauses are instances of the same ladder law + tie |
| `wiring : GC13Wiring` (C0) | both sides `1` | **genuine (c)** — a real per-realization relation at general q |
| calculus + B-1 supplies (C0/C1) | D3-stack μ₄ bank | **genuine (c)** — post-PK `ChainRealization` carries no calculus (USUP's structural finding); the L2E shared engine (C136l2e0–4, verified frame-generic: "no declaration specialized to the S2 datum") is the campaign program that produces exactly this |

**Scope answer**: the site package is NOT constructible from the realization's own fields
+ generic residue algebra alone — but the three consumer dictionaries' ENTIRE calculus
coupling is generic and is discharged here, uniform in q.

## Charges 2/3 — what landed (namespace `Uniformity.Density.DeepExport`)

* **§1 generic layer**: `thetaRatioCleared_one_of_ne_zero` (general-q supersession of the
  keystone's card-2 route; coherence example re-derives the keystone's
  `thetaRatioCleared 1 = 1` with NO card-2 input).
* **§2 the named remainder** (NEW STATEMENTS, review):
  - `LadderReadLaw X hr j` — row C2's exact calculus-free residue: the D.44 ladder law
    `R(n̂(s·q)) = θ(s)·R(n̂ q)^s` (all s ≥ 1), the `s = 0` head (verbatim
    `RangeCompleteAt`'s first clause), and the peel tie `(peelUnit : Kt) = R(n̂ q)`.
    NO FGMN operator occurs in any clause.
  - `SiteCalculusSupply X` — rows C0/C1: per deep-live level ∃ positive triple + site
    calculus + the four B-1 normalizer supplies + the GC-13 wiring leg (exactly what an
    L2E-genre bank engine produces; the cleared law is NOT demanded).
  - `LadderReadSupply X` — `LadderReadLaw` at every deep-live level.
  - Shallow vacuity teeth for both.
* **§3 ★ the generic reduction (the unit's theorem content)**:
  - ★ `wleSiteExists_of_supplies` — bank + wiring + ladder law ⟹ the FULL per-level
    `WiredSiteSupply` content (site with DERIVED cleared law; all three dictionaries with
    DERIVED calculus coupling).  Uniform in q: no cardinality, no S2 datum, no numeral.
  - ★ `wiredSiteSupply_of_supplies : SiteCalculusSupply X → LadderReadSupply X →
    WiredSiteSupply X` + `gentowPerWitnessExporter_of_supplies`.
* **§4 universal forms**: `UniversalSiteCalculusSupply n` / `UniversalLadderReadSupply n`
  (NEW STATEMENTS), ★ `universalWiredSiteSupply_of_supplies` — fires USUP's
  `UniversalWiredSiteSupply n`, i.e. HALF the capstone deepTwist boundary now sits at the
  strictly smaller bank/ladder surface — and ★ `deepTwistField_of_bank_supplies` : the
  capstone `deepTwist` field from THREE named supply Props (USUP's tau supply + these
  two), through `deepTwistField_of_supplies`.
* **§5 keystone nonvacuity**: `s2Four_siteCalculusSupply` + `s2Four_ladderReadSupply` at
  EVERY depth-4 keystone witness (full parametric payload; conditionality exactly the
  keystone's: `w₁ w₂ w₃ w₄` + `IsAdicComplete` + R8r payload), plus the coherence pin —
  the new generic route re-derives the landed `WiredSiteSupply` instance on the wired
  genre.  The card-2 collapses are now visibly CONFINED to the calculus-free residue.

## Honesty — what does NOT close, named exactly

`UniversalWiredSiteSupply` is NOT proved: per the landed iff
(`deepTwistField_iff_universalPerWitness`) the leftover IS (half) the capstone field.
The reduction is SUFFICIENT-ONLY (the constructive normal form, same character as USUP
§2); no converse claimed.  Remaining boundary, per arising realization and deep-live
level:

| leftover Prop | rows | discharging math | character |
|---|---|---|---|
| `SiteCalculusSupply` | C0/C1 | per-level FGMN operator banks at general towers (L2E shared engine, already frame-generic in C136l2e0–4) + the GC-13 wiring law | research (L2E program, DWR §11.7); parametric in FORM |
| `LadderReadSupply` | C2 residue | the D.44 ladder-read law on the realization's OWN exports (`R`/`θ`/peel unit) | strictly smaller than GCW-4/GCW-5 as scoped: all calculus coupling discharged; pure per-realization export coherence |

Strict progress vs the pre-WSS boundary: the demanded surface no longer contains the
cleared `∃w` law, the peel power-law clause, or ANY dictionary mention of
`Rgr`/`thetaRatioCleared`/`chainNormBelow`.

## Notes for the orchestrator

* Lean gotcha recorded: the receiver `levelHom j` has domain `core.T.fld j` while
  calculus terms live at `(core.T.trunc j _).fld j` — defeq but NOT reducibly, so `rw`
  and `simpa` fail to match across the boundary (invisible "identical types" mismatch).
  Fix pattern: term-level assembly (`congrArg`/`map_mul _ _ _`/`.trans`) for
  cross-boundary steps; `rw` only on pure Kt-side patterns; align `hr` proof terms via a
  re-typed `have hlad' : LadderReadLaw X hr1 j := hlad` before rewriting with theta
  fields.
* One landed-file edit: the ChapI aggregator import line (standing convention).
* Flagged NEW statements for the standing review: `LadderReadLaw`, `SiteCalculusSupply`,
  `LadderReadSupply`, `UniversalSiteCalculusSupply`, `UniversalLadderReadSupply`
  (supplier-side interface Props below the signed surface; no leanspec name touched).
* AxCheck: 15/15 declarations print `[propext, Classical.choice, Quot.sound]` — no cite,
  no new axiom, nothing added to the trusted base.
* Universe note: the new Props follow USUP's convention (`{uG, uKt, uL}`, site pieces at
  `uE = 0`); keystone instances pinned `.{0, 0, uL}` matching USUP's keystone site pin.
