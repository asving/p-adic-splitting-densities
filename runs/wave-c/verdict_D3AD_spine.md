# Verdict D3AD (SPINE) — the D3-03 spine adapter LANDS: `LevelDatum` per truncation from `DeepTower`, rung-2 packs at every arising tower truncation, B-1 PROVED from the tower's own floor chain (2026-08-30)

**Status: COMPLETE.** `leanfinal/Uniformity/ChapI/I10SpineAdapter.lean` (NEW, ~390 lines,
namespace `Uniformity.Density.Tower.I10spine`) — 0 errors, 0 warnings, 0 `sorry`; all
**15** printed footprints exactly `[propext, Classical.choice, Quot.sound]`.  Verified
per-file (`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10SpineAdapter.lean`,
exit 0), per-target (`lake build Uniformity.ChapI.I10SpineAdapter` — Build completed
successfully, 8854 jobs), and the chapter aggregator `Uniformity/ChapI.lean` re-verified
exit 0 after the one standing import-line edit.  Cite ledger: **empty** — Lean core only;
no numeral, no `residueCard`, no S2 datum in any declaration (grep: docstring prose only).

**NAMING NOTE (read first):** `runs/wave-c/verdict_D3AD.md` is a DIFFERENT, already-landed
2026-08-28 unit (the depth-three μ-key adapter, `ChapC/C136d3ad.lean` — the DWC blueprint's
OLD "D3-03 μ3 survival core" row, superseded numbering).  THIS unit is the site bank's
D3-03 remainder row as named in `verdict_RUNG.md` §4 / `verdict_SCS.md`: the
LevelDatum-per-truncation-from-`DeepTower` **spine identification**.  This verdict lives at
`verdict_D3AD_spine.md` to preserve the earlier unit's audit trail.

## STATUS FIRST

| charge | status | exact result |
|---|---|---|
| 1. per-field scope | **GREEN — every field derivable; correspondence mapped; the rungs-≥3 fence recorded** | a `LevelDatum` is EXACTLY the tower's stage-2 data through the LANDED C.42/C.44 depth-2 bridge (table below); higher rungs are PROVABLY not `LevelDatum`-shaped (frame-anchored `r`/`hκ`; no `KeyFrame` at stages ≥ 2) — they enter only through RUNG's `RungLift`, per its §2.3 adjudication |
| 2. the adapter + ★ instantiation | **GREEN — ★ LANDED, Lean-core, uniform in `q` and the frame** | `levelDatumOf : DeepTower F H₀ hpin r → 2 ≤ r → Irreducible π → LevelDatum F H₀ hpin` + truncation coherence AT `rfl` (`levelDatumOf_trunc` — the datum is truncation-INVARIANT); ★ `truncRung2Pack`/`arisingRung2Pack` — RUNG's rung-2 pack at EVERY tower/arising-core truncation `3 ≤ j ≤ r`, key = C.47's `composedKey` (canonical, not just `Nonempty`), slopes = the tower's OWN `(T.u 3, T.e 3)`; the convolution `wcoeff_mul` fires there (`truncRung2_wcoeff_mul`, `arising_rung2_wcoeff_mul`); `towerPackAt` bundles it as the `towerPacks` BASE POINT — **the bank's depth-adapter row (D3-03) DISCHARGED at rung 2** |
| 3. the B-1 slope inequality | **GREEN — PROVED from the tower's own strictness** | `levelDatumOf_b1 : T.e 3 * (L.ℓ * L.seam) < T.u 3` — RUNG's named remainder `ℓ₂·(L.ℓ·L.seam) < u₂` at `(u₂,ℓ₂) := (T.u 3, T.e 3)` IS the tower's floor-chain DATUM FIELD `T.hfloor 2` (`u₃ > e₃·E₂`), via the new identification `L.ℓ·L.seam = T.Econst 2` (`levelDatumOf_kgrade`); this is exactly where the keystone's `+1` thresholds live (S2: `85 = 2·42+1 > 84`); honesty: per C.83's S12.1 carve-out `hfloor` is a HYPOTHESIS of the tower datum, inherited, not re-derived |

## Charge 1 — the per-field correspondence (the spine identification)

Route: `DeepTower --(stage-2 fields)--> TowerDatum (C.42) --(C.44 levelDatum)--> LevelDatum (C.09)`,
so the η-twisted label (`towerLabel`), its four properties (`towerLabel_spec`), and the
canonical test key (`composedKey_isTestKey`, C.47) are consumed from landed nodes, never
re-derived.  Per field:

| `LevelDatum` field | tower supply (truncation-invariant) |
|---|---|
| `u` | `T.u 2` |
| `ℓ` | `T.e 2` |
| `r` | `towerLabel` of the stage-2 `TowerDatum` whose `ψ₂ = (T.ψ 1).map T.base` (the GC-7 iterate witness moves `ψ₁` to the concrete stage field; the η-twist enters via C.44; consumes `hπ`) |
| `hℓ` | `T.he 2` |
| `hcop` | `T.hcop 2` |
| `hκ` | `T.hfloor 1` + the frame pins `he1/hf1/hu1` (+ one `mul_assoc`) |
| `hrmonic/hrirr/hr0/hrdeg` | `T.hψ 1` transported along `T.base` (`spineResidual_spec`: monic along the hom; irreducible along `Polynomial.mapEquiv` + `MulEquiv.irreducible_iff`; degree/constant term by injectivity), then `towerLabel_spec` |

Honest inputs: `2 ≤ r` (a depth-1 tower carries no level datum) and `hπ : Irreducible π`
(the stage letter's unitness, consumed once through C.44 — same as every landed consumer).

**The rungs-≥ 3 fence (recorded, not papered over):** `LevelDatum` is FRAME-anchored (its
`r` lives over `F.stageField H₀ hpin`; its `hκ` reads `F.e₁·F.f₁·F.h`), and a `DeepTower`
carries no `KeyFrame` at stages ≥ 2 — so there is NO j-indexed family of `LevelDatum`s
covering higher rungs.  The per-truncation output is the truncation-INVARIANT rung-2 datum
(exactly what `rung2Carrier` consumes at each `core.T.trunc j hj`); rungs ≥ 3 feed the
machinery through `towerPacks` given per-rung `RungLift`s — unchanged, RUNG's remaining
research leg.

## Charge 2 — what landed (all Lean-core, all sorry-free)

§0 private twins `isKey_X`/`localFieldStageField` (**4th corpus repetition — flagged for
the dedup pass**).

§1 the identification: `spineResidual` (+`_spec`), `towerDatumOf` (+ 4 rfl pins,
`towerDatumOf_trunc = rfl`), ★ `levelDatumOf` := the C.44 bridge at it, with pins
`levelDatumOf_u/ℓ/r` (rfl), `levelDatumOf_r_natDegree` (`= T.f 2`),
`levelDatumOf_keyDeg₂` (`= (F.e₁*F.f₁)·e₂·f₂`), `levelDatumOf_keyDeg₂_Dcum`
(`= T.Dcum 2` — the datum's key degree IS the tower's ladder numeral `D₂`),
`levelDatumOf_seam` (`= T.f 2 * T.u 2`), ★ `levelDatumOf_kgrade`
(`L.ℓ·L.seam = T.Econst 2` — the rung-2 key grade IS the side constant `E₂`),
`levelDatumOf_trunc` (coherence, `rfl`-level via `congrArg`), ★ `levelDatumOf_b1`.

§2 `isTestKey_composedKey` — C.47 consumed verbatim at the adapter's datum (under the
standing `hh` and `[Finite (ResidueField O)]`).

§3 the instantiation: `towerRung2Carrier`/`towerRung2Key`/★★ `towerRung2Pack`
(`RungPack O (AdjoinRoot L.r) (T.u 3) (T.e 3)`), ★ `truncRung2Pack` at every `3 ≤ j ≤ r`,
★ `truncRung2_wcoeff_mul` (the weighted convolution at every truncation's pack),
★ `towerPackAt : PackAt O` (the `towerPacks` recursion base at the adapter — an arising
tower's own rungs now feed the iterated carrier machinery given `LiftAt`s).

§4 the arising layer at `ArisingCore` (C130a): `arisingLevelDatum`, `arisingLevelDatum_eq`
(ALL truncations hand the machinery ONE datum), ★ `arisingRung2Pack`,
★ `arising_rung2_wcoeff_mul`.  The core supplies `π`/`hπ`/frame/tower/residue-field
finiteness (`core.finite`); the honest remainders are `0 < core.F.h` (an `ArisingCore`
does not pin `h ≥ 1`) and the depth bound `3 ≤ j` (stage-3 slopes must exist).

## RUNG's obligation map after this unit

| leg | before (verdict_RUNG §4) | after |
|---|---|---|
| depth adapter (D3-03) | open — "the LevelDatum-per-truncation-from-DeepTower spine identification remains the research leg" | **DISCHARGED**: `levelDatumOf` + trunc-invariance; rung-2 packs fire at every tower/arising truncation with the tower's own slopes and the canonical composed key |
| B-1 at rung 2 | reduced to the single slope inequality `ℓ₂·(L.ℓ·L.seam) < u₂` | **PROVED at the adapter's output** = `T.hfloor 2` (tower-datum hypothesis, S12.1 carve-out) via `L.ℓ·L.seam = T.Econst 2` |
| key lifting rungs ≥ 3 (`RungLift`) | open, shape pinned | untouched (out of scope; the fence above explains why no LevelDatum route exists) |
| `LevelSiteBank` / `FGMNCalculus` at a truncation | open (SCS) | untouched — this unit feeds the CARRIER machinery per truncation; the bank's calculus leg is the L2E program's remaining mathematics |

## Honesty

* Uniform in `q` and the frame: zero numerals, zero `residueCard`, zero S2 data in
  declarations (grep hits: docstring prose only).
* Nothing weakened: `LevelDatum`/`TowerDatum`/`DeepTower`/`RungPack`/`CarrierKey` consumed
  verbatim; no landed file edited (aggregator import line only); `hfloor`, `hπ`, `hh`,
  `2 ≤ r`/`3 ≤ j`, `Finite (ResidueField O)` carried as honest hypotheses exactly where the
  corpus carries them.
* The adapter's `LevelDatum` is truncation-invariant BY CONSTRUCTION (`trunc` re-scopes
  hypotheses only) — recorded as the coherence lemmas rather than hidden.

## New statements flagged for the standing review

`spineResidual`, `towerDatumOf`, `levelDatumOf`, `truncRung2Pack`, `towerPackAt`,
`arisingLevelDatum`, `arisingRung2Pack` (supplier-side interface shapes below the signed
surface; no leanspec name touched).

## Verification, repair log, footprint

* Per-increment command run throughout (skeleton → `spineResidual_spec` → 8-pin batch →
  `towerPackAt`); FINAL: per-file exit 0 with 0 errors/warnings/`sorry`; AxCheck **15/15**
  Lean-core (`towerDatumOf`, `levelDatumOf`, `levelDatumOf_trunc`, `levelDatumOf_kgrade`,
  `levelDatumOf_b1`, `isTestKey_composedKey`, `towerRung2Carrier`, `towerRung2Key`,
  `towerRung2Pack`, `truncRung2Pack`, `truncRung2_wcoeff_mul`, `towerPackAt`,
  `arisingLevelDatum`, `arisingRung2Pack`, `arising_rung2_wcoeff_mul`);
  `lake build Uniformity.ChapI.I10SpineAdapter` — success (8854 jobs); aggregator
  re-verified exit 0.
* Repair log: **zero repairs** — every increment compiled first-pass (the skeleton's full
  signature layer included).  Notable non-events: (a) the RUNG defeq gotcha did NOT bite —
  `towerDatumOf_trunc` and the structure-literal coherences close by `rfl`/`congrArg`
  (trunc changes no data; proof fields by irrelevance); (b) `0 < F.h` vs `1 ≤ F.h` unified
  definitionally; (c) the `PackAt` instance-diamond risk (ambient `instCommRing` vs
  `AdjoinRoot.instField.toCommRing`) did not bite, matching RUNG's precedent.
* Footprint: `leanfinal/Uniformity/ChapI/I10SpineAdapter.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No landed theorem file
  edited; no git operation; IFCG25 untouched.
