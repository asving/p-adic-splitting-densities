# VERDICT — unit WLE: witness-dependent `WleCleared` exporter design

**[WLE, 2026-08-28] · STATUS: DESIGNED-ANCHORED; DEEP INHABITANTS OPEN.**  The dated design
record is appended to `docs/in-progress/GC13_WIRING_2026-08-27.md`.  Statement authority is
the new zero-`sorry` probe `leanfinal/scratch/WLE_probe.lean`.  No landed `.lean`, leanspec,
socket, `CapstoneHypotheses`, guard, or existing scratch file was edited; no commit was made.

## DESIGNED-ANCHORED — per-level export

`WleClearedLevelExport X j hjr` is the dependent owner package.  It contains:

* positive parameters `(e',f',u')` with `0 < f'`;
* a calculus family `I i hi : FGMNCalculus (core.T.trunc i hi) e' f' u'`;
* `WleCleared core.T e' f' u' I j`;
* `GC13Wiring` at the explicit witness's own transported normalizer, `useHeightFamily X j`,
  `towerReadFamily X j`, top calculus `I j hjr`, and canonical receiver
  `Aℛ.receiver.levelHom j`.

The exporter is exactly

```lean
def WleClearedPerLevelExporter (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) →
    Nonempty (WleClearedLevelExport X j hj.2.le)
```

At a deep level, `S.cleared j hj.1 le_rfl hj.2.le` is the top
`GENTOW5WCleared (core.T.trunc j ...) ...`; probe theorem
`WleClearedLevelExport.top_cleared` compiles this projection.

The binder placement is machine-anchored:

* the free-`f'=0` existential defect is excluded by `S.f_pos` and the nonvacuous `j ≥ 3`
  top projection (`IFC3.gc13Wiring_vacuous_of_f'_zero` remains the falsifier);
* no law is demanded at every arbitrary calculus—one owner-exported package is produced;
* `core, Aℛ, X` precede `j` and `S`, so every site component can depend on the witness;
* the range is exactly `DeepLive core.r j`, so no junk export branch is consumed.

## DESIGNED-ANCHORED — universal wired supplier

`UniversalWiredDeepGentowSupplier n` quantifies over explicit `core`, `Aℛ`, and `X`, assumes
that this explicit witness has `WleClearedPerLevelExporter X`, then concludes at every
`DeepLive` level:

```lean
∃ S : WleClearedLevelExport X j hj.2.le,
  IFC3.WiredGentowDemand
    (arenaFamily X ... j) (useHeightFamily X j) (towerReadFamily X j)
    (Aℛ.node.peelUnitFamily j) (S.calculus j hj.2.le)
    (Aℛ.receiver.levelHom j)
```

This is a strict strengthening of IFC0's flat `DeepGentowSupplier` conclusion at the
explicit witness; `.gentowW` projects the old conclusion.  It does not extend the byte-frozen
socket guard.  The complete elaborated statement is at probe lines 58–74.

`wiredDemand_of_level_export` is proved in the probe, not sorry-backed: a level export plus
`ThetaCompatibleAt`, `PeelCompatibleAt`, and `RangeCompleteAt` feeds
`IFC1.gentowWWindow_of_cleared_law`, then
`IFC1.gentowW_iff_zero_window_tail`, yielding `WiredGentowDemand`.

## BLOCKED-BECAUSE — why this is not landed supply

Today's `ChainRealization` has no FGMN calculus field: PK-1 deliberately factored the FGMN
legs out.  Therefore the owner package is a new standalone export obligation, not a projection
from a bare `RealizedInput`.  Deep inhabitants require source-faithful FGMN realization data
(FIELDLIST §8 OPEN-DICT-1–4) and the open C.89 single-`w` mathematics.  Freely fabricating
the existential calculus would be the same cooked-site error in a new wrapper.

Likewise, the byte-frozen external `CanonicalDeepTwistConfig` does not by itself imply that
its hidden realization is wired.  A later capstone binding needs an honest theorem that every
consumed deep configuration exports the witness package; a zero-read deep witness would refute
such a theorem.  No guard extension or socket change is proposed here.

## S2 adjudication

The S2 chain recovers the local route but is **not literally a deep exporter instance**:

* `C132sg3.s2Mu3_gentow5w_two` is the positive depth-2 cleared endpoint;
* `IFC4.s2Wired_gc13Wiring` is the own-export wiring law;
* their translation is exactly `IFC4.s2Wired_gentowWWindow_at_own_exports`, and IFC4 already
  proves the stronger `s2Wired_wiredGentowDemand_at_own_exports`.

However, `WleCleared ... 2` is vacuous because the carrier begins at rung `3`, and
`DeepLive 2 j` is empty.  The own-export theorem is at `GaugeLive 2 j`, hence at S2 `j=1`,
while `s2Mu3Calculus` has depth 2; `j=2` is off the gauge-live range.  Probe theorems
`no_s2_deep_level` and `wleCleared_two_vacuous` machine-pin the discrepancy.  Thus S2 is the
documented depth-2 shape/base tooth, not evidence of any `3 ≤ j < r` export.

## OPEN-LEMMA — deep arising-witness campaign

For every explicit `X`, `hj : DeepLive core.r j`, and exported `S`, the campaign owes:

1. `deep_wleCleared_level_export`:
   `Nonempty (WleClearedLevelExport X j hj.2.le)` — includes the source-faithful calculus,
   positive `f'`, cumulative/top cleared law, and own-export GC13 wiring.
2. `deep_thetaCompatibleAt`:
   `ThetaCompatibleAt X (by omega) S` — the general-exponent GCW-4 dictionary.
3. `deep_peelCompatibleAt`:
   `PeelCompatibleAt X S` — the top cleared single-`w` witness maps to this witness's own
   exported peel unit.
4. `deep_rangeCompleteAt`:
   `RangeCompleteAt X (by omega) S` — D.44's `s=0` clause and `s>S.f'` tail at own exports.

All four exact statements are printed in the dated design record and their carrier predicates
compile in the probe.  All remain mathematically open for `r ≥ 4`.

## Validation

From `leanfinal/`:

```text
timeout 580 ~/.elan/bin/lake env lean scratch/WLE_probe.lean
```

Exit 0, no output, no `sorry`, no new axiom.
