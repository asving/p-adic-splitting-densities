# Unit SIMP verdict — the read-only simplification map

**Charge:** map the duplication/consolidation opportunities the 2026-08-24–26 sprint
created in `leanfinal/Uniformity/ChapC/` (~90 new C130*/C131* + sibling files), across four
named suspects (duplicate lemma clusters, private-helper re-derivations, refuter/quarantine
record conventions, file sprawl), and produce the enactment plan for a later wave.
**READ-ONLY**: no Lean file was edited or written; no `git add`/commit performed.
**Deliverables:** `docs/in-progress/SIMPLIFICATION_MAP_2026-08-26.md` (the four tables + a
5-tier ranked enactment plan) + this verdict.

## Verdict: MAP DELIVERED — 4 suspects surveyed, 2 live-risk items flagged for immediate attention

| suspect | verdict | headline finding |
|---|---|---|
| Duplicate lemma clusters | SURVEYED | `C131ae.lean` and `C131y.lean` independently built the SAME 11-lemma "ultrametric equality-off-ties + negation" chain (identical statements, mostly identical names), with neither file importing the other; both copies are externally cited (`C130rp2` calls `C131y.twistRead_add_deep`). Also: 4 independent private redefinitions of `C118a.smul_top_pos` (`C127`, `C131y`, `C27`, `C72` — one self-documented as "private does not export"). `toZ` itself is NOT duplicated (single def site, dictionary lemmas each defined once, just split across 3 files). |
| Private-helper re-derivations | SURVEYED | ~141 `private` declarations in the new files; 13 distinct facts collapse ~35–40 of them into re-derivation clusters (worst: an S2 key-degree numeral re-derived **7×**, self-docstringed each time as "the private-copy pattern"). Two rows carry real risk rather than being free hygiene wins: a 4-way same-namespace `slot_eq`/`window_data` collision (`C14`/`C46`/`C47`/`C131f`), and a genuinely live ambiguous-name landmine in `C131af.lean:46-47` (opens both `ChapB.B39b`'s and `C131ae`'s namespaces — dormant only because no bare reference has been written yet). |
| Refuter/quarantine conventions | SURVEYED | Four coexisting conventions (dedicated old `lean/quarantine/` dir + README; scattered in-place `.lean.txt`/`.md` in ChapC with no index; in-file `QUARANTINE` prose markers on code kept compiling for a live `IsEmpty` theorem's sake; `runs/wave-*/verdict_*.md` process records). Found one concrete same-fact double-recording (`verdict_FD01.md` ↔ `C130k2.lean:288-292`). Recommendation: add one new `docs/DEAD_ENDS_INDEX.md`; move nothing (Convention C is structurally immovable; the old dir's README just needs 4 backfilled entries). |
| File sprawl (C130*/C131*) | SURVEYED | Full topic map of all ~90 files with an import graph. 13 files are excluded outright (PK12 RUNNING retype, per `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` §5). Clean, low-risk merge candidates identified (freeze-v2 preamble quartet, DT1/DT2 definitional twins, two DV-engine small pairs, three GENTOW2/5 supply-cascade pairs); several staged proof ladders (NV/RP/KP) and the deliberately-separate C123/C123r pair correctly flagged STAY-SEPARATE, not sprawl. |

No approximation was introduced and none is proposed: no Lean statement is changed by any
recommendation in the map; every "promote private → public" and "merge files" item is
flagged by whether it's a pure move/visibility change or a proof-touching consolidation
that must re-enter the standard build + `#print axioms` + byte-identity verification bar
when a later unit enacts it.

## Files

* `docs/in-progress/SIMPLIFICATION_MAP_2026-08-26.md` (new) — the four tables + the 5-tier
  ranked enactment plan (Tier 1 cheap/safe, Tier 2 urgent-flavored live risks, Tier 3
  moderate-effort real dedup, Tier 4 defer/schedule-separately).
* `runs/wave-b/verdict_SIMP.md` (this file).
* No file under `leanfinal/` was created, edited, or moved. `leanfinal/scratch/SIMP_probe.lean`
  was NOT used — no elaboration probe was needed for a read-only survey.

## Flagged for immediate attention (independent of this map's own enactment scheduling)

1. **`C131af.lean:46-47`** — the live ambiguous-name risk (dual namespace `open`). Cheap to
   fix, worth doing before any other DV-engine-family edit lands near it.
2. **`C14.lean`/`C46.lean`/`C47.lean`/`C131f.lean`** — all four declare `slot_eq` in the same
   namespace (`Uniformity.Density.Tower`); any future blanket "unprivate everything" pass
   must NOT touch this cluster mechanically.

## Verification

None applicable — no Lean file changed. The map itself was cross-checked by four
independent research passes reading file:line evidence directly (not name-matching), and
every duplication/collision claim in `SIMPLIFICATION_MAP_2026-08-26.md` carries an exact
file:line citation for the next unit to re-verify before enacting.
