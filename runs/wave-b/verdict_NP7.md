# Verdict — unit NP7F: S2-source plan node NP-7 (finisher)

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 row NP-7.
File: `leanfinal/Uniformity/ChapC/C130np7.lean` (draft found on disk at 20KB from the
dead predecessor agent; verified and repaired here, nothing else touched).

## Verdict: LANDED, 21/21 declarations, nothing dropped

The draft's mathematics was sound; only two mechanical defects blocked verification, both
fixed without touching any statement:

1. **Fence self-mention (honesty-ledger prose, not code).** The docstring's own disclaimer
   ("this file does not touch `arenaRead`, `towerRead`, `peelUnit`, or `GaugeArena`")
   literally contained the fenced identifiers, so the required grep
   `rg -n "arenaRead|GaugeArena|towerRead|peelUnit" C130np7.lean` was non-empty even though
   NO code in the file uses these objects. Reworded to "NP-8's arena/tower-read/peel-unit/
   gauge-arena objects" (same meaning, no literal substring match). Grep is now empty
   (confirmed below).
2. **One real proof gap**, in `s2_levelExponentHeight_two`: after `Fin.sum_univ_one`
   instantiates the level-two sum's index at `(0 : Fin 1)`, the resulting term reads
   `.ehat (2 + ↑(0 : Fin 1))` / `.u (2 + ↑(0 : Fin 1))`, not the literal `.ehat 2`/`.u 2` the
   `have`-lemmas (`hehat2`, `hu2`) are stated at — `simp only [he1, hu1, hehat2, hu2]` alone
   left `↑(0 : Fin 1)` un-reduced, so `ring` saw two different atoms and failed
   ("unsolved goals", case `e_6`). Fix: added `Fin.val_zero` to the `simp only` set so
   `↑(0:Fin 1)` reduces to `0` (then `2 + 0 → 2` by the default arithmetic simproc,
   `hehat2`/`hu2` fire, `ring` closes). No statement changed; the theorem now proves exactly
   what it always claimed.
   Cosmetic-only: also dropped three simp lemmas (`Finset.univ_eq_empty`, `Finset.sum_empty`,
   `add_zero`) from `s2_levelExponentHeight_one`'s proof that the linter flagged as unused
   (`he1, hu1, hehat1` alone already close the `Fin 0` case) — zero warnings now, no
   behavior change.

**Nothing was dropped from the draft.** All 21 declarations the dead agent wrote survive
unchanged in statement: the four height-law lemmas (`s2_levelExponentHeight_one/two`,
`s2_mem_ker_one_iff`, `s2_mem_ker_two_iff`/`'`), the level-one read (`s2CanonicalRead1` +
`_coe` + `_wrapClass`), the level-two generator coordinates (`s2_wrapClass_two_coe`,
`s2_letterClass_two_coe`), the level-two read (`s2CanonicalRead2` + `_coe` + `_wrapClass` +
`_letterClass` + `_generatorWord` + `_generatorWord_eq_one`), and the total field-shaped
read (`s2CanonicalRead` + `_one` + `_two` + `_wrapClass` + `_letterClass`). The construction
matches the brief: `canonicalRead`'s exact field shape from `C130s17`, generator
regressions tying to CC-10's D62w teeth pattern, `laurentSolve` unfolded via its equation
lemmas + `decide` (not defeq) per CC-10's recorded gotcha, and the tie to NP-6's
`s2AmbientLetter` (both generator regressions land on `s2AmbientLetter L 1`/`L 2`).

## Fence and hygiene checks

* `rg -n "arenaRead|GaugeArena|towerRead|peelUnit" Uniformity/ChapC/C130np7.lean` → **no
  output** (exit 1). Confirmed clean after the reword.
* `rg -n "sorry|^axiom|unsafe" Uniformity/ChapC/C130np7.lean` → only matches the status
  paragraph's own prose ("Zero `sorry`; no new axiom; no `unsafe`"); no live `sorry`,
  no new `axiom` declaration, no `unsafe` anywhere.
* No `SplitNodePointSource`/`FGMNSourceData`/`S2SourceFrontier` instance is assembled here
  (per plan scope, FD-0/SG-0's job) — only the one field's concrete inhabitant, as briefed.
* 21 declarations, 21 `#print axioms` lines, one-to-one (checked by name).

## Verification

From `leanfinal/`:
```
lake env lean Uniformity/ChapC/C130np7.lean
```
Exit 0, **zero errors, zero warnings**, zero `sorry`. All 21 `#print axioms` lines print
exactly `[propext, Classical.choice, Quot.sound]` (Lean-core only; no `sorryAx`).
```
lake build Uniformity.ChapC.C130np7
```
Build completed successfully (8701 jobs) — olean available for downstream consumers
(FD-0/SG-0's later `SplitNodePointSource` assembly).

`git status`: only `leanfinal/Uniformity/ChapC/C130np7.lean` modified (untracked new file);
no other unit's file touched; no commit made (per brief).
