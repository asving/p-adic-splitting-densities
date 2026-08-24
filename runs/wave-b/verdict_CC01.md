# Verdict CC01 — CC-0 core re-home + CC-1 carrier skeleton (2026-08-24)

## Per-node verdicts

**CC-0: LANDED.** `leanfinal/Uniformity/ChapC/C130a.lean` created; the five declarations
`StageLive`, `GaugeLive`, `DeepLive`, `TerminalReceiver`, `ArisingCore` MOVED there from
`leanfinal/Uniformity/ChapI/I10FreezeV2.lean` — **byte-identical** (docstrings included;
verified by a Python diff of the moved block against `git show HEAD:.../I10FreezeV2.lean`
lines 40–94: exact match), same namespace `Uniformity.Density.Tower`, same
`universe`/`variable` context. `I10FreezeV2.lean` now imports `Uniformity.ChapC.C130a`
(one added import line + a re-home note in the module docstring; no other content changes),
its own copies deleted; `DeepTwistConjunctLive` + the `deepTwistConjunctLive_iff` Iff.rfl
pin stay there untouched (no retargeting needed — same fully-qualified names, now imported).
Its AxCheck section still prints all seven footprints, unchanged
(live ranges: none; `TerminalReceiver`/`ArisingCore`: Lean core; Ladder pair: propext+Quot.sound).
No roll-up file touched.

**CC-1: LANDED.** `leanfinal/Uniformity/ChapC/C130k.lean` created with
`import Uniformity.ChapC.C130f` only (C130a/I10FreezeV2 come transitively; the scratch's
C53b/C80/C97 imports belong to the CC-2 depth-two check and were correctly not needed).
Landed in production namespace `Uniformity.Density.Tower`:

* `KeyChain`, `LaurentNormalizer`, `NodePointSource` — types verified **identical to
  `leanfinal/scratch/U11_carrier_check.lean`** (comment-stripped, whitespace-normalized
  Python diff: exact match on all three); docstrings carry the design doc §4/§9 per-field
  source labels (OPEN-DICT-1/C.130b; EFF.T2.04/.05/.07/.09/.11; EFF.GENTOW5.15/.16/.19,
  S2.1/S2.3; EFF.T1.01–.03; D.07/D.08/D.44; EFF.T3.21; the E.11 `BlockData.T` dictionary
  and the C130B `(2,5,1)` `towerNorm` refutation notes included).
* Live-lint helpers (all proved, no `True` bodies): `stageLive_iff`/`gaugeLive_iff`/
  `deepLive_iff` (Iff.rfl anti-drift pins), `GaugeLive.stageLive`,
  `GaugeLive.stageLive_succ`, `DeepLive.gaugeLive`, `DeepLive.stageLive`,
  `not_stageLive_zero`, `not_gaugeLive_terminal`, `not_stageLive_of_terminal_lt`,
  and `Decidable` instances `instDecidableStageLive/GaugeLive/DeepLive`.
* NOT landed (per CC-1 scope): `FGMNSourceData`/`FGMNSourceLaws` (CC-13),
  `ChainRealization`/packaging (CC-13/16), `RealizedInput` (CC-8), S2 key chain (CC-2).
  No carrier structure instantiated anywhere.
* `#print axioms` for all 16 new declarations at file end: every footprint is
  Lean-core-or-less (structures: propext, Classical.choice, Quot.sound; helpers: at most
  propext, Quot.sound; several axiom-free). No `sorry`, no axiom, no `unsafe`.

## Verification commands and results (all from `leanfinal/`, fresh oleans)

| command | result |
|---|---|
| `lake env lean Uniformity/ChapC/C130a.lean` | exit 0; 5 footprints, Lean-core only |
| `lake env lean Uniformity/ChapI/I10FreezeV2.lean` | exit 0; all 7 footprints unchanged |
| `lake env lean Uniformity/ChapC/C130k.lean` | exit 0; 16 footprints, Lean-core only |
| `lake build Uniformity.ChapI` | green (8710 jobs; sole warning = pre-existing header-linter nit on the import-only roll-up `Uniformity/ChapI.lean`, replayed from cache, untouched) |
| `cd ../leanspec && lake build Leanspec.ChapI` | green (9173 jobs) |
| `lake build Uniformity.ChapC.C130a` / `...C130k` (module builds) | both green |
| regressions: `lake env lean Uniformity/ChapC/C130f.lean`, `lake env lean scratch/U11_carrier_check.lean` | both exit 0 |

## Duplicate-name check output

```
$ rg -n "def StageLive|def GaugeLive|def DeepLive|structure TerminalReceiver|structure ArisingCore" leanfinal/
leanfinal/Uniformity/ChapC/C130a.lean:34:def StageLive (r j : ℕ) : Prop := 1 ≤ j ∧ j ≤ r
leanfinal/Uniformity/ChapC/C130a.lean:37:def GaugeLive (r j : ℕ) : Prop := 1 ≤ j ∧ j < r
leanfinal/Uniformity/ChapC/C130a.lean:40:def DeepLive (r j : ℕ) : Prop := 3 ≤ j ∧ j < r
leanfinal/Uniformity/ChapC/C130a.lean:47:structure TerminalReceiver (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (r : ℕ)
leanfinal/Uniformity/ChapC/C130a.lean:60:structure ArisingCore (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L]
```

Exactly one site each. (`KeyChain`/`LaurentNormalizer`/`NodePointSource` have one production
site each in C130k; the scratch file's copies live in the distinct scratch-only namespace
`...Tower.U11` and are outside the library import graph — scratch still elaborates green.)

## Notes for the orchestrator

* Roll-up wiring for `Uniformity.ChapC.C130a`/`C130k` into `Uniformity/ChapC.lean` is
  yours (not done here, per instructions). Builds are green without it because
  I10FreezeV2 imports C130a directly and C130k was module-built.
* Not committed (per instructions). Files touched: NEW `Uniformity/ChapC/C130a.lean`,
  NEW `Uniformity/ChapC/C130k.lean`, MODIFIED `Uniformity/ChapI/I10FreezeV2.lean`,
  NEW `runs/wave-b/verdict_CC01.md`.
* CC-2 can now promote the scratch `s2DepthTwoKeyChain` against C130k's production
  `KeyChain`; CC-3/4/5/9/13 are unblocked on the C130a/C130k vocabulary.
