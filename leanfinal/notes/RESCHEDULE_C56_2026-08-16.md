# RESCHEDULE record — NODE C.56 (`refine_invariants`, `refine_kills`), Chapter-C fleet wave 8, agent 1

**Date.** 2026-08-16. **Verdict.** BLOCKED — SIGNATURE-referenced definition not landed.
**Pre-check only; not attempted, not weakened, no partial file committed.**

Context: this agent's assigned node **C.56a LANDED** (`leanfinal/Uniformity/ChapC/C56a.lean`,
this session) and the brief said to continue to C.56 *only if* all its dependencies were landed.
They are not.

## The block

C.56's A-C.1-signed SIGNATURE (`blueprint/CHAP-C_tower_grammar.md` §8; twin
`leanspec/Leanspec/ChapC.lean:1857-1918`) names `composedKey T` — the composed key `Φ₂` — in
**every clause of both theorems**:

```lean
axiom refine_invariants … (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty)
    (hres : dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
      = (Polynomial.X - Polynomial.C s) ^ μ₂) :
    (composedKey T - k2DigitLift T s lam).Monic ∧ …
```

`composedKey` is **NODE C.43**'s declaration (blueprint line 2784). There is no `C43.lean` in
`leanfinal/Uniformity/ChapC/`, and `grep -rn composedKey leanfinal/ --include=*.lean` returns only
prose mentions in C.14a, C.44 and C.45 — no `def`. **RESCHEDULE: needs `composedKey` (C.43).**

## Second, independent block on clause (ii) at general `μ₂`

Even once C.43 lands, `refine_kills` is only half-supplied. The blueprint's own STATEMENT says the
`μ₂ = 2` case is pointwise-elementary but "at general `μ₂` layer 1 consumes the composed graded
frame: **DEPENDS on §9's C.85 (GENTOW5's S1.5 graded frame — the retirement of GENTOW-BOX-1)**,
and fires only after it." **C.85 has no file either** (no `C85.lean`). So C.56 needs *two*
landings ahead of it, not one; scheduling it on C.43 alone would strand `refine_kills`.

## What IS landed (so the wait is exactly C.43 + C.85)

| item | node | file |
| --- | --- | --- |
| `k2DigitLift`, `k2Coord`, `n2Exp` | **C.56a** | `C56a.lean` (this session) |
| `dv2SideSet`, `dv2ResPoly` | C.38a | `C38a.lean` |
| `dv2Pin` | C.11 | `C11.lean` |
| `IsTestKey` | C.13 | `C13.lean` |
| `towerLocus` | C.51 | `C51.lean` |
| `TowerDatum` (`E₂`, `D₂`) · `levelDatum` | C.42 · C.44 | `C42.lean` · `C44.lean` |
| `KeyFrame.Pin`, `stageCoord`, `resLift` | C.14a | `C14a.lean` |

## Also unblocked-but-not-ready by C.56a's landing

C.84 (`DeepTower.towerLift`, the `i = 2` reconciliation to `k2DigitLift`) and C.62's
`∑ t ∈ Finset.range f', k2DigitLift T (c t) …` display now have their `k2DigitLift`. Each still
needs its own pre-check — C.84 in particular reads `DeepTower.towerNorm` (C.83, landed) *and*
`composedKey`-adjacent key data, so it is not automatically clear.
