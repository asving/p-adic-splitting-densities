# RESCHEDULE record — NODE C.56a (`k2DigitLift`), Chapter-C fleet wave 6, agent 2

**Date.** 2026-08-16. **Verdict.** BLOCKED — dependency not landed. **Not weakened, not
attempted with a stand-in.**

## The block

C.56a's A-C.1-signed SIGNATURE (`blueprint/CHAP-C_tower_grammar.md` §7, lines 3455–3512;
twin `leanspec/Leanspec/ChapC.lean:1827-1855`) has body

```lean
noncomputable def k2DigitLift … (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T))
    (m : ℕ) : Polynomial O :=
  ∑ r ∈ Finset.range F.f₁, ∑ t ∈ Finset.range T.f₂,
    Polynomial.C (resLift (F.stageCoord H₀ hpin (k2Coord T s t) r) * π ^ …) * …
```

`KeyFrame.stageCoord` — the `F_Q`-digit read of a stage-field element in the letter basis — is
**NODE C.14a**'s declaration (blueprint clause (iv), lines 1145–1152), and C.14a has no file in
`leanfinal/Uniformity/ChapC/`. Verified: `grep -rn stageCoord leanfinal/` returns nothing;
there is no `C14*.lean`.

`resLift` (the choice-section of the residue map) is likewise C.14a's — blueprint states it is
"a private helper of this file". That one is NOT the blocker on its own: `private` does not
export, so C.56a would carry its own copy under the standing D9 pattern (as C.04/C.12/C.19/C.22/
C.44 each carry `isKey_X`). The blocker is the **public** `stageCoord`.

## What IS landed (so the reschedule is a one-dependency wait)

Every other SIGNATURE-referenced item of C.56a is in place:

| item | node | file |
| --- | --- | --- |
| `KeyFrame` (`e₁`, `f₁`, `h`, `key`, `hne`) | C.01 | `C01.lean` |
| `KeyFrame.frameRes`, `KeyFrame.stageField` | C.03 | `C03.lean` |
| `KeyFrame.slotIdx` | C.15 | `C15.lean` |
| `TowerDatum` (`u₂`, `e₂`, `f₂`, `D₂`) | C.42 | `C42.lean` |
| `towerLabel` | C.44 | `C44.lean` |
| `towerSolve` | C.83 | `C83.lean` |

So `k2Coord` and `n2Exp` are both writable today; only the `stageCoord` call inside
`k2DigitLift` is not.

## Disposition

**RESCHEDULE C.56a behind C.14a.** No partial landing was committed: splitting off `k2Coord` +
`n2Exp` alone would put two orphan defs in the tree whose only consumer is the blocked one, and
the blueprint signs C.56a as a single three-declaration node (the A-7 SCC repair already split
it once out of C.56 — splitting again is a statement-level decision this agent does not own).

Downstream also waiting on the same landing: C.56 (`refine_invariants`, `refine_kills`),
C.84/C.85 (both consume `k2DigitLift` at heights `(f'−t)·u'`), and C.62's
`∑ t ∈ Finset.range f', k2DigitLift T (c t) …` display (`leanspec/Leanspec/ChapC.lean:2180`).
