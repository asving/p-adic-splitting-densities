# N1 verdict — GC-13 bridge, split row's PARENT (`mixBlock`, `mixIface`)

**Charge:** `docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` §3, node DEC1-N1 — land the
SPLIT row's parent block/interface pair over the landed flat carrier
(`E57pCert.flatCarrier`): `F = X² − 1 = (X + 1)(X − 1)`, one side `(1,1)`, TWO
unit-weight linear classes (labels `1`, `−1`) — the A-E.6 countermodel's interface SHAPE
(`E57pCert.dupBlock`/`dupIface`, `F = X²`) realized at a LEGAL, separable polynomial.
File: `leanfinal/Uniformity/ChapE/E57i1.lean` (new; namespace
`Uniformity.Density.Ladder.E57iCert`, matching sibling `E57i2.lean`).

## Verdict: LANDED

- **`mixBlock : BlockData flatCarrier`** — `Φ = X`, `F = X^2 - 1`, `μ = 2`,
  `A := fun j => if j = 0 then -1 else 0`, `T = 0`. Template `E57pCert.dupBlock`
  (E57p.lean:633–659), field by field, with `hΦdeg` simplified to the `pureBlock` shape
  (`Φ = X`, not `X + 1`). `hkeyfree` Bézout witness `⟨-1, X⟩`
  (`(-1)(X²-1) + X·X = 1`); `hdev` via `show` + `simp` + `ring`; `hA0` via `norm_num`.
- **`mixIface : RungInterface.{0,0,0} flatCarrier mixBlock`** — `sides = {(1,1)}`,
  `len ≡ 2`, `linFac ≡ {(1,1), (-1,1)}`, `hiFac ≡ 0`, `rootCount ≡ 2`, `classCount ≡ 1`,
  `classCountHi ≡ 1`, `W = Unit`. Numeric-law proofs (`hresdeg`, `haccount`, `hnonempty`,
  `hforce`, `hexhaust`, `hlen_sum`, `hside_cop`, `hside_node`) reused verbatim from
  `dupIface` (label-independent).
- Closing `example` — `DEC1Check.N1_target`'s body byte-copied from
  `leanfinal/scratch/DEC1_check.lean:44–49` (anti-drift pin), discharged
  `⟨mixBlock, mixIface, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩` (all ten
  conjuncts computational).

No `sorry`, no new axiom, no `unsafe`. `#print axioms` on both declarations reports only
Lean-core `{propext, Classical.choice, Quot.sound}`.

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapE/E57i1.lean
```

Exit 0, no warnings (unused-simp-arg in `hdev` fixed by dropping the redundant
`[Finset.sum_range_succ]` simp lemma — bare `simp; ring` closes it).

```
'Uniformity.Density.Ladder.E57iCert.mixBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.mixIface' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope note

Only `leanfinal/Uniformity/ChapE/E57i1.lean` written (new file). `E57p.lean`, `leanspec/`,
roll-ups, and sibling node files (`E57i2.lean`, `E57i.lean`, `E57ih.lean`) not touched. No
commit made (per brief).
