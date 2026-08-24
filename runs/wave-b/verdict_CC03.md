# CC-3 (terminal maps) — verdict: LANDED

Unit CC03, chain-carrier node CC-3 (`docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md` §10).
Deliverable: `leanfinal/Uniformity/ChapC/C130tr.lean` (new file; nothing else touched).

**Verdict: LANDED** — canonical `TerminalReceiver` at `Kt = W.fld r` constructed, step square
and injectivity proved, zero `sorry`, no new axiom, all 18 declarations Lean-core-only
(`{propext, Classical.choice, Quot.sound}` or none).

## Declarations (namespace `Uniformity.Density.Tower`, mostly under `DeepTower`)

- `instDecidableStageLive` — `Decidable (StageLive r j)` (axiom-free).
- `DeepTower.stepEmb` — one-rung embedding `K_j →+* K_{j+1}`:
  `(W.step j _ _).symm.toRingHom.comp (AdjoinRoot.of (W.ψ j))`, byte-identical to
  `levelHom_step`'s inner composite. + `stepEmb_injective`.
- `DeepTower.climbTo` — fuel recursion (`j + d = r`, codomain pinned at `r`, no index casts in
  the recursive case; base-case cast reduces by proof irrelevance). + `climbTo_congr`
  (fuel proof-irrelevance), `climbTo_injective`.
- `DeepTower.towerHom` — canonical live level map `K_j →+* K_r` (= `climbTo (r - j)`).
  + `towerHom_terminal` (identity at `j = r`), **`towerHom_step`** (THE step square),
  `towerHom_injective`.
- `DeepTower.receiverLevelHom` + `receiverLevelHom_live` (junk never read on live range).
- **`DeepTower.terminalReceiver`** — the CC-3 receiver: `topEquiv := RingEquiv.refl`,
  level maps = step composites, `levelHom_step` discharged by `towerHom_step`.
  + `terminalReceiver_topEquiv` (rfl), `terminalReceiver_levelHom_live`.
- `TerminalReceiver.levelHom_injective` — EVERY level map of ANY receiver is injective
  (ring hom out of a field; no liveness hypothesis), + specialization
  `DeepTower.terminalReceiver_levelHom_injective`.
- `DeepTower.terminalReceiver_nonempty_iff` — exactness certificate (see below).

## Honest finding (design-relevant, not a weakening)

`TerminalReceiver.levelHom` is total over `j : ℕ`, but C.83's telescope pins `fld j` only on
the live range; off it (`j = 0` under a positive tower, and `j > r`) the hom type
`W.fld j →+* W.fld r` can be EMPTY (junk `fld j = ℚ` vs. positive-characteristic `fld r`).
So the canonical receiver takes the exact missing datum as an argument:
`junk : ∀ j, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r)` (the `j ≠ r` guard exempts the
degenerate `r = 0` terminal, filled by the identity). `terminalReceiver_nonempty_iff` PROVES
receiver existence at `Kt = W.fld r` is equivalent to junk-level fillability — the argument is
the obstruction, verbatim. Supply note for CC-17: C.97's `s2Witness` has constant
`fld := fun _ => stageField …`, so `fun _ _ _ => RingHom.id _` fills `junk` there trivially.

## Verification

```
cd leanfinal && lake env lean Uniformity/ChapC/C130tr.lean
```

Output = exactly the 18 `#print axioms` lines, all Lean-core only; no errors, no warnings,
no `sorry`. (Defs are `noncomputable` — forced by `AdjoinRoot.instCommRing`, as elsewhere in
the repo, e.g. `s2Witness`.)
