# Verdict — DEC4R chapter-C chain-blockers plan

**Verdict: SUPPLY delivered; probe additions LANDED; production blockers remain BLOCKED on
named mechanisms.** No signed spec, landed `Uniformity/` file, roll-up, or unrelated file was
edited.

## Mandatory first action and final verification

From `leanfinal/`, the inherited 181-line file was run before any corpus inspection:

```text
lake env lean scratch/DEC4_check.lean
# exit 0
```

It printed only `[propext, Classical.choice, Quot.sound]` for all six inherited declarations.
After extending the file to 246 lines, the same command again exits 0 and all ten printed
declarations have exactly the same Lean-core footprint
(`leanfinal/scratch/DEC4_check.lean:227-246`). Zero `sorry`, zero `axiom`, zero `sorryAx`.

## LANDED — elaboration/proof probes

The inherited F2-1 result is confirmed: B53a's generic quotient equivalence and B53c's generic
determinant–length dictionary prove equality of the two norm valuations
(`leanfinal/scratch/DEC4_check.lean:42-66`; landed inputs at
`leanfinal/Uniformity/ChapB/B53a.lean:90-101` and
`leanfinal/Uniformity/ChapB/B53c.lean:114-140`). This bridge is assembly, not new mathematics.

F2-2's inherited prose was too strong. Its original theorem transfers a nonzero scalar's
principal-ideal membership from the `AdjoinRoot φ` quotient and thereby proves the opposite norm
nonzero; it does not prove a bare norm-nonzero implication
(`leanfinal/scratch/DEC4_check.lean:77-100`). DEC4R added and proved the reverse orientation
(`leanfinal/scratch/DEC4_check.lean:102-131`). The plan now uses the honest contract: ramified
exactness supplies scalar membership, quotient symmetry transfers it.

F1-1 still confirms that `BlockFrontier` projects exactly the four block reads via the already
landed packaging theorem (`leanfinal/scratch/DEC4_check.lean:133-145`). F3-1 still confirms both
RB3 signed closures elaborate (`leanfinal/scratch/DEC4_check.lean:147-188`).

DEC4R strengthened F3-2: besides the inherited `dev` decomposition, new Lean proofs establish
`biRead_add`, monicity of `biRead F (composedKey T)`, and `shadowDev_add`
(`leanfinal/scratch/DEC4_check.lean:190-226`). Therefore RB3's alleged additivity gap is a small
API landing. The only genuinely new `shadow_persistence` mechanism is the upward
coefficient-budget-to-discrepancy-height bridge.

## SUPPLY — enactment plan

Delivered `docs/in-progress/BLOCKERS_PLAN_2026-08-26.md` with per-node statements, named landed
inputs, mechanisms, sizing, exit gates, dependency order, and the required fence.

- **C.35:** eight honest `_of_frontier` rows are separated from the root construction. The root
  is a new one-slope `dv`-graded residual-Bézout Hensel existence/uniqueness engine; the declared
  `fgmn_dv_exact_mul` cite certifies products after factors exist but cannot construct them
  (`leanfinal/Uniformity/ChapC/C66b.lean:85-107`). The plan preserves the indispensable degree
  rider refuted without maximal provenance (`leanfinal/Uniformity/ChapC/C35b.lean:375-390`).
- **C.27:** quotient symmetry is scheduled first as probe-complete. Ramified level-1 exactness is
  honestly priced as a new completion-free weighted-determinant/no-cancellation mechanism
  (285–485 lines), followed by the missing frame-key read and C.59/C.61 wrappers. Arbitrary-`C`
  exactness is separately priced above factor-label heredity, as required by the landed C27
  diagnosis (`leanfinal/Uniformity/ChapC/C27x.lean:77-82`).
- **RB3:** `refine_invariants` is decomposed into `n2Exp` arithmetic, exact lift degree/read
  lemmas, corrected-key stability, and a wrapper. `shadow_persistence` is decomposed into the
  probe-complete linearity API, the new upward height bridge, and strict-add assembly. Both unclear
  mechanisms receive examples-first Python certificate specifications before Lean work.

Ordering recommendation: land the already-proved norm bridge and shadow linearity first; run the
RB3 certificates and close RB3; build ramified level-1 exactness and close the key read; then build
the larger one-slope Hensel engine, discharge `BlockFrontier`, and remove the eight conditional
riders. Full arbitrary-`C` C.27 comes last.

## BLOCKED — exact remaining mechanisms

1. `dv`-graded one-slope residual-primary Hensel existence and uniqueness (the C.34/C.35 root).
2. Completion-free ramified norm exactness at `AdjoinRoot F.key`, including initial-determinant
   noncancellation.
3. Corrected-key refinement stability for `k2DigitLift` after its exact degree/read companions.
4. The upward `hbudget` → shadow-discrepancy `dv2Hgt ≥ theta+1` bridge.
5. Full arbitrary-`C` C.27 additionally needs factor-label heredity and order-2 no-cancellation.

Held and not planned: C.100/OPEN-EVAL-ISO; C.102 and `one_shape`'s `htie`/OPEN-LETTERS;
`peel_row_law`/undesigned `PeelLeg`; and μ₃ `hprev`/`hcop` satisfiability. This fence is the one
recorded in PROJECT_STATE (`docs/PROJECT_STATE.md:95-99`).
