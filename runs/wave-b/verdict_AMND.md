# Verdict AMND — signed consumer amendments A-C.17--A-C.20

**Date:** 2026-08-26  
**Unit:** AMND  
**Overall:** **LANDED** — all four recorded amendments and their audited landed consumers
re-elaborate.  No amendment is `BLOCKED-BECAUSE`.

## Amendment disposition

| amendment | status | enacted repair | landed evidence / consumer disposition |
|---|---|---|---|
| **A-C.17** | **LANDED** | C.99 and both C.89 paths now take `hprev : 2 ≤ f' → I.PrevGrade u'`. | `C99r.gentow2_Bpp` splits the cancellation-only `f'=1` case from the graded-multiplication range; `C107ac14.gentow5w_two` and `gentow5w_one_shape_of_letter_tie` consume the fenced premise.  The signed comment cites `MU3_CAMPAIGN_2026-08-26.md` §3 and `scratch/DEC3_probe.lean`'s `ratio_power_one`. |
| **A-C.18** | **LANDED** | Added `FGMNCalculus.chainNormBelow I r k := I.chainNorm (r-1) k`; re-indexed `thetaRatio` and the coordinated C.99--C.101, C.89, and C.90 consumers to the below-current normalizer. | `C130pk`, `C99r`, `C107gt5`, and `C107ac14` elaborate; `AMNDCheck.chainNormBelow_succ` pins the successor-index equation.  This preserves the strict degree premise rather than weakening it. |
| **A-C.19** | **LANDED** | Added `hdeg : g.natDegree < μ₂ * T.D₂` to signed `shadow_persistence`, immediately before `hbudget`. | The only landed consumer-shaped closure, `DEC4Check.ShadowPersistenceStatement`, and `AMNDCheck.ShadowPersistenceAmended` elaborate with the fence.  No landed theorem named `shadow_persistence` existed to repair. |
| **A-C.20** | **LANDED** | Pinned every load-bearing C.34 labelled block and C.35 selector/frontier maximality candidate to `HasLabel L fS ∧ (F.e₁*F.f₁) ∣ fS.natDegree`. | The current `blockFactor`, `BlockFrontier`, `exists_dv_residual_dissection_of_frontier`, and `blockFactor_spec_of_frontier` use the pinned stratum.  Historical refutations retain the old object explicitly as `blockFactorLeaky`/`mult₂Leaky`; C35b itself is verbatim untouched.  C48's legitimate degree-divisible consumer supplies the new pin. |

### Named OPEN row required by A-C.18

| row | status | statement |
|---|---|---|
| **OPEN-NORM-BASE** | **OPEN (non-blocking for the charged positive-depth consumers)** | The blueprint pins `chainNormBelow (i+1) = chainNorm i`, but does not independently pin a source-level semantic normalizer below depth `0`.  The enacted total definition uses natural subtraction, so `chainNormBelow 0 = chainNorm 0`; no additional base theorem or guessed statement was introduced. |

## Files touched

Signed and records:

- `leanspec/Leanspec/ChapC.lean`
- `docs/REVIEW_QUEUE_2026-08-26.md` (Tier-2 rows A-C.17--A-C.20)
- `runs/wave-b/verdict_AMND.md`

Landed twins and consumers:

- `leanfinal/Uniformity/ChapC/C130pk.lean`
- `leanfinal/Uniformity/ChapC/C99r.lean`
- `leanfinal/Uniformity/ChapC/C107gt5.lean`
- `leanfinal/Uniformity/ChapC/C107ac14.lean`
- `leanfinal/Uniformity/ChapC/C34.lean`
- `leanfinal/Uniformity/ChapC/C35.lean`
- `leanfinal/Uniformity/ChapC/C48.lean`
- `leanfinal/Uniformity/ChapC/C64.lean`
- `leanfinal/Uniformity/ChapC/C67.lean`
- `leanfinal/Uniformity/ChapC/C80.lean`
- `leanfinal/Uniformity/ChapC/C78adj.lean`

Checks:

- `leanfinal/scratch/DEC4_check.lean`
- `leanfinal/scratch/AMND_check.lean`

`leanfinal/Uniformity/ChapC/C35b.lean` was audited and left unchanged.  No Chapter I file
and no roll-up was edited by AMND.

## Re-elaboration record

Every touched Lean source was checked from its own project with `lake env lean <file>` and
returned exit 0:

- leanspec: `Leanspec/ChapC.lean`;
- leanfinal: `C130pk.lean`, `C99r.lean`, `C107gt5.lean`, `C107ac14.lean`, `C34.lean`,
  `C35.lean`, `C48.lean`, `C64.lean`, `C67.lean`, `C80.lean`, `C78adj.lean`,
  `scratch/DEC4_check.lean`, and `scratch/AMND_check.lean`.

The only diagnostics were pre-existing linter warnings (unused variables/`simp` arguments
and the signed file's overlapping-instance warning).  There were no elaboration errors.
The unchanged active-consumer audit also returned exit 0 for `C35b.lean` (kept verbatim),
`C83.lean`, `C130la.lean`, and the C.99 signature check in `C106m.lean`.

The two cited executable certificates were rerun from the repository root:

- `verification/rb3_bridge_cert.py`: **210 PASS / 0 FAIL**;
- `verification/dv_hensel_cert.py`: **2832 checks / 0 FAIL**.

`git diff --check` also returned exit 0.

## AxChk

The source footers and `scratch/AMND_check.lean` printed the footprints of the amended or
re-proved declarations, including:

- `FGMNCalculus.chainNormBelow`, `FGMNCalculus.thetaRatio`;
- `C99r.gentow2_Bpp`, `gentow2_B_supply`, `gentow2_B`;
- `GENTOW5W`, `C107ac14.gentow5w_two`,
  `gentow5w_one_shape_of_letter_tie`, `gentow5_key_certificate`;
- `exists_dv_residual_dissection_of_frontier`;
- `blockFactorLeaky_eq_of_frontier`, `blockFactor_eq_of_frontier`,
  `blockFactor_spec_of_frontier`;
- the adjusted C48/C64/C67/C80/C78adj consumer declarations;
- `AMNDCheck.chainNormBelow_succ` and `AMNDCheck.ShadowPersistenceAmended`.

Every printed proof/definition footprint was exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `sorry`, and no new leanfinal axiom was introduced.  The amended signed
declarations remain explicit recorded axioms in leanspec, as required by that project's
statement-corpus role.
