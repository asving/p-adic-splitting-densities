# UNIT C — Codex diff-confirmation gate (R-5), archived

Gate run 2026-08-01 (machine clock; the 2026-08-05-dated dispatch), fresh-context
Codex (thread 019fbc42-5164-70b1-b833-2ca94c1ddb78), per the standing
definition-change authority. Input: the (NSF-KEY-RET) R-1/R-2/R-3 spec + M02 §2's
sanctioned-repair text + the recorded ripple enumeration (UNITC_ripple.md) + the
applied diff (`git show dfdb558 -- BridgeD3_treeCarrier.lean BridgeD4_vtLaws.lean
BridgeKernels.lean`; the UnitC hunks of the orchestrator's WIP sweep commit).
Prompt preserved at /tmp/openmath/UNITC_diff_prompt.txt (14,614 bytes); raw
stream at /tmp/openmath/UNITC_diff.jsonl.

## Codex verdict (verbatim)

1. `bridgeTree` gains exactly the sanctioned third conjunct `∧ MovesT.NsFree V`; existing conjuncts and their order are unchanged.
2. `bridgeVt_realizedSelf` is mechanically re-pointed from `T.2.2` to `T.2.2.1`.
3. `bridge_slice_finite` is mechanically re-pointed from `T.2.2` to `T.2.2.1`; its theorem statement is unchanged.
4. `bridgeVt_nsFree` is added exactly as the sanctioned read-off projection, with proof `T.2.2.2`.
5. Header and docstring changes only describe the new carrier clause and its sanctioned drainage semantics.
6. No changes appear to `DefsLedger.lean` or `Defs.lean`; therefore the statement texts of `count_tie`, `canonical_stable`, and `VPSound` remain untouched and are re-scoped solely through the carrier.
7. No other definition or theorem statement in the pasted diff is changed, weakened, strengthened, deleted, or added beyond the expressly sanctioned `bridgeVt_nsFree`.

VERDICT: CONFIRMED
