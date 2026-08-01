# H2-U10 Codex diff-gate confirmation (2026-08-05 window execution)

Charge: confirm (a) statement fence held (diff purely additive, no existing declaration changed) and (b) the BLOCKED verdict — PROBE F-4 refutes the single clause both signed-off restatement routes preserve. Prompt archived at /tmp/openmath/h2u10_prompt.txt (10.3 KB: §2.3 package verbatim + sign-off + carrier/ConsF facts + full applied diff + compile status).

```
The statement fence held: every added line is a comment, new definition, new theorem, or new `#print axioms` command. No existing declaration was altered, and the probe file is not imported elsewhere.

The refutation is valid:

- `duplicateEHist.continuingPart.nodes = []`, so `ConsF`’s node-reading obligation is vacuous.
- `emptyDataDup.rootOrder = duplicateEHist.a0 = 1`, satisfying the remaining `ConsF` obligation.
- `noneReaderDup.side 0 = none`, while `duplicateEHist.nodes[0]? = some probeNode`.
- Therefore the preserved `childDetermined` clause would demand an `S` with `none = some S`, an impossibility.
- Both signed-off routes preserve this clause under the landed III-U3b consumption shape. Avoiding the counterexample would require an additional guard or carrier restriction beyond the signed-off envelope.

The core-only axiom footprint and successful compilation support the evidence; no fake axiom, contradiction, or vacuous proof was introduced. BLOCKED is mathematically correct.

VERDICT: CONFIRMED
```
