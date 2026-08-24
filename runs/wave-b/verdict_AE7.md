# Unit AE7 verdict — amendment A-E.7

Date: 2026-08-24

## Applied diff summary

- Added the leanspec-local `ClassIx` and `classWeight` twins immediately before the E.57 target area.
- Added `PartitionLeg` against `LeanspecE.SlotCarrier`, `LeanspecE.BlockData`, and
  `LeanspecE.RungInterface.{uO, uK, uW}`, with the landed field list and docstrings.
- Re-signed `BlockSplitTarget` from `hpart : True` to
  `hpart : Nonempty (PartitionLeg I)` and recorded the A-E.7 landed proof reference.
- Prefixed the `BlockSplitTarget` docstring's historical `**NOT ASSERTED.**` record with the
  A-E.7 execution paragraph. The historical A-E.6 text remains intact below it.
- No declaration outside this E.57 amendment area was changed. No `leanfinal/` file or roll-up
  was changed.

## Field-match audit

The landed and leanspec `PartitionLeg` regions were extracted from the `structure PartitionLeg`
line through the `hthr` field and compared with `diff -u`. The diff was empty. Thus the requested
comment-stripped comparison is empty as well; the stronger comparison including field docstrings
also matches byte-for-byte (modulo the enclosing namespace, which lies outside the extracted
structure region).

Field order on both sides:

1. `cls`
2. `hclsLin`
3. `hclsHi`
4. `blk`
5. `hprod`
6. `hdisj`
7. `hdeg`
8. `hone`
9. `hpureLin`
10. `hpureHi`
11. `hthr`

Added-token audit over the amendment diff found no `sorry`, new `axiom`, or `unsafe`.

## Build result

Command:

```text
cd leanspec && lake build Leanspec.ChapE
```

Result: **PASS** (exit code 0; `Build completed successfully (9240 jobs)`). The output contains
only the file's pre-existing `List.Chain` deprecation warnings at the shifted lines 363 and 1463.
