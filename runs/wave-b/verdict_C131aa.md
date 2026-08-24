# Unit C131aa verdict

## Per-node verdict

| node | verdict | declarations |
|---|---|---|
| C.131aa′ | LANDED | `Uniformity.Density.Tower.isTestKey_isDvPure` |
| C.131ab′ | LANDED | `Uniformity.Density.Tower.dvResPoly_testKey` |

Both declarations are in `leanfinal/Uniformity/ChapC/C131aa.lean`.  The file also proves the
private local calculations needed by the nodes: the exact test-key `dvSupp`, the height-zero
read of the monic top digit, and the zero-block read.  It contains no `sorry`, new axiom, or
`unsafe` declaration.  The printed axiom footprints of both public theorems are Lean core only
(`propext`, `Classical.choice`, `Quot.sound`).

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C131aa.lean
```

Result: exit code 0.

## Repository note

Commit creation was attempted twice for the compiling skeleton and once for the completed
increment.  The environment exposes `.git` read-only, so every attempt failed while creating
`.git/index.lock` with `Read-only file system`; the two deliverable files themselves are present
in the writable workspace.
