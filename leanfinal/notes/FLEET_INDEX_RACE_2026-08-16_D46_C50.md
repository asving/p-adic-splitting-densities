# Forensics: shared-index race at commit `763a1427` (chapter-D wave-2 bundle 3)

Filed by the chapter-D wave-2 bundle-3 transcription agent (D.35 / D.46 / D.59).
**No file content was lost or altered.** One commit's tree contains one more file than
its message names.

## What happened

`763a1427` — message `BP:D.46: CertFrame — T4's certificate frame (the §7 schema)` —
adds **two** files:

| path | whose |
|---|---|
| `leanfinal/Uniformity/ChapD/D46.lean` | this agent's (D.46) |
| `leanfinal/Uniformity/ChapC/C50.lean` | the chapter-C **C.50** agent's |

Mechanism: the working tree and the git index are shared across the fleet. This agent
ran `git status --short` (C50.lean was untracked, `??`), then `git add <its own file>`
— correctly scoped — and then a bare `git commit`. In the gap the C.50 agent staged
`C50.lean` into the SHARED index, and the bare `git commit` committed the whole index.
This is the same failure as the one recorded in `3ab7ff1a` (`8481fa52` sweeping
`C17.lean`); the scoped `git add` does not prevent it, because the race is on `commit`,
not on `add`.

## Disposition

* **C.50 IS landed.** `leanfinal/Uniformity/ChapC/C50.lean` (198 lines, three public
  declarations `slotOffset` / `gridWeight` / `E₂_gt_xfloor` with its own `AxCheck`
  block) is in `763a1427` intact and byte-unchanged; nothing was truncated or rewritten.
  If the C.50 agent's own commit reports an empty tree change, that commit is its
  record and this note is its provenance.
* **History is NOT rewritten** (standing fleet rule). `763a1427` stands as-is.
* The D.35 (`be92a501`) and D.59 (`cb65f701`) commits of this bundle are clean —
  one file each.

## The fix for the next agent

`git add <path>` is not enough. Commit with an explicit pathspec, which ignores the
index for every other file:

```
git add leanfinal/Uniformity/ChapX/Xnn.lean
git commit -F <msg> -- leanfinal/Uniformity/ChapX/Xnn.lean
```

This note itself was committed that way.
