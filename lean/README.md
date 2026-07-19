# Lean formalization (`LeanUrat`)

Lean 4 (`v4.31.0`) / mathlib (`v4.31.0`). Formalizes the uniform-rationality + palindromy
theorem for projective *p*-adic factorization densities, including the wild primes.

**The authoritative statement of what is proved, on what it rests, and the module ↔
math-proof map is [`../docs/PROJECT_STATE.md`](../docs/PROJECT_STATE.md).** The trusted-axiom
audit is [`../docs/AXIOM_FAITHFULNESS.md`](../docs/AXIOM_FAITHFULNESS.md); the standing
faithfulness re-audit log is [`notes/SEMANTIC_AUDIT_LOG.md`](notes/SEMANTIC_AUDIT_LOG.md).

## Build

```
lake exe cache get        # prebuilt mathlib oleans (large download)
lake build                # build the whole library
```

Reproduce the machine-checked axiom footprint of every capstone (the honesty deliverable):

```
lake build LeanUrat.AxChk_baseline
```

This runs `#print axioms` on the capstones and load-bearing lemmas; that output is the ground
truth for the trusted base.

> **Environmental caveat.** On a heavily loaded NFS-backed node, `lake build` has been
> observed to hang at the *final-job commit* step (the worker `lean` exits 0 but lake does
> not return). This is an environmental I/O issue, not a code error: every module compiles
> green via `lake env lean`, and `AxChk_baseline` elaborates all declarations with exit 0.

## Layout

- `LeanUrat/` — the ~117 modules. `Goal.lean` holds the capstones (`goal_theorem`,
  `goal_theorem_montes`, `goal_theorem_via_montes`); `L3/L4/L5fix/L6M4/L7/M1/R1/Witness`
  mirror §§3–13 of the math-language proof (`../docs/HUMAN_PROOF.md`); `PadicMeasure.lean`
  is the measure route + the Denef cell-recursion axiom; `OM/` is the Okutsu–Montes
  classifier subsystem (the wild-prime engine); `AxChk_baseline.lean` is the footprint census.
- `quarantine/` — retired dead-end modules, kept as documented negative results.
- `notes/SEMANTIC_AUDIT_LOG.md` — the standing semantic-guardian audit log.

## `sorry` status

Exactly **one** `sorry` in the tree: `OM/Classifier.npVertices_stable_of_hull_preserved`
(a Newton-polygon hull-invariance helper), which is **off the capstone path** — consumed only
by an off-capstone reduce-stability lemma, never by any capstone. Every capstone is
`sorry`-free.
