# Verdict A0G1 — uniform-`a0` campaign openers: `A0G-Z` and `A0G-RP`

**Date:** 2026-08-28
**Source of truth:** `docs/in-progress/A0_GENERAL_2026-08-28.md` §6, rows `A0G-Z`/`A0G-RP`.
**Target file:** `leanfinal/Uniformity/ChapI/IFCG0.lean` (new; header `[A0G1 2026-08-28]`).
**Verification:** per-file only, `cd leanfinal && lake env lean Uniformity/ChapI/IFCG0.lean`
(never a bare `lake build`, per the unit's discipline). Final full run: zero errors, zero
warnings, zero `sorry`. No git operation performed; no landed/leanspec file touched;
`C136e1.lean` untouched (belongs to another unit).

## Node A0G-Z — the degree-zero slice: **CLOSED**

Statement landed exactly as specced: `decidedSliceAt_zero : Uniformity.Density.DecidedSliceAt 0`
(`IFCG0.lean:92`), no positivity hypothesis on `σ` anywhere in the proof.

Proof route, from the definitions (not by citing any prior degree-0 theorem — none existed;
the exploration pass confirmed `typeOf_one` and any degree-0 lemma were entirely absent from
the repo before this unit):

* `monicPoly_finZero` (`IFCG0.lean:71`): for `a : Fin 0 → O`, `monicPoly a = 1` — the sum over
  the empty index type `Fin 0` vanishes regardless of `a`'s (nonexistent) values. Holds for
  every `a`, not just "the" unique one, so no `Unique (Fin 0 → O)` instance is needed.
* `typeOf_one` (`IFCG0.lean:82`): `typeOf (1 : Polynomial O) = ⟨0⟩` (the empty multiset) — a
  monic factorization of the unit `1` must be the empty multiset (`Multiset.prod_zero`),
  since a nonempty one would force an irreducible (non-unit) factor to divide a unit.
* `decidedSliceAt_zero` (`IFCG0.lean:92`) then case-splits on `σ = ⟨0⟩`:
  - **`σ = ⟨0⟩`** (the actual type): `DecidedAt` holds at *every* level-`N` class unconditionally
    (the conclusion `typeOf (monicPoly a) = σ` reduces to `typeOf 1 = ⟨0⟩`, true regardless of
    the hypothesis), so `decidedSet = Set.univ`, `decidedCount = q^0 = 1` (`Nat.card_univ` +
    `card_coeff`), `decidedSeq ≡ 1`, `decidedDensity = ⨆_N 1 = 1` (`ciSup_const`). Value **`1/1`**.
  - **`σ ≠ ⟨0⟩`** (everything else, including every malformed label): `DecidedAt` is false at
    every class (any witnessing `a` would force `typeOf 1 = σ`, contradiction, via
    `proj_surjective`), so `decidedSet = ∅`, `decidedCount = 0`, `decidedSeq ≡ 0`,
    `decidedDensity = 0`. Value **`0/1`**.

The empty-vs-malformed distinction the gate demands is witnessed concretely
(`IFCG0.lean:151–158`): `⟨{(0, 5)}⟩` is a **nonempty** multiset with `.degree = 0`
(`FactorizationType.degree` has no positivity guard on its `(e, f)` pairs — this is exactly the
"malformed degree-zero label" the blueprint warns about), and it is *provably distinct* from
`⟨0⟩` (`FactorizationType.ext`-style: their `.data` multisets differ). Both fall on the `σ ≠ ⟨0⟩`
branch of `decidedSliceAt_zero` and get density `0/1`, same as any other non-actual type.

`#print axioms`: `monicPoly_finZero`, `typeOf_one`, `decidedSliceAt_zero` — all
`[propext, Classical.choice, Quot.sound]` only. Size: ~100 source lines (§1 of the file).

## Node A0G-RP — finite residue-divisor patterns: **CLOSED**

`ResiduePattern n` (`IFCG0.lean:288`) is realized as `{σ : FactorizationType //
σ ∈ residuePatternFinset n}` — literally a constrained `FactorizationType` (reusing its
`data : Multiset (ℕ × ℕ)` carrier, the blueprint's named input), where `residuePatternFinset n`
is a genuine `Finset` (not a `Set`) built via the same Sigma-of-`Sym` finiteness technique
`IFC6.exists_uniform_coveringMenu` uses for its covering menu — cited there as precedent for
the *technique only*; the object is different (§4.1's residue-divisor layer, prior to any
Newton–Okutsu engine, versus IFC6's `typeOf`-image output menu).

**Symbolic (all-`n`) finiteness/completeness**, the gate's central demand:
`mem_residuePatternFinset_iff` (`IFCG0.lean:228`) proves, for every `n` and every `σ` at once
(no case split on `n`):
```
σ ∈ residuePatternFinset n ↔ σ.degree = n ∧ ∀ p ∈ σ.data, 1 ≤ p.1 ∧ 1 ≤ p.2
```
i.e. `residuePatternFinset n` contains **every** `FactorizationType` meeting the blueprint's
`(δ, m)`, `δ, m ≥ 1`, `Σ δ·m = n` pattern constraints, not merely a sample. The forward
direction is a direct Sigma-element decode; the reverse direction bounds every pair's
coordinates and the multiset's cardinality by `n` (`Multiset.single_le_sum`,
`Multiset.card_nsmul_le_sum` — the same two lemmas IFC6's own completeness argument uses) and
then builds the Sigma witness via `Multiset.attach` + `Multiset.map_map`. `ResiduePattern.data`,
`.sum_eq`, `.pos` (`IFCG0.lean:296–304`) expose the multiset, the sum law, and the positivity
directly off this theorem. `Fintype (ResiduePattern n)` and `DecidableEq (ResiduePattern n)`
(`IFCG0.lean:290–293`) are immediate from the ambient `Finset` coercion — no separate
combinatorial argument needed once the `Finset` exists.

**The `n ≤ 6` enumeration check.** Two independent computational routes, cross-checked against
a third, hand-derived one:

1. `rpCount n` (`IFCG0.lean:218`) — the *official* count, defined via the exact same
   `Sym`-grid/`Finset.filter` object the completeness theorem characterizes (bridged by
   `residuePatternFinset_card_eq : (residuePatternFinset n).card = rpCount n`, via
   `Finset.card_image_of_injective` + `rpEmbed_injective`). This is tractable to *run* only for
   small `n`: `#eval rpCount 5` alone did not return within 150s (mathlib's generic
   `Sym`/`Fintype`/`Finset.univ` machinery is built for proof, not computation) — recorded
   honestly in the file's comments (`IFCG0.lean:318–325`) rather than papered over.
   - `#eval rpCount 0..4` → **`1, 1, 3, 5, 11`**.
2. `rpCountFast n` (`IFCG0.lean:349`) — a hand-written, genuinely fast generator
   (`rpCandidates`/`rpGen`, `partial def`, never touching `Sym`/`Sigma`/`Finset.univ`, purely a
   combinations-with-repetition recursion over the same `(δ, m)` alphabet) used *only* for this
   regression check, never cited by `mem_residuePatternFinset_iff` or any proof.
   - `#eval rpCountFast 0..6` → **`1, 1, 3, 5, 11, 17, 34`**.
3. Independent hand computation (generating-function `∏_w (1 - x^w)^{-τ(w)}`, `τ` = divisor
   count, expanded by partition-of-`n`/stars-and-bars, done before writing any Lean): predicted
   **`1, 1, 3, 5, 11, 17, 34`** for `n = 0, …, 6`.

All three agree exactly on the overlap (`n ≤ 4`: `rpCount` = `rpCountFast` = hand count), and
`rpCountFast` extends the agreement through `n = 6` against the hand-derived sequence. `n = 2`
(3) and `n = 3` (5) match the landed cubic bank's five-type enumeration
(`IFC6.CubicValueLaw` etc.); `n = 4` (11) matches the blueprint §8 quartic table's eleven
residue genres exactly.

`#print axioms`: `rpEmbed_degree`, `rpEmbed_injective`, `mem_residuePatternFinset_iff`,
`residuePatternFinset_card_eq`, `ResiduePattern.sum_eq`, `ResiduePattern.pos` — all
`[propext, Classical.choice, Quot.sound]` only. Size: ~260 source lines (§2 of the file).
Neither node cites `C33Cite.exists_dvDissection` or any other axiom; the file touches no
Okutsu–Montes/dv machinery at all (by design — both nodes are purely arithmetic/combinatorial,
per the blueprint's own description of this layer).

## Full-file status

`leanfinal/Uniformity/ChapI/IFCG0.lean`, 373 lines. `lake env lean` final run: zero errors,
zero warnings, zero `sorry`. Nine `#print axioms` checks in the footer, all exactly
`{propext, Classical.choice, Quot.sound}`. Both nodes' exit conditions (per the blueprint's §6
table) are met:

* **A0G-Z gate** — per-file Lean ✓; values literally `1/1` or `0/1` ✓; no positivity
  assumption ✓.
* **A0G-RP gate** — enumerated through `n = 6` ✓; finiteness proved symbolically (the
  `Fintype`/completeness argument is uniform in `n`, no numeral case-split) ✓, not by the
  examples (the `n ≤ 6` `#eval`s are a *regression check* on top of the symbolic theorem, not
  a substitute for it) ✓.

Both nodes are Lean-core only, as required — neither touches the C.33 dissection cite.

## What this does *not* close

This unit closes exactly the two named opener nodes. It does **not** touch `A0G-GC` (the
finite genre cover — the blueprint's stop-line, still fully open), `A0G-FF`/`A0G-CV`/`A0G-PD`/
`A0G-NP`/`A0G-HE`/`A0G-CH`/`A0G-RW`/`A0G-RS`/`A0G-FP`/`A0G-CL`/`A0G-AS`/`A0G-DS`, or the
capstone `A0G-ALL`. `ResiduePattern n` is the blueprint's *first layer only* (§4.1); nothing
here classifies what happens *inside* one cluster (§4.2), which is where the real
mathematical risk (`A0G-GC`) lives.
