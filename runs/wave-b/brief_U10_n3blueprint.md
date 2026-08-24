# Unit U10 — blueprint: formalize the n=3 drainage proof (HYP.08 → DrainageAt 3)

You are a blueprint-conversion unit (high reasoning) in the p-adic-splitting-densities
campaign. Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean
project: `leanfinal/` (mathlib v4.31.0, built; per-file `lake env lean` from `leanfinal/`;
NEVER bare `lake build`).

## Context

Unit U8 delivered a complete mathematical proof of the cubic drainage block:
`docs/in-progress/N3_DRAINAGE_PROOF_2026-08-24.md` — the recurrence
u_N ≤ q^{-N} + q^{-5} u_{N-3} (N ≥ 3), proved uniformly for every complete DVR with
finite residue field (q ≥ 2, including residue characteristic 2 and 3), plus the
Haar-null statement for the infinite undecided locus. This is exactly the missing math
for the chapter-I rows HYP.08 (cubic tail recurrence) and HYP.09 (cubic triple-root
drainage): per `blueprint/CHAP-I_capstone_conditionality.md` (rows ~286–291), the exact
missing Lean statement is H.97's `hrate`:

```
∀ O [bundle], Induction.RateSpecies (residueCard O) 1 1 0 (undecidedSeq O 3)
```

and HYP.09's `DrainageAt 3` then follows via landed H.97 + H.98 step 1
(`RateSpecies ⟹ undecidedSeq → 0 ⟹ UndecidedVanishes`). HYP.04–06 (strong Hensel,
`typeOf` shift/scale invariance) are ALREADY DISCHARGED in Lean (P5 set); HYP.07 is
contracted through B.42+B.58. The remaining gap is the rate, nothing else.

Your job: convert U8's proof into a formalization-trivial node-plan blueprint (the style
of `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §5: one table row per 30–60 min
node, dependencies, plus per-node prose with the proof written out against named landed
lemmas).

## Read (in this order)

1. `docs/PROJECT_STATE.md`.
2. `docs/in-progress/N3_DRAINAGE_PROOF_2026-08-24.md` — the whole proof. Note its §
   distinguishing actual `undecidedSet` drainage from the conservative `hex3U` reader —
   the blueprint must respect chapter G honesty H-1's bridge (the target counts
   `undecidedCount O 3 N`, not `hex3U`).
3. The landed Lean vocabulary the nodes must be typed against (rg each in
   `leanfinal/Uniformity/`): `Induction.RateSpecies`, `undecidedSeq`, `undecidedCount`,
   `DrainageAt`, `UndecidedVanishes`, H.97/H.98 (`rg -n "H\.97|H97|hrate" leanfinal/
   blueprint/CHAP-H*.md`), the P5 set (`strongHensel`, `strongHensel_addVal`,
   `typeOf_shift`, `typeOf_scaleRoots`, `typeOf_scale`), `drainage_three_of_triple`
   (ChapG N3Drain), `hex3U` + `hex3U_rec` (chapter G), and `residueCard`.
4. `blueprint/CHAP-I_capstone_conditionality.md` rows HYP.04–HYP.09 and
   `blueprint/CHAP-G_base_cases_menus.md` §§ around `hex3U` (~lines 3180–3230) and the
   H-1 honesty note (~line 2612).

## Deliverable

`docs/in-progress/N3_DRAINAGE_BLUEPRINT_2026-08-24.md` containing:

1. The target statement(s) verbatim in the present Lean vocabulary — H.97's `hrate`
   exactly as typed at its use site (quote the use site), and the `DrainageAt 3`
   corollary chain with the named landed theorems it fires through.
2. A complete node plan (table: node id | content | deps), each node 30–60 min of Lean
   work, with per-node prose giving the proof from U8's document rewritten against the
   NAMED landed lemmas (verify each name by `rg` — never trust the blueprint/U8 doc's
   names without checking). Where U8 uses a counting argument, make the Lean-facing
   statement explicit (Finset cardinalities over `(O/π^N)³`? the corpus's existing
   counting vocabulary? — find what chapter G/H actually use and match it).
3. Honest per-node status: PROVED (in U8's doc, transcription only) / BLUEPRINT (design
   fixed, proof sketched) / OPEN (real gap — name it precisely).
4. Elaboration check: write the node SIGNATURES (with `sorry`-free `True`-body stubs or
   `example` forms — no `sorry`) to `leanfinal/scratch/U10_sig_check.lean` and verify
   `lake env lean` accepts it; report the command output status.

## Rules

- Do NOT edit `leanspec/`, `leanfinal/Uniformity/`, or the blueprint chapter files.
  Your only writes: the deliverable doc + the scratch check file.
- Honesty: if any step of U8's proof cannot be typed in the present vocabulary, mark
  that node OPEN with the exact missing carrier — do not paper over.
- Do NOT `git commit` (sandbox mounts `.git` read-only); the orchestrator commits.
