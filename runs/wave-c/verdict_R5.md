# Verdict R5 — ambient letters and the canonical dictionary at depth four (OPEN-LETTERS core)

**Date:** 2026-08-29
**Unit:** R5 / DEEP_WITNESS_CAMPAIGN §6.4 row R5 ("Define ambient letters/canonical reads
and prove the shared receiver/letter equalities required by G4")
**Overall verdict:** **LANDED — the G4 clause bodies are PROVED at the S2 depth-four data;
the record-typed inhabitation is one application away at R7 (named handoff).**

New file: `leanfinal/Uniformity/ChapC/C136r3.lean` (1221 lines, zero `sorry`, zero
warnings; all 99 AxCheck footprints are Lean-core `{propext, Classical.choice, Quot.sound}`
subsets).  No landed `.lean`, leanspec, or scratch file was edited; no git operation was
performed.  Landing note for the orchestrator: the chapter aggregator
`Uniformity/ChapC.lean` takes the one-line `import Uniformity.ChapC.C136r3` at commit time
(exactly how C136r0–r2 entered; per this unit's fence I did not edit the landed aggregator).

## Re-grounding (what this row is)

G4's shared record `I10DeepExport.DeepLevelExport X j hj` demands, at the unique deep-live
level `j = 3` of the depth-four witness, two dictionary clauses that no landed field
supplied (the TAU adjudication's named opens `LVS-CANONICAL-GENERATOR-DESCENT` /
OPEN-LETTERS): the **receiver/letter equality** `algebraMap Kt L (levelHom 3 (letterZ (a+2)))
= letterValue a` and the **canonical-generator descent** (wrap/letter values are embedded
`Kt`-units).  The depth-two precedent supplied these through NP-6/NP-7
(`C130np6.s2AmbientLetter`, `C130np7.s2CanonicalRead`): residue letters forced by the
ψ-root law, plus an L-valued kernel read CONSTRUCTED as the distinguished-generator basis
inversion — so the generator regressions are consequences of coordinate formulas, not a
freely chosen table (the anti-cook content demanded by the twist audit,
`C130s18.embeddedValue_not_uniform`).  R5 is that construction at `s2DepthFour` (R0's
receiver/normalizer, live levels 1..4), consumed against the D3-19/D4-18 calculi.

## What landed (charge item → artifact)

1. **Ambient letters/canonical reads defined at the depth-four occurrence.**
   * `s2AmbientLetterFour` (constant unit `1`) + `s2AmbientLetterFour_psi_root` — the
     exact `SplitNodePointSource.psi_root` field law at the R0 receiver (`ψ_i = X − C 1`
     at every T3 stage; root `1` in ANY `L`, no residue-cardinality input).
   * Height/kernel laws at all four levels (`s2four_levelExponentHeight_one..four`,
     `s2four_mem_ker_*_iff('` forms`)`): weighted sums `2p+q`, `4p+2q+5t₀`,
     `8p+4q+10t₀+21t₁`, `16p+8q+20t₀+42t₁+85t₂` — the depth-four extension of D62w's
     regressed lattices, now theorems of the T3 datum.
   * Generator coordinates (machine-checked through the CC-4 Laurent solve, `simp only
     [laurentSolve, …] + decide`, no bare `rfl` through the WF-compiled solve):
     `wrapGen = (−1,2,0)` at every level; `n̂₂(10)=(2,1,0)`, `n̂₃(20)=(2,1,0,0)`,
     `n̂₃(42)=(4,0,1,0)`, `n̂₄(40)=(2,1,0,0,0)`, `n̂₄(84)=(4,0,1,0,0)`,
     `n̂₄(170)=(8,0,0,1,0)`; hence `Λ`-coordinates `(−2,−1,2)`, `(−2,−1,2,0)`,
     `(−4,0,−1,2)`, `(−2,−1,2,0,0)`, `(−4,0,−1,2,0)`, `(−8,0,0,−1,2)`.
   * The reads `s2CanonicalReadFour1..4` + the total field-shape `s2CanonicalReadFour`
     (trivial hom at junk indices, NP-7's total pattern): each level's read is the
     triangular basis inversion `g ↦ η^m ∏ β_a^{s_a}` in raw lattice coordinates, built
     from single-letter `zpow` homs (`zpowHom`, the file's one generic helper — flagged)
     whose additivity lemmas are exactly the kernel-law evenness arithmetic (omega).
   * Generator regressions at every live level, proved through the coordinates (never
     through the S2 collapse): `read(W₀) = η` (levels 1–4), `read(Λ_a) = β_{a+2}` (levels
     2, 3, 4; uniform `s2CanonicalReadFour3_letterClass` / `..Four4_letterClass` with the
     G4 stage pairing `Λ_a ↔ a+2`), the generator-word displays
     (`..._generatorWord`, levels 2–4, freeze v2 §4's `η^m·∏β^t` shape) and their S2
     collapse to `1` recorded separately (`..._generatorWord_eq_one`).

2. **The equalities at j = 3 PROVED.**
   * `s2Mu4Calculus` / `s2Mu5Calculus` — the explicit `fgmnCalculusOf` terms inside
     D3-19's/D4-18's `Nonempty`s, named with `letterZ` pinned by `rfl` to the forced
     constant-1 letters (`s2Mu4Calculus_letterZ`, `s2Mu5Calculus_letterZ`).
   * ★★★ `s2four_letter_receiver_mu4` — **the OPEN-LETTERS core**: the exact
     `DeepLevelExport.letter_receiver` body at the S2 depth-four data, `j = 3`, with this
     file's read in the `canonicalRead` slot:
     `algebraMap Kt L (s2TerminalReceiverFour.levelHom 3 (s2Mu4Calculus.letterZ (a+2)))
     = (s2CanonicalReadFour L 3 (s2LaurentNormalizerFour.letterClass hi a) : L)`.
   * ★★ `s2four_letter_receiver_mu5` — the μ₅ twin at the terminal level `j = 4`.
   * ★★ `s2four_wrap_descent` / `s2four_letter_descent` — the exact
     `CanonicalGeneratorDescent.wrap`/`.letter` clause bodies (embedded-`Kt`-unit
     existentials along the same `Units.map (algebraMap Kt L)` as I10's
     `unitAlgebraMap`), at EVERY gauge-live level (j = 1, 2, 3), witness the unit `1`.
   * Honest scope: the literal `CanonicalGeneratorDescent Aℛ 3 hj` RECORD is typed at an
     `ArisingCore`/`ChainRealization`, and none exists at depth four (R7/R9; the GCW-6
     fence keeps R5, like R0, at DATA + dictionary).  What "inhabits the dictionary" can
     honestly mean pre-R7 is exactly what landed: every clause BODY proved at the same
     receiver/normalizer/embedding, plus the node-typed conditional theorems below, so
     R7's realization inhabits the record by direct application (through
     `DeepLevelExport.ofLetterEq`, whose remaining input is the G3 site package).

3. **Generalized freely / named handoff (R34's precedent).**
   * Generalized: the whole bank runs at all live levels 1..4 (not only j = 3) — descent
     at every gauge-live level; the μ₅/terminal-level letter equality; the level-4 letter
     regressions serving the `(1,1,171)` refinement consumers.
   * Handoff theorems (Part 7): `s2four_node_wrapValue_descent`,
     `s2four_node_letterValue_descent`, `s2four_node_letter_receiver` — for ANY future
     depth-four `SplitNodePointSource` at the R0 receiver with
     `S.canonicalRead j = s2CanonicalReadFour … j`, the node's own `wrapValue`/
     `letterValue` satisfy the descent clauses and the exact `letter_receiver` body.
   * Handoff records (header, "Named handoff to R7"): (i) the node/realization instance
     itself (R7/R9); (ii) the **site-calculus truncation transport** — G4's
     `site.calculus` lives on `core.T.trunc 3` while D3-19's lives on `s2DepthThree`;
     the towers agree on the live range but differ at junk indices (`u 4 = 85` vs `21`),
     so the transport is a genuine assembly step for R7/C0.  Mitigation proved here:
     `letter_receiver` reads ONLY the letter VALUE, and all S2 stage fields are the same
     constant `stageField`, so the landed equalities serve either typing verbatim.
   * NO spanning claim is made (C130cr's triangular-basis bridge / `LVS-TAU-WORD` stays
     OPEN): the reads are formulas + regressions, exactly the NP-7 discipline.

4. **OPEN-LETTERS fence (C.102 / htie) — status changed, NOT discharged; fence stands.**
   * `C.102 letter_formula` (leanspec ChapC.lean:2857): ties
     `letterZ 2 · letterZ 1^⌊e₂u₂/e₁⌋ = ρ.symm (AdjoinRoot.root ψ₂)` through an
     evaluation iso `ρ`.  R5 supplies the LETTER half of the audited gap ("no class field
     relates `letterZ` to `ρ` or `AdjoinRoot.root ψ₂`") at the S2 witness in
     receiver/canonical-read form; the `ρ`/`AdjoinRoot` half is untouched — it is the
     OPEN-EVAL-ISO bridge (C.100's fence), so C.102 is NOT dischargeable by R5 alone.
   * `gentow5w_one_shape`'s `htie` (leanspec ChapC.lean:4083 commentary): the missing law
     is `Rgr u' (chainNorm 1 u') = letterZ 1 ^ k` — a GRADED-RESIDUAL scalar tie, a
     different carrier from the lattice reads R5 constructs.  What R5 changes: at the S2
     occurrence `letterZ ≡ 1` is now a PINNED read (`s2Mu4Calculus_letterZ` etc.), so
     htie's S2 instance narrows to the concrete μ-bank claim "`Rgr` of the chain
     normalizer at its own grade is `1`" — stateable entirely inside the landed
     C132/C136 operator stacks.  Recorded as a candidate follow-up; the signed statement
     is untouched.

## Verification

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136r3.lean
```
Exit 0; zero errors, zero warnings, zero `sorry`; all 99 footer declarations report only
Lean-core axioms.  Repository scope: `git status` shows only this new file (plus other
units' concurrent artifacts); no landed statement touched.

## Proof notes (for the next porter)

* The letter-class coordinate lemmas need the Laurent-solve rewrite EXPLICIT before
  `decide` (`rw [show … laurentSolve (j−1) k = … from …]`): norm_num leaves the `(j−1)`
  index unreduced inside `ofAdd`, and `decide` then chokes on the free `h2 hq`.
* The receiver/letter equalities must NOT rewrite `letterZ … = 1` (cross-tower motive is
  type-incorrect at instances transparency); use `map_one (levelHom j)` directly — the
  defeq between the depth-three- and depth-four-typed `1`s is elaborator-level.
* The level-4 exponent additivity omegas (three nested exact `/2`s against two kernel
  equations) need `maxHeartbeats 1600000`.
* `fin_cases` on `Fin (2−1)` produces a wrapped index; close with `show` at the literal
  index (or `exact`), never `rw`.
