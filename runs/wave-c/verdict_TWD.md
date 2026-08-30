# verdict_TWD — UNIT TWD: the tau-word/descent supply at general witnesses (rows C3 + R5)

**Status: COMPLETE.**  `leanfinal/Uniformity/ChapI/I10TauSupply.lean` (802 lines) — 0
errors, 0 warnings, 0 `sorry`, all 24 printed footprints Lean core
`{propext, Classical.choice, Quot.sound}`.  Verified per-file:
`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10TauSupply.lean` (clean,
footprints printed).  Registered in the chapter aggregator `Uniformity/ChapI.lean` (one
import line — the standing landing plumbing; only landed-file edit).  Cite ledger:
**empty**.  No git ops (per charge).

## Charge 1 — SCOPE (settled, machine-checked where "derivable")

### (a) `CanonicalTauWordAt` (row C3) — a LATTICE statement in disguise; the spanning
CLOSES for the concrete normalizer

* The demanded tau classes are the normalizer two-cocycle
  `τ(a,b) = n̂(a)·n̂(b)·n̂(a+b)⁻¹` (D02's `NormSection.tau` at the transported arena
  section).  Under the landed plumbing
  (`canonicalResFamily → canonicalResAt → canonicalRes0 → canonicalRead ∘ kerLevelProj0`,
  through the view's `KernelRead` equality) its read is the read of a level-`j` KERNEL
  element, and the read of any distinguished-generator word is already the demanded
  word shape (C130cr's landed `canonicalRead_generatorWord`).  So row C3 follows from
  pure exponent-lattice spanning — **the residue field never enters**.
* **What q = 2 bought at the keystone: the READ side** (`s2CanonicalReadFour3_eq_one`,
  read ≡ 1, so `m = 0, t = 0`).  **What replaces it: the lattice side** — ★★
  `DeepTower.laurentNormalizer_kernelSpan`: for the CONCRETE greedy normalizer
  (`laurentNormAt`, the CC-4 digit solve), EVERY level-kernel element IS a
  distinguished-generator word, at every stage-live level of every tower — freeze v2
  §4's OPEN "triangular-basis bridge", now a THEOREM for the canonical normalizer,
  **uniform in q**.  Proof: induction on the level — the top exponent of a kernel
  element is divisible by `e_{i+2}` (rung coprimality `gcd(u_{i+2}, e_{i+2}) = 1`),
  peeling `Λ_top` lands in the top-zero inclusion of the level-down lattice (heights
  scale exactly by `e_{i+2}`), and the level-1 kernel is exactly `⟨W₀⟩` by the frame
  coprimality `gcd(e₁, u₁) = 1`.
* **The spanning does NOT close for the abstract field**: `ChainRealization.normalizer`
  demands only `norm_zero`/`exact_height`; twisting the norm word at the top letter
  height by `Λ_top` replaces `Λ_top` by `Λ_top²`, whose span has index 2 in the kernel —
  the lattice Prop is falsifiable across the abstract field, so no universal proof from
  the realization interface can exist.  The keystone's normalizer IS the concrete one
  **definitionally** (`s2LaurentNormalizerFour := (s2DepthFour h2 hq).laurentNormalizer`;
  `s2Four_normalizer_eq_laurent := rfl`), as is every landed witness's.

### (b) `CanonicalGeneratorDescent` (row R5) — splits; letter half consolidates, wrap
half irreducible

* letter clauses ⟸ field-level `Kt`-preimages of the letter values — in particular ⟸
  the `DeepLevelExport.letter_receiver` receiver equalities (the site-tied shape the
  campaign already targets), via the landed `letter_descent_of_receiver_eq`.
* wrap clause (`WrapDescentAt`, NEW name for the extracted field): NO landed law ties
  `wrapValue = canonicalRead (x^{e₁}π^{−u₁})` to any site letter or receiver value.
  This unit claims NO reduction for it — it is the OPEN-LETTERS core, exactly as DWR
  §11.5 graded row R5.

## Charge 2 — what landed (all PROVED, Lean-core)

* **§1 the spanning engine** (namespace `Uniformity.Density.Tower`): `levelSnocHom`
  (top-zero inclusion) + transport laws (`levelSnocHom_wrapGen/keyLetter/letterClass`,
  `laurentSolve_e_mul`, `laurentNormAt_e_mul`, `letterClass_top_coe`,
  `generatorWord_snoc`, `heightAux_add/zsmul`, `wrapGen_zpow`, `span_assemble`), the
  main induction `laurentGeneratorSpan_aux`, and ★★ `laurentNormalizer_kernelSpan`.
* **§2 the C3 reduction** (namespace `Uniformity.Density.DeepExport`):
  - `KernelSpanAt Aℛ j hj` (NEW Prop — row C3's exact lattice remainder: read-free,
    residue-free, universe-free).
  - ★ `canonicalTauWordAt_of_kernelSpan` — row C3 at EVERY arising realization from
    `KernelSpanAt` alone (plumbing: `canonicalResFamily_eq_canonicalResAt` — the
    generic form of the landed keystone step — then `canonicalRead_generatorWord`).
  - `kernelSpanAt_of_laurent` — the remainder CLOSES whenever
    `Aℛ.normalizer = core.T.laurentNormalizer`.
* **§3 the R5 dissection**: `WrapDescentAt` (NEW Prop),
  `canonicalGeneratorDescent_of_wrap_letterPreimages`,
  `canonicalGeneratorDescent_of_wrap_letterReceiver` (site-tied; consumes any
  `WleClearedLevelExport`'s `calculus.letterZ` letters).
* **§4 supply compilations**: `tauWordDescentSupply_of_span_descent`, ★
  `tauWordDescentSupply_of_laurent_descent` — **row C3 is ELIMINATED from the
  per-witness vartheta boundary at every canonical-normalizer realization**; the open
  boundary there is row R5 ONLY.  Universal forms `UniversalKernelSpan` /
  `UniversalGeneratorDescent` (NEW Props) + ★
  `universalTauWordDescentSupply_of_span_descent` into USUP's
  `UniversalTauWordDescentSupply` (hence, with USUP's ★ `deepTwistField_of_supplies`,
  into the capstone `deepTwist` field's vartheta half).
* **§5 keystone coherence**: `s2Four_normalizer_eq_laurent` (`rfl`), ★
  `s2Four_canonicalTauWordAt_uniform` — the keystone's `tau_word` clause re-derived
  through the GENERAL spanning route with **no use of the card-2 collapse** (the
  uniform mechanism machine-checkedly REPLACES what q = 2 bought), and
  `s2Four_tauWordDescentSupply'` (USUP's keystone supply re-derived; descent leg =
  the keystone's `s2Four_canonicalGeneratorDescent`, conditionality unchanged).

## Charge 3 — does the vartheta half fire?  NO (and why not)

`UniversalTauWordDescentSupply n` quantifies over ALL `ChainRealization`s, whose
`normalizer` and `canonicalRead` are free fields; the lattice remainder is falsifiable
across that freedom (index-2 twist above), and the wrap descent is OPEN-LETTERS.  The
honest post-TWD boundary of the vartheta half, per arising realization and deep-live
level:

| missing datum (Lean `Prop`) | row | status after TWD |
|---|---|---|
| `KernelSpanAt` | C3 | **closed by `rfl`-side condition at every canonical-normalizer realization (all landed witnesses); open only across the abstract normalizer field** |
| `WrapDescentAt` | R5 (wrap) | open — OPEN-LETTERS core, no reduction claimed |
| letter receiver equalities (`letter_receiver` shape) | R5 (letters) | consolidated into the site record's own target shape; discharged per-site |

## Interface recommendation (owner-gated, NOT enacted)

If `ChainRealization.normalizer` were PINNED to `W.laurentNormalizer` (dropping the
free field), row C3 would vanish from the campaign entirely: `KernelSpanAt` becomes a
theorem at every realization.  That is a signature change on a landed structure —
flagged for the owner/orchestrator, not touched here.

## Flagged for human review (trust boundary — new statements)

`KernelSpanAt`, `WrapDescentAt`, `UniversalKernelSpan`, `UniversalGeneratorDescent`
(supplier-side interface `Prop`s below the signed surface; no leanspec name touched).
All other new names are proved general lemmas over the landed corpus.

## Notes

* Universe finding: `KernelSpanAt` needs NO `uG` (the exponent lattice is `Type 0`);
  the universal forms are `.{uKt, uL}` while USUP's supply is `.{uG, uKt, uL}` — the
  compilation is polymorphic over the extra `uG`.
* Repo footprint: the new module + the aggregator import line + this verdict.
