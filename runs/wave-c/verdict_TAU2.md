# verdict_TAU2 — UNIT TAU: the tau rows at abstract normalizers (the shared vartheta gate)

**Date:** 2026-08-31.  **Status: COMPLETE.**
`leanfinal/Uniformity/ChapI/I10TauRows.lean` (NEW, ~870 lines) — 0 errors, 0 warnings,
0 `sorry`, all **28** printed footprints exactly Lean core
`{propext, Classical.choice, Quot.sound}` (machine-tallied, non-core set = NONE).
Verified per-file (`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10TauRows.lean`,
exit 0), per-target (`lake build Uniformity.ChapI.I10TauRows` — Build completed
successfully, 8970 jobs), and the chapter aggregator `Uniformity/ChapI.lean` re-verified
exit 0 after the one standing import-line edit.  Cite ledger: **empty**.  No git ops.

FILENAME NOTE: `verdict_TAU.md` already existed (2026-08-28, the LVS-CANONICAL-TAU-EXPORT
unit — a different charge/era); per the coordinator it is untouched and this unit's verdict
is `verdict_TAU2.md`.

## STATUS FIRST

| charge | verdict | machine anchor |
|---|---|---|
| (a) does the deepTwist socket PIN the normalizer? | **NO — RECEIVED, abstractly, like the ladder guard** | source: `CanonicalDeepTwistConfig`'s body is C130s18's `DeepTwistRealizationData` = `∃ E fE core Aℛ X eK eG, core.r = r ∧ views` (`C130s18.lean:180-201`); machine: the LITERAL leanspec socket fires at the TWISTED witness (`s2FourTwisted_canonicalDeepTwistConfig`) |
| (b) do the config's other laws force kernel-span at the received witness? | **NO — REFUTED, machine-checked** | the twist satisfies ALL config laws AND ¬`KernelSpanAt` — ★★ `s2FourTwisted_canonicalDeepTwistConfig` + ★ `s2FourTwisted_not_kernelSpanAt`; **STOP-LINE**: ★★ `s2Four_not_universalKernelSpan` — TWD's `UniversalKernelSpan n` is FALSE at any degree hosting a keystone occurrence |
| honesty pin | the READ row SURVIVES the twist at q = 2 | `s2FourTwisted_canonicalTauWordAt` (m = 0, t = 0; read ≡ 1).  The twist kills the LATTICE route only — `UniversalTauWordDescentSupply` itself is NOT refuted (its descent half also survives at the twisted keystone: the doubled letter reads 1² = 1) |
| (c) minimal restriction | **owner-amendment territory, flagged NOT enacted** | `NormalizerPinned` + `s2Four_not_universalPinning` (the pinning is FALSE as an unguarded universal supply — it can only enter as a structural guard); guarded route landed: ★ `universalPinnedTauSupply_of_descent` |
| charge 2: `WrapDescentAt` vs RUNG's carriers | **NO reduction — machine-separated** | ★ `wrapDescentAt_not_uniform`: the χ-twist fixes normalizer (CANONICAL), keys, receiver, input — everything RUNG's `LevelDatum` machinery could consume — yet moves the wrap value off the embedded subfield.  Row R5's wrap clause is genuinely per-realization supply (OPEN-LETTERS core, exactly TWD's grading) |

## 1. The mechanism (TWD's prose "index 2", now a theorem)

`LaurentNormalizer` (C130k) has THREE fields — `norm : (i) → ℤ → LevelExponentLattice i`,
`norm_zero`, `exact_height` — and **no additivity/coherence law in the height**, so any
pointwise kernel-element multiple of a legal normalizer is legal (§1 `LaurentNormalizer.twist`,
`twistAt3`).  `DeepTower.topTwistedNormalizer` twists the CC-4 canonical normalizer at level 3
at the SINGLE input `k₀ = e₃·((ê₃/ê₃)·u₃)` (the top letter's height; `letterInput3`) by
`Λ_top⁻¹`:

* the non-top letter class is UNCHANGED (`topTwisted_letterClass_castSucc` — its height
  input differs from `k₀`; at S2 depth-4: `20 ≠ 42`, value pins by kernel reduction);
* the top letter class DOUBLES: `Λ'_top = Λ_top²` (`topTwisted_letterClass_top`);
* the wrap is normalizer-free.

The **top-exponent character** `topCoord3 : LevelExponentLattice 3 →* Multiplicative ℤ`
separates: twisted-span top coordinates = `2e₃ℤ`, while the canonical `Λ_top` (a level-3
KERNEL element) sits at `e₃ ≠ 0`.  ★★ `topTwisted_letterClass_not_generatorWord` — generic
in the tower, hypotheses only the two numeric side conditions (`hk₀`, `hsep`) + stage-liveness.

## 2. Why the socket cannot exclude the twist (the structural finding)

* `ChainRealization` = {receiver, keys, normalizer, node}; `RealizedInput`'s five fields
  (`receiver_eq/stageKey_eq/stageDeg_eq/point/point_mem`) never mention the normalizer —
  §3 `ChainRealization.setNormalizer` + `RealizedInput.setNormalizer` transport the input
  VERBATIM.  (This is the exact dual of C130s18's `twistRealization`, which frees
  `canonicalRead` while fixing the normalizer.)
* The view equations are PRODUCING equalities: they pin the EXTERNAL socket tuple to the
  witness's own exports (`RealizedInput.gaugeFamilyViewEq` etc., `C130vw.lean`) and hold at
  EVERY realization — so the landed general application `realizedInput_deepTwistConfigData`
  fires at the twisted witness unchanged, producing the LITERAL capstone socket body
  (leanspec-typed `CanonicalDeepTwistConfig`, `uE = 0` profile).
* Hence: for the config instance exported by the twisted witness, the received witness is
  twisted with ¬`KernelSpanAt` — no proof of kernel-span from the config laws can exist.
  (Precision note: the twisted witness exports a DIFFERENT external `N` than the canonical
  witness — the twist changes `norm 3` at one input — so this refutes "the socket forces
  kernel-span at ITS received witness", which is exactly what the vartheta route needs.)

## 3. The keystone theorems (all in `Uniformity.Density.DeepExport`, §4 of the file)

Conditionality of every §4/§6 keystone item: EXACTLY the landed keystone theorems'
(TWD §5 / USUP §5) — the S2 hypotheses `(h2, hq)` + instances, the four threshold datums
`w₁–w₄`, and the R8/R8r payload `(F₀, hF₀, μ, …, hcop)` (G9-gated; no payload instance is
landed).  If no such instance existed the refutations would be vacuous — same standing
disclosure as the whole wired genre.

* `s2Four_letterInput3_top_eq/castSucc_eq` — the height inputs are `42`/`20`.
* `s2FourTwistedNormalizer` / `s2FourTwistedRealization` / `s2FourTwistedInput`.
* `s2FourTwisted_not_pinned` — the twisted witness's normalizer ≠ canonical.
* ★ `s2FourTwisted_not_kernelSpanAt` — ¬`KernelSpanAt` at deep-live level 3.
* ★★ `s2FourTwisted_canonicalDeepTwistConfig` — the capstone socket at the twisted witness.
* ★★ `s2Four_not_universalKernelSpan : ¬ UniversalKernelSpan n` — **the stop-line**: TWD's
  row-C3 universal Prop is dead as stated; LDR's chain
  (`ladderVarthetaSupplierLive_of_span_descent` ⟸ `UniversalKernelSpan ∧
  UniversalGeneratorDescent`) and TWD's `universalTauWordDescentSupply_of_span_descent`
  remain valid implications but are now provably UNDISCHARGEABLE through the span leg.
* `s2FourTwisted_canonicalTauWordAt` — the honesty pin (read row survives).

## 4. Charge 2 — `WrapDescentAt` (row R5's wrap) after RUNG

* RUNG's carrier packs (`I10RungPacks`) live at `LevelDatum`/polynomial carriers
  (`rung2Read`, `nextCarrier`, `towerPacks`) — none of their laws mentions
  `node.canonicalRead`, which is ALL that `wrapValue = canonicalRead(x^{e₁}π^{−u₁})`
  consumes.
* §5 machine form: `twistRealization_wrapValue/_normalizer/_keys_receiver` pin that
  C130s18's χ-twist fixes every carrier-side field (normalizer stays CANONICAL) while
  `wrapValue ↦ wrapValue · χ(W₀)`; ★ `wrapDescentAt_not_uniform` — no derivation uniform
  in {canonically-normalized realization + realized input} can produce `WrapDescentAt`
  (χ with an unembedded value at the wrap class defeats it).  A fortiori no carrier read
  law implies it.  **Verdict: no reduction — the wrap clause does NOT collapse into
  RUNG's carrier read laws even at the canonical normalizer.**  It stays the OPEN-LETTERS
  per-realization supply, exactly as TWD graded it; the discharge site remains witness
  construction (where `canonicalRead` is chosen), per the old TAU unit's supplier ledger.

## 5. The exact post-unit tau boundary (charge 3)

The capstone `deepTwist` field's vartheta half (and, through LDR, the ladder `vartheta`
leg) now rests on, per arising realization and deep-live level:

| item | status after TAU |
|---|---|
| `KernelSpanAt` at abstract normalizers (row C3, lattice form) | **REFUTED as a universal** (`s2Four_not_universalKernelSpan`); closed by `rfl` at every canonical-normalizer (= every landed) witness — unchanged |
| the normalizer freedom itself | settled: the socket RECEIVES; view laws cannot exclude the twist |
| the honest route | **owner amendment (flagged, NOT enacted)** — either **(O-TAU-1)** pin `ChainRealization.normalizer := W.laurentNormalizer` (TWD's recommendation), or **(O-TAU-2)** conjoin `NormalizerPinned` into `DeepTwistRealizationData`'s existential.  Under either, ★ `universalPinnedTauSupply_of_descent`: the tau boundary collapses to `UniversalPinnedGeneratorDescent` = row R5 only |
| row R5, wrap clause (`WrapDescentAt`) | OPEN — per-realization supply; machine-checkedly NOT reducible to carrier laws (§5) |
| row R5, letter clauses | unchanged — consolidated into the site record's `letter_receiver` equalities (TWD) |
| read-level row (`CanonicalTauWordAt`) at general q | unchanged — open, NOT refuted (survives the twist at q = 2) |
| `UniversalTauWordDescentSupply` itself | NOT refuted; but its only landed general-depth discharge route (span + descent) is now provably closed — a new mechanism or the amendment is REQUIRED |

## 6. Flagged for human review (trust boundary — new statements)

`Prop`-level: `NormalizerPinned`, `UniversalNormalizerPinning` (recorded ONLY to be
refuted), `UniversalPinnedGeneratorDescent`, `UniversalPinnedTauWordDescentSupply`.
Constructions consumed by the refutations: `topCoord3`, `letterInput3`,
`LaurentNormalizer.twist`/`twistAt3`, `DeepTower.topTwistedNormalizer`,
`ChainRealization.setNormalizer`, `RealizedInput.setNormalizer`,
`s2FourTwisted{Normalizer,Realization,Input}`.  All supplier-side, below the signed
surface; no leanspec name touched.  OWNER ITEMS (flagged, not enacted): O-TAU-1/O-TAU-2
above — both are signed-surface amendments (a landed-structure retype resp. a socket-body
conjunct).

## 7. Verification & footprint

* Per-increment command run throughout; FINAL per-file exit 0, 0 errors, 0 warnings,
  0 `sorry`; 28/28 `#print axioms` exactly `[propext, Classical.choice, Quot.sound]`
  (scripted tally, non-core = NONE).
* `lake build Uniformity.ChapI.I10TauRows` — success (8970 jobs); `Uniformity/ChapI.lean`
  aggregator exit 0 after the one import line.
* Repair log (mechanical only): (1) `letterClass_coe` takes `N` explicitly; (2) a
  ∀-quantified product-split `have` failed `Fintype (Fin (3-1))` synthesis — replaced by
  direct `rw [Fin.prod_univ_castSucc, Fin.prod_univ_one]`; (3) `decide` rejects free
  variables (O, h2, hq) — value pins via projection-`rfl` `have`s + `simp only` +
  `norm_num`; (4) payload section variables auto-included into payload-free defs —
  variable blocks re-scoped so defs precede the payload block; (5) `include … in` must
  precede the docstring (RUNG's note, re-confirmed); one `omit [IsAdicComplete …] in`.
* Files: `leanfinal/Uniformity/ChapI/I10TauRows.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No other file
  touched; IFCG53 untouched; no git operation.
