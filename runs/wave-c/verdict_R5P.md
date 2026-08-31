# verdict_R5P — UNIT R5P: `UniversalPinnedGeneratorDescent` (row R5) at pinned normalizers — SETTLED NEGATIVE, REPAIR LANDED

**Date:** 2026-08-31.  **Status: COMPLETE.**
`leanfinal/Uniformity/ChapI/I10WrapPinned.lean` (NEW, ~370 lines) — 0 errors, 0 warnings,
0 `sorry`, all **15** printed footprints exactly Lean core
`{propext, Classical.choice, Quot.sound}` (one, `coordFunctional`, even choice-free).
Verified per-file (`timeout 580 ~/.elan/bin/lake env lean
Uniformity/ChapI/I10WrapPinned.lean`, exit 0) and per-target (see §7).  Registered in the
chapter aggregator `Uniformity/ChapI.lean` (one import line).  One comment-only dated
update block added to `I10PinnedBoundary.lean`'s honesty scope (the OTAU→I10TauRows
precedent; re-verified green).  Cite ledger: **empty** (the one new Mathlib import,
`RatFunc`, is instance plumbing for the `uL = 0` witness).  NO git operations.

## STATUS FIRST

| charge | verdict | machine anchor |
|---|---|---|
| 1. is `WrapDescentAt` derivable at the PINNED normalizer? | **NO — and the premise of the charge is false: the χ-twist is NOT excluded by the pin** | `twistRealization_normalizerPinned := hN` — the χ-twist moves only `node.canonicalRead`; its normalizer is `rfl`-unchanged, so a pinned witness's twist is pinned.  TAU's `wrapDescentAt_not_uniform` had already quantified `huniform` over PINNED realizations; the only gap was the existence of a χ with unembedded wrap-class value — now closed (§1 below) |
| 2. prove `UniversalPinnedGeneratorDescent` | **IMPOSSIBLE — REFUTED, machine-checked** | ★★ `s2Four_not_universalPinnedGeneratorDescent` (any `L` with an unembedded unit) + ★★ `s2Four_not_universalPinnedGeneratorDescent₀ : ¬ UniversalPinnedGeneratorDescent.{0,0} n` (the `L`-freedom DISCHARGED at `L := RatFunc Kt`, `g := X`) — **THE STOP-LINE**: the single tau remainder OTAU left both capstone vartheta halves on is FALSE at every keystone-hosting degree |
| 3. honest fallback | **DELIVERED: the minimal named residue is a GUARD, not a supply** | `DescentPinned` (row R5's content as a per-realization guard) + ★★ `universalDoublyPinnedTauSupply` — under {`NormalizerPinned`, `DescentPinned`} the whole per-witness tau supply is an UNCONDITIONAL THEOREM (zero residue); keystone instance `s2Four_descentPinned` (+ pin tooth, + coherence re-derivation) |

## 1. The mechanism (what closed TAU's parametric gap)

The wrap generator `W₀ = x^{e₁}·π^{−u₁}` has exponent vector `(−u₁, e₁, 0)` in the
CONCRETE Laurent lattice `LevelExponentLattice i = Multiplicative (ℤ × ℤ × (Fin (i−1) → ℤ))`
— a PRIMITIVE vector in the `(π, x)`-plane, by the same frame coprimality
`gcd(e₁, u₁) = 1` that closes TWD's spanning base case.  §1 lands:

* `coordFunctional c₁ c₂ i : LevelExponentLattice i →* Multiplicative ℤ` (the
  `(c₁, c₂)`-coordinate functional; kills letter coordinates);
* `DeepTower.coordChar` — the functional restricted to the level kernel, followed by
  `g^·` (`zpowersHom`): a character family of exactly the shape C130s18's
  `twistRealization` consumes, value at the wrap class = `g^(c₁·(−u₁) + c₂·e₁)` by `rfl`;
* ★ `DeepTower.exists_wrapChar` — **for every tower, every stage-live level, every target
  `g : Lˣ`, a character family with `χ i (W₀-class) = g`** (Bézout pair from the
  coprimality; uniform in `q`, no keystone numerics, no residue field).

Feeding `g := RatFunc.X` (unembedded over the keystone terminal field
`Kt = (s2DepthFour h2 hq).fld 4`: scalar-tower + `RatFunc.algebraMap_injective` +
`Polynomial.X_ne_C`) through TAU's ★ `wrapDescentAt_not_uniform` at the landed depth-4
keystone — whose `huniform` is exactly what `UniversalPinnedGeneratorDescent n` supplies
via `.wrap` at the deep-live level 3 — yields `False`.

## 2. The refutation's scope and honesty

* **Conditionality**: exactly the landed keystone theorems' (S2 hypotheses `(h2, hq)` +
  instances incl. `IsAdicComplete`, the four thresholds `w₁–w₄`, the R8/R8r payload
  `(F₀, hF₀, μ, …, hcop)`, G9-gated, no payload instance landed) — if no such instance
  existed the refutation would be vacuous.  Same standing wired-genre disclosure as TAU's
  `s2Four_not_universalKernelSpan`, whose exact successor this is, one guard deeper.
* **Universe profile**: refuted at `.{0, uL}` for every `uL` (parametric form) and fully
  instantiated at `.{0, 0}`.  All landed witnesses live at `uKt = 0`.
* Degrees: every `n = μ·16, μ ≥ 1` hosting the keystone payload.

## 3. Consequence for the post-OTAU boundary (the load-bearing finding)

Post-A-I.9, BOTH capstone vartheta halves rest on `UniversalPinnedGeneratorDescent`
(verdict_OTAU §3): `deepTwistField_of_pinned_descent_site` (deepTwist half, with the
pinned site supply) and `ladderVarthetaSupplierLive_of_pinned_descent` /
`ladderFieldLive₃_of_pinned_boundary` (ladder half, row R5 ALONE).  Those implications
remain valid but are now **provably undischargeable through their descent premise** —
the exact situation TAU created for LDR's span leg, reproduced one amendment later.
A dated update block records this in `I10PinnedBoundary.lean`.

**The structural diagnosis**: the normalizer pin closed the LATTICE freedom
(`KernelSpanAt` is free under it), but the READ freedom (`node.canonicalRead`, protected
by C130s18's non-swallowing fence — no realization law ties it to anything) is a second,
independent adversarial axis, and the wrap clause lives entirely on it.  No socket view
law can exclude the χ-twist (it exports its own twisted config; the twisted input is
verbatim).  So — exactly as with the pin — the descent clause can only enter as a
structural GUARD.

## 4. The repair (O-R5P, flagged NOT enacted) and what is now a THEOREM

* `DescentPinned Aℛ := ∀ j (hj : DeepLive core.r j), CanonicalGeneratorDescent Aℛ j hj.gaugeLive`
  — row R5's content as a received guard.  NEW STATEMENT (review).
* ★★ `universalDoublyPinnedTauSupply : UniversalDoublyPinnedTauWordDescentSupply n` —
  **UNCONDITIONAL, every `n`**: under {normalizer pin, descent guard} the whole
  per-witness tau supply holds (span leg free under the pin, descent leg IS the guard).
  **Zero per-witness tau mathematics remains open behind the guards.**
* Keystone teeth: `s2Four_normalizerPinned` (`rfl`), ★ `s2Four_descentPinned` (the landed
  `s2Four_canonicalGeneratorDescent` — O-R5P would RE-FIRE at every landed witness),
  ★ `s2FourTwisted_not_descentPinned` (the guard EXCLUDES the χ-twist at an unembedded
  wrap value — teeth exactly where the normalizer pin has none), and the coherence
  re-derivation `s2Four_tauWordDescentSupply''`.
* **O-R5P (owner/orchestrator territory, the A-I.9 genre one field deeper)**: conjoin
  `DescentPinned` into `DeepTwistRealizationData` and `IFC5.CanonicalLadderLiveAt`.
  Direction is the same as A-I.9 (premise position → weakens `CapstoneHypotheses` →
  strengthens the conditional capstone); the keystone re-fires (`s2Four_descentPinned`);
  the defeating genre is excluded (`s2FourTwisted_not_descentPinned`).  Under it the tau
  boundary of both vartheta halves VANISHES via `universalDoublyPinnedTauSupply`.
  NOT enacted here — socket-body changes are A-I.9-genre owner calls, not this unit's.

## 5. ⚠ FLAGGED OPEN QUESTION (urgent, one level up — a candidate stop-line on the SIGNED surface)

The same χ mechanism plausibly reaches the vartheta ELEMENTS, not just the wrap class.
If at the keystone some `varthetaEl q s` (the `n̂(sq)·n̂(q)^{−s}` words; `Ladder.VarthetaRes`
demands their reads descend) has a NONZERO exponent vector, a coordinate character
refutes `VarthetaPerWitnessExporter` at the χ-twisted (pinned!) witness — hence
`UniversalPinnedVarthetaSupplier`, hence **`IFC0.DeepTwistField n` ITSELF through G10U's
landed converse `universalPinnedVartheta_of_deepTwistField`** — i.e. the signed
`deepTwist` capstone hypothesis would be unsatisfiable pre-O-R5P.  Mechanism sketch for
the follow-up unit: the greedy digit solves are bounded (`b(k) ∈ [0, e)`), so the letter
coordinates of `varthetaEl q s` are `b(sq) − s·b(q)` — bounded minus linear-in-`s` —
nonzero for large `s` unless `b(q) = 0` at every rung; at the keystone `q` is the level-3
use height with `towerNorm`-computable digits (C136t's decide-genre pins).  Either way
**O-R5P repairs both surfaces**: under the descent guard the exporter's demands flow from
the guard through the spanning theorem (every kernel element is a generator word whose
read then descends).  Entry points: `Ladder.VarthetaRes`/`HVarthetaRes`,
`useHeightFamily X 3`, `liftKerHom`, `arenaNormSection0.transport`.

## 6. Flagged for human review (trust boundary — new statements)

`DescentPinned`, `UniversalDoublyPinnedTauWordDescentSupply` (supplier-side interface
`Prop`s below the signed surface).  Constructions consumed by the refutation:
`coordFunctional`, `DeepTower.coordChar`, `DeepTower.exists_wrapChar` (all proved general
lemmas over the landed corpus).  OWNER ITEM (flagged, not enacted): O-R5P above (a
socket-body conjunct, same genre as the enacted A-I.9/O-TAU-2).

## 7. Verification record

* Per-increment `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10WrapPinned.lean`
  throughout; FINAL: exit 0, 0 errors, 0 warnings, 0 `sorry`; 15/15 `#print axioms`
  exactly Lean core (scripted check; non-core = NONE).
* `Uniformity/ChapI/I10PinnedBoundary.lean` re-verified after the comment-only update
  block (exit 0, footprints unchanged).
* `lake build Uniformity.ChapI.I10WrapPinned` — **Build completed successfully
  (8977 jobs), exit 0**; `lake env lean Uniformity/ChapI.lean` (aggregator, with the new
  import line) — exit 0.
* Repair log (mechanical only): (1) section variables used only in proofs need
  `include … in` before the docstring (TAU/RUNG's note, re-confirmed twice); (2) `omit
  [IsAdicComplete …]` illegal on `s2Four_normalizerPinned` (the core's `complete` field
  references it); (3) the twisted-tooth equalities must be stated at
  `(s2FourArisingCoreOf …).T.wrapClass` (not the defeq `(s2DepthFour …).wrapClass`) for
  the `rw`-chain to match `twistRealization_wrapValue`'s terms syntactically.
* Files: `leanfinal/Uniformity/ChapI/I10WrapPinned.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line;
  `leanfinal/Uniformity/ChapI/I10PinnedBoundary.lean` comment-only dated block;
  `leanfinal/scratch/R5P_probe.lean` (scratch, disposable); this verdict.  No other file
  touched; IFCG76 untouched; no git operation.
