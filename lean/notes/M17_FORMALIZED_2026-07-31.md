# M17 FORMALIZED (2026-07-31) — the (REG-p) failing-prime set is FINITE, exactly characterized

Unit: formalize the dual-proved open-math result M17-regp-density into
`lean/LeanUrat/MovesU/RegPFinite.lean` (NEW file, 488 lines, 0 sorry, Lean-core).
Authorization: Asvin 2026-07-31 ("Sign-off granted on all 21 items as preferred,
execute the queue") + the /goal standing authority. Scope fence respected: one
new file in `LeanUrat/MovesU/` + this note; NO existing statement touched
(`RegP`, `RegData`, `RegPin`, `theoremU` all consumed as-is); MovesC/HC1/HC2/
MovesD untouched.

## Dual provenance (the proof being formalized)

* **Fable attempt** `lean/notes/openmath/M17-regp-density_fable.md`
  (VERDICT: PROVED, 2026-07-31). Lemma 0 (the dictionary: RegP at a pinned
  record ⟺ no pool value in the zero/pole set B; the act-agreement conjunct is
  FREE given definedness; instance-independence), Lemma 1 (B finite), Lemma 2
  (prime-power escape), Theorem A (failing set = {p : ∃ δ ∈ Δ, p^δ ∈ B}, exact,
  finite), Theorem B (DetHyp is a corpus theorem — `rs3_det_symbolic`).
* **Codex twin** `/tmp/openmath/M17-regp-density_codex.jsonl` (independent
  model, fresh context, launched from the neutral brief
  `lean/notes/openmath/M17-regp-density_brief.md`). Its Lemma 1
  ("Active-value equality introduces no exceptions") = `RegPin.act_agree`
  here; its Theorem 1 (RegP D ⟺ p ∉ ℬ, exact, both directions) =
  `regP_iff_pool_avoids`/`not_regP_iff_exists_depth`/`regP_failing_eq` here;
  its Theorem 2 (ℬ finite + effective) = `regP_failing_finite` +
  `pow_hits_finite` here. The two proofs agree on every load-bearing step
  (act-freeness; poles/zeros as the only failure channels; the finite-roots +
  prime-power-escape assembly); the Lean file follows the shared skeleton.

## What is now MACHINE-CHECKED (all in `LeanUrat/MovesU/RegPFinite.lean`)

All declarations verified `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (Lean-core exact, 2026-07-31, this session; 14/14 checked).
Per-file gate `lake env lean` clean (0 errors, 0 warnings); targeted
`lake build LeanUrat.MovesU.RegPFinite` green (8702 jobs).

* `UCarriers.detHyp` — **M17 Theorem B wired**: every carrier pack `C :
  UCarriers n` satisfies `MovesS.DetHyp C.T C.RB C.hK`, by
  `Kernels.detHyp_of_escape_infinite` (= `MovesS.rs3_det_symbolic`, KA9's
  consumer face) at the chain's own `PrimePools`/`prime_sub`/`prime_base`/
  `pools_e0`. Branch (A-ii) of the note's Theorem A never fires at a carrier.
* `RegPin.act_agree` — **the act-agreement FREENESS lemma** (deliverable 3):
  at a pinned record, `DefinedAt g q₀ → g.eval (RingHom.id ℚ) q₀ = D.act g q₀`
  (`act_pin` + the definitional equality `MovesS.evalAt = RatFunc.eval`).
  So (r2) can only fail through a pole, never through the ACT seam.
* `RegData.detFull` + `RegP.detFull_clause` + `RegP.detFull_ne_zero` — (r1)'s
  full determinant named; Lemma 0(ii)'s contrapositive (RegP D → det ≠ 0 in
  ℚ(q), via the junk-evaluation of the zero function at p ∈ Pool).
* `RegPin.detFull_eq` / `RegPin.detFull_ne_zero` — the pin transports the
  abstract determinant to the real Φ_e (the `RegPin.detHyp` submatrix calc,
  factored), hence nonzero under DetHyp.
* `blockZeroPole`, `RegData.zeroPoleSet` — **Theorem A's B as a `Finset ℚ`**
  (Lemma 1's finiteness carried BY TYPE): per block, roots of num/denom of
  det(1 − K_e) plus the denominator roots of every `entryList` member.
* `regP_iff_pool_avoids` — **THE DICTIONARY, exact** (single record):
  `RegP D ↔ ∀ q₀ ∈ D.Pool, (q₀ : ℚ) ∉ D.zeroPoleSet`, hypotheses
  (P : RegPin C D) (hdet : DetHyp). ⟹ is pin-free; ⟸ consumes the pin exactly
  twice (act freeness; Φ ≠ 0 for the numerator-value clause).
* `not_regP_iff_exists_depth` — **the ∃δ, p^δ ∈ B form** (deliverable 2):
  `¬ RegP D ↔ ∃ δ ∈ D.depthSet, ((p ^ δ : ℕ) : ℚ) ∈ D.zeroPoleSet`.
* `RegPin.depth_ne_zero`, `pow_hits_finite` — **M17 Lemma 2** (prime-power
  escape): finite B, finite positive Δ ⟹ {p | ∃ δ ∈ Δ, (p^δ : ℚ) ∈ B} finite,
  every member ≤ the ceiling-sup of B. (Stated for all ℕ bases; primality
  not needed.)
* `realEntryList` + `RegPin.entryList_eq` — **Lemma 0's (r2) ROSTER IDENTITY**:
  the abstract `entryList` IS the p-independent real entry list E(e) — all
  seven families transported (`K_pin`, `bterm_pin`, `bsplit_pin` (under
  DetHyp), `Jcell_pin`, `iota_pin`, `W_pin`, and the β-legs via
  `depth_pin` + `legEquiv` + `legSt_pin` + `betaLeg_pin` with
  `powSubst d = powSubst ⟨↑d, d.pos⟩` closed by structure eta).
* `realZeroPoleSet` + `RegPin.zeroPoleSet_eq` — **the p-UNIFORM real locus**:
  B(D) = B(instance data) for every pinned record at every prime.
* `regP_iff_of_pins` — **Lemma 0(iii), instance-independence**: two pinned
  records at the same prime have the same (REG-p) truth value.
* `regP_failing_eq` — **M17 THEOREM A, exact characterization, family form**
  (deliverable 1): for `Dfam : ∀ p, p.Prime → RegData p` with pins
  `Pfam : ∀ p hp, RegPin C (Dfam p hp)`,
  `{p | ∃ hp, ¬ RegP (Dfam p hp)} = {p | p.Prime ∧ ∃ δ ∈ Δ, (p^δ : ℚ) ∈ B}`
  with Δ = the ℕ-image of `MovesS.consumedDeltas C.T C.Fam` and
  B = `realZeroPoleSet C hdet`. EXACT equality, both inclusions.
* `regP_failing_finite` — **M17 THEOREM A, finiteness**: that set is FINITE.
* `regP_cofinite` — **the hypothesis-free corollary** (Theorem A + Theorem B):
  `∃ S : Set ℕ, S.Finite ∧ ∀ p hp, p ∉ S → RegP (Dfam p hp)` — theoremU's one
  per-prime hypothesis holds at every prime outside a finite set (density-1
  applicability), with NO hypotheses beyond the carrier pack + the pinned
  family (the DetHyp witness is `C.detHyp`).

## Honesty ledger (what is NOT in this file)

* **Corollary U at `theoremU`'s signature** (the note's §5): not restated —
  it is one `fun p hp hnot => (theoremU …).2.2 … (hcofinite …)` composition
  away, but carrying theoremU's full 13-bare-parameter signature into this
  unit adds no mathematical content. `regP_cofinite` is the exact per-p
  premise feed. theoremU itself remains CONDITIONAL exactly as documented
  (wave-4 boundary; see U10's docstring) — nothing here changes that.
* **The note's Theorem C** (failure channels confined to determinant-numerator
  vanishing at composite depths M̂; the localization/denominator-class
  bookkeeping) and the **cardinality bound** |failing| ≤ #(B ∩ prime powers):
  NOT formalized (the Lean form carries only finiteness + the ceiling-sup
  bound inside `pow_hits_finite`'s proof). Open for a future unit.
* **Sharpness** ({2} is realized as a failing set): the compiled countermodel
  `MovesU/BridgeB15a_r2Neg.lean` already witnesses (r2)-failure at p = 2 at
  schema level; the tie "its `zeroPoleSet` characterization yields exactly
  {2}" is numerically verified (fable note §7 + executed sympy checks) but
  not Lean-checked. NOT formalized here.
* **Vacuity note**: `regP_failing_eq`/`regP_failing_finite`/`regP_cofinite`
  quantify over a SUPPLIED pinned family — exactly theoremU's own `inst`
  shape (every `UInstance` carries `D` + `Dpin`); whether a real pinned
  family exists at every prime is the standing instance obligation (owner:
  the bridge campaign, `bridgeRegData`/`bridgeRegPin` at BP1), not this unit.
* `PROJECT_STATE.md` fold-in: pending (owner: orchestrator) — this unit's
  scope fence was MovesU/ + notes only.

## Build & verify record

* `lake env lean LeanUrat/MovesU/RegPFinite.lean` — clean (2026-07-31).
* `lake build LeanUrat.MovesU.RegPFinite` — "Build completed successfully
  (8702 jobs)".
* `#print axioms` on all 14 public declarations — Lean-core exact.
* Imports added (new file only): `LeanUrat.MovesU.DefsLedger`,
  `LeanUrat.MovesU.BridgeB4_legRosterFintype` (the `LegRoster` Fintype),
  `LeanUrat.Kernels.KA9` (the DetHyp consumer face). No module outside MovesU
  imports MovesU (unchanged).
