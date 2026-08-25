# DT2 verdict — definitional twins, batch 2

New file: `leanfinal/Uniformity/ChapC/C141defs.lean` (484 lines).

## Curation method

`python3 spec/census_driver.py` from the repo root, chapter C section (356 signed names;
113 UNLANDED). Filtered to `[def;...]`/`[inductive;...]`-kind rows (43 total: 42 `def` +
1 `inductive`; no `structure`-kind rows were UNLANDED in chapter C — the one remaining
UNLANDED `structure`-shaped item, `DescentState`, is not itself flagged UNLANDED by the
census and was not touched). Cross-checked every candidate's leanspec context for
STRUCK/REFUTED/superseded markers, checked every referenced identifier against leanfinal,
and excluded FGMNCalculus-adjacent items per the task's own carve-out.

Build check per declaration: `cd leanfinal && lake env lean Uniformity/ChapC/C141defs.lean`
— **zero errors, zero warnings**, `#print axioms` run on every landed name (see Verification
below). Every item below was `diff`-verified byte-for-byte against its cited leanspec line
range (script check, reported per item; all passed with empty diffs).

## LANDED (40 census-flagged names + 2 auxiliary carried defs)

* **`complementConst`** — leanspec `ChapC.lean:1610–1612` (NODE C.36(a), the complement
  constant `c_g`). Deps: `KeyFrame` (C01), `LevelDatum` (C09), `dvSupp` (C06), `blockFactor`
  (C35) — all landed.
* **`γg`** — leanspec `:1695–1697` (NODE C.39, the complement's own `K₂`-residue read). Deps:
  `dv2Res` (C38a), `blockFactor` (C35) — landed.
* **`pinHeight`** — leanspec `:1701–1703` (NODE C.39, the PIN height at the side's start
  index). Deps: `dv2Pin` (C11), `dv2SideMin`/`dv2SideSet` (C38a) — landed.
* **`refineDom`, `refineCod`** — leanspec `:2161–2168` / `:2170–2176` (NODE C.57, R2b's
  domain/codomain coefficient-box strata). Deps: `TowerDatum`/`TowerDatum.D₂` (C42),
  `Coeff`/`proj`/`monicPoly` (Density/LocalData), `towerLocus` (C51), `composedKey` (C43),
  `towerLabel`/`TowerDatum.levelDatum` (C44), `dv2SideSet`/`dv2ResPoly`/`dv2Pin` (C38a/C11),
  `k2DigitLift` (C56a) — all landed and cross-checked signature-for-signature.
* **`FgmnResidualMulStatement`** — leanspec `:3991–4046` (the docstring) / `:4027–4046` (the
  def itself). This is NODE C.66's A-C.6 REDRAFT: the named `[cite:FGMN]` Prop that replaced
  the machine-refuted A-C.1 draft (`ChapC.lean:3958–3989` records the refutation and names
  this redraft as its replacement — it is NOT itself marked struck/refuted/superseded).
  Landed here as a bare, universe-polymorphic `Prop`-valued `def` (`.{v}`), wired to no
  axiom. **Honest disclosure of the nuance**: leanspec's own docstring says "on signature
  this becomes, and ONLY becomes, `axiom fgmn_residual_mul : FgmnResidualMulStatement` —
  nothing is declared here" — i.e. the drafting-time plan was to axiomatize THIS name. The
  actual gate-(b) signature (`Uniformity.ChapC.C66.fgmn_residual_mul`, owner-signed
  2026-08-17, already landed) instead inlines an equivalent statement at a fixed `Type`
  rather than quantifying over `Type v` and referencing this def — a design choice made at
  landing time, not a repudiation of this Prop. The two now coexist: `fgmn_residual_mul`'s
  axiom carries its own inlined type and does not reference `FgmnResidualMulStatement`;
  landing this name here is a purely definitional record of the redraft's exact signed text,
  closing the one remaining UNLANDED def-kind node of C.66's drafting history, and creates
  no axiom, no inconsistency, no strengthening. `set_option linter.unusedVariables false in`
  added (the twelve source hypothesis binders are threaded but not referenced in the
  conclusion body, exactly as signed — same situation as DT1's `ClassSizeSupplyData`).
* **`slotIdxN`, `twistExpN`, `slotWindowN`** — leanspec `:4062–4068` (C.16/C.18's numeral
  mirror generators; no signature, defect D1 — audit-script defs, not blueprint
  declarations). Self-contained `ℕ`/`List ℕ` arithmetic.
* **`shiftN`, `cocycleN`** — leanspec `:4070–4072`. **Not on the census's UNLANDED list**
  (a `private def shiftN`/`private def cocycleN` pair already exists in
  `Uniformity.ChapC.C28.lean`'s `NumericRegression` section, which is what the census's
  name-only grep matches) — but `private` makes those inaccessible outside `C28.lean`, and
  `c28_grid` below needs them. Carried here as leanspec's own separate top-level (non-`private`)
  mirrors, verbatim, for the same reason DT1 carried `pmul`/`padd`/`psmul` alongside
  `Phi1`/`Phi2`/`Phi3`: without them the consuming def does not elaborate. Distinct
  declarations from C28's private ones (Lean's `private` hygiene means no name clash).
* **`c16_grid`** (`:4074–4087`), **`c18_grid`** (`:4091–4102`), **`f9mul`** (`:4119`,
  reusing the already-landed `Uniformity.Density.Weld.F9` carrier from
  `Uniformity/ChapF/GateFields.lean:108` instead of re-declaring leanspec's local `abbrev
  F9` — the census already classifies that abbrev as `CARRIER`/satisfied), **`c28_grid`**
  (`:4139–4153`), **`c30_grid`** (`:4163–4175`), **`c31_floor_grid`** (`:4179–4192`),
  **`jumpDropAsSigned`**, **`jumpDropCounterCount`**, **`jumpDropRepaired`**,
  **`jumpDropRepairedCount`** (`:4196–4237`), **`c32_check`** (`:4241–4247`), **`c50_grid`**
  (`:4252–4267`), **`clipDivergesAt`** (`:4285–4290`), **`c55_grid`** (`:4307–4320`),
  **`c10_grid`** (`:4339–4352`) — all self-contained `ℕ`/`List`/`Bool`/`Int` arithmetic
  audit-script mirrors, no chapter-C vocabulary needed, no signature (defect D1).
* **`v2`** (`:4381–4383`) and **`isPure2`** (`:4392–4398`) — C.97's `2`-adic valuation and
  one-sidedness test on `List ℤ`. `v2` is the item DT1's own verdict flagged as "NOT
  landed... recorded here rather than silently included" — landed now.
* **`vtheta`, `vxi`, `vzeta`, `vPhi1_at_xi`, `vPhi1_at_zeta`, `vPhi2_at_theta`,
  `vPhi2_at_zeta`** (`:4405–4411`) — the C.97 tower-ladder rational scalars.
* **`c16_unique_grid`** (`:4433–4442`), **`c18_iff_grid`** (`:4446–4455`), **`c41_grid`**
  (`:4459–4472`), **`c41_nsmul_grid`** (`:4476–4487`) — further C.16/C.18/C.41 grid checks.
* **`gateC_q3_budget_w0`, `gateC_q3_budget_w5`, `gateC_q3_htSpot_atN6`** (`:4515–4517`) — the
  `q = 3` companions of `Uniformity.ChapC.C123`'s already-landed `q = 2` rows
  (`gateC_q2_budget_w0` etc.); `gateC_frame3_budget_w0` (the third-frame companion) is
  likewise already landed in `C123.lean` and was not re-curated here.

None of the leanspec `#guard`/`#eval` self-test lines were carried (per the DT1 precedent:
`C140defs.lean`'s docstring explicitly excludes "the later `#eval`/`#guard` rows"). Every
landed name's `#print axioms` footprint is Lean-core-only — a subset of
`{propext, Classical.choice, Quot.sound}` (structure/`Prop`-formation and `Classical.choice`
in the `open Classical in` bodies pulled in transitively via `blockFactor`/`dv2Res`; the pure
arithmetic defs are axiom-free or `[propext, Quot.sound]`-only from `Bool`/`decide`
elaboration). No `sorry`, no new axiom, no `unsafe` declaration.

## SKIPPED

* **`DescentStep`** (`inductive;L1747`) and **`NS7TerminationStatement`** (`def;L1768`) —
  already adjudicated by DT1 (`runs/wave-b/verdict_DT1.md`): the A-C.1 draft is
  machine-refuted and explicitly struck in leanspec itself (`ChapC.lean:1777–1796`:
  *"kept for the record and MUST NOT BE CONSUMED"*); the A-C.6 redrafts `DescentStepR` /
  `NS7TerminationStatementR` are already landed in `Uniformity.ChapC.C94`. Re-confirmed
  still struck at their current line numbers; not re-landed.
* **`GENTOW5W`** (`def;L3764`) — FGMNCalculus-adjacent, explicitly out of scope per the
  task's carve-out. `Uniformity.ChapC.C130pk`'s own module docstring ("Deliberately NOT
  here") lists *"any `FGMNCalculus`-conditional §10 theorem (the GENTOW2 supply layer stays
  in leanspec until its own transcription nodes)"* — `GENTOW5W`'s signature
  (`(I : FGMNCalculus W e' f' u') : Prop`) is exactly that layer. Deferred to its own future
  transcription node, per C130pk's own plan; not landed here.

No item was skipped for a missing leanfinal dependency — every referenced identifier in the
40 landed census-flagged names resolves to an already-landed leanfinal declaration (verified
above, per item).

## Verification

```bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal && lake env lean Uniformity/ChapC/C141defs.lean
```

Succeeds with zero errors and zero warnings. `#print axioms` was run for all 42 landed
declarations (40 census-flagged + `shiftN`/`cocycleN`); every footprint is a subset of
Lean core `{propext, Classical.choice, Quot.sound}` — no custom axiom anywhere. Every
declaration's body was `diff`-verified byte-for-byte (via `sed`-extracted line ranges) against
the cited leanspec range; all diffs were empty.
