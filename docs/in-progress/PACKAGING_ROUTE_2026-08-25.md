# U15 — the packaging route (final design decision)

Date: 2026-08-25
Status: **DECIDED — Route A (retype the packaging), with the Route C parameter
adjudication folded in; Route B (build μ₃) DEFERRED as a separately-scoped follow-on
campaign at the CORRECTED parameters (2,1,21).**
Elaboration authority: `leanfinal/scratch/U15_check.lean` (exit 0, zero errors/warnings,
every `#print axioms` row exactly `[propext, Classical.choice, Quot.sound]`).

## 1. Decision in one paragraph

`ChainRealization` (CC-13) is retyped: the node leg becomes the split-ambient
`SplitNodePointSource` (the SF-3 ripple U13 demanded), and the FGMN legs — together with
the record's `(e' f' u')` parameters — are REMOVED from the carrier and factored into a
standalone packaging map `FGMNSourceData + FGMNSourceLaws + KeyChain → FGMNCalculus`.
This is not a compromise but the shape the corpus already proves correct: CC-16's
`toCalculus` never consumed `node`, `receiver`, `normalizer`, or either compat field
(C130pk lines 201–224 read only `keys`/`fgmn`/`fgmnLaws`), and the socket view layer never
consumed `fgmn`, `fgmnLaws`, the `(e',f',u')` parameters, or any of the four evaluation
fields (grep-verified over C130vw/C130ar/C130pt/C130st/C130cr/C130th: zero occurrences of
`fgmn`, `coeffHom`, `valueOn`, `pointHgt_eval`, `coord`).  The carrier was a shotgun
marriage of two independent consumer feeds; both U13's `ev`-refutation and FD-0's
`lf`-refutation were the machine catching the marriage, not the feeds.  After the retype:
the I.10 sockets fire from the S2 landed material with NO `LegacyEvaluation` and NO
`LegacyFGMN` premise (conditional only on `w : S2LevelOneThreshold` and `IsAdicComplete`),
and the FIRST NON-VACUOUS, UNCONDITIONAL class discharge lands —
`Nonempty (FGMNCalculus (s2DepthOne h2 hq) 2 1 5)` — already elaborated end-to-end in the
scratch authority (`U15Check.s2_calculus_discharge`, Lean-core).

## 2. The Route C finding (adjudicated here): the depth-2 parameters were mis-anchored

The killed-U13-predecessor flag in `runs/wave-b/verdict_CC17.md` (orchestrator addendum,
2026-08-24: "whether that is (2,1,5) or (2,1,21) at the S2 chain must be traced … a wrong
parameter here would make the frontier bundle inhabitable-but-useless") was never
adjudicated.  **Adjudicated now, with machine pins**: U9's Q1 convention itself is
CORRECT, and under it the CC-17 instantiation chose the wrong depth-2 triple.

* The landed witness's stage data are `(e,f,u) = (2,1,1), (2,1,5), (2,1,21)`
  (`C97.s2Witness`; `u 3 = 21` is `rfl` — scratch §1).
* Per Q1 (the class at repo depth `r` is the calculus of the NEXT augmentation, keyed at
  `keyAt r`, data `(e_{r+1}, f_{r+1}, u_{r+1})`): the honest parameters are **(2,1,5) at
  depth 1** (the μ₁→μ₂ augmentation, key `Φ′` — exactly FD-0's landed records) and
  **(2,1,21) at depth 2** (the μ₂→μ₃ augmentation, key `Φ₂`).
* The consumers' own arithmetic enforces this: `gentow5w_two`/`gentow2_Bpp` demand
  `hfloor : e' * W.Econst 2 < u'` with `Econst 2 = 10` (rfl), so `u' = 5` gives `20 < 5` —
  **REJECTED** — and `u' = 21` gives `20 < 21` — **ACCEPTED** (scratch
  `depthTwo_floor_rejects_five` / `depthTwo_floor_accepts_u3`); `gentow2_A`'s
  `hκ : e₂f₂u₂ < u'` (= `10 < u'`) rejects 5 the same way.  The depth-1 consumer's floor
  `2 * Econst 1 = 4 < 5` ACCEPTS (2,1,5) (scratch `depthOne_floor_accepts_five`).
* Consequence: SG-1's `Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 5)` is a phantom
  target — no consumer's hypotheses can ever be satisfied at it, independent of FD-0's
  operator refutation.  Every future depth-2 statement at S2 must be typed `(2,1,21)`.
* Internal confession in CC-13 itself: `ChainRealization.grade_compat` ties
  `fgmn.nextValue g = node.pointHgt r x g` — the tower's OWN terminal valuation μ_r — while
  `fgmn`'s docstring declares `nextValue = μ_{r+1}`.  These agree only at the (r−1)-anchored
  reading, which is exactly what the landed model realizes
  (`s2SourceDataOne.nextValue = s2Hgt₂` is `rfl`, C130fd0:536) and what FD-1's
  `s2_grade_compat` proved definitionally.

## 3. Route comparison against the end-to-end criterion

| | Route A (retype) | Route B (build μ₃) as briefed | Route B corrected |
|---|---|---|---|
| I.10a/b sockets non-vacuous | **YES, now** — `ev`/`lf` deleted; fires from `s2Frontier.node`, conditional only on `w` + `IsAdicComplete` (scratch `s2CarrierV2`/`s2RealizedInputV2`) | no (still needs the `ev` split regardless) | no (same) |
| Class discharge non-vacuous | **YES, now, UNCONDITIONAL** — `Nonempty (FGMNCalculus (s2DepthOne) 2 1 5)` (scratch `s2_calculus_discharge`) | target `(s2DepthTwo) 2 1 5` is consumer-rejected (§2) — building it wins nothing | `(s2DepthTwo) 2 1 21` after ~20–30 nodes |
| GENTOW depth-2 consumers fire at S2 | not yet (needs the μ₃ instance AND the open supply rows `hnorm/hnormdeg/hnormz/hprev/htie`) | never (wrong parameters) | not immediately (same open supply rows remain) |
| Cost | 6 nodes + docs | ~25–35 nodes, wasted | ~20–30 nodes |

Honest Route-B estimate (the brief's question "re-run of the S2-source campaign one level
up, or cheaper?"): a genuine second campaign of the same genre, **~20–30 nodes** —
level-3 value/table family (NV/NP-genre, ~6–8; `Dcum 3 = 8`, tables over the same constant
field), the `R₃` graded/normalized operators (RP-genre, ~8–10; the Def 3.13 recursion goes
THROUGH the landed `R₂`-level operators, so they are ingredients, not just templates),
`KP(μ₃)` interface + laws (KP-genre, ~5–7), assembly/FD/SG-genre ~2–3.  Cheaper than
U13's original 30–45 only because the node-point/normalizer/stage-interface layers are now
level-general or reusable.  It is a campaign, not a packaging decision, and NOTHING in it
de-vacuifies the sockets — so it is sequenced AFTER Route A, at the corrected parameters.

Note also that even a genuinely-μ₃-level record cannot rescue the `LegacyFGMN` premise as
typed: `lf` is typed at `(2,1,5)`, and the μ₃ recipe grades are multiples of `u₃ = 21`, so
"Route B as written" (making the r=2-typed records satisfiable AS WRITTEN) is incoherent —
the parameters must be amended first, which is the §2 adjudication.

## 4. The retyped shapes (elaborated in `scratch/U15_check.lean`; do NOT apply — the
orchestrator enacts through the node plan)

### 4.1 CC-13 (`C130fg.lean`) — `ChainRealization`

```lean
-- BEFORE: ChainRealization (W) (Kt) [Field Kt] (L) [Field L] [Algebra Kt L] (e' f' u' : ℕ)
--   with fields receiver keys normalizer node(un-split) fgmn fgmnLaws grade_compat letter_compat
-- AFTER (scratch name ChainRealizationV2; land under the original name):
structure ChainRealization (W : DeepTower.{0, uKt} F H₀ hpin r)
    (Kt : Type uKt) [Field Kt] (E : Type uE) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L] where
  receiver : TerminalReceiver F H₀ hpin r W Kt
  keys : KeyChain W
  normalizer : LaurentNormalizer W
  node : SplitNodePointSource (L := L) W E receiver keys
```

`E` as a PARAMETER (recommended: visible conditionality, no dependent projections); the
field-bundled variant (`ChainRealizationV2b`, `E : Type uE` + `[fieldE : Field E]`) also
elaborates and is the fallback if the leanspec I.10 binder blocks fight the extra
existential later.  `SplitNodePointSource` (+ `legalPoint`/`legalPoint_mem`/
`stageCarrier`) moves verbatim from C130s17 to the carrier skeleton (new small file
`C130k2.lean` imported by C130fg, to avoid touching landed C130k content; C130s17 keeps
`abbrev`-compatibility re-exports).  The four deleted legs are NOT lost: `fgmn`/`fgmnLaws`
live standalone (they already do — `FGMNSourceData`/`FGMNSourceLaws` are independent
structures); the two compat fields live where they are already landed and PROVEN — the S2
bundle `S2SourceFrontier.grade_compat`/`letter_compat` (FD-1) — and a future general
"anchored realization" record can re-bundle them when a second instance exists.

### 4.2 CC-16 (`C130pk.lean`) — the factored packaging map

```lean
@[implicit_reducible] def fgmnCalculusOf (K : KeyChain W) {e' f' u' : ℕ}
    (S : FGMNSourceData W K e' f' u') (hL : FGMNSourceLaws W K e' f' u' S) :
    FGMNCalculus W e' f' u' := ...   -- field-for-field C130pk's toCalculus, minus the carrier

theorem fgmn_model_calculus_nonempty ... : Nonempty (FGMNCalculus W e' f' u') :=
  ⟨fgmnCalculusOf K S hL⟩
```

`ChainRealization.toCalculus`/`chainRealization_calculus_nonempty` are retired (their
docstrings re-point here; no consumer outside C130s17/C130sg — grep-verified).

### 4.3 `RealizedInput` (`C130in.lean`) — binder-only diff

Drop `{e' f' u'}`, add `{E}` (scratch `RealizedInputV2`); the five fields are byte-identical.

### 4.4 CC-18 (`C130s18.lean`) — socket bodies

In `LadderRealizationData`/`DeepTwistRealizationData`: replace `∃ (e' f' u' : ℕ) … (Aℛ :
ChainRealization … e' f' u')` by `∃ (E : Type uE) (_ : Field E) (Aℛ : ChainRealization
core.T Kt E L)`; the three/four view conjuncts are unchanged.  The S2 gate theorems drop
`ev`/`lf`.  This is the LAST cheap moment for this amendment: the leanspec I.10a/b re-sign
is gated on these bodies and has not happened yet.

### 4.5 CC-17 (`C130s17.lean`) and SG (`C130sg.lean`)

* `toChainRealization ev lf` → `toCarrier` (no premises): receiver/keys/normalizer from
  `s2RepositoryRealization`, `node := S.node`.
* `calculusNonempty ev lf : Nonempty (FGMNCalculus (S2DepthTwo …) 2 1 5)` → the HONEST
  anchored discharge `s2_calculus_discharge : Nonempty (FGMNCalculus (s2FgmnAnchor h2 hq)
  2 1 5)` (scratch §2; unconditional — not even `w`).
* `realizedInput`/`s2RealizedInput` drop `ev`/`lf` (scratch `s2RealizedInputV2`: all three
  dictionary fields still `rfl`).
* `LegacyEvaluation`/`LegacyFGMN`/`withLegacy` + the un-split `NodePointSource` are KEPT,
  marked QUARANTINE (they are the refutation record); C130sg's two `IsEmpty`/emptiness
  theorems keep their statements verbatim.
* C130sg's funnel stages 1–4 re-run `ev`/`lf`-free; the socket stages become the first
  non-vacuous I.10a/b-shaped statements of the campaign (conditional on `w` +
  `IsAdicComplete` only).

## 5. Node plan (Route A; Sonnet, 30–45 min each; serial where marked)

| node | files | work | gate |
|---|---|---|---|
| PK-1 | NEW `C130k2.lean`; `C130fg.lean`; `C130in.lean` | move `SplitNodePointSource`+helpers; retype `ChainRealization` (§4.1); `RealizedInput` binders (§4.3) | `lake env lean` both; AxChk Lean-core |
| PK-2 (after PK-1) | `C130pt/st/cr/th/ar/vw.lean` | binder ripple un-split→split (signature-only; proofs expected byte-stable — the consumed fields are identical) | file-by-file green; view lemma statements otherwise byte-unchanged |
| PK-3 (after PK-1) | `C130pk.lean` | `fgmnCalculusOf` + `fgmn_model_calculus_nonempty` (§4.2); retire the carrier-typed pair; teeth | AxChk; no instance declared |
| PK-4 (after PK-2/3) | `C130s17.lean` | §4.5 first half: `toCarrier`, quarantine marking, `ev`/`lf` deletion in the input path | SF-4 tooth re-run |
| PK-5 (after PK-4) | `C130s18.lean` | §4.4: socket bodies + applications + S2 gate + twist audit re-run | non-swallowing grep-tooth (rg exit 1) |
| PK-6 (after PK-5) | `C130sg.lean` | funnel `ev`/`lf`-free; ★ `s2_calculus_discharge`; emptiness theorems retained | full funnel Lean-core; `lake build Uniformity.ChapC Uniformity.ChapI` |
| PK-7 | docs | PROJECT_STATE; review-list rows of §6; note the leanspec I.10 re-sign now targets the §4.4 bodies | — |

Route B follow-on (deferred; open a separate blueprint when scheduled): the μ₃ campaign at
`FGMNSourceData (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 21`, ~20–30 nodes (§3),
its discharge plugging into PK-3's `fgmn_model_calculus_nonempty` with zero new packaging.

## 6. Review-list rows (flagged, not fixed here)

1. **Depth-2 parameter amendment (print-read-adjacent).** Everywhere the S2 depth-2 class/
   record is mentioned at `(2,1,5)` — CC-17 verdict, `LegacyFGMN`'s typing, SG-1's
   `calculusNonempty` target — the honest triple is `(2,1,21)` (§2, machine-pinned).  U9 Q1
   itself is CONFIRMED correct (three independent legs: consumer floor arithmetic, the
   witness's `u 3 = 21`, CC-13's own `grade_compat` typing).
2. **The `hprev`/`hcop` clearing tension.** RP-6's landed `PrevGrade` realization is
   evenness, and `¬S2PrevGrade 5 ∧ ¬S2PrevGrade 21` (scratch §1) — so `hprev :
   I.PrevGrade u'` is unsatisfiable at ANY evenness-realized instance whose `u'` passes
   `hcop`.  U14's own note says the intended μ₃ instance discharges `hprev` under the
   PRECEDING-group clearing `β̂ = e(μ₂)β`; which clearing the μ₃ operators use is
   OPEN-DICT-2 work that must be decided BEFORE the Route-B campaign fixes its `nextValue`.
   Also: at `f' = 1` the `ratio_power_law` induction never consumes `hprev` — a candidate
   A-C.15 re-sign could fence `hprev` by `2 ≤ f'`, unblocking depth-1 S2 consumption.
3. **NODE C.90's truncation family (leanspec).** `gentow5_key_certificate` binds
   `I : ∀ i ≤ r, FGMNCalculus (W.trunc i hi) e' f' u'` with ONE fixed triple across all
   truncations; per Q1 each truncation's honest data differ (at S2: `(2,1,5)` at `i=1`,
   `(2,1,21)` at `i=2`), so the current signature is satisfiable only for uniform-data
   towers.  Print-read-adjacent; needs a per-level family `(e'ᵢ, f'ᵢ, u'ᵢ)` at its next
   re-sign.
4. **`gentow5w_one_shape`'s remaining holds at the landed instance**: `htie`
   (OPEN-LETTERS) and row 2's `hprev` — the depth-1 consumer cannot fire until both move.

## 7. What becomes non-vacuously true after PK-1..6 (the honest bottom line)

* Both I.10-shaped socket applications and the I.10b→I.10a refinement, at the concrete
  `keyAt 2 + 1` occurrence, conditional on exactly `w : S2LevelOneThreshold` (the one open
  faithfulness datum) + `IsAdicComplete` — no provably-empty premise anywhere on the path.
* `Nonempty (FGMNCalculus (s2DepthOne h2 hq) 2 1 5)` — unconditional, Lean-core: the class
  is a genuinely inhabited hypothesis carrier for the first time (C92-vacuity closed at a
  concrete anchor; `fgmn_calculus_exists` stays undeclared, per the standing adjudication).
* NOT claimed: any GENTOW consumer conclusion at S2 (blocked by §6 rows 2/4 and, at depth
  2, by the deferred μ₃ campaign).
