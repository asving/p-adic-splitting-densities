# GR-3 ×2 / GR-4 DISPOSITION PRICING (synthesis pass 5, queue item 4)

Unit: analysis-only (NO .lean file touched). Artifacts priced for the orchestrator's
owner call: route (a) "pin frames into ReadHyps" vs route (b) "keep history-keyed
graded_read + displayed obstruction", plus the p ≠ 2 countermodel forge (F5 species:
stage forge). Everything below verified against HEAD (ea9f615) on 2026-08-08.

## 0. The residue being adjudicated (exact)

Three E-phase sorries, all in B2D, all one obstruction:

| # | decl | file:line | statement shape |
|---|------|-----------|-----------------|
| 1 | `GR3_keyResidual_pinned` | `lean/LeanUrat/B2D/GR3_keyResidual.lean:85-88` | `(hlift : IsNodeLift ν Φ') (R : ReadHyps ν) : ν.σ.R Φ' = T ν.mhat * toLaurent ν.ψ` |
| 2 | `GR3_keyResidual` | `lean/LeanUrat/B2D/GR3_keyResidual.lean:95-98` | same binders `: ∃ mh, ν.σ.R Φ' = T mh * toLaurent ν.ψ` |
| 3 | `graded_read` | `lean/LeanUrat/B2D/GR4_gradedRead.lean:85-98` | same binders + `(Mpar : GenuineStageModel ν.σ)` `: (K1) ∧ (K2-Laurent) ∧ (K2-graded)` |

The obstruction (GR-3 module docstring + N-GR1 check N5): `ReadHyps` forces the READ
pins `ν.e = 1, ν.t = 0, m̂ = 0` (`GR0b.readHyps_e_eq_one` etc.) but pins NOTHING about
the FRAME triple `(ν.σ.e, ν.σ.s, ν.σ.t)`. At an abstract frame with `σ.e ≥ 2` the
position lattice compresses: present slots sit on `κ ≡ g (mod σ.e)`, so `ψ = φ(z^σ.e)`
(a gap polynomial, irreducible whenever `p ∤ σ.e`, e.g. `z²+1`/F₃) and
`σ.R Φ' = T^c·toLaurent φ` with `deg φ = g/σ.e < g` — both the pinned and the ∃-form
FAIL (`toLaurent` injective; `T`-shifts preserve support gaps). So the three frozen
statements are believed FALSE at the abstract carrier (mathematical countermodel at
p = 3; not yet compiled). The exact missing input is the frame pins
`(ν.σ.s, ν.σ.t) = (1, 0)` — supplied at interior coherent reads by
`GR0b.frame_level_of_history` (GR0b_suppliers.lean:206), where `child_e` ties
`σ.e = ν.e = 1`, and NOT derivable from `ReadHyps` at the abstract carrier.

Proved forms already on file (Lean-core): `GR3_keyResidual_level` (+`'`),
`graded_read_level`, `graded_read_of_history` — the frozen conclusions WITH the two
frame pins, and the history-keyed consumer-ready discharger.

## 1. ROUTE (a) — pin the frame into `ReadHyps`

Mechanism: add the frame pins as `ReadHyps` FIELDS. Then every `R : ReadHyps ν` binder
supplies them, the σ.e-compression configuration is excluded by the pack itself, and
the three frozen sorry bodies become one-liners from the existing `_level` proofs. The
three THEOREM SIGNATURES stay byte-identical (they bind `R : ReadHyps ν`); the
statement change is entirely in the STRUCTURE (a §4 frozen-interface change — fence
(vii): campaign-owner adjudication, which is exactly this pricing's purpose).

### (i) Exact statement diffs

**Diff 1 — the structure (GRDefs.lean:68, `ReadHyps`).** Two new fields appended
(the two-field form matches `frame_level_of_history`'s output exactly; the one-field
alternative `hσe : ν.σ.e = 1` also works — then `σ.t = 0` via `Stage.he1t` and
`σ.s = 1` via `Stage.hbez` inside proofs — but re-derives at every use site).

BEFORE (fields, unchanged part elided):
```lean
structure ReadHyps (ν : Node p F) : Prop where
  hscale : (ν.h : ℤ) = (ν.e : ℤ) * ν.σ.w ν.σ.Φ
  hbez : (ν.e : ℤ) * ν.s + (ν.h : ℤ) * ν.t = 1
  hbezCanon : 0 ≤ ν.t ∧ ν.t < (ν.e : ℤ)
  hψmonic / hψirr / hψdeg / hψ0 / hRmul / hRlt / hRadd / hRΦ  -- as at HEAD
```
AFTER (append):
```lean
  /-- the frame level pin σ.s = 1 (GR-3/GR-4's exact residue; supplied at interior
      coherent reads by `GR0b.frame_level_of_history`). DISPLAYED-HYPOTHESIS at a
      bare node. -/
  hσs : ν.σ.s = 1
  /-- the frame level pin σ.t = 0 (ditto). -/
  hσt : ν.σ.t = 0
```

**Diffs 2-4 — the constructor/suppliers** (the ONLY anonymous-constructor site is
`readHyps_of_node`; everything else routes through it):

`GR0_readHyps.lean:97 readHyps_of_node` — BEFORE:
```lean
theorem readHyps_of_node (ν : Node p F)
    (hscale : (ν.h : ℤ) = (ν.e : ℤ) * ν.σ.w ν.σ.Φ)
    (hψ0 : ν.ψ.coeff 0 ≠ 0) : ReadHyps ν where
```
AFTER (two binders + two `where` lines added):
```lean
theorem readHyps_of_node (ν : Node p F)
    (hscale : (ν.h : ℤ) = (ν.e : ℤ) * ν.σ.w ν.σ.Φ)
    (hψ0 : ν.ψ.coeff 0 ≠ 0)
    (hσs : ν.σ.s = 1) (hσt : ν.σ.t = 0) : ReadHyps ν where
  ...
  hσs := hσs
  hσt := hσt
```

`GR0_readHyps.lean:117 readHyps_of_node_level` — gains the same two binders, passes
through (the level READ configuration `e = 1, h = σ.h` does NOT supply frame pins at a
bare node — they stay displayed there; honest).

`GR0b_suppliers.lean:93 readHyps_of_node'` — gains the same two binders, passes
through (its docstring's "10/11 fields supplied, `hscale` sole residue" becomes
"10/13 supplied; residue = `hscale` + the two frame pins" — matching GR-0's table
discipline).

**Signature-diff count: 4** (1 structure + 3 supplier theorems). No other signature
in the repo changes.

**Body-only edits (signatures byte-unchanged): 2.**
* `GR0b_suppliers.lean:168 readHyps_of_history` — body supplies the two new fields
  from `frame_level_of_history hcoh hi hprev he1` (SAME hypotheses already in scope;
  no signature change).
* `_interior`/`_rec` variants (GR0b:180, 191) — call through, untouched.

### (ii) Every consumer that must change (exhaustive grep, 2026-08-08 @ ea9f615)

Use sites of the THREE sorry declarations: **NONE**. `grep -rn "GR3_keyResidual\|graded_read"
--include=*.lean LeanUrat/` outside their home files hits ONLY docstrings
(GRDefs.lean:19, GR0_readHyps.lean:19/48, GR0b_suppliers.lean:40,
GR1_equalWeights.lean:160). Additionally NO file imports `B2D/GR3_keyResidual.lean` or
`B2D/GR4_gradedRead.lean` (import grep: zero hits) — the sorryAx is contained in two
leaf modules.

`ReadHyps`-binding declarations (all inside B2D; field ADDITIONS break only
constructor sites, not projection sites):
| decl | file:line | edit needed |
|---|---|---|
| `readHyps_of_node` | GR0_readHyps.lean:97 | YES — constructor site (diff 2) |
| `readHyps_of_node_level` | GR0_readHyps.lean:117 | YES — pass-through binders (diff 3) |
| `readHyps_of_node'` | GR0b_suppliers.lean:93 | YES — pass-through binders (diff 4) |
| `readHyps_e_eq_one` / `_h_eq` / `_t_eq_zero` / `_mhat_eq_zero` | GR0b:104/113/122/131 | NO — projections only |
| `readHyps_of_history` (+`_interior`, `_rec`) | GR0b:168/180/191 | body-only / none |
| `GR1_slotWeights`, `GR1_equalWeights` | GR1_equalWeights.lean:42/162 | NO — projections only |
| `GR2_slotResidual`, `GR2_posStep`, `GR2_slotResidual_graded` | GR2_slotResidual.lean:50/68/103 | NO — projections only |
| `GR3_keyResidual_pinned` / `GR3_keyResidual` / `GR3_keyResidual_level` / `'` | GR3 file | sorry bodies filled; `_level` untouched (its explicit pins become redundant, harmless) |
| `graded_read` / `graded_read_level` / `graded_read_of_history` | GR4 file | sorry body filled; others untouched |

The B-M2 §S4 consumption shape (H1_BM2_2026-08-06.md §S4 (i-b) + the REV 15 bracket,
lines 248-258 and 970-980): B-M2 consumes **`LeanUrat.B2D.graded_read_of_history`** at
the HISTORY signature (`HistoryCoherent H` + interior index + non-recentering
predecessor + `he1` + `Mpar` ⟹ three (i-b) clauses) — commit-cited (a5911fd). That
signature does NOT change under route (a); the note text needs no edit (an optional
annotation that the abstract-frame residue was re-adjudicated is ROOT-owner hygiene,
not a consumer change). ROOT_ASSEMBLY (H1) row displays the residue as
"OPEN-OBSTRUCTED ... interface re-adjudication = a campaign-owner statement-change
decision" (ROOT_ASSEMBLY_2026-08-02.md §3.1 (H1) REVISION-22 bracket; audit rows
r23-3, r23-6; census row `GRADED-READ`) — under route (a) those displays get a
one-bracket restatement at the next ROOT sync (r24), which is already owed for VC25.

### (iii) The killer question: is any consumer ORPHANED at abstract σ.e ≥ 2?

**NO — there is no such consumer.** Checked three ways:
1. The three sorry decls have zero Lean use sites (E-phase ledger discipline: "no
   consumer may cite a sorry-bodied statement" — and none does).
2. The proved GR-1/GR-2 theorems DO hold at abstract frames today; pinning `ReadHyps`
   narrows their effective scope. But their only consumer is `graded_read_level`
   (GR4:115, via `GR1_equalWeights`) — itself pinned already. No external consumer.
3. B-M2's (i-b) row and every ROOT display consume the HISTORY face, where
   `TransitionCoreL.child_e` ties `σ.e = ν.e` and `ReadHyps` forces `ν.e = 1` — the
   pin is SUPPLIED there, nothing narrows.

So route (a) is a scope cut ONLY of generality that (α) nothing consumes and (β) is
believed FALSE (the σ.e-compression countermodel). It is honestly a DISCHARGE of the
actual interface and a DELETION of refuted dead generality — provided the change is
displayed as a statement change (fence (vii) record + blueprint §4 annotation), not
passed off as a proof of the frozen semantics. Precedent: `ReadHyps` was already
narrowed-by-force once (`readHyps_e_eq_one`: the pack "was never a steep-read
theory"); the frame pin is the same genre, one level up.

### (iv) Post-pin proof cost per sorry

All three become one-liners from EXISTING suppliers (no new mathematics):
1. `GR3_keyResidual_pinned` := `GR3_keyResidual_level ν Φ' hlift R R.hσs R.hσt`.
2. `GR3_keyResidual` := `⟨ν.mhat, GR3_keyResidual_pinned ν Φ' hlift R⟩`.
3. `graded_read` := `graded_read_level ν Mpar Φ' hlift R R.hσs R.hσt`.
Plus the 4 signature diffs + 1 body edit above, docstring/table syncs (GR-0's supplier
map, GR-3/GR-4 adjudication blocks, blueprint §5 status lines, MANIFEST), and a B2D
recompile + `AxChk` check. **Total: S (≈ 2-4 unit-hours), zero mathematical risk.**
Optional golf (separate, not required): delete the now-redundant `_level` forms and
re-point `graded_read_of_history` at `graded_read`.

## 2. ROUTE (b) — keep history-keyed graded_read + displayed obstruction

**What stays open:** exactly the 3 sorries of §0, byte-frozen, PERMANENTLY — their
statements are believed false at the quantifier scope they bind, so they are not open
goals but standing refuted-statement ledger entries: never fillable, only refutable
(and refutation needs the §3 forge). Census consequence: `grep sorry` (the repo's
open-goals list) carries 3 forever-red entries; every future synthesis pass re-prices
them (this is pass 5's second time).

**Containment (verified):** no module imports GR3_keyResidual.lean or
GR4_gradedRead.lean, so the sorryAx reaches no capstone footprint; the in-file
`#print axioms` cover only the proved `_level`/`_of_history` forms.

**Where the obstruction must be DISPLAYED (all sites already exist at HEAD):**
* ROOT_ASSEMBLY_2026-08-02.md §3.1 (H1) row, REVISION-22 bracket item (ii) — "GR-3 ×2
  + GR-4 ×1 frozen sorries; ψ = φ(z^σ.e) gap countermodel mathematical, not compilable
  in-corpus" + audit rows r23-3/r23-6 + the `GRADED-READ` census row. Route (b) duty:
  the r24 fold restates "re-adjudication pending" → "adjudicated: history-keyed face
  is THE interface; abstract-frame sorries stand as displayed obstruction" .
* H1_BM2_2026-08-06.md §S4 (i-b) REV 15 bracket (the consumer-of-record display).
* blueprints/B2DEF_LEAN_2026-08-08.md §5 GR-3/GR-4 adjudication blocks.
* docs/SYNTHESIS_PASS5_2026-08-08.md F5 + queue 4 (this unit's charter).
* B2D/GRDefs.lean E-phase header — already corrected to "only open B2D sorries = 3 GR
  entries" (F6 hygiene commit 112b9ac).

**Honest-declaration verdict: YES, with exact phrasing.** "B2D: 0 sorries on the
consumed face" is TRUE — no current consumer consumes the abstract-frame face
(zero use sites, §1(ii)); the only consumer of GR content anywhere is B-M2's (i-b)
row, and it consumes `graded_read_of_history` (the history-keyed face) by name and
commit. "B2D sorry-free" simpliciter is FALSE (census: 3) and must never be written.
The honest formula on record: "B2D: TD front sorry-free; GR front sorry-free on the
consumed (history-keyed) face; 3 displayed open-obstructed sorries at the
never-consumed abstract-frame face, believed false there (countermodel priced,
not compiled)."

## 3. COUNTERMODEL PRICING (p ≠ 2 stage forge — NOT built here)

Target: a compiled instance refuting `GR3_keyResidual` (∃-form suffices; it kills the
pinned form and `graded_read` clause 2 with it): a `Node 3 (ZMod 3)` ν with
`ν.σ.e = 2` hosting `ν.e = 1`, plus `IsNodeLift ν Φ'` and `ReadHyps ν`, plus the
refutation `∀ mh, ν.σ.R Φ' ≠ T mh * toLaurent ν.ψ`.

**Structures to instantiate** (the designed configuration, GR-3 docstring + N-GR1 N5
numeric shadow `verification/openmath/ngr1_slotpos_trace.py`):
1. **The frame stage** `σCM : Stage 3 (ZMod 3)` — the MacLane augmentation
   [v₃; w(X) = 1/2] in the corpus normalization: `Φ = X`, `(e,h,s,t) = (2,1,0,1)`,
   `w = min_i (2·v₃(aᵢ) + i)`, `wPrev = v₃` (Gauss), `R` = the compressed residual
   map into `LaurentPolynomial (ZMod 3)` with `R X = T^0 = 1` (hRΦ at s = 0... NB:
   `hRΦ : R Φ = T σ.s` with s = 0) — ALL Stage law fields proved concretely:
   `hwmul, hwult, hvalgrp, hwΦ, hStretch, hR0, hRne, hRmul, hRadd, hRlt, hRΦ, hK1,
   hS5, hS6a, hS6b, hreps/hTvec/hWS` etc. (the field pack toyStage3 supplies at the
   Gauss stage, now at a RAMIFIED stage).
2. **The node** `νCM : Node 3 (ZMod 3)` at σCM — ~39 fields: `(e,h,s,t) = (1,1,1,0)`,
   `g = 2`, `ψ = z² + 1` (irreducible over ZMod 3: −1 non-square), `μ = 1`,
   anchored-residual fields `pat/Ranch/hOrd/hμ/hpat0/hRanch` (take Ranch = ψ,
   pat = its coefficient stream — satisfies `node_hψ0`'s provenance), species
   non-recentering, `hcop/hbez/hbezCanon/hψ*` all numeric, plus the line/height
   bookkeeping (`line, ustar, gam, hLineU, hDwidth, wSide, hEdvd, ...`) at the
   concrete slope.
3. **The lift witness** `Φ' = X² + 3`, `IsNodeLift νCM Φ'` via `tt 0 = C 3, tt 1 = 0`:
   checks `w(C 3) = 2·v₃(3) + 0 = 2 = ν.h·(g−0)` ✓ and
   `R (C 3) = C 1 * T^(−σ.t·wPrev(C 3)) = C 1 * T^(−1)` ✓ (forces the forged R's
   value at constants).
4. **The `ReadHyps` pack**: via (pinless) `readHyps_of_node` — `hscale`:
   `1 = 1·w(X) = σ.h = 1` ✓. (Under route (a) this constructor gains the frame-pin
   binders and the countermodel target statement no longer exists — the forge is a
   ROUTE (b) artifact only.)
5. **The mismatch witness**: compute `σCM.R (X²+3) = C 1 * T^(−1) + C 1 * T^2·...`
   — per the trace, `R(Φ') = C(1)·T⁻¹ + 1`-shaped adjacent support — then the
   support-gap argument `∀ mh, T^mh · toLaurent (z²+1) ≠ that` (finite support
   comparison; easy once R evaluates).

**Closest existing compiled instances (searched LeanUrat/):**
* `toyStage3 : Stage 3 (ZMod 3)` (MovesT/G1_toyGate.lean:2568) + `MovesJ.sigma0 :
  Stage 3 F9` (HC2/U28_gateSep.lean:558) — full-law p = 3 GAUSS stages (e = 1). The
  p = 3 residue machinery (`bw3`, `bres3`, the `s0*` law pack, the Λ3 transport)
  EXISTS and is the natural parts bin. Missing: everything e = 2.
* `ramifiedStage : Stage 2 F4` (MovesD/R7_ramifiedForge.lean:147) — the only compiled
  e = 2 stage, forged FREE via the D.7 constructor `HC1.S9_transStage` from
  `bStageP` + `StageCoreL` + a ramified `TransHyp`. **This route is CLOSED for the
  countermodel, twice over:** (α) it is `ramifiedStage_exists.choose` — a
  Classical.choice-opaque term whose `R` cannot be EVALUATED at the concrete `Φ'`
  (the refutation in step 5 needs a computable/unfoldable R; R7 only ever consumed
  `e = 2`, never an R-value); (β) S9 children carry composite keys (degree e·g·deg Φ),
  never the key-X augmentation stage the designed configuration uses.
* `bStageP : Stage 2 F4` (HC2/HK13_bStageCoreP1a.lean:553, + HK56/HK14 law arc,
  ~700+ lines) — the only HAND-FORGED stage with concretely-proved laws; the genre
  template for σCM.
* `TD0_ledgerInstance.lean` (450 lines) — the skeletal-carrier instantiation genre
  (shows the Node-scale field-fill discipline; different carrier).
* `HK53_e2Ruling.lean` — e′ ≥ 2 ruling THEOREMS over ramifiedStage; no R evaluation
  (consistent with (α)).

**Cost class: L (one full unit, est. 10-16 unit-hours).** Decomposition: σCM hand
forge with concrete law proofs ≈ the HK-13/56/14 arc re-run at p = 3 WITH e = 2
lattice compression (the dominant chunk; the p = 2 arc was ~700 lines at e = 1);
νCM + IsNodeLift + ReadHyps ≈ TD0-scale field fill (S-M); the final support-gap
refutation is S once R evaluates.

**The single hardest instantiation obstacle, named:** proving `hK1` (the
development-weight law: every nonzero Φ-development attains its weight on a slot)
TOGETHER WITH `hRadd`/`hRlt` for the CONCRETE compressed valuation
`w = min(2v₃ + i)` over ℤ₃ — i.e., hand-building the e = 2 graded-residue calculus
that the corpus has only ever obtained abstractly (S9_transStage) or at e = 1
(bStageP/toyStage3), where the abstract route is choice-opaque and thus useless for
the required concrete R-evaluation at `X² + 3`.

## 4. Decision table + recommendation

| axis | route (a) frame pins into ReadHyps | route (b) history-keyed + display | countermodel forge |
|---|---|---|---|
| consumer orphaned at σ.e ≥ 2 | NONE (zero use sites; B-M2 consumes history face) | n/a | n/a |
| statement diffs | 4 signatures (1 structure + 3 suppliers) + 1 body | 0 | 0 (new files only) |
| sorries after | **0 in B2D** (3 one-line proofs from existing suppliers) | 3, permanent, believed-false | 3 → 3 + refutation on file |
| cost | S (2-4 h) | 0 now; recurring re-pricing + forge L to ever close | L (10-16 h) |
| honesty duty | display the §4 statement change (fence (vii) record; ROOT r24 bracket) | exact phrasing "0 sorries on the consumed face" forever; never "sorry-free" | none extra |

**Recommendation: route (a).** The ONE decisive fact: the three frozen statements
have ZERO consumers and are believed FALSE at the abstract carrier — so route (b)
preserves nothing anyone uses and nothing that is true, at the price of 3 permanent
census entries and an L-class forge as the only path to closure; route (a) replaces
refuted dead generality with the scope every live consumer already operates at, for 4
signature diffs and three one-line proofs. The forge (F5 stage-forge species) should
then be DECLINED for GR purposes (its only GR payoff is refuting statements route (a)
deletes from the interface); re-price it solely against junc_bundle/readsOf need.

— analysis unit, GR-3x2/GR-4 disposition pricing, 2026-08-08
