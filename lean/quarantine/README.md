# Quarantine — foreign session's Order0Capstone tail (2026-07-03)

`omDensity_tail_2026-07-03.lean.txt` is the tail a parallel (stale-context) session appended to
`LeanUrat/OM/Order0Capstone.lean` (lines 196-446 at the time of quarantine). Removed because:

1. **It contains an ARITHMETICALLY FALSE axiom** (`omDensity_tame_functionalEquation`, was line 403):
   from its own definitions, `omDensity(n=2) = q(q+2)/(q+1)`, and `R(1/q) ≠ R(q)` (at `q = 2`:
   `8/3 ≠ 5/6`) — asserting `IsPalindromic` for it makes the base inconsistent (exact sympy check,
   session 2026-07-03). Concreteness prevents falsification-by-instantiation, NOT arithmetic
   falsehood (the A11 lesson).
2. **Its density object is the wrong function**: `omDensity := Σ clusterCount(cellsOfShapeWF …)` uses
   the `clusterCount` per-node aggregation REFUTED by the engine reconciliation
   (`VACUITY_SIGMA_BLUEPRINT.md §2.6` D1-D4): e.g. `clusterCount(sepShape (2)) = 4/3` at `q = 2` vs
   the true stratum density `1/4`, and `4/3` for the provably-EMPTY p=2 split stratum. Non-degenerate
   (≠ 0) but incorrect. The engine-validated object is `Order0.rootCount`
   (`montes_order0_unconditional`, footprint pure Lean core).
3. It discards σ (`_σ`), reintroducing the O1 σ-vacuity.

Salvageable ideas already adopted into the plan: the pin-field/invariant architecture and the
enforcement audit of `notes/MONTES_ARCHITECTURE_REDESIGN.md` §3/§7. The tail's
`clusterCount_isRational` engine instantiation is fine as a theorem about that function and can be
resurrected for Phase B once `clusterCount`'s node form is corrected. The tail also had two compile
errors (stuck `decide` at :311, type mismatch at :352) and was never built — the false axiom never
entered any olean.

## BB3inf_2026-07-07.lean.txt (R5 Step 0)
Retired 2026-07-07. The old measure-route BB3 module: 3 axioms (`descend`, `descend_size_lt`,
`AX_GMN_IV_terminates`) + its theorems (`clusterVolume_rational_of_OM`, `T_BB3`, `T_BB1`,
`bb3CellCount_isRational`). Verified DEAD before retirement: imported only by the root
`LeanUrat.lean`, reached by NO count-native capstone (the `PadicMeasure`/`RatFn` "BB3inf." mentions
are docstrings, neither imports it). Tree axiom count 10 → 7. The remaining measure cone
(PadicMeasure ×5) + the Interface split (R5 Steps 1-3, 7→2) stay per notes/R5_REFACTOR_PLAN.md.

## BP5 hygiene quarantines (2026-07-30) — CL-21 / CL-26 / CL-24

Executed per `notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` (REVISION 2) under the binding
2026-07-30 adjudications (`notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`: Q-5
quarantine-with-record, Q-7 fifth file YES, Q-8 execute immediately). Importer census
for EVERY file below was re-run by grep AT EXECUTION TIME (the A7 discipline, not the
ledger snapshot): **zero live importers for all 13 files**; none is in the root import
graph (`LeanUrat.lean`) or in `AxChk_baseline.lean`. Acceptance gate: full `lake build`
green + BUILD-ONLY AxChk census byte-compare (forced recompile of the census module,
`lake build LeanUrat.AxChk_baseline`, `#print axioms` info lines diffed against the
pre-move capture — never `lake env lean`).

### CL-21 — MovesGr superseded modules (the golf-ledger R2 six)

Each declared the SAME fully-qualified name as its proved successor, so any
`#print axioms` on the shared name depended on which module got imported (golf ledger
R2/A11/A12/A26 — the audit-soundness defect). Removal deletes 7 of MovesGr's 20
censused sorry tokens.

| file | reason (TRUE reason, per R-6) | collision partner (KEEP) | sorries |
|---|---|---|---|
| `MovesGr_L1_gradedRingStr_exists_2026-07-30.lean.txt` | superseded v1, sorry-backed; IN-namespace collision on `LeanUrat.MovesGr.L1_gradedRingStr_exists` (A11) | `L1_gradedRingStr_exists_2.lean` (PROVED capstone of D.1(a)-(c)) | 1 @115 (`mul_assoc`) |
| `MovesGr_L1_gr_domain_iff_val_2026-07-30.lean.txt` | superseded v1, sorry-backed; ROOT-namespace collision | `L1_gr_domain_iff_val_v3.lean` (PROVED, in-namespace) | 1 @59 |
| `MovesGr_L1_gr_domain_iff_val_v2_2026-07-30.lean.txt` | superseded v2, sorry-backed; ROOT-namespace collision (v2 diagnosed the OLD statement false pre-rekey; superseded by v3) | `L1_gr_domain_iff_val_v3.lean` | 1 @124 |
| `MovesGr_L2_coeffLoc_2026-07-30.lean.txt` | superseded v1, sorry-backed; ROOT-namespace | (root name now UNBOUND — the v2 partial went to CL-26 below; `CoeffLocLaw` is an open obligation) | 3 @22/27/35 |
| `MovesGr_L2_degZero_subring_2026-07-30.lean.txt` | **sorry-FREE** — the reason is NOT sorries but same-name supersession after the `add_def` re-key (R-6 record): pre-move byte-diff shows the v1 and v2 THEOREM STATEMENT LINES ARE BYTE-IDENTICAL (`LeanUrat.MovesGr.L2_degZero_subring`, both in-namespace); v2 is the MANIFEST-canonical module (and its 2026-07-29 red-module repair borrowed v1's componentwise `add_def` neg-leg argument). Quarantining removes the exact-duplicate declaration, keeping one owner | `L2_degZero_subring_v2.lean` (PROVED) | 0 |
| `MovesGr_L4_genuine_imp_stageCoreL_2026-07-30.lean.txt` | superseded v1, bare `:= sorry`; ROOT-namespace; its own header argues the statement NOT provable from its hypotheses (A13) | (root name now UNBOUND — v2 went to CL-26) | 1 @70 |

Expected baseline delta vs the frozen `notes/golf_baseline_2026-07-30/MovesGr_axioms.txt`
(record it so future fence checks do NOT read it as a regression): **Group B disappears
entirely** (its import list was exactly these superseded modules minus the v2 partials'
group) **and Group A loses the root `L1_gr_domain_iff_val` line** (the proved v3 is
in-namespace). Post-quarantine name resolution:
`LeanUrat.MovesGr.L1_gradedRingStr_exists` binds uniquely to the PROVED `_2` module;
root `L1_gr_domain_iff_val` is gone; root `L2_coeffLoc` and root
`L4_genuine_imp_stageCoreL` are UNBOUND in the live tree (see CL-26).

### CL-26 — MovesGr live FAITHLESS partials (binding Q-5: quarantine-with-record)

Both files carry grounded in-file arguments that their open conjuncts are UNPROVABLE
from `(σ : Stage) (M : GenuineStageModel σ)` — StageWF/DEF-3-type data is absent from
the interface. FAITHLESS-classified by the standing semantic audit
(`notes/MOVES_LEAN_SEMAUDIT_GR_2026-07-26.md` §B): #15 — "`GenuineStageModel` contains
no genuine coefficient sublocalization or S4 identification from which `CoeffLocLaw`
follows"; #21 — "`StageCoreL` includes coefficient-localization/T-vector content absent
from `M`". Supersession pointer: **NONE** — these are OPEN OBLIGATIONS; the
`MovesGr/MANIFEST.json` `status_asbuilt` records are the pointers (HELD-unit
precedent). Any future revival is fence-gated (statement repair adding a named
`RepLattice σ`-type hypothesis — §3.3 option (a), not taken).

| file | live sorries removed | PROVED content preserved verbatim inside |
|---|---|---|
| `MovesGr_L2_coeffLoc_v2_2026-07-30.lean.txt` | 2 @161/169 (the "(L^coeff)₀ ⊇ K" and "(P1) z-pinning" conjuncts) | the Ein/Eout weight-detecting evaluation + the S4 ⊆ conjunct |
| `MovesGr_L4_genuine_imp_stageCoreL_v2_2026-07-30.lean.txt` | 11 @395-422 (7 certified-UNDERIVABLE from the interface: `wPrev_mul`, `wPrev_ult`, `prevIaug`, `tvec`, `tvec_unit`, `reps_nonempty`, `p_is_rep` — free-field independence arguments; + 4 derivable-in-principle, quoted next) | the header's per-obligation classification + all closed legs |

The 4 derivable-in-principle legs, quoted per the CL-23 tombstone for any future
fence-gated revival: **`coeff` clauses 2-3** by hS5-monomial product induction with the
(−t·ν, e·ν) position/degree coupling and the `e·k_j = j − t·γ` stride; **`slot`.2** by
distinct-position termwise vanishing; **`coeff_loc` clause 1** by graded-invariant
closure induction. Filling them would NOT change the FAITHLESS classification nor kill
the sorryAx (the 7 underivable + the L2_coeffLoc_v2 inheritance remain).

POST-MOVE CENSUS (verified): MovesGr live sorry tokens = **0** (was 20 on 19 lines in
7 files; CL-21 removed 7, CL-26 the remaining 13). The five HELD units
(`L4_baseStage_exists`, `L4_base_nonvacuity_gate`, `L4_TRANSvi`, `L4_TRANSstage`,
`L5_recTRANSRS`) have no files and keep their MANIFEST `held_status` records — no
action.

### CL-24 — deprecated Moves modules (golf R2 sweep + the Q-7 fifth file)

⚠ **VertexDigit A/B label guard (EXECUTION-BLOCKING, honored):** the golf baseline's
Group A/B labels are REVERSED for the `L5_landVertexDigit` pair (golf ledger VERIFY-2
FOLD-IN CORRECTION). The file quarantined here is `L5_landVertexDigit_repair.lean`;
the canonical `L5_landVertexDigit.lean` STAYS — verified by grep BEFORE and AFTER the
move that `HC1/K1_vertexPin.lean:8` and `HC1/S16_levelLanding.lean:11` import
`LeanUrat.Moves.L5_landVertexDigit` and that both imports still resolve.

| file | reason | supersession pointer (KEEP) | sorries |
|---|---|---|---|
| `Moves_L4_TRANSviii_b_R3_2026-07-30.lean.txt` | deprecated R3; name collision on `LeanUrat.Moves.L4_TRANSviii_b` (A5); the :98-103 I-aug/prev-read sorry is CLOSED in the successor | `L4_TRANSviii_b_R4.lean` (sorry-free, adds `hcore : StageCore σ`) | 1 @103 |
| `Moves_L5_landTransport_R3_2026-07-30.lean.txt` | deprecated R3, REFUTED-as-stated (A6) — honest `sorry` was the only honest body | `L5_landTransport_R4.lean` (sorry-free, restated with the K1At slot-tie hypothesis) | 1 @54 |
| `Moves_L5_landTwoSided_R5_2026-07-30.lean.txt` | deprecated R5; the anchor-exactness clause was not encodable in the cylinder as stated (believed-false/superseded form) | `L5_landTwoSided_repair.lean` (:756 hexact form, post-R1; see the R1 execution record) | 1 @964 |
| `Moves_L5_landVertexDigit_repair_2026-07-30.lean.txt` | the NON-canonical member of the reversed-label pair; sorry-FREE, theorem byte-identical to the canonical file — reason is duplicate-name hygiene ONLY | `L5_landVertexDigit.lean` (canonical; imported by HC1/K1 + HC1/S16) | 0 |
| `Moves_L4_TRANSviii_a_R5_2026-07-30.lean.txt` | Q-7 ADJUDICATED fifth file: sorry-FREE, statement byte-identical to `_final`, header self-declares DEPRECATED ("Do not import"); a sorry-free duplicate is still a census ambiguity | `L4_TRANSviii_a_R5_final.lean` | 0 |

Census effect: the golf baseline header's caveat "sorryAx only at the ten fenced sites
+ deprecated Moves files" simplifies to the fenced sites alone (dated addendum in
`notes/GOLF_CAMPAIGN_2026-07-30.md`; the frozen baseline files are NOT rewritten).
