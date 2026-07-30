# SYN-E0 — ResVal engine concordance table (C1 gate; 2026-07-30)

CHARGE (SYNTHESIS_PASS1 PART 2, ratified in BRIDGE_ADJUDICATIONS "C1+C4"): diff all
copies of the (w,R) residual-valuation kernel lemma-by-lemma BEFORE any hoist;
classify identical / α-renamed / genuinely-diverged; fix the exact law set and the
w-codomain census. Any SEMANTIC divergence = stop-and-report.

METHOD: mechanical extraction of every declaration from the 10 source files
(L3_K1, L5_landBox, L5_landVertex, L5_landVertexDigit, L5_landTwoSided_repair,
L3_liftWeight, L4_TRANSi_R3, L4_TRANSiii_R3, HC1/V3_readLift, HC1/V4_readLanding,
plus HC2/SharedRecenter as the existing public partial home), normalization of
α-names (primes, `wiii_`, `v3_` prefixes), separate statement-level and body-level
diffs. Script run in-session; verdicts below are statement-level unless noted.

## SYN-E0b (sequencing gate) — CONFIRMED

BP5's Moves-cluster quarantines landed first: `L5_landTwoSided_R5`,
`L5_landVertexDigit_repair`, `L5_landTransport_R3`, `L4_TRANSviii_b_R3` are all in
`lean/quarantine/*_2026-07-30.lean.txt` and absent from the live tree. Out of scope.

## 1. Statement-level verdicts (α-normalized)

Key: ID = byte-identical after α-normalization; ASC = differs only by a type
ascription/parenthesization that elaborates identically; VAR = hypothesis-strength
variant (see §3); K1/LB/LV/LVD/TS/SR/T1/T3/V3/V4/LW as in the script.

| family            | K1 | LB | LV | LVD | TS | SR | T1 | T3 | V3/V4 (ReadFrame) |
|-------------------|----|----|----|-----|----|----|----|----|----|
| w_one             | ref| ID | ID | ID  | ID | ID | ID*| ID | v3_wv_one: carrier-translated |
| w_neg             | ref| ID | ID | ID  | ID | ID | ID*| ID | v3_wv_neg: carrier-translated |
| w_pow             | ref| ID | ID | ID  | ID | ID | —  | —  | v3_wv_pow: carrier-translated |
| R_one             | ref| ASC| ASC| ASC | ID | ASC| —  | —  | v3_rv_one: carrier-translated |
| R_neg_one_sq      | ref| ASC| ASC| ASC | ID | —  | —  | —  | (inlined in v3 proofs) |
| R_neg             | ref| —  | ID | ID  | ID | ID | —  | —  | (inlined) |
| R_pow             | ref| ASC| ID | ID  | ID | —  | —  | —  | v3_rv_pow: carrier-translated |
| w_sum_ge          | ref| —  | ID | ID  | ID | ID | VAR-G | VAR-G | v3_wv_sum_ge: carrier-translated |
| GRf (ψ-order sum) | ref| —  | —  | —   | ID | —  | —  | —  | v3_GRf: ID (generic-K already) |
| psiNotDvd         | ref| ID | VAR-H | VAR-H | ID | — | — | — | v3_psiNotDvd: carrier-translated |
| w_Phat            | ref| VAR-S | ID | ID | VAR-H | — | — | — | inside v3_lift_core |
| cslot             | ref| —  | —  | —   | ID | —  | —  | —  | v3_cslot: carrier-translated |
| key_no_cancel     | ref| —  | —  | —   | ID | —  | —  | —  | v3_key_no_cancel: carrier-translated |
| minsum_facts      | ref| —  | —  | —   | ID | —  | —  | —  | v3_minsum_facts: carrier-translated |
| residual_sum_machine | — | — | ref| ID  | —  | INST | — | — | — |
| Laurent toolkit   | —  | OrdAt family | ref | ID | poly_dvd_of_laurent_dvd | — | — | — | V4 tail: ID with LV |

ID* (T1): identical statement with explicit binders instead of section variables.

Block-level facts (byte diffs, not α-normalized):
- LV private block (lines 55–405) vs LVD (64–472): **byte-identical** (single diff =
  the file boundary). Golf Moves#7's "copied near-verbatim, edits must be mirrored"
  drift risk CONFIRMED as still-in-sync; retired by SYN-M2/M3.
- V3 kernel (75–933) vs V4 (49–838): **byte-identical** after removing `v3_lift_core`
  (V3-only, 157 ln) and the pure-Laurent tail (V4-only, 96 ln, = the LV Laurent
  toolkit verbatim). Golf HC1#99 CONFIRMED; retired by SYN-M7.
- L3_liftWeight ≡ K1.w_Phat: identical statement, explicit binders (Moves#4 confirmed).

## 2. Verdict: GENUINELY CONCORDANT — GATE PASSES

**No semantic divergence found.** Every diff is one of: α-renaming; a redundant type
ascription; explicit-vs-section binders; a hypothesis-strength variant (§3); or the
Stage→ReadFrame carrier translation (σ.w/σ.R ↦ childW σ σ.Φ e★ h★ / V.D.Rv — exactly
the `ResValPack` instance map). Proof BODIES differ stylistically in places
(omega/linarith, simpa/rw) with no mathematical content difference.

## 3. Hypothesis-strength variants (the "diverged" rows, each benign)

- **VAR-H (more hypotheses than needed):** LV/LVD `psiNotDvd_local` adds `hg1 : 1 ≤ g`
  (derivable from `hψ.natDegree_pos` + `hg`); TS `w_Phat_priv` adds unused
  `hg hψ hψz hmon hDeg`. Shared module carries the K1 (weakest-hypothesis attested)
  form; migrated call sites drop the extra args.
- **VAR-S (stronger than K1):** LB `w_lift` omits `hg1 : 1 ≤ g` entirely (its proof
  handles g = 0) and reorders binders. DISPOSITION: shared `w_Phat` keeps the K1 form
  (all call sites have `hg1` in scope); LB's call sites re-ordered at migration.
  The g = 0 strengthening is UNCONSUMED anywhere — not hoisted (no invented strength).
- **VAR-G (generalized index/carrier):** T1 `wsum_ge'` is the bare-(W, hult) form over
  a general index type ι — the WEAKEST-assumption copy on disk; T3 `wiii_sum_ge` the
  Stage form over ι. DISPOSITION: T1's bare form is hoisted verbatim as the single
  proof source (`ult_sum_ge`); every other copy is a one-line specialization
  (recorded per-file in migration docstrings).
- **residual_sum_machine:** LV/LVD carry the ABSTRACT no-cancellation machine (hsep
  against all involutive u); SR's `decomp_machine` is its monomial-position INSTANCE
  (positions + R(−1) = C d discharge hsep; in the Laurent domain u² = 1 ⟹ u = ±1).
  DISPOSITION: machine hoisted from LV (pack-keyed = SYN-E3); decomp_machine derived
  from it (SYN-M9), statement unchanged.

## 4. Law census (fixes the `ResValPack` field list — SYN-E2)

Laws actually consumed by the engine, from the bare `Stage`/`ReadFrame` laws:
`hwmul`, `hwult`, `hRne`, `hRmul`, `hRadd`, `hRlt`.
**`hRne` is ADDED to the plan's five-law list** (the plan anticipated this: "exact law
list fixed by the Phase-0 concordance"): R_one's derivation cancels `R 1` in the
Laurent domain and needs `R 1 ≠ 0`; both carriers prove it (Stage.hRne; ReadResLaws
conjunct 2). `hR0` is NOT needed by any engine lemma (omitted). `hwΦ/hK1/hStretch/hS5`
are Stage-specific and stay OUT of the pack (the deep lemmas that need them are
Stage-keyed, not pack-generic).

## 5. w-codomain census

ℤ everywhere: `Stage.w : Polynomial ℤ_[p] → ℤ`; `childW σ σ.Φ e★ h★ : … → ℤ`;
T1's bare `W : Polynomial ℤ_[p] → ℤ`. **No ℚ-valued copy** ⟹ per the plan, the pack
codomain stays ℤ (no LinearOrderedAddCommGroup parameterization).

## 6. Copies beyond the plan's list (recorded for the M8 sweep / BP5 backlog)

w_one-family and/or sum_ge-family privates also present in: Moves/L5_landTransport_R4,
L5_realDomination_R3, L5_recSubst_R4, L4_TRANSviii_b_R4, L2_slotDecomp_R4;
HC1/T3_htChainWeight, T4_slotMinHt, T7_alphabetSpan, S5_childValuation,
S9c_coreAssembly, S11a_coreTransport, V2_readResidual, K1_vertexPin, S10_recStage,
V7/V8/V9/V10; HC2/HK05_countermodelGate (concurrent agent — do not touch).
These are MICRO copies (1–5 lemmas each); the plan's M8 covers the HC1 V-row; the
rest go to the BP5 sweep ledger. NOT migrated in this unit unless listed in M1–M9.
