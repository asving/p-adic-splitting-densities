# SYN C1 — ResVal engine cluster EXECUTED (2026-07-30)

Plan: SYNTHESIS_PASS1_2026-07-30.md PART 2 (ratified BRIDGE_ADJUDICATIONS "C1+C4",
sequenced after the BP5 Moves quarantines — SYN-E0b confirmed on the quarantine dir).
Concordance gate: `SYN_E0_CONCORDANCE_2026-07-30.md` (PASSED — no semantic divergence;
law census = plan's five + `hRne`; w-codomain ℤ everywhere).

## What landed

NEW (single proof sources):
- `Moves/LaurentOrd.lean` (~220 ln) — the (w,R)-free Laurent ψ-order toolkit
  (dvd_of_dvd_mul_T/T_mul, psi_not_dvd_X_pow, toLaurent_pow_dvd_transfer + its two
  binder-variant wrappers, OrdAt + ordAt_unique/unit_mul/add, pow_order_unique,
  GRf_priv, psi_order_of_sum). Verbatim hoists; sources per lemma in the header.
- `Moves/ResVal.lean` (~570 ln) — `ResValPack p K` (w, R, hwmul, hwult, hRne, hRmul,
  hRadd, hRlt) + `ult_sum_ge` (bare form, VERBATIM from L4_TRANSi.wsum_ge') + the
  arithmetic nine + `residual_sum_machine` (SYN-E3, VERBATIM from L5_landVertex,
  pack-keyed) + `decomp_machine` (monomial instance, DERIVED from the machine) +
  `Stage.pack` + Stage-keyed wrappers with the exact classic signatures + the deep
  Stage engine (psiNotDvd, w_Phat, cslot, key_no_cancel, minsum_facts — VERBATIM from
  L3_K1 = L5_landTwoSided_repair).
- `HC1/V34_readKernel.lean` (~845 ln) — `ReadFrame.pack` (the SECOND carrier) + the
  V3/V4 shared kernel hoisted ONCE (arithmetic six re-based on the pack; deep v3_*
  lemmas verbatim; v3_GRf delegates to LaurentOrd).

MIGRATED (all public statements byte-identical — scripted HEAD-vs-worktree signature
diff PASS; per-file records in each header):
- SYN-M1 L5_landBox 581→~350 · M2 L5_landVertex 707→~320 · M3 L5_landVertexDigit
  817→~420 · M4 L5_landTwoSided_repair 970→~630 · M5 L3_K1 563→160 + L3_liftWeight
  143→44 (delegation; Moves#4 dup retired) · M6 L4_TRANSi/L4_TRANSiii (privates
  deleted; ult_sum_ge source) · M7 V3_readLift 1113→256 + V4_readLanding 1221→428
  (the ~790-line verbatim copy DEAD; HC1#99 retired) · M8 V8/V9/V10/S10 micro-copies
  (V7's v7_* are compound lemmas, not engine dups — left, recorded; V11 had none) ·
  M9 SharedRecenter re-exported from ResVal (U20c/U22E1 untouched).

NET: −2,586 deletions / +109 insertions on the migrated files at the final diff
(plus the earlier-checkpointed K1/landBox/landVertex/landVertexDigit deletions swept
into 690cc4a), against ~1,640 lines of new shared modules — and the ≥9-way drift
surface is gone.

VERIFICATION: full `lake build` green (8,579 jobs); AxChk_baseline census
byte-identical to the archived golf2 baseline (0 sorryAx); scripted public-signature
fence check PASS over all 15 touched files.

## SYN-F1 (BP2 prompt amendment — the σV instance)

For HK-02 / HK-52 / HK-11a (and any unit that would "copy V10 helper patterns"):
DO NOT re-derive the (w,R) arithmetic at σV. Post-HK-06, build
`RegradeOf.pack : ResValPack p ↥σ.K` from the recorded regrade laws (the `RegradeOf`
record's law fields are exactly the pack's six) and consume
`ResValPack.{w_one, w_neg, w_pow, R_one, R_neg_one_sq, R_neg, R_pow, w_sum_ge,
residual_sum_machine, decomp_machine}` — the same engine now serving `Stage.pack`
and `ReadFrame.pack` (`HC1/V34_readKernel.lean` is the model instance to imitate).
The per-slot window recursion (the units' hard content) is NOT supplied — only the
~200-line scaffold under it.

## SYN-F2 (BP4 prompt amendment — the KB5 enum-model seam)

KB5/KB5a's noninterference input ("pairwise-distinct Φ-adic positions all in one
class mod e; addition never mixes positions; min attained, no cancellation") is an
instance of `ResValPack.residual_sum_machine` / `decomp_machine`
(`Moves/ResVal.lean`): positions = the Φ-adic slots j₀+ek, weights = wt, the
separation hypothesis discharged by position-injectivity exactly as in
`decomp_machine`'s derivation. State KB5's input in the machine's Finset form and
consume the "min ≥ W" leg from `ult_sum_ge`/`w_sum_ge` rather than re-proving. If the
enum carrier is not `Polynomial ℤ_[p]`, the seam unit should transcribe THROUGH the
machine's proof shape (the machine's domain is currently pinned to `Polynomial ℤ_[p]`
per the ratified plan; a domain-generic re-parameterization is a one-line change to
`ResValPack` — flag for adjudication rather than copying).

## Golf ledger closures

- Moves#4 (L3_liftWeight ≡ L3_K1.w_Phat verbatim dup): CLOSED — single source
  `ResVal.w_Phat`, L3_liftWeight delegates; the stale ".olean not built" historical
  notes removed from L3_K1/L5_landVertex headers.
- Moves#5 (L4_TRANSi vs L4_TRANSiii helper dups): CLOSED for the engine trio
  (w_one/w_neg/sum_ge); the OTHER Moves#5 items (unused-binder hygiene) unaffected.
- Moves#7 (landVertex ↔ landVertexDigit "edits must be mirrored" drift risk): CLOSED —
  the shared block deleted from both; single source ResVal/LaurentOrd.
- HC1#99 (V4:45–832 verbatim copy of V3 kernel): CLOSED — `HC1/V34_readKernel.lean`.
- HC1#100 (V7/V8/V9 micro-copies): CLOSED for V8/V9/V10/S10; V7's `v7_w_mul_keyPow`/
  `v7_dev_exists_bounded` are compound (not statement-level dups) — left with record.

## Residue (for the next sweep, no adjudication needed)

SYN-E0 §6 lists the remaining micro-copy files OUTSIDE the ratified M1–M9 scope
(L5_landTransport_R4, L5_realDomination_R3, L5_recSubst_R4, L4_TRANSviii_b_R4,
L2_slotDecomp_R4; HC1 T3/T4/T7/S5/S9c/S11a/V2/K1_vertexPin; HK05 [concurrent
agent's]). Fold into the BP5 sweep unit (plan N8) with this cluster as the template.

## Codex per-conjunct equivalence pass (Phase-4 protocol) — 5/5 CLEAN

Charge: quote-and-classify over the statement-level packet (pack law transcription;
ReadFrame.pack conjunct wiring; decomp_machine old/new/re-export triple; call-site
equivalences H1 w_lift→w_Phat, H2 psiNotDvd hg1-drop, H3 S10 w_sum_ge delegation,
H4 v10_R_pow guard-drop, H5 wiii_sum_ge→ult_sum_ge; the four verbatim-statement
claims). Verdicts: 1 CLEAN (exact transcription, hR0 omission intentional and
recorded), 2 CLEAN (projections .2.1/.2.2.1/.2.2.2.1/.2.2.2.2.1 correct, shapes exact),
3 CLEAN (re-export statement byte-identical; derivation conclusion identical; unused
(d,hd) binders statement-level sound), 4 CLEAN (all five call-site claims), 5 CLEAN
(verbatim claims true). Session 019fb529-7544-7dd1-92c2-82c67710d921, model
gpt-5.6-sol, output /tmp/c1_codex_out.txt (this summary is the durable record).
