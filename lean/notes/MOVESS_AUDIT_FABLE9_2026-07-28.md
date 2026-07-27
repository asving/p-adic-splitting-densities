# MovesS blueprint REV 11 (THE CORE, 93 units) — fresh-instance confirmation audit #9 (Fable)

**Date:** 2026-07-28 · **Auditor:** fresh Fable instance #9 (via workflow subagent,
zero prior context) · **Scope:** REV 11 final confirmation of THE CORE (§2.A–2.D +
§3, 93 units); §W4-SYNC read solely for the self-containment and device-replacement
checks. **Blueprint:** `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (2000 lines, read in
full). **Ground truth:** `MOVES_2026-07-24.md` §S-RESUM, lines 11557–12577 (read in
full). **Method:** charge = `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` below its rule;
campaign calibration: every settled number recomputed (sympy via uv, transcript in
session); adversaries constructed beyond the listed ones.

---

## PART A — the directed verifications

**A1. PER-CELL RE-KEYING (R45) — PASS, with one adjacent GAP (finding G-2).**
`cellP : ∀ e τ, M.Cell e τ → Polynomial ℚ` + `cellP_deg` (≤ `T.Wstate e τ` — the
note's "each cell size one polynomial of degree ≤ W_state(s)") + `cellP_nonzero`
(per cell, e ∈ Icc 1 n) + per-cell `act_iff` (`activeState ↔ ∀ c, (cellP e τ c).eval
q₀ ≠ 0`) match CTS-M(ii)'s displayed mechanism ("else EMPTY CELLS at wild p corrupt
rows, denominators, determinants", S.0 item (7); "only finitely many primes are
roots of some not-identically-zero cell-size polynomial", S.4(ii)). THE ADVERSARY
CONSTRUCTED: cells {c₁, c₂} over one outcome o, cellP c₁ = X − 2, cellP c₂ = 1,
aggregate countS(o) claimed nonzero at q₀ = 2 with activeState 2 e τ asserted.
Verified: `act_iff` is violated directly (cellP c₁ eval 2 = 0, computed), and
`countS_cells` forces countS(o).eval 2 = (X−2)·1 at 2 = 0 — the empty cell can no
longer hide behind a nonzero aggregate; pre-R45 (act_iff on the aggregate countS
alone) the same adversary satisfied every law. U-22b consumes the per-cell roots
(finitely many (e, τ, c), each root set finite by cellP_nonzero; `finC`/`fin`
supply finiteness) ✓. `rep_indep` re-checked verbatim: rowVal (x-free) = Σ_{c ∈
cells o} μcell x c for EVERY representative x — outcome-level weighted grouping,
exactly RS.0(α)'s display ("the MEASURED row (T·G) is identical from every
representative of the cell (weighted form)"); μcell keeps its free x argument, so
no cellwise strengthening exists ✓ (trust flag 4 holds). BUT the new `countS_cells`
PRODUCT law itself exceeds the display — finding G-2 below.

**A2. THE FULL-STRUCTURE GATE (R46) — PASS on values and labels; ONE field missing
from the displayed obligation lists (finding G-1).** Field-by-field walk of
RS4Chain against the gate's coverage lists (n2_rsh: "Sigmas/sig_exact, PrimePools/
prime_base/prime_sub, decidedTotal, Rval/r_bdd, x3_total, rs1_equates, rsh_interp,
pools_e0/legs_reg, L, B, hns" + `n2_shallow_device`: "WshP … WshVal … shDom,
shEvtH/visH/shEvt … and the laws wshval_bdd/shDom_ne/sh_realized/shevt_grouping/
shweight_card/wsh_ok/wsh_interp"): 30 of 31 fields covered; `wshval_card` (§2.D
line ~957) appears in NEITHER list — see G-1. DEVICE labeling ✓ ("LABEL:
device-only"); seam replacement lists name the device fields (S-8: WshP/WshVal/
shDom/shEvtH/visH/shEvt/shWeightH; S-10: rs1_equates/rsh_interp/sh_realized/
wshval_card) ✓. VALUES RECOMPUTED (sympy, exact): WshP ≡ 1-presentation ⟹ val = 1,
OK at every pool, wshval_bdd ∈ [0,1] ✓; with the singleton root shape (k = 1,
σ0 = ∅, δ = 1) Rsh σ = blockSolve values ✓; measured fixpoint β = q₀⁻³β + b
re-solved per σ′: β_{(1,2)} = (q+1)/(q²+q+1) ✓, β_{(1,1)²} = q²/(q²+q+1) ✓,
β_{(2,1)} = 0 ✓; Σ_{σ∈Sigmas} Rval = 1 = decidedTotal (x3_total by construction) ✓;
at q₀ = 2: 3/7 + 4/7 + 0 = 1 ✓, kernel entry 1/8 = the msW_eighth_le shadow ✓.
n2_rsh's REV-10 scope contradiction is gone ✓.

**A3. U-17b DISPLAY GUARD (R47) — PASS.** §3c now reads "∀ e he h_ent τ σ' q₀,
q₀ ∈ M.Pools → B.βfull … = B.βmeas …" — identical binder list and pool guard to the
§2.D field `rexact : nsNull → ∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools → …` (R40 form);
βfull off-pool is unconstrained data, as the field intends ✓.

**A4. THE SIX R48 SPLITS — PASS.** U-12c/U-12d each one equation (comp law / pool
law) ✓; U-22b one statement (Finite ∧ Infinite — one note display), U-22c the
base-prime Finite face with the chain hypotheses (hsub/hbase) EXPLICIT ✓;
n2_polygeom_data + n2_ok, n2_interp_tg + n2_interp_iota, n2_degpins_tg +
n2_degpins_iota each one obligation-group per the batch's stated standard ✓;
U-29e → n2_det / n2_solve_vals / n2_checksum, one display each, retagged NOTE-W6 ✓.

**A5. SELF-CONTAINMENT — PASS.** Grep of TreeIface/FiberIface/ReadLedger/
XRBPackage/RS1GivenPackage/Wsh17Package + the W-pins over the core spans
(§2.A–2.D ≈ 400–998; §3 ≈ 1229–1782): every hit is comment/provenance register
(xrb's "discharge = the pinned W-2 … §W4-SYNC" at 885; the R44 NOT-claimed
disclaimer at 1539–40; the S-11 tombstone at 1651) — no typed field, statement,
dep, or hyp of any core unit consumes a seam carrier. The §3b W-1-hok edge is
tagged [seam] ✓. `∨ True`/`: True` grep: only historical-record mentions ✓.
Live pointers to the retired §2.E: one residual in §5 (see O-1).

**A6. SETTLED ARITHMETIC RECOMPUTED (all exact, sympy) — PASS.** part1: q⁻³ +
(1−q⁻¹) + (q⁻¹−q⁻³) = 1 ✓; row masses ≥ 0 at q₀ ≥ 2 ✓; det(1−K) = 1−q⁻³ =
(q−1)(q²+q+1)/q³ ≠ 0 ✓; the reduced solve and checksum as in A2 ✓; PolyGeom
representability under the R30 law — reduced denominators q³, q, q³, q³ divide
X^qpow (3, 1, 3, 3) exactly ✓; R35 windows: 2 = 2·1 + 0, g·μ = 1 = ℓ, W′D′ = 1·2 =
2 = WD = member size ✓; DegCons sums (2), (1,1), (2) ≤ 2 with routing
(1,1)/(2,0)/(1,0) ✓; sig_exact rosters enumerated: n = 2 gives exactly {(1,1)²,
(1,2), (2,1)}, n = 3 exactly the note's displayed five (S.7(i)) ✓.

**A7. FRESH 93-UNIT SWEEP + CENSUS — PASS on the census; two label-level defects
(O-1, O-2).** Every §3/§3c unit walked against its moves_ref (quotes verified
against lines 11557–12430; U-1/U-2/U-4/U-5/U-8/U-10/U-16a1/U-16b/U-17a/U-17b/
U-18/U-22/U-22b/U-23d/U-25/U-27/U-28 and the S5 layer quote all verbatim-faithful;
quantifier orders, activity guards, (BDY) conventions, every-σ′ scope, empty-Act
edge case all match). Census recounted from the unit lists: S0:9 (7e/2m) · S1:4
(0e/4m) · S2:17 (5e/12m) · S3:12 (5e/7m) · S4:6 (2e/4m) · S5:45 (32e/13m) = 93 =
51 easy / 42 medium / 0 hard — EXACT, including the itemized easy/medium name
lists (19 + 32 easy; 27 + 2 + 13 medium). Seam: 11 entries ✓. But two headcount
LABELS in the prose are stale (O-1, O-2 below).

---

## PART B — findings

**G-1 (GAP — spec completeness at the R46 gate).** Quote: "and the laws
wshval_bdd/shDom_ne/sh_realized/shevt_grouping/shweight_card/wsh_ok/wsh_interp"
(`n2_shallow_device`, ~1637) and n2_rsh's coverage list (~1627–29). RS4Chain
demands `wshval_card` (§2.D ~957: "WshVal Ŝ q₀ * (Fintype.card …) = ((shEvt Ŝ q₀
N).card …)"), and seam entry S-10 (~1044) presupposes its device-satisfied
instance — but NO S5 unit's displayed obligation list supplies it. The FULL-chain
claim (R46: "no partial structures") has one field with no owning unit. Lean's
elaborator would catch the omission (missing field), and the device's singleton
height class satisfies it trivially via shweight_card + shevt_grouping — hence
GAP, not critical: add `wshval_card` to `n2_shallow_device`'s laws list.

**G-2 (GAP — hypothesis fidelity: an undisplayed strengthening in RatBurdens).**
Quote: "`countS_cells : ∀ e τ o, (if routeOf … = .split then jP e τ o else tgP e τ
o).countS = ∏ c ∈ {c | M.cellOut e τ c = o}.toFinset, cellP e τ c` — the aggregate
count-piece IS its cells' product" (§2.C ~759–764). The note displays per-cell
polynomials, their degree bound, not-identically-zero, and activity-as-vanishing
(S.0 item (7), S.3, S.4(ii)) — it NOWHERE displays that the aggregate count piece
FACTORS as the product of its cells' polynomials. For split outcomes the displayed
aggregate is a SUM, not a product: "J_{τ,o}(q) := … the sum, over the branching
digit CELLS of outcome class o …, of the XHD-resummed conditional cell mass …
EACH CELL ONCE" (S.0), and the (J-RAT) deliverable is per-cell tables SUMMED into
J. Codex#7-1's demand (checked against `MOVESS_AUDIT_CODEX_FINAL7…`) was per-cell
keying of activity/nonvanishing — not a product law. For a multi-cell outcome the
product pin forces the interpolated mass (j_interp/tg_interp: val = rowVal =
Σ_cells μcell) to carry ∏ cell-sizes as a factor within the (iv)-POLY presentation
— a constraint on [1v]'s burden with no note support, whose satisfiability by the
intended CTS instance is unestablished (spurious denominators at the OTHER cells'
roots must cancel into countT/geom, corrupting geom's displayed meaning as "the
XHD-s height sum"). The R45 goal is already fully carried by per-cell `act_iff` +
`cellP_nonzero` (which U-22b consumes directly); `countS_cells` is consumed by no
core theorem beyond the gate's trivial cellP ≡ 1 instance. REPAIR OPTIONS: weaken
to the root-set face actually needed (e.g. `(….countS).eval q₀ ≠ 0 ↔ ∀ c, (cellP
e τ c).eval q₀ ≠ 0` at pools, or divisibility `∀ c, cellP e τ c ∣ …` is likewise
undisplayed — prefer the iff), or record an owner-side [1v] adjudication that the
computed tables DO present countS as the cells' product before E-phase freezes it.

**O-1 (observation — staleness in live §5 text).** "§2.A–2.D + the 85 §3 units"
(~1817) is the REV-10 count (Fable#8's scope line confirms 85 at REV 10); the
REV-11 census three lines below and the §3 heading both say 93. Same paragraph:
"Statement changes to §2/§2.E = statement-fence events" (~1822) still points at
the retired §2.E (should read §2/§W4-SYNC per R49's own sweep rule).

**O-2 (observation — stale headcount label).** "FOURTEEN units after the
REV-10/11 splits" (~1560) heads a batch of FIFTEEN listed units (count verified;
12 REV-10 units + 3 R48 splits = 15). The census (S5 = 45 = 32e/13m) is computed
from the 15-entry list and is correct — label only.

---

## PART C — counts and verdict

Findings: **0 CRITICAL / 2 GAP** (G-1 gate-spec completeness; G-2 undisplayed
countS_cells product pin) + 2 observations (O-1 "85"/§2.E staleness; O-2
"FOURTEEN" label). All directed verifications (per-cell adversary, full-gate walk
with exact recomputation, U-17b guard, R48 splits, self-containment, settled
arithmetic, 93-unit sweep, census 51/42/0) otherwise PASS; no architectural
finding; the note is nowhere misrendered by a core THEOREM statement.

**VERDICT: REJECT (0 crit / 2 gap)** — the two gaps are one-line-class repairs
(add wshval_card to the device unit's list; weaken or owner-adjudicate
countS_cells), after which this auditor's residue is empty.
