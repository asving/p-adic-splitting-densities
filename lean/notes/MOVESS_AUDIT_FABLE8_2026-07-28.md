# MovesS blueprint REV 10 (THE CORE) — fresh-instance confirmation audit #8 (Fable)

**Date:** 2026-07-28 · **Auditor:** fresh Fable instance #8 (via workflow subagent,
zero prior context) · **Scope:** REV 10 CORE ONLY (post-seam-split; 85 units, §2.A–2.D
+ §3); §W4-SYNC skimmed solely for the self-containment check.
**Blueprint:** `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (1918 lines, read in full).
**Ground truth:** `MOVES_2026-07-24.md` §S-RESUM, lines 11557–12430 (read in full),
citing the ACCEPTANCE RECORD at ~12854 (dual-accepted rev 6), never the in-body
trailer. **Method:** charge = `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` below its rule;
campaign calibration: verify by computation and display (exact recomputation via
sympy/Fraction, transcript preserved in this session).

---

## PART A — the five directed verifications

**A1. SELF-CONTAINMENT — PASS.** Grep of the full blueprint for
W1/W1e/W1m/W2/W3/W4/W7/W8/W10/W17ii and TreeIface/FiberIface/ReadLedger/XRBPackage/
RS1GivenPackage/Wsh17Package, filtered to the core spans (§2.A–2.D ≈ lines 400–956;
§3 ≈ 1184–1600): every hit is comment/provenance register ("discharge = the pinned
W-2", "pinned as W-4", "the evaluated shadow of the PINNED W-1", "= seam duties,
W17ii's contract") — permitted by the split record ("only its provenance notes point
into the seam"). NO typed field, statement, dep, or hyp of any core unit references a
seam carrier or pin. U-29d6 is correctly tombstoned to seam entry S-11 and excluded
from the 85. RS4Chain/RS1Bundle/ReadOffBundle fields re-walked: all carriers core-
declared (Shape, PolyGeom, M.Hgt, M.Box, PoolHyp, AVAgree). Import DAG closed. (Two
sync residues found at the PROSE level — findings F2-adjacent O-1 and finding F3
below.)

**A2. Multiset `resFactors` + position-indexed `memberOf` — PASS, computation-
verified.** The m = 1 inference: mem.length = 1 ⟹ Fin 1 = {selIdx}; `memberOf` is
injective into member positions avoiding selIdx (`memberOf_ne_sel`), so its domain
`Fin flankCount ⊕ Fin ((resFactors.erase (g,μsel)).card)` is empty ⟹ flankCount = 0
and erase-card = 0; with `sel_mem`, card resFactors = 0 + 1 ⟹ singleton;
`res_sum` on the singleton gives g·μ = ℓ; `flank_zero` + `window_comp` give W = e·ℓ.
THE REPEATED-FACTOR CASE (constructed, per charge): resFactors = {(g,μ),(g,μ)} with
the selected pair duplicated — `Multiset.erase` removes ONE copy, the surviving copy
demands its own member position ≠ selIdx, impossible in Fin 1 ⟹ the structure
correctly FORBIDS a duplicated residual factor at m = 1 (checked: capacity m − 1 = 0
< domain 1). Finset counterfactual reproduced: dedup collapses the duplicate to card
1, the phantom factor becomes invisible and the m = 1 inference would wrongly pass
while the indexed family "Σᵢ g⁽ⁱ⁾μ⁽ⁱ⁾" sums 2gμ. At m = 2 the duplicate carries its
own position (checked satisfiable). Codex#6-10 is genuinely fixed; `res_sum` is
multiplicity-correct (Multiset.map/sum).

**A3. `act_iff`/`cellsize_nonzero` ROUTED — PASS.** Both route tgP.countS on
routeOf ≠ .split and jP.countS on = .split, ∀ o over the FULL roster, matching the
note's mass carriers: (iv)-POLY's cell-size polynomial for K/terminal columns (tgP;
`tg_interp` non-split) and (J-RAT)'s "cell-level counts polynomial per the (iv)-POLY
pattern" for split cells (jP; `j_interp` split). U-22b's consumption re-derived: an
exceptional pool is a root of one of the finitely many ((e ≤ n) × Fintype State ×
Fintype Out) routed countS, each ≠ 0 by `cellsize_nonzero` hence finitely many roots.
The iff shape itself is the verifier-specified R39 form (settled at rev 9, Fable#7
0-crit); the rev-10 delta is the routing only, verified faithful.

**A4. n = 2 gate internal-consistency labeling — PASS.** R44's split of claims
checked against the note: note-displayed and reproduced = {the 1×1 block shape, the
solve denominator q² + q + 1, the p = 2 ratio-1/8 shadow `msW_eighth_le`, the
checksum shadows} — all four ARE the note's display (11647–49; S.7 12399–400).
The three-outcome roster, the masses, and the numerators (q+1, q²) are claimed as
CONSISTENCY DEVICE only. Grep of every S5 unit: no unit attributes the roster or
numerators to the note; U-29e claims only "denominator q² + q + 1 exactly"; U-29b3
cites the note (11858–60) only to diagnose what the display is NOT (the μ = 2
root-entrance conflation). Seam structures correctly NOT claimed inhabited
(Codex#6-12 honored). One scope contradiction inside the d-iv…vi block = finding F2.

**A5. U-22b in-scope route — PASS.** Infinitude = `M.pools_infinite` minus the
finite exceptional set (the `Nat.exists_infinite_primes` route, which cannot place a
prime in Pools, correctly rejected — Fable#7-GAP-2 fixed). The base-prime face
`allActive_cofinite_primes` takes PP ⊆ M.Pools and the prime_base iff as EXPLICIT
theorem hypotheses, exactly matching the chain's prime_sub/prime_base at U-24b's
locus instantiation (hbase is slack for the finiteness proof — subset of the part-1
finite set — but documents the intended domain per the split record's demand; not a
defect). Note display matched: "cofinitely many — only finitely many primes are roots
of some not-identically-zero cell-size polynomial" (S.4(ii)).

## PART B — settled arithmetic recomputed EXACT (sympy/Fraction, this session)

- part1: q⁻³ + (1−q⁻¹) + (q⁻¹−q⁻³) = 1 ✓; row masses ≥ 0 and kernel entry < 1 at
  q₀ ∈ {2,3,4,5,7,8,9} ✓; at p = 2 the kcol mass = 1/8 (the msW_eighth_le shadow) ✓.
- det(1−K) = 1 − q⁻³ = (q−1)(q²+q+1)/q³ ✓ ≠ 0.
- β_{(1,2)} = (q⁻¹−q⁻³)/(1−q⁻³) = (q+1)/(q²+q+1) ✓; β_{(1,1)²} = (1−q⁻¹)/(1−q⁻³) =
  q²/(q²+q+1) ✓; sum = 1 ✓; at p = 2: 3/7, 4/7 ✓.
- PolyGeom corrected law (denom ∣ X^qpow · ∏(1−X^a)) verified by polynomial division
  on all five exhibits: q⁻³ (qpow 3, ∅), 1−q⁻¹ (qpow 1), q⁻¹−q⁻³ (qpow 3), the det
  (X³−1)/X³ (qpow 3, {3}), and the XHD-s face 1/(1−q⁻²) ↦ X²/(X²−1) (qpow 0, {2}) —
  all divide ✓ (units-tolerant divisibility as intended).
- R35 windows: 2 = 2·1 + 0 ✓; g·μ = 1 = ℓ ✓; W′D′ = 1·2 = 2 = WD = member size ✓.
- sig_exact rosters recomputed: degree-2 = {(1,1)², (1,2), (2,1)} (three, = n2_sigmas)
  ✓; degree-3 count = 5 = the note's displayed five ✓.

## PART C — full sweep, census, DAG

**Full sweep (85/85), deep spot-checks (11):** U-1 vs the (m,c) classification incl.
"c ≥ 1 with m = 1 forces c = 1" (hc ≤ m derivable, harmless) ✓ · U-4/U-5/U-6 vs
SP.1's flank/co-factor typing + SP.2's stage law W′D′ = μ·e·g·D = ℓ·e·D = W·D ✓ ·
U-8/U-9a/U-9b: the (K-SUB) "= 1" correctly decomposed as regroup (U-8) / evaluated
per active pool via part1+rep_indep+interps (U-9a) / symbolic via U-22b+U-27 (U-9b),
matching the note's PART-1 route and conditionality bracket ✓ · U-10's routed
nonnegativity derived (gwt ≥ 0 from meas_card card-ratios + boxpos; no swapped
hypothesis exists) ✓ · U-16a1's pinned def-equation vs the b_e^split display incl.
the §T.4 factor-1/verdict-singleton indicator and SIBLING-INDEXED Fin m convolution ✓
· LedgerIV vs the NINE-input ledger 1:1 (xhd trio = XHD-d's no-stray/no-orphan;
d4r0; part1; rep_indep = RS.0(α) verbatim; meas_card; kstep_one+hmc; act_target =
the ONLY displayed ACT law; init trio + ent_count_card; comp_once — heights summed
once structurally) ✓ · U-22's per-block binders vs S.4(ii) ✓ · U-24a1/a2 vs
RS.1-DEEP restricted to the ACTIVE block + the (ii-c) read-off as HYPOTHESIS ✓ ·
U-24b's full-Lean statement: binders, hread coverage, and conclusion quantify
identically; locus = the note's own all-active quote ✓ · U-28 vs RS.4's three-step
route with the FULL inherited set and the acceptance fence verbatim ✓ · DELTA-ABS
chain (U-12c/U-16a3): powSubst composition and ≤ n factor bound re-derived ✓.

**Census EXACT:** S0 9 · S1 4 · S2 16 · S3 11 · S4 6 · S5 39 (= 12 construction +
7 + 7 ledger + b3 + c + 4 d-i…iv + d2 + 4 sigmas/x3/rs1eq/rsh + d5 + e) = **85**;
easy 18 + 27 = **45** (name-by-name against the §5 lists), medium 28 + 12 = **40**,
hard **0**. Machine-recounted: (85, 45, 40) ✓.

**DAG ACYCLIC:** topological order exhibited (S0 → S1/S2-prefix → S3 → U-22 →
U-16b/c → S4 → S5). The one suspicious pair — U-22 → hdet of U-16b while U-22
consumes Kmat — is clean: Kmat is a Defs-level declaration, not U-16b's output.
Consumption discipline holds: nothing proves toward `xrb` (n2_xrb instantiates the
gate's field, it does not discharge the kernel); no PCI site consumed by S.1-shaped
content; S5 flows forward only.

---

## FINDINGS (quote · cite · class)

**F1 · GAP — U-17b's carried-forward spec drops the R40 pool guard (unprovable as
displayed).** Quote (§3c): "`theorem rexact_solve (B) (hns : B.nsNull) : ∀ e he
h_ent τ σ' q₀, B.βfull e he h_ent τ σ' q₀ = B.βmeas e he h_ent τ σ' q₀`". The
supplying field (§2.D) is pool-quantified per R40/Codex#5-6: "`rexact : nsNull →
∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools → …`" — so the sketch "fire `rexact`" cannot
close the displayed goal at q₀ ∉ Pools (βfull there is unconstrained data). The §3
S2 line "U-17b … unchanged" is the tell: the rev-9 re-quantification never
propagated to §3c. Leaf unit (no consumers in §3b), caught at build; repair = add
`q₀ ∈ M.Pools →`. Precedent class: R2-16 (missing [Nonempty ι]) = gap.

**F2 · GAP — the gate's R44 scope list contradicts itself on `rsh_interp`
(n2_rsh unbuildable as scoped).** Quote (U-29d-iv…vi): "CHAIN FIELDS INSTANTIATED
(R44 scope): … x3_total, rs1_equates, rsh_interp, … — NOT the shallow-production
carriers (WshP/WshVal/shDom/shEvtH/… = seam duties, W17ii's contract)." But
`rsh_interp`'s statement is parametrized by `C.WshP` (`Rsh … F WshP σ` — §2.D line
"Rsh T M RB hdc hK hdet F WshP σ ∈ OKat p"), so instantiating rsh_interp REQUIRES a
WshP value the same sentence excludes; further, RS4Chain cannot be partially
inhabited as a structure, so "chain fields instantiated" must mean standalone
propositions — fine for x3/rs1eq (WshP-free), impossible for rsh_interp as scoped.
The intended content is clear and consistent (WshP is CORE-typed data, Shape T →
PolyGeom; a device WshP ≡ the 1-presentation on n2_shapefam's root shape gives
Rsh σ = blockSolve σ and the unit's stated "explicit values" arithmetic goes
through, verified: eval = (q₀+1)/(q₀²+q₀+1) etc.). Repair = one line: permit the
device-WshP DATA at the gate (production LAWS stay excluded), and name the unit
that carries the Rval/WshP definitions; or strike rsh_interp from the instantiated
list. Precedent class: Codex#4-10 (U-29d5 scope) = gap.

**F3 · GAP — stale §2.D FILE PLACEMENT line contradicts the seam split.** Quote
(§2.D): "**`RS1Bundle`, `RS4Chain`, `ReadOffBundle`, and all of §2.E live in
`MovesS/Interfaces.lean`**". "and all of §2.E" is pre-split text: the governing
§W4-SYNC preamble says "`Interfaces.lean`, which at E-phase contains NOTHING from
this section", and §5's E-PHASE SCOPE agrees. A builder following §2.D's placement
line literally would elaborate seam pins into a core file. Self-correcting within
the document (the split record is marked READ FIRST), hence gap not critical;
repair = strike "and all of §2.E" (and sync the line-843 "§2.E" comment pointer,
O-5). Precedent class: Codex#3-8 (stale SyncDefs references) = gap.

## OBSERVATIONS (uncounted)

- **O-1** §3b edge "U-12b → {U-24a2 plumbing, W-1 hok}" names a seam pin as a
  future consumer — dormant and correctly directed (core feeds seam); tag it
  [seam] at the next touch.
- **O-2** S5 stale sub-labels: the construction header still reads "U-29a1–a1b,
  a2a–a2c, a3a–a3d … nine units" over 12 bullets (the Codex#6-13 splits absent
  from the enumeration); "U-29d-iv…vi" is a 3-slot range over 4 bullets that
  collides with d-i…iv. Census unaffected (recounted exact).
- **O-3** "No split outcomes (S.7: 'the deep convolution is thin')": S.7's display
  is an n = 3 statement (two CONTINUING clusters need degree ≥ 4); at n = 2 a
  (halted+continuing) m = 2 split is not excluded by it. Harmless under R44 (the
  roster is a device needing no note support) — cite is decorative.
- **O-4** Name collision: U-29e's "the W6 CHECK" (the note's W6 geometric-series
  display) vs the pin "W-6" (= AVAgree). Pre-existing; a disambiguating word would
  cost nothing.
- **O-5** Line-843 comment "TYPED XRBPackage, §2.E" — pointer should read §W4-SYNC
  (fold into F3's repair).

---

## COUNTS AND VERDICT

Criticals: **0**. Gaps: **3** (F1 U-17b pool guard; F2 rsh_interp/R44 scope
contradiction; F3 stale §2.E placement line). Observations: 5 (uncounted).

All five directed verifications PASS (self-containment; the Multiset m = 1
pigeonhole with the constructed repeated-factor case; the routed act_iff; the gate
relabeling; U-22b's route). All settled arithmetic recomputed EXACT. Census 45/40/0
EXACT; DAG acyclic. The three gaps are mechanical one-line repairs — no
architectural finding survives; the core's hypothesis-register discipline (R37),
guard consumption (R13/R14/R16), and conditionality tags are intact throughout.

**VERDICT: REJECT (0 crit / 3 gap).** The core is E-phase-ready modulo the three
mechanical repairs; under the campaign bar (clean pass required) this is a
near-miss confirmation, not an acceptance.
