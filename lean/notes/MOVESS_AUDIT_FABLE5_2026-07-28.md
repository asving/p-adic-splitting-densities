# MovesS blueprint REV 7 — fresh-instance confirmation audit (Fable #5)

Date: 2026-07-28 · Auditor: fresh Fable instance #5 (no prior MovesS context) ·
Scope: REV-7 closing confirmation per `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`,
including independent recomputation of the R26 n = 2 instance. Ground truth:
`MOVES_2026-07-24.md` §S-RESUM (11557–12430, in-place rev 6) + the in-place
(m,c) amendment (~12840) + the DUAL-ACCEPTED record (~12855, verified present).
Blueprint: `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (1400 lines, read in full).
Method: recomputation by exact Fraction arithmetic (cross-multiplied identities
checked at 10 rational points, degree margin ample), display-by-display
comparison, full 68-unit sweep. I judge; I fix nothing.

## 0. The n = 2 recomputation (charge item 1) — ARITHMETIC ALL EXACT

Recomputed independently, all five R26 displays confirmed:
- row masses: q⁻³ + (1 − q⁻¹) + (q⁻¹ − q⁻³) = 1 identically ✓ (at q = 2:
  1/8 + 1/2 + 3/8); every mass ≥ 0 at q ≥ 2 ✓;
- E0 entry: q₀⁻³ ≤ 1/8 < 1 at every q₀ ≥ 2 ✓ (the msW_eighth_le 1/8 face at
  q = 2 ✓, checked against `OM/SeriesAssembly.lean:200`);
- det(1 − K) = 1 − q⁻³ = (q−1)(q²+q+1)/q³ ✓ (q³−1 = (q−1)(q²+q+1) ✓);
- β_{(1,2)} = (q⁻¹−q⁻³)/(1−q⁻³) = (q+1)/(q²+q+1) ✓; β_{(1,1)²} =
  (1−q⁻¹)/(1−q⁻³) = q²/(q²+q+1) ✓ — the note's displayed denominator
  (11648–49, 12399–2400) EXACTLY; sum = 1 ✓ (3/7 + 4/7 at q = 2).
Row-mass-level joint consistency (part1 = 1 with kernel entry < 1 and a
nonsingular 1×1 solve) HOLDS — Codex's rev-6 one-outcome impossibility is
gone at the roster level. But joint inhabitability fails at two OTHER
components of the same gate — the two criticals below.

## Findings

### F1 · CRITICAL — U-29b3's window data is uninhabitable against SCSData's own laws

Quote (U-29b3, §3 S5): "SCS at o_K: the single member has size 2 = e ✓
(window data W=2, D=1, ℓ=2, g=1, μ=2)."
Cite: SCSData laws `window_comp : W = e * ℓ + flankWidth` and
`cluster_child : … size = W' * D'` with `stage_W : W' = μsel`, `stage_D : D' = e·g·D` (§2.A).
With e = 2, W = 2, ℓ = 2: window_comp demands 2 = 4 + flankWidth — insoluble
in ℕ (recomputed: W − e·ℓ = −2). And W′·D′ = μ·(e·g·D) = 2·2 = 4 ≠ 2 = the
member's size, violating cluster_child (equivalently U-5's W′D′ = WD = 2).
No SCSData instance with the displayed values exists; U-29b3 as specced is
unprovable, and the S5 joint-inhabitation gate fails at the SCS component —
the same failure class as Codex#3-1, one layer down. The laws force
ℓ = g = μ = 1 (then W = e·ℓ = 2 ✓, W′D′ = 1·2 = 2 ✓); the displayed μ = 2
appears to conflate o_K's in-block window with the note's ROOT-ENTRANCE
typing "μ = 2 cluster into the size-2 block" (11858–60), which is entrance-
side data, not the kcol outcome's. Classification: CRITICAL (uninhabitable
instance data in the gate whose whole point is joint inhabitation).

### F2 · CRITICAL — `PolyGeom.geom_denom_dvd` excludes q-power denominators; RatBurdens is uninhabitable on the note's own n = 2 masses

Quote (§2.C): "`geom_denom_dvd : geom.denom ∣ ∏ a ∈ geomDenoms,
(1 - Polynomial.X ^ (a:ℕ))` — 'G ∈ ℚ(q) with geometric denominators
(1 − q^{−a})' (cleared form)".
Cite vs note (S.3, 11633): "G ∈ ℚ(q) with geometric denominators (1 − q^{−a})".
Every factor 1 − X^a (a ≥ 1) has constant term 1, so the product is coprime
to X; `count` is a polynomial; hence val = count·geom can NEVER have a
q-power in its reduced denominator. But the instance's three row masses
reduce to denominators q³, q, q³ (numerators 1, q−1, q²−1 — constant terms
≠ 0, verified), and `tg_interp` + pool infinitude FORCE tgP.val to equal
exactly those functions. So RatBurdens at the R26 roster (U-29a: "RatBurdens
data (q⁻³, 1−q⁻¹, q⁻¹−q⁻³) in PolyGeom form") is uninhabitable, and with it
U-29c's Kmat entry, U-29e's det = (q³−1)/q³, and the whole S5 gate. The
mathematical root: clearing 1 − q^{−a} gives (q^a − 1)/q^a — the q-power
lands in the NUMERATOR only for the pure series 1/(1−q^{−a}); a shifted or
finite XHD-s sum (e.g. the single-height G = q^{−c}, the note's "no HMC at
k = 1" case) keeps q^c in the denominator. The pin is therefore STRONGER
than the note's display and excludes the intended wave-4 CTS instance too
(every one-step mass is count/q^level). Present since REV 3 (R2-7); survived
four audits; first exposed by the R26 instance's explicit masses.
Consumers blocked: tgP/jP/ιP, RS4Chain.WshP (same PolyGeom), U-29a/c/e.
Classification: CRITICAL (Defs skeleton unsound: statement stronger than the
note; the note's own displayed objects are excluded).

### F3 · GAP — W17ii's carriers `ιDom'`/`shWeight` are prose-deferred, violating R10's own pin rule

Quote (§2.E): "HasSum (fun h : M.ιDom' Ŝ => shWeight Ŝ h q₀) (C.WshVal Ŝ q₀)
… (ιDom'/shWeight: the Ŝ-level analogues … added to MeasuredSide at phase E)".
Neither is a field of MeasuredSide (§2.B); the pinned Prop cannot elaborate
as written — exactly the "no prose deferrals" defect R10 was ruled to
eliminate. (Cosmetic: `def W17ii` also sits outside §2.E's lean code fence,
lines 782–783.) The rest of the R27 tether is sound: `wshval_bdd` (mass),
`shEvt`/`wshval_card` (counting face, R7 idiom), owners [1v]/[3t] named,
CL-17(ii) kept OPEN with the note's acceptance fence quoted. GAP
(underspecified Defs dependency in a load-bearing pin).

### F4 · GAP — DecidableEq batch incomplete: U-15 omitted

Quote (U-13 batch note): "`[DecidableEq ι]` is likewise added at EVERY
generic-index matrix `1`/`^` site — EscapeE0 (§2.C, done), U-21a, U-21b,
U-23a, U-23b, U-23c, U-23d".
U-15 `solve_cramer` uses `(1 - K)⁻¹`, `(1 - K).det`, `.adjugate` over the
same generic ι (Mathlib `Matrix.det`/`⁻¹` need `DecidableEq ι`) and its §3c
display shows no instance binders; it is absent from the enumeration. Same
mechanical class as Fable#4-F1. GAP.

## Clean checks (charge items 2–7)

- W-bound pins (item 2): `tg_deg`/`j_deg` = Wloc + Wstate — faithful to
  "T … degree ≤ W_loc(m) and each cell size … ≤ W_state(s)" (product bound =
  sum; W-data fixed on TableShape/MeasuredSide BEFORE RatBurdens, so degBound
  is no longer chosen after the polynomial — R27's point holds); `ι_deg` =
  Went verbatim ("degree ≤ W_ent(ε)"). j_deg's bound is an interpolation of
  J-RAT's "per the (iv)-POLY pattern" (note displays no J-specific bound) —
  acceptable: strengthens a hypothesis field only, and Wloc/Wstate are the
  instantiator's data. PASS.
- W_Ŝ tether (item 3): mass + counting face + pinned W17ii with owners,
  CL-17(ii) held OPEN, capstone fence quoted — PASS modulo F3.
- S5 one-display splits (item 4): b1 → 7 one-FIELD units (LedgerIV items
  (1)–(5): 3 XHD + d4r0 + part1 + rep_indep + meas_card = 7 ✓); b2 → 4
  (items (6)–(9) ✓); d1 → 3 ✓; d3 → 3 ✓; U-29e single display ✓. Spot-checked
  n2_part1 (the display, field_simp-able ✓), n2_kstep_hmc (kstep k = q₀⁻³ᵏ,
  1×1 geometric ✓), n2_sigmas (degree-2 multisets over vEquiv's three types
  (1,1),(1,2),(2,1) are exactly {(1,1)², (1,2), (2,1)} — recomputed ✓),
  n2_act (all-active, vacuous inactive case ✓), n2_recursion (β̂ = q₀⁻³β̂ + b̂
  checked exactly ✓). PASS.
- U-29d5 (item 5): S = all-active pools (instance: all prime powers,
  infinite); hok from q₀²+q₀+1 ≥ 7 ≠ 0 at q₀ ≥ 2 on the REDUCED denominators;
  active solve = the explicit values (verified: (q₀⁻¹−q₀⁻³)/(1−q₀⁻³) =
  (q₀+1)/(q₀²+q₀+1)); off-support σ′ coordinates read 0 = 0; the e = 1 slice
  satisfiable with State 1 = Empty (U-21c's det_isEmpty covers the empty Act;
  worth one line in U-29a at repair, observation only). Inhabitation argument
  SOUND — modulo F1/F2 blocking the upstream instance data. PASS-conditional.
- DecidableEq batch (item 6): grep of every `1`/`^`/det/inv site — EscapeE0,
  U-13, U-14, U-20 display it; U-21a/b, U-23a–d covered by the batch note;
  Kmat/Aℝ sites ride TableShape.deq/Finset coercion ✓. One omission = F4.
- Random spot-checks (item 7; 10 > 6 done): U-1 (route iff-triple vs the
  (m,c) display — exact, incl. c≥1∧m=1 ⟹ c=1 ✓); U-4/U-5/U-6 (the SCS chain
  vs SP.1/SP.2 quotes — every step has its field since R12/R15 ✓); U-8
  ((K-SUB) regroup, third summand = Σ J per cell once, never marked T·G ✓);
  U-16a1 (halted-member factor-1/verdict-singleton indicator = §T.4's leaf
  convention, displayed ✓); U-22 (S.4(ii) verbatim, quantifiers per-block ✓);
  U-25 (μ̂ fence, ι once on the left ✓); U-28 (full inherited set explicit in
  RS4Chain, acceptance fence verbatim ✓); U-7a/b/c + W8 ((BDY): edge-into-ν
  entrance-side, node block-side, β charges nothing for the entering read ✓);
  U-24a1/a2/b (per-pool guards consumed; (ii-c) a hypothesis, never claimed ✓).
- Fresh sweep of all 68: census recounted exactly (S0:9 S1:4 S2:16 S3:10
  S4:6 S5:23 = 68; easy 18 + 14 = 32, medium 27 + 9 = 36 ✓). The nine-input
  ledger maps 1:1 to S.0's CL-5 roster ✓. No `True` fields, no vacuous
  disjuncts, PART-2's surplus row carrierless, ESCAPE-UNIF absent, xrb/hmc/
  e0/x3_total/W-pins all honest OPEN hypotheses with owners ✓. DELTA-ABS,
  prime_base iff, vEquiv/sig_exact (n = 3 roster = exactly the note's five —
  recomputed) re-verified standing. Header correctly cites the ACCEPTANCE
  RECORD (~12855, confirmed DUAL-ACCEPTED on rev-6 text), not the stale
  in-body trailer.

## Counts and verdict

CRITICAL: 2 (F1 U-29b3 window data; F2 PolyGeom.geom_denom_dvd).
GAP: 2 (F3 W17ii carriers; F4 DecidableEq batch/U-15).

**REJECT (2 crit / 2 gap)**

Both criticals are inhabitability failures inside the rev-7 headline repair's
own perimeter — the R26 arithmetic itself is exact (every display recomputed
and confirmed), but the gate's SCS window data contradicts SCSData's laws,
and the PolyGeom presentation layer cannot carry the very masses R26 pins.
Both have evident local repairs (ℓ = g = μ = 1; allow an X^c factor in
geom_denom_dvd's product) — for the repairer, not this auditor.
