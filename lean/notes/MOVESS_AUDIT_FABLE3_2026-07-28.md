# MovesS Lean blueprint REV 5 — fresh-instance confirmation audit (Fable #3)

- **Date:** 2026-07-28 (run 2026-07-27 session)
- **Auditor:** fresh Fable instance #3 (no prior contact with any MovesS revision)
- **Scope:** confirmation pass on the identical REV-5 text
  (`MOVESS_LEAN_BLUEPRINT_2026-07-28.md`, 1169 lines, read in full), including the
  charged nested-δ trace. Parallel to a Codex confirmation on the same text.
- **Ground truth:** `MOVES_2026-07-24.md` lines 11557–12577 read in full. Provenance
  check: the §S-RESUM body at 11557–12430 IS rev 6 (it contains the pass-6 (m, c)
  CLASSIFICATION with its "REV 6 [pass-6 critical …]" bracket; the pass-3…7 records
  and the DUAL-ACCEPTED record sit at 12655–12863). The body's trailing STATUS
  paragraph still says "Rev 3 … Awaits pass 3" — a stale note-side trailer
  (observation O-4 below, out of blueprint scope). The blueprint's baseline claim
  ("DUAL-ACCEPTED §S-RESUM rev 6, ~11557–12430") is correct.
- **Charge:** `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` checklist (faithfulness /
  non-vacuity / hypothesis fidelity / Defs soundness / decomposition), with six
  directed verifications.

---

## Directed verification 1 — CONVENTION DELTA-ABS, the nested trace: PASS

**Convention as declared (R17 / §2.A):** "the SEMANTIC base-change index of any
consumed leg is its index relative to the BASE PRIME p ([2r] (e2), 'δ ABSOLUTE');
the STORED `Member.δ`/`Shape.δOf` is the FACTOR contributed at its nesting step, and
nested substitution COMPOSES MULTIPLICATIVELY."

**Checked against the note's own owner display**, [2r] R.1 BASE-INDEX CONVENTION
(MOVES 9423–9438): "δ_j := δ·δ_j^rel, the ABSOLUTE accumulated residue degree …
pool size q_{δ_j} = p^{δ_j} = q_δ^{δ_j^rel}", and (e2) (9514–9515): "the β-argument
is p^{δ_j} with δ_j ABSOLUTE …, = q_δ^{δ_j^rel}". The stored-relative /
semantic-absolute split is therefore the NOTE's own convention: at ambient pool q_δ
the leg's argument is q_δ^(relative factor), and the absolute index is the chain
product. DELTA-ABS is faithful; the purged REV-4 flat reading was the incompatible
one.

**Trace (charged instance), both routes:**
- Two-step (U-12b `powSubst_OKat_evalAt`): evalAt p² (powSubst 3 g) = evalAt (p²)³ g
  = evalAt p⁶ g; with g = powSubst 2 f: evalAt p⁶ (powSubst 2 f) = evalAt (p⁶)² f
  = evalAt p¹² f.
- Composed (U-12c `powSubst_mul` + `pow_pool`): powSubst 3 ∘ powSubst 2 = powSubst 6;
  evalAt p² (powSubst 6 f) = evalAt (p²)⁶ f = evalAt p¹² f. The routes AGREE (p⁶,
  then p¹²), matching q_δ^{δ^rel} at each step and p^{δ·δ^rel} absolutely.

**Coverage:** `consumedDeltas` = all products of ≤ n stored factors from {split-leg
δ's over the roster} ∪ ⋃ Ŝ.δOf images, empty product 1 included. Realizable nesting
chains have ≤ 1 shape factor + ≤ (e−1) ≤ (n−1) split factors ((K-TRI)/U-2: sizes
strictly decrease at m ≥ 2), so length ≤ n — every effective index p^(δ₁···δ_k) is
covered (`nested_delta_mem`, U-16a3's spec obligation); `pools_closed` (∀ δ : ℕ+)
keeps every leg pool inside `Pools`; `RegP`/`legs_reg` then carry E0 packages over
δ = 1 AND every consumed leg pool, wild pools included — the note's widened per-pool
kernel quantifier (S.4: "δ ranging over 1 AND every base-change index a
β_{e_j,τ_j}(q^{δ_j}) leg of b_e^split or RS.1-SH consumes … δ = 1 the base
instance"). Coverage COMPLETE.

**Old-phrasing grep:** "stays inside the roster" occurs ONLY in purge-mentions
(lines 770, 1158); "ABSOLUTE/absolute" occurs at the convention declaration (28),
in verbatim note-quotes (778, 975), and one historical table row (1146). Every live
δ-mention (Member.δ, Shape.δOf, bSplit's powSubst μ.δ, evalRe/U-24a1's measured legs
at q₀^(δ:ℕ), consumedDeltas, RegP, pools_closed, U-12/12b/12c) is consistent with
the declared convention. No residue of the flat reading.

## Directed verification 2 — `sig_exact` at n = 3: PASS

Spec: `sig_exact : ∀ σ, σ ∈ Sigmas ↔ (σ.map fun v => ((T.vdeg v : ℕ))).sum = n`.
Enumeration at n = 3 over the MovesSp verdict vocabulary (one VType per (e, f),
vdeg = e·f): degree-1 types {(1,1)}; degree-2 {(1,2), (2,1)}; degree-3
{(1,3), (3,1)}. Multisets of total degree 3: 1+1+1 → (1,1)³; 1+2 → (1,1)+(1,2) and
(1,1)+(2,1); 3 → (1,3) and (3,1). Exactly FIVE, no more — precisely the note's
S.7(i) roster: "the FIVE rational functions R_σ, σ ∈ {(1,1)³, (1,1)+(1,2), (1,3),
(1,1)+(2,1), (3,1)}". vdeg : VType → ℕ+ excludes degree-0 padding; the empty
multiset is excluded (sum 0). The pin is exact RELATIVE to the instantiated
catalogue, whose content is the named owner's (MovesSp; `finV`/`vdeg` fields) —
correct division. No menu freedom survives (SigSet remains deleted; W-1 and RS.4
inherit the roster through Sigmas).

## Directed verification 3 — the activeState guards: PASS (no silent strengthening; U-24a1 closes)

**Guarded (R13 + R16(i)):** part1, rep_indep, xhd_sum, xhd_no_stray, meas_card,
kstep_one, hmc, init_agg, init_count, ent_count_card, comp_once, recursion_meas +
W3_recursion (identical quantifiers), U-9a/9b/10 ripple. Each is a per-(e,τ,q₀)
MEASURED mass/probability claim, and the note's own scope lines govern exactly
these: "Every probabilistic claim in S.4/SQ.2 is about K_e restricted per CTS-M(ii)
to the ACTIVE block" (S.0 ledger close) and "Scope: realized states only" (S.4).
The measured β_{e,τ} is "the probability, given ONE branch entering state τ" (S.0
typing) — at an unrealized τ the conditioning event is empty, so the note cannot be
demanding the fixpoint there; the guard is the note's scope, not a new one.

**Nothing displayed-unconditional got guarded:** (R_e-lump)'s "[UNCONDITIONAL]" tag
(which contrasts the lump typing with (R_e-exact)'s GIVEN (ns-null)) governs the
SYMBOLIC recursion — U-17a `blockSolve_spec` remains unguarded, every σ′. Likewise
unguarded, matching their displays: d4r0 (disjointness needs no realization),
xhd_no_orphan (h ∉ H(γ) ⟹ event empty — inactivity only adds empty events), W-10
convergence (the note: "CONVERGENCE (unconditional)"), U-28's RS.4 identity, xrb,
β_bdd. act_target keeps its target-side-only form (S.7(iv) displays "every entry
INTO an inactive cell"; the source side is the guards). VERIFIED: the guard set is
exactly the note's scope, in both directions.

**U-24a1 re-walked with the guards:** fires at τA : P.Act; `act_spec` (iff) supplies
`M.activeState q₀ e τA`, so `recursion_meas` applies at every fired coordinate.
Subsystem closure: the K-row sum splits over Act/non-Act; entries into β ∉ Act
evaluate to 0 by `inactive_vanish` (hok suppliable at EVERY pool: tg_ok/j_ok/ι_ok
hold at all pools — dischargeable, since PolyGeom's geometric denominators
∏(1 − q^a) are nonzero at every q₀ = p^δ ≥ 2; the tolerated wild-pool poles live in
the SOLVE quotients, exactly where AVAgree gates). So β̂ := (βmeas)|_Act satisfies
β̂ = Aℝ β̂ + b̂ with b̂ = bhatMeas (bTerm evaluated + split legs as MEASURED values at
q₀^δ, pools_closed-typed — no induction, no leg evaluation, no hok claim);
(1 − Aℝ P) invertible via P.e0 → U-21c → `Aℝ_det_iff`; empty Act trivial
(det_isEmpty / empty type). U-24a1 CLOSES from the note's own displays. (One
carrier residual — Finding 2.)

## Directed verification 4 — U-24b vs the note's RS.2 fixedness: PASS (quantifiers match)

**Blueprint (U-24b):** "GIVEN an INFINITE pool set `S ⊆ allActivePools M` with, at
every q₀ ∈ S, a package P and the AVAgree read-off for every (e, τA, σ') consumed
(the explicit `hread` bundle): any family f that is OK on S and interpolates βmeas
there equals `blockSolve …`"; "at an all-active pool EVERY (e, τ) is active …, so
each coordinate's identification set is ALL of S — no coordinate is identified
outside its activity locus, and none is skipped."

**Note:** S.3 THE SOLVE: "GIVEN det(I − K_e) ≠ 0 in ℚ(q) (S.4), Cramer/adjugate
gives β_e = adj(I − K_e)b_e/det(I − K_e) entrywise …: every β_{e,τ}(σ′) is one
fixed rational function." S.4(ii): "at all-active primes (cofinitely many — only
finitely many primes are roots of some not-identically-zero cell-size polynomial)
K_e(p) = A and ρ(A) < 1 gives det(I − A) ≠ 0".

Comparison: the note's fixedness is symbolic-given-det (covered separately by U-15
Cramer, verbatim); U-24b is R8's DERIVED interpolant-uniqueness anchoring that fixed
function to the measured βmeas — claimed exactly on the note's own locus (all-active,
cofinite/infinite), CONDITIONAL on the per-pool per-object (ii-c) read-off (`hread`,
OPEN, provenance W-6 — "the sealed check … must pass BEFORE it may be read off"),
with `allActive_infinite` only a CANDIDATE-locus supply. Quantifier order matches
(∀ coordinate, uniqueness over the full S; hread per pool per object); no
identification outside a coordinate's activity locus; no overclaim, no silent
discharge of (ii-c). The Codex-4 boundary defect is repaired, not displaced.

## Directed verification 5 — the single coercion point Aℝ: PASS with one residual (Finding 2)

`Aℝ P := P.A.map (algebraMap ℚ ℝ)` declared once in Defs; U-24a1 states its identity
entirely over ℝ (matrix through Aℝ once, bTerm through algebraMap once, legs already
ℝ); AVAgree coerces only the evaluated ℚ-value (`((… : ℚ) : ℝ)`); U-24a2 likewise;
W1m_marked likewise; `Aℝ_det_iff` transports det through `RingHom.map_det` (map
commutes with 1 and sub) + `Rat.cast_injective` — all conceptually well-typed, and
no other coercion site exists in any statement. Residuals: (a) U-13/U-14 are pinned
at carrier `Matrix ι ι Qq` while U-24a1's fixpoint-uniqueness must run over ℝ —
Finding 2; (b) D11's prose lists "U-10's row sums" among mixed-ℝ statements, but
U-10's statement is ℚ-pure (only its PROOF crosses ℝ via rowVal) — cosmetic,
observation O-3.

## Directed verification 6 — unit spot-checks (7 of 50): ALL PASS

- **U-4 `scs_flank`** vs "m = 1 forces NO flank side (the read side spans the
  window: e·ℓ = W) and a SINGLETON residual shape λ = {(g, μ)}" (S.0 (SCS)(1)):
  the memberOf-injectivity/ne_sel argument now genuinely forces flankCount = 0 AND
  resFactors singleton; flank_zero → width 0; window_comp → W = e·ℓ; res_sum →
  g·μ = ℓ. Every step has its field. EXACT.
- **U-7b `bdy_node_shadow`** vs "the first entrance node ν is BLOCK-side as a STATE
  INDEX …, while the edge INTO ν is entrance-side MASS" ((BDY), S.0): at r = fe
  node → block, edge → entrance; owners agree at r ≠ fe. W-8's split (Wcharge over
  Icc 0 fe — entering read INCLUSIVE; βcharge from fe+1) matches "β … charges NO
  mass or height for the entering read". EXACT.
- **U-8 `ksub_regroup`** vs "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′} b_e^{term,fin}(τ)(σ′) +
  (branching-cell one-step mass, per cell once) = 1": correctly decomposed into the
  pure regroup (U-8, RHS = routed total via the (m,c) routeOf) + measured `= 1` at
  active pools (U-9a, part1 + rep_indep) + symbolic (U-9b, infinitude). verdictImage
  covers the (c = 0) columns by construction; J per cell once, never the marked T·G.
  EXACT.
- **U-16a1 `bSplit_def`** vs "b_e^split(τ)(σ′) := Σ_{o branching} J_{τ,o}(q) ·
  Σ_{σ′ = σ₁⊎…⊎σ_m} ∏_j β_{e_j,τ_j(o)}(σ_j)(q^{δ_j}) [… ALL branch members]": the
  pinned def-equation carries J as coefficient, the multiset convolution over ALL m
  members, the halted-member factor-1/verdict-singleton indicator (§T.4 cited), β
  legs at powSubst μ.δ with the ktri bound. EXACT.
- **U-18 `rsh_def`** vs RS.1-SH's display: shConv = Σ over {g // σ = Ŝ.σ0 + Σ g i}
  of ∏ powSubst(δOf i)(blockSolve …); Rsh = Σ_{Ŝ ∈ F.Sh} WshP·shConv — σ₀ ⊎
  decomposition, finite [2a] family, W_Ŝ in the CL-17(ii) presentation. EXACT.
- **U-22 `rs3_det_symbolic`** vs S.4(ii) (quoted above): per-block quantifiers both
  sides; the all-active locus DEFINED, only its infinitude a burden; evaluation vs
  U-21c contradiction. EXACT.
- **U-28 `rs4_rational_step`** vs "(RS.4) Σ_σ R_σ = 1 identically in q … RS.4
  inherits EVERY condition of the block solve": conclusion Σ_{σ ∈ Sigmas} Rsh = 1;
  the full displayed inherited set is explicit in RS4Chain (nine CL-5 inputs, RS.1's
  set, hns, pools_e0 + legs_reg = CL-1's full per-pool quantifier, CL-17(ii)
  presentation, POLY/XHD-s/INIT-RAT/(J-RAT) burdens, x3_total = W-4, rs1_equates =
  W-1e, rsh_interp = W-1's shadow); route = eval at infinitely many base primes
  (prime_base pins δ = 1, the note's "at each prime p") + U-27. EXACT.

## Fresh sweep (whole-blueprint, checklist items 1–5)

Checked and clean: the (m,c)/routeOf routing (exhaustive/exclusive, U-1's iff-triple
= the note's rev-6 classification); DEG-CONS full-roster per-member form; U-2/U-3/
U-5/U-6 = the (SCS) derivation steps with the fenced species edge unclaimed; the
nine-input ledger 1:1 against CL-5 (XHD two-sided exactness representative-
quantified; D4R.0 event disjointness; PART-1 guarded; REP = RS.0(α) weighted-
grouping VERBATIM at row level; MEAS counting-native; HMC open with the hK-free
kstep_one base tie; ACT as guards + the one displayed target law; INIT/ENT-COUNT
with the ε-own-level card tie; COMP-TYPING with the only-two-height-sums design
note); rowVal's uniform cell-sum reading = T·G row on non-split AND the J cell-sum
on split (rep_indep is exactly J's "each cell once" on split outcomes — the pass-1
retype preserved); the MuHat fence (no Add, no coercion; markedPairing never enters
R_σ; identification only via the gated W1m); (ns): no b^ns column exists anywhere,
rexact GIVEN nsNull only; PART-2's surplus row has no carrier; ESCAPE-UNIF absent;
no new axioms; open kernels (E0/CL-1, CL-17(ii), XRB/CL-9, HMC, X.3/CL-4, REL.2/
CL-8, (SIB)/CL-10, (J-RAT), (JC-INV), INIT-RAT, STATE-probe-2) all live as
hypothesis fields/pinned W-Props with owners, none proved toward, none smuggled;
consumption-DAG discipline (§3b) honored; U-29a–e's schema-consistency claim honest
(R11), W6 denominator q² + q + 1 the displayed check; census arithmetic verified
(50 = 20 easy + 30 medium; per-layer sums 9/4/16/10/6/5 all correct — Fable2-G4
genuinely repaired); non-vacuity: every §2.A–D structure is inhabited by the S5
batch.

---

## Findings

**Finding 1 — GAP (mechanical: declaration-order / undefined-symbol regressions in
the Defs skeleton; the R2-3 class, reintroduced by the REV-4/5 additions).**
Spec texts: (i) `RS4Chain.legs_reg : ∀ p, (p:ℚ) ∈ PrimePools → RegP T M RB p hK F`
— but the field `PrimePools` is declared NINE fields later in the same structure; a
Lean structure cannot elaborate this order. (ii) `RS1Bundle.recursion_meas` (and
the pinned `W3_recursion`) reference `evalRe`, and `RS4Chain.rsh_interp` (and
`W1_RS1SH`) reference `Rsh`, and `W1m_marked` references `markedPairing` — yet §5
pins "`bSplit`/`evalRe`/`bTot` live in U-16a/c" and Rsh/markedPairing are U-18/U-25
defs, so `Defs.lean`/`SyncDefs.lean` as laid out cannot see them (either they join
the phase-E skeleton `sorry`s or the interface structures move after S2/S4).
(iii) `splitOuts` is consumed by U-8/U-16a1/U-16c and declared nowhere (unlike
`cells o`, which has its notation comment); `rsh_interp`'s `∀ hdet` binder is
untyped. Violated rule: the blueprint's own "§2 … declaration order = spec;
findings R2-3" header. No semantic content is at stake — the intended statements
are unambiguous — but phase E cannot elaborate the spec as written. GAP.

**Finding 2 — GAP (the one residual of the ℚ/ℝ architecture: U-13/U-14's carrier
does not cover their U-24a1 consumption).**
Spec texts: U-13 `theorem solve_iff [Fintype ι] (K : Matrix ι ι Qq) …`, U-14
`theorem solve_exists_unique … (hdet : (1 - K).det ≠ 0) : ∃! β, β = K *ᵥ β + b`
(both pinned at `Qq`, §3c), consumed by U-24a1 as "deps: U-13, U-14 (over ℚ)". But
U-24a1's fixpoint β̂ = Aℝ β̂ + b̂ and its uniqueness argument live over ℝ (b̂ =
bhatMeas is ℝ-valued; the note's active-subsystem solve is the measured one —
"the evaluated object's q₀-value … equals the active-subsystem solve there",
S.4(ii-c)); a Qq-carrier lemma cannot be applied, and "(over ℚ)" cannot mean the
ℚ-matrix since the exit vector is not ℚ. Repair is trivial (state U-13/U-14 over a
generic `[Field K]`/`[CommRing R]`, or add the ℝ instance), but as written the spec
has a typing hole at exactly the audited seam. GAP.

## Observations (not counted; no repair demanded)

- **O-1.** `consumedDeltas`' closure (all products of ≤ n factors) and
  `pools_e0`'s locus (all all-active POOLS, where S.4(ii) consumes E0 at all-active
  PRIMES) are displayed SUPERSETS of the note's semantic quantifiers — sound
  direction (over-demand of open hypotheses, documented in R17/R9), coverage the
  side that matters. Also: the factor set "over the full roster" must be read as
  e ∈ Icc 1 n for Finset-ness (forced by the ≤ n chain bound; worth one word in
  U-16a3's file).
- **O-2.** U-12c is absent from §3b's edge list though U-16a3 deps on it;
  bookkeeping only (§3b is "load-bearing edges").
- **O-3.** D11's prose lists "U-10's row sums" among mixed-ℝ statements; U-10's
  statement is ℚ-pure (its PROOF crosses ℝ). Cosmetic.
- **O-4.** Note-side: §S-RESUM's in-body STATUS trailer (12412–12430) still narrates
  only through rev 3 ("Awaits pass 3") though the body is rev 6 and DUAL-ACCEPTED
  (12854). Stale trailer; the blueprint's baseline citation is nonetheless correct.

---

## Counts and verdict

Directed verifications 1–6: ALL PASS (DELTA-ABS trace complete and consistent, both
routes agree at p² → p⁶ → p¹²; sig_exact yields exactly the note's five at n = 3;
guards = the note's own scope with nothing displayed-unconditional guarded and
U-24a1 closing; U-24b's locus/quantifiers match the note's own; one coercion point
with one carrier residual; 7 unit spot-checks exact). The 11 REV-4-union repairs
verified genuinely in place; no semantic finding anywhere.

**Findings: 0 critical / 2 gaps** (both mechanical-spec, neither touches
faithfulness to a display).

**VERDICT: REJECT (0 crit / 2 gap)** — confirmation withheld on the two mechanical
gaps only; on semantic faithfulness the REV-5 text is clean, and both gaps are
one-batch repairs (reorder/relocate the interface defs; genericize U-13/U-14's
carrier).
