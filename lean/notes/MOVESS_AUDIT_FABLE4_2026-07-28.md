# MovesS Lean blueprint REV 6 — fresh-instance confirmation audit (Fable #4)

- **Date:** 2026-07-28 (run 2026-07-27 session)
- **Auditor:** fresh Fable instance #4 (no prior contact with any MovesS revision)
- **Scope:** confirmation pass on the identical REV-6 text
  (`MOVESS_LEAN_BLUEPRINT_2026-07-28.md`, 1282 lines, read in full), parallel to the
  Codex confirmation on the same text.
- **Ground truth:** `MOVES_2026-07-24.md` lines 11557–12577 read in full. Provenance:
  the §S-RESUM body 11557–~12430 IS rev 6 (it carries the pass-6 "(m, c)
  CLASSIFICATION … REV 6 [pass-6 critical …]" bracket); the DUAL-ACCEPTED record
  verified present at ~12855 ("Codex pass 7 + the Fable confirm, both CLEAN on
  identical rev-6 text") — the blueprint header's citation discipline (acceptance
  record, never the stale in-body trailer) is correct and was followed here.
- **Charge:** `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` checklist (faithfulness /
  non-vacuity / hypothesis fidelity / Defs soundness / decomposition), with six
  directed verifications.

---

## Directed verification 1 — the structural roster pin (R20): PASS, counting adversary defeated

**Spec:** `vEquiv : VType ≃ {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ n}` +
`vdeg_spec : ∀ v, (vdeg v : ℕ) = ((vEquiv v).1.1 : ℕ) * ((vEquiv v).1.2 : ℕ)` (§2.A)
+ `sig_exact : ∀ σ, σ ∈ Sigmas ↔ (σ.map fun v => ((T.vdeg v : ℕ))).sum = n` (§2.D).

**Forcing argument, checked:** vEquiv is an `Equiv`, so the label set is in
BIJECTION with the pairs — no duplicate label (over-count via two labels per pair is
impossible) and no missing pair (under-count impossible). vdeg_spec routes vdeg
THROUGH the bijection, so vdeg cannot be gamed; vdeg : ℕ+ (≥ 1, forced consistent by
e·f ≥ 1) makes {σ | Σ vdeg = n} finite (card σ ≤ n over a Fintype), so the Finset
demanded by the sig_exact iff exists and is UNIQUE. Hence Sigmas is determined
elementwise at every instance — an adversarial instance has zero freedom on either
the catalogue or the roster.

**The ≤ n vs = n subtlety (charged):** the bounds are split correctly across the two
pins — VType carries e·f ≤ n (members of a degree-n splitting type have degree ≤ n;
degree-< n types like (1,1), (1,2), (2,1) are REQUIRED as members, degree-= n types
(1,3)/(3,1) as singletons; every ≤ n pair completes to a degree-n multiset with
(1,1)-padding, so none is junk), while Sigmas carries total = n (ORC-3: "σ := the
multiset of (e_i, f_i) of the certified factorization" — a degree-n factorization has
Σ e_i·f_i = n). Swapping either bound breaks the roster: = n on VType kills
(1,1)³/(1,1)+(1,2)/(1,1)+(2,1) (under-count); ≤ n on Sigmas admits e.g. {(1,1)} at
n = 3 (over-count). As written, at n = 3 the forced enumeration is 1+1+1 → (1,1)³;
1+2 → (1,1)+(1,2), (1,1)+(2,1); 3 → (1,3), (3,1) — EXACTLY the note's display "the
FIVE rational functions R_σ, σ ∈ {(1,1)³, (1,1)+(1,2), (1,3), (1,1)+(2,1), (3,1)}"
(S.7(i)); at n = 2, {(1,1)², (1,2), (2,1)} (U-29d3's claimed degree-2 roster ✓).
Sigmas-nonemptiness honest as a lemma ({(1,n)} witnesses, 1·n ≤ n). PASS.

## Directed verification 2 — the declaration DAG (R25, the rev-5 gap): PASS

Walked as specified. **Defs.lean** internal order: TableShape → SCSData/DegCons →
MeasuredSide → allActivePools → LedgerIV → OKat/evalAt (skeleton sorry) → PolyGeom →
RatBurdens → splitOuts → kTarget/Kmat/bTerm (skeleton) → EscapeE0 → PoolHyp → Aℝ →
AVAgree → MuHat/ReadOwner/Shape/ShapeFam → consumedDeltas (skeleton) → RegP — every
symbol declared before first use (splitOuts now declared in §2.C before U-8/U-16a1
consume it; consumedDeltas after ShapeFam; RegP after both).
**Interfaces.lean** imports {BSplitDef, EvalReDef, ConsumedDeltas, BlockSolve,
BlockSolveTot, RshDef, MarkedDef}, so `evalRe`/`bhatMeas` (U-16a2), `Rsh` (U-18),
`markedPairing` (U-25), `blockSolve`/`blockSolveTot` (U-16b/c) are all in scope for
RS1Bundle → RS4Chain → ReadOffBundle → the W-Props, in that internal order
(RS4Chain.B : RS1Bundle after RS1Bundle; ReadOffBundle cites RS1Bundle/blockSolve/
bhatMeas after both; W1_RS1SH cites RS4Chain after it). Inside RS4Chain,
PrimePools/prime_sub/prime_base now precede legs_reg (the predecessor's Finding-1(i)
field-order blocker is genuinely gone); `rsh_interp`'s `hdet` binder is typed. Phase
E can elaborate the spec as written, modulo Finding 1 below (instance binders, a
different site). The rev-5 gap is repaired, not displaced. PASS.
(Residual label staleness — §2.E's heading and §4 item 1 still say `SyncDefs.lean`
where R25/§2.D place that content in `Interfaces.lean` — observation O-a.)

## Directed verification 3 — generic carriers (R22): PASS on the seam, one instance-binder defect (Finding 1)

U-13 now `[CommRing R]`, U-14 `[Fintype ι] [DecidableEq ι] [Field F]` with the
explicit instantiation notes "Instances at Qq (U-14/16b) AND at ℝ via `Aℝ` (U-24a1)"
/ "F := Qq at the solve; F := ℝ at U-24a1 (det transported by `Aℝ_det_iff`)" — the
predecessor's Finding-2 typing hole (Qq-pinned lemma applied to an ℝ fixpoint) is
closed: U-24a1's β̂ = Aℝ β̂ + b̂ uniqueness now has a carrier-correct supply, with the
det hypothesis crossing via `RingHom.map_det` + `Rat.cast_injective`. U-10's
conclusion is now stated over `Aℝ P` (ℝ), matching D11's corrected prose (O-3
repaired); the derivation chain (tg_interp/j_interp → rowVal → Σ μcell ≥ 0 via
meas_card/xhd_sum) is ℝ-native as claimed. Residual ℚ/ℝ sweep: every mixed statement
(U-24a1, AVAgree, U-24a2, W1m_marked, rsh_interp, tg/j/ι_interp, W1_RS1SH) coerces
only evaluated ℚ-values through `((… : ℚ) : ℝ)`/`algebraMap`/`Aℝ` — no second seam.
BUT: U-13 as displayed omits `[DecidableEq ι]`, without which `1 - K` has no `One
(Matrix ι ι R)` instance — Finding 1 (a family-wide elision, see below). Otherwise
PASS.

## Directed verification 4 — ReadOffBundle (R23): type-level coverage PASS; gate coverage gap (Finding 2)

**Spec (§2.D):** `pkg : ∀ q₀ ∈ S, ∀ e ∈ Finset.Icc 1 n, PoolHyp …` and `read : ∀ q₀
(hq : q₀ ∈ S), ∀ e (he : …), ∀ τA : (pkg q₀ hq e he).Act, ∀ σ' : Multiset T.VType,
∀ h_ent, AVAgree (pkg …) (blockSolve … τA σ') (bhatMeas (pkg …) B σ' h_ent) τA`,
with `S ⊆ allActivePools M`.

Checked against the note's read-off quantifiers: S.4(ii-c) demands the sealed check
PER POOL PER OBJECT ("the sealed check that the evaluated object's q₀-value … equals
the active-subsystem solve there must pass BEFORE it may be read off") and RS.2's
fixedness is claimed at "all-active primes (cofinitely many …)" (S.4(ii)). The
bundle's type quantifies every q₀ ∈ S, every e ∈ Icc 1 n, every τA : Act (= every τ,
since S sits inside the all-active locus where `allActivePools` quantifies ∀ e ∀ τ),
every σ', every h_ent — total coordinate coverage READABLE FROM THE TYPE, per-object
AVAgree preserved as the hypothesis (nothing demanded at pools where the (ii-c) gate
fails, since S is the read-off-valid family), U-24b consuming it as `hread`. The
Codex#2-4 auditability defect is repaired. Arities check (AVAgree : PoolHyp → Qq →
(Act → ℝ) → Act → Prop matches; Finset-coercion of τA into `blockSolve`'s
`T.State e` slot is the standard coe). PASS on the type. However the S5 gate never
instantiates the structure — Finding 2.

## Directed verification 5 — predecessor's directed checks survive rev 6: PASS

- **The guards (Fable C2/R13 + Fable2-C1/R16(i)):** part1, rep_indep, xhd_sum,
  xhd_no_stray, meas_card, kstep_one, hmc, act_target(target-only), init_agg,
  init_count, ent_count_card, comp_once all still carry `M.activeState q₀ e τ`
  exactly as at rev 5; `recursion_meas` and `W3_recursion` still guard with
  IDENTICAL quantifiers (re-diffed field vs W-Prop: same binder list, same guard,
  same evalRe call). Unguarded set unchanged and still correct (d4r0, xhd_no_orphan,
  U-17a's symbolic (R_e-lump), xrb, β_bdd, W-10, U-28). `act_row` absent from live
  code (grep: repair-narration mentions only).
- **U-24a1:** statement, hypothesis list (recursion_meas + xrb + P/E0 + subsystem
  closure), and the no-induction/no-leg-evaluation/no-hok design are unchanged;
  still fires the guard via `act_spec` at τA ∈ P.Act. Closure argument re-walked:
  sound. (Its deps line still reads "U-13, U-14 (over ℚ)" — stale annotation
  contradicting R22/§3c's "F := ℝ at U-24a1"; observation O-b.)
- **The δ-trace (DELTA-ABS/R17):** Member.δ and Shape.δOf comments, `pools_closed
  (∀ δ : ℕ+)`, `consumedDeltas` = multiplicative closure (≤ n factors, empty product
  1) with `nested_delta_mem`, U-12c `powSubst_mul`/`pow_pool`, U-16a3, bSplit's
  `powSubst μ_j.δ`, evalRe's measured legs at q₀^(δ:ℕ) — all verbatim from rev 5;
  the two-route trace (powSubst 3 ∘ powSubst 2 = powSubst 6; (p²)³ → p⁶ → p¹²)
  still composes; "stays inside the roster" still purge-mentions only. The rev-6
  diffs (R20–R25) touched none of these. PASS.

## Directed verification 6 — six random unit spot-checks: ALL PASS

- **U-1 `dispatch_spec`** vs the (m, c) CLASSIFICATION "(c = 0, any m) → b^{term,fin}
  / (c ≥ 1, m ≥ 2) → b^split / (c = 1, m = 1) → a K_e column … EXHAUSTIVE AND
  EXCLUSIVE BY CONSTRUCTION (c ≥ 1 with m = 1 forces c = 1)": the iff-triple under
  h1/hc reproduces exactly the three-row partition of {(m,c) : m ≥ 1, 0 ≤ c ≤ m};
  routeOf's if-chain checked case-by-case. EXACT.
- **U-4/U-5 `scs_flank`/`scs_stage`** vs "(1) m = 1 LEAVES NO ROOM TO SHRINK …
  (2) THE STAGE LAW … W′·D′ = μ·e·g·D = (g·μ)·e·D = ℓ·e·D = W·D": the
  memberOf-injectivity/ne_sel emptiness argument forces flankCount = 0 + singleton
  residual (every step fielded: flank_zero, window_comp, sel_mem, res_sum);
  stage_W/stage_D + U-4 give the displayed chain. EXACT.
- **U-8 `ksub_regroup`** vs "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′} b^{term,fin} +
  (branching-cell one-step mass, per cell once) = 1": pure regroup to the routed
  total (J per split cell once, never the marked T·G), = 1 delegated to U-9a
  (part1 + rep_indep at active pools) and U-9b (infinitude). verdictImage covers the
  (c = 0) columns by construction. EXACT.
- **U-16a1 `bSplit_def`** vs "b_e^split(τ)(σ′) := Σ_{o branching} J_{τ,o}(q) ·
  Σ_{σ′ = σ₁⊎…⊎σ_m} ∏_j β_{e_j,τ_j(o)}(σ_j)(q^{δ_j}) [… ALL branch members;
  τ-halted members contribute FACTOR 1 with σ_j their verdict value]": J
  coefficient, convolution over ALL m members, halted-member indicator forcing the
  verdict singleton (§T.4 cited), continuing legs powSubst μ.δ ∘ βlt with the U-2
  bound. EXACT.
- **U-22 `rs3_det_symbolic`** vs S.4(ii) "at all-active primes (cofinitely many …)
  K_e(p) = A and ρ(A) < 1 gives det(I − A) ≠ 0; a rational function vanishing at
  infinitely many prime evaluations is 0": e bound inside both hypothesis and
  conclusion; infinitude needed and supplied (allActive_infinite — denominators
  vanish at only finitely many pools); contradiction via U-20/U-21c. EXACT.
- **U-28 `rs4_rational_step`** vs "(RS.4) Σ_σ R_σ = 1 identically in q … inherits
  EVERY condition of the block solve": conclusion Σ_{σ ∈ Sigmas} Rsh = 1 with the
  full inherited set explicit in RS4Chain (nine CL-5 inputs, RS.1's set, hns,
  pools_e0 + legs_reg = CL-1's per-pool quantifier at EVERY base prime (R21),
  CL-17(ii)'s WshP, POLY/XHD-s/INIT-RAT/(J-RAT), x3_total = W-4, rs1_equates = W-1e,
  rsh_interp = W-1's shadow); Σ Rsh ∈ OKat p by Subring closure over rsh_interp's
  hoks; prime_base pins "at each prime p". EXACT.

## Fresh sweep (whole blueprint, checklist items 1–5)

Clean: R21's prime_base iff + prime_sub forces every base prime into PrimePools ⊆
Pools with x3_total/rs1_equates/rsh_interp/legs_reg re-domained (the note's "at each
prime p"; prime_infinite correctly demoted); the nine-input ledger still 1:1 against
CL-5 with the only-two-height-sums design note ((COMP-Σ) structural); rowVal =
RS.0(α)'s object, rep_indep verbatim weighted-grouping; the MuHat fence intact
(markedPairing never enters R_σ; W1m gated per pool); PART-2's surplus row has no
carrier; ESCAPE-UNIF absent; no b^ns column anywhere, rexact GIVEN nsNull only; all
open kernels (E0/CL-1, CL-17(ii), XRB/CL-9, HMC, X.3/CL-4, REL.2/CL-8, (SIB)/CL-10,
(J-RAT), (JC-INV), INIT-RAT) live as hypothesis fields/pinned W-Props with owners,
none proved toward, none smuggled into axioms (no new axioms); consumption-DAG
discipline holds (U-24a1/a2/b consume xrb/recursion_meas; nothing proves toward
xrb); §3b acyclic with the U-12c → U-16a3 edge added (O-2 repaired); R24's gate
splits (29b1/b2/b3, 29d1/d2/d3) one display each; census verified by hand:
54 = 21 easy + 33 medium, per-layer 9/4/16/10/6/9 all correct; grep duties: no
`: True` fields, `∨ True` and `act_row` in repair narration only.

---

## Findings

**Finding 1 — GAP (mechanical: missing `[DecidableEq ι]` instance binders wherever
matrix `1`/`^` appear over a generic index; U-13 is the rev-6-touched site).**
Spec texts: U-13 `theorem solve_iff [Fintype ι] [CommRing R] (K : Matrix ι ι R) …
(1 - K) *ᵥ β = b`; also standing since REV 2: `structure EscapeE0 {ι : Type*}
[Fintype ι] (A : Matrix ι ι ℚ)` (field uses `A ^ k`), U-21a/U-21b (`A ^ k`),
U-23a–d (`1 - A`, `A ^ m`). Mathlib's `One (Matrix n n α)` (hence `Monoid`/`^`)
requires `[DecidableEq n]`; none of these declarations carries it (U-14/U-20 do),
so phase E cannot elaborate them as written — the same "elaborates as written"
standard R25 was held to. Semantically vacuous (Classical.decEq inhabits it for any
type; no statement is weakened), one-batch repair across ~7 sites. GAP.

**Finding 2 — GAP (non-vacuity: the new `ReadOffBundle` has no inhabitation unit in
the S5 gate, against R11's standing coverage claim).**
Spec texts: R11 — "U-29 `consistency_n2` inhabits EVERY §2 structure simultaneously
with a nontrivial instance"; §2.D — `structure ReadOffBundle (S : Set ℚ) …` (NEW at
REV 6, R23). The S5 roster (U-29a–e, as split by R24) constructs TableShape,
MeasuredSide, RatBurdens, SCSData/ShapeFam, LedgerIV, DegCons, PoolHyp/E0,
RS1Bundle, pools/legs_reg, RS4Chain — but no `ReadOffBundle`, though it is the
`hread` a wave-2 unit (U-24b) consumes; if it were uninhabitable, U-24b would be
vacuously conditional, which is exactly what the gate exists to exclude. It IS
inhabitable at n = 2 (S := the all-active pools; βmeas := the evaluated solve;
denominator q² + q + 1 ≠ 0 at every q₀ ≥ 2 supplies hok; no split legs), so this is
a missing unit (extend U-29d2/d3 or add U-29d4), or else amend R11's claim. GAP.

## Observations (not counted; no repair demanded)

- **O-a.** §2.E's heading still reads "`MovesS/SyncDefs.lean`" and §4 item 1's grep
  duty still names "Defs/SyncDefs", while R25 and §2.D's FILE PLACEMENT block (the
  governing declarations, stated twice consistently) place all of §2.E in
  `MovesS/Interfaces.lean`. Stale labels only.
- **O-b.** U-24a1's deps line still says "U-13, U-14 (over ℚ)" — the rev-5 phrasing
  Fable#3's Finding 2 quoted — while §3c now pins "F := ℝ at U-24a1". The §3c unit
  specs govern; stale annotation.
- **O-c.** `consumedDeltas` is placed in Defs.lean (§2.D) as a skeleton `sorry`
  while U-16a3 "defines" it — read as: phase E fills the Defs body, U-16a3 proves
  `nested_delta_mem`; worth one clarifying word. Likewise U-25's `markedPairing`
  display takes no `hdet` (Mathlib's `⁻¹` is total) while W1m_marked cites it with
  `hdet` — harmless arity slack; align at phase E.

---

## Counts and verdict

Directed verifications 1–6: ALL PASS (the roster pin forces exactly the note's
roster at every n with the ≤/= bounds correctly split — counting adversary has zero
freedom; the declaration DAG elaborates in order; the generic carriers close the
rev-5 seam; ReadOffBundle's coverage is auditable from its type; every predecessor
directed check survives rev 6 untouched; 6 spot-checks exact). All 8 rev-5-union
repairs (Codex#2-1..6 + Fable#3-G1/G2 + O-2/3/4) verified genuinely in place. No
semantic finding anywhere.

**Findings: 0 critical / 2 gaps** (both mechanical — an instance-binder family and
one missing gate-coverage unit; neither touches faithfulness to a display).

**VERDICT: REJECT (0 crit / 2 gap)** — confirmation withheld on the two mechanical
gaps only; the REV-6 text is semantically clean and both gaps are one-batch repairs
(add `[DecidableEq ι]` at the ~7 matrix-one/pow sites; add a ReadOffBundle instance
unit to the S5 gate or amend R11's coverage claim).
