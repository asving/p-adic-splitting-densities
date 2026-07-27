# FABLE FRESH-INSTANCE VERIFICATION — §U-SQUEEZE rev 4 (2026-07-27)

Verifier: fresh-context Fable (dual bar, Fable half; Codex accepted passes 4+5 CLEAN
on identical rev-4 text). Target: MOVES_2026-07-24.md '## §U-SQUEEZE' (lines
12879–13622). Duties: (a) honesty audit; (b) independent two-sided-squeeze
arithmetic + numeric instance; (c) the four tag-free claims one by one; (d) the
(REG-p) schema vs §S per-pool displays; (e) implication-audit routing spot-checks.

## A. Honesty audit (fresh eyes)

VERIFIED HONEST: Theorem U never described as machine-checked; conditional form at
every claim site; the zero-unconditional banner (opening = STATUS, restated
identically); the NO-CLAIM failure semantics (incl. the removable-auxiliary-zero
NOT-ASSERTED paragraph — which correctly anticipates exactly the case where (r1)
over-excludes, see D-G2); §X's toothless-envelope honesty carried verbatim at both
consumption sites (SQ.1 and gate (L-thy)); TRACK-COUNT quoted verbatim + STATUS
HONESTY on the unexecuted REV 15 kernel unit; the probe scoped candidate-refuter
only; SQ.6's exactness claim literal after the rev-4 CL-17 completion (checked:
SQ.5's consumed list and SQ.6 item 12 both carry CL-17 beyond (ii)); the five σ
for n = 3 exhaustive; 25 = 5×5 bracket pairs correct; (U-n)'s hypothesis stacks
account for all of CL-1..19 (CL-2/3 in the rate form only, CL-4 on the lower
side + limit, CL-12 closed, CL-14 inside "CL-13…CL-16").

ONE GAP found (D-G2 below) — wording-level, conservative direction, in Theorem U's
own display. Plus 5 WATCH items (A-W1..A-W5):
 A-W1 (BOX-N) "tag-free as an identity of counts": disjointness of the decided_τ
   sets rests on T_can^τ's choice-free totality ([1] L2 + VP; ONE-F — VP open at
   CL-10), displayed two sentences earlier. The banner's "definitional count
   identity" is honest only read as "given SQ.1's partition"; recommend adding
   that clause to the banner.
 A-W2 E(e) includes "each entry of ι_e" though R_σ (RS.1-SH) consumes no ι —
   over-inclusive (shrinks the adjudicated prime set; no overclaim), and sits
   oddly next to the notation fence "ι ... appears in NO display of this note".
 A-W3 (L-meas)'s "EQUIVALENT ... by (BOX-N)" also consumes the checksum at p
   (rewriting 1 − R_σ as Σ_{τ≠σ}R_τ(p)); "no envelope hypothesis" is true, but
   the attribution to (BOX-N) alone is loose. Operationally covered by the five
   sealed checksum rows in the same gate.
 A-W4 Q(p)'s parenthetical "one per base-change depth δ in RS.1-SH's assembly"
   should echo S.4's pool quantifier verbatim ("b_e^split or RS.1-SH consumes");
   the broad reading is supported by the note's own "assembled through RS.1-SH"
   usage, but the statement-of-record should not need that inference.
 A-W5 The Codex acceptance banner's "~21 named open kernels": SQ.6 has 25
   top-level entries (1–21 + 13a–d), 24 open after the 13b closure (item 6 stays
   open at (i),(iii)–(ix)). Record-level cosmetic, not in the rev-4 note text.

## B. Independent squeeze arithmetic + numeric instance

Arithmetic walked independently: SQ.3's chain (decided_σ = p^{nN} − Σ_{τ≠σ}
decided_τ − undec, then SQ.2 per τ≠σ + Σ R = 1) is exact; SQ.0(c)'s units check
(interval w*(N) / step 1/D(n) × L(n) tracks = L·D·w*) consistent; env → 0 with
the two-sided bracket forces d_σ → R_σ (squeeze, pure analysis).

Numeric instance (/tmp/usq_squeeze_check.py): n = 2 monic quadratics, exact
decidedness oracle on the D = b²−4c coset image of each level-N residue class
(p odd: full coset, 4 a unit; p = 2: D₀ + 2^{N+1}ℤ₂ b odd / 2^{N+2}ℤ₂ b even,
derived and then brute-validated against depth-6 lift enumeration, 0 mismatches).
 - p = 3 (tame), N = 1..6: R = (3/8, 3/8, 1/4). (BOX-N) exact at every N; upper
   leg d_σ ≤ R_σ EXACT at every (σ,N); lower leg d_σ ≥ R_σ − env; partial sums
   monotone (SQ.2's Neumann picture); |d_σ − R_σ| ≤ env; env = 3^{−N} → 0. ALL PASS.
 - p = 2 (wild), N = 2..8: R = (1/3, 1/3, 1/3). Same five checks ALL PASS;
   env = 4·2^{−N} → 0, d_σ → 1/3 from below.
 - FALSIFICATION DEMO (unplanned but instructive): my first classical-value
   derivation for p = 2 wrongly assumed D uniform on ℤ₂ (4 is not a unit),
   giving R = (1/6, 1/6, 2/3); the EXACT upper leg caught it immediately
   (d_split = 1/4 > 1/6 at N = 2). The gate's "any single-f overshoot falsifies
   SQ.2" discipline demonstrably has teeth; the error was mine, not the note's.

## C. The four tag-free claims

 C1 (BOX-N): the count identity IS definitional GIVEN SQ.1's partition (Undec
   defined as the complement; typemult a function of the tree). The partition's
   choice-freeness carries displayed cites (ONE-F/VP) — see A-W1. VERIFIED with
   that one caveat.
 C2 SQ.3's bracket arithmetic AS arithmetic: exact; every input (SQ.2 per τ≠σ,
   RS.4, env's definition) tagged at the use site. VERIFIED.
 C3 Tonelli extended-value existence in [0, ∞]: correctly retyped to existence
   only — nonneg terms suffice; finiteness/identification carry the displayed
   stack (TREE-N/TREE-EXP-fin, CL-5 mass id, E0, (e1)–(e5), CL-17), and the
   terms' own well-definedness (fiber masses) is inside that tagged stack, not
   claimed by the Tonelli step. VERIFIED.
 C4 env(N) → 0 ⟹ limit forcing in (U-n): pure squeeze given the two displayed
   brackets; env → 0 itself tagged (X.3/CL-4, qualitative). VERIFIED.
Count check: exactly four, opening = STATUS lists identical. VERIFIED.

## D. (REG-p) entry schema vs §S displays

ENTRY-COMPLETE for the evaluation: R_σ is a finite sum of finite products of
W_Ŝ and β entries (no division at assembly level), so (r2) over E(e) = {K_e,
b_e both components + per-cell J (CL-18), ι_e, W_Ŝ, every β at every pool}
+ (r1) does license the literal-vs-ACT identification; R_σ itself needs no
separate row. Failure semantics coherent (NO-CLAIM; removable-zero case typed).
Q(p) finiteness rides CL-14's finite catalogue — tagged. Two findings:
 D-G2 (GAP, wording; the one finding above WATCH): the gloss "it is §S's
   per-pool ESCAPE(E0)/CL-1 + the CTS-M(ii) ACT ... (ii-c)/CL-5" (SQ.4) and
   "(its CONTENT already rides in the solve stack's E0 + CL-5 ACT citations
   above)" ((U-n)) overstate an identification. The operative schema (r1)∧(r2)
   is NEITHER implied by NOR implies E0+ACT: (r1) requires the FULL
   det(I − K_e(q₀)) ≠ 0 including junk blocks, which §S S.4 explicitly does NOT
   require ("a blanket det(I − D_{q₀}) ≠ 0 is NOT required"; a junk zero is a
   FINDING not a FAIL), and E0's ρ(A) < 1 is not implied by (r1). Direction is
   CONSERVATIVE (stronger hypothesis ⟹ fewer adjudicated primes; the NO-CLAIM
   semantics absorbs it — no overclaim, and the NOT-ASSERTED paragraph already
   anticipates the over-exclusion case). But the statement-of-record should not
   assert the identity: repair is one clause at each site, e.g. "it NAMES the
   evaluation-step face of (and strengthens at wild pools) §S's per-pool
   E0/ACT burdens". No downstream breakage: the DAG already treats (REG-p) as
   the ONE explicit hypothesis rather than deriving it from CL items.
 D-W (= A-W4): Q(p)'s parenthetical vs S.4's "b_e^split or RS.1-SH" pool
   quantifier — echo it verbatim.

## E. Implication-audit routing spot-checks (3 CL items)

Checked against ASSEMBLY_PLAN_2026-07-26.md §0 event rows + the CL ledger:
 E1 CL-6 (iv)-POLY, owner [1v]: NOT in the plan's [1v]-FULL blocker list (six
   fences + HMC) nor any event row ⟹ must appear in the [4] row's residual
   table inputs — it does. Route CONSISTENT.
 E2 CL-15 = X.1a, owner [5]: the [5] EVENT row (plan and note, verbatim match:
   WEIGHT-CHARGE, (X1a-ALIGN), (X2-*), VP-SOUND, X-n3/STALL) does NOT carry
   X.1a itself ⟹ residual table input — it is. The audit's [5]-carries list
   (CL-2, CL-3, CL-4, (X1a-ALIGN)) matches the plan row. CONSISTENT.
 E3 CL-9: ledger "(β) IS the prover of XRB ... proved in [3], discharged at the
   acceptance-only edge [3] → [3t]-FULL"; note DAG has [3t]-FULL ⇐ [3] EVENT
   (+ [5], (SIB)/(SIB-STEP), (JC-multi), VP-SOUND cites), matching the plan's
   [3t]-FULL row. The audit's "CL-9 discharges at the acceptance-only edge"
   claim CONSISTENT.
 Incidental: CL-16's two faces route correctly (M4b-T-AUD fence at [2b]; the
 [1v] face in the residuals); the note's [1v]-FULL row is a superset of the
 plan's "exactly six fences + HMC" (adds the owed deliverables) — conservative,
 per the pass-1 crit-2 repair; events can only fire later, never earlier.

## VERDICT

0 CRITICALS. 1 GAP (D-G2 — the (REG-p)↔(E0+ACT) identification gloss at two
sites in Theorem U/(U-n); conservative direction, one-clause repairs). 5 WATCH
(A-W1..A-W5). The squeeze arithmetic, the four tag-free claims, the entry
schema's completeness, the failure semantics, and the spot-checked routings all
VERIFY; the numeric instance passes every check at both a tame and a wild prime
and demonstrated the upper leg's falsification teeth against a planted-by-
accident wrong R_σ. Per the campaign's dual-bar discipline (a gap on the
statement-of-record triggers a repair rev before acceptance on identical text):
NOT CLEAN as rev 4 stands — expected to be CLEAN after the D-G2 clause repairs
(+ optionally A-W1/A-W4), then a confirm on the repaired text.
