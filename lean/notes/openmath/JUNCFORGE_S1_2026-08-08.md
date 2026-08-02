# FORGE junc_bundle STAGE 1 — the first deep run (numerics): the clause-(iii) out-of-carrier residual measured, ALL 10 preregistered rows GREEN first-pass (4,116 samples), the two-scale law pinned, the compiled-gate D0 stratum exposed, stage-2 spec fixed

**Unit:** FORGE junc_bundle stage 1 (SYNTHESIS_PASS6 queue #2, the F1 charter —
hardest-first; carries the pass-6 F6 StageCore docstring sync).
**Harness:** `verification/openmath/juncforge_stage1.py` (preregistration header
SEALED pre-run at commit 023a9d7; output `juncforge_stage1_output.txt`, JSON
`juncforge_stage1_results.json`).  Deterministic seed 20260816, exact arithmetic;
machinery = grb_order2_check Towers (N-1-certified) + strata_probe Composite
anchors; CERT (T1/T2/T5/T11+PARI) re-run per instance.
**Scope:** 7 tower rows (e₀ ∈ {1,2,3}, e₁ ∈ {2,3}, g₁ = 2 row N; e₁g₁ ≥ 2 so
deg Φ₂ > deg Φ₁) × 4 base rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]} = 28 instances; per
instance families D0 (f = Φ₂), D1/D2/DA (f = Φ₂ + perturbation, controlled
weights/digits/anchors), D3 (f = Φ₂² + D, deg f > deg Φ₂), D4 (refinement
control, report-only).  Every measured f has deg f > deg Φ₁ — the corpus's
first deep runs with real digit data.

## S1. VERDICT — ALL GREEN on every preregistered row (first pass)

| row | content | pred | obs (samples) |
|---|---|---|---|
| P0 | CERT on all 28 instances (bug detector) | 0 | 0 GREEN |
| P1 | MacLane/K1 commutation at the terminal key (bug det.) | 0 | 0 (392) GREEN |
| P4n | pooled run classes nonzero (val, κ) (bug det.) | 0 | 0 (784) GREEN |
| P2 | terminal case census (D0 KEY-ONLY / D1,D2,DA TIE-AUG) | 0 | 0 (336) GREEN |
| P3a | side-endpoint support == on-line set | 0 | 0 (336) GREEN |
| P3b | stage-scale support == {top vertex} at FLAT and MID | 0 | 0 (336) GREEN |
| P3c | as-written meter: S(FLAT) ≠ S(side) at ALL sites | =336 | 336/336 MATCH |
| P5 | node-1 pattern tie (ψ₁ exact; D3 μ=2, width 2g₁) | 0 | 0 (336) GREEN |
| P6 | seam legs width/window/steep | 0 | 0 (700) GREEN |
| P4 | ITER-LAW on run-realized classes | 0 | 0 (840) GREEN |
| P7 | DA terminal digit == anchor coordinate (u₀ class) | 0 | 0 (56) GREEN |

Census: D0 28/28 KEY-ONLY; D1 84/84 + D2 112/112 + DA 56/56 TIE-AUG (λ₃ ∈
{1,…,16}, all strictly > 0); D3 56/56 MULTI (width-2 terminal polygon); D4
56/56 REFINE.  Exit 0.  4,116 preregistered samples + CERT.

## S2. THE MEASURED CLAUSE-(iii) RESIDUAL SHAPE (the charter's hardest item)

Vocabulary: at a read site with key Φ and development f = Σ B_j Φ^j, a stage
valuation is λ-augmented MacLane — cumulative slot functional w(B_j) + j·λ —
with λ = flat (= w(Φ), the pre-read stage's own diagonal) up to λ_side (the
read side's endpoint, = γ₂/e₁ at node 1; the σV/regraded scale = harness w₂).
The stage residual σ.R f is carried by the argmin slot set S(λ).

**(a) The two-scale law (P3, 336/336 sites, zero exceptions).**  At every deep
read site (deg f > deg Φ): S(λ_side) = exactly the recorded on-line pattern
set; for EVERY strictly coarser λ (flat and midpoint probed), S(λ) = {top
slot} — the single monic key-power vertex.  So the σ.R-rendering of clause
(iii) reads the recorded `(a, Ranch, μ)` pattern IF AND ONLY IF the node's
stage is graded at the read's own pair (the read is FLAT at its stage); at any
coarser stage scale, σ.R f is the key-power MONOMIAL R(B_top)·T^{s·jtop} —
zero ψ/μ/pattern content.  This CONFIRMS at nature the clause-(iii) E-PHASE
FLAG (HC2/Defs.lean: "the σ.R f rendering … may over-strengthen") and pins the
repairless cure: **the corpus's own compiled convention already builds child
stages at the child-read pair** (HK25's σ₁rec is the (1,3)-stage = exactly the
recentering side; U31's base read is the (1,1) diagonal) — so clause (iii) is
honest AS WRITTEN provided the run's stages are read-pair-graded.  At such a
stage the residual is interface-DERIVABLE from clauses (i)+(ii): σ.R f =
Σ_{on-line} R(B_j)·T^{sj} by hRmul + hRΦ + hS5 + hRadd/hRlt, the on-line
terms occupying CONSECUTIVE DISTINCT Laurent positions (a+k, verified in the
pattern reads) — no cancellation possible, so no opacity remains.

**(b) The terminal (deg f = deg Φ) site (P2).**  With B₀ := f − Φ₂ ≠ 0 and
w₂(B₀) > w₂(Φ₂) (252/252 non-degenerate sites): the residual is the RANK-2
BINOMIAL R f = R(B₀) + T^s — ONE carrier digit + ONE pure key letter; Ranch =
pat₀ + z (recentering shape), μ = 1, center = −pat₀.  WHERE the digit lives:
the measured coordinate κ₀ := val(B₀)/val(φ_{w₂(B₀)}) — the 𝒟₂ canonical-
anchor coordinate — takes 105× the value 1, 95× z̄-powers, 52× GENERAL
K2-units (row-N/K raw values; JSON census) — i.e. the free hS6b-type unit
range, pinned exactly on designed anchors: P7, 56/56, κ₀ == the u₀ scalar
class verbatim.  **The out-of-carrier residual at deg f = deg Φ is therefore
NOT opaque on real runs: it is the two-term sum of one in-carrier residual
(whose digit is a 𝒟₂-anchor coordinate) and the interface-pinned key residual
T^s.**

**(c) The degenerate stratum D0 (f = Φ exactly) — the compiled gate's own
shape.**  28/28 KEY-ONLY: R f = R(Φ) = T^s, Ranch = 1, μ = 0 — the residual
holds NO pattern data.  A recentering-shaped recorded node (pat₀ ≠ 0 at slot
0, Ranch = z − c, μ = 1) is UNSATISFIABLE here: the unique development of
f = Φ in key Φ has B₀ = 0, so bundle clause (ii) (demands B(s0) ≠ 0) and
clause (iii) (monomial vs binomial) both fail.  **Lean-side flag (measured
shape, NOT a Lean proof):** `gate_glue_junction`'s `hbundle`
(H1/GlueRun.lean:1105) instantiates exactly this stratum — f = fq =
HK25.σ₁rec.Φ, junction node ν₁rcRoot with `hpat0 : pat 0 = −rcCenter ≠ 0`
(RCWitness.lean:213) — so `hbundle` appears INSTANCE-FALSE (hence
`gate_glue_conditional` vacuous), the one unverified step being development
uniqueness at a monic key (Fact A; standard, Lean-checkable via
divModByMonic uniqueness).  Queued for stage 2 as a small probe +
orchestrator adjudication of the gate's display text.  The D-1 "wall" at the
compiled seam is thus not an opacity wall at all: it is the degenerate
stratum; the dischargeable junction lives at deg σ₁.Φ < deg f — consistent
with `DIterJunctionSupplier`'s own antecedent `σ₁.Φ.natDegree < n`.

## S3. ITER-LAW WHERE §S3 PREDICTS (DITER_RESTATE_2026-08-08 §S3(b))

840 pair-samples on RUN-REALIZED classes (the deep reads' own on-line slot
classes B_jΦ₁^j and terminal B₀ digits, in-window shifted, anchor coordinates
κ): val(χ_a·χ_b) == κ_a·κ_b·c_ITER(γ_a,γ_b)·val(φ_{γ_a+γ_b}) with the
two-constant fibred cocycle EXACT, 0/840.  The constants genuinely appear in
the junction bundle's own digit algebra (c ≠ 1 pair meters per row: A 2/120,
B 0/120, C 25/120, K 50/120, L 64/120, M 49/120, N 5/120).  Honest display:
row B's realized pool grades happened to be carry-free (e₀ = 1, c = z̄^{δ₂}
needs an s₂-carry) — the law held there trivially; rows A/N did realize
carries.  This is the §S3 consumable confirmed at the exact place the
supplier will compute: deep digits ARE 𝒟₂-anchor coordinates, multiplied by
(ITER-LAW) — never a single-ζ′ cyclic constant (fence intact; nothing here
weakens the 22/28 refutation).

## S4. gate_glue_junction HYPOTHESIS SHAPE vs THE MEASURED RUNS

Hold AS-IS on every measured seam (0 violations): `seam_width` (deg Φ₂ =
e₁g₁·deg Φ₁, 28/28 rows), `seam_window` (terminal s0 + wSide ≤ μ₁: 1 ≤ 1 at
D1/D2/DA, 2 ≤ 2 at D3 — the window leg is TIGHT at both depths),
`seam_steep` (strict per-seam augmentation: λ₃ > 0 at all 252 TIE sites),
`ends_at` (node-1 pattern = ψ₁ exactly, μ₁ = 1; D3: μ₁ = 2, width 2g₁ —
landing tie exact reading C).  Bezout ties (`seam_s_tie`/`seam_t_tie`):
convention-internal, consistent by construction (eq12 normalized pair).
NEED THE RESIDUAL (i.e. need the stage graded at the read pair): exactly
`junc_bundle` clauses (ii)+(iii) — per S2(a) they hold and are derivable at
read-pair-graded stages, fail at every coarser scale, and are unsatisfiable
at the D0 stratum.  RG-2 fence respected by the measured geometry: the deep
junction reads at e₁ ≥ 2 sit at the glued BASE (L₁ = 1 seams — our runs'
shape), never interior.

## S5. STAGE-2 LEAN FORGE SPEC (exact structures; the smallest all-green instance)

Target tower: row A over ℤ₂ (every field = F₂; e₀ = 1 so the supplier's
ITER-LAW hypothesis DEGENERATES to the theorem-backed D-REAL leg — the
stage-2 gate is ITER-LAW-free, an honest scope display).  Compiled data
(harness-exact): Φ₀ = X, Φ₁ = X + 2, Φ₂ = X² + 4X + 12, ψ₀ = ψ₁ = z + 1
(F₂), γ₂ = 3, w₂(Φ₂) = 6; classificand **f = Φ₂ + 2⁴ = X² + 4X + 28**
(deg f = 2 > deg Φ₁ = 1: a genuine deep run).  Run data: node-0 read at X:
dev (28, 4, 1), v = (2,2,0), side (1,1) width 2, on-line {0,2}, pattern
(1,0,1) = ψ₀², μ₀ = 2, lands Φ₁.  Node-1 DEEP read at Φ₁: dev f = 24 + Φ₁²,
w1 = (3,∞,0), side pair (2,3) (γ = 6, on-line {0,2}), pattern (1,1) = ψ₁,
μ₁ = 1, lands Φ₂.  Terminal at Φ₂: dev (16, 1), λ₃ = 2, κ₀ = 1, recentering
shape z + 1.  Structures to instantiate:
1. Base stage at Φ₀ = X over K = F₂ (U31.bStage pattern, simpler: no F4).
2. Node-0 `SideReads` for f (flat (1,1) read; U31 shape with width-2 ψ₀²
   pattern, μ = 2) + full 1-node `ReadsOf` H₁.
3. **The junction stage σ₁ at key Φ₁ BUILT AT THE READ PAIR (e′,h′) = (2,3)**
   (IAug: 3 > 2·w1(Φ₁) = 2 ✓) — THE SPEC'S CENTRAL PIN from S2(a): with
   σ₁ graded at (2,3), the node-1 read is flat at its own stage and clause
   (iii) is derivable: σ.R f = R(24)·T^{−t·3} + T^{2s} at consecutive
   positions (with the 0 ≤ t < e convention (s,t) = (−1,1): positions −3,
   −2), Ranch = 1 + z = ψ₁, a = −3, μ = 1.  Route: HC1 S9_transStage-style
   construction or a hand-rolled concrete stage (R defined by the actual
   graded computation — NOT choice-built, so nothing is opaque).
4. The junction node ν₁ (root species for the truncated H₂; recorded
   (a, Ranch, μ) = the harness values above) + `junc_bundle` discharged
   clause-by-clause: (i)/(ii) from the compiled digits, (iii) per 3, (iv)
   LandingKey = Φ₂, (v) polOM lift + canonRoot, (vi) vertex read-off at
   slot μ₁ = 1 of f's Φ₂-development (digit of B₁ = 1).
5. Fire the `gate_glue_junction` analog at the deep seam H₁(root read of f)
   → σ₁ → H₂ (truncated, base = ν₁, continuation to Φ₂): L₁ = 1, so the
   e = 2 junction read sits at the glued base — ALSO the first compiled
   e ≥ 2 junction instance (the C-e escapee finally fed).  Then
   `gate_glue_conditional` fires UN-hypothesized at this seam.
6. Support kernel needed: development uniqueness at a monic key (Fact A;
   mathlib divModByMonic route; price S) — used by 3/4 and by the D0
   vacuity probe (S2(c)).
Honest blocker note: none found at this scope — every ingredient measured
green; the ONLY statement-adjacent item is the S2(c) vacuity probe, which is
an adjudication (display text of the existing gate), not a prerequisite.

## S6. WHAT THIS UNIT DOES NOT CLAIM

Numerics are falsifiers, never proofs: no Lean statement is proved/refuted
here; S2(c) is a flagged observation pending a Lean check.  No order ≥ 3
claim; no touch of sealed strata-probe/GRB rows; ITER-LAW remains the OPEN
LEMMA of DITER_RESTATE §S2 (this unit only confirms it 0/840 on a NEW class
family — run-realized classes — extending the falsifier record).  D4
(refinement stratum) carried report-only as preregistered.

## S7. CARRIED F6 ITEM — StageCore docstring sync (comment-only)

`lean/LeanUrat/Moves/DefsCore.lean`: the `StageCore` docstring (and the
`TransitionCore` docstring's same-name cite) no longer point at the retired
FAITHLESS `L1.baseStage_exists`/`L4.TRANSstage`/`L5.recTRANSRS`; they now
name the live chain HC1 `T1_baseStage`/`S9_transStage`/`S10_recStage` with
the retirement displayed.  git diff verified comment-only (two docstring
hunks, zero code lines).

— FORGE junc_bundle stage 1, 2026-08-08 (wallclock 2026-08-02).
