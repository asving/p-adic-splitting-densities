# SYNTHESIS PASS 4 (2026-08-08) — post-window pattern hunt: collapses, shared kernels, revised queue

Standing charge: the periodic whole-proof synthesis duty. Sources: PROJECT_STATE (r21
checkpoint), ROOT §0–§1/§3.1/§26 (REVISION 20, TEN [M] rows), SYNTHESIS_PASS3, the GRB/B-M2
leaf residues, the ledger tail, H1/{RecParamE,RCWitness}.lean, HDISCHARGE_H1/H2. Map-making
only — the orchestrator dispatches.

## F1 — THE ORDER-2 UNRAMIFIED-BELOW STRATUM COLLAPSE (one unit, two open lemmas' consumers)

**Pattern.** On the stratum {order 2, every relevant preceding e_j = 1} (at order 2: e₀ = 1),
the GRB leaf's two open lemmas REDUCE TO ONE STATEMENT, and every reduction step is already
proved: (1) the marched twist is PROVED trivial there (ǫ₁ ≡ 1 from s ≡ 0, ℓ₁ = 0 — corrected
Def 3.15; S3.2 corrected picture, FACT not conjecture); (2) TR-3′-GEN(i) restricted there ⟺
"assembled pre-ǫ coefficient agreement" (S3.4 displays the reduction as holding exactly where
triviality is proved); (3) TR-3-ORD-X restricted there "would follow OUTRIGHT from (i)" (S3.4
+ R2.3: the rescaling argument with t = 1 PROVED). **Evidence.** GRB S3.2/S3.4/R2.3/R11.3–R13;
the S3.1 structural rows proved by inspection; the r = 2 monomial computation (S3.2) is the
identity's skeleton; harness T9 0/500 + T2 0/1,200 exact; D-REAL covers full-stage there
(E_i = 1) and D-ITER does not fire (it needs E_i > 1). **Action licensed.** ONE new leaf unit
**TR3-S1**: prove the assembled pre-ǫ coefficient agreement for the marched order-2 read at
that stratum (finite algebra: FGMN eq (12)/Def 3.16 assembly vs GMN Defs 2.19–2.21, twist gone).
It converts TR-3′-GEN(i)|ord-2 conjecture → theorem and discharges TR-3-ORD-X on the stratum as
a corollary — serving BOTH consumer families (GD3-FULL/OL-B; GD3-MIN Route B + clause-(4)
ord-consumers) plus B-M2's OL-1(b) GMN-verbatim face (which rides TR-3-ORD-X). Honesty: this
closes NEITHER lemma (twist revives at deeper orders when some e_j > 1; e₀ ≥ 2 untested); the
march-level σ_j-compatibility must still be WRITTEN even at order 2 — that is the unit's
content, bounded, with a green falsifier already standing.

## F2 — the derive-from-wiring genre (REC-WIRE-G) has named next targets

**Pattern.** A debt displayed "no field ties X" falls by deriving X from already-compiled
coherence/width laws + a stage-layer kernel whose TYPE excludes the fiat (`recentering_natDegree_eq`
+ `recParam_eg_of_recentering`: e·g·d = d, d ≥ 1 ⟹ e·g = 1; `hspecRec` unused). **Targets.**
(a) **(H8′)(iii) POOL-DICT** — "vBridge constrained only by keying/injectivity/support": attempt
deriving the node-level τ/δ pool read-off from the compiled K-CUT laws (`kcut_reduce` ownership +
`massFactor` support) before treating it as blocked on [2r]/CL-8. Attempt-grade, one unit, success
OR compiled obstruction. (b) **TerminalPolySem (H6)** — no supplier at HEAD; its k′ = 0 face may be
derivable from the landed emission specs (`terminalDatumD_slope_spec`/`ReadThroughIota`).
Attempt-grade. (c) NOT candidates: the V9/HK-11 steep+corner legs (the genre already ran there —
`HK52_stretchGate` is a compiled FALSE-SUSPECT obstruction at e′ ≥ 2); `leakFree` (Codex fold of
record: no faithful typed shadow exists at the skeletal carrier — the opposite verdict).

## F3 — the hspecRec-transport genre (structure-field ⟹ actual-parameter)

`k0_actual_of_recentering` transports a synthetic conclusion to actual parameters because a
structure field pins them. Same shape: **(T-READ)** (emitted fields = the (c1)-shape polygon-side
datum) — if H6's emission fields already pin the datum, conformance transports; check when H6's
C0/TRM carrier lands. The `readsOf_landing_K0` recentering-branch debt is witness-grade (H₃rc
method, RCWitness.lean), one cheap unit.

## F4 — GRADED-READ vs TRANS-DEEP: SIMILAR, one shared supplier kernel, NOT the same

**Verdict: not the same obligation.** TRANS-DEEP = finite-level fiberwise (F)/(L)/(J) product-box
law (H2 §5, "the finite-level shadow of (GR-B)(2′)/(3)/(4) + (P4)"); GRADED-READ = the graded
identity in(D_κΦ^(eκ)) = U₀ψ_κϕ_{γ̂}ȳ^κ at fired lifts, the GenuineStageModel seam (B-M2 §S4
(i-b)); H2's blueprint itself rules "nothing on file derives (TRANS-DEEP) from (H1)(a)". **But
both discharge routes run through the SAME unbuilt Lean layer**: the compiled §B2-DEF
carry-algebra graded-read apparatus (𝒟 = F[u]/(u^e − z̄), aligned DIG, anchor-monomial
transport) — TRANS-DEEP names it as supplier (H2 §5 note (i)); GRADED-READ's identity is stated
in exactly that language (H1 §1.2 (0′) row). **Action.** Charter the §B2-DEF Lean formalization
ONCE with TWO displayed consumer interfaces (H2's `TransDeep` row supplier; H1's
GenuineStageModel instantiation), so the corpus never grows two carry-algebra formalizations.

## F5 — SYNTHESIS_PASS3 execution audit

EXECUTED: F1 FirstEntrance + F4 Tonelli hoists, F2 H1-wave-0 pull-forward, F5 RootHyps sync, F6
r14 batch, F7 K1-scope one-home (→ (K1-CANON) discharged, (H9) retired), §2 items 1–4 ((K-CUT)
retired to (H8′); D-12r → §4; (E-N) witness-backed). NOT executed: **F8 TestChains** (no
`DictIII/TestChains.lean`; H6 partially paid the predicted rebuild), **F9 BP_III ID map**, §2
item 5 (**P(O-8b/M14) still owed** — H4a un-retired), item 6 (H5 mop-up partial). Lesson: pure
interface-hygiene findings drop when fleets run hot — fold F8/F9 as one-line DUTIES in the next
dispatch templates, not standalone units.

## F6 — dead weight

Little survives the r21 sweep. Confirmed moot/synced: the S3.2 discrepancy law (zero ROOT
displays), B2-FINAL gates (H2's was the only one; satisfied by §B2-DEF), the H1 (H-CHAIN) range
(REV-3 synced), REC-PARAM/REC-WIRE-G/e-half rows (discharged; any doc still listing them open is
stale — grep duty for the next ROOT batch).

## REVISED PRIORITY QUEUE (value/cost; blocker named)

1. **VC22** on REVISION 20 — re-anchors the acceptance; blocks nothing, everything folds under it.
2. **D-11 confirming pass** — owed; doubles as the (H9) re-open trigger; one pass.
3. **TR3-S1 (F1)** — cheapest genuine-math unit on the board; three consumer families; falsifier green.
4. **§B2-DEF Lean formalization as the ONE shared supplier (F4)** — heavy, double-counted value ((FRESH) + (H1) tower vehicle); consumers (`TransDeep`, H2-U5/U8) already compiled and waiting.
5. **P(O-8b/M14)** — fire the owed pass on the composed Route-B note; retires (H4a) mod (K3-δ); mechanical.
6. **(ADM) track B (ADM-U6a/U6b) + EN-U3** — specced follow-up cycle; decidable content; blocker: ADM-U0 triangular repair (authority on file).
7. **Three small derive/witness units (F2/F3)**: `readsOf_landing_K0` witness; POOL-DICT derivation attempt; TerminalPolySem k′ = 0 attempt — each ends in a discharge or a compiled obstruction.
8. **TR-4 harness family** (Cor 4.5/4.11 factorization/bijectivity — currently NO family) — cheap numerics-fleet item, closes the leaf's displayed evidence gap.
9. **Asvin review batch** — hf Monic, (ed-1) M04 §5.5 pin, TerminalPolySem supplier; zero cost, unblocks H2-U10 (gated).
10. **H6 C2** — BLOCKED (III-G3a/G4/G6 typeclass-stuck); no agents without a new mechanism; route = a dedicated GDOrder1 typeclass repair unit.
11. **The (H1)/(H2) tower proper** (GRADED-READ, REC-SL, SITE-EXH, TR-3′-GEN(ii), D-ITER E_i > 1, members (b)/(c)/(d)) — staff AFTER 3–4 land (they are its first slices/carriers). SITE-EXH: attempt ONCE at the engine layer (every fleet's universal-quantifier debt), never per-leaf.
12. **F8/F9 duties** folded into the next H1/H6 dispatch templates.

— Synthesis pass 4, 2026-08-08.
