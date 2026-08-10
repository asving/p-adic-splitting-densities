# SIMPLIFICATION CAMPAIGN BLUEPRINT — 2026-08-10

**Unit:** SIMPLIFICATION-BLUEPRINT (pipeline stage 1.5 kickoff; Asvin's standing
directive: when the hostile arcs pass → compress the proof, hunt the
second-generation short proof — THEN stage two = Lean modulo literature except
arXiv:2212.00294). **Status:** DESIGN ONLY. No compression is performed here; no
accepted text is touched; every accepted text stays byte-frozen. **Sources:**
PROJECT_STATE dated appends #14–#20 · HEURISTICS_AND_INTUITIONS_2026-08-08 §C1 ·
the corpus notes' STATUS headers at HEAD · SITE_REFRESH2_DRAFT_2026-08-10 §0.

**The verdict up front.** The corpus is 26 texts, ~38,200 lines. Five compression
targets are real and rank cleanly by Asvin's criterion (revision-scope-reduction
— how many notes a future erratum would ripple through):

1. **T1 the gauge/ϑ cocycle lemma** — one letter-layer lemma absorbs the wrap/
   gauge annexes of the seven tower notes; the gauge seam produced findings on
   the seven tower first passes (appends #17–#20), i.e. this exact fact is
   currently proved seven times in seven local coordinate systems.
2. **T2 the σ-ladder master instance** — HETOW and GENTOW4 already prove their σ
   reads are LITERAL INSTANCES of THEOREM HE7.A; inverting that (state HE7.A once
   at a general carrier) turns five notes' bridge layers into instances.
3. **T3 the cocycle-telescope lemma** — GENTOW2-B″, HETOW-4, and GENTOW-6.4 (the
   𝒯-free cap) are three proofs of one telescoping-cocycle-monomial shape.
4. **T4 the certificate witness lemma** — GENTOW3's Θ_j threshold and GENTOW6's
   CERT-TOP share the touched-coordinate witness; one definition + one lemma.
5. **T5 the w-frame note** — define the cross-frame unit w and ψ^{(w)} once, in
   the w-inclusive canonical frame; the per-note riders become instances.

Two second-generation routes could bypass whole notes (§3): the literal-instance
cascade (T2 pushed to the whole σ-chain) and the weld one-face consumption
(retiring three junction notes from the load-bearing path). Both are graded
speculation with named cheap probes. **Proposed first wave: S-0 (the statement
ledger — the byte-tracking instrument) + S-1 (T1 through the full 2-clean bar).**

---

## 1. THE CORPUS MAP (26 texts, dependency DAG)

All files in `lean/notes/openmath/`, suffix `_2026-08-08.md` unless dated
otherwise. Grade: 25 texts ACCEPTED 2/2 at the hostile bar; JD0 is PROVED grade
(machine 68,523/0; sub-bar — the one exception, flagged where consumed).
"←" = consumes. Sizes in lines.

### 1.1 The carry/weld layer (8 texts, 11,942 lines) — letters, gauge, transport

| Text | Lines | Role (one line) |
|---|---|---|
| LIFTCORNER | 1,481 | NR-1 lift-orbit corner ((ITER-LAW-LIFT) at g₀=1∧δ₁=1); supplier to W-2's cap. |
| GRTW2 | 1,440 | W-2 the lift junction: admissible representative + (ξ,w) unit covariance + ψ-transport. ← LIFTCORNER. |
| GRTJA | 943 | J-A the dictionary junction: type→tower data, four operator equalities, covariance-corrected residual tie. ← GRTW2. |
| GRTJB | 3,161 | J-B the tree junction: expansion + polygon identities, division-step correspondence, (C-READ) transport, ε-carry collapse. ← GRTW2, GRTJA. |
| GRTJC | 2,807 | J-C the carry-algebra junction: graded target exists, TC-3 load-bearing iff δ ≥ g_m, anchor-transport Ψ, cocycle semantics. |
| WELDMASTER | 1,092 | The consolidation: four junctions = faces of ONE anchored graded transport (M0–M4); canonical gauge c = z̄^δ·∂Ẽ; one-perimeter fence. ← all four junctions. |
| JD0 | 385 | Count gauge-blindness: stratum counts see the SHAPE, never the letters. [PROVED grade, sub-bar.] |
| SIGMALAW | 633 | The Σ-LAW: per-coordinate ledger identity at every level; sign = the ξ-composite. ← GRTW2. |

### 1.2 The menu/reduction chain, n ≤ 7 (7 texts, 12,900 lines) — counts

| Text | Lines | Role |
|---|---|---|
| W11 | 719 | n=2 complete decided menu (7 families) + exact drainage q^{−N}; hExhaust as a theorem at n=2. ← JD0. |
| W12 | 1,995 | W-12.A order-1 shape-generic count law at all degrees; **THEOREM W-12.D (the reduction): menus + drainage ⟹ one R_τ ∈ ℚ(q) per splitting type, wild included**. ← W11 pattern, JD0. |
| HMENU3 | 952 | (hMenu-3): the 33-family cubic menu; W-12.D fires at n=3. ← W12. |
| HEX3 | 969 | (hExhaust-3): the exact U₃ law by per-center transport; n=3 drainage. ← W12. |
| GENIND | 3,054 | The two-species induction (α self-similar / β partition-fracture); (hMenu-n)+(hExhaust-n) scaffold; composite criterion = ≥4 keys (n ≥ 4). ← W12.A, HMENU3/HEX3 as base. |
| GENH4 | 2,173 | [GENIND-H(4)] discharged at both quartic genres (Q22-L1/L2/L3); the four-step method; 11 quartic densities. ← GENIND, weld faces. |
| GENHN | 2,038 | The general composite-stage law: genre classification FINITE+UNIFORM; every stage = W-12.A (e₁,f₁)-re-based; towers ⟺ μ ≥ 4 ⟺ n ≥ 8. ← GENH4's method, W-9 graded weld face via GENHN-4. |

### 1.3 The σ-ladder, n ≤ 7 (4 texts, 6,177 lines) — the wild read

| Text | Lines | Role |
|---|---|---|
| HE3 | 1,618 | The stage-σ recursion: σ at a μ-stage = label read of the degree-μ stage resolvent over the stage ring; [GENHN-HE(μ≥3)] closed at μ ≤ 3. ← GENHN interfaces; deliberately weld-face-minimal (§S0). |
| HE6 | 1,047 | The enlarged test family at fractional heights pins label class sizes at ℓ ≥ 2 sides, base-change-free. ← HE3. |
| HE7 | 2,652 | (SLOT₂)/(LIFT₂); the whole level ladder by ONE induction; TERMINATION depth ≤ log₂n − 2. ← HE6. |
| HE6R1 | 860 | The reconciliation: HE7 covers the widened HE6 box as a LITERAL INSTANCE; composition lemmas HE6R1-1/2/3; two errata on HE7. ← HE6, HE7. |

### 1.4 The tower leg, n ≥ 8 (7 texts, 8,160 lines) — composed carriers

| Text | Lines | Role |
|---|---|---|
| HETOW (…-09) | 834 | Tower-stage σ read = LITERAL INSTANCE of HE7.A at the composed carrier; bridges HETOW-1/2/3 + HETOW-4 (normalizer, the Codex-demanded cocycle bridge). ← GENHN, HE7 frozen, HE6R1. |
| GENTOW1 (…-09) | 975 | Items (1)(2)(5): composed budgets E₂ = e₂f₂u₂, inner refine transfer, window ledger, depth-3 floor. ← GENHN. |
| GENTOW2 (…-09) | 1,498 | Item (6α) via the PDF-verified FGMN cite; LEMMA B″ u(β_t) = ϑ(t)·w^{f₃−t}; the canonical letter formula z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}. ← GENTOW1, FGMN. |
| GENTOW3 (…-09) | 878 | Item (3) the faithfulness geography: threshold Θ_j = (μ₂−j)E₂ + δ; touched-coordinate certificate. ← GENTOW1. |
| GENTOW4 (…-09) | 1,037 | Item (4) partial inner sides = level-1 block split + HE6R1-2 projection + per-block literal HE7.A instances. ← HE6R1, HE7, GENTOW1. |
| GENTOW5 (…-09) | 1,741 | The composed graded frame at general μ₂ + the level-r grammar (depth ≥ 4); ψ^{(w)} re-scope; depth-4/5/6 witnesses. ← GENTOW1/2. |
| GENTOW6 (…-09) | 1,197 | The mixed-side tie + CERT-TOP + LEMMA GENTOW-6.4 (the 𝒯-free window cap); residues = count-grade BOX-1/2/3 (+BOX-4 battery ask). ← GENTOW1/3/4. |

**DAG summary.** Three load-bearing spines meet at W-12.D: (i) the COUNT spine
W11 → W12 → {HMENU3, HEX3} → GENIND → GENH4 → GENHN → GENTOW1/2/3/5/6, fed by
the weld layer through TWO faces (JD0 count-blindness; the W-9 graded face via
GENHN-4); (ii) the σ spine HE3 → HE6 → HE7 → HE6R1 → HETOW → GENTOW4, which
consumes strictly fewer weld faces (HE3 §S0: GENHN-4/W-9 deliberately NOT
inherited); (iii) the LETTER layer (GRTW2/WELDMASTER gauge + SIGMALAW + the
tower notes' ϑ/wrap formulas), which never enters counts (JD0) and enters σ only
through canonical-frame choices — the layer T1 unifies.
