# ITER-LAW-n — the uniform all-orders theorem: the (ITER-LAW-n) recursion c_{n+1}(γ,γ′) = z̄^δ·∏ⱼ z_j^{D_j} for ALL n ≥ 1 on the (n+1)-read standard-lift harness class, BY INDUCTION on the rung — the level-generic inductive step executed (integer layer + ε-chain L6-(n) + W-MULT-(n) Case I unconditional-given-base; the Case-II legs closed modulo ONE displayed open engine family (RM-m); DCX-(n) excluded honestly per level) — with the exact conditionality ledger and the first 5-read data

**Unit:** the GENERAL-n COMPOSE (chartered at 13b026b, "the general-n compose
(L6-(n) + W-MULT-(n)) is the chartered next unit"; the campaign's uniformity
directive). Genre: attempt-grade theorem note in the ITERLAW/ITERLAW3 genre —
finite algebra executed in full where the level-generic proof closes, explicit
displayed open lemmas WITH PRICES where it does not (the honesty architecture
is the deliverable: per the charter, the fallback grade of any resisting leg is
the INDUCTION SCHEMA — the exact generic lemma statements whose proof would
close all orders). Acceptance counter 0 — no hostile pass has run on THIS
note. Author: Fable, campaign date 2026-08-08 (wallclock 2026-08-03).

**The base of the induction (rung 1), cited per CHECKLIST RULE 8 with the
package of record PASTED (ledger block "ITER-LAW ACCEPTED — 2026-08-03",
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`):** [IL] =
`ITERLAW_2026-08-08.md`, ACCEPTED 2026-08-03 at the 2-clean model-diverse bar —
"Scope as accepted: the harness tower class (superset of DITER_RESTATE §S2's
E₂ > 1 pin; on-the-nose coincidence restricted to E₂ > 1); residuals:
(ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the
accepted GRB retarget; orders ≥ 3 untouched." — i.e. accepted on the harness
tower class, STANDARD-LIFT, a strict superset of DITER_RESTATE §S2's pinned
E₂ = e₀e₁ > 1 setting, coinciding with the §S2 display on the nose restricted
to E₂ > 1, with all three residuals in force. Every citation of [IL] below
carries this same package.

**The rung-2 link, cited with its honest grade at EVERY consumption:** [IL3] =
`ITERLAW3_PROOF_2026-08-08.md` AS AMENDED at f9daca0 (errata round 1 applied:
COR-3 re-scoped OFF-DCX; DEV-1 measure scoped to e₀ ≥ 2 with the fenced
non-consumed corner {e₀ = 1 ∧ d₀ ≥ 2 ∧ j ≥ g₀} displayed; rung relabel) —
**ATTEMPT GRADE: acceptance counter 0/2 — hostile round 2 COMPLETED
NOT-CLEAN on both legs (PC2 1C/1G @ cf013a4 + PE2 0C/2G @ 467b523; all
findings new AND narrow: the S4.5 e₂ = 1 display-line slip, conclusion true
with the in-sentence cure valid, + residual rung-index citation tokens;
S2–S5's mathematics byte-stable and re-run-exact); errata round 2 then round
3 (PC3+PE3) owed**; it proves the 3-read theorem OFF its DCX corner.
Everything in this note that consumes [IL3] is conditional on that arc
closing; the conditionality ledger (S7) threads it explicitly. (This note's
generic II-1 top-level e_n = 1 branch, S4.6, derives the read-0 conclusion by
the CORRECTED inequality — slot weight B_n − γ_{n+1} < w_n(E₁ⁿᵉʷ) — and does
not inherit the PC2-F1/PE2-F1 display defect.)

**Rung indexing (the 997c467 convention, used throughout):** an (n+1)-read
tower = RUNG n. Rung 1 = 2-read = [IL] (ACCEPTED 2026-08-03 on the harness
tower class — standard-lift, strict superset of DITER_RESTATE §S2's
E₂ = e₀e₁ > 1 pin, on-the-nose at E₂ > 1; residuals: (ITER-LAW-LIFT) open at
g₀ = 1 ∧ δ₁ = 1, gr(w₂) wrapper rides the accepted GRB retarget, orders ≥ 3
untouched). Rung 2 =
3-read = [IL3] (attempt grade 0/2, proved off DCX + MEASURED 0/123,564-and-up).
Rung 3 = 4-read = MEASURED GREEN only (`ITERLAW4_PROBE_2026-08-08.md` verdict
13b026b: 0/362,624 on 72 fresh towers × 4 rings — instance evidence, never a
proof step). Rung 4 = 5-read: first data produced by THIS unit's post-seal
diagnostic (S8). The theorem below is stated at every rung n ≥ 1.

**PRINT-CONSUMPTION DISPLAY.** As in [IL] (ACCEPTED; package as pasted in the
base paragraph above — harness tower class, standard-lift, strict superset of
§S2's E₂ > 1 pin, three residuals in force) and [IL3] (attempt grade 0/2;
round 2 completed not-clean on narrow findings, errata round 2 → round 3
owed): no printed formula and no text extraction is consumed.
Every object is consumed as a DEFINITION — the harness calculus
(`verification/openmath/grb_order2_check.py` levels 0–2, `strata3_probe.py`
level 3, `iterlaw4_probe.py` level 4, and the level-5 mirror layer of this
unit's own diagnostic `verification/openmath/iterlawn_diag.py`, all built by
the SAME one-level-up mirror discipline). Print faithfulness lives upstream in
the accepted GRB/TR3 arcs and is not consumed.

## S0. Setting, statement, status

### S0.1 The (n+1)-read standard-lift harness class (the class pin)

O a DVR with uniformizer π, residue field k₀, valuation w₀ (coefficientwise on
O[x]; harness instances ℤ₂, ℤ₃, F₂[[t]], F₃[[t]], the proof ring-blind). Fix
n ≥ 1 and tower data with reads j = 0, …, n:

* Φ₀ ∈ O[x] monic, deg Φ₀ = d₀ ≥ 1, w₀(Φ₀) = 0, reduction irreducible;
  K₀ := k₀[X]/(φ̄); res and lift as in [IL S0] (ACCEPTED; package pasted in
  the header: harness tower class, standard-lift, strict superset of §S2's
  E₂ > 1 pin, all three residuals).
* Read j (0 ≤ j ≤ n): e_j ≥ 1, h_j ≥ 1, gcd(e_j, h_j) = 1; ψ_j ∈ K_j[y]
  monic irreducible, deg ψ_j = g_j ≥ 1, ψ_j(0) ≠ 0;
  K_{j+1} := K_j[z_{j+1}]/(ψ_j). Letters: z₁, …, z_n and the top letter
  z̄ := z_{n+1}. Normalized Bézout pairs (ℓ_j, ℓ_j′): ℓ_jh_j + ℓ_j′e_j = 1,
  0 ≤ ℓ_j < e_j (ℓ_j = 0, ℓ_j′ = 1 at e_j = 1).
* Weights, with the UNIFORMIZING CONVENTION γ₁ := h₀ (so every level speaks
  one language): γ_{j+1} := e_j·w_jΦ_j + h_j and w_{j+1}Φ_{j+1} :=
  e_jg_jγ_{j+1} for j ≥ 1; w₁Φ₁ := e₀g₀h₀ = e₀g₀γ₁ (so w_jΦ_j =
  e_{j−1}g_{j−1}γ_j for ALL j ≥ 1).
* Lifts: Φ₁ := the STANDARD LIFT of ψ₀ (grb_order2_check :499–507); for
  1 ≤ m ≤ n−1, Φ_{m+1} := the CANONICAL ε_m-CORRECTED LIFT of ψ_m:
  Φ_{m+1} = Σ_{k ≤ g_m, ψ_{m,k} ≠ 0} C_k·Φ_m^{e_mk}, C_{g_m} = 1,
  C_k := realize_m(ε_m((g_m−k)γ_{m+1})^{−1}·ψ_{m,k}, (g_m−k)γ_{m+1}) for
  k < g_m — the build_Phi2/build_Phi3/build_Phi4 pattern verbatim, one level
  up each time (well-definedness on the class: Lemma WELL-DEF-(n), S4.1).
  The top ψ_n needs no lift (the cocycle never consumes Φ_{n+1}).
* E_{n+1} := e₀e₁⋯e_n. E-positivity: every e_j ≥ 1 individually, NO joint
  floor (the erratum lesson of [IL] — ACCEPTED 2026-08-03 on the harness
  tower class, standard-lift, strict superset of DITER_RESTATE §S2's
  E₂ = e₀e₁ > 1 pin, on-the-nose at E₂ > 1, residuals (ITER-LAW-LIFT) /
  gr(w₂)-wrapper / orders ≥ 3 in force — applied proactively as in [IL3]
  S0.1).

The (ITER-LAW-LIFT) residual propagates verbatim to every level: nothing is
claimed for any non-canonical lawful lift at any level.

### S0.2 Calculus, splits, anchors, cocycle

The calculus is the iterated harness read, defined once per level by the
mirror recursion (verbatim semantics of the pinned code, as in [IL3] S0.2):
ε_m(β) := z_m^{ℓ_{m−1}′s − ℓ_{m−1}u} with (s,u) := eq12(β; e_{m−1}, h_{m−1})
(reading C at every level; ε₁ = harness eps1, ε₂ = eps2, ε₃ = eps3, ε₄ = the
diagnostic's eps4); w_{m+1}(f) := min_j{e_m·w_m(A_j) + j·γ_{m+1}} over the
Φ_m-development f = Σ A_jΦ_m^j; the level-(m+1) read at γ := w_{m+1}(f) has
grid s_{m+1}(γ) + je_m, slot weights γ_j := (γ − (s_{m+1}+je_m)γ_{m+1})/e_m,
coefficients C_j := ε_m(γ_j)·R_mv(A_{s_{m+1}+je_m}) when the digit is on-line
(w_m = γ_j exactly), else 0; R_{m+1}v(f) := Σ_j C_j·z_{m+1}^j ∈ K_{m+1};
**val(f) := R_{n+1}v(f) ∈ K_{n+1}** (harness val₃/val₄/val₅ at n = 2, 3, 4).
Base facts consumed (as in [IL S1]; ACCEPTED, package pasted in the header —
harness tower class, standard-lift, superset of §S2's E₂ > 1 pin, three
residuals): division algorithm in O[x] (Φ monic ⟹ unique developments), w₀ a
valuation, res additive and vanishing on strict π-excess, q: O[x] → K₀ a ring
homomorphism.

**The iterated eq-(12-int) split.** For γ ∈ ℤ:

    (s_{n+1}, u_{n+1}) := eq12(γ; e_n, h_n);   β_n(γ) := u_{n+1} − s_{n+1}·w_nΦ_n
    for j = n, …, 2:  (s_j, u_j) := eq12(β_j; e_{j−1}, h_{j−1});
                       β_{j−1}(γ) := u_j − s_j·w_{j−1}Φ_{j−1}
    (s₁, u₁) := eq12(β₁; e₀, h₀)
    [so γ = e_nβ_n + s_{n+1}γ_{n+1} and β_j = e_{j−1}β_{j−1} + s_jγ_j for all j]

Anchor φ_γ := π^{u₁}·Φ₀^{s₁}·Φ₁^{s₂}·⋯·Φ_n^{s_{n+1}}; window
W_{n+1} := {γ : u₁(γ) ≥ 0}; cocycle on anchors, for γ, γ′ ∈ W_{n+1}
(γ+γ′ ∈ W_{n+1} by WINDOW-(n), S2):

    c_{n+1}(γ,γ′) := val(φ_γ·φ_{γ′}) / val(φ_{γ+γ′}).

Pair abbreviations (fixed throughout): s_j := s_j(γ), s_j′ := s_j(γ′),
s_j″ := s_j(γ+γ′); B_j := β_j(γ)+β_j(γ′), β_j″ := β_j(γ+γ′); the s_j-defect
:= s_j + s_j′ − s_j″; plain carries δ_j^{pl} := ⌊(s_j+s_j′)/e_{j−1}⌋ ∈ {0,1}
(j = 1..n+1; the TOP one is δ := δ_{n+1}^{pl}); Γ″ := γ+γ′.

### S0.3 THEOREM (ITER-LAW-n) — the statement, verbatim the recursion of record

**THEOREM (ITER-LAW-n; the L3CONVERGENCE S2 Candidate-2 recursion, verbatim;
= ITERLAWR_PROBE S6 item 1; unrolled instances: the [IL] display at n = 1
(ACCEPTED; package pasted in the header — harness tower class, standard-lift,
strict superset of §S2's E₂ = e₀e₁ > 1 pin, on-the-nose restricted to E₂ > 1,
three residuals in force), the [IL3] display at n = 2 (attempt grade 0/2), the
sealed ITERLAW4 display at n = 3).** For all γ, γ′ ∈ W_{n+1}, with

    δ := ⌊(s_{n+1}(γ) + s_{n+1}(γ′))/e_n⌋ ∈ {0,1}          [top carry]
    S_n := δ·γ_{n+1};                                       [top shift]
    for j = n, …, 1:
      D_j     := (s_j-defect + ℓ_{j−1}·S_j)/e_{j−1} ∈ ℤ     [level-j exponent]
      S_{j−1} := D_j·γ_j + S_j·(ℓ_{j−1}′ − ℓ_{j−1}·w_{j−1}Φ_{j−1})
                                                  [composed shift; S₀ unused]

it holds that

    c_{n+1}(γ,γ′) = z̄^{δ} · z_n^{D_n} · z_{n−1}^{D_{n−1}} · ⋯ · z₁^{D_1}.

(Convention at j = 1: w₀Φ₀ := 0 and γ₁ = h₀, so S₀ = D₁h₀ + S₁ℓ₀′ — computed
by the recursion but consumed by nothing.)

**STATUS (the exact grade, per clause and per rung — the point of this
note).** The theorem is proved BY INDUCTION ON THE RUNG with the level-generic
step of S4, on the following honest perimeter:

* **Excluded locus:** DCX-(n) := ∪_{m=2}^{n} DCX_m, the per-level
  double-cascade corners (S4.7: outer bound proved generically; sharp form
  proved at m = 2 = the [IL3] corner; DCX-(1) = ∅). On DCX-(n) the theorem is
  conjectural (instance-true at every probed instance, all rungs).
* **Conditionality off DCX-(n):** rung 1 UNCONDITIONAL (= [IL], ACCEPTED
  2026-08-03 on the harness tower class — standard-lift, strict superset of
  DITER_RESTATE §S2's E₂ = e₀e₁ > 1 pin, on-the-nose at E₂ > 1; residuals
  (ITER-LAW-LIFT) at g₀ = 1 ∧ δ₁ = 1 / gr(w₂) wrapper rides the accepted GRB
  retarget / orders ≥ 3 untouched). Rung 2 = [IL3] at attempt grade (counter 0/2;
  round 2 completed not-clean on narrow display/naming findings, errata
  round 2 → round 3 owed). Rung n ≥ 3: conditional on (i) the [IL3] rung-2 package and
  (ii) the OPEN ENGINE FAMILY (RM-m) for 2 ≤ m ≤ n−1 (S4.6) — the one leg of
  the generic step that resists; every other leg of the inductive step is
  proved level-generically in this note.
* **Unconditional at every rung and on ALL pairs (DCX included):** the entire
  integer layer — the shift cascade β_j″ = B_j + S_j (all j), D_j-integrality
  (all j), the (★)-positivity of the shift chain, WINDOW-(n), the slotwise
  cocycle identity of the displayed constants, ℤ/E_{n+1}-descent of all
  constants, and the degeneration collapses at integer level (S2, S6).

| clause | grade | where |
|---|---|---|
| L1 EQ12-ADD at a general read | ACCEPTED ([IL S2 L1] — harness tower class, standard-lift, strict superset of §S2's E₂ > 1 pin, three residuals in force) | S2 |
| SHIFT-(n): β_j″ = B_j + S_j for j = n..1 | PROVED, generic, unconditional | S2 |
| D_j-INT for all j | PROVED, generic, unconditional | S2 |
| (★)-POS: S_j = 0 or e_jS_j ≥ γ_{j+1} | PROVED, generic, unconditional (NEW display) | S2 |
| WINDOW-(n) | PROVED, generic, unconditional | S2 |
| EXP-KIT (a)/(b)/(c), generic in the level | PROVED (re-displayed self-contained) | S3 |
| TRUNC (the truncation dictionary) | PROVED, generic | S4.0 |
| REALIZE-(m) + WELL-DEF-(n) (canonical lifts exist; Ĉ-clauses) | PROVED, generic (incl. the (I_m) descent invariant — NEW) | S4.1 |
| READ-ADD-(m) (additivity + strict-above kill) | PROVED, generic | S4.1 |
| L6-(n) ANCHOR-VAL = ε-chain, all n | PROVED given only the [IL] base (ACCEPTED on the harness tower class, standard-lift, superset of §S2's E₂ > 1 pin, three residuals; no RM, no DCX) | S4.2 |
| the induction package (ITER-PKG-r) | STATED; base r = 1 ACCEPTED, r = 2 = [IL3] 0/2 | S4.3 |
| CASE-SPLIT-(n) | PROVED, generic (given IH package) | S4.4 |
| W-MULT-(n) Case I | PROVED, generic (given IH package) | S4.5 |
| (RM-m) engine: m = 1 | PROVED via [IL3] (e₀ ≥ 2; + e₀ = 1 ∧ d₀ = 1; corner inherited) | S4.6 |
| (RM-m) engine: 2 ≤ m ≤ n−1 | **OPEN, priced** (THE resisting leg) | S4.6 |
| W-MULT-(n) Cases II-1/II-2/II-3, off DCX | PROVED generic MODULO (RM-(n−1)) | S4.6 |
| DCX-(n): outer bound per level | PROVED, generic | S4.7 |
| DCX-(n): sharp form + emptiness | m = 2 proved ([IL3]); m ≥ 3 engine-dependent, conjectured e_{m−2} ≥ 3 | S4.7 |
| W-MULT on DCX-(n) | **OPEN** ((W-MULT-DCX-m) family), instance-true | S4.7 |
| THE THEOREM, off DCX | proved modulo the S7 ledger (per-rung conditionality above) | S5 |
| COR-1..COR-5 (with OFF-DCX qualifiers baked in) | S6 | S6 |
| (INV-n) class, gr(w) wrapper, GMN, general lifts, Lean | NOT TOUCHED (fences) | S9 |

## S1. The induction, architecturally (what is generic, what resists, and why)

The L3CONVERGENCE S3 strategy at general rung, executed: the induction carrier
is the ε-chain gauge. The induction hypothesis is a PACKAGE (ITER-PKG-r,
S4.3): not the cocycle law alone but the three exports the next level
consumes — (P-L6) anchor value = ε-chain with its weight clause, (P-WM) the
pair value with the single-top-slot shape, and (P-DS) the pair product's
digit shapes (weights + reads + degree bounds), certified well enough for the
next level's correction products. The step rung r → rung r+1:

1. **L6-(r+1)**: the anchor's top digit IS the truncated tower's anchor
   (TRUNC); one degree telescope + the IH (P-L6). Fully generic; the L6 chain
   never consumes W-MULT, RM, or any DCX exclusion.
2. **W-MULT-(r+1)**: the pair product's top digit A IS the truncated tower's
   anchor-pair product, so the IH (P-WM)/(P-DS) computes it — "L7 stacked on
   L7", now as the literal induction mechanism. Case I (no Φ_{r+1}-overflow)
   is pure slot-grid absorption: generic, proved. Cases II-* (top overflow at
   g_r = 1) substitute Φ_r^{e_r} = Φ_{r+1} − Ĉ_r once and must re-develop the
   products (IH digit)·Ĉ_r at level r — THE one genuinely new object per
   level. At r = 1 the inputs are monomials and [IL3] hand-built the engine
   (DIGIT-SPLIT + DEV-1). At r ≥ 2 the inputs are the IH's E₀/E₁ exports
   (reduction normal forms, not monomials), and the required engine is the
   displayed OPEN family (RM-m): product-with-correction re-development with
   read-transparency and the ε-carry factoring (S4.6). Everything AROUND the
   engine call — the slot bookkeeping, the line tables, the ε′-cancellation
   against the canonical lift, the DS-export propagation, the DCX exclusion —
   is proved level-generically here.
3. **The theorem** is then division plus ONE EXP-KIT(c) kernel per level with
   shift T = S_j (the proved composed shifts), exactly as at rungs 1–2: no
   cross-level denominators ever form.

**Why the engine is the honest boundary:** rung 2's DEV-1 induction already
carried a sharp corner (the e₀ = 1 measure erratum) and its DCX corner is
priced as a DEV-2 unit ([IL3] S4.7). The generic engine is that unit stated
at every level — its termination problem (two substitution identities per
level, the e-descent failure mode recurring at each) is a genuine dedicated
unit, not a paragraph. Attempting it inline would produce exactly the kind of
unproved "routine" step this campaign's verifiers exist to catch. So (RM-m)
is stated exactly, priced, and consumed visibly; the theorem's grade at each
rung is read off the ledger (S7).

**Consumption manifest:** [IL] (ACCEPTED 2026-08-03; rule-8 package, pasted:
"Scope as accepted: the harness tower class (superset of DITER_RESTATE §S2's
E₂ > 1 pin; on-the-nose coincidence restricted to E₂ > 1); residuals:
(ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the
accepted GRB retarget; orders ≥ 3 untouched" — standard-lift, strict superset
of the pinned E₂ = e₀e₁ > 1 setting): consumed as the r = 1 package (L1, L6,
L7 + displayed developments, EXP instances). [IL3] (attempt grade 0/2; round
2 completed not-clean on narrow findings, errata round 2 → round 3 owed):
consumed as the r = 2 package + DEV-1/DIGIT-SPLIT (= RM-1) +
EXP-KIT (re-displayed below) + WELL-DEF(i)-(ii) (generalized below). Sealed
artifacts (ITERLAWR, ITERLAW4_PROBE verdicts, the method notes): INSTANCE
EVIDENCE ONLY, never proof steps.

## S2. The integer layer (proved, generic, unconditional — all n, ALL pairs)

**Lemma L1 (EQ12-ADD; [IL S2 L1] — ACCEPTED; rule-8 package as pasted in the
header: harness tower class, standard-lift, strict superset of §S2's
E₂ > 1 pin, on-the-nose at E₂ > 1, all three residuals in force).** For a
read (e,h), gcd(e,h) = 1, and β, β′ ∈ ℤ with eq-(12-int) data (s,u), (s′,u′),
(s″,u″) at β, β′, β+β′, δ := ⌊(s+s′)/e⌋: δ ∈ {0,1}, s″ = s+s′−δe,
u″ = u+u′+δh. ∎ (Consumed; the two-line proof is in [IL S2].)

Throughout S2, γ, γ′ ∈ ℤ are arbitrary (no window hypothesis needed except in
WINDOW-(n) itself).

**Lemma SHIFT-(n) (the composed-shift cascade).** For j = n, …, 1:
β_j″ = B_j + S_j, with S_j as in the S0.3 recursion (S_n = δγ_{n+1}).

*Proof.* Downward induction on j. **Top (j = n):** L1 at (e_n, h_n):
s_{n+1}″ = s_{n+1}+s_{n+1}′−δe_n, u_{n+1}″ = u_{n+1}+u_{n+1}′+δh_n; so
β_n″ = u_{n+1}″ − s_{n+1}″w_nΦ_n = B_n + δ(e_nw_nΦ_n + h_n) = B_n + δγ_{n+1}
= B_n + S_n. **Step (j → j−1, j ≥ 2):** assume β_j″ = B_j + S_j. From
β_j = e_{j−1}β_{j−1} + s_jγ_j at all three arguments:

    e_{j−1}(β_{j−1}″ − B_{j−1}) = (β_j″ − B_j) + (s_j-defect)·γ_j
                                = S_j + (s_j-defect)·γ_j.            (S-rec)

By D_j-INT below (whose proof needs only β_j″ = B_j + S_j, already in hand at
this j), s_j-defect = e_{j−1}D_j − ℓ_{j−1}S_j, so the right side is
e_{j−1}D_jγ_j + S_j(1 − ℓ_{j−1}γ_j), and 1 − ℓ_{j−1}γ_j =
1 − ℓ_{j−1}h_{j−1} − ℓ_{j−1}e_{j−1}w_{j−1}Φ_{j−1} =
e_{j−1}(ℓ_{j−1}′ − ℓ_{j−1}w_{j−1}Φ_{j−1}) by the Bézout identity. Divide by
e_{j−1}: β_{j−1}″ = B_{j−1} + D_jγ_j + S_j(ℓ_{j−1}′ − ℓ_{j−1}w_{j−1}Φ_{j−1})
= B_{j−1} + S_{j−1}. ∎

**Lemma D_j-INT (integrality, every level).** For j = n, …, 1:
e_{j−1} | (s_j-defect + ℓ_{j−1}S_j); hence D_j ∈ ℤ.
*Proof.* s(β) ≡ ℓβ (mod e) for eq-(12-int) data at any read (from ue + sh = β
and ℓh ≡ 1 (mod e)). So, using β_j″ = B_j + S_j (SHIFT at level j):
s_j-defect + ℓ_{j−1}S_j ≡ ℓ_{j−1}(β_j + β_j′ − β_j″ + S_j) = 0
(mod e_{j−1}). (Trivial at e_{j−1} = 1.) ∎

(The two lemmas interleave one level at a time, top-down: SHIFT at j gives
D_j-INT at j gives SHIFT at j−1 — no circularity. This IS the sealed
recursion's integer content: the "realized shift" β_j″ − B_j and the closed
form S_j are ONE object at every level, the G8 identity family of the rung-3
battery, now a theorem for all n.)

**Lemma (★)-POS (the shift chain is positive-or-zero, with a uniform gap —
NEW generic display, the n-level form of [IL3] L3-(3)'s case analysis).**
For j = n, …, 1: S_j ≥ 0, and

    (★_j)   S_j = 0   or   e_j·S_j ≥ γ_{j+1}.

*Proof.* Downward induction. j = n: S_n ∈ {0, γ_{n+1}} and e_nγ_{n+1} ≥
γ_{n+1}. Step (★_j) ⟹ (★_{j−1}), j ≥ 2, using (S-rec):
**Restart case S_j = 0:** then β_j″ = B_j, L1 gives s_j-defect =
δ_j^{pl}e_{j−1}, so D_j = δ_j^{pl} ∈ {0,1} and S_{j−1} = δ_j^{pl}γ_j ∈
{0, γ_j}; e_{j−1}γ_j ≥ γ_j. ✓ **Active case S_j > 0:** s_j-defect ≥
−(e_{j−1}−1), so by (S-rec) and (★_j), using γ_{j+1} = e_je_{j−1}g_{j−1}γ_j
+ h_j:

    e_{j−1}S_{j−1} = S_j + (s_j-defect)γ_j
                   ≥ γ_{j+1}/e_j − (e_{j−1}−1)γ_j
                   = e_{j−1}g_{j−1}γ_j + h_j/e_j − (e_{j−1}−1)γ_j
                   = (g_{j−1}−1)e_{j−1}γ_j + γ_j + h_j/e_j  >  γ_j.

So S_{j−1} > 0 and e_{j−1}S_{j−1} > γ_j ≥ γ_j: (★_{j−1}) holds (and once the
chain is active it stays active). ∎
(Diagnostic: (★_j) verified at every pair, 4 reads and 5 reads — S8.)

**Lemma WINDOW-(n).** γ, γ′ ∈ W_{n+1} ⟹ γ+γ′ ∈ W_{n+1}.
*Proof.* e₀u(β₁″) = β₁″ − s₁″h₀ = e₀(u₁+u₁′) + (s₁-defect)h₀ + S₁ (by SHIFT
at j = 1 and the defining equations). If S₁ = 0: u(β₁″) = u₁+u₁′+δ₁^{pl}h₀ ≥
0 by L1. If S₁ > 0: by (★₁), e₁S₁ ≥ γ₂ = e₁e₀g₀h₀ + h₁ > e₁(e₀−1)h₀, so
S₁ > (e₀−1)h₀ ≥ −(s₁-defect)·h₀'s worst case, giving e₀u(β₁″) > 0. ∎

**Slotwise cocycle identity (unconditional; consumed by COR-2).** For
a, b, t ∈ ℤ the displayed constants satisfy the additive 2-cocycle identity
at every slot: δ-slot by L1 at (e_n,h_n) (associate both ways:
e_n[δ(a,b)+δ(a+b,t)] = s_{n+1}(a)+s_{n+1}(b)+s_{n+1}(t)−s_{n+1}(a+b+t) =
e_n[δ(b,t)+δ(a,b+t)]); then downward induction on j: S_n-totals are
γ_{n+1}·(δ-totals), equal; if the S_j-totals of the two associations agree
then the D_j-totals agree ((s_j-defect)-sums telescope to the symmetric
s_j(a)+s_j(b)+s_j(t)−s_j(a+b+t) in both associations, and ℓ_{j−1}(S_j-total)
agrees), hence the S_{j−1}-totals agree. ∎

**ℤ/E_{n+1}-descent of the constants (unconditional; consumed by COR-4).**
γ ↦ γ+E_{n+1} fixes s_{n+1} (E_{n+1} ≡ 0 mod e_n) and shifts β_n by
Π_n := e₀⋯e_{n−1}; downward, it fixes every s_j (Π_j := e₀⋯e_{j−1} ≡ 0 mod
e_{j−1}) and shifts β_{j−1} by Π_{j−1}; at the bottom it shifts u₁ by 1. So
φ_{γ+E_{n+1}} = π·φ_γ exactly, and every constant of the display (δ, all D_j,
all S_j) depends only on (γ mod E_{n+1}, γ′ mod E_{n+1}). ∎

## S3. EXP-KIT (the per-level Bézout kernel; re-displayed self-contained)

**Lemma EXP-KIT.** Fix a read (e,h), gcd(e,h) = 1, its normalized Bézout pair
(ℓ,ℓ′), a field K with a unit z ∈ K^×, and set ε(β) := z^{ℓ′s(β) − ℓu(β)} on
the eq-(12-int) data of (e,h). Then:

(a) **EPS-CLOSED**: (s(β) − ℓβ)/e ∈ ℤ and ε(β) = z^{(s(β)−ℓβ)/e}.
*Proof.* ℓβ = ℓeu(β) + (1−ℓ′e)s(β), so s(β) − ℓβ = e(ℓ′s(β) − ℓu(β)). ∎
(At e = 1: ℓ = 0, s ≡ 0, ε ≡ 1.)

(b) **EPS-MULT**: ε(β)ε(β′) = z^{δ}·ε(β+β′), δ := ⌊(s(β)+s(β′))/e⌋.
*Proof.* Exponents via (a); substitute s(β+β′) = s(β)+s(β′)−δe (L1). ∎

(c) **EXP-SHIFT**: for any T ∈ ℤ and β″ := β+β′+T, with δ as in (b):

    z^{δ} · ε(β+β′)/ε(β″) = z^{D},   D = (s(β)+s(β′) − s(β″) + ℓT)/e ∈ ℤ.

*Proof.* By (a) the left exponent is δ + [(s(β+β′)−ℓ(β+β′)) − (s(β″)−ℓβ″)]/e;
substitute L1 and ℓ(β″−β−β′) = ℓT; the δ-terms cancel. Integrality: δ plus a
difference of integers by (a) twice. ∎

(This is [IL3] S3 verbatim — already generic in the level there; re-displayed
with proof so that this note's integer/character layers are self-contained
modulo the ACCEPTED [IL] alone ([IL S3 L4/L5/EXP] are (a)/(b)/(c) at level 1;
[IL] package per the header paste: harness tower class, standard-lift, strict
superset of §S2's E₂ > 1 pin, three residuals). Instantiations used in S5:
level j with (e_{j−1}, h_{j−1}, ℓ_{j−1}, z_j) and shift T = S_j, one kernel
per level, j = n, …, 1 — each denominator cured inside its own kernel, no
cross-level denominator ever formed.)

## S4. The value layer: the package induction

### S4.0 Lemma TRUNC (the truncation dictionary)

Reads 0..n−1 of an (n+1)-read tower of the class form an n-read tower OF THE
SAME CLASS with identical Φ_j, K_j, ψ_j, ε_j, reads, and lifts (the canonical
lift construction at level m consumes only data of levels ≤ m). For every
γ ∈ ℤ, the (n+1)-read split of γ below the top equals the n-read split of
β_n(γ) (immediate: the split is defined by the same downward recursion from
β_n), so with φ⁽ⁿ⁾ the truncated tower's anchors:

    φ_γ = φ⁽ⁿ⁾_{β_n(γ)} · Φ_n^{s_{n+1}(γ)},   γ ∈ W_{n+1} ⟺ β_n(γ) ∈ W_n
    (the windows read the same u₁), and B-, defect-, δ^{pl}-data agree. ∎

(At n = 2 this is [IL3] S0.3's consumption dictionary; at general n it is the
same two lines.)

### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)

**Lemma REALIZE-(m) (the canonical realizer, all levels; generic).** Define
realize₀(τ₀, w) := lift(τ₀)·π^w (τ₀ ∈ K₀, w ≥ 0), and for 1 ≤ m ≤ n−1,
τ ∈ K_m with z_m-power-basis coordinates τ_i ∈ K_{m−1} (i < g_{m−1}), β ∈ ℤ
with grid (s,u) := eq12(β; e_{m−1}, h_{m−1}), slots k_i := s + ie_{m−1} and
slot weights γ⁽ⁱ⁾ := (β − k_iγ_m)/e_{m−1}:

    realize_m(τ, β) := Σ_{i < g_{m−1}, τ_i ≠ 0}
                       realize_{m−1}(ε_{m−1}(γ⁽ⁱ⁾)^{−1}·τ_i, γ⁽ⁱ⁾) · Φ_{m−1}^{k_i}

(the harness realize1/realize2/realize3 recursion verbatim, with ε₀ := 1).
Suppose the DESCENT INVARIANT (I_m): β ≥ e_{m−1}g_{m−1}γ_m (with (I₀): w ≥ 0
— here γ_m-weights per the γ₁ = h₀ convention and, for m = 1, the [IL3]
realize1 admissibility u(β) ≥ (g₀−1)h₀). Then: (R1) deg realize_m(τ,β) <
deg Φ_m; (R2) every recursive call satisfies its own invariant, and for
τ ≠ 0, w_m(realize_m(τ,β)) = β; (R3) R_{m,β}(realize_m(τ,β)) = τ.

*Proof.* Induction on m. m = 0: trivial; m = 1 is [IL3] WELL-DEF(i)'s display
(single-line monomial sum; note (I₁): β ≥ e₀g₀h₀ gives e₀u(β) = β − s(β)h₀ ≥
e₀g₀h₀ − (e₀−1)h₀, so u(β) ≥ (g₀−1)h₀ + h₀/e₀ > (g₀−1)h₀ — admissible).
Step: **invariant descent.** k_i ≤ (e_{m−1}−1) + (g_{m−1}−1)e_{m−1} =
e_{m−1}g_{m−1} − 1, so by (I_m):

    γ⁽ⁱ⁾ ≥ (β − (e_{m−1}g_{m−1}−1)γ_m)/e_{m−1} ≥ γ_m/e_{m−1}
         = (e_{m−1}e_{m−2}g_{m−2}γ_{m−1} + h_{m−1})/e_{m−1} > e_{m−2}g_{m−2}γ_{m−1},

which is (I_{m−1}) for every child. (R1): each summand has degree
< deg Φ_{m−1}·(1 + k_i) ≤ deg Φ_{m−1}·e_{m−1}g_{m−1} = deg Φ_m. (R2)/(R3):
each summand is the single Φ_{m−1}-digit realize_{m−1}(…) at slot k_i (IH
(R1)), on the line e_{m−1}γ⁽ⁱ⁾ + k_iγ_m = β (IH (R2), τ_i ≠ 0); distinct i
give distinct slots, so developments add slotwise and w_m ≥ β. The level-m
read at β: grid abscissas s + je_{m−1} = exactly the k_i; coefficient at slot
i: ε_{m−1}(γ⁽ⁱ⁾)·R_{m−1,γ⁽ⁱ⁾}(child) = ε_{m−1}(γ⁽ⁱ⁾)·ε_{m−1}(γ⁽ⁱ⁾)^{−1}τ_i =
τ_i (IH (R3)); so the read is Σ τ_i y^i ↦ τ ≠ 0, forcing w_m = β exactly. ∎

**Lemma WELL-DEF-(n) (the canonical lifts exist on the class; the exact
g_m = 1 corner form).** (i) Every C_k of the S0.1 lift construction is
well-defined: its realize_m entry weight gp = (g_m−k)γ_{m+1} ≥ γ_{m+1} =
e_me_{m−1}g_{m−1}γ_m + h_m > e_{m−1}g_{m−1}γ_m satisfies (I_m). (ii) At
g_m = 1 (ψ_m = y + c_m, c_m := ψ_m(0) ≠ 0, z_{m+1} = −c_m, K_{m+1} = K_m):

    Φ_{m+1} = Φ_m^{e_m} + Ĉ_m,   Ĉ_m := realize_m(τ_m, γ_{m+1}),
    τ_m := ε_m(γ_{m+1})^{−1}·c_m ∈ K_m^×,

with (Ĉ1) deg Ĉ_m < deg Φ_m — a single Φ_m-slot-0 digit; (Ĉ2)
w_m(Ĉ_m) = γ_{m+1}; (Ĉ3) R_{m,γ_{m+1}}(Ĉ_m) = τ_m. All three from
REALIZE-(m). ∎ (At m = 1 this is [IL3] WELL-DEF(ii) verbatim.)

**Lemma READ-ADD-(m) (read additivity with strict-above kill; generic).** For
f, g ∈ O[x] with w_m(f) ≥ λ, w_m(g) > λ: R_{m,λ}(f+g) = R_{m,λ}(f) (reads at
a prescribed line λ ≤ w: digits develop additively; a digit strictly above
its slot line contributes 0).
*Proof.* Induction on m. m = 1: developments add (uniqueness); at each grid
abscissa the g-digit either has w₀ strictly above the required ordinate (res
kills strict π-excess) or g has no digit there. Step: dev_m(f+g) =
dev_m(f) + dev_m(g) slotwise; at each grid slot of the λ-read, g's digit has
w_{m−1} strictly above the slot weight (else w_m(g) ≤ λ), and by IH at level
m−1 it contributes 0 to that slot's read. ∎

### S4.2 L6-(n) (ANCHOR-VAL = the ε-chain; all n, no engine, no DCX)

**Proposition L6-(n).** For every rung n ≥ 1 and γ ∈ W_{n+1}:

    val(φ_γ) = ε_n(β_n(γ)) · ε_{n−1}(β_{n−1}(γ)) · ⋯ · ε₁(β₁(γ)) ∈ K_{n+1}^×,
    and w_{n+1}(φ_γ) = γ.

*Proof.* Induction on n; base n = 1 = [IL S4 L6] (ACCEPTED; rule-8 package as
pasted in the header: harness tower class, standard-lift, strict superset of
DITER_RESTATE §S2's E₂ > 1 pin, on-the-nose at E₂ > 1, residuals
(ITER-LAW-LIFT) / gr(w₂)-wrapper / orders ≥ 3 in force). Step: by TRUNC,
φ_γ = a·Φ_n^{s_{n+1}} with a = φ⁽ⁿ⁾_{β_n(γ)}. Degree telescope: deg a =
Σ_{j<n} s_{j+1}·deg Φ_j ≤ Σ_{j<n} (e_j−1)·deg Φ_j ≤ Σ_{j<n} (deg Φ_{j+1} −
deg Φ_j) = deg Φ_n − d₀ < deg Φ_n (using deg Φ_{j+1} = e_jg_j·deg Φ_j ≥
e_j·deg Φ_j). So the Φ_n-development of φ_γ is the single digit a at slot
s_{n+1}. By the IH: w_n(a) = β_n(γ) and R_nv(a) = ∏_{j<n} ε_j(β_j) (TRUNC
matches all split data). Hence w_{n+1}(φ_γ) = e_nβ_n + s_{n+1}γ_{n+1} = γ;
the level-(n+1) grid at γ is s_{n+1} + je_n; the digit sits at j = 0 with
slot weight (γ − s_{n+1}γ_{n+1})/e_n = β_n = w_n(a): on-line; all other grid
slots carry zero digits. So val(φ_γ) = ε_n(β_n)·R_nv(a)·z̄⁰ = the ε-chain, a
unit (unit powers in the field K_{n+1}). ∎

(The L6 chain is therefore unconditional at EVERY rung given only [IL] — the
base as ACCEPTED on the harness tower class, standard-lift, strict superset
of §S2's E₂ > 1 pin, three residuals in force — and never consumes W-MULT,
(RM-m), or any DCX exclusion. The 5-read instance: B1_L6 56/56 exact, S8.)

### S4.3 The induction package (ITER-PKG-r)

**(ITER-PKG-r)** — the exports of rung r, for (r+1)-read towers of the class
and pairs (β, β′) in the window, OFF DCX-(r); P := φ⁽ʳ⁺¹⁾_β·φ⁽ʳ⁺¹⁾_{β′};
plain carries δ_j^{pl} of the pair at each level; B_j the split sums:

* **(P-L6)**: val(φ_β) = ∏_{j=1}^{r} ε_j(β_j) ≠ 0; w(φ_β) = β.
  [No DCX exclusion needed for this clause — L6-(n), S4.2.]
* **(P-WM)**: val(P) = z_{r+1}^{δ_{r+1}^{pl}}·val(φ_β)·val(φ_{β′})
  = z_{r+1}^{δ_{r+1}^{pl}}·∏_{j=1}^{r} z_j^{δ_j^{pl}}·∏_{j=1}^{r} ε_j(B_j);
  the level-(r+1) read of P is a SINGLE nonzero coefficient, at slot
  δ_{r+1}^{pl}; w(P) = β+β′.
* **(P-DS)** (digit shapes of P, certified for the next level): the
  Φ_r-development of P has slot support ⊆ {S_{r+1}, S_{r+1}+1}
  (S_{r+1} := s_{r+1}(β)+s_{r+1}(β′)); the slot-S_{r+1} digit E₀ ≠ 0 has
  deg E₀ < deg Φ_r, w_r(E₀) = B_r, and CERTIFIED READ
  R_rv(E₀) = ∏_{j=1}^{r} z_j^{δ_j^{pl}}·∏_{j=1}^{r−1} ε_j(B_j); the
  slot-(S_{r+1}+1) digit E₁ (possibly 0) has deg E₁ < deg Φ_r and
  w_r(E₁) ≥ B_r − e_{r−1}γ_r; and E₁ ≠ 0 only in the CASE-II stratum:
  CII_r := (g_{r−1} = 1) ∧ (δ_r^{pl} = 1 ∨ (CII_{r−1} ∧ S_r = e_{r−1}−1)),
  with CII₁ := (g₀ = 1 ∧ δ₁^{pl} = 1).

**Base r = 1 (ACCEPTED).** (P-L6) = [IL S4 L6]; (P-WM) = [IL S4 L7 + COR-5];
(P-DS) = [IL L7]'s displayed developments: Case I — E₀ = π^UΦ₀^{S₁} at slot
S₂, w₁ = B₁, read z₁^{δ₁^{pl}} (the empty ε-product), E₁ = 0; Case II
(g₀ = 1 ∧ δ₁^{pl} = 1) — E₀ = A₀ = −ĉ₀π^{U+h₀}Φ₀^{S₁−e₀} at slot S₂, w₁ =
B₁, read −c₀ = z₁ = z₁^{δ₁^{pl}}, and E₁ = A₁ = π^UΦ₀^{S₁−e₀} at S₂+1 with
w₁(A₁) = B₁ − e₀h₀ = B₁ − e₀γ₁ (the γ₁ = h₀ convention makes the DS weight
clause uniform). DCX-(1) = ∅. All from [IL], ACCEPTED 2026-08-03 — rule-8
package pasted: "Scope as accepted: the harness tower class (superset of
DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose coincidence restricted to
E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂)
wrapper rides the accepted GRB retarget; orders ≥ 3 untouched" —
standard-lift, strict superset of the pinned E₂ = e₀e₁ > 1 setting.

**Link r = 2 ([IL3], ATTEMPT GRADE 0/2; round 2 completed not-clean on
narrow display/naming findings, errata round 2 → round 3 owed).** (P-L6) = its
L6-(3); (P-WM) = its W-MULT-(3) (proved off DCX_2); (P-DS) = its S4.4–S4.6
digit constructions: Case I E₀ = A (single digit, w₂ = B₂, read
z₂^{δ₂}z₁^{δ₁}ε₁(B₁)), E₁ = 0; II-1 E₀ = −aĈΦ₁^k−QΦ₁^{k+1} (w₂ = B₂, read as
displayed), E₁ = aΦ₁^k with w₂(E₁) = B₂ − e₁γ₂; II-2/II-3 likewise (its S4.6
line tables give exactly the (P-DS) weight clauses — checked term by term in
S4.6 below at general level). CII₂ = (g₁ = 1) ∧ (δ₂^{pl} = 1 ∨ (CII₁ ∧
S₂ = e₁−1)) = its CASE-SPLIT Cases II-1∪II-2∪II-3 predicate on the nose.

**The inductive step (S4.4–S4.6): (ITER-PKG-r) off DCX-(r), plus (RM-r) ⟹
(ITER-PKG-(r+1)) off DCX-(r+1).** [DCX-(r+1) := DCX-(r)-pullback ∪ the new
top corner DCX_{r+1}; S4.7.]

### S4.4 CASE-SPLIT-(n) (the exact partition at the top of rung n)

Fix rung n = r+1 and γ, γ′ ∈ W_{n+1} with the inner pair (β_n, β_n′) off
DCX-(n−1) (else the pair is in DCX-(n) and excluded). By TRUNC, P :=
φ_γφ_{γ′} = A·Φ_n^{S_{n+1}} with A := φ⁽ⁿ⁾_{β_n}φ⁽ⁿ⁾_{β_n′}, and the IH
(P-DS) gives A's Φ_{n−1}-slot support ⊆ {S_n, S_n+1}, E₁ᴵᴴ ≠ 0 only on
CII_{n−1}. deg A < deg Φ_n ⟺ top slot of A ≤ e_{n−1}g_{n−1} − 1. Exactly one
of:

* **Case I** (deg A < deg Φ_n): automatic at g_{n−1} ≥ 2 (top slot ≤
  S_n+1 ≤ 2e_{n−1}−1 < e_{n−1}g_{n−1}); at g_{n−1} = 1: E₁ᴵᴴ = 0 ∧
  δ_n^{pl} = 0, or E₁ᴵᴴ ≠ 0 ∧ S_n ≤ e_{n−1}−2.
* **Case II-1**: g_{n−1} = 1, E₁ᴵᴴ = 0, δ_n^{pl} = 1 (forces e_{n−1} ≥ 2).
* **Case II-2**: g_{n−1} = 1, E₁ᴵᴴ ≠ 0, δ_n^{pl} = 1.
* **Case II-3**: g_{n−1} = 1, E₁ᴵᴴ ≠ 0, S_n = e_{n−1}−1 (δ_n^{pl} = 0).

*Proof.* Direct from the slot support (E₁ᴵᴴ = 0: overflow ⟺ S_n ≥
e_{n−1}g_{n−1}, possible only at g_{n−1} = 1 with S_n ≥ e_{n−1} ⟺
δ_n^{pl} = 1; E₁ᴵᴴ ≠ 0: overflow ⟺ S_n+1 ≥ e_{n−1}, i.e. δ_n^{pl} = 1 or
S_n = e_{n−1}−1). ∎ (At n = 2 this is [IL3] CASE-SPLIT verbatim with "inner
Case II" = CII₁; the union of Cases II-* is CII_n — the (P-DS) predicate
propagates by construction.)

Weights consumed below (IH (P-DS)): w_n(A) = B_n attained at slot S_n; the
E₁ᴵᴴ-slot line at level n is ≥ e_{n−1}(B_{n−1}−e_{n−2}γ_{n−1}) +
(S_n+1)γ_n = B_n + (γ_n − e_{n−1}e_{n−2}γ_{n−1}) ≥ B_n + h_{n−1} when CII
holds (g_{n−2} = 1, so w_{n−1}Φ_{n−1} = e_{n−2}γ_{n−1}) — strictly above.

### S4.5 W-MULT-(n), Case I (single top digit) — PROVED, generic

The Φ_n-development of P is the single digit A at slot S_{n+1}. w_{n+1}(P) =
e_nw_n(A) + S_{n+1}γ_{n+1} = e_nB_n + S_{n+1}γ_{n+1} = Γ″ (sum γ = e_nβ_n +
s_{n+1}γ_{n+1} over the pair). Grid at Γ″: s_{n+1}(Γ″) = S_{n+1} − δe_n
(L1), so A sits at slot j = δ with slot weight (Γ″ − S_{n+1}γ_{n+1})/e_n =
B_n = w_n(A): on-line; all other grid slots carry zero digits. The read of P
is the single coefficient

    C_δ = ε_n(B_n)·R_nv(A) = ε_n(B_n)·z_n^{δ_n^{pl}}·∏_{j<n} z_j^{δ_j^{pl}}·∏_{j<n} ε_j(B_j)

at slot δ (IH (P-WM) on the digit — the LEVEL-(n−1) LAW consumed exactly as
rung 2 consumed rung 1), whence

    val(P) = z̄^{δ}·∏_{j=1}^{n} z_j^{δ_j^{pl}}·∏_{j=1}^{n} ε_j(B_j)
           = z̄^{δ}·val(φ_γ)·val(φ_{γ′})

(the second equality: EPS-MULT at every level, EXP-KIT(b), + L6-(n)). The
(P-DS) export: E₀ⁿᵉʷ = A (w_n = B_n; certified read = the display above
without the ε_n(B_n)-factor — i.e. ∏_{j≤n}z_j^{δ_j^{pl}}∏_{j≤n−1}ε_j(B_j)),
E₁ⁿᵉʷ = 0. ∎

### S4.6 The engine (RM-m), and Cases II-1/II-2/II-3 — PROVED generic MODULO (RM-(n−1)), off DCX-(n)

**THE OPEN ENGINE FAMILY — the exact statement (the one resisting leg).**

┌────────────────────────────────────────────────────────────────────────┐
│ **(RM-m) [READ-MULT with the canonical correction, level m], 1 ≤ m.**  │
│ Setting: level m of a class tower with g_m = 1, Ĉ_m the canonical      │
│ correction digit of WELL-DEF-(n)(ii) (deg < deg Φ_m, w_m = γ_{m+1},   │
│ R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}c_m). Input: f ∈ O[x],    │
│ f ≠ 0, deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f) its read. Claim: │
│ there exist R, Q ∈ O[x] with deg R < deg Φ_m, deg Q < deg Φ_m, and    │
│                                                                        │
│   f·Ĉ_m = R + Q·Φ_m,   w_m(R) ≥ λ + γ_{m+1},                          │
│   w_m(Q) ≥ λ + γ_{m+1} − w_mΦ_m   (Q = 0 allowed),                    │
│   R_{m,λ+γ_{m+1}}(R) = z_m^{ε′}·v·τ_m,                                │
│   ε′ := ⌊(s_m(λ) + s_m(γ_{m+1}))/e_{m−1}⌋  [the level-m EPS-carry].   │
│                                                                        │
│ STATUS. m = 1: PROVED — [IL3] DIGIT-SPLIT + DEV-1 (attempt grade 0/2; │
│ round-2 arc not-clean on narrow findings, rounds owed) + the           │
│ double-sum factoring: writing f = Σ b_iΦ₀^i,                          │
│ Ĉ₁ = Σ c_jΦ₀^{k_j}, each coefficient product splits by DIGIT-SPLIT    │
│ and reduces by DEV-1 (children have Φ₀-exponent ≤ 2e₀g₀−2 < 2e₀g₀);   │
│ on-line contributions carry i ≡ s_m(λ), k_j ≡ s_m(γ₂) (mod e₀), and   │
│ (i+k_j−s_m(λ+γ₂))/e₀ = (i−s_m(λ))/e₀ + (k_j−s_m(γ₂))/e₀ + ε′, so the  │
│ read factors as z₁^{ε′}·v·τ₁ exactly. SCOPE inherited from the DEV-1  │
│ erratum: proved for e₀ ≥ 2, and at e₀ = 1 ∧ d₀ = 1 (junkΦ ≡ 0); at    │
│ {e₀ = 1 ∧ d₀ ≥ 2} general inputs enter [IL3]'s fenced DEV-1 corner —  │
│ open there ([IL3]'s own consumptions dodge it, PE-verified; rung ≥ 3  │
│ steps never consume RM-1).                                             │
│ m ≥ 2: **OPEN.** Expected resistances (stated so the unit is priced   │
│ honestly): (i) TERMINATION — the level-m reduction tree mixes the     │
│ standard-lift identity at level 1 with the canonical-correction        │
│ identities Φ_i^{e_ig_i}-shape at 2 ≤ i ≤ m, and the e-descent failure │
│ mode of the DEV-1 erratum (non-descending junk children at e = 1)     │
│ recurs at every level — a well-founded measure across levels is the   │
│ real content; (ii) READ-TRANSPARENCY across Ĉ-insertions:             │
│ 𝔯_m(XΦ_{m−1}^{e_{m−1}}) = 𝔯_m(XΦ_m) − 𝔯_m(XĈ_{m−1}) (the [IL3] S4.7   │
│ DEV-2 clause, per level); (iii) input-class closure (the IH (P-DS)    │
│ exports and their junk legs under the weight filtration). PRICE: one  │
│ dedicated unit per level-family (the wave-20 (W-MULT-3-DCX)/DEV-2     │
│ queue item is the m = 2 instance; a generic-engine unit would subsume │
│ the whole family). Instance evidence: every probed instance at rungs  │
│ 2, 3, 4 (S8) is consistent with (RM-m) — cited as evidence only.      │
└────────────────────────────────────────────────────────────────────────┘

**Case II-1 (g_{n−1} = 1, E₁ᴵᴴ = 0, δ_n^{pl} = 1) — proved modulo
(RM-(n−1)).** A = E₀ᴵᴴ·Φ_{n−1}^{S_n}, k := S_n − e_{n−1} ∈ [0, e_{n−1}−2].
One substitution Φ_{n−1}^{e_{n−1}} = Φ_n − Ĉ_{n−1} (WELL-DEF-(n)(ii)):

    P = E₀ᴵᴴΦ_{n−1}^{k}·Φ_n^{S_{n+1}+1} − E₀ᴵᴴĈ_{n−1}Φ_{n−1}^{k}·Φ_n^{S_{n+1}},

both Φ_n-cofactors of degree < deg Φ_n (k+2 ≤ e_{n−1} = e_{n−1}g_{n−1}), so
this IS the development: E₁ⁿᵉʷ := E₀ᴵᴴΦ_{n−1}^k at slot S_{n+1}+1, E₀ⁿᵉʷ :=
−E₀ᴵᴴĈ_{n−1}Φ_{n−1}^k at slot S_{n+1}. Apply (RM-(n−1)) to f = E₀ᴵᴴ
(λ = B_{n−1}, v = the IH certified read): E₀ᴵᴴĈ_{n−1} = R + QΦ_{n−1}, so
E₀ⁿᵉʷ = −RΦ_{n−1}^k − QΦ_{n−1}^{k+1}, slots ⊆ {k, k+1} ⊆ [0, e_{n−1}−1]:

* slot k line: e_{n−1}(B_{n−1}+γ_n) + kγ_n = e_{n−1}B_{n−1} + S_nγ_n = B_n,
  attained (the R-read z_{n−1}^{ε′}vτ_{n−1} is a product of units ≠ 0);
* slot k+1 line: ≥ e_{n−1}(B_{n−1}+γ_n−w_{n−1}Φ_{n−1}) + (k+1)γ_n =
  B_n + h_{n−1} > B_n.

So w_n(E₀ⁿᵉʷ) = B_n. Level-n read at B_n: grid s_n(B_n) + je_{n−1} with
s_n(B_n) = S_n − e_{n−1} = k (L1, δ_n^{pl} = 1); j = 0 reads −R:

    C₀ = ε_{n−1}(B_{n−1}+γ_n)·(−z_{n−1}^{ε′}·v·τ_{n−1})
       = −c_{n−1}·v·ε_{n−1}(B_{n−1})        [EPS-MULT: ε_{n−1}(B_{n−1}+γ_n)
         = z_{n−1}^{−ε′}ε_{n−1}(B_{n−1})ε_{n−1}(γ_n); τ_{n−1} contributes
         ε_{n−1}(γ_n)^{−1}c_{n−1} — the ε′-carry/canonical-lift CANCELLATION]
       = z_n^{δ_n^{pl}}·v·ε_{n−1}(B_{n−1})   [z_n = −c_{n−1}, δ_n^{pl} = 1];

j ≥ 1: abscissa k+je_{n−1} ≥ k+2 carries zero digits; k+1 is off the grid
(e_{n−1} ≥ 2). So R_nv(E₀ⁿᵉʷ) = z_n^{δ_n^{pl}}vε_{n−1}(B_{n−1}) =
∏_{j≤n}z_j^{δ_j^{pl}}∏_{j≤n−1}ε_j(B_j) — the (P-DS) export. Top level:
slot S_{n+1} line = e_nB_n + S_{n+1}γ_{n+1} = Γ″; slot S_{n+1}+1 line =
e_n(B_n − e_{n−1}γ_n) + (S_{n+1}+1)γ_{n+1} = Γ″ + h_n (g_{n−1} = 1) — off
grid at e_n ≥ 2, on-grid-strictly-above at e_n = 1 (slot weight B_n −
γ_{n+1} < B_n − e_{n−1}γ_n = w_n(E₁ⁿᵉʷ)); read 0 either way. Grid:
s_{n+1}(Γ″) = S_{n+1} − δe_n, E₀ⁿᵉʷ at slot δ, on-line. Hence

    val(P) = z̄^{δ}·ε_n(B_n)·R_nv(E₀ⁿᵉʷ) = z̄^{δ}·val(φ_γ)·val(φ_{γ′}). ∎

**Case II-2 (E₁ᴵᴴ ≠ 0, δ_n^{pl} = 1) — proved modulo (RM-(n−1)), off
DCX_n.** A = E₁ᴵᴴΦ_{n−1}^{S_n+1} + E₀ᴵᴴΦ_{n−1}^{S_n}; substitute on both
overflowing slots (k := S_n − e_{n−1}):

    P = [E₁ᴵᴴΦ^{k+1} + E₀ᴵᴴΦ^{k}]·Φ_n^{S_{n+1}+1}
        − [E₁ᴵᴴĈΦ^{k+1} + E₀ᴵᴴĈΦ^{k}]·Φ_n^{S_{n+1}}     (Φ := Φ_{n−1}).

E₁ⁿᵉʷ := E₁ᴵᴴΦ^{k+1} + E₀ᴵᴴΦ^k: slots ≤ k+1 ≤ e_{n−1}−1, a digit;
w_n(E₁ⁿᵉʷ) ≥ B_n − e_{n−1}γ_n (slot k line = B_n − e_{n−1}γ_n; slot k+1
line ≥ B_n − e_{n−1}γ_n + h_{n−1}, using w_{n−1}(E₁ᴵᴴ) ≥ B_{n−1} −
e_{n−2}γ_{n−1} and γ_n − e_{n−1}e_{n−2}γ_{n−1} = h_{n−1} at g_{n−2} = 1) —
the (P-DS) E₁-weight clause propagates. Two engine calls: E₀ᴵᴴĈ = R⁰+Q⁰Φ
(read clause consumed), E₁ᴵᴴĈ = R¹+Q¹Φ (WEIGHT clauses only). E₀ⁿᵉʷ =
−R⁰Φ^k − (Q⁰+R¹)Φ^{k+1} − Q¹Φ^{k+2}. **Off DCX_n (k+2 ≤ e_{n−1}−1 or
Q¹ = 0)** E₀ⁿᵉʷ is a digit, and: slot k on-line at B_n (R⁰-read ≠ 0); slot
k+1 lines ≥ B_n + h_{n−1} (Q⁰ as in II-1; R¹ ≥ e_{n−1}(B_{n−1} −
e_{n−2}γ_{n−1} + γ_n) + (k+1)γ_n = B_n + γ_n − e_{n−1}e_{n−2}γ_{n−1} =
B_n + h_{n−1}); slot k+2 (if Q¹ ≠ 0, which with k+2 ≤ e_{n−1}−1 forces
e_{n−1} ≥ 3 — the [IL3] N3 vacuity, generic) line ≥ B_n + 2h_{n−1}, off-grid
at e_{n−1} ≥ 3. So w_n(E₀ⁿᵉʷ) = B_n, grid s_n(B_n) = k, the j = 0
coefficient is C₀ = ε_{n−1}(B_{n−1}+γ_n)·(−R⁰-read) = z_n^{δ_n^{pl}}·v⁰·
ε_{n−1}(B_{n−1}) exactly as in II-1 (v⁰ := the E₀ᴵᴴ certified read); higher
grid slots zero/above-line (READ-ADD-(n−1) where components share a slot).
Top level verbatim as II-1 (E₁ⁿᵉʷ's weight bound gives slot-(S_{n+1}+1)
line ≥ Γ″ + h_n). val(P) = z̄^δ·val·val ∎, and (P-DS) exports as displayed.

**Case II-3 (E₁ᴵᴴ ≠ 0, S_n = e_{n−1}−1, δ_n^{pl} = 0) — proved modulo
(RM-(n−1)), off DCX_n.** Only slot S_n+1 = e_{n−1} overflows:

    P = E₁ᴵᴴ·Φ_n^{S_{n+1}+1} + [E₀ᴵᴴΦ^{e_{n−1}−1} − E₁ᴵᴴĈ]·Φ_n^{S_{n+1}}.

E₁ⁿᵉʷ = E₁ᴵᴴ: slot S_{n+1}+1 line = e_ne_{n−1}w_{n−1}(E₁ᴵᴴ) +
(S_{n+1}+1)γ_{n+1} ≥ Γ″ + h_n + e_nh_{n−1} > Γ″ (the S4.4 weight display).
E₀ⁿᵉʷ = E₀ᴵᴴΦ^{e_{n−1}−1} − R¹ − Q¹Φ (engine on E₁ᴵᴴĈ, weight clauses
only). **Off DCX_n (e_{n−1} ≥ 2 or Q¹ = 0)** E₀ⁿᵉʷ is a digit: slot
e_{n−1}−1 carries E₀ᴵᴴ (w = B_{n−1}, line B_n, attained); R¹ at slot 0, line
≥ e_{n−1}(B_{n−1} − e_{n−2}γ_{n−1} + γ_n) = B_n − (e_{n−1}−1)γ_n + γ_n −
e_{n−1}e_{n−2}γ_{n−1}... = B_n + h_{n−1} + (e_{n−1}−1)(γ_n... [direct: line
− B_n = e_{n−1}(γ_n − e_{n−2}γ_{n−1}) − (e_{n−1}−1)γ_n = γ_n −
e_{n−1}e_{n−2}γ_{n−1} = h_{n−1} > 0]; Q¹ at slot 1, line ≥ B_n + 2h_{n−1} −
... > B_n similarly. Slot collisions (slot 1 = e_{n−1}−1 at e_{n−1} = 2;
slot 0 = e_{n−1}−1 at e_{n−1} = 1 with Q¹ = 0): benign — the colliding
summand sits strictly above the line inside the digit and READ-ADD-(n−1)
kills it. Grid s_n(B_n) = S_n = e_{n−1}−1 (δ_n^{pl} = 0): the j = 0
coefficient is C₀ = ε_{n−1}(B_{n−1})·v⁰ = z_n^0·v⁰·ε_{n−1}(B_{n−1}),
matching δ_n^{pl} = 0. Top level as before. val(P) = z̄^δ·val·val ∎.

(At n = 2 the three legs specialize clause-for-clause to [IL3] S4.5/S4.6
with (γ_n, e_{n−1}, z_n, ε_{n−1}, c_{n−1}, v) = (γ₂, e₁, z₂, ε₁, c₁,
z₁^{δ₁}) — a consistency display, not a second proof; [IL3]'s own grade
0/2 rides every rung-2 consumption.)

### S4.7 DCX-(n): the excluded locus, characterized per level

**Definition.** For 2 ≤ m ≤ n, DCX_m := the pairs whose level-m top analysis
(the S4.6 cases run on the truncated pair at level m, via TRUNC the split
data are literally shared) has a SECOND-ROUND OVERFLOW: the engine Q-part of
the E₁-product lands at Φ_{m−1}-slot ≥ e_{m−1} (II-2: slot k+2 = e_{m−1};
II-3: slot 1 ≥ e_{m−1}, i.e. e_{m−1} = 1) with Q ≠ 0 — a second substitution
Φ_{m−1}^{e_{m−1}} = Φ_m − Ĉ fires on Q and the one-round analysis above does
not close. **DCX-(n) := ∪_{m=2}^{n} DCX_m.**

**Outer bound (PROVED, generic — from the S4.6 slot arithmetic alone):**

    DCX_m ⊆ DCX_m^out := { g_{m−1} = 1,  s_m(γ) = s_m(γ′) = e_{m−1}−1,
                            CII_{m−1} holds for the pair }
           ⊆ { g_{m−2} = g_{m−1} = 1, s_m-track extreme }.

*Proof.* Q-emission at slot ≥ e_{m−1} requires: from Q⁰ (the E₀-product) at
slot k+1: k+1 ≥ e_{m−1} ⟺ S_m ≥ 2e_{m−1}−1, impossible (S_m ≤ 2e_{m−1}−2);
so only the E₁-product's Q¹, needing E₁ᴵᴴ ≠ 0 (⟹ CII_{m−1}, ⟹ g_{m−2} = 1
by (P-DS)) and slot k+2 ≥ e_{m−1} (II-2: S_m = 2e_{m−1}−2 ⟺ both s_m-values
= e_{m−1}−1) or e_{m−1} = 1 (II-3: s_m ≡ 0 = e_{m−1}−1 automatically). ∎

**Sharp form and emptiness:**
* m = 2 (PROVED = [IL3] S4.7, attempt grade 0/2): DCX_2 = {g₀ = g₁ = 1,
  δ₁^{pl} = 1, s₂ = s₂′ = e₁−1, S₁ + s(γ₂) ≥ 2e₀} — EMPTY unless e₀ ≥ 3.
* m ≥ 3: the exact Q¹-emission predicate is (RM-(m−1))-internal — the sharp
  characterization is OPEN, priced with the engine. Proved emptiness NOW:
  DCX_m = ∅ whenever g_{m−2} ≥ 2 or g_{m−1} ≥ 2 (outer bound). CONJECTURED
  (the e_{j−1} ≤ 2 analogue, from the m = 2 mechanism + all instance data):
  DCX_m = ∅ unless e_{m−2} ≥ 3.
* Consequences: DCX-(n) = ∅ on the sub-class with no two consecutive
  degree-1 reads among ψ₀,…,ψ_{n−1}; and at n = 2, DCX-(2) = ∅ iff-covered
  by e₀ ≤ 2 (proved). The full-class emptiness statement for n ≥ 3 at
  e_j ≤ 2 is conjectural (engine-dependent).

**On DCX-(n) the W-MULT display is the OPEN family (W-MULT-DCX-m)** —
instance-true at every probed instance (rung 2: [IL3] S4.7's roster-B
evidence + its diag 16 DCX pairs/0; rung 3: the sealed 4-read battery's
strata; rung 4: this unit's diagnostic — T5B realizes 16 sharp-DCX_2 pairs
per instance at 5 reads, law exact on ALL of them, S8). The DEV-2/engine
unit's price display ([IL3] S4.7) carries over; a proof of (RM-m) with a
second-round clause would close both II-legs and DCX at once.

## S5. The theorem (assembly; the induction closed on the stated perimeter)

*Proof of (ITER-LAW-n), by induction on the rung, off DCX-(n), modulo the S7
ledger.* Rung 1 = [IL] (ACCEPTED 2026-08-03; rule-8 package pasted: "Scope as
accepted: the harness tower class (superset of DITER_RESTATE §S2's E₂ > 1
pin; on-the-nose coincidence restricted to E₂ > 1); residuals:
(ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the
accepted GRB retarget; orders ≥ 3 untouched" — standard-lift, strict superset
of the pinned E₂ = e₀e₁ > 1 setting): its display IS the n = 1 recursion
(δ = δ₂, S₁ = γ₂δ₂, D₁ = (s₁-defect + ℓ₀γ₂δ₂)/e₀). Rung n ≥ 2: assume
(ITER-PKG-(n−1)) on the truncated tower (n = 2: the base; n = 3: [IL3] at
0/2; n ≥ 4: the S4 step iterated, consuming (RM-m) for 2 ≤ m ≤ n−1). Let
γ, γ′ ∈ W_{n+1}, pair off DCX-(n); Γ″ ∈ W_{n+1} (WINDOW-(n)). By L6-(n) at
Γ″ and W-MULT-(n) (S4.5/S4.6):

    c_{n+1}(γ,γ′) = z̄^{δ} · ∏_{j=1}^{n} [ z_j^{δ_j^{pl}}·ε_j(B_j)/ε_j(β_j″) ].

For each j, β_j″ = B_j + S_j (SHIFT-(n)), so EXP-KIT(c) at
(e_{j−1}, h_{j−1}, ℓ_{j−1}, z_j) with T = S_j turns the j-th bracket into
z_j^{D_j}, D_j = (s_j-defect + ℓ_{j−1}S_j)/e_{j−1} ∈ ℤ — the recursion's
exponents exactly; the internal carries δ_j^{pl} cancel inside the per-level
kernels and do not appear in the law. Hence c_{n+1} = z̄^δ·∏_j z_j^{D_j}. ∎

The (P-WM)/(P-DS) clauses proved in S4.5/S4.6 are exactly (ITER-PKG-n): the
induction climbs. The GRADE of each rung is the S7 ledger — no clause above
is claimed beyond it.

## S6. Corollaries (derived; the OFF-DCX qualifier baked into every
field-level clause from the start — the [IL3] errata-round-1 lesson)

Convention: "on the proved perimeter (n)" = pairs (triples: all constituent
pairs) off DCX-(n), at a rung whose S7 conditionality is met. INTEGER-LEVEL
clauses are unconditional on ALL pairs at ALL rungs.

### S6.1 COR-1: integrality
e_{j−1} | (s_j-defect + ℓ_{j−1}S_j) for every level j and every pair —
D_j-INT, unconditional. The per-level denominator architecture is structural:
each denominator is cured inside its own EXP-KIT kernel; no cross-level
denominator ever forms (the converged reading, now a theorem at every n).

### S6.2 COR-2: the cocycle identity
*Integer level (UNCONDITIONAL, all triples, all n):* the displayed constants
satisfy the additive 2-cocycle identity slotwise — the S2 slotwise lemma.
*Field level (on the proved perimeter (n)):* c_{n+1} = z̄^{δ(·,·)}·∂F with
F(γ) := val(φ_γ) (L6-(n) + W-MULT-(n)): a coboundary times the top-carry
2-cocycle (δ is a 2-cocycle by L1 at (e_n,h_n), associating both ways). ∎

### S6.3 COR-3: degenerations (every field-level clause OFF-DCX; DCX does
NOT evacuate under degeneration — the [IL3] S6.3 erratum lesson, baked in)

* **e_n = 1 (top read trivial):** s_{n+1} ≡ 0, δ = 0, S_n = 0, D_n =
  δ_n^{pl}, S_{n−1} = δ_n^{pl}γ_n — the display collapses VERBATIM to
  (ITER-LAW-(n−1)) of the truncated tower (integer level: unconditional
  identity of constants). Value level: the anchors coincide (Φ_n-exponent
  ≡ 0) and c_{n+1} = embed(c_n) on the proved perimeter (n) — the two-way-tie
  mechanism; diagnostic-confirmed at 5 reads (B6_topcontrol 128/128 exact:
  constants tie AND value tie, S8). At n = 2, e₂ = 1 gives the [IL] law —
  [IL] ACCEPTED (rule-8 package pasted: "Scope as accepted: the harness tower
  class (superset of DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose coincidence
  restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at
  g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the accepted GRB retarget; orders ≥ 3
  untouched"; standard-lift, strict superset of the E₂ = e₀e₁ > 1 pin) — but
  only OFF DCX-(2), per the [IL3] erratum: the degeneration does not empty
  the corner.
* **Interior e_{j−1} = 1:** ℓ_{j−1} = 0, s_j ≡ 0: D_j = 0 and S_{j−1} = S_j
  (passthrough) — unconditional integer identities (diag: 960 passthrough
  checks/0, S8).
* **e₀ = 1:** D₁ = 0, the letter z₁ leaves the law.
* Iterating: all e_j = 1 gives c ≡ 1 (the E = 1 leg trivially covered, as in
  the [IL3] class-coincidence display).
* **DCX non-evacuation witnesses:** [IL3]'s ℤ₅ tower at 3 reads (4 DCX pairs
  per block at e₂ = 1); at 5 reads, T5C (e₄ = 1) carries 4 outer-locus pairs
  per block — empty at the SHARP level only because e₀ = 2 there (S8).

### S6.4 COR-4: ℤ/E_{n+1} descent, representative independence, monodromy
φ_{γ+E_{n+1}} = π·φ_γ exactly and every displayed constant descends to
ℤ/E_{n+1} (unconditional — the S2 descent lemma). The gauge does NOT descend:
by EXP-KIT(a), with Π_j := e₀⋯e_{j−1},

    F(γ+E_{n+1})/F(γ) = ∏_{j=1}^{n} z_j^{−ℓ_{j−1}·Π_{j−1}}  =: ρ   (Π₀ := 1),

a CONSTANT monodromy (the generic ρ display — NEW at n ≥ 3; measured exactly:
A3_rho 36/36 at 4 reads, B5_rho 56/56 at 5 reads, S8). On the proved
perimeter the measured c_{n+1} therefore descends too, mixed blocks included
(diag B5_descent 224/224 one-sided-mixed at 5 reads).

### S6.5 COR-5: the gauge form
On the proved perimeter (n): **c_{n+1} = z̄^{δ}·∂F**, F(γ) = ∏_j ε_j(β_j(γ))
= val(φ_γ), with the closed monomial form (EXP-KIT(a) at every level)
F(γ) = ∏_{j=1}^{n} z_j^{(s_j(γ) − ℓ_{j−1}β_j(γ))/e_{j−1}}, all exponents
integral. Modulo the single top carry the entire law is the explicit
coboundary of the ε-chain, uniformly in n.

### S6.6 What is NOT derived here
The (INV-n) class invariant class(c_{n+1}) = [∏_j z_{j+1}^{Π_j·ℓ_j}] stays
CITED-MEASURED (M2 S3 at 3 reads, single-source; FCLASSS 72/0 at 4 reads) —
not re-derived; flagged for its own leg as before. The J-window fine
structure likewise (M3; FJ1–FJ3 at 4 reads). No new derivation is claimed.

## S7. THE CONDITIONALITY LEDGER (the exact grade of every clause, per rung)

Base citations, once more per rule 8: [IL] = ACCEPTED 2026-08-03 ("Scope as
accepted: the harness tower class (superset of DITER_RESTATE §S2's E₂ > 1
pin; on-the-nose coincidence restricted to E₂ > 1); residuals:
(ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the
accepted GRB retarget; orders ≥ 3 untouched" — standard-lift, strict superset
of the pinned E₂ = e₀e₁ > 1 setting). [IL3] = attempt grade, counter 0/2;
round 2 completed NOT-CLEAN (PC2 1C/1G @ cf013a4 + PE2 0C/2G @ 467b523, all
narrow display/naming findings, S2–S5 math byte-stable); errata round 2 then
round 3 owed; proved off DCX-(2); errata r1 at f9daca0.

| # | clause | rung 1 | rung 2 | rung 3 | rung n ≥ 3 (general) |
|---|---|---|---|---|---|
| 1 | integer layer (SHIFT, D-INT, (★), WINDOW, slotwise cocycle, descent of constants) | UNCONDITIONAL | UNCONDITIONAL | UNCONDITIONAL | UNCONDITIONAL (this note, S2) |
| 2 | EXP-KIT | ACCEPTED instance ([IL]) | proved ([IL3]/S3) | proved (S3) | proved (S3, self-contained) |
| 3 | REALIZE/WELL-DEF/READ-ADD | — | [IL3] + S4.1 | S4.1 | proved generic (S4.1) |
| 4 | L6 chain (anchor = ε-chain) | ACCEPTED | proved given [IL] | proved given [IL] | proved given [IL] only (S4.2) |
| 5 | W-MULT Case I | ACCEPTED ([IL] L7-I) | [IL3] 0/2 | given #6 at rung 2 | generic step proved; chain rides #6 |
| 6 | W-MULT Cases II (off DCX) | ACCEPTED ([IL] L7-II) | [IL3] 0/2 (its DEV-1 = RM-1) | + OPEN (RM-2) | + OPEN (RM-m, 2 ≤ m ≤ n−1) |
| 7 | W-MULT on DCX-(n) | vacuous (DCX-(1) = ∅) | OPEN (W-MULT-3-DCX) | OPEN | OPEN ((W-MULT-DCX-m) family) |
| 8 | THE THEOREM off DCX-(n) | **ACCEPTED** | **attempt grade 0/2** (= [IL3]) | conditional: [IL3] + (RM-2) | conditional: [IL3] + (RM-m), 2 ≤ m ≤ n−1 |
| 9 | COR-1/COR-2-integer/COR-4-constants | UNCOND. | UNCOND. | UNCOND. | UNCONDITIONAL |
| 10 | COR-2-field/COR-3-field/COR-4-gauge/COR-5 | per #8 | per #8 | per #8 | per #8 (proved perimeter) |
| 11 | measured evidence (never proof) | — | 0/123,564+ sealed | 0/362,624 sealed | rung 4: this diag, ~5,300 checks/0 (S8) |

**Failure propagation (displayed honestly):** if the [IL3] round-2 arc does
NOT close clean, the rung-2 link re-opens and every rung ≥ 2 row of #5/#6/#8
falls back to "open at the rung-2 link" — the integer layer (#1), EXP-KIT
(#2), REALIZE (#3), and the L6 chain (#4) are NOT affected (they consume only
[IL] and this note's generic proofs). If (RM-m) is proved for all m, rows
#5/#6/#8 become unconditional-off-DCX at every rung (given [IL3]); if
additionally the second-round clause closes (W-MULT-DCX), the perimeter
becomes the whole class. **The INDUCTION SCHEMA reading (the charter's
fallback grade, achieved-plus):** the exact statements whose proofs would
close ALL orders are: (RM-m) [S4.6 box] and (W-MULT-DCX-m) [S4.7] — two
displayed families, each priced; everything else needed for every n is proved
in this note.

## S8. POST-SEAL-LABELED DIAGNOSTIC (run at composition; NOT a proof step,
NOT a seal; the [IL3]/iterlaw3_proof_diag precedent)

`verification/openmath/iterlawn_diag.py` (md5 cd7581b7fd9df555e517b69556199ef3)
+ `iterlawn_diag_output.txt` (md5 7c72c4c6c0a953ebd41a56eab1e266e1) — exact
arithmetic, deterministic full blocks, exit 0, **ZERO violations across
~5,300 family-checks, first run** (wallclock 2.5 s). Sealed artifacts consumed
READ-ONLY (imports byte-untouched).

**LEG A — 4 reads (RUNG 3), sealed-harness reuse: A4, B4, C3 @ (ℤ_p, p=3):**
the note's NEW generic intermediates on the sealed rows (not displayed in
this form by the sealed battery): A1 shift-cascade β_j″ = B_j + S_j (j=3,2,1)
464/464 · A2 (★)-positivity 464/464 · A3 monodromy ρ =
z₃^{−ℓ₂e₀e₁}z₂^{−ℓ₁e₀}z₁^{−ℓ₀} exact 36/36 (first measurement of the generic
ρ display) · A5 e₁ = 1 passthrough (B4) 144/144 · A4 DCX outer-locus census:
A4-row 28 pairs, C3-row 7, B4-row 0, sharp-DCX₂ 0 everywhere (e₀ = 2 rows —
the proved m = 2 emptiness); measured law re-checked ON all 35 outer-locus
pairs: 35/35 exact (instance evidence for the open corner).

**LEG B — 5 reads (RUNG 4), FRESH — the first 5-read data in the campaign:**
a Tower5/Composite5 mirror layer (one-level-up discipline; canonical
ε-corrected lifts at every level; Φ₄ consumed from the sealed Tower4,
w₄(Φ₄) = e₃g₃γ₄ key asserted). Shapes × rings (E₅ ≤ 12, full W1×W1):
T5A = (1; 2,1,1; 1,1,2; 2,1,1; 1,1,2; 2,1,1), E₅ = 8, @ ℤ₃, F₂[[t]] —
letters z₂, z₄ live, NO DCX locus (no consecutive degree-1 reads: the S4.7
proved-emptiness leg); T5B = (1; 3,2,1; 1,1,1; 2,1,1; 1,1,2; 2,1,1), E₅ = 12,
@ ℤ₃, F₃[[t]] — DCX₂-LIVE BY DESIGN (e₀ = 3, g₀ = g₁ = 1, s(γ₂) = 2);
T5C = (1; 2,1,1; 2,1,1; 1,1,2; 2,1,1; 1,1,2), E₅ = 8, @ ℤ₃, F₂[[t]] — e₄ = 1
top control with a genuine top letter (g₄ = 2). 544 pairs total; per-pair
actuals, all exact:

    B1  L6-(5) anchor = ε₄ε₃ε₂ε₁-chain, ≠ 0:            56/56
    B2  W-MULT-(5) z̄₅^{δ₅}-form + single-top-slot at δ₅
        + w₅(P) = γ+γ′:                                  544/544
    B2' L7-(5) explicit form (plain carries × ε-chain):  544/544
    B3  (ITER-LAW-5) closed form (the first 5-read law): 544/544
    B4  integer cascade j = 4..1 + all D_j integral:     544/544
        (★_j) at every pair and level:                   544/544
    B5  φ_{γ+E₅} = π·φ_γ 24/24 · ρ (4 letters) 56/56 ·
        one-sided MIXED descent:                         224/224
    B6  e₄ = 1 two-way tie (constants AND value):        128/128
        e_j = 1 passthroughs (D_j = 0 ∧ S_{j−1} = S_j):  960/960
    B7  DCX censuses: T5B 16 sharp-DCX₂ pairs per instance (48
        outer), LAW EXACT ON ALL OF THEM (inside B3's zero);
        T5A 0 loci; T5C 4 outer / 0 sharp (e₀ = 2 emptiness).

Standing: instance evidence only. The 5-read data confirms every NEW generic
display of this note ((★), the cascade, ρ, the passthroughs, the two-way tie,
the DCX locus geometry) at a rung never before measured, including on
DCX₂-live pairs. Nothing here upgrades any proof grade.

## S9. Scope box — fences (what this note does NOT do)

* **No (RM-m) proof for m ≥ 2** — THE open engine family, exactly boxed in
  S4.6, priced. No (W-MULT-DCX-m) proof — S4.7. No sharp DCX_m for m ≥ 3.
* **No upgrade to [IL3]** (attempt grade 0/2 stands; round 2 owed first) and
  no edit to it, to [IL], or to any sealed artifact — all consumed read-only;
  brackets on other notes ride the next r-fold (S10).
* **General lawful lifts:** (ITER-LAW-LIFT) propagates to every level
  (canonical ε-corrected lifts are part of the statement; the measured
  LIFT-DEV-3/LIFT-DEV-4 deviations ε_m(γ_{m+1})^{δ} are consistent with, and
  explained by, the S4.6 cancellation — not proved here).
* **(INV-n) class, gr(w) semantics wrapper, GMN transport:** untouched
  (harness-calculus-internal throughout, as at rungs 1–2; the gr(w₂) wrapper
  residual of the [IL] acceptance package — pasted in the header: harness
  tower class, standard-lift, superset of §S2's E₂ > 1 pin, three residuals
  including "gr(w₂) wrapper rides the accepted GRB retarget" — extends: no
  gr(w_{n+1}) claim at any level).
* **No Lean work; no probability/density-side claim; no orders-∞ or
  limit statement.** The theorem is a per-n family with a uniform proof
  skeleton, not a statement about towers of infinite length.

## S10. Records: claim DAG, hostile-pass charges, consumers

**Claim DAG (arrows = consumed-by):**

    [IL L1] → SHIFT-(n) ⇄ D_j-INT → (★)-POS → WINDOW-(n) → S5
    EXP-KIT [self-contained] → S5, S6.4, S6.5
    TRUNC → L6-(n), CASE-SPLIT, S4.5/S4.6
    REALIZE-(m) → WELL-DEF-(n) → S4.6 (Ĉ-clauses); READ-ADD-(m) → S4.6
    [IL pkg r=1] → (ITER-PKG-1) → step → (ITER-PKG-2) [= [IL3], 0/2]
      → step (+RM-2) → (ITER-PKG-3) → … → (ITER-PKG-(n−1))
      → step (+RM-(n−1)) → (ITER-PKG-n)
    L6-(n) + W-MULT-(n) → S5 (THEOREM) → S6.2/6.3/6.4/6.5 field clauses
    (RM-m) [OPEN, m ≥ 2] → S4.6; (W-MULT-DCX-m) [OPEN] → S5 on DCX only

(Rule-8 gloss for the DAG tokens: [IL] = ACCEPTED 2026-08-03 on the harness
tower class, standard-lift, strict superset of DITER_RESTATE §S2's
E₂ = e₀e₁ > 1 pin, on-the-nose at E₂ > 1, residuals (ITER-LAW-LIFT) /
gr(w₂)-wrapper / orders ≥ 3 in force; [IL3] = attempt grade 0/2, round 2
not-clean on narrow findings, errata round 2 → round 3 owed.)

**Suggested hostile-pass charges (2-clean bar; model-diverse):**
(i) CONTENT pass on the generic step's index arithmetic — the places an
error would hide: the (I_m) descent invariant (S4.1), the (★)-POS active-case
inequality chain (S2), the S4.6 line tables (slot k+1/k+2 bounds, the
e_{n−1} ∈ {1,2} collision legs), the (P-DS) weight-clause propagation
(w_r(E₁) ≥ B_r − e_{r−1}γ_r through all three II-legs), and whether ANY step
silently consumes more of the IH than (ITER-PKG-r) states. (ii) EXECUTION
pass: from-note reimplementation of the recursion + the (P-DS) digit
predictions at 5 reads on OFF-diagnostic shapes (the F2c genre), with a
DCX-locus meter checking the S4.7 outer bound is exactly where this note
says. (iii) RULE-8 audit: every [IL] mention carries the pasted acceptance
package; every [IL3] mention carries "attempt grade 0/2" + the round-2
not-clean state.

**Consumers and owed displays (ride the next r-fold; NOT applied here):**
* L3CONVERGENCE S2 Candidate 2: status upgrade owed AT THIS NOTE'S ACCEPTANCE
  only — from "uniform conjecture, three confirmed instances" to "theorem on
  the class off DCX-(n), conditional on the S7 ledger (rows 6–8)". Until the
  hostile arc closes, nothing changes anywhere.
* The (W-MULT-3-DCX)/DEV-2 wave-20 queue item: now the m = 2 instance of the
  (RM-m)/(W-MULT-DCX-m) families; the generic-engine unit is the higher-value
  target (closes every rung at once) — queue decision at the fold.
* [IL3] acceptance arc: unaffected by this unit (round 2 returned NOT-CLEAN
  at cf013a4/467b523 before this compose; errata round 2 + round 3 are that
  arc's own next steps, on its own text). On an eventual clean close, S7
  rows 5/6/8 tighten at rung 2 automatically; on a structural failure they
  re-open per the S7 failure-propagation display.
* HARDEST_FIRST / PROJECT_STATE / ROOT: (ITER-LAW-n) row gains "general-n
  compose executed: generic step proved except the (RM-m) engine family
  (open, priced); integer layer + L6 chain unconditional at all orders;
  first 5-read data 0-violation" — at the fold.

— GENERAL-n COMPOSE unit, campaign date 2026-08-08 (wallclock 2026-08-03).
