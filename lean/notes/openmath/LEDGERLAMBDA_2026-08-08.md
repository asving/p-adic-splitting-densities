# LEDGER-Λ — the graded path ledger on the extended exponent lattice ℤ^{1+m} over the accepted [RMG] S2.2 tree: ONE per-edge quantum table, ONE telescope, and the closure program's five additive bookkeeping displays (E-L1, SD-L2 + (★), W-D4, SDY-L2's spine, W-D5's floor + L-MONO) as weight-functional faces — with POOL-UNROLL and the three micro-moves displayed once

**Unit:** LEDGER-Λ COMPOSE — synthesis pass 9 unit **S7.U1**
(`docs/in-progress/SYNTHESIS_PASS9_2026-08-08.md` S2 + S7.U1: THE
highest-value unification of the pass). Genre: CONSOLIDATION THEOREM note —
one theorem proved fresh from the ACCEPTED [RMG] displays, five corollaries
each audited byte-for-byte against its committed counterpart. Acceptance
counter 0 — no hostile pass has run on THIS note; grade ATTEMPT until its
own arc runs. Author: Fable, campaign date 2026-08-08 (wallclock
2026-08-04).

**SCOPE AND FENCES (stated before anything else).**

* **Scope = the [RMG] S2.2 tree.** Every object below (cells, the three
  identity families, the E1-priority tree, L-NORM splits, lines, the
  λ-chain) is consumed from the ACCEPTED [RMG] note as a DEFINITION or a
  PROVED display; this note is therefore ACCEPTED-based in its substrate.
  The two-stage tree T² (stage 1 = the anchor product, stage 2 = the
  Ĉ_m-seeded quotient) and its counters are the WMULTDCX† S1 setting,
  consumed at ATTEMPT grade.
* **CONSUMPTION-ONLY.** No accepted or committed statement is touched.
  This note SUBSUMES the five displays listed in S3 (they become
  corollaries of one theorem); it does not edit, bracket, or retire them.
  Retirement/supersession brackets happen at the NEXT FOLD, not here (the
  pass-9 charter's explicit fence).
* **THE GRADE-CAP SENTENCE.** The corollary audits consume WMULTDCX†
  (0/2 CLEAN), EMPTY† (1/2), SURVDISJ† (1/2), SDYJ† (0/1), SURV† (0/2) at
  attempt grade; the W arc is the single cap on all of Q2 (pass-9 S8.1).
  THEOREM LED-Λ itself consumes only [RMG] (ACCEPTED) and the [ILN]† class
  pin through it — but every FACE-to-committed-display tie inherits the
  consumed note's grade. Nothing here upgrades anything.

**Incorporation convention (dagger forms, declared once).**
**[RMG]** = `RMENGINE_2026-08-08.md`, **ACCEPTED** 2026-08-08 campaign
(wallclock 2026-08-04) at the corpus's hostile 2-clean model-diverse bar
(round-7 verdicts PC7 + PE7 both CLEAN on a0e266c; theorem RM-GEN on
T-scope(m) = d₀ = 1 ∨ (e₀ ≥ 2 ∧ eᵢ ≥ 2)). Displays consumed from it:
S2.1 (cells, lines, L-CELL, **L-NORM**), S2.2 (the identity families
(ID-(i+1)), the child inventory, L-EXACT, the exit-cofactor structural
remark), S3.1 (λ/t-chain, L-GRID, L-ZMULT), S3.2 (**L-LINE**, L-MONO).
**WMULTDCX†** = `WMULTDCX_2026-08-08.md` at attempt grade 0/2 CLEAN (W-r2
text): the T² setting, W-D1/W-D2/W-D3 (LED_l)/W-D4/W-D5. **EMPTY†** =
`EMPTY_PROOF_2026-08-08.md` (E arc 1/2): E-L1/E-L2/E-L4/E-L5 context.
**SURVDISJ†** = `SURVDISJ_PROOF_2026-08-08.md` (SD arc 1/2): SD-L1/SD-L2/
(★). **SDYJ†** = `SDYJ_PROOF_2026-08-08.md` (SDYJ arc 0/1): SDY-L1/SDY-L2.
**SURV†** = `SURV_PROOF_2026-08-08.md` (S arc 0/2): S-L1. **[ILN]†** = the
ledger block "[ILN] ACCEPTED — 2026-08-03" (`BRIDGE_ADJUDICATIONS`): the
S0.1 class pin and weight recursion, consumed as definitions through
[RMG] S0.1.

**THE EXTRACTION-DECORRELATION LAW, obeyed as follows.** The quantum table
of S1 is assembled FRESH from the [RMG] S2.2 child inventory + L-NORM +
L-LINE (each table row cites its [RMG] display), NOT imported from the
five consuming notes; the five committed displays enter this note ONLY in
S3, as byte-quoted AUDIT TARGETS. The non-textual leg is
`verification/openmath/ledger_lambda_checks.py` — ONE walk-replay runner
that recomputes every path's extended exponent vector per-edge from its
own fresh implementation of the S1 table and checks ALL FIVE faces
simultaneously on BOTH committed rosters (the WMULTDCX battery selection
over `wmultdcx_stress.ROSTER`, and the SURVDISJ/SDYJ rosters), with
mutation controls of the CTRL-TEL0 genre (S5). Per the standing engine
rule (ENGINE REFIT, ledger d326677) the runner imports `engine_ext`,
calls `install()`, and RE-RUNS `agreement_gate()` in-unit, reporting its
counts. Two-commit seal: note + runner at commit 1 with the S5
predictions sealed; verdict appended from the artifacts at commit 2.

## S0. Setting (all consumed; nothing new defined until S1)

Level-m tower data on the [ILN]† S0.1 class through [RMG] S0.1: reads
(e_l, h_l, g_l) with gcd(e_l, h_l) = 1, e_l ≥ 1, h_l ≥ 1; P_l := e_l·g_l;
E_0 := 1, E_l := e₀e₁⋯e_{l−1} (so E_m = e₀⋯e_{m−1}); γ₁ = h₀,
w_lΦ_l = e_{l−1}g_{l−1}γ_l, γ_{l+1} = e_l·w_lΦ_l + h_l; the line scales
Γ_l := γ_{l+1}·∏_{l<t<m} e_t (Γ_{m−1} = γ_m); the promotion quanta
q_l := h_l·∏_{l<t<m} e_t (1 ≤ l ≤ m−1; the L-LINE(i) quantum INTO level
l, WMULTDCX† S5's convention).

Cells C = b·Φ₀^{j₀}⋯Φ_{m−1}^{j_{m−1}} and their lines
line(C) = E_m·w₀(b) + Σ_l j_l·Γ_l are [RMG] S2.1. The tree is the [RMG]
S2.2 E1-priority reduction; T² is WMULTDCX† S1's two-stage instance:
stage 1 reduces the anchor product a·a′ = π^{u₁+u₁′}·∏Φ_l^{σ_{l+1}}
(W-D1: a single formal cell, b₀ = π^{u₁+u₁′}), stage 2 L-NORM-seeds each
stage-1 exit cofactor with every d-cell (c_D, j⃗D) of Ĉ_m and reduces
again; two-exit terminals are the Q¹ cells. Path counters (WMULTDCX† S1):
π_l = promotion edges into level l (π₀ := 0), r = corrections at
reduction level m−1, dmp_l = dump mass received at level l (correction
dumps a_{d,l}, +1 at l = 0 per Φ₀Y-edge, including the seeding's),
Y₂ ∈ {0,1} = the stage-2 seeding Φ₀Y-flag, CE = the correction-edge
multiset (i_c, k_c, a⃗_c, Y_c), junk = the number of π-junk/Φ₀Y-junk
edges, X(C) = the number of π-junk edges. Pools/carries (WMULTDCX S6.1
law side): t_l := σ_l + s_l(u_l), pool_l = t_l + c_{l−1},
c_l = ⌊pool_l/e_{l−1}⌋, ρ_l = pool_l − e_{l−1}c_l (c₀ := 0);
D := t_m, k := 2e_{m−1} − D; λ̂ := λ + λ′ + γ_{m+1} − 2·w_mΦ_m;
u₀ := (u₁ − s₁(u₁)h₀)/e₀. Hypothesis names as in WMULTDCX†/EMPTY†:
(H1) TRACK, (H2) g_{m−1} = 1, (H3) interior g ≡ 1 (g₀ FREE), (STK) the
stage-1 stock clause.

## S1. THE QUANTUM TABLE — Δ ∈ ℤ^{1+m} per S2.2 edge type, assembled fresh

**The extended exponent vector.** For a cell C = b·∏Φ_l^{j_l} put

    J(C) := ( w₀(b_C) ; j₀(C), j₁(C), …, j_{m−1}(C) ) ∈ ℤ^{1+m},

coordinate −1 (the π-coordinate = the coefficient valuation) prepended to
the m level coordinates. e⃗_l denotes the level-l unit vector; the
π-coordinate's unit vector is written e⃗_{−1}.

**The table.** One row per [RMG] S2.2 child type (+ the two stage rows of
T²). The LEVEL BLOCK of every row is EXACT (the S2.2 moves are exact
exponent arithmetic); the π-COORDINATE is exact on main/L rows and a
LOWER BOUND on junk rows (L-NORM(b)/(c) are one-sided) — the two blocks
are typed separately throughout (the pass-9 S2 hygiene warning). The
`line` column is the derived value λ_E·Δ (see S2 face E); `res` is the
K₀-residue action on the normalized coefficient residue b̄ := res(b/π^{w₀(b)});
`sgn` the tree sign.

| # | edge ([RMG] S2.2 cite) | Δ₋₁ (π-coord) | Δ_lev (level block, exact) | sgn | res | λ_E·Δ (line) |
|---|---|---|---|---|---|---|
| P_i | promotion at level i ≤ m−2 (S2.2 "promotion child": j_i −= P_i, j_{i+1} += 1, **b unchanged**) | 0 (exact) | −P_i·e⃗_i + e⃗_{i+1} | + | ×1 | +q_{i+1} > 0 (L-LINE(i)) |
| X_m | Φ_m-exit (S2.2: cofactor leaves the tree, b unchanged) | 0 (exact) | −P_{m−1}·e⃗_{m−1} | + | ×1 | −w_mΦ_m (L-LINE(i) exit clause) |
| C^L_{i,k,d} | correction main (L-)child, reduction level i, index k < g_i, digit cell d = (c_d, a⃗_d) of C_k^{(i)} (S2.2 "correction children" + L-NORM(a)) | +w₀(c_d) (EXACT, L-NORM(a); never absent) | −(P_i − e_ik)·e⃗_i + Σ_{l<i} a_{d,l}·e⃗_l | − | ×c̄_d ≠ 0 (L-NORM(a), K₀ a field) | 0 (EXACT — L-LINE(ii): correction-main is line-null) |
| C^X_{i,k,d} | correction π-junk child (L-NORM(b)) | ≥ w₀(c_d) + 1 | same as C^L | − | — | ≥ +E_m (L-LINE(iii)) |
| C^Y_{i,k,d} | correction Φ₀Y-junk child (L-NORM(c); d₀ ≥ 2 only, identically absent at d₀ = 1) | ≥ w₀(c_d) | C^L's + e⃗₀ | − | — | ≥ +Γ₀ (L-LINE(iii)) |
| S^L_D | stage-2 seeding, L-child of b·c_D at d-cell (c_D, j⃗D) (WMULTDCX† S1 seeding = the same L-NORM split; d-cells reduced, ON-LINE at γ_{m+1}, on-grid — [RMG] S2.1 (Ĉ1)–(Ĉ3)) | +w₀(c_D) (EXACT) | +j⃗D | + | ×c̄_D ≠ 0 | +γ_{m+1} (EXACT: E_m·w₀(c_D) + Σ jD_l·Γ_l = line(D) = γ_{m+1}) |
| S^X_D | seeding π-junk child | ≥ w₀(c_D) + 1 | +j⃗D | + | — | ≥ γ_{m+1} + E_m |
| S^Y_D | seeding Φ₀Y-junk child (d₀ ≥ 2 only) | ≥ w₀(c_D) | +j⃗D + e⃗₀ | + | — | ≥ γ_{m+1} + Γ₀ |

At i = 0 the correction digit is the single coefficient cell
C_k^{(0)} = lift(ψ₀,k)·π^{(g₀−k)h₀} with w₀(c_d) = (g₀−k)h₀ and a⃗_d = ()
([RMG] S2.2's i = 0 clause verbatim); at g₀ = 1 this is w₀ = h₀ ≥ 1 —
the i = 0 anchor of SDY-L1's floor.

**Row provenance (the freshness audit trail).** Level blocks: the S2.2
child inventory sentences quoted in each row. π-coordinate: L-NORM(a)
("the L-child π^w·lift(b̄c̄) has w₀ EXACTLY w and normalized residue
b̄·c̄, which is NEVER zero"), L-NORM(b) ("the π-junk child π^{w+1}X̂ has
w₀ ≥ w + 1"), L-NORM(c) ("the Φ₀Y-junk child π^w·Ŷ at exponent j₀ + 1
has w₀ ≥ w", absent identically at d₀ = 1); promotions/exits move b not
at all (S2.2: "b unchanged"). Line column: L-LINE(i)/(ii)/(iii) verbatim
plus, for the seed rows, the (Ĉ1)–(Ĉ3) on-line certificate. No row is
copied from EMPTY†/SURVDISJ†/SDYJ†/WMULTDCX† — those notes' displays
reappear only in S3 as audit targets.

## S2. THEOREM LED-Λ (the graded path ledger)

**THEOREM LED-Λ.** Let π be any root-to-terminal path of the [RMG] S2.2
tree on T² (stage-1 seed the W-D1 formal cell J(seed) = (u₁+u₁′; σ⃗);
stage-2 arrival = the seeding row S^{L/X/Y}_D of the table). Then:

**(A1) [the exact level lattice].** The level block telescopes EXACTLY,
edge by edge, with the S1 table's Δ_lev:

    j⃗(C)  =  σ⃗  +  Σ_{edges e ∈ π} Δ_lev(e)      (in ℤ^m, every path,
                                                     every child type).

Consequently, for EVERY weight vector λ⃗ ∈ ℚ^m, λ⃗·j⃗(C) = λ⃗·σ⃗ +
Σ_e λ⃗·Δ_lev(e) — an exact identity, no hypothesis.

**(A2) [the π-coordinate, one-sided].** With Δ₋₁^floor(e) := the S1
table's π-column floor (0 on P/X_m rows; w₀(c_d) on C^L; w₀(c_d)+1 on
C^X; w₀(c_d) on C^Y; w₀(c_D), w₀(c_D)+1, w₀(c_D) on S^{L/X/Y}):

    w₀(b_C)  ≥  (u₁ + u₁′)  +  Σ_{e ∈ π} Δ₋₁^floor(e),

with EQUALITY iff the path is junk-free (every split rode its L-child);
each junk edge's excess over its floor is ≥ 0, and the π-junk floors
alone give w₀(b_C) ≥ (u₁+u₁′) + Σ_{L,S} w₀(c) + X(C).

**(A3) [weight functionals].** For λ = (λ₋₁; λ⃗) ∈ ℚ^{1+m} with
λ₋₁ ≥ 0: λ·J(C) ≥ λ₋₁·[(u₁+u₁′) + Σ Δ₋₁^floor] + λ⃗·[σ⃗ + Σ Δ_lev],
equality on junk-free paths; at λ₋₁ = 0 the ≥ is an exact = for every
path. (The two blocks stay typed apart: equalities live in the level
lattice, the inequality lives in the π-coordinate ALONE.)

**(B) [the five faces].** The five weight functionals

    λ_A := (0; W₀, …, W_{m−2}, 0),  W_l := 1/(P_l·P_{l+1}⋯P_{m−2}), W_{m−1} := 1
    λ_B := (0; E₀, E₁, …, E_{m−1})
    λ_C := (0; 0, …, 0, 1)                      (the top indicator δ_{l,m−1})
    λ_D := (1; 0, …, 0)
    λ_E := (E_m; Γ₀, …, Γ_{m−1})                (the line functional)

evaluate on the table rows as follows (each entry is λ·Δ, computed from
the S1 table by the displayed arithmetic; junk rows inherit the ≥ from
(A2) exactly when λ₋₁ > 0 or the line column is consulted):

| face | P_i, i ≤ m−3 | P_{m−2} | X_m | C^{L/X/Y}_{i,k,d}, i ≤ m−2 | C^{L/X/Y}_{m−1,k,d} | S^{L/X/Y}_D |
|---|---|---|---|---|---|---|
| λ_A | 0 (**promotion-null**: W_{i+1} − P_iW_i = 0) | −1 (P_{m−2}W_{m−2} = 1, top coord 0-weighted) | 0 | Σ_{l<i} a_lW_l − (P_i − e_ik)W_i (+W₀ on Y) | Σ_{l<m−1} a_lW_l (+W₀ on Y) | Σ_{l≤m−2} jD_lW_l (+W₀ on Y) |
| λ_B | −(P_iE_i − E_{i+1}) ≤ 0 (**promotion loss**, = 0 iff g_i = 1) | −(P_{m−2}E_{m−2} − E_{m−1}) | −P_{m−1}E_{m−1} | −defc_c − Y_c·0 [see below] | −defc_c | M(j⃗D) (+1 on Y) |
| λ_C | 0 | +1 | −P_{m−1} | 0 | −(P_{m−1} − e_{m−1}k) | jD_{m−1} |
| λ_D | 0 | 0 | 0 | w₀(c_d) / ≥ w₀(c_d)+1 / ≥ w₀(c_d) | same | w₀(c_D) / ≥ +1 / ≥ +0 |
| λ_E | +q_{i+1} | +q_{m−1} | −w_mΦ_m | 0 / ≥ E_m / ≥ Γ₀ | same | γ_{m+1} / ≥ +E_m / ≥ +Γ₀ (over γ_{m+1}) |

Here defc_c := (P_{i_c} − e_{i_c}k_c)·E_{i_c} − Σ_{l<i_c} a_{c,l}E_l − Y_c
(SURVDISJ†'s deficit, re-derived: it is EXACTLY −λ_B·Δ_lev(correction)
− Y_c·E₀ with E₀ = 1, i.e. the correction rows' λ_B-value is −defc_c once
the Y-child's +e⃗₀ is folded in). M(x⃗) := Σ x_lE_l = λ_B·x⃗.

**(C) [the residue face].** On a junk-free path the terminal normalized
residue is the product of the seed residue and the consumed digit
residues, and the sign is (−1)^{#corrections}:

    b̄_C = b̄₀ · c̄_D · ∏_{c ∈ CE} c̄_{d_c}   in K₀ (b̄₀ = 1),
    sgn(C) = (−1)^{|CE|},

each factor nonzero (L-NORM(a)) — the substrate that SURV†'s S-L1 and
SURVK2's K2-L4 instantiate.

*Proof.* (A1): each table row's Δ_lev IS the [RMG] S2.2 move (quoted in
S1, row by row); induct along the path. (A2): the π-column of S1 is
L-NORM(a)/(b)/(c) per edge (promotions and exits carry b UNCHANGED —
S2.2); chain the per-edge (in)equalities; the junk-free case chains
L-NORM(a) equalities only. (A3): linear combination of (A1) and (A2),
sign-safe at λ₋₁ ≥ 0. (B): evaluation arithmetic on the table —
λ_A: W_{i+1} = P_iW_i kills every promotion below the top and
P_{m−2}W_{m−2} = W_{m−1} = 1 prices the top promotion at −1 in the
0-weighted top coordinate's stead; λ_B: promotion into level l+1 trades
P_lE_l at level l for E_{l+1} one level up; λ_C: only level-(m−1)
entries survive; λ_D: the π-column verbatim; λ_E: the line column,
proved row-wise in S1 from L-LINE. (C): L-NORM(a) ("normalized residue
b̄·c̄, never zero") chained along the path's L-splits (the only
coefficient-mutating edges); each correction edge flips the tree sign
([RMG] S2.2's sign −), promotions/exits/seeding do not. ∎

**Remark (what the theorem is).** LED-Λ is W-D3's LED_l lifted to the
extended lattice and stated ONCE for all weight vectors: LED_l itself is
the coordinate face λ = (0; e⃗_l). The five named faces below are the
five weightings the closure program actually used, each currently proved
by its own telescope in its own note.

## S3. THE FIVE FACES vs THE COMMITTED DISPLAYS — byte-fidelity audits

Protocol per face: (i) the committed display, QUOTED BYTE-VERBATIM from
the committed note (fenced); (ii) the EXACT specialization of LED-Λ;
(iii) the derivation; (iv) verdict MATCH or finding. Any mismatch is a
FINDING, never a silent fix.

### S3.A Face λ_A = the promotion-null face ⟹ E-L1 (EMPTY† S2)

Committed display (EMPTY_PROOF_2026-08-08.md S2, byte-verbatim):

    **Lemma E-L1.**  Along any root-to-terminal path of T², with C the
    terminal state and ccons_l := Σ_{(i,k,·,·)∈CE, i=l} (P_l − e_lk) the
    correction consumption at level l:

        π_{m−1}  =  Σ_{l=0}^{m−2} W_l · ( σ_{l+1} + jD_l + dmp_l − ccons_l − j_l(C) ).

Specialization: λ = λ_A = (0; W₀,…,W_{m−2}, 0) in LED-Λ(A1)/(B), ANY
root-to-terminal path of T², no hypothesis (E-L1 is scope-free, as its
note says). Derivation: (A1) at λ_A reads λ_A·j⃗(C) = λ_A·σ⃗ + Σ λ_A·Δ.
By the (B) row: promotions below the top contribute 0 (promotion-null),
each promotion into level m−1 contributes −1 (total −π_{m−1}), exits 0,
a correction at level i contributes (Σ_{l<i} a_lW_l + Y_cW₀) −
(P_i − e_ik)W_i·[i ≤ m−2] — i.e. its dumps' W-value received minus its
consumption's W-value paid — and the seeding contributes
Σ_{l≤m−2} jD_lW_l + Y₂W₀. Collecting the received dump masses as
Σ W_l·dmp_l (the note's dmp_l INCLUDES the Y-units at l = 0 — both
conventions verbatim from W-D3) and the paid consumptions as
Σ W_l·ccons_l, and moving λ_A·j⃗(C) = Σ_{l≤m−2} W_l·j_l(C) across:

    π_{m−1} = Σ_{l=0}^{m−2} W_l·(σ_{l+1} + jD_l + dmp_l − ccons_l − j_l(C)) —

the display on the nose, term for term (σ_{l+1} = the stage-1 seed at
level l; jD_l = the d-cell exponent; W_l the same weights, W_{m−1} = 1
entering only through P_{m−2}W_{m−2} = 1). **Verdict: MATCH (exact, same
weights, same term grouping).** Machine: face A of the runner (LAM-A).

### S3.B Face λ_B = the mass face ⟹ SD-L2, SD-L1's bound, and (★) (SURVDISJ† S2)

Committed displays (SURVDISJ_PROOF_2026-08-08.md S2, byte-verbatim):

    **Lemma SD-L2 (the E-weighted mass ledger; any g₀).**  For every
    two-exit terminal cell C of T², with seed d-cell exponent vector
    j⃗(D), Y₂(C) ∈ {0,1} the stage-2 seeding Φ₀Y-flag, CE(C) its
    correction-edge multiset (each c at reduction level i_c, index k_c,
    dump vector a⃗_c, Φ₀Y-flag Y_c ∈ {0,1}):

        M(j⃗(C)) = M(σ⃗) + M(j⃗(D)) + Y₂(C)
                   − 2·P_{m−1}E_{m−1}
                   − Σ_{l=1}^{m−1} π_l·(P_{l−1}E_{l−1} − E_l)
                   − Σ_{c ∈ CE(C)} defc_c ,

        defc_c := (P_{i_c} − e_{i_c}k_c)·E_{i_c} − Σ_{l<i_c} a_{c,l}E_l − Y_c .

and, at (H2) ∧ (H3) ∧ g₀ = 1:

        defc_c ≥ E_{i_c+1} − E_{i_c} + 1 − Y_c ≥ 0 ;                 [SD-L1]

        (★)      Σ_{c ∈ CE(C)} defc_c  =  Y₂(C)  ∈ {0, 1}.           [at ĵ]

Specialization: λ = λ_B = (0; E₀,…,E_{m−1}) in LED-Λ(A1), two-exit
terminal paths, ANY g₀. Derivation: (A1) at λ_B with the (B) row —
promotions into level l cost P_{l−1}E_{l−1} − E_l each, the two exits
cost P_{m−1}E_{m−1} each, a correction's λ_B·Δ (with its Y-unit at
E₀ = 1) is −defc_c by the (B)-row identity, the seeding adds
M(j⃗D) + Y₂ — SD-L2 verbatim. SD-L1's bound is the table's reduced-dump
pin (a_{d,l} ≤ P_l − 1, [RMG] S2.2) fed through micro-move M-1 (S4):
at g₀ = 1 ∧ (H3), P = e everywhere and k_c = 0, so
defc = E_{i+1} − Σ a_lE_l − Y ≥ E_{i+1} − (E_i − 1) − Y. (★) is NOT a
new face fact: it is SD-L2 evaluated at the cascade slot ĵ against the
pool telescope (SURVDISJ† S2's own three-line computation, consumed);
the runner re-checks it as a face-B corollary (LAM-BSTAR). **Verdict:
MATCH (SD-L2 exact at any g₀; SD-L1's bound re-derived from the table +
M-1; (★) re-derived as the slot evaluation).** Machine: LAM-B, LAM-B1,
LAM-BSTAR.

### S3.C Face λ_C = the top-indicator face ⟹ W-D4 (WMULTDCX† S4)

Committed display (WMULTDCX_2026-08-08.md S4, byte-verbatim):

    **Proposition W-D4.**  Assume (H2).  Then for EVERY Q¹ cell of T² (live or
    dead row alike):

        π_{m−1} = k + e_{m−1}·r + j_{m−1}(cell)   ≥   k ,

    r = its path's correction count at reduction level m−1.

Specialization: λ = λ_C = (0; 0,…,0,1) in LED-Λ(A1), two-exit terminals,
(H2) g_{m−1} = 1 entering ONLY through the seed pin jD_{m−1} = s_m(u_m)
(W-D2(i), consumed) and k_c = 0 at level m−1. Derivation: (A1) at λ_C:
j_{m−1}(C) = σ_m + jD_{m−1} + π_{m−1} − 2P_{m−1} − r·P_{m−1} (each top
correction consumes P_{m−1} − e_{m−1}·0 = e_{m−1} = P_{m−1} at (H2);
corrections dump strictly below level m−1, so no dump term — the table's
C-rows have a_{d,l} only at l < i). With jD_{m−1} = s_m(u_m),
P_{m−1} = e_{m−1}, D = σ_m + s_m(u_m) and k = 2e_{m−1} − D:

    π_{m−1} = j_{m−1}(C) + (2 + r)e_{m−1} − D = k + e_{m−1}·r + j_{m−1}(C) ≥ k

(j_{m−1}(C) ≥ 0 — cells). **Verdict: MATCH (W-D4 IS the top-indicator
face; the ≥ k threshold is the face identity plus nonnegativity of the
terminal coordinate).** Machine: LAM-C.

### S3.D Face λ_D = the (1; 0⃗) valuation face ⟹ SDY-L2's additive spine (SDYJ† S3)

Committed display (SDYJ_PROOF_2026-08-08.md S3, byte-verbatim):

    **Lemma SDY-L2 (path valuation superadditivity).**  On TRACK,
    (H1)–(H3), g₀ = 1, any d₀: every two-exit terminal cell C of T²
    satisfies

        w₀(b_C)  ≥  (u₁ + u₁′) + u₀ + Σ_{c ∈ CE(C)} w₀(c_{d_c}) + X(C)
                 =  ŵ + Σ_{c ∈ CE(C)} w₀(c_{d_c}) + X(C) ,

    where X(C) := the number of π-junk edges on C's path, and c_{d_c} is
    the digit cell consumed by correction c.  Equality holds on junk-free
    paths (then every split takes its L-child and each step is EXACT).

Specialization: λ = λ_D = (1; 0⃗) in LED-Λ(A2)/(A3), two-exit terminals,
at (H3) ∧ g₀ = 1 where W-D2(iii) pins w₀(c_D) = u₀ (any d₀). Derivation:
(A2) verbatim gives the GENERAL face — w₀(b_C) ≥ (u₁+u₁′) + w₀(c_D) +
Σ_c w₀(c_{d_c}) + X(C), equality iff junk-free, at ANY g₀ (the ledger
face is g-free; at g₀ ≥ 2 the seed term is w₀(c_D) = u₀ − t·h₀ for the
t-family d-cell, W-D2(iv)) — and the committed display is its
w₀(c_D) = u₀ instance. Note the committed display's Y-accounting rides
Δ₋₁ ≥ +0 (the Y-child gains exponent mass at level 0, NOT valuation —
SDY-L2's own parenthetical), which is exactly the table's C^Y/S^Y floor.
The FLOOR w₀(c_{d_c}) ≥ 1 (SDY-L1) is NOT subsumed — it is digit
CONTENT (the forced v-chain + (INV) + integrality), a consumer of the
ledger, fenced in S6. **Verdict: MATCH (the committed display = the
face at the W-D2(iii) pin; the general-g₀ form is the face proper —
STRICTLY more general, displayed here as the ledger's own statement).**
Machine: LAM-D (checked at EVERY g₀ on the rosters, with the seed term
read off the actual consumed d-cell).

### S3.E Face λ_E = the line face ⟹ W-D5's floor (WMULTDCX† S5) + L-MONO ([RMG] S3.2)

Committed displays, byte-verbatim. WMULTDCX_2026-08-08.md S5:

    **Proposition W-D5.**  For every Q¹ cell, with q_l := h_l·∏_{l<t<m}e_t
    (the L-LINE(i) promotion quantum into level l) and
    λ̂ := λ + λ′ + γ_{m+1} − 2·w_mΦ_m:

        line(cell) = λ̂ + Σ_{l=1}^{m−1} π_l·q_l + (junk gains),

    junk gains ≥ 0 with equality iff the path took no π-junk/Φ₀Y-junk edge.

RMENGINE_2026-08-08.md S3.2 (ACCEPTED):

    **Corollary L-MONO (line monotonicity).** Along every tree edge,
    line(child) ≥ line(parent), with equality exactly on correction-main
    children; promotions rise by the exact (i)-quantum.

Specialization: λ = λ_E = (E_m; Γ₀,…,Γ_{m−1}) — note λ_E·J(C) = line(C)
BY DEFINITION of the line — in LED-Λ(A3), λ₋₁ = E_m > 0. Derivation:
the (B) row for λ_E: seed value λ_E·J(seed) = E_m(u₁+u₁′) + Σ σ_{l+1}Γ_l
= line(a) + line(a′) = λ + λ′ (W-D1); the seeding adds γ_{m+1} exactly
(+ junk floors); the two exits −2w_mΦ_m; promotions +q_l each;
correction-mains 0; junk ≥ E_m (π) / ≥ Γ₀ (Y) — summing gives
line(cell) = λ̂ + Σ π_l q_l + (junk gains), junk gains ≥ 0 with equality
iff junk-free, and in fact ≥ X(C)·E_m + (#Y-edges)·Γ₀ (the table's
sharper slack, machine-checked as LAM-E's second clause). W-D5's second
display (w_m(Q¹) ≥ λ̂ + max(k,0)·h_{m−1}) rides this face + face C
(π_{m−1} ≥ k) + q_{m−1} = h_{m−1} + the [RMG] exit-cofactor structural
remark — consumed, not re-derived (it needs w_m of a SUM, an ultrametric
step outside the per-path ledger; fenced in S6). L-MONO is the
positivity/vanishing pattern of the λ_E row of the table restricted to
in-tree edges (promotion +q > 0, correction-main = 0, junk ≥ E_m, Γ₀
> 0), i.e. the face's per-edge signs — the [RMG] display re-read as the
line column of ONE table. **Verdict: MATCH on W-D5's first display
(exact, same λ̂, same quanta, same junk clause); MATCH on L-MONO's edge
signs (its "every cell reachable ≥ λ + γ_{m+1}" consequence = the face
telescope with all in-tree entries ≥ 0). W-D5's w_m-floor display:
CONSUMED, not subsumed (ultrametric step) — no fidelity claim made.**
Machine: LAM-E.

## S4. POOL-UNROLL and the micro-moves — displayed ONCE (the three-site fold)

### S4.1 Lemma POOL-UNROLL (the carry chain and the pooled line value)

With t_l := σ_l + s_l(u_l) (1 ≤ l ≤ m−1), the carry chain and remainders

    c₀ := 0,   c_l := ⌊(t_l + c_{l−1})/e_{l−1}⌋,   ρ_l := t_l + c_{l−1} − e_{l−1}·c_l,

and the literal-e weights w_{m−1} := 1, w_l := w_{l+1}/e_{l+1}·(…) — i.e.
w_l := 1/(e_l·e_{l+1}⋯e_{m−2}) — the following hold by pure arithmetic of
the chain (no tree, no hypothesis):

    (i)  [the E-L4 unroll]   c_{m−1} = Σ_{l=1}^{m−1} (t_l − ρ_l)·w_{l−1},
         and Σ_{l=1}^{m−1} ρ_l·w_{l−1} ≤ Σ (e_{l−1}−1)·w_{l−1} = 1 − w₀;
    (ii) [the pooled line value] β̂ := λ̂ + Σ_{l=1}^{m−1} c_l·q_l is, on
         (H3) ∧ g₀ = 1 ∧ (STK) ∧ c_{m−1} ≥ k rows, the line of the
         cascade cell: the junk-free correction-free principal path has
         π_l = c_l and hits β̂ exactly — face E at π⃗ = c⃗ (this is the
         ONLY tree input: W-D7(ii)'s cascade existence, consumed).

*Proof.* (i): c_l·w_l−… — unroll c_l = (t_l + c_{l−1} − ρ_l)/e_{l−1}
top-down, exactly EMPTY† E-L4's two lines: multiply the l-th relation by
w_{l−1} and sum; the carry terms telescope ((e_{l−1}−1)w_{l−1} =
w_l − w_{l−1}, micro-move M-1). (ii): face E of LED-Λ on the cascade
path (promotion count c_l into level l, zero junk, zero corrections,
seed the principal d-cell) — the three consolidated sites below. ∎

**The three sites this folds (all currently prove/recompute it):**
(1) EMPTY† E-L4/E-L5 (the unroll + the c⁺-perturbation of the same
chain); (2) SURV† S-L1's line clause — byte-verbatim there:

        line:        β̂ := λ̂ + Σ_{l=1}^{m−1} c_l·q_l    (exactly);

(3) the SDYJ† Y-r1 de-tautologized runner formula (sdyj_checks_v2.py:
"betahat = lamhat + sum_{l=1}^{m-1} c_l * q_l", recomputed independently
from the pool arithmetic). The consolidation claim is DISPLAY-level:
one lemma, three citation sites at the next fold; no committed text is
touched here.

### S4.2 The micro-moves (S6.8 of the pass; two-line lemmas, stated once)

**M-1 (mixed-radix telescope).** For any weights with x_{l+1} = d_l·x_l
(d_l ≥ 1 integers): Σ_{l<i} (d_l − 1)·x_l = x_i − x₀. Instances: the
W-form Σ_{l<i}(P_l − 1)W_l = W_i − W₀ (EMPTY† E-L2's proof line), the
E-form Σ_{l<i}(e_l − 1)E_l = E_i − 1 (SURVDISJ† SD-L1's proof line —
"mixed-radix telescope" verbatim there), the w-form
Σ(e_{l−1} − 1)w_{l−1} = 1 − w₀ (E-L4). *Proof:* (d_l − 1)x_l =
x_{l+1} − x_l; telescope. ∎

**M-2 (INT-FLOOR).** If x ∈ ℤ and x > B for some rational B, then
x ≥ ⌊B⌋ + 1. Instances: SDYJ† SDY-L1's (INV) chain step ("v_{l−1} ∈ ℤ
strictly above the integer e_{l−2}γ_{l−1} gives (INV_{l−1}) —
integrality is load-bearing") and EMPTY† E-L5's level-0 floor
arithmetic. Stated once so the eventual write-up cites a name instead
of re-proving the move inline. ∎

**M-3 (forced chain at g = 1).** In the [RMG] S3.1 λ-chain of a REDUCED
on-grid cell, the level-l freedom is t_l ∈ [0, g_{l−1}) (window
arithmetic: 0 ≤ j_{l−1} ≤ e_{l−1}g_{l−1} − 1 and 0 ≤ s_l < e_{l−1} pin
−1 < t_l < g_{l−1}); at g_{l−1} = 1 this forces t_l = 0 — the chain is
FORCED. Instances: SDYJ† SDY-L1(a) (the forced v-chain), WMULTDCX†
W-D2(ii)/(iii) (the principal d-cell forcing), SURV† S-L1's uniqueness
clause. Per pass-9 S3, this move is WINDOW-CALC's g = 1 degeneration —
displayed here as the shared two-line kernel, NOT as a window-calculus
statement (that is unit S7.U2's charge, not this note's). ∎

## S5. MACHINE BRACKET — ledger_lambda_checks.py (the non-textual leg)

**Runner:** `verification/openmath/ledger_lambda_checks.py`, committed at
commit 1 of the two-commit seal WITH this note; predictions SEALED below
BEFORE the battery runs; verdict appended at commit 2 from the artifacts
(`ledger_lambda_checks_output.txt`, `ledger_lambda_checks_results.json`).

**Design.** ONE walk-replay: rows are traced with the committed recording
walk (`survk2_derive_checks.walk_rec`, byte-pinned) on top of the
committed engines routed through `engine_ext.install()` (the standing
rule; `agreement_gate()` re-run in-unit, counts reported as LAM-GATE).
For every two-exit terminal the runner REPLAYS the recorded edge list
through ITS OWN fresh implementation of the S1 quantum table (fresh
γ/Γ/E/W/q arithmetic from the S0.1 recursion — LAM-GAM cross-ties it to
the engine's constants) and computes ALL FIVE faces simultaneously,
per-edge in the level lattice, per-path in the π-coordinate (the
recorded flags resolve X vs Y; the walk does not label L vs X per edge,
so the π-face is checked in its per-path form — exactly the form the
committed displays take). Stage sums are tied to the canonical divisions
(LAM-CONS), the strong external anchor.

**Rosters (BOTH committed rosters, as charged).**
Phase W: `wmultdcx_stress.ROSTER` (20 towers) under the WMULTDCX battery
pid-key selection, replicated verbatim from the committed
`wmultdcx_derive_checks.py` (caps 40/14 — the 412-row selection).
Phase SD: the SURVDISJ rosters `PX_ROSTER` + `SD_ROSTER` (16 towers,
copied verbatim) under the committed fresh-tower live-row selection
(kdef ≤ c_top, per-stratum caps 12/6).
Phase YJ: the SDYJ rosters `T3_COMMITTED` + `FRESH` (15 towers, copied
verbatim) under the SDYJ live-clause selection (uncapped).

**Families and SEALED PREDICTIONS (violation counts; any family whose
observed count differs from its prediction is RED):**

    LAM-PIN    md5 pins on the consumed artifacts.            PREDICTED 0.
    LAM-GATE   engine_ext.agreement_gate() re-run in-unit.    PREDICTED 0
               (counts reported).
    LAM-GAM    fresh γ/Γ_l/E_l/w_mΦ_m/q_l recursion == the engine's
               constants; fresh line() == E.line on every terminal.
                                                              PREDICTED 0.
    LAM-CONS   stage-1 sum == E1IH; stage-2 sum == Q¹ (canonical
               divisions).                                    PREDICTED 0.
    LAM-LAT    per-edge replay of Δ_lev == terminal j⃗ AND the replayed
               π/dmp/ccons/exit counters == the walk's own counters
               (the exact level-lattice telescope, LED-Λ(A1)). PREDICTED 0.
    LAM-A      face λ_A == the E-L1 display, per terminal.    PREDICTED 0.
    LAM-B      face λ_B == the SD-L2 display, per terminal.   PREDICTED 0.
    LAM-B1     SD-L1's deficit bound + equality analysis on all-g-1
               rows.                                          PREDICTED 0.
    LAM-BSTAR  (★) Σ defc = Y₂ on cascade-slot terminals of all-g-1
               (STK ∧ c ≥ k) rows.                            PREDICTED 0.
    LAM-C      face λ_C == the W-D4 display (+ the ≥ k threshold + the
               (H2) seed pin jD_{m−1} = s_m(u_m)).            PREDICTED 0.
    LAM-D      face λ_D: w₀(b_C) ≥ w₀(b₀) + w₀(c_D) + Σ w₀(c_{d_c})
               + X(C) at EVERY g₀ (seed term read off the actual
               consumed d-cell), equality iff junk-free.      PREDICTED 0.
    LAM-E      face λ_E: junk-free line EQUALITY at λ̂ + Σ π_l q_l;
               always ≥ that + X·E_m + (#Y)·Γ₀ (the table's slack
               floors).                                       PREDICTED 0.
    LAM-R      residue face on junk-free terminals: b̄_C = b̄₀·c̄_D·∏c̄_d
               in K₀, every factor nonzero; sign = (−1)^{|CE|}.
                                                              PREDICTED 0.
    LAM-POOL   POOL-UNROLL: fresh c/ρ chain == WS.pools_of; the E-L4
               unroll identity (exact Fractions) on every traced row;
               β̂ = λ̂ + Σ c_l q_l == the cascade cell's line (+ ŵ =
               u₁+u₁′+u₀, residue ≠ 0 — the S-L1 shadow) on every
               all-g-1 (STK ∧ c ≥ k) row with the cascade realized.
                                                              PREDICTED 0.
    LAM-MICRO  M-1 (three instances, per tower, exact Fractions).
                                                              PREDICTED 0.
    HARNESS    engine-internal violations harvested from the consumed
               modules.                                       PREDICTED 0.

**Mutation controls (the CTRL-TEL0 genre: a broken quantum table must
fire on every face; run on the designated sub-roster W3DEEP + W3G2B +
YJ2F; each control must fire ≥ 1 or the battery is RED):**

    MUT-LAT   one corrupted Δ entry (level-0 promotion consumes P₀ − 1)
              must break the lattice replay.                  FIRES ≥ 1.
    MUT-A     the l = 0 term dropped from the face-A telescope (the
              CTRL-TEL0 precedent verbatim).                  FIRES ≥ 1.
    MUT-B     the exit mass corrupted (2·P_{m−1}E_{m−1} − 1).  FIRES ≥ 1
              (every two-exit terminal).
    MUT-C     the face-C identity offset by +1.               FIRES ≥ 1
              (every terminal).
    MUT-D     the junk-free π-coordinate equality offset by +1.
                                                              FIRES ≥ 1.
    MUT-E     λ̂ corrupted by +1 in the face-E equality.       FIRES ≥ 1.
    MUT-R     the expected residue product shifted by +1 in K₀.
                                                              FIRES ≥ 1.

**[VERDICT — appended at commit 2 from the committed artifacts
(`ledger_lambda_checks_output.txt` / `ledger_lambda_checks_results.json`;
one runner repair between shakedown and seal is on record: the shakedown
itself caught a double-counted u₀ in the face-D floor (base included u₀
AND the seed term w₀(c_D), which coincide at g₀ = 1) — fixed BEFORE the
seal commit; the sealed text is the fixed runner.]**

**ALL GREEN — 0 violations across all 17 families; every sealed
prediction met.** The battery: **876 rows traced** (phase W: **412 —
the committed WMULTDCX battery selection reproduced EXACTLY**, 20/20
towers; phase SD: 16/16 SURVDISJ-roster towers; phase YJ: 15/15
SDYJ-roster towers), **2,338 two-exit Q¹ cells**, all five faces checked
on every one (junk-free: 2,179 — the residue face verified on ALL
2,179); (★) verified on 497 cascade-slot cells; POOL-UNROLL (fresh
carry chain + E-L4 unroll + β̂ = λ̂ + Σ c_l q_l + ŵ + residue ≠ 0) on
486 cascade rows; LAM-GAM/LAM-MICRO on all 72 tower constructions
(incl. mutation re-traces). The agreement gate re-ran GREEN in-unit:
**0 violations (pairs=60, irr=158, cert=1181, pick=30)** — the standing
rule's report. Mutation controls, ALL FIRING on their target faces
(the CTRL-TEL0 genre has teeth on every face): MUT-LAT 106 ·
MUT-A 106 · MUT-B 113 · MUT-C 113 · MUT-D 98 · MUT-E 211 · MUT-R 98.
Elapsed 25.0s; deterministic, exact arithmetic.

## S6. WHAT LED-Λ DOES NOT SUBSUME (the honest fences, from pass-9 S2)

* **K2-L1's window normal form** — event-ORDER content (arrival-driven
  runs, complete drains); the ledger is order-blind by construction.
  That is unit S7.U2's (WINDOW-CALC's) charge.
* **The residue ALGEBRA** — face (C) carries the PRODUCT STRUCTURE only.
  S-L1's nonvanishing uses it plus field arithmetic; the K2-THM-A
  dichotomy, SD-L6/SD-L7's netting, and every cancellation argument are
  consumers, not corollaries.
* **The integrality arguments** — SDY-L1's (INV) chain and E-L5's floor
  chain use M-2 INSIDE digit/pool content the ledger does not carry
  (SDY-L1's v-chain floor w₀(c_d) ≥ 1 is digit content; E-L5's
  c⁺-classification is floor-perturbation content). M-2 names the shared
  move; the lemmas stand.
* **Every hypothesis-dependent step** — (STK), the law clause
  c_{m−1} ≥ k, W-D7's cascade existence, W-D5's w_m-floor (an
  ultrametric step over cell SUMS), E-L2/E-L2h's payment bounds (they
  PRICE the table against the W-weights — consumers of face A, kept in
  EMPTY†), and the theorems E-THM/SD-THM-A/SDY-THM/K2 themselves.
* **E-L1's own machine bracket, and every consuming note's machine
  legs** — decorrelation is deliberate, never redundancy (S6.9 of the
  pass).

## S7. CLAIMS TABLE, dependency line, record

| # | claim | status | rests on |
|---|---|---|---|
| L1 | The S1 quantum table: level blocks exact, π-floors, line column, residue column, per [RMG] S2.2 row | PROVED (assembled fresh; row provenance displayed) | [RMG] S2.2 + L-NORM + L-LINE + (Ĉ1)–(Ĉ3), all ACCEPTED |
| L2 | LED-Λ(A1) exact level-lattice telescope, every path, every λ⃗ | PROVED | L1 + induction |
| L3 | LED-Λ(A2) π-coordinate floor telescope, equality iff junk-free | PROVED | L1 (L-NORM legs) |
| L4 | LED-Λ(A3) weight-functional form (λ₋₁ ≥ 0) | PROVED | L2 + L3 |
| L5 | LED-Λ(B) the five-face evaluation table | PROVED (displayed arithmetic) | L1–L4 |
| L6 | LED-Λ(C) residue face (product + sign, junk-free) | PROVED | L-NORM(a), [RMG] |
| L7 | Face A ⟹ E-L1, byte-fidelity MATCH | PROVED (audit S3.A) | L5; EMPTY† (grade rides) |
| L8 | Face B ⟹ SD-L2 (any g₀) + SD-L1 bound + (★), MATCH | PROVED (audit S3.B) | L5 + M-1; SURVDISJ† |
| L9 | Face C ⟹ W-D4 incl. ≥ k, MATCH | PROVED (audit S3.C) | L5 + W-D2(i)†; WMULTDCX† |
| L10 | Face D ⟹ SDY-L2's spine (committed display = the W-D2(iii) pin of the g-free face), MATCH | PROVED (audit S3.D) | L3; SDYJ†, WMULTDCX† (W-D2) |
| L11 | Face E ⟹ W-D5's first display + L-MONO's edge signs, MATCH; W-D5's w_m-floor consumed NOT subsumed | PROVED (audit S3.E) | L5; WMULTDCX†, [RMG] |
| L12 | POOL-UNROLL (i) unroll identity (ii) β̂ = cascade line; folds E-L4/E-L5-site, S-L1-site, SDYJ-v2-runner-site | PROVED ((ii) consumes W-D7(ii)†) | S4.1 |
| L13 | Micro-moves M-1/M-2/M-3 displayed once with instance lists | PROVED (two-liners) | S4.2 |
| L14 | Machine leg: 17 families + 7 mutation controls on BOTH committed rosters, agreement gate re-run | **ALL GREEN at commit 2** (876 rows / 2,338 cells / 0 violations; all controls fire) | S5 |
| L15 | Non-subsumption fences (window calculus, residue algebra, integrality consumers, hypothesis steps) | DISPLAYED | S6 |
| L16 | Consumption-only: no accepted/committed statement touched; retirement at next fold | FENCE | header |

**Dependency line.** [RMG] (ACCEPTED a0e266c) ⟶ LED-Λ (this note,
attempt) ⟵ consumes W-D1/W-D2/W-D7(ii) from WMULTDCX† (0/2 CLEAN — THE
grade cap) for the T² frame and the cascade; audits against EMPTY† /
SURVDISJ† / SDYJ† / SURV† at their attempt grades. Downstream (design,
not executed here): the definitive Q2 write-up consumes ONE ledger
theorem + one table in place of five telescopes + the triplicated pool
formula; K2-CLOSE (S7.U4), g₀ ≥ 3, and the Lean transcription consume
LED-Λ; the subsumed displays get dated supersession brackets at the
next fold (S7.U6), not here.

— LEDGER-Λ COMPOSE, 2026-08-08 campaign (wallclock 2026-08-04); unit
S7.U1 of synthesis pass 9. Machine verdict ALL GREEN (commit 2).
