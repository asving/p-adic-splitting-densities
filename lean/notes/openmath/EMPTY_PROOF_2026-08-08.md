# (EMPTY-(m+1)) PROVED at attempt grade on (H1)–(H3), g₀ FREE — the weighted path-ledger assembly: the two excess channels cannot fund π_{m−1} ≥ k on any legal path when c_{m−1} < k

Object: the conjecture-grade route displayed at WMULTDCX_2026-08-08.md S9
(the W-r1 positive lead):

    (EMPTY-(m+1)):  on TRACK, (H1)–(H2), c_{m−1} < k := 2e_{m−1} − D
    ⟹  T²(γ,γ′) has NO two-exit path at all (Q¹ has no cells; a
    fortiori Q¹ = 0).

THIS NOTE PROVES IT, with one hypothesis added and displayed: (H3)
(interior g ≡ 1, the instrument class pin of the whole W arc), with **g₀
FREE and d₀ free inside T-scope** — i.e. on the full class where the W-D
layers themselves live.  The general-interior-g residual is boxed (S9,
(EMPTY-gen)); nothing else is left open.  Scope: the [ILN]† S0.1 class
via the RM-GEN S0.1 pin, level m ≥ 2, g_m = 1, uniform in m and in the
characteristic — the proof is class-level arithmetic of the tree, no
instance input.  Date: 2026-08-08 campaign (wallclock 2026-08-04;
composer unit of the W-MULT-DCX arc, the (EMPTY) leg).

**Grade (header summary):** E-L1–E-L7 and the assembled theorem E-THM —
**PROVED at attempt grade** (composed this unit, ZERO hostile passes so
far; every displayed intermediate machine-checked at instance level:
`verification/openmath/empty_derive_checks.py`, 17 verdict families ALL
GREEN — 22,261 terminal states, 54,615 correction edges, 616 traced dead
rows with zero two-exit paths, 1,380 fresh TRACK keys law-censused
clean).  **Grade cap carried from consumption [dagger discipline]: this
note consumes WMULTDCX_2026-08-08.md (W-D0–W-D7) at ATTEMPT grade — that
arc stands at 0/2 CLEAN hostile passes, not accepted — so (EMPTY-(m+1))
CANNOT grade higher than its weakest consumed block until the W arc
closes.**  (SURV-(m+1))(i) [survival] — UNTOUCHED, open.  LAW-DCX-(m+1)
— grade UNCHANGED (m = 1 proved, m ≥ 2 conjecture; see S9/S10).

## S0. Authority, provenance, consumption, and the instrument disclosure

Charge (the W-r1 S9 route display + the orchestrator's composer charge):
prove (EMPTY-(m+1)) via the verified reduction — by W-D4 + W-D6c it
suffices to show that when c_{m−1} < k the two excess channels
(correction dumps; non-principal d-cells) cannot fund π_{m−1} ≥ k on any
legal path — or box the exact blocking obstruction.  The reduction
itself was re-derived VALID by two independent hostile passes (PE2, PE3;
WMULTDCX S11 records).  Outcome: PROVED on (H1)–(H3) with g₀ free; the
only box left is the interior-g ≥ 2 extension (S9), which is OUTSIDE
every battery ever run in this program and outside (H3).

Consumption, all read-only, every block daggered with its standing grade:

* **WMULTDCX_2026-08-08.md (attempt grade, 0/2 CLEAN)**: W-D0 (T² = the
  proof object; T-scope pin (H1) consumed ONLY here), W-D1 (X₀ formal-cell
  identity — no L-NORM split at stage-1 seeding, hence no junk children
  before the first correction), W-D2 (d-cell inventory: top pin at (H2);
  interior principality and the level-0 (iv)-form j₀(D) = s₁(u₁) + t·e₀,
  0 ≤ t < g₀, at (H3)), W-D3 (LED_l — THE input; consumed with its pins:
  terminal-cell machine coverage disclosed there, edge-by-edge proof
  general), W-D4 (top identity π_{m−1} = k + e_{m−1}r + j_{m−1}, (H2)),
  W-D6 (the P-divisor cap; its induction pattern is reused), W-D6c (the
  channel dichotomy that frames the charge).  The (STK) and law-clause
  pins of W-D7 are NOT consumed (this note nowhere needs attainment);
  g₀ = 1 is NOT consumed (unlike W-D7).
* **RMENGINE_2026-08-08.md [RMG], ACCEPTED (round-7 double-clean)**: the
  S2.2 tree and child inventory (correction children: a_{d,l} ≤ P_l − 1
  for l < i, a_{d,l} = 0 for l ≥ i; indices k < g_i with ψ_{i,k} ≠ 0;
  consumption P_i − e_ik = e_i(g_i − k); +1 at l = 0 on the Y-child),
  L-NORM (the normalized split; clause (c): the Φ₀Y-junk child and its
  d₀ = 1 absence, THE mechanism generalized here at E-L6), L-EXACT,
  T-TERM, the S3 line laws (cited only for orientation).
* **[IL3]† DIGIT-SPLIT** through L-NORM: αβ = lift(q(α)q(β)) + πX + Φ₀Y
  with deg < d₀ each; the canonical Y = quo of the primitive product by
  Φ₀ — consumed at E-L6.
* **[ILN]† S4.1 (R1)/WELL-DEF-(n)(ii)/(Ĉ1)–(Ĉ3)** through RM-GEN S2.1
  (the certified Ĉ_m inventory feeding W-D2).

Sealed artifacts (DCX3 a9dd275, stress d3950f2/d774ecb, the derive
battery) are instance evidence and design input only, never proof steps.

**Machine leg of THIS unit:** `verification/openmath/empty_derive_checks.py`
(md5 8fed92402bcffe6e0c536f1f9d847612), output
`empty_derive_checks_output.txt` (ddae400794ce1b25bd332beddd40528d),
results `empty_derive_checks_results.json`
(229a1b1e0c1a93f154bc34e5ce1f5059).  It replicates the sealed battery's
412-row selection VERBATIM (rows 412 / cells 858 / dead 126 reproduced
exactly — EDC-SEAL) and adds the frozen fresh roster of the instrument
phase (15 EQ towers), re-implements the two-stage walk WITH PER-EDGE
LOGGING (each correction edge records its level, index, dump vector, and
Y-flag), and checks every displayed lemma below at every terminal/edge.
All consumed committed runners are md5-pinned (EDC-PIN 0).

**Instrument-phase disclosure.**  The dedicated (EMPTY) instrument unit
died before committing: its runner `empty_instrument.py`, design census
`empty_instrument_design.json` (md5 f4ff4a90603d3be90bf8c07df985a1b3),
and smoke output `empty_instrument_smoke.json` were found UNTRACKED in
the working tree, the design/smoke self-pins (abe2dafe…) not matching
the current runner bytes (6994bfc2… — edited after the smoke run; the
full battery was never executed; no results file exists).  The three
files are committed unmodified in a separate salvage commit for
provenance.  This note consumes from that phase ONLY the frozen fresh
roster (the 15 EQ tower specs, re-declared in my runner) and one design
observation quoted at S7 (the smoke MAXPI census: on every smoke dead
row the stage-2 maximum of π_{m−1} stayed < k while stage-1 DEAD-END
paths breached — exactly the two-exit-repayment mechanism proved here).
No instrument code is a proof step or a machine leg of this note.

## S1. Setting, pins, and the statement

All notation is WMULTDCX S1 verbatim (through the RM-GEN S0.1 pin): the
tower reads (e_j, h_j, g_j), P_l := e_lg_l; the pair (γ, γ′) with
iterated splits s_l, s_l′, σ_l := s_l + s_l′; the u-chain u_m := γ_{m+1},
u_{l−1} := (u_l − s_l(u_l)γ_l)/e_{l−1} with split values s_l(u_l) ∈
[0, e_{l−1}−1]; pools pool_l := σ_l + s_l(u_l) + c_{l−1}, carries
c_l := ⌊pool_l/e_{l−1}⌋, c₀ := 0; direct top mass D := σ_m + s_m(u_m);
deficit k := 2e_{m−1} − D; TRACK := (s_{m+1} = s_{m+1}′ = e_m − 1) ∧
E₁ᴵᴴ ≠ 0.  The two-stage E1-priority tree T² is W-D0's object: stage 1
seeded by the single formal cell X₀ (W-D1: j_{l−1}(X₀) = σ_l, an
identity — no split), stage-2 seeded per stage-1 exit cofactor Y and
d-cell D of Ĉ_m by the L-NORM split of b_Y·c_D at exponents
j(Y) + j(D), +1 at level 0 on the Φ₀Y-junk child.  Path counters (W-D3):
π_l (promotion edges into level l), dmp_l, cons_l, r (corrections at
reduction level m−1), junk.

**Hypotheses.**  (H1) T-scope(m): d₀ = 1 (any e), OR e_i ≥ 2 for ALL
1 ≤ i ≤ m−1 together with e₀ ≥ 2 [the RMENGINE L-MU r1-amended scope,
verbatim; note the d₀ ≥ 2 branch bounds EVERY e_i including the top].
(H2) g_{m−1} = 1 (g_m = 1 from the box setting).  (H3) interior g ≡ 1:
g_l = 1 for 1 ≤ l ≤ m−2; **g₀ IS FREE** ((H3) says nothing about g₀; no
g₀ = 1 sub-flag is consumed anywhere in this note — the level-0 divisor
mismatch P₀ = e₀g₀ vs the law's literal e₀ is handled by the integer
floor at E-L5, not assumed away).

**Abbreviations used throughout.**  t_l := σ_l + s_l(u_l) (1 ≤ l ≤ m−1;
so pool_l = t_l + c_{l−1} and D = t_m); for a fixed root-to-terminal
path of T²: jD_l := the exponent of the d-cell joined at stage-2 seeding
(0 in stage 1); Y₂ ∈ {0,1} := whether the stage-2 seed edge taken was
the Φ₀Y-junk child; CE := the multiset of correction edges taken, each
recorded as (i, k, a⃗, y) with reduction level i, index k < g_i, dump
vector a⃗ (a_l ≤ P_l − 1 for l < i, RMENGINE S2.2), and y ∈ {0,1} the
Y-child flag (its +1 lands at level 0).  Weights:

    W_{m−1} := 1,   W_l := W_{l+1}/P_l   (so W_l = 1/(P_l·P_{l+1}⋯P_{m−2}));
    w_l     := the literal-e form (P replaced by e), used only at E-L4.

Under (H3): W_l = w_l for l ≥ 1; W₀ = w₀·(e₀/P₀) ≤ w₀.

    ┌────────────────────────────────────────────────────────────────────┐
    │ THEOREM (EMPTY-(m+1)) [proved below, attempt grade].               │
    │ On TRACK, (H1)–(H3):  c_{m−1} < k  ⟹  T² has no two-exit path.    │
    │ Equivalently: every two-exit path of T² forces k ≤ c_{m−1}.       │
    │ A fortiori Q¹ has no cells and Q¹ = 0: deadness is path            │
    │ non-existence — the mechanism the 126/126 (now 616/616) zero-cell  │
    │ census observed.                                                   │
    └────────────────────────────────────────────────────────────────────┘

Route map: E-L1 turns LED_l into an exact rational identity for π_{m−1}
(the telescope).  E-L2 prices every correction edge: its dumps are worth
at most its own consumption (the self-funding constraint).  E-L3 = W-D4
prices the top: each level-(m−1) correction costs e_{m−1} extra
promotions and refunds at most 1.  E-L4/E-L5 evaluate the seed supply
against the law's nested floors: at most c_{m−1}, PLUS 1 exactly on a
single arithmetically-characterized stratum that requires the path to
ride the stage-2 Φ₀Y-junk child (Y₂ = 1).  E-L6 kills that rider: a
path with no correction edges has a π-monomial coefficient at its
stage-1 exit, and the Φ₀Y-child of a monomial-coefficient split is
CANONICALLY ABSENT.  E-L7 assembles: k ≥ c_{m−1} + 1 forces
simultaneously "no corrections" and "Y₂ = 1" — contradiction.

## S2. E-L1: the weighted telescope (LED_l made a single exact identity)

**Lemma E-L1.**  Along any root-to-terminal path of T², with C the
terminal state and ccons_l := Σ_{(i,k,·,·)∈CE, i=l} (P_l − e_lk) the
correction consumption at level l:

    π_{m−1}  =  Σ_{l=0}^{m−2} W_l · ( σ_{l+1} + jD_l + dmp_l − ccons_l − j_l(C) ).

*Proof.*  Multiply LED_l (W-D3) by W_l and sum over l = 0..m−2.  For
l ≤ m−2 the consumption decomposes cons_l = P_l·π_{l+1} + ccons_l (each
promotion edge out of level l consumes exactly P_l; exits consume only
at level m−1).  The promotion terms telescope:

    Σ_{l=0}^{m−2} W_l(π_l − P_l·π_{l+1}) = Σ_{l=0}^{m−2} (W_lπ_l − W_{l+1}π_{l+1})
                                         = W₀π₀ − W_{m−1}π_{m−1} = −π_{m−1}

(π₀ = 0, W_{m−1} = 1, W_lP_l = W_{l+1}).  Rearrange.  ∎  [Machine:
EDC-TEL — the identity holds EXACTLY (rational arithmetic) at all 22,261
terminal states of all four classes (stage-1 leaves, stage-1 exit
cofactors, stage-2 leaves, two-exit cells), sealed + fresh batteries; 0
violations.  Control CTRL-TEL0: dropping the l = 0 term breaks the
identity at 11,731 terminals — the level-0 seed mass is load-bearing.]

Every term is elementary: seeds (σ, jD), dumps received, corrections
paid, and the terminal exponents j_l(C) ≥ 0 (never negative — cells).
E-L1 is scope-free: any hypotheses enter only through WHAT the seeds and
dumps can be, not through the identity.

## S3. E-L2: the dump payment — every correction edge is self-funded

**Lemma E-L2 (pure form).**  For every correction edge (i, k, a⃗, y) ∈ CE:

    Σ_{l<i} a_l·W_l + y·W₀   ≤   (P_i − e_ik)·W_i        (i ≤ m−2),
    Σ_{l<m−1} a_l·W_l + y·W₀ ≤   1                        (i = m−1).

*Proof.*  a_l ≤ P_l − 1 (RMENGINE S2.2: the C_k^{(i)}-digits are reduced
cells) and (P_l − 1)W_l = W_{l+1} − W_l telescopes:
Σ_{l<i}(P_l − 1)W_l = W_i − W₀; adding the Y-child's +1 at level 0
(worth W₀) gives ≤ W_i.  And P_i − e_ik = e_i(g_i − k) ≥ e_i ≥ 1 since
k ≤ g_i − 1.  At i = m−1, W_{m−1} = 1.  ∎  [Machine: EDC-PAY, 0/54,615
correction edges, per-edge dump vectors from my instrumented walk.
Measured min slack: 1/12 — comfortably positive everywhere probed;
control CTRL-PAY1 (tightening by W₀ must fire) did NOT fire: the
exact-tightness corner (e_i = 1 with maximal dump vector AND the
Y-child) is not realized in these batteries — DISCLOSED, S8.]

**Lemma E-L2h (hybrid form — the level-0 dump re-priced by the floor).**
For every correction edge at level i ≥ 1:

    Σ_{1≤l<i} a_l·W_l + ⌈(a₀ + y)/P₀⌉·W₁  ≤  (P_i − e_ik)·W_i   (i ≤ m−2),
    and ≤ 1 at i = m−1   (W₁ := 1 at m = 2).

*Proof.*  Σ_{1≤l<i}(P_l−1)W_l = W_i − W₁ (telescope from level 1), and
a₀ + y ≤ (P₀ − 1) + 1 = P₀ gives ⌈(a₀+y)/P₀⌉ ≤ 1, worth W₁.  Total
≤ W_i, and the payment is ≥ e_iW_i ≥ W_i as before.  ∎  [Machine:
EDC-PAYH, 0/54,615.]

The hybrid form is the one the assembly uses: dumps into level 0 are not
valued linearly (at g₀ ≥ 2 the linear value W₀ = 1/(e₀g₀·…) is far below
the law's literal-e₀ rate) but by their worst-case effect on the level-0
INTEGER floor — at most one extra level-0 promotion per correction edge,
worth W₁.

## S4. E-L3 = W-D4, consumed verbatim (the top repayment)

For every two-exit path, at (H2):

    π_{m−1} = k + e_{m−1}·r + j_{m−1}(C)   ≥   k + e_{m−1}·r,

with r = its correction count at reduction level m−1 (index k = 0 only,
consumption e_{m−1} each; two exits consume 2e_{m−1}; dmp_{m−1} = 0
since corrections dump strictly below their level; j_{m−1}(D) = s_m(u_m)
by W-D2(i) at (H2)).  Consumed at WMULTDCX grade; re-verified here
[Machine: EDC-HEAD identity leg, 0/1,009 two-exit cells; the (H2) d-cell
top pin re-checked at every seeding: EDC-INV 0].

This is the engine of the whole route: **a level-(m−1) correction buys
≤ 1 promotion-worth of refund (E-L2, i = m−1) but costs e_{m−1} extra
promotions (E-L3)** — the "free money" the smoke instrument saw on
stage-1 DEAD-END paths (which never repay) is exactly what a TWO-EXIT
path cannot afford.

## S5. E-L4/E-L5: the seed supply against the law's floors

**Lemma E-L4 (the literal-e unroll).**  With ρ_l := (t_l + c_{l−1}) mod
e_{l−1} (the pool remainders) and w the literal-e weights:

    c_{m−1} = Σ_{l=1}^{m−1} t_l·w_{l−1} − Σ_{l=1}^{m−1} ρ_l·w_{l−1},
    and   Σ ρ_l·w_{l−1} ≤ Σ (e_{l−1}−1)·w_{l−1} = 1 − w₀.

*Proof.*  c_l = (t_l + c_{l−1} − ρ_l)/e_{l−1}; unroll top-down; the
remainder bound telescopes ((e_{l−1}−1)w_{l−1} = w_l − w_{l−1}).  ∎
[Machine: EDC-UNROLL — exact on every all-g = 1 traced row, 0
violations; the R ≤ c_{m−1} + 1 − w₀ bound never breached.]

**Lemma E-L5 (the level-0 floor chain, g₀ free — the c⁺ chain).**  For
Y ∈ {0,1} and the worst d-cell index t = g₀ − 1 define

    c⁺₁(Y) := ⌊( t₁ + (g₀−1)e₀ + Y ) / P₀⌋,
    c⁺_l(Y) := ⌊( t_l + c⁺_{l−1}(Y) ) / e_{l−1}⌋      (2 ≤ l ≤ m−1).

Then, under (H3):

    (i)   c⁺_{m−1}(0) ≤ c_{m−1}   — ALWAYS;
    (ii)  c⁺_{m−1}(1) ≤ c_{m−1} + 1, and c⁺_{m−1}(1) = c_{m−1} + 1
          exactly on the Y-TIGHT STRATUM:
             tight₀:  [g₀ = 1:  t₁ ≡ e₀ − 1 (mod e₀)]
                      [g₀ ≥ 2:  t₁ = e₀ − 1  (so c₁ = 0)]
          together with maximal remainders at every higher level
          (ρ⁺_l-propagation: (t_l + c_{l−1}) ≡ e_{l−1} − 1 mod e_{l−1}
          for 2 ≤ l ≤ m−1).

*Proof.*  Level 0, (i): write t₁ = q·e₀ + s, 0 ≤ s < e₀, so c₁ = q.
Then t₁ + (g₀−1)e₀ < (q+1)e₀g₀ ⟺ q + g₀ − 1 + s/e₀ < (q+1)g₀ ⟺
q − 1 + s/e₀ < q·g₀, which holds always (at q = 0: s/e₀ − 1 < 0; at
q ≥ 1: q − 1 + s/e₀ < q ≤ qg₀).  So c⁺₁(0) ≤ q = c₁; the higher floors
are monotone, giving (i).  Level 0, (ii): c⁺₁(1) ≥ q + 1 ⟺
s + 1 + (g₀−1)e₀ ≥ q·e₀(g₀−1) + e₀g₀; the left side is ≤ e₀g₀ with
equality iff s = e₀ − 1, so this forces q(g₀−1) = 0 and s = e₀ − 1 —
i.e. tight₀ — and then c⁺₁(1) = c₁ + 1 exactly (never more:
t₁ + (g₀−1)e₀ + 1 ≤ t₁ + P₀).  Above level 0 the +1 survives the floor
at level l iff (t_l + c_{l−1}) ≡ e_{l−1} − 1, level by level; else it
dies and c⁺_{m−1}(1) ≤ c_{m−1} by monotonicity.  ∎  [Machine:
EDC-CPLUS — both chains and the exact +1-classification on every traced
row (including every g₀ = 2 row), 0 violations; the guard "the Y-unit
crossed the level-0 floor off tight₀" never fired.]

The d-cell inventory feeding E-L5 is W-D2 at (H2)+(H3): jD_{m−1} =
s_m(u_m); jD_l = s_{l+1}(u_{l+1}) at 1 ≤ l ≤ m−2; jD₀ = s₁(u₁) + t·e₀
with 0 ≤ t ≤ g₀ − 1.  [Machine: EDC-INV — all three clauses re-checked
at every stage-2 seeding, 0 violations.]

## S6. E-L6: the Φ₀Y-junk child of a monomial coefficient is ABSENT

**Lemma E-L6.**  Let b ∈ O[x] with deg b = 0 (a π-monomial times a unit
scalar — in T² stage 1 without correction edges, b = π^{u₁+u₁′} exactly)
and let c_D be a d-cell coefficient (deg c_D < d₀).  Then the L-NORM
split of b·c_D has Φ₀Y-junk child IDENTICALLY ZERO: the seed edge with
the +1 at level 0 DOES NOT EXIST.

*Proof.*  L-NORM normalizes: b = π^{w₀(b)}·b̂, c_D = π^{w₀(c_D)}·ĉ with
b̂, ĉ primitive, and applies [IL3]† DIGIT-SPLIT to the primitive product
b̂ĉ: b̂ĉ = lift(q(b̂)q(ĉ)) + πX̂ + Φ₀Ŷ, in which Ŷ is the CANONICAL
Φ₀-quotient of the overflow: deg(b̂ĉ) < d₀ forces Ŷ = 0 — this is the
same degree mechanism L-NORM(c) already displays for its d₀ = 1 absence
clause ("deg(b̂ĉ) ≤ 2d₀ − 2 = 0 < d₀, no Φ₀-overflow, Ŷ = 0"), applied
one step more generally: here deg b̂ = deg b = 0, so deg(b̂ĉ) =
deg ĉ < d₀ for ANY d₀.  ∎  [Machine: EDC-YMON, two clauses, 0
violations: (a) every digit_split call anywhere in both trees with
deg(b·c) < d₀ produced a zero Y-child (the canonicity leg — checked at
every correction and every seeding); (b) every stage-2 seeding whose
stage-1 prefix took NO correction edge had deg(b_Y) = 0 AND zero
Y-child.  Teeth: 1,373 digit_split calls elsewhere DID produce nonzero
Y-children (CTRL-Y), and 61 stage-2 Y-child edges were actually taken in
the batteries — ALL 61 on stage-1 prefixes with ≥ 1 correction edge,
none ever on a correction-free prefix.]

**Why b stays monomial without corrections (the W-D1 leg).**  Stage 1
seeds by the IDENTITY X₀ = â·â′ (W-D1: no development, no DIGIT-SPLIT,
no re-expansion — b(X₀) = π^{u₁+u₁′}); promotion edges carry b unchanged
(RMENGINE S2.2: "b unchanged"); Φ_m-exits keep the coefficient in the
cofactor.  L-NORM splits — the only b-mutating edges — occur exactly at
correction edges and at stage-2 seeding.  So on a path whose stage-1
prefix has CE = ∅, the stage-1 exit cofactor coefficient is b_Y =
π^{u₁+u₁′} verbatim, and E-L6 applies to its stage-2 seeding.

## S7. E-L7 + E-THM: the assembly and the tight-corner contradiction

**Assembly.**  Fix a two-exit path with terminal cell C on a TRACK row,
(H1)–(H3).  Truncating E-L1 at level 1 (same telescope, stopping at
W₁π₁) and bounding π₁ by the level-0 integer floor (LED₀ with j₀(C) ≥ 0
and cons₀ ≥ P₀π₁ + [level-0 correction consumption]):

    π_{m−1} = W₁·π₁ + Σ_{l=1}^{m−2} W_l·( σ_{l+1} + jD_l + dmp_l − ccons_l − j_l(C) ),

    π₁ ≤ ⌊( t₁ + t·e₀ + Y₂ + Σ_{CE}(a_{c,0} + y_c) − Σ_{CE, i=0}(P₀ − e₀k_c − y_c) )/P₀⌋
       ≤ c⁺₁(Y₂) + Σ_{CE, i≥1} ⌈(a_{c,0}+y_c)/P₀⌉ − 𝟙[some level-0 correction]
       ≤ c⁺₁(Y₂) + #CE_{≥1} − 𝟙[CE₀ ≠ ∅]

using jD₀ = s₁(u₁) + te₀ ≤ s₁(u₁) + (g₀−1)e₀ (W-D2(iv)), floor
subadditivity ⌊(x + Σy_c)/P₀⌋ ≤ ⌊x/P₀⌋ + Σ⌈y_c/P₀⌉ with y_c ≤ P₀, and,
for the last step, that each level-0 correction removes P₀ − e₀k − y ≥
e₀ − 1 ≥ 1 from the numerator on the (H1) branches where level-0
corrections can matter (d₀ ≥ 2 forces e₀ ≥ 2; at d₀ = 1 the Y-children
are absent so P₀ − e₀k ≥ 1 outright).  Now insert E-L2h per correction
edge at levels 1..m−2 (dump value + floor unit ≤ payment, with STRICT
loss (e_i − 1)W_i > 0 whenever e_i ≥ 2), the ≤ 1 refund per level-(m−1)
correction against its e_{m−1}-cost from E-L3, the c⁺-unroll (E-L4
pattern at levels ≥ 1: W₁c⁺₁ + Σ_{l≥2} t_lW_{l−1} ≤ c⁺_{m−1} + 1 − W₁),
and E-L5.  Every slack term collected on one side:

    k  ≤  c_{m−1} + 𝟙[Y-tight stratum ∧ Y₂ = 1]
          − Σ_{l=2}^{m−1} ρ⁺_l·W_{l−1}                    [E-L4/E-L5 unroll slack;
                                                           = 0 iff remainders maximal]
          − Σ_{CE, 1≤i≤m−2} (e_i − 1)·W_i                 [E-L2h strict loss]
          − (e_{m−1} − 1)·r                               [E-L3 vs the ≤ 1 refund]
          − 𝟙[CE₀ ≠ ∅]·W₁                                 [level-0 corrections kill
                                                           the floor's +1]
          − j_{m−1}(C) − Σ_{l=1}^{m−2} W_l·j_l(C)          [terminal exponent slack]

(every collected term is ≥ 0; the machine checks the assembled midpoint
bound π_{m−1} ≤ Σ W_l(σ_{l+1}+jD_l) + Y₂W₀ + r directly: EDC-BND
0/1,009).  Since k and c_{m−1} are integers:

**Lemma E-L7 (forcing).**  If k ≥ c_{m−1} + 1 then EVERY slack vanishes;
in particular (a) Y₂ = 1 (the path took the stage-2 Φ₀Y-junk child, on
the Y-tight stratum), and (b) CE = ∅ and r = 0 — no correction edge
anywhere on the path.  For (b): at d₀ = 1 nothing is needed (Y₂ = 1 is
already impossible — L-NORM(c) absence — so k ≥ c+1 is refuted
outright); at d₀ ≥ 2, (H1) gives e₀ ≥ 2 and e_i ≥ 2 for all
1 ≤ i ≤ m−1, so every correction edge at levels 0..m−2 carries a
strictly positive displayed loss and every level-(m−1) correction
carries (e_{m−1}−1)r ≥ r > 0.  ∎

**Theorem E-THM = (EMPTY-(m+1)), proof.**  Suppose a two-exit path
exists with k ≥ c_{m−1} + 1.  By E-L7(b) its stage-1 prefix has no
correction edges, so its stage-1 exit coefficient is b_Y = π^{u₁+u₁′}
(S6, the W-D1 leg), and by E-L6 the stage-2 Φ₀Y-junk child of that
seeding is IDENTICALLY ABSENT — contradicting E-L7(a) Y₂ = 1.  Hence
every two-exit path has k ≤ c_{m−1}; contrapositive: c_{m−1} < k ⟹ no
two-exit path, no Q¹ cell, Q¹ = 0.  ∎

[Machine, the theorem's own line: EDC-HEAD — k ≤ c_{m−1} at every one
of the 1,009 two-exit cells ever produced (sealed + fresh, live rows);
EDC-EMPTY — 616 traced law-dead rows (126 sealed + 490 fresh: deficits
k up to 4, non-near-miss strata c ≤ k−2, m = 4, g₀ = 2, d₀ = 2, both
characteristics) carry ZERO two-exit terminals; EDC-Q1LAW — the full
fresh census, 1,380 TRACK keys, Q¹ ≠ 0 ⟺ the law clause, 0 breaches;
CTRL-HEAD1 — 560 live cells sit AT k = c_{m−1}, so the bound is sharp.
The Y-tight stratum is populated: 116 traced rows (104 at d₀ = 1, 12 at
d₀ ≥ 2, witnesses in the results json) — all dead, all zero-cell, i.e.
the corner the Y-rider would need is instance-realized and the E-L6
kill is what closes it there.]

**Reading (the mechanism, in one paragraph).**  The pools/carries are
exactly the tree's seed supply measured in promotion capacity; the two
excess channels are real (dumps and non-principal d-cells DO push π
beyond the floors — the sealed 72, and stage-1 dead-end paths DO breach
depth k on dead rows, as the salvaged smoke shows with maxpi_all ≥ k at
13 rows) — but they are PRICED: every dump was paid for by exponent mass
the same path consumed at its source level (E-L2), every top correction
costs e_{m−1} ≥ 1 promotions against a refund ≤ 1 (E-L3/E-L2), the
non-principal d-cell excess (g₀−1)e₀ dies against the level-0 divisor
P₀ = e₀g₀ (E-L5(i)), and the single unpaid +1 in the entire economy —
the stage-2 Φ₀Y-junk child — exists only on paths whose coefficient
history could overflow Φ₀, which a correction-free history cannot
(E-L6).  A two-exit path must repay everything; on a dead row there is
nothing left to repay with.

## S8. Machine brackets (summary) and disclosures

`empty_derive_checks.py` (md5 8fed924…), single deterministic run, exact
integer/rational arithmetic: **17 verdict families, 0 violations.**
EDC-PIN (4 consumed-runner md5s) · EDC-SEAL (412/858/126 sealed
replication exact) · EDC-LED + EDC-TEL (22,261 terminals, all four
classes — extends the committed DCK-LEDGER coverage from Q¹ cells to
leaves and stage-1 states) · EDC-PAY + EDC-PAYH (54,615 correction
edges, per-edge) · EDC-FLOOR (level-0 integer floor, every terminal) ·
EDC-BND + EDC-HEAD (1,009 cells) · EDC-EMPTY (616 dead rows, zero
two-exit paths) · EDC-Q1LAW (1,380 fresh TRACK keys) · EDC-UNROLL ·
EDC-CPLUS · EDC-YMON · EDC-INV · EDC-CONS · HARNESS.  Controls:
CTRL-TEL0 11,731 · CTRL-FLOOR1 7,675 · CTRL-HEAD1 560 · CTRL-Y 1,373 ·
CTRL-TIGHT 116 — all fired.

**Disclosures.**  (i) CONTROL FAILURE, CTRL-PAY1: the E-L2 payment
inequality was never within W₀ of equality on any probed edge (min
slack 1/12) — the tightness corner (e_i = 1, maximal dump vector, plus
Y-child) is not realized in these batteries; E-L2's proof is displayed
arithmetic and does not lean on the control, but the corner is
instance-unprobed.  (ii) Machine coverage is m ∈ {3, 4} (the sealed
roster + the EQ roster); the displayed proofs are uniform in m ≥ 2 and
the m = 2 top-identity anchor is the sealed DCX3-C2 leg cited at W-D4.
(iii) Fresh dead rows were traced under per-stratum caps (24 at m = 3,
10 at m = 4 per (k, c_{m−1}) stratum): 490 of the 793 census-dead fresh
rows traced; the UNTRACED dead rows are still law-censused (EDC-Q1LAW
covers all 1,380 keys — a Q¹ ≠ 0 dead row anywhere would have violated
there).  (iv) The stage-2 Y-child population: 61 edges, all on
corrected stage-1 prefixes — consistent with, and required by, E-L6.

## S9. What remains open (the honest boxes)

    ┌────────────────────────────────────────────────────────────────────┐
    │ (EMPTY-gen)  [OPEN, boxed].  (EMPTY-(m+1)) WITHOUT (H3): interior  │
    │ g_l ≥ 2 levels.  The S9 box of WMULTDCX states the route at        │
    │ (H1)–(H2); this note proves it at (H1)–(H3) (g₀ free).  At an      │
    │ interior level with g_l ≥ 2 the same two leaks reopen one level up │
    │ (non-principal d-cell exponents t·e_l and the P_l = e_l·g_l vs     │
    │ literal-e_l divisor mismatch); the E-L5 integer-floor treatment    │
    │ should lift level by level, BUT the d-cell inventory at interior   │
    │ g ≥ 2 is only displayed in proof shape at W-D2 (its machine leg    │
    │ is g₀ ∈ {1,2} only — WMULTDCX F4), and no battery in this program  │
    │ has ever contained an interior-g ≥ 2 tower.  Do not consume        │
    │ (EMPTY) off (H3) — state the pin at every use site.                │
    └────────────────────────────────────────────────────────────────────┘

    ┌────────────────────────────────────────────────────────────────────┐
    │ (SURV-(m+1))(i)  [OPEN — unchanged by this note].  Survival:       │
    │ c_{m−1} ≥ k ⟹ Q¹ ≠ 0.  This note contributes nothing to (i): it   │
    │ bounds paths above, never below, and says nothing about residue    │
    │ survival of the cells that do exist.  (i) still needs the residue  │
    │ layer (DEV-at-depth — the WMULTDCX S9 display) and, at g₀ ≥ 2,     │
    │ the recycled-mass economy (fence F2 there STANDS: the live rows at │
    │ pool₁ < P₀ ride channels this note only ever needed to BOUND, not  │
    │ to realize).                                                       │
    └────────────────────────────────────────────────────────────────────┘

**The honest consequence display.**

* **(SURV-(m+1))(ii) follows on (H1)–(H3)**: c_{m−1} < k ⟹ (E-THM) no
  cells ⟹ Q¹ = 0 — with NO cancellation lemma, exactly as the W-r1
  positive lead predicted.  Grade: attempt, capped by the WMULTDCX
  consumption (W-D2/W-D3/W-D4 are load-bearing here and stand at 0/2
  CLEAN).
* **(SURV-(m+1))(i) [survival] is STILL OPEN** — the box above.
* **LAW-DCX-(m+1) is STILL A CONJECTURE at every m ≥ 2**: the law is
  (i) ∧ (ii); this note closes only the (ii) leg, only at (H3), and
  only at attempt grade.  Nothing here upgrades the law, and nothing
  here is consumed by any accepted block.
* When BOTH (i) and (ii) close AND the W arc accepts, LAW-DCX-(m+1)
  becomes a theorem on its class and the [ILN]† Case-II legs close ON
  it per the S7.2/COND-B thread — that chain is unchanged.

## S10. Claims table, dependency line, fences

| # | claim | grade | consumes |
|---|---|---|---|
| E-L1 | weighted telescope: π_{m−1} as the exact W-weighted LED sum | PROVED (attempt) — scope-free | W-D3 (LED_l) |
| E-L2 | per-edge dump payment, pure form (≤ W_i; ≤ 1 at top) | PROVED (attempt) | RMENGINE S2.2 inventory (a_{d,l} ≤ P_l−1, k < g_i) |
| E-L2h | hybrid form: level-0 dumps priced by the integer floor (≤ 1 floor unit per edge) | PROVED (attempt) | E-L2 telescope + floor subadditivity |
| E-L3 | top repayment identity | = W-D4, consumed (attempt grade, (H2)) | W-D3 + W-D2(i) |
| E-L4 | literal-e unroll c_{m−1} = R − Σρw; R ≤ c+1−w₀ | PROVED (attempt) | arithmetic |
| E-L5 | c⁺ floor chain: c⁺(0) ≤ c always; c⁺(1) ≤ c+1 with +1 exactly on the Y-tight stratum | PROVED (attempt; (H3), g₀ free) | W-D2(ii)–(iv) inventory |
| E-L6 | Φ₀Y-child of a deg-0 coefficient split is canonically absent | PROVED (attempt) | L-NORM(c) mechanism + [IL3]† DIGIT-SPLIT canonicity + W-D1 |
| E-L7 | forcing: k ≥ c+1 ⟹ Y₂ = 1 ∧ CE = ∅ ∧ r = 0 | PROVED (attempt; (H1) e-bounds at d₀ ≥ 2) | E-L1–E-L5 |
| **E-THM** | **(EMPTY-(m+1)) on (H1)–(H3), g₀ free: c_{m−1} < k ⟹ no two-exit path** | **PROVED at attempt grade** | E-L6 + E-L7 |
| (SURV)(ii) | c < k ⟹ Q¹ = 0 on (H1)–(H3) | follows from E-THM (attempt, same cap) | E-THM |
| (EMPTY-gen) | interior g ≥ 2 extension | **OPEN** (boxed, S9) | — |
| (SURV)(i) | survival | **OPEN** (unchanged; WMULTDCX S9 box) | — |
| LAW-DCX-(m+1) | the law | UNCHANGED: m = 1 proved, m ≥ 2 conjecture | not upgraded |

**Dependency line.**  Consumes: WMULTDCX_2026-08-08.md† (W-D0–W-D4,
W-D6/6c framing; ATTEMPT GRADE, 0/2 CLEAN — **this note's grade is
capped by that consumption until the W arc closes**; the W-D7
(STK)/law-clause pins NOT consumed); RMENGINE_2026-08-08.md [RMG]†
(ACCEPTED): S2.2 tree + child inventory, L-NORM (incl. clause (c)),
L-EXACT, T-TERM on the (H1) pin; [IL3]† DIGIT-SPLIT (through L-NORM);
[ILN]† S4.1/(Ĉ) inventory through RM-GEN S2.1 (their conditionality
riders — the ITERLAWN S4.7 erratum chain for the (H2) discharge — ride
through unchanged; (H2) stays EXPLICIT here as in WMULTDCX).  Dagger
convention: † = consumed at the block's own standing grade; grades ride
through; the weakest consumed grade (WMULTDCX, attempt/0-clean) caps
this note.  Sealed artifacts as instance evidence only: the derive
battery (WMULTDCX S0 pins), stress d3950f2/d774ecb, the salvaged
instrument design/smoke (this unit's salvage commit).  Machine legs of
THIS unit: `empty_derive_checks.py` 8fed92402bcffe6e0c536f1f9d847612 ·
output ddae400794ce1b25bd332beddd40528d · results
229a1b1e0c1a93f154bc34e5ce1f5059.

**Fences.**
F-A. (H3) is consumed throughout (W-D2's forced inventory); (EMPTY-gen)
     boxed — do not cite this theorem off (H3).
F-B. (H1) T-scope enters twice: through W-D0 (T² = the canonical
     divisions) and through the d₀ ≥ 2 e-bounds in E-L7(b).  The
     e₀ = 1 ∧ d₀ ≥ 2 corner is outside T-scope, as everywhere in the
     program.
F-C. (H2) explicit; its on-TRACK discharge rides the [ILN]† (P-DS)
     chain with the ITERLAWN S4.7 erratum conditionality (WMULTDCX F1
     verbatim).
F-D. Machine coverage m ∈ {3,4}, g₀ ∈ {1,2}, d₀ ∈ {1,2}, both
     characteristics; displayed proofs uniform in m ≥ 2.  The E-L2
     tightness corner and the untraced 303 fresh dead rows are
     disclosed at S8 (the latter law-censused).
F-E. Nothing here touches (SURV)(i), the residue layer, attainment, or
     the law's grade.  This note proves properties of T² plus the
     emptiness leg ONLY.
F-F. This unit's grade: PROVED at attempt grade, ZERO hostile passes.
     Verification protocol owed: hostile pass(es) on this text +
     runner, Codex leg included, per the standing arc discipline.
