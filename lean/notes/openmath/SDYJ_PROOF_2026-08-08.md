# (SD-YJ′) PROVED at attempt grade — the digit-valuation floor closes the g₀ = 1 ∧ d₀ ≥ 2 corner: every cascade-slot companion sits at w₀ ≥ ŵ + 1, so SD-THM-A extends to EVERY d₀ and the g₀ = 1 leg of (SURV-DISJ) is class-wide

Object: the single open lemma extracted by the (SURV-DISJ) construction
unit (SURVDISJ_CONSTRUCT_2026-08-08.md S6 T3, ledger 1047b48), sharpening
the (SD-YJ) box of SURVDISJ_PROOF_2026-08-08.md S6:

    (SD-YJ′): at g₀ = 1 ∧ (STK), every cascade-slot companion carries
    junk ≥ 1 (automatic: it is Φ₀Y-fed by (★) + SD-L1), and junk ≥ 1 at
    the FIXED slot ĵ forces line > β̂ (equivalently w₀ > ŵ) — the junk
    line-gain cannot be offset by promotion savings at fixed slot.

**Verdict, stated first.  (SD-YJ′) is PROVED at attempt grade (capped),
in a form STRONGER than charged**: on TRACK, (H1)–(H3), g₀ = 1, ANY d₀,
(STK), c_{m−1} ≥ k, every two-exit terminal at the cascade slot ĵ other
than the cascade cell Ĉ and its X-mate has w₀ ≥ ŵ + |CE| + #π-junk ≥
ŵ + 1, hence line = β̂ + E_m·(w₀ − ŵ) > β̂ — the line-gain is forced by
the CORRECTION EDGES ALONE, junk or no junk (the junk clause of the box
remains true and automatic, but is not what pays).  The mechanism is a
THIRD ledger, new to this unit: the MULTIPLICATIVE VALUATION ledger.
The two prior ledgers cannot see this statement — the E-weighted mass
ledger (SD-L2) tracks exponents and is exactly what the Φ₀Y-economy can
balance to 0 (that is why companions exist at all), and the additive
line ledger (W-D5) has the open m ≥ 3 resonance corner (S-L4(iii)).
The valuation ledger tracks w₀(b) through the only edges that mutate b
— L-NORM splits at corrections and at the stage-2 seeding — and there
the new Lemma SDY-L1 (the digit-valuation floor) forces every
correction to pay ≥ 1 unit of π-valuation at g₀ = 1: the correction
digit C₀^{(i)} is a SINGLE on-line on-grid cell whose coefficient
valuation is the forced descending weight chain from γ_{i+1}, and that
chain can never reach 0.  Promotion edges carry b unchanged, so
"promotion savings" cannot offset anything in this ledger — the offset
feared by the box is a mass/line phenomenon, absent by construction
from the valuation ledger.  Consequence: SD-THM-A's clauses (ii)–(v)
hold at EVERY d₀ (Theorem SDY-THM below); the (SD-YJ) box CLOSES; the
open set of (SURV-DISJ) is exactly (SURV-K2); the LAW-DCX-(m+1) pinned
class drops its d₀ = 1 pin.

Scope: the [ILN]† S0.1 class via the RM-GEN S0.1 pin, level m ≥ 2,
g_m = 1.  Date: 2026-08-08 campaign (wallclock 2026-08-04); the
(SD-YJ′) composer unit, on the construction unit's two-commit seal
84edf07/092471d (ledger 1047b48).

**Grade (header summary) and THE GRADE-CAP SENTENCE.**  SDY-L1, SDY-L2,
SDY-L3 (= (SD-YJ′)) and SDY-THM — PROVED at attempt grade (composed
this unit; hostile-pass record 0/2 CLEAN — no pass yet; the arc opens
with this revision).  **Grade cap carried from consumption [dagger
discipline]: this note consumes WMULTDCX_2026-08-08.md† (W-D1, W-D2(0)/
(ii)/(iii), W-D3 via SD-L2, W-D5's q_l bookkeeping, W-D7) at ATTEMPT
grade — that arc stands at 0/2 CLEAN, not accepted, THE BINDING CAP —
and SURVDISJ_PROOF_2026-08-08.md† (SD-L1, SD-L2, (★), SD-L4, the
SD-THM-A architecture) at ATTEMPT grade (1/2 CLEAN after its PE2), and
SURV_PROOF_2026-08-08.md† (S-L0, S-L1, S-L4(i)(ii), S-L4(iii)'s
uniqueness half, S-THM(c)) at ATTEMPT grade (0 CLEAN passes), and
EMPTY_PROOF_2026-08-08.md† (E-L6; E-THM in the S6 consequence display
only) at ATTEMPT grade (1/2 CLEAN); so every result here is capped at
attempt grade by the weakest of these (the W arc, 0/2) until those
arcs close.  RMENGINE [RMG] is ACCEPTED (round-7 double-clean):
L-NORM(a)(b)(c), the S2.2 child inventory (correction children,
reduced dumps a_{d,l} ≤ P_l − 1, the i = 0 form, b unchanged on
promotions/exits), L-CELL(i), L-GRID + the S3.1 λ-chain, and the S0.2
weight kit carry no cap.  The [ILN]† S0.1 weight recursion (γ₁ = h₀,
γ_{j+1} = e_j·w_jΦ_j + h_j, w_jΦ_j = e_{j−1}g_{j−1}γ_j) is consumed as
class DEFINITIONS.  The construction unit's artifacts (41 rows, 8
companions) are design input + instance evidence, never proof steps.**
(SURV-DISJ) class-wide after this note — OPEN = exactly (SURV-K2).

## S0. Authority, charge, consumption, machine leg

Charge (the orchestrator's composer charge, ledger 1047b48): prove
(SD-YJ′) or box the exact obstruction; expected route "the E-weighted
ledger (SD-L2) applied to the companion's path — the Y-edge's mass gain
must be paid by π-junk or by correction deficits that (★) caps".
**Deviation from the charged route, displayed:** the mass ledger is the
wrong instrument for the second clause — (★) says exactly that the
companion's MASS economy balances (Σ defc = Y₂), so no mass imbalance
is available to force a line gain; what forces the gain is the
VALUATION economy, which the mass ledger does not see.  The charged
route's ingredients ((★), SD-L1, L-NORM(b)/(c)) are all consumed, but
re-keyed: (★) + SD-L1 supply the Φ₀Y-fed clause (junk ≥ 1) and the
companion anatomy; L-NORM supplies the per-edge valuation laws; the new
floor SDY-L1 supplies the payment.

Consumption (read-only, dagger discipline; grades ride through as in
the header sentence): **[RMG] ACCEPTED**: L-NORM(a) (L-child valuation
EXACTLY w₀(b) + w₀(c), residue product ≠ 0), L-NORM(b) (π-junk child
w₀ ≥ w + 1), L-NORM(c)/E-L6 mechanism (Φ₀Y-child w₀ ≥ w, exponent +1
at level 0; identically zero when deg(b̂ĉ) < d₀), S2.2 (promotion/exit
children carry b UNCHANGED; correction children = L-NORM split of
b·c_d, one per reduced cell d of C_k^{(i)}, dumps a_{d,l} ≤ P_l − 1 at
l < i; the i = 0 children = split of b·lift(ψ₀,k)·π^{(g₀−k)h₀}; the
C_k^{(i)} := realize_i(ε_i((g_i−k)γ_{i+1})^{−1}ψ_{i,k}, (g_i−k)γ_{i+1})
display with every cell reduced, ON-LINE at (g_i−k)γ_{i+1}, ON-GRID,
nonzero residue — the RM-GEN S2.1 certified inventory one level down),
L-CELL(i) (distinct reduced cells, keyed by exponent vectors), L-GRID +
the S3.1 λ-chain (top-down forcing; λ₀ = w₀(b)).  **WMULTDCX†**: W-D1
(X₀ = (π^{u₁+u₁′}, σ⃗) an identity), W-D2(0)/(ii)/(iii) (u-chain; the
d-cell inventory: at (H3) ∧ g₀ = 1 every d-cell has j⃗(D) = j⃗_prin and
w₀(c_D) = u₀), W-D7 (cascade existence under (STK) ∧ clause).
**SURVDISJ_PROOF†**: SD-L1 (deficit bound + equality analysis), SD-L2 +
(★) (Σ defc = Y₂ ∈ {0,1} at the cascade slot, any d₀), SD-L4 (the
b₀-seeding: Y-child zero at ANY d₀ on correction-free prefixes;
L-child at ŵ; X-child ≥ ŵ + 1), SD-THM-A (the d₀ = 1 theorem whose
proof architecture is extended verbatim).  **SURV_PROOF†**: S-L0
(weight kit), S-L1 (cascade content: ŵ = u₁ + u₁′ + u₀, β̂, residue
≠ 0 — its unique-d-cell display is ALREADY any-d₀), S-L4(i) (line =
E_m·w₀ + Σ j_lΓ_l — the fixed-slot affinity), S-L4(ii), S-L4(iii)'s
uniqueness half (correction-free junk-free two-exit path unique),
S-THM(c).  **EMPTY_PROOF†**: E-L6 (+ the "why b stays monomial" leg);
E-THM only in S6.  **[ILN]†**: the S0.1 class pin (e_j ≥ 1, h_j ≥ 1,
gcd(e_j, h_j) = 1) and weight recursion, as definitions.

**Machine leg of THIS unit (the derivation shadow + fresh instances):**
`verification/openmath/sdyj_checks.py`, committed WITH this note at
commit 1 (verdict + artifacts = commit 2; the S7 machine bracket is
PENDING at commit 1 with every family's prediction SEALED below).
Engines consumed byte-untouched, md5-pinned inside the runner — and
UNPATCHED: unlike the construction unit, this unit needs no pick
extension (all towers g₀ = 1, interior g ≡ 1, d₀ ≤ 2).  Eleven verdict
families (S7).  Roster: the construction unit's NINE committed T3
towers re-traced (replication family) PLUS six fresh in-class towers
(YJX1–YJX6, S7.2) chosen to stress the floor's arithmetic: h₀ = 3 with
flat h₁ = 3; e₀ = 3 at p = 3 (twice, h₀ ∈ {1, 2} — the razor-thin
v₀ = 1 corners where the naive rational bound is < 1 and INTEGRALITY
is load-bearing); a double-flat m = 4 tower; a d₀ = 1 flat control; an
m = 2 corner.  **Design-probe disclosure:** one pre-commit shakedown
run of the runner on a THROWAWAY spec outside every roster (m = 2,
p = 3, d₀ = 2, reads [(2,1,1),(2,3,1),(2,1,1)]) plus a small-grid
sweep smoke test, for crash-freedom only; no roster tower was traced
and no family verdict on any roster quantity was observed pre-seal.

## S1. Setting and the two reductions

Notation: WMULTDCX S1 / SURV_PROOF S1 / SURVDISJ_PROOF S1 verbatim
(T², counters, pools, carries, D, k := 2e_{m−1} − D; the cascade slot
ĵ at line β̂ with cascade cell Ĉ, coefficient valuation
ŵ = u₁ + u₁′ + u₀ — S-L1; E_0 := 1, E_l := e₀⋯e_{l−1}; Γ_l :=
γ_{l+1}∏_{l<t<m}e_t).  Standing hypotheses (H1)–(H3), g₀ = 1, (STK),
c_{m−1} ≥ k; d₀ FREE — the whole point.  Under (H2) + (H3) + g₀ = 1
every g_l = 1 (0 ≤ l ≤ m−1), so P_l = e_l and every correction has
k_c = 0 (SD-L1's standing remark).  The weight data ([ILN]† S0.1, all
g = 1): γ₁ = h₀;  w_lΦ_l = e_{l−1}γ_l (l ≥ 1);  γ_{l+1} = e_l·w_lΦ_l
+ h_l = e_le_{l−1}γ_l + h_l;  e_l ≥ 1, h_l ≥ 1, gcd(e_l, h_l) = 1.

**Reduction 1 (fixed-slot affinity).**  line(C) = E_m·w₀(b_C) +
Σ_l j_l(C)·Γ_l (S-L4(i)), and Ĉ sits at (ĵ, β̂) with w₀ = ŵ (S-L1).
So for ANY cell C at slot ĵ:  line(C) − β̂ = E_m·(w₀(C) − ŵ), and

    (SD-YJ′)'s second clause  ⟺  w₀(C) ≥ ŵ + 1  for every
    cascade-slot companion C.

**Reduction 2 (companion anatomy).**  Let C be a two-exit terminal
with j⃗(C) = ĵ, C ≠ Ĉ.  If CE(C) = ∅ then the stage-1 prefix is
correction-free, so its exit coefficient is b₀ = π^{u₁+u₁′} verbatim
(W-D1 + S2.2 b-unchanged, the E-L6 leg), the stage-2 seeding is the
L-NORM split of b₀·c_D with the Φ₀Y-child IDENTICALLY ZERO at ANY d₀
(SD-L4(i): deg b̂₀ = 0), and off the seeding a correction-free path
has no forks at all (promotion/exit children unique per firing,
E1-priority deterministic — the S-L4(iii) uniqueness half).  Hence C
terminates the L-branch — and IS Ĉ — or the X-branch: the X-mate,
ce = ∅, junk ≥ 1, w₀ ≥ ŵ + 1 (L-NORM(b), SD-L4(iii)), at most one.
So every companion C ∉ {Ĉ, X-mate} has **CE(C) ≠ ∅**, and by (★)
(Σ_c defc_c = Y₂(C) ∈ {0,1}, any d₀) with SD-L1's equality analysis it
is Φ₀Y-fed: Y₂ = 1 (the seeding rode its Y-child) or Y₂ = 0 with every
defc = 0, forcing EVERY correction to ride its Y-child (Y_c = 1) —
either way **junk(C) ≥ 1**: the box's automatic clause, displayed.

What remains is the payment: every correction edge costs ≥ 1 unit of
coefficient valuation.  That is the new lemma.

## S2. SDY-L1: the digit-valuation floor (the new mathematics)

**Lemma SDY-L1.**  Assume (H2), (H3), g₀ = 1 (so g_l = 1 for all
0 ≤ l ≤ m−1).  Then for every reduction level 0 ≤ i ≤ m−1, every cell
d of the correction digit C₀^{(i)} has coefficient valuation

    w₀(c_d) ≥ 1 ;

precisely: at i = 0, C₀^{(0)} = lift(ψ₀,0)·π^{h₀} with w₀ = h₀ ≥ 1
exactly ([RMG] S2.2, g₀ = 1); at i ≥ 1, every cell of C₀^{(i)} has the
SAME forced exponent vector and valuation — the digit is a single cell
up to coefficient — given by the descending weight chain

    v_i := γ_{i+1};   for l = i, …, 1:
    s_l := s_l(v_l) ∈ [0, e_{l−1}),   a_{l−1} = s_l  (the dump digit),
    v_{l−1} := (v_l − s_l·γ_l)/e_{l−1} ∈ ℤ ;
    w₀(c_d) = v₀ ,

and the chain obeys the invariant

    (INV_l)   v_l ≥ e_{l−1}·γ_l + 1   for every 1 ≤ l ≤ i,

whence v₀ ≥ 1.

*Proof.*  (a) The forced chain.  By the certified inventory ([RMG]
S2.2 / RM-GEN S2.1 one level down), every cell d = c_d·∏_{l<i}Φ_l^{a_l}
of C₀^{(i)} = realize_i(ε_i(γ_{i+1})^{−1}ψ_{i,0}, γ_{i+1}) is REDUCED
(a_l ≤ P_l − 1 = e_l − 1), ON-LINE at γ_{i+1} at level i, and ON-GRID.
Run the S3.1 λ-chain top-down from λ_i = γ_{i+1} (L-GRID): at each
level, on-grid gives a_{l−1} ≡ s_l(λ_l) mod e_{l−1} with t_l :=
(a_{l−1} − s_l(λ_l))/e_{l−1} ∈ [0, g_{l−1}) — and g_{l−1} = 1 forces
t_l = 0, i.e. a_{l−1} = s_l(λ_l) EXACTLY, at every level including
l = 1 (level 0: this is where g₀ = 1 enters).  So the dump vector is
forced, the λ-chain is the displayed v-chain (integrality of each step
from γ_l ≡ h_{l−1} and ℓ_{l−1}h_{l−1} ≡ 1 mod e_{l−1} — the L-GRID
remark), and its terminal is λ₀ = w₀(c_d) (L-GRID: λ-values are the
truncation lines; at level 0, line₀(b) = w₀(b)).  Since c_d ∈ O[x],
v₀ = w₀(c_d) ≥ 0 automatically; the content is v₀ ≠ 0.
(b) The invariant.  Base l = i: v_i = γ_{i+1} = e_i·w_iΦ_i + h_i with
w_iΦ_i = e_{i−1}γ_i (all g = 1), e_i ≥ 1, h_i ≥ 1, so v_i ≥
e_{i−1}γ_i + 1.  Step l → l−1 (2 ≤ l ≤ i): using s_l ≤ e_{l−1} − 1
and (INV_l),

    v_{l−1} ≥ (v_l − (e_{l−1}−1)γ_l)/e_{l−1} ≥ (γ_l + 1)/e_{l−1}
            = w_{l−1}Φ_{l−1} + (h_{l−1} + 1)/e_{l−1}
              [γ_l = e_{l−1}·w_{l−1}Φ_{l−1} + h_{l−1}]
            > w_{l−1}Φ_{l−1} = e_{l−2}γ_{l−1} ,

and v_{l−1} ∈ ℤ strictly above the integer e_{l−2}γ_{l−1} gives
(INV_{l−1}) — integrality is load-bearing: the rational bound alone
can sit below e_{l−2}γ_{l−1} + 1 (instances at S7.2 realize this).
(c) Terminal: v₀ ≥ (v₁ − (e₀−1)γ₁)/e₀ ≥ (γ₁ + 1)/e₀ > 0 by (INV_1),
and v₀ ∈ ℤ, so v₀ ≥ 1.  ∎

[Machine: SDYJ-DIG — on every tower of both rosters, every level
i ≥ 1: the digit has exactly ONE cell, its dump vector equals the
forced v-chain dumps, w₀(c_d) = v₀ EXACTLY, v₀ ≥ 1, and every (INV_l)
holds; at i = 0, w₀ = h₀ exactly.  SDYJ-SWEEP — the same arithmetic
engine-free on ≈ 10⁶ deterministic read-grids (chain lengths i ≤ 4,
all-g-1, gcd-filtered), 0 predicted violations, with counters for the
sharp corner v₀ = 1 and for integrality-load-bearing chains.
SDYJ-GAM — the engine's γ-values equal the S0.1 recursion on every
tower (the non-textual leg for the weight-recursion pin).]

Remark (why this fails at g₀ ≥ 2, and must).  At g₀ ≥ 2 the level-0
step has t₁-freedom t₁ ∈ [0, g₀): the dump is not forced and the
level-0 window widens to a₀ ≤ e₀g₀ − 1, so the chain can terminate at
v₀ = 0 — mass-cheap corrections are exactly the (SURV-K2) box's
recycle-economy headroom (WMULTDCX F2).  Nothing here touches g₀ ≥ 2.

## S3. SDY-L2: the multiplicative valuation ledger

**Lemma SDY-L2 (path valuation superadditivity).**  On TRACK,
(H1)–(H3), g₀ = 1, any d₀: every two-exit terminal cell C of T²
satisfies

    w₀(b_C)  ≥  (u₁ + u₁′) + u₀ + Σ_{c ∈ CE(C)} w₀(c_{d_c}) + X(C)
             =  ŵ + Σ_{c ∈ CE(C)} w₀(c_{d_c}) + X(C) ,

where X(C) := the number of π-junk edges on C's path, and c_{d_c} is
the digit cell consumed by correction c.  Equality holds on junk-free
paths (then every split takes its L-child and each step is EXACT).
*Proof.*  The root coefficient is π^{u₁+u₁′} exactly (W-D1: X₀ is an
identity, not a convention).  Promotion and exit edges carry b
UNCHANGED ([RMG] S2.2) — the valuation ledger has NO promotion terms:
this is why "promotion savings" cannot offset anything here.  The only
b-mutating edges are L-NORM splits: at a correction (b·c_{d_c}) and at
the stage-2 seeding (b·c_D, where EVERY d-cell has w₀(c_D) = u₀ at
(H3) ∧ g₀ = 1 — W-D2(iii), any d₀).  At each split, every child obeys
w₀(child) ≥ w₀(b) + w₀(other factor), with the L-child EXACT and
never absent (L-NORM(a)), the π-junk child ≥ +1 more (L-NORM(b)), and
the Φ₀Y-child ≥ +0 (L-NORM(c): coefficient π^w·Ŷ — the Y-child gains
EXPONENT mass at level 0, not valuation; its valuation gain may be
zero, and the instances realize zero).  Chain the inequalities along
the path; the junk-free case chains equalities.  ∎

[Machine: SDYJ-SUPER — the inequality on EVERY two-exit terminal of
every live row on both rosters (with X(C) = junk − Y₂ − Σ_c Y_c read
off the recording walk), and the EQUALITY on every junk-free terminal;
0 predicted violations.  SDYJ-CASC — ŵ = u₁ + u₁′ + u₀, residue ≠ 0,
line = β̂ on every cascade cell (the S-L1 shadow at d₀ = 2, first
dedicated exercise).]

## S4. SDY-L3 = (SD-YJ′), proved

**Lemma SDY-L3 ((SD-YJ′); the charged statement and its
strengthening).**  On TRACK, (H1)–(H3), g₀ = 1, ANY d₀, (STK),
c_{m−1} ≥ k: let C be a two-exit terminal cell at the cascade slot,
j⃗(C) = ĵ, other than Ĉ and the X-mate.  Then:

* (a) [the automatic clause, as charged] CE(C) ≠ ∅ and C is Φ₀Y-fed:
  junk(C) ≥ 1, with the correction economy in the (★)/SD-L1 shapes
  (Y₂ = 1 with one deficit-1 correction, or Y₂ = 0 with all
  corrections defc = 0, each e_i = 1 ∧ Y-child ∧ full dump);
* (b) [the payment — STRONGER than charged]
  w₀(C) ≥ ŵ + |CE(C)| + X(C) ≥ ŵ + 1;
* (c) [the charged conclusion] line(C, ĵ) = β̂ + E_m·(w₀(C) − ŵ)
  ≥ β̂ + E_m > β̂.

In particular EVERY cell at slot ĵ other than Ĉ (companion or X-mate)
has w₀ ≥ ŵ + 1 and line > β̂: the charged reading "junk ≥ 1 at fixed
slot forces line > β̂" holds a fortiori, but the gain is paid by the
corrections (SDY-L1), not by the junk — a junk edge alone can gain
zero valuation (the Y-child), and the realized companions confirm it:
their Y-edges gained nothing, their corrections gained exactly v₀.

*Proof.*  (a) is Reduction 2 (S1).  (b): SDY-L2 gives w₀(C) ≥ ŵ +
Σ_c w₀(c_{d_c}) + X(C); every correction consumes a digit cell of some
C₀^{(i_c)} (k_c = 0 at all-g-1), and SDY-L1 gives w₀(c_{d_c}) ≥ 1 for
every one, so Σ_c w₀(c_{d_c}) ≥ |CE(C)| ≥ 1.  (c): Reduction 1.  ∎

[Machine: SDYJ-COMP — clauses (a)(b)(c) + (★) + the SD-L1 shapes on
every realized cascade-slot companion on both rosters; SDYJ-NEP — the
β̂-line population at ĵ is exactly {Ĉ} on every g₀ = 1 ∧ (STK) live
row; 0 predicted violations either family.]

## S5. SDY-THM: SD-THM-A at every d₀ (the extension theorem)

**THEOREM SDY-THM.**  On TRACK, (H1)–(H3), g₀ = 1, (STK),
c_{m−1} ≥ k — d₀ FREE:

* **(i′) [the ĵ population]**  Every two-exit terminal cell at ĵ is
  the cascade cell Ĉ (at w₀ = ŵ exactly), or the X-mate (≤ 1,
  correction-free, junk ≥ 1, w₀ ≥ ŵ + 1), or a Φ₀Y-fed companion in
  the SDY-L3 shapes with w₀ ≥ ŵ + |CE| + X ≥ ŵ + 1.  [At d₀ = 1 the
  companion genre is empty (SD-L3 = L-NORM(c): no Φ₀Y-edge exists) and
  (i′) degenerates to SD-THM-A(i).]
* **(ii) [(NEP) at every d₀]**  The equal-line population at (ĵ, β̂)
  is the singleton {Ĉ}: the cascade has no equal-line partner.
* **(iii)**  The cascade slot survives netting at the cascade line:
  B_ĵ ≠ 0, w₀(B_ĵ) = ŵ, line(B_ĵ, ĵ) = β̂.
* **(iv) [(SURV-DISJ) on this locus]**  The disjunction holds — by the
  cascade leg, whatever the bottom stratum does.
* **(v) [(SURV)(i) on this locus]**  Under (RW) additionally: Q¹ ≠ 0.

*Proof.*  (i′): a two-exit terminal at ĵ with CE = ∅ is Ĉ or the
X-mate (Reduction 2); with CE ≠ ∅ it is a companion, and SDY-L3 gives
its shapes and floor.  (ii): by (i′) every non-Ĉ cell at ĵ has w₀ ≥
ŵ + 1, i.e. line ≥ β̂ + E_m > β̂ (Reduction 1).  (iii): B_ĵ = b_Ĉ +
Σ ±b_others with w₀(b_Ĉ) = ŵ < w₀(every other) — S-L0(b) at w₀ gives
B_ĵ ≠ 0 with w₀ = ŵ and line β̂ (equivalently S-L4(ii): the equal-line
subsum at β̂ is the single S-L1 term, residue b̄₀c̄_D ≠ 0).  (iv) is
(iii).  (v): (ii) is (NEP); S-THM(c) applies verbatim with (NEP)
supplied by theorem, exactly as at SD-THM-A(v).  ∎

The differences from SD-THM-A's proof are exactly two: clause (i)'s
"CE(C) = ∅ forced" (true only at d₀ = 1, where Y₂ ≡ Y_c ≡ 0 turns (★)
into Σ defc = 0 with every term ≥ 1) is replaced by the SDY-L3 floor on
the CE ≠ ∅ genre; and the X-mate's "same exponent vector" display is
not consumed (only its slot membership and valuation floor matter).
Everything else is the SD-THM-A architecture verbatim.

## S6. The honest consequence display

* **The (SD-YJ) box (SURVDISJ_PROOF S6): CLOSED** — not by excluding
  Φ₀Y-fed companions (they EXIST: 8 realized instances) but by proving
  them line-harmless.  The box's demand "exclude Φ₀Y-fed cascade-slot
  companions" was the WRONG target; the right target, (SD-YJ′), is
  proved.  The box's deficit-shape analysis stands and is consumed.
* **(SURV-DISJ)**: PROVED at attempt grade (capped) on
  TRACK ∧ (H1)–(H3) ∧ g₀ = 1 ∧ (STK) ∧ (c_{m−1} ≥ k) — ANY d₀ — by
  the cascade leg (SDY-THM(iv)).  The class-wide open set is now
  EXACTLY the (SURV-K2) box (g₀ ≥ 2 protected-group existence).  The
  g₀ = 1 leg is class-complete: no g₀ = 1 residual remains anywhere.
* **(NEP)**: a THEOREM on the full g₀ = 1 locus, every d₀
  (SDY-THM(ii)); its former d₀ = 1 pin was an artifact of the proof,
  not of the phenomenon.
* **(SURV-(m+1))(i)**: closed at the capped grade on
  (H1)–(H3) ∧ g₀ = 1 ∧ (STK) ∧ (RW), any d₀ (SDY-THM(v)).
* **LAW-DCX-(m+1) ON THE PINNED CLASS**: the pinned class of
  SURVDISJ_PROOF S8 DROPS ITS d₀ = 1 PIN: on TRACK ∧ (H1)–(H3) ∧
  g₀ = 1 ∧ (STK) ∧ (RW), for every m ≥ 2 and every d₀:
  c_{m−1} ≥ k ⟹ Q¹ ≠ 0 (this note) and c_{m−1} < k ⟹ Q¹ = 0 (E-THM†,
  which is g₀- and d₀-free on (H1)–(H3); W-D4† framing) — the law
  holds on that class at the capped attempt grade.  Class-wide,
  LAW-DCX-(m+1) REMAINS A CONJECTURE (the g₀ ≥ 2 leg).
* **What must still close before any acceptance-grade claim**, named:
  (1) the W arc (0/2 CLEAN — the binding cap); (2) the EMPTY arc (1/2);
  (3) the SURV_PROOF arc (0 CLEAN); (4) the SURVDISJ arc (1/2, Codex
  leg owed); (5) THIS note's own hostile arc (0/2 — fresh); (6) the
  (H2) on-TRACK discharge rider; (7) (RW) at m ≥ 3; (8) (STK) as an
  explicit pin; (9) the (SURV-K2) box; (10) the T-scope rider (H1) —
  see F-C: the realized companion instances all sit OUTSIDE (H1)'s
  sufficient condition, with T-TERM machine-certified per row;
  (11) (EMPTY-gen)/interior g ≥ 2 (program-wide out of scope).

## S7. Machine brackets (families, rosters, SEALED predictions)

`sdyj_checks.py`, single deterministic run, exact arithmetic, engines
md5-pinned byte-untouched and UNPATCHED (grb_order2_check dab62713…,
rmengine_pe_reimpl 103c1a9c…, empty_derive_checks 8fed9240…,
wmultdcx_stress 15315cca…, wmultdcx_derive_checks bea1a43d…,
survk2_derive_checks d8493ab9…; the construction runner
survdisj_construct.py d8001674… and its results json cdf2ce6f… pinned
as the replication reference).  Row tracing reuses the construction
runner's machinery (ED.walk + SK2.walk_rec reference/recording pair,
its seed and row-selection logic replicated verbatim).

**S7.1 The eleven families and their SEALED predictions (commit 1;
verdict appended at commit 2):**

    SDYJ-PIN    8 md5 pins green.                              [0 pred]
    SDYJ-GAM    engine γ/wΦ values = the S0.1 recursion,
                every tower, every level.                      [0 pred]
    SDYJ-DIG    every correction digit: single cell (i ≥ 1),
                forced v-chain dumps, w₀ = v₀ exactly, v₀ ≥ 1,
                (INV_l) all l; i = 0: w₀ = h₀.                 [0 pred]
    SDYJ-SWEEP  the v-chain floor engine-free on the full
                deterministic read-grids (lengths i = 1..4;
                e ≤ 8/6/5/4, h ≤ 9/7/6/5 resp., gcd-filtered,
                all-g-1): integrality, (INV_l), v₀ ≥ 1.        [0 pred]
    SDYJ-CASC   cascade cell: ŵ = u₁+u₁′+u₀, residue ≠ 0,
                line = β̂ (S-L1 shadow, any d₀).                [0 pred]
    SDYJ-SUPER  SDY-L2 inequality on every two-exit terminal;
                equality on junk-free terminals.               [0 pred]
    SDYJ-COMP   SDY-L3(a)(b)(c) + (★) + SD-L1 shapes on every
                realized companion.                            [0 pred]
    SDYJ-NEP    β̂-population at ĵ = {Ĉ} on every g₀ = 1 ∧
                (STK) live row.                                [0 pred]
    SDYJ-REP    the nine committed T3 towers re-trace to the
                construction unit's artifacts: same live keys,
                same per-row companion counts and cascade
                states, the 8 companions at the same (w₀,line). [0 pred]
    SDYJ-WALL   the d₀ = 3 capability wall reproduces: the
                committed tower chain hardcodes a QUADRATIC
                Φ₀-reduction whenever d₀ ≥ 2, so d₀ = 3 is
                engine-dark (F-D).                             [wall pred]
    HARNESS     engine-internal violations.                    [0 pred]

Measured (no seal): companion realizations on the fresh towers (pool
arithmetic — any count is a finding); the per-companion L/X-child
resolution census (F-E).

**S7.2 The fresh roster and the DISPLAYED v-chain predictions** (each
number below is hand-derived from SDY-L1's chain in this note and
SEALED as an exact machine prediction; the committed nine towers'
values are displayed alongside — the realized companion gains
w₀ − ŵ ∈ {1, 2} of the construction record are exactly the i = 1
values below plus 0 or 1 units of junk overshoot):

    tower     reads (e,h,g) levels 0..m         v₀ per level i ≥ 1
    YJ2F      (2,1)(2,1)|top(2,1)               i1: 2
    YJ3F      (2,1)(2,1)(2,1)|(2,1)             i1: 2   i2: 4
    YJ3FLT    (2,1)(1,1)(2,1)|(2,1)             i1: 1   i2: 3
    YJ3FLTB   (2,3)(1,1)(2,1)|(2,1)             i1: 2   i2: 6
    YJ3DPF    (3,1)(2,1)(2,1)|(2,1)             i1: 2   i2: 3
    YJ4FLT    (2,1)(1,1)(2,1)(2,1)|(2,1)        i1: 1   i2: 3   i3: 5
    YJ3Z      = YJ3FLT reads (Zp)               i1: 1   i2: 3
    YJ3F3     = YJ3FLT reads (p = 3)            i1: 1   i2: 3
    YJT1F     (2,1)(2,1)(2,1)|(1,1)             i1: 2   i2: 4
    ---- fresh ----
    YJX1  m3 p2 d0=2  (2,3)(1,3)(2,1)|(2,1)     i1: 3   i2: 8
    YJX2  m3 p3 d0=2  (3,1)(1,1)(2,1)|(2,1)     i1: 1   i2: 3
    YJX3  m3 p3 d0=2  (3,2)(1,1)(2,1)|(2,1)     i1: 1   i2: 5
    YJX4  m4 p2 d0=2  (2,1)(1,1)(1,1)(2,1)|(2,1) i1: 1  i2: 2   i3: 4
    YJX5  m3 p2 d0=1  (2,1)(1,1)(2,1)|(2,1)     i1: 1   i2: 3
    YJX6  m2 p2 d0=2  (2,1)(1,1)|(2,1)          i1: 1

YJX2/YJX3 are the razor-thin corners: there the naive rational bound
(γ₂ − (e₀−1)γ₁)/e₀ is 2/3 < 1 resp. 1 exactly, and the FORCED s₁
(1 resp. 2) lands v₀ = 1 — integrality doing the work the induction
says it does.  YJX5 is the d₀ = 1 control: same floor arithmetic, zero
Φ₀Y-edges, zero companions predicted there (SD-L3).

**S7.3 VERDICT (from artifacts; appended at commit 2).**  PENDING.

## S8. Claims table, dependency line, fences

| # | claim | grade | consumes |
|---|---|---|---|
| SDY-L1 | digit-valuation floor: every correction-digit cell has w₀ ≥ 1 at all-g-1; = the forced v-chain value; (INV_l) | PROVED (attempt, capped; (H2)–(H3) ∧ g₀ = 1) | [RMG] S2.2 + RM-GEN S2.1 inventory, L-GRID/S3.1, [ILN]† S0.1 weights |
| SDY-L2 | valuation superadditivity: w₀(term) ≥ ŵ + Σ w₀(c_d) + #π-junk; = on junk-free | PROVED (attempt, capped; (H1)–(H3) ∧ g₀ = 1, any d₀) | W-D1†, W-D2(iii)†, L-NORM(a)(b)(c), S2.2 |
| SDY-L3 | (SD-YJ′): companions are Φ₀Y-fed (junk ≥ 1) AND w₀ ≥ ŵ + CE + X ≥ ŵ + 1 ⟹ line > β̂ | PROVED (attempt, capped; + (STK) ∧ clause) | SDY-L1, SDY-L2, (★)†, SD-L1†, SD-L4†, S-L4(i)†, S-L4(iii)-uniq† |
| SDY-THM | SD-THM-A at EVERY d₀: ĵ population, (NEP), B_ĵ survives, (SURV-DISJ), +(RW) Q¹ ≠ 0 | PROVED (attempt, capped) | SDY-L3, S-L0†, S-L1†, S-L4(ii)†, S-THM(c)† |
| (SD-YJ) box | | **CLOSED** (superseded by SDY-L3/SDY-THM) | — |
| (SURV-DISJ) | class-wide | OPEN = exactly (SURV-K2); PROVED on TRACK ∧ (H1)–(H3) ∧ g₀ = 1 ∧ (STK) ∧ clause, any d₀ | — |
| LAW-DCX-(m+1) | on the pinned class, d₀ pin DROPPED | holds at capped attempt grade on TRACK ∧ (H1)–(H3) ∧ g₀ = 1 ∧ (STK) ∧ (RW), any d₀ | SDY-THM + E-THM† + W-D4† |

**Dependency line.**  Consumes: RMENGINE [RMG]† ACCEPTED (L-NORM(a)(b)
(c), S2.2 child inventory + C_k^{(i)} certified cells, L-CELL(i),
L-GRID/S3.1); WMULTDCX† 0/2 CLEAN — THE BINDING CAP (W-D1, W-D2,
W-D7; W-D5 only as the line-law context); SURVDISJ_PROOF† 1/2 CLEAN
(SD-L1, SD-L2/(★), SD-L4, SD-THM-A architecture); SURV_PROOF† 0 CLEAN
(S-L0, S-L1, S-L4(i)(ii)+(iii)-uniqueness, S-THM(c)); EMPTY_PROOF† 1/2
CLEAN (E-L6; E-THM in S6 only); [ILN]†/[IL3]† through those blocks (+
S0.1 weights as definitions).  Construction-unit artifacts (seal
84edf07/092471d): design input + instance evidence only.  Machine leg:
`sdyj_checks.py` + artifacts (md5s at commit 2).

**Fences.**
F-A. Pins per claim as displayed; nothing is claimed at g₀ ≥ 2, at
     interior g ≥ 2, or for (SURV-K2).  The SDY-L1 remark shows the
     floor FAILS structurally at g₀ ≥ 2 (t₁-freedom) — do not cite it
     there.
F-B. (STK) and the clause c_{m−1} ≥ k enter only through cascade
     existence (W-D7), as at SD-THM-A; both stay explicit pins.
F-C. (H1) T-scope is consumed ONLY for T-TERM/W-D0 (tree =
     canonical divisions); every per-path lemma here (SDY-L1/L2/L3) is
     scope-free.  DISCLOSURE: the flat-e₁ d₀ = 2 towers — the ONLY
     towers where companions have been realized — sit OUTSIDE (H1)'s
     sufficient condition (d₀ ≥ 2 with an interior e_i = 1); on them
     the tree/division identification is not proved but was
     machine-certified row-by-row (the construction unit's CON-ENG/
     CON-XWALK/CON-CONS, 0 violations; re-certified here).  SDY-THM's
     letter carries (H1); its instance record currently rides the
     per-row certificates.
F-D. d₀ = 3 is ENGINE-DARK: the committed tower chain hardcodes the
     Φ₀-reduction to a fixed quadratic whenever d₀ ≥ 2
     (grb_order2_check Tower2 __init__ — the d₀-analogue of the K2-ENG
     g₀ ≥ 3 pick wall, one slot over; no monkeypatch seam exists short
     of forking the constructor, out of this unit's scope and
     disclosed instead, family SDYJ-WALL).  The PROOF is uniform in d₀
     — d₀ enters only through L-NORM/E-L6 degree arguments that are
     any-d₀, and SDY-L1's arithmetic never mentions d₀ — so the gap is
     an instance-coverage gap only: no d₀ ≥ 3 instance record exists
     anywhere in the program (machine-dark corner, honestly labeled).
F-E. Cross-note observation (display precision, no erratum performed;
     the construction note is not touched per the charge): the
     construction note's S6 bullet "[Y₂ = 1: the correction rides its
     X-child, defc = 1]" is contradicted by its own committed
     artifacts — those companions carry junk = 1 accounted by the
     seeding Y-edge, and correction X-children increment junk, so the
     Y₂ = 1 corrections rode their L-CHILDREN (defc = 1 via dump 1,
     Y_c = 0).  The runner's companion census resolves this per
     instance (measured, no seal).
F-F. This note upgrades nothing class-wide beyond the displayed
     closures; (SURV-K2) and every acceptance leg named at S6 remain
     open.  The machine counters are instance evidence, never proof
     steps.
