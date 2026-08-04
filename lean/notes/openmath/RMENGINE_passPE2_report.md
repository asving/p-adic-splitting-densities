# RMENGINE-PE2 — Fable round-2 HOSTILE content pass on RMENGINE_2026-08-08.md @ 8835d20

**Pass:** PE2 (round 2, fresh context; predecessor PE1 = `RMENGINE_passPE_report.md`).
**Date:** 2026-08-08 campaign (wallclock 2026-08-04).
**Object:** `lean/notes/openmath/RMENGINE_2026-08-08.md`, last-touch commit confirmed
`8835d20` (the round-1 repaired text; round-0 was bf18bfe).
**Charge:** (1) hostile discharge of every round-1 remedy — (a) L-NORM + the
re-derivation of L-LINE(ii)/(iii) and the DEV-(m)/T-tele residue steps through it;
(b) THE R2 EXTENSION: L-MU branch (b) near-ceiling induction re-derived, the
necessity cascade checked, the S4.2 inspection census verified by grep, and branch
(b) tested mechanically on d0 = 1 flat towers BEYOND the D7 shapes; (c) L-GRID +
L-VNZ proofs verified; (d) the R3 proved/heuristic split audited for downstream
consumption; (e) R5/R6 (COR-A at-acceptance coherence; claims-table completeness +
grade match). (2) Full spine re-verification as repaired. (3) No-weakening check
against `git diff bf18bfe 8835d20`.
**Referee:** PE1's `verification/openmath/rmengine_pe_reimpl.py` (read, not
mutated); my extension saved as a COPY at `verification/openmath/rmengine_pe2_ext.py`.

Findings are numbered PE2-1, PE2-2, ... Each carries a verbatim quote, a
classification (CRITICAL ERROR / JUSTIFICATION GAP / NOTE), and my derivation.
Sections are appended incrementally as verified.

---
## 1. Remedy discharges (charge 1, hostile)

### 1(a) Lemma L-NORM (R1 repair of PC-C1) — DISCHARGED, no finding

Statement re-derived from scratch. With b = π^{w₀(b)}·b̂, c = π^{w₀(c)}·ĉ,
b̂/ĉ primitive of degree < d₀: a nonzero primitive polynomial of degree < d₀
reduces to a nonzero element of k₀[x] of degree < deg ψ̄₀, hence nonzero in
the field K₀ = k₀[x]/(ψ̄₀); so b̄, c̄ ≠ 0 and b̄c̄ ≠ 0, and lift(b̄c̄) is
primitive — the L-child π^w·lift(b̄c̄) has w₀ EXACTLY w = w₀(b)+w₀(c) and is
never zero (L-NORM(a) confirmed). (b): π^{w+1}X̂ has w₀ ≥ w+1 trivially.
(c): at d₀ = 1, deg(b̂ĉ) ≤ 2d₀−2 = 0 < 1 and monic-division uniqueness
forces Ŷ = 0 (a degree-≥1 term Φ₀Ŷ cannot cancel against deg-0 remainders)
— confirmed. Upstream check: [IL3] S4.1 DIGIT-SPLIT read at source
(ITERLAW3_PROOF_2026-08-08.md:386) — stated for ALL α, β of deg < d₀, no
primitivity hypothesis; the note's parenthetical "for PRIMITIVE inputs" is a
conservative mis-paraphrase (see finding PE2-3, NOTE).

L-LINE(ii) re-derived through L-NORM: Δline(L-child) = E_m·w₀(c_d) +
Σ_{l<i} a_{d,l}Γ_l − (P_i−e_ik)Γ_i; scaling the realize on-line identity
E_i·w₀(c_d) + Σ a_{d,l}Γ_l^{(i)} = (g_i−k)γ_{i+1} by ∏_{i≤t<m}e_t, with
E_i·∏ = E_m, Γ_l^{(i)}·∏ = Γ_l, and (g_i−k)γ_{i+1}·∏ = e_i(g_i−k)Γ_i =
(P_i−e_ik)Γ_i — all three conversions re-checked exact — gives Δline = 0.
L-LINE(iii): π-child at the SAME exponents with w₀ ≥ w+1 gives Δline ≥
E_m > 0; Y-child w₀ ≥ w at j₀+1 gives Δline ≥ Γ₀ > 0; the i = 0 case with
the explicit π^{(g₀−k)h₀} riding outside the normalization: Δline =
E_m(g₀−k)h₀ − (P₀−e₀k)Γ₀ = 0 using Γ₀ = h₀E_m/e₀ — exact. The DEV-(m)
T-tele residue step "residue res(b̄)·res(c̄_d) — this is L-NORM(a)" is now
genuinely supported: the L-child's normalized residue is the product and
the child is never absent, which is what the ψ_i(z_{i+1})-collapse needs
(every k-term present with residue ψ̄-coefficient times res(b̄)).
Machine: V-LINE green on all 8 fresh flat towers (L-child w₀ == w₀(b)+w₀(c_d)
checked per child), plus PE1's 97 calls and the committed diag's D3.

### 1(b) THE R2 EXTENSION — L-MU branch (b) + the census — DISCHARGED, no finding

**The near-ceiling induction, re-derived.** Branch (b) (d₀ = 1, ρ₀ = P₀−1,
any e_i ≥ 1): the interval (S_i, w_{i−1}P_{i−1}) is a SUB-interval of the
(B_i)∧(A_i) region since w_i > S_i ⟹ w_ie_i ≥ w_i > S_i for e_i ≥ 1.
Nonemptiness ⟺ w_{i−1}P_{i−1} > S_i = S_{i−1} + w_{i−1}(P_{i−1}−1) ⟺
w_{i−1} > S_{i−1} — exactly the invariant one step down (re-derived; the
rearrangement is exact since ρ_{i−1} = P_{i−1}−1 for i−1 ≥ 1). Base
i = 1: (S₁, w₀P₀) = (P₀−1, P₀) nonempty — THIS is the single point where
d₀ = 1 enters (at d₀ ≥ 2, ρ₀ = P₀ and the base interval is empty).
Midpoint choice keeps w_i > S_i strictly; (A_i) strict; positivity from
w_i > S_i ≥ 0. No e-lower-bound consumed anywhere in the branch. SOUND.

**The necessity cascade.** From a flat level i: (B_i) at e_i = 1 reads
w_i > S_i; (A_i) then gives w_{i−1}P_{i−1} > S_i = S_{i−1} +
w_{i−1}(P_{i−1}−1) ⟹ w_{i−1} > S_{i−1}; each step down repeats the same
rearrangement (only (A_l) used below the flat level, ρ_l = P_l−1 for
l ≥ 1); bottom: w₀P₀ > S₁ = w₀ρ₀ ⟹ ρ₀ < P₀ ⟺ d₀ = 1. So flat-level
satisfiability ⟹ d₀ = 1, and branch (b) supplies the converse:
"satisfiable IFF d₀ = 1" CONFIRMED. The fence box's re-scoped claim ("at
d₀ ≥ 2 ... the (A_i)/(B_i) system is INFEASIBLE ... NO linear measure of
the L-MU family") is stated family-relative — honest.

**The S4.2 inspection census, verified by independent grep.** Every
"≥ 2" site in the note was enumerated (grep, 50 sites). On the proof
chain of the four clauses (S2.1/S2.2/S3.1/S3.2/S5.1/S5.2): ZERO e_i ≥ 2
consumptions found. The e ≥ 2 sites are exactly: L-MU branch (a) itself
(S4.1 — the censused consumer); the W-WIN m = 2 path argument (display,
consumed by nothing — C5/C14); the S4.1 consistency display (the sealed
m = 2 measure point — display, not a proof step); the LAW thresholds
2e₀/2e₁ (conjecture side); scope-definition and upstream-paste sites. The
class-level degeneracy claim "at a flat level s_i ≡ 0, ε_i ≡ 1" is
LITERALLY on record upstream: EXP-KIT(a) in ITERLAWN_PROOF (S3): "(At
e = 1: ℓ = 0, s ≡ 0, ε ≡ 1.)" — so L-ZMULT's carry cancellation, L-GRID's
congruences, and the T-tele shifts all degenerate as the census claims
(δ_l = ⌊(0+0)/1⌋ = 0; t_l = j_{l−1} ∈ ℤ). The [ILN] head paste grades
REALIZE/WELL-DEF "unconditional-generic" (quoted in-note), and the class
pin imposes gcd(e_j, h_j) = 1 only, satisfied at e = 1. "NO leg other
than L-MU consumed e_i ≥ 2": CONFIRMED.

**Machine test (the extension referee — section 3).** 8 fresh d₀ = 1 flat
towers NONE of which passes the old T-scope₀ predicate (verified per tower),
disjoint from D7's roster and PE1's M2C/M3C: e₀ = 1 towers (X1 double-degenerate
(1,1); X8 (1,2,1) mixed), g₀ = 2 + flat (X2), h₀ = 2/e₀ = 3 + flat (X3),
double-flat at ℤ₅ (X4), flat-mid at F₂[[t]] (X5), m = 4 mid-flat (X6) and
m = 4 double-mixed flat at levels 1 and 3 (X7). 67 engine calls, STRICT
verdict: all four box clauses exact, tree == canonical division, STRICT
μ-descent on every in-tree edge under the note's branch-(b) midpoint
weights, exact line quanta, 𝔷-kernel end-to-end, ZERO violations. Plus the
pure-arithmetic sweep: branch-(b) rule strict-satisfies the full system on
1080/1080 d₀ = 1 shapes (m ≤ 5, e_i ∈ {1,2,3}, three g-profiles);
225/225 d₀ = 2 flat shapes grid-INFEASIBLE (necessity corroborated);
branch-(a) rule 252/252 on its scope. v = 0 realized 0/67 (L-VNZ shadow).

### 1(c) Lemma L-GRID and Lemma L-VNZ — DISCHARGED, no finding

**L-GRID.** Re-derived: line_l := E_l·w₀(b) + Σ_{t<l} j_tΓ_t^{(l)}
satisfies line_l = e_{l−1}·line_{l−1} + j_{l−1}γ_l (checked: E_l =
e_{l−1}E_{l−1}; Γ_t^{(l)} = e_{l−1}Γ_t^{(l−1)} for t < l−1; Γ_{l−1}^{(l)} =
γ_l), so the λ-chain from β* = line(C) descends exactly through the
truncation lines, all integers. Grid congruence: s_l(λ_l) ≡ ℓ_{l−1}λ_l ≡
ℓ_{l−1}j_{l−1}γ_l ≡ ℓ_{l−1}j_{l−1}h_{l−1} ≡ j_{l−1} (mod e_{l−1}) — each
step from the S0.1 conventions (γ_l ≡ h_{l−1}, ℓh ≡ 1); s ≡ ℓβ mod e is
eq-(12-int)'s defining congruence (EXP-KIT(a) upstream displays
(s(β)−ℓβ)/e ∈ ℤ). So t_l ∈ ℤ at every l. SOUND — and it kills the (D3)
off-grid case and RM-GEN's old off-grid branch exactly as claimed. The
first-failure convention (stop at the largest failing l) is complete as a
definition, and by L-GRID it is only reachable at foreign targets where
the above-line branch governs — C20 verified.

**L-VNZ.** Re-derived: base m = 0 is the L-NORM(a) argument. Step: digits
f_j, 0 ≤ j ≤ P_{m−1}−1 (from deg f < deg Φ_m); on-grid slots j = s_m(λ) +
te_{m−1} give 0 ≤ t ≤ g_{m−1}−1 (checked: te ≤ eg−1−s ⟹ t ≤ g−1 in ℤ);
the read is Σ_t (ε/z-unit)·R_{m−1,slot}(f_j)·z_m^t with unit ∈ K_{m−1}^×
and coefficients in K_{m−1}; t ↔ j is a bijection on the grid, so there
is no cross-slot cancellation; a min-achieving digit j has λ =
e_{m−1}w_{m−1}(f_j) + jγ_m, hence (i) the grid congruence holds at that j
automatically (λ ≡ jγ_m ≡ jh_{m−1}) and (ii) its slot weight EQUALS
w_{m−1}(f_j), so its coefficient is a unit times R_{m−1,w(f_j)}(f_j) ≠ 0
by the IH; non-achieving digits contribute 0 (read below target),
harmless. A nonzero K_{m−1}-polynomial in z_m of degree < g_{m−1} =
deg ψ_{m−1} = [K_m:K_{m−1}] is nonzero in the field K_m (ψ_{m−1}
irreducible per the class pin's field towers). SOUND. Machine shadow
extended: v = 0 realized 0/67 on the fresh flat roster (on top of PE1's
0/97 and the diag's 0/319 + 0/30).

### 1(d) The R3 regrade (crossing law proved / pool identification heuristic) — DISCHARGED, no finding

The split is honest and correctly placed. The crossing law's proof by
child inventory is real: promotions are the only child type that raises a
higher-level exponent (correction children touch levels ≤ i with j_i
strictly dropping; exits leave), P_{l−1} consumed per unit delivered —
verified against S2.2's displayed children. The heuristic half (pool
identification, c_{l−1} recursion, support-containment) is marked
HEURISTIC at BOTH its sites (S6.2 and the S1 architecture point 3, each
with the r1 bracket). Downstream consumption audit: S8 row 11c basis "—";
the DAG routes LAW-DCX-(m+1) to COND-B only; RM-GEN/DEV-(m) (rows 7/8)
rest on rows 1–4 only; no proved clause consumes 11c. The μ-descent
citation inside the crossing law carries the T-scope pin (PC-G2's leak
cured). CLEAN.

### 1(e) R5/R6 — COR-A coherent; claims table: ONE GAP + notes

**COR-A (R5).** The at-acceptance qualifier is now coherent at all four
surfaces: headline ("at acceptance only — S7.1"), the S7.1 inline LEDGER
STATUS block, S8 row 12 ("LEDGER APPLICATION at acceptance only"), S11
consumers ("at acceptance only"). The n = 1, 2 correction is right: the
call family 2 ≤ m ≤ n−1 is empty there, and I re-derived the n ≥ 3
exact-union claim: ∧_{m=2}^{n−1} T-scope(m) = d₀ = 1 ∨ (e₀ ≥ 2 ∧ e_i ≥ 2
∀ 1 ≤ i ≤ n−2) — distributing the conjunction over the disjunction gives
exactly T-class(n) as displayed. The e_{n−1}-absence remark (flat-top
call sites) is consistent: the level-(n−1) engine's own scope concerns
levels ≤ n−2. NO finding.

**Claims table (R6).** Grade-vs-body: every S8 row checked against its
body site — all match (row 4's amended scope = S4.1's; row 6's complement
form is the exact complement of T-scope; rows 11a/b/c match S6.2's split;
row 12 matches S7.1). Completeness: I ran the charter's own census
(only/never/nothing/free/self-contained/automatic, 112 raw hits,
whitespace-normalized) and the table is STILL not exhaustive as
chartered — see finding PE2-1 (GAP). Also the head bracket says
"claims table completed (C15–C19)" where S8 and the repair record say
C15–C22 — see PE2-2 (NOTE).

## 2. Full spine re-verification (charge 2)

* **L-CANON / L-CELL / L-EXACT:** re-checked (monic-division uniqueness;
  deg Q < deg Φ_m from deg(fĈ_m) < 2deg Φ_m; the exit-cofactor structural
  remark makes L-EXACT window-free — C4 stands).
* **μ-induction, BOTH branches:** branch (a) re-derived (nonemptiness
  w_{i−1}P_{i−1}e_i ≥ 2w_{i−1}P_{i−1} > S_{i−1} + w_{i−1}P_{i−1} ≥ S_i,
  using the (B_{i−1}) invariant and ρ ≤ P; base (ρ₀/e₁, P₀) nonempty at
  e₁ ≥ 2); branch (b) per 1(b). The combined-scope algebra checked:
  [(a) ∧ (e₀ ≥ 2 ∨ d₀ = 1)] ∨ (b) = amended T-scope exactly. The three
  descent legs re-checked, including the level-1 corner Δj₀ ≤ −e₀ +
  [d₀ ≥ 2] and the Y-child absence at d₀ = 1 (L-NORM(c)). Well-foundedness
  via the common denominator. SOUND.
* **𝔷-mult self-curing (L-ZMULT):** re-derived; δ_l ∈ {0,1} from s-values
  in [0, e−1]; t_l^Σ = t_l + t_l′ + δ_l; the t-leg z_l^{+δ_l} cancels
  EXP-KIT(b)'s ε-leg z_l^{−δ_l} at l ≤ m−1 (upstream statement re-read:
  ε(β)ε(β′) = z^δ·ε(β+β′) — matches); the top level has a t-leg and no
  ε-leg, leaving exactly z_m^{ε̃}. SOUND.
* **Line quanta (L-LINE):** (i) re-derived via γ_{i+2} = e_{i+1}w_{i+1}Φ_{i+1}
  + h_{i+1} and w_{i+1}Φ_{i+1} = P_iγ_{i+1}: quantum h_{i+1}∏_{i+1<t<m}e_t;
  exit drop = P_{m−1}γ_m = w_mΦ_m. (ii)/(iii)/(iv) per 1(a). SOUND.
* **T-tele:** T-tele(1): the child chain agrees at levels ≥ 2 (only j₀
  changes), t₁ shifts by k−g₀, no ε-leg touches λ₀; Σ_kψ̄₀,k z₁^{k−g₀} =
  z₁^{−g₀}(ψ₀(z₁)−z₁^{g₀}) = −1 with the correction sign — collapse exact.
  T-tele(i+1): the child's level-≤i data IS the product shape (G-part at
  λ_i) ⊕ (d-cell at β_k) — j_i belongs to the level-(i+1) t-leg, not the
  ≤i chain, resolving the one place I probed for an indexing slip;
  L-ZMULT-at-level-i produces z_i^{ε̃_k} with ε̃_k = ⌊(s_i(λ_i)+s_i(β_k))/
  e_{i−1}⌋; EPS-MULT + ε_i(β_k)τ_k = ψ_{i,k} (realize (R3)) collapse the
  k-sum via ψ_i(z_{i+1}) = 0. B-READ on C_k^{(i)} inside the k-sum is
  legitimate (finite sums, d-cells on-line on-grid per prep-checked
  realize structure). SOUND.
* **DEV-(m):** the three (D3) cases with the off-grid case EMPTY via
  L-GRID (the converse-integrality appeal is verified DELETED from the
  text); induction carrier = μ (well-founded on T-scope); (D2)'s exit leg
  via the single-digit remark. SOUND.
* **RM-GEN:** (C-W_R)/(C-W_Q)/(C-EPS)/(C-READ) re-walked; the deleted
  "off-grid x-cells" branch is verified gone; ε′ uniformity across
  on-line x-cells holds (shared target pair). SOUND.
* **LAW-DCX-(m+1) sealed-not-proved at EVERY site:** grep-audited
  (headline, head declaration, S1 pt 3, S6.1 STATUS + specialization
  audit, S6.2, S8 row 10, S9 D5/D6 standing lines, S10, S11 DAG, C12) —
  conjecture/sealed grade present at each; the m = 1 and m = 2
  specializations re-checked exact (u₁ = (γ₃ − s₂(γ₃)γ₂)/e₁ = DCX3's u₀).
  L-CAP re-proved (pool₁ ≤ 3e₀−3 ⟹ c₁ ≤ 2; pool_l ≤ 3e_{l−1}−1 ⟹ c_l ≤ 2;
  e = 1 branch trivial). W-MULT-DCX-m stands conditional (S7.2), consumed
  by nothing proved.
* **T-scope form at every site:** headline (L36), the OFF-complement
  (L51: d₀ ≥ 2 ∧ (e₀ = 1 ∨ ∃ e_i = 1) — the exact complement), S4.2
  (L625), S5.1/S5.2 (L699/L795), S7.1 T-class (L946, i ≤ n−2 form), S8
  rows 4/6/7/8, S9 rosters (RME3A/B/C all-e≥2 + D7 all-d₀=1), S10
  (L1149), S11 (L1205), COR-A headline (L66). ALL carry the amended form;
  no site retains T-scope₀. CONSISTENT.
* **m = 1 reproduction:** T-scope(1) = e₀ ≥ 2 ∨ d₀ = 1 = the [IL3] RM-1
  scope of record; the m = 1 DEV coincidence remark checked (promotion =
  exit; μ = j₀-descent; e₀-scope agreement exact).

## 3. Machine tests (what ran, actuals)

1. **Commit + object:** `git log -1` on the note → 8835d20 (confirmed).
2. **Committed diagnostic re-run** (`rmengine_diag.py`, md5
   c50c08e3350c2f3f1e9aa50df7914463 == the note's D7-record pin): exit 0;
   output byte-exact vs committed `rmengine_diag_output.txt` (md5
   d9118f5a52a5ad8fc87beca4ce00b4fe == the note's pin) modulo the volatile
   `elapsed` float; all six GREEN verdict lines + D5 census reproduced.
3. **PE1 referee integrity:** `rmengine_pe_reimpl.py` md5
   103c1a9c99e2b4a3e8b63c93cbf87e25 == PE1's provenance pin — untouched;
   my extension is a separate file importing it read-only.
4. **The PE2 extension** `verification/openmath/rmengine_pe2_ext.py`
   (md5 574f87d89fae5794bede7e0b38121877; output
   `rmengine_pe2_ext_output.txt` md5 663fcb11cdc968dade8cbe756c0f7208;
   exit 0, 0.5 s). Legs and actuals:
   * XA — 8 fresh d₀ = 1 flat towers (roster in 1(b); every one fails the
     OLD T-scope₀ predicate and passes the amended one): 67 engine calls,
     STRICT verdict on V-BOX/V-MU/V-CONS/V-LINE/V-ZH/V-ID — GREEN,
     0 violations everywhere. Branch-(b) weights per tower, e.g.
     X2 (1, 7/2); X4 (1, 3/2, 5/4); X6 (1, 3/2, 11/4, 21/8);
     X7 (1, 3/2, 5/4, 19/8); X8 (1, 1/2, 3/4) — all (A_i)/(B_i)-strict
     with the invariant w_i > S_i checked. Trees up to 1824 nodes (X6:
     786 promotions, 914 corr-L children incl. corrections AT flat
     levels), 0 non-descending μ-edges anywhere. LAW-DCX censuses on the
     flat shapes: 0 mismatches (25 live rows total, all chain-fed).
   * XB(i) — branch-(b) rule: 1080 d₀ = 1 shapes (m = 2..5,
     e ∈ {1,2,3}^m, g-profiles (1..1)/(2,1..)/(2..2)), 0 failures.
   * XB(ii) — necessity: 225 d₀ = 2 shapes with a flat level, full-system
     grid search INFEASIBLE on all (0 feasible) — corroborates the
     cascade.
   * XB(iii) — branch-(a) rule on its scope (all e_i ≥ 2 for i ≥ 1, any
     e₀, d₀ ∈ {1,2}): 252 shapes, 0 failures.
5. **Grep censuses:** T-scope/T-class sites (charge-2 bullet above);
   "≥ 2" e-bound census (50 sites, 1(b)); only/never/nothing/free/
   self-contained/automatic census (112 raw hits → PE2-1); LAW-grade
   sites; upstream DIGIT-SPLIT/EXP-KIT statements read at source.

## 4. No-weakening check (charge 3)

`git diff bf18bfe 8835d20` on the note (511+/202−), all grade-bearing
lines extracted. Grade movements found: title/headline/S4/S8 rows
4/6/7/8 — SCOPE WIDENED (d₀ = 1 flats OPEN → PROVED; fence narrowed to
d₀ ≥ 2): strengthenings. New PROVED rows 1a/2a/2b (L-NORM/L-GRID/L-VNZ).
Row 3 basis gains L-NORM (dependency made honest). Scope remark (ii)
"v = 0 legal" → L-VNZ v ≠ 0 forced: strengthening. COR-A: n = 1, 2 now
carry the FULL accepted scopes (previously over-constrained by a
spurious T-condition) + the at-acceptance rider: strengthening +
honesty. The only DOWNGRADES: (i) row 11 "L-CAP + the floor-form
derivation | PROVED, generic" → 11a PROVED / 11b PROVED / 11c
**HEURISTIC** — this is PC-G2's repair itself: the floor-form pool
identification was never proved, so no genuinely-proved content is lost;
(ii) row 5 L-LEX "PROVED (as scoped)" → REMARK — its content (the
σ-tiebreak) is retained verbatim in S4.2 and its sole consumer
(termination of the m = 2, e₁ = 1 ∧ d₀ = 1 shape) is now covered by the
STRONGER branch-(b) strict descent. LAW-DCX-(m+1) grades verified
untouched (conjecture at m ≥ 2 on both sides of the diff).
**CONFIRMED: no genuinely proved clause was weakened; every theorem
statement's scope moved monotonically outward.** One wording remark: the
tail sentence "the only statement changes are the T-scope/T-class
STRENGTHENING ... and the L-LEX regrade" does not name the row-11
GRADE change; defensible (a grade is not a statement, and the regrade is
disclosed in the repair-record table eight lines above), so no finding.

## 5. Findings

**PE2-1 [JUSTIFICATION GAP — charter completeness; no chain impact].**
S8 dependency-claims table charter: "every 'only/never/nothing/
free/self-contained/automatic' claim of this note, enumerated ...
[r1 ...: rows C15–C22 added from a fresh full-text census of the
repaired text]". My independent census (112 raw keyword hits,
whitespace-normalized) finds the table STILL not exhaustive as
chartered. In-scope absentees, each verified TRUE by me (so nothing
downstream is threatened): (i) L-MONO's "**the on-line skeleton at
target λ + γ_{m+1} is PROMOTION-FREE and junk-free: carry depth 0**"
(S3.2, echoed in S1 point 2 "PROMOTION-FREE: carry depth 0") — a
load-bearing proved claim of exactly the C18/C19 genre, uncovered by any
C-row; (ii) "L-EXACT is scope-free" (S4.2 census) and "(L-LINE(i),
scope-free)" (S6.2) — the C4/C7 genre; (iii) "proved there,
engine-free" (S1 manifest + L-NORM) — the anti-circularity rider for
DIGIT-SPLIT; (iv) the S4.2 census-internal "only"s ("valuation +
division arithmetic only", "needs only h ≥ 1", "gcd(e_j, h_j) = 1
only"). Same finding class as PC-G3, one round later, smaller residue;
the exhaustiveness claim as re-stated at r1 is not yet true.

**PE2-2 [NOTE — internal metadata inconsistency].** The head repair
bracket says "**R6** ... claims table completed (C15–C19)" while the S8
preamble and the repair-record table both say "rows C15–C22 added"; and
rows C21/C22 carry no [r1] tag although the composed table had only
C1–C14 (PE1's census: "All 14 grep keys located"). Cosmetic; the table
itself is the authoritative surface.

**PE2-3 [NOTE — citation paraphrase].** L-NORM cites "DIGIT-SPLIT
([IL3]† S4.1: for PRIMITIVE inputs, αβ = lift(q(α)q(β)) + πX + Φ₀Y ...)".
The upstream lemma (ITERLAW3_PROOF_2026-08-08.md:386) is stated and
proved for ALL α, β of degree < d₀ with NO primitivity hypothesis;
primitivity is where the split is USEFUL (nonzero L-child), not a
validity condition. Conservative direction (the note consumes it only on
primitive inputs, where it certainly holds); no math impact.

## 6. Verdict block

The round-1 repairs all DISCHARGE under hostile re-derivation: L-NORM is
correct and complete and L-LINE(ii)/(iii) + the DEV-(m)/T-tele residue
steps genuinely route through it; the R2 extension's branch-(b)
near-ceiling induction is sound (invariant re-derived, necessity cascade
confirmed as an iff, inspection census independently verified by grep
and by 67 zero-violation engine calls on 8 fresh flat towers including
e₀ = 1, g₀ = 2, h₀ = 2, m = 4, and cross-ring shapes, plus a
1080-shape arithmetic sweep); L-GRID and L-VNZ are proved; the
proved/heuristic split of S6.2 is honest with no proved consumer of the
heuristic half; COR-A is coherent; the no-weakening claim is confirmed
against the actual diff. The spine as repaired verifies end-to-end. The
sole surviving defect is a charter-level completeness shortfall in the
dependency-claims table (PE2-1) plus two cosmetic notes — no critical
errors, no false mathematical claim found.

RMENGINE-PE2 FINDINGS: 0 critical, 1 gaps
VERDICT: GAPS-ONLY
