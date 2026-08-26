# RB3's upward budget→height bridge — certificate findings, refutation, proof, nodes

Unit MBRIDGE, 2026-08-26. Enacts `docs/in-progress/BLOCKERS_PLAN_2026-08-26.md` §F3B rows
F3.6/F3.8 (the one genuinely-new `shadow_persistence` mechanism). Certificate:
`verification/rb3_bridge_cert.py`, log `verification/rb3_bridge_cert.log` —
**210 PASS / 0 FAIL** over six (frame, μ₂) blocks: `s2Tower` (p=2, u₂=5, E₂=10, δ=1) at
μ₂∈{2,3}; a margin-3 variant (u₂=7, E₂=14, δ=3); a lift-unit variant (resLift(1)=3); a p=3
mirror at μ₂∈{2,3}. Landed cross-checks reproduced: `s2Witness` j=0 digit height = 31,
`wtCoeff(2⁶,1,1) = 31`, `budgetFloor(3,0,1,1) = 6` tight (`C131uf.lean:207-294`).

Protocol-L rebinding used throughout: Φ′ = `F.key` (deg D′ = e₁f₁), Φ₂ = `composedKey T`
(deg D₂ = D′·e₂f₂), E₂ = e₂f₂u₂, δ = `T.margin` = u₂ − e₂D′h ≥ 1,
θ_j = `T.theta μ₂ j` = (μ₂−j)E₂ + δ, d = e₁e₂, w(a,b) = `slotOffset T a b` = a·e₂h + b·u₂,
`wtCoeff T c a b` = d·addVal(c) + w(a,b),
`dv2Hgt L A` = inf_b (e₂·stageHeight(dev Φ′ A b) + u₂·b) (`C11.lean:130`),
D_j(g) := `shadowDev T g j − dev Φ₂ g j` (the shadow discrepancy).

## 1. STOP-THE-LINE: the signed `shadow_persistence` is REFUTABLE as stated

The signed statement (`leanspec/Leanspec/ChapC.lean:3482-3494`) quantifies `hbudget` over
`j' < μ₂` only and carries **no degree hypothesis on `g`**. Take `g := Φ₂^μ₂`:

* `dev Φ₂ (Φ₂^μ₂) j' = 0` for every `j' < μ₂` (`dev_pow_self` + `if_neg` — exactly
  `C123r.lean`'s drain facts), so every `hbudget` leg reads
  `budgetFloor ≤ addVal 0 = ⊤`: **`hbudget` holds vacuously**.
* Clause 1 then asserts `θ_j + 1 ≤ dv2Hgt(D_j(Φ₂^μ₂))`, while the hypothesis
  `hc : TouchCert T hπ μ₂ j` (`leanspec/Leanspec/ChapC.lean:3470-3474`) is BY DEFINITION
  `dv2Hgt(D_j(Φ₂^μ₂)) = θ_j`. Since `θ_j` is a finite numeral cast, `θ_j + 1 ≤ θ_j` is
  false. So at ANY instance where `TouchCert` holds, the signed statement yields `False`.

TouchCert is not vacuous: the certificate finds it HOLDS at (s2Tower, μ₂=2, j=0) with
`D₀(Φ₂²) = 16·Φ′`, height 21 = θ₀ (hand-checkable: `biRead(Φ₂²) = Z⁴ − 8x̄Z² + 16Z + 32`,
`devQ` remainder `16Z` since `16x̄² = 32`, the x-carry `16x² = 16Φ′ + 32` being the census
overflow); also at (s2Tower, μ₂=3, j=1), height 21 = θ₁, and at the margin-3 variant
(μ₂=2, j=0), height 31 = θ₀. Where TouchCert fails the statement is uninstantiable, not
saved: e.g. (s2, μ₂=3, j=0) has key-power discrepancy height 35 ≠ 31 = θ₀.

**Amendment (required, honest, consumer-compatible):** insert
`(hdeg : g.natDegree < μ₂ * T.D₂)` before `hbudget`. This is automatic for the intended
instantiation `g = f − Φ₂^μ₂` (`f` monic of degree μ₂D₂, the `towerLocus_iff_budget`
shape, `leanspec/Leanspec/ChapC.lean:2030-2038`), excludes the defeat
(deg Φ₂^μ₂ = μ₂D₂ ⊀ μ₂D₂ — certificate P3c), and is exactly what the proof consumes
(step EN below). An alternative fix — extending `hbudget`'s quantifier to all `j'`
(then `budgetFloor(μ₂,j',0,0) = 1` for `j' ≥ μ₂` forces high digits one unit up) — also
blocks the defeat, but `hdeg` matches every consumer and mirrors `towerLocus_iff_budget`'s
own `hdeg`; recommend `hdeg`. Refutation is Lean-transcribable once a TouchCert instance
lands (§4, node F3.8.TC); until then it is a certificate-grade + hand-verified finding.

## 2. Mechanism read off the certificate tables

* **P0 (the +1's origin).** For `w(a,b) ≤ (μ₂−j')E₂`, both branches of
  `budgetFloor = (tgt+d−1)/d + [d ∣ tgt]` (tgt = (μ₂−j')E₂ − w) equal `⌊tgt/d⌋ + 1
  = ⌈(tgt+1)/d⌉`, the least `v` with `d·v + w ≥ (μ₂−j')E₂ + 1`. So `hbudget` ⟺ every
  nested slot of `g`'s j'-th Φ₂-digit sits STRICTLY above the entry line, by ≥ 1.
  Verified over the whole grid at all six blocks.
* **Extremal slot / where θ+1 is tight.** Single-slot g at exact floor: observed height
  = `mech(j₀,a,b,j) := (μ₂−j₀)E₂ + ε + j₀E₂ − jE₂ + δ` with per-slot excess
  `ε = d − (tgt mod d) ∈ {1..d}` — EQUALITY in every finite row that a single paid carry
  dominates (ultrametric equality-off-ties; only (2,1,0)/(2,1,1) at deep j exceed mech).
  `θ_j + 1` is attained exactly at the excess-1 inner-top lanes `(a,b) = (D′−1, e₂f₂−1)`
  with `j₀ = μ₂−1` (floor 1): tight slots (1,1,1,j) at μ₂=2, (2,1,1,j) at μ₂=3. The
  margin-3 frame has NO θ+1-tight slot (excess ≥ 1 but the +δ=3 ledger overshoots) —
  θ+1 is the honest uniform floor, tight iff δ-tight carries exist.
* **Vanishing rows.** Slots that never x-overflow (a = 0, or j₀ = 0 with b ≤ e₂f₂−1
  low) give D_j ≡ 0 (height ⊤): `censusOverflow` collects only PAID x-carries. The floor
  is an implication; ⊤ satisfies it.
* **N1 (the floor bites).** One valuation unit below floor at a carrying slot drops the
  height by exactly d = 4 below the tight value (e.g. 22 → 18 at s2 μ₂=2 slot (1,1,1)),
  landing `< θ+1` — 2–6 biting controls per block; `hbudget` fails at exactly the
  mutated slot each time.
* **P4 (clause 2).** At every TouchCert coordinate and every budgeted degree-bounded g
  tested (all tight singles + the all-slot sum): `dv2Hgt(D_j(Φ₂^μ₂ + g)) = θ_j` exactly.

## 3. The proof (amended F3.6, rigorous informal)

**Theorem (`shadow_discrepancy_floor_of_budget`, F3.6 amended).** Let O be a DVR,
π irreducible, F a KeyFrame, T a TowerDatum, μ₂ ∈ ℕ, j < μ₂, and g ∈ O[x] with
`hdeg : g.natDegree < μ₂·D₂` and `hbudget` as signed (over `j' < μ₂`). Then
`(θ_j + 1 : ℕ∞) ≤ dv2Hgt(T.levelDatum hπ) (shadowDev T g j − dev Φ₂ g j)`.

*Proof.* Five steps; every landed input named was signature-verified this session.

**AR (budget → strict weight).** For `j' < μ₂`, a, b, c:
`budgetFloor T μ₂ j' a b ≤ addVal c  →  ((μ₂−j')E₂ + 1 : ℕ∞) ≤ wtCoeff T c a b`.
Case c = 0: `wtCoeff_zero` gives ⊤ (`C131a.lean:56-60`). Case w(a,b) > (μ₂−j')E₂:
`wtCoeff ≥ w ≥ (μ₂−j')E₂+1`. Else by P0's identity `budgetFloor = ⌈(tgt+1)/d⌉`:
`d·addVal c ≥ d·⌈(tgt+1)/d⌉ ≥ tgt+1`, add w. (Pure ℕ/ℕ∞ arithmetic; the landed converse
direction is `budgetFloor_le_addVal_of_wtCoeff`, `C131ag.lean`, used at `C131uf.lean:247`.)

**EN (entry floor).** `hdeg` + `hbudget` ⟹ `(μ₂E₂ + 1 : ℕ∞) ≤ dv2Hgt(T.levelDatum hπ) g`.
Set `P := ∑_{j' ∈ range μ₂} xNF F (dev Φ₂ g j') * (K_T T)^{j'} ∈ O[X][Z]`. Then:
(i) `Polynomial.eval F.key P = g`: `eval F.key (xNF F A) = A` (digit reconstruction,
`sum_dev_eq`/`sum_dev_tail` genre, `C131w.lean:698-711`; `xNF_coeff`+`xDigit_eq_dev`
identify xNF's coefficients with `dev F.key` digits), `eval F.key (K_T T) = Φ₂`
(`eval_K_T`, used `C131w.lean:781`), and `∑_{j'<μ₂} dev Φ₂ g j' · Φ₂^{j'} = g` — the
reconstruction over range μ₂, valid EXACTLY because `hdeg` kills digits `j' ≥ μ₂`
(`dev_eq_zero_of_lt`, used `C131uf.lean:127`). **This is `hdeg`'s sole, indispensable
consumption — the unamended statement fails precisely here.**
(ii) `WT T P ≥ μ₂E₂ + 1`: `le_WT_sum` over j'; per summand `WT_mul` (`C131a`) splits off
`WT(K_T^{j'}) ≥ j'E₂` (`le_WT_K_T_pow`, used `C131w.lean:795`); for the digit factor,
`le_WT_of_forall_wtCoeff` (`C131w.lean:101-105`) + the coefficient identification
`((xNF F (dev Φ₂ g j')).coeff b).coeff a = (dev F.key (dev Φ₂ g j') b).coeff a` — the
EXACT `hbudget` subject — feed AR to get `≥ (μ₂−j')E₂ + 1`. Out-of-grid indices vanish
by the MONIC-DIVISION digit degree bounds, not by `hdeg` [Codex-audit fix]: every `dev φ`
digit is a `%ₘ` remainder, so `deg(dev F.key A b) < D′` kills a ≥ D′ and
`deg(dev Φ₂ g j') < D₂ = D′·e₂f₂` kills the b ≥ e₂f₂ key-digits of each Φ₂-digit
(landed: `natDegree_dev_lt`, `C130in.lean:113`, monic form; also `dev_natDegree_lt`,
`C109.lean:635`); zero coefficient gives ⊤ weight
(`wtCoeff_zero`). Sum: `(μ₂−j')E₂ + 1 + j'E₂ = μ₂E₂+1` for j' < μ₂.
(iii) `le_dv2Hgt_of_eval` (`C131w.lean:163-169`, abstract w) transports to `dv2Hgt g`.

**CE (census floor, w-abstract).** For any w ∈ ℕ:
`(w : ℕ∞) ≤ WT T (xNF F g)  →  ((w + δ : ℕ) : ℕ∞) ≤ dv2Hgt(censusOverflow T g)`.
This is the landed `dv2Hgt_censusOverflow_floor` (`C131w.lean:769-806`) with its floor
`μ₂ * T.E₂` renamed w: its only floor-dependent inputs are `quotDigit_floor_of_le` —
ALREADY abstract in w (`C131n.lean:213-217`) — and one ℕ-truncated omega line
`w + δ ≤ (w − j'E₂) + δ + j'E₂`. `WT_paidLift` (the `paid ≥ 1 ⟹ +δ` inner ledger,
`C131w.lean:751-764`) is already abstract. Textual generalization, no new mathematics.
The hypothesis in xNF form comes from EN via `dv2Hgt_eq_WT_phiNF` (Cnv11, C131t).

**PA (pay jE₂).** `dv2Hgt_dev_floor` (`C131w.lean:399-403`, abstract w) at
`A = censusOverflow T g`, `w = μ₂E₂ + 1 + δ`, `i = j`:
`dv2Hgt(dev Φ₂ (censusOverflow T g) j) ≥ μ₂E₂ + 1 + δ − jE₂ = (μ₂−j)E₂ + δ + 1 = θ_j + 1`
(j < μ₂; `Nat.sub_mul` + omega, the same cancellation as `shadow_floor`'s
`C131w.lean:866-869`).

**SP (splice).** `shadow_discrepancy T hπ g j` — fully general in g, NO locus/degree
hypothesis (`C131v.lean:674-679`) — rewrites `D_j(g) = −dev Φ₂ (censusOverflow T g) j`;
`dv2Hgt_neg` (`C131w.lean:157`) absorbs the sign. Chain EN → CE → PA. ∎

**Clause 2 (F3.8 assembly, for the record).** With `hc : TouchCert` and the amended
clause 1: `D_j` is additive in the polynomial argument (`shadowDev_add` — probe-proved,
`leanfinal/scratch/DEC4_check.lean:203-226`, being landed as F3.5 by unit BW1 — plus
`dev_add_of_monic`), so `D_j(Φ₂^μ₂ + g) = D_j(Φ₂^μ₂) + D_j(g)`; `hc` pins the first
height at θ_j exactly, clause 1 puts the second at ≥ θ_j+1 > θ_j, and
`dv2Hgt_add_eq_left_of_lt` (`C131y.lean:557-584`) gives equality θ_j. ∎
(Certificate P4 confirms exactness at every TouchCert coordinate.)

## 4. Formalization-trivial node decomposition (wired to the plan's F3.6/F3.8 rows)

| node | statement | named landed inputs | mechanism | size |
|---|---|---|---|---|
| F3.6.AR | `wtCoeff_strict_of_budgetFloor_le`: j' < μ₂ → `budgetFloor T μ₂ j' a b ≤ addVal c` → `((μ₂−j')E₂+1 : ℕ∞) ≤ wtCoeff T c a b` | `budgetFloor` (C52), `wtCoeff`/`wtCoeff_zero` (C131a), `slotOffset` (C50) | ceiling arithmetic ⌈(tgt+1)/d⌉; ENat case-split on c = 0 then omega | 25–45 |
| F3.6.EN1 | `eval_xNF : Polynomial.eval F.key (xNF F A) = A` (skip if already landed under another name — check C131t/C131v `collapse` glue first) | `sum_dev_eq`, `xNF_coeff`, `xDigit_eq_dev` | digit reconstruction | 10–20 |
| F3.6.EN | `dv2Hgt_of_budget`: hdeg → hbudget → `(μ₂E₂+1 : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) g` | F3.6.AR, F3.6.EN1, `le_WT_sum`, `WT_mul`, `le_WT_K_T_pow`, `le_WT_of_forall_wtCoeff`, `dev_eq_zero_of_lt`, `natDegree_dev_lt` (C130in), `eval_K_T`, `le_dv2Hgt_of_eval` | the P-lift `∑ xNF(digit)·K_T^{j'}`; per-slot AR; product/sum weight laws; eval transport. THE plan's "hbudget → WT" half | 60–100 |
| F3.6.CE | `dv2Hgt_censusOverflow_floor_of_entry` (w-abstract) | verbatim `C131w.lean:769-806` guts; `quotDigit_floor_of_le` already w-abstract | textual generalization + one omega | 30–45 |
| F3.6.SP | `shadow_discrepancy_floor_of_budget` (the amended F3.6, assembly) | `shadow_discrepancy`, `dv2Hgt_neg`, `dv2Hgt_dev_floor`, `dv2Hgt_eq_WT_phiNF`, θ arithmetic | `shadow_floor`'s skeleton (`C131w.lean:851-870`) at w = μ₂E₂+1 | 30–50 |
| F3.8.AM | AMENDED signed `shadow_persistence` (insert `hdeg` binder; both clauses) | F3.6.SP, F3.5 (`shadowDev_add`), `dev_add_of_monic`, `dv2Hgt_add_eq_left_of_lt`, `TouchCert` | clause 1 = F3.6.SP; clause 2 = additivity + strict-add | 25–45 |
| F3.8.TC (optional but recommended) | land `TouchCert (s2Tower) h2 2 0` (`D₀(Φ₂²) = 16Φ′`, height 21) + `shadow_persistence_unamended_refuted` (unamended ∀-statement → False) | s2 frame kit (C80/C97), `s2Witness_digit_height`'s toolkit (C131uf), `dev_pow_self`, `addVal_zero` | C131uf-scale digit computation; then the §1 defeat, ~20 lines | 60–100 |

Total 180–305 lines, inside the plan's 140–240 (F3.6) + 25–45 (F3.8) envelope once CE's
copy-discount is counted. Ordering: AR → EN1 → EN → CE → SP → (BW1's F3.5) → F3.8.AM →
F3.8.TC.

## 5. Open items (named, honest)

* **OPEN-AMEND**: the `hdeg` amendment to the signed `shadow_persistence` needs the
  statement-fence process (statement change; standing authority covers honest changes —
  this one removes a refutable signing). No Lean was edited by this unit.
* **OPEN-TC-LEAN**: the refutation is certificate-grade until F3.8.TC lands a TouchCert
  instance in Lean (§1's 16Φ′ computation is elementary and C131uf-style).
* **OPEN-F3.5**: clause 2 consumes `shadowDev_add` (probe-proved at
  `leanfinal/scratch/DEC4_check.lean:203-226`, being landed by concurrent unit BW1);
  clause 2 is conditional on that landing. Clause 1 (the bridge proper) does NOT use it.
* Codex adversarial pass (2026-08-26, fresh context, quote-and-classify): **no critical
  error**; three justification gaps = OPEN-TC-LEAN, OPEN-F3.5 above, and a degree-bound
  misattribution in step EN, fixed in place ([Codex-audit fix] marker).
* Model-fidelity notes: the certificate's `slotIdx 5 = 1` matches C15's junk-defaulting
  solve at (h,e₁) = (1,2); `resLift(1)` unit-independence is certified by the
  `s2unit3` block; frames are margin-1/margin-3, f₁ = f₂ = 1 — the PROOF nowhere uses
  these specializations, but a wider-frame certificate block (f₂ = 2) would be a cheap
  strengthening if desired.
