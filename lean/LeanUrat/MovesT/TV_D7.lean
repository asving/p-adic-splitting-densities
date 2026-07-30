/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.Defs

/-! # TV-D7 — the `HistLawful` conjunct census at the planned two-node literals

BRIDGE CAMPAIGN unit **TV-D7** (area BP3, cluster D; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.D + §4 [REV 2, findings 2 + 10];
bound by `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`). **GATE UNIT
(countermodel/census) — EXECUTED, no `sorry`**: runs BEFORE TV-D4/TV-D5 and
pre-verifies the ¬-prover's script conjunct by conjunct.

## Dependency status (recorded honestly)

`deps: D6 (needs σ₁'s data)`. TV-D6 has NOT landed: BP2's HK-15/HK-16
(`HC2/HK15_gateChildCarrier.lean`, `HC2/HK16.lean`) are E-phase skeletons with
`sorry` bodies at gate time. The census therefore runs at the PLANNED literals
— G1 record #7's data columns plus σ₁'s STATED pins (HK-15 header: key
`fq = X² + 2X + 4` of degree 2; `Nat.card ↥σ₁.K = 4`):

    node 0 (BP3's own literal, §3.D):  card K₀ = 2,  g₀ := 1 (deg-1 irred ψ),
                                       Φ₀ deg 1 (bStage-keyed), Dwidth₀ = 1
    node 1 (σ₁-keyed):                 card K₁ = 4,  Φ₁ = fq deg 2, Dwidth₁ = 2
    p = 2, n = toyN = 2

None of the census verdicts consumes a `sorry`d value: every lemma below is
stated at the literal NUMBERS. RE-RUN NOTE: when HK-15/16 land P-phase and
TV-D6 pins `Nat.card ↥σ₁.K = 4` as a named lemma, the pins feed
`censusD7_wchain_refutes` directly; no verdict here can change unless a STATED
pin of σ₁ changes (in which case this gate must be re-executed).

## The census table (`HistLawful 2 toyN` roster, MovesT/Defs.lean:146)

Verdicts at the literals; free data (e, h, s0, wSide, μ, slopes, γ, u*, a)
instantiated at the explicit admissible pin row
    node 0: e=2, h=1, (s,t)=(0,1), s0=0, wSide=2, μ=1, slope=1/2, u*=0, γ=2, a=−1
    node 1: e=1, h=3, (s,t)=(1,0), s0=0, wSide=1, μ=1, slope=3/4, u*=0, γ=3, a=0
(e₀ = 2 is FORCED by chain clause (b) at the stated key degrees:
Dwidth₁ = 2 = e₀·g₀·Dwidth₀ = e₀·1·1; every other free datum has slack.)

| # | conjunct (Defs.lean:146 order)  | at the literals           | verdict |
|---|---------------------------------|---------------------------|---------|
| 1 | NodeDataLawful: 1 ≤ e,g,μ       | 1 ≤ 2,1,1 / 1 ≤ 1,1,1     | PASS (satRow) |
| 1'| NodeDataLawful p-pow, node 0    | 2 = 2^(factorization 2 2) | PASS (ppow_K0) |
| 1"| NodeDataLawful p-pow, node 1    | 4 = 2^(factorization 4 2) | **PASS** (ppow_K1) |
| 2 | root key degree: deg Φ₀ = 1     | 1 = 1 (bStage-keyed)      | PASS (stated pin) |
| 3 | w₀ = 1: card K₀ = p             | 2 = 2                     | PASS (satRow) |
| 4 | slope tie (nodes 0, 1)          | (1/2)·(2·1·1) = 1; (3/4)·(1·2·2) = 3 | PASS (satRow) |
| 5 | γ-tie (nodes 0, 1)              | 2 = 2·(1·0)+(0+2)·1; 3 = 1·(2·0)+(0+1)·3 | PASS (satRow) |
| 6 | anchor / e∣wSide / gμ ≤ wSide/e | 2·(−1) = 0 − bezT 2 1·2;  | PASS (satRow) |
|   |                                 | 1·0 = 0 − bezT 1 3·3;     |         |
|   |                                 | 2∣2, 1∣1; 1·1 ≤ 1 (both)  |         |
| 7a| chain: s0₁+wSide₁ ≤ μ₀          | 0+1 ≤ 1                   | PASS (satRow) |
| 7b| chain: Dwidth₁ = e₀·g₀·Dwidth₀  | 2 = 2·1·1                 | PASS (satRow) |
| 7c| chain: slope₀ < slope₁          | 1/2 < 3/4                 | PASS (satRow) |
| 7d| chain: **W-MULT** card K₁ = card K₀ ^ g₀ | **4 = 2¹**       | **FAIL** (wmult_fails) |
| 8 | root width: s0₀+wSide₀ ≤ n      | 0+2 ≤ 2                   | PASS (satRow) |
| 9 | MONIC-LEAD: s0₀+wSide₀ = n →    | top digit ≠ 0 (`hpatTop`) in the card-2 K₀   | PASS |
|   |   top sideDigit = 1             | forces it = 1 (unique nonzero element)       |      |

(verdict names abbreviate `censusD7_satRow` / `censusD7_nodeData_ppow_K0` /
`censusD7_nodeData_ppow_K1` / `censusD7_wmult_fails` below; row 1" is the
clause the adversarial review worried the refutation might rest on — finding
2's worry, discharged: it PASSES, so it is NOT the violated conjunct.)

CENSUS VERDICT: exactly ONE conjunct fails at the literals — the REV 4
W-MULTIPLICATIVITY chain sub-clause 7d, forced false by the PINNED columns
(card K₀, card K₁, g₀) = (2, 4, 1) alone, independent of every free datum and
of n (the gate lemma is proved for ALL n and ALL carriers F). All other
conjuncts are jointly satisfiable at the explicit pin row. **The E-3
contingency does NOT fire**: `toy_v8_wchain` survives as stated, refutable by
a NON-artifact clause (the K-card/g tie, not root-width or any node-local
clause).

## The g₀ = 1 node-0 pin: well-typedness against `Node`'s full law roster

Roster scan (MovesC/Defs.lean:361-458), every g-mentioning law:
* `hg : 1 ≤ g` — holds at g = 1 (`censusD7_satRow`);
* `hψdeg : ψ.natDegree = g` — the ONLY data tie: needs a deg-1 monic
  irreducible ψ; witness compiled over ANY field: `censusD7_g1_psi_admissible`
  (ψ := X − C c; in particular over the card-2 K₀);
* `hspecInc : species = increment → 1 < e·g` — at node 0 the species is ROOT
  (`History.root_iff` at j = 0), so vacuous; (also: e₀·g₀ = 2 > 1 anyway);
* `hspecRec`, `hspecRecCenter` — root species, vacuous.
No other law mentions `g` (hψmonic/hψirr are satisfied by the same deg-1
witness; hpat0/hpatTop by pat ≡ 1, nonzero in K₀; hbezCanon/hbez by
(s,t) = (0,1) at (e,h) = (2,1); hDwidth by Dwidth₀ = deg Φ₀ = 1; hEdvd by
2 ∣ 2; hAnchor by 2·(−1) = 0 − 1·2 at t₀ = 1 = bezT 2 1). §3.D's read is
CONFIRMED at the literals: nothing blocks the g₀ = 1 pin.

## The gate (D5's pre-verified script)

`censusD7_wchain_refutes`: for EVERY history over EVERY finite-field carrier
whose first two nodes carry the pinned columns, `HistLawful 2 n` FAILS — by
projecting chain sub-clause 7d at i = 0 and closing `4 = 2¹` with `norm_num`.
TV-D5 instantiates it at `twoNodeKcardH` (once TV-D4 lands, behind the E-2
ruling) with n := toyN; the violated conjunct is certified BY NAME
(W-MULTIPLICATIVITY), per the D5 unit spec.

FENCE DISCIPLINE: this file does NOT import `G1_toyGate` (where
`twoNodeKcardH`/`toy_v8_wchain` stand `sorry`d); the census proves statements
of the SAME polarity as the sorried ¬-goal (evidence FOR it), so no compiled
negation witness coexists with an un-repaired universal.

deps: D6 (NOT landed — census run at the stated literals, see above).
Consumed by: TV-D4, TV-D5. difficulty: routine-opus (executed). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ## Census row 1': the NodeDataLawful p-power clause at node 0 — PASSES -/

/-- TV-D7 census (row 1'): node 0's `NodeDataLawful` p-power clause at the
literal `card K₀ = 2`: `2 = 2 ^ ((2).factorization 2)` — PASS. -/
theorem censusD7_nodeData_ppow_K0 : (2 : ℕ) = 2 ^ ((2 : ℕ).factorization 2) := by
  rw [Nat.Prime.factorization_self Nat.prime_two]; norm_num

/-- TV-D7 census (row 1"): node 1's `NodeDataLawful` p-power clause at the
literal `card K₁ = 4`: `4 = 2 ^ ((4).factorization 2)` — **PASS** (4 = 2² with
factorization exponent 2). This is the clause the adversarial review worried
the refutation might rest on (finding 2); the census certifies it PASSES, so
the refutation rests on the W-multiplicativity chain clause alone. -/
theorem censusD7_nodeData_ppow_K1 : (4 : ℕ) = 2 ^ ((4 : ℕ).factorization 2) := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.Prime.factorization_self Nat.prime_two]

/-! ## Census row 7d: the W-MULTIPLICATIVITY sub-clause — FAILS -/

/-- TV-D7 census (row 7d, THE TARGET): the REV 4 W-MULTIPLICATIVITY chain
sub-clause `Nat.card K₁ = Nat.card K₀ ^ g₀` at the pinned literals
`(card K₀, card K₁, g₀) = (2, 4, 1)` demands `4 = 2 ^ 1` — **FALSE**.
This is the exact sub-clause TV-D5's ¬-prover refutes. -/
theorem censusD7_wmult_fails : ¬ ((4 : ℕ) = 2 ^ 1) := by norm_num

/-! ## The remaining numeric clauses at the explicit pin row — all PASS -/

/-- TV-D7 census (rows 1, 3, 4, 5, 6, 7a, 7b, 7c, 8 — every OTHER numeric
clause of the `HistLawful 2 toyN` roster, instantiated at the explicit
admissible pin row of the module docstring): jointly satisfiable, so the
TV-D5 refutation does NOT rest on an artifact clause (root-width included:
`0 + 2 ≤ toyN` holds). Conjunct order follows the census table. -/
theorem censusD7_satRow :
    -- row 1: NodeDataLawful e,g,μ ≥ 1 at both nodes (g₀ = 1 pinned)
    ((1 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 1) ∧ (1 ≤ 1 ∧ 1 ≤ 1 ∧ 1 ≤ 1)) ∧
    -- row 3: w₀ = 1, card K₀ = p
    (2 : ℕ) = 2 ∧
    -- row 4: slope ties, node 0 then node 1 (STR₀ = 1, STR₁ = e₀ = 2)
    ((1 / 2 : ℚ) * ((2 : ℚ) * 1 * 1) = 1 ∧ (3 / 4 : ℚ) * ((1 : ℚ) * 2 * 2) = 3) ∧
    -- row 5: γ-ties, node 0 then node 1
    (((2 : ℤ) : ℚ) = (2 : ℚ) * ((1 : ℚ) * 0) + (((0 + 2 : ℕ)) : ℚ) * (1 : ℚ) ∧
      ((3 : ℤ) : ℚ) = (1 : ℚ) * ((2 : ℚ) * 0) + (((0 + 1 : ℕ)) : ℚ) * (3 : ℚ)) ∧
    -- row 6: anchors (via bezT), e ∣ wSide, g·μ ≤ wSide/e, node 0 then node 1
    (((2 : ℤ) * (-1) = (0 : ℤ) - bezT 2 1 * 2 ∧ (2 : ℕ) ∣ 2 ∧ 1 * 1 ≤ 2 / 2) ∧
      ((1 : ℤ) * 0 = (0 : ℤ) - bezT 1 3 * 3 ∧ (1 : ℕ) ∣ 1 ∧ 1 * 1 ≤ 1 / 1)) ∧
    -- rows 7a-7c: the chain clauses OTHER than W-mult
    ((0 + 1 ≤ 1) ∧ ((2 : ℕ) = 2 * 1 * 1) ∧ ((1 / 2 : ℚ) < 3 / 4)) ∧
    -- row 8: root width at n = toyN
    (0 + 2 ≤ toyN) := by
  have hb21 : bezT 2 1 = 1 := by
    rw [bezT, Nat.xgcd, Nat.xgcdAux_rec (by norm_num), Nat.xgcdAux_rec (by norm_num)]
    norm_num
  have hb13 : bezT 1 3 = 0 := by norm_num [bezT]
  refine ⟨by norm_num, rfl, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩,
    ⟨⟨by rw [hb21]; norm_num, by norm_num, by norm_num⟩,
      ⟨by rw [hb13]; norm_num, by norm_num, by norm_num⟩⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num [toyN]⟩

/-! ## The g₀ = 1 admissibility witness (the roster's only g-tie) -/

/-- TV-D7 gate (well-typedness of the g₀ = 1 pin): `Node`'s only g-tie is
`hψdeg : ψ.natDegree = g` (with `hψmonic`/`hψirr` on the same ψ) — and a
degree-1 monic irreducible ψ exists over EVERY field (in particular over the
card-2 residue field K₀ of the bStage-keyed node 0): ψ := X − C c. The species
conditionals (`hspecInc`/`hspecRec`/`hspecRecCenter`) are vacuous at node 0's
ROOT species (`History.root_iff` at j = 0). So NO law of the roster blocks the
g₀ = 1 pin — §3.D's read, re-checked compiled. -/
theorem censusD7_g1_psi_admissible {K : Type*} [Field K] (c : K) :
    (Polynomial.X - Polynomial.C c).Monic ∧
    (Polynomial.X - Polynomial.C c).natDegree = 1 ∧
    Irreducible (Polynomial.X - Polynomial.C c) :=
  ⟨Polynomial.monic_X_sub_C c, Polynomial.natDegree_X_sub_C c,
    Polynomial.irreducible_X_sub_C c⟩

/-! ## The gate: D5's pre-verified refutation script, generic over carriers -/

/-- **TV-D7, THE GATE** — D5's refutation script, pre-verified GENERICALLY:
over EVERY finite-field carrier `F`, EVERY history whose first two nodes carry
the pinned literal columns (`card K₀ = 2`, `card K₁ = 4`, `g₀ = 1`), and EVERY
`n`, `HistLawful 2 n` FAILS — via the chain-clauses conjunct at i = 0, 4th
sub-clause (REV 4 W-MULTIPLICATIVITY, §3.D display), which demands `4 = 2 ^ 1`.
TV-D5 closes `toy_v8_wchain` as `censusD7_wchain_refutes twoNodeKcardH …` once
TV-D4 lands the carrier (behind the E-2 ruling). The genericity over `n`
certifies the refutation does not touch the root-width clause (no artifact). -/
theorem censusD7_wchain_refutes {F : Type*} [Field F] [Finite F]
    (H : History 2 F) (hlen : 2 ≤ H.nodes.length)
    (hK0 : Nat.card ↥((H.nodes[0]'(by omega)).σ.K) = 2)
    (hK1 : Nat.card ↥((H.nodes[1]'(by omega)).σ.K) = 4)
    (hg0 : (H.nodes[0]'(by omega)).g = 1) (n : ℕ) :
    ¬ HistLawful 2 n H := by
  rintro ⟨-, -, -, -, -, -, hchain, -, -⟩
  have h01 : 0 + 1 < H.nodes.length := by omega
  obtain ⟨-, -, -, hw⟩ := hchain 0 h01
  have hw' : Nat.card ↥((H.nodes[1]'(by omega)).σ.K)
      = Nat.card ↥((H.nodes[0]'(by omega)).σ.K) ^ (H.nodes[0]'(by omega)).g := hw
  rw [hK0, hK1, hg0] at hw'
  exact censusD7_wmult_fails hw'

end LeanUrat.MovesT
