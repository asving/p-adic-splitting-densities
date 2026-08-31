# UNIT DDT — VERDICT: THE E2 dd TOWER CLOSES **CITE-FREE** — all three
`ZcURLim (e2DdDecFam σ)` terms PROVED by translation self-similarity, the E2 front
UNCONDITIONAL, two mass-4 rows land cite-free, the census front is E2-FREE (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG54.lean` (2393 lines, ZERO sorries,
zero errors, ZERO warnings; 23 AxCheck footer lines).  **Axiom fence, better than
charged:** the ENTIRE mechanism layer — the deepBox, the DecidedAt translation
transport (`decidedAt_shiftClass_iff`), BOTH box transports (`shift_mem_deepBox`,
`shift_mem_ddFiber`), the root parametrization (`mem_ddPairs_iff`, `dd_root_unique`),
and the fibration counts (`card_decided_ddFiber`, `card_decided_dd_stratum`) — is
**pure Lean core** `{propext, Classical.choice, Quot.sound}`.  The three ★★★ fires,
the unconditional E2 closures, and the cite-free mass-4 rows carry Lean core + EXACTLY
the owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42), inherited through IFCG53's decided counts — never re-consumed.  **No C.33
cite occurs; no OM/FactorCorrespondence axiom is consumed anywhere** (the `_of_fc2`
wirings are conditional theorems through IFCG51's Lean-core fires).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG54.lean`
(11 increments, each GREEN before the next; final: zero diagnostics beyond the 23
expected prints); targeted `lake build Uniformity.ChapI.IFCG54` GREEN (8967 jobs);
aggregator `lake env lean Uniformity/ChapI.lean` GREEN with the IFCG54 line wired
between IFCG53 and ID12 (note: the concurrent unit's `I10IfaceCore` aggregator line
was present un-built in the working tree; its targeted build also ran GREEN here so
the full aggregator verifies).  No landed file touched except the one aggregator
import line; no git ops.  Validation artifacts preserved:
`runs/wave-c/ddt_battery.gp` + `ddt_battery_results.txt` (PARI, 9/9 cells match) ·
`runs/wave-c/ddt_codex_brief.md` + `ddt_codex_verdict.txt` (fresh-context
adversarial read: NO CRITICAL ERROR).

## ★★★ THE HEADLINES

    theorem zcURLim_e2DdDecFam_ramPair   : ZcURLim (e2DdDecFam ramPairType)    -- ★★★
    theorem zcURLim_e2DdDecFam_splitTail : ZcURLim (e2DdDecFam splitTailType)  -- ★★★
    theorem zcURLim_e2DdDecFam_inertTail : ZcURLim (e2DdDecFam inertTailType)  -- ★★★
      -- ALL THREE UNCONDITIONAL (Lean core + B.42) — E2L's three named open
      -- premises are DISCHARGED, with NO FactorCorrespondence cite
    theorem zcURLim_e2DecFam_final : ∀ σ, ZcURLim (e2DecFam σ)                 -- ★★★
    theorem coneRemainderLaw_four_splitTail : ConeRemainderLaw 4 splitTailType -- ★★★
    theorem coneRemainderLaw_four_inertTail : ConeRemainderLaw 4 inertTailType -- ★★★
      -- TWO MASS-4 ROWS CLOSE CITE-FREE
    theorem coneRemainderLaw_four_ramPair_of_fc2 :
      FactorCorrespondenceAt 2 → ConeRemainderLaw 4 ramPairType                -- ★★
    theorem decidedSliceAt_all_of_e1dd_limits :   -- ★★★ THE CENSUS FRONT, E2-FREE
      E1IrrLeafDecision → (∀ σ, ZcURLim (e1DdDecFam σ)) → (e≥5 laws) → (bridges)
        → ∀ n, DecidedSliceAt n
    theorem decidedSliceAt_all_of_fc2 :           -- ★★★ the same on the staged cite
      E1IrrLeafDecision → FactorCorrespondenceAt 2 → (e≥5 laws) → (bridges)
        → ∀ n, DecidedSliceAt n

Values (uniform in q): dd-ram `(q−1)³/((q²−1)(q³−1)q⁶)` = `(q−1)/(q⁶(q+1)(q²+q+1))`;
dd-split = dd-inert `(q−1)³/(2(q²−1)(q³−1)q⁷)`.  σ-sum = the dd measure
`(q−1)²/(q⁷(q³−1))` EXACTLY.  In-sector fractions: ram `q/(q+1)`, split = inert
`1/(2(q+1))` — s-independent.

## THE MECHANISM (the charge's cite-free attempt — SUCCEEDED, and lighter than planned)

E2L's recorded discharge path (two-block Hensel decidedness transport + mass-2
zero-cone consumption) was NOT needed.  The key observation: **the E2-dd recentring
key is LINEAR** — `x ↦ x + zπ^s` over the SAME `O` — so it is an `O`-algebra
automorphism of `O[x]`, and `typeOf`/`DecidedAt` transport through it for FREE
(IFCG1's landed `shiftVecN`/`coeffShiftEquivN` kit; zero new factorization theory).

1. **Digit transport** (`shift_mem_deepBox`/`shift_mem_ddFiber`, pure digit
   arithmetic, ANY residue characteristic incl. 2): with `δ = resDig π 1 (c 2)` and
   dd pair `(t+t, t·t)` (residual `(Y+t̄)²`, root `−t̄`), translating by `−uπ^s`
   (`residue u = t`) kills the level-`(s+1)` and level-`(2s+1)` digits
   (`d₁ + 2δ(−t) = 0`, `d₀ + d₁(−t) + δt² = 0`), landing the stratum EXACTLY on
   `deepBox s = {v₀ ≥ 2s+2, v₁ ≥ s+2, v₂ = 1, v₃ ≥ 1}`; translating back reconstructs
   the pair with the corner EXACT (`t²δ ≠ 0`).
2. **Fibration** (`card_decided_dd_stratum`): the root `t` is unique char-free
   (`(t−t')² = t·t − (t+t)t' + t'·t'`), so
   `#(decided σ ∩ cBox s dd) = (q−1)·#(decided σ ∩ deepBox s)`.
3. **Self-similarity**: `deepBox s` re-partitions into IFCG53's OWN genre strata at
   corner depths `> s` (windows narrowed by omega alone) — genre a/b/c decided counts
   are LANDED EXACT; the dd part recurses through the same fibration.
4. **Unroll** (`tail_sum_geom`, first-order recursion `U(s−1) = E(s) + q·U(s)`):
   `#(decided σ ∩ e2DdBox) = (q−1)·Σ_j q^j·(E_σ(j+1) + Bd(j+1))`, exact at every
   level; the weight swap (`sum_weight_swap`/`_3`) turns the main term into
   per-stratum truncated-geometric weights `(q^{t−1}−1)`, i.e. differences of
   `q^{−2t}`/`q^{−3t}` geometric sums (`tendsto_geom_sum_k`, the general-`k`
   machine); the boundary sum is `≤ q^{K/2}·q^{3K}/q^{4K} = EBd → 0`
   (`ZcURLim.sandwich`).

## VALIDATION (both decorrelated arms, BEFORE the Lean)

* **PARI battery** (`/tmp/ddt_battery.gp`, factorpadic; p ∈ {2,3,5} × s ∈ {1,2,3} ×
  N = 4000): all nine cells match ram `q/(q+1)`, split = inert `1/(2(q+1))` within
  2σ; ZERO anomalous factor patterns (independently re-confirms IFCG53's
  `typeOf_e2_mem` shape pin).  **E2L's consumption-note guess
  ("`1/(q²+q+1)`-shaped" per-s values) is REFUTED**; this unit's values stand.
* **Codex adversarial read** (fresh context, quote-and-classify): NO CRITICAL ERROR;
  two justification gaps, both the window/limit bookkeeping that the Lean form makes
  exact by construction (precise Finset windows; swap-at-finite-K BEFORE limits);
  explicitly confirmed: no circularity in the self-similar recursion, geometric
  algebra and all three values correct.

## Charge disposition

**(1) CITE-FREE ATTEMPT — E2 leg: FULL SUCCESS** (above).  **E1 leg: NEGATIVE, with
the mechanism mapped**: the E1-dd recentring key is QUADRATIC (`X² − bπ`), an
extension step, not an automorphism.  The Krasner/two-quadratic route CAN reach the
split-genre legs of `FactorCorrespondenceAt 2` at `e' = 2` (explicit lifts:
`g = (φ−t₁)(φ−t₂) − λφ` with `v(λ) ≥ 2`, Hensel-separable on the decided locus), but
the INERT leg (transform irreducible over `O'`, `f = 2`) requires exactly the open
unramified bridge (scoreboard row: `UnramifiedBlockBridge`) — not closable this
unit.  IFCG52's iso machinery transports typeOf within ONE ring; FC 2's content is
cross-ring (`O` vs `AdjoinRoot (eisKey)`), so KDW's route cannot substitute alone.
**The E1 dd limits stay on `FactorCorrespondenceAt 2`** (ASM's `zcURLim_e1DdDecFam`).

**(2) THE FIRES** — all three `e2DdDecFam σ` CITE-FREE (★★★ headlines); the e1 dd
limits re-wired at the two consumption points (`coneRemainderLaw_four_ramPair_of_fc2`,
`decidedSliceAt_all_of_fc2`).  The charge's ★★★ contingency "MASS 4 CLOSES ENTIRELY"
required the E1 dd terms cite-free too — NOT achieved (honest negative above); what
closed entirely is the E2 SIDE, plus two full mass-4 rows outright.

**(3) THE CENSUS SCOREBOARD (recomputed; delta vs ASM §3 + E2L §3).**

| # | Surviving premise | Kind | Notes |
|---|---|---|---|
| 1 | `FactorCorrespondenceAt D`, `D ≥ 2` | THE STAGED CITE (owner gate) | unchanged; at `D = 2` now ALSO fires the ramPair mass-4 row OUTRIGHT (`_of_fc2`) and the whole census front's E1-dd leg |
| 2 | `EisFullSpanRemainderLaw m σ`, composite `m ≥ 6` | named law (ASM) | unchanged |
| 3 | `Split/PowerConvolutionDefectLaw`, `e ≥ 5` ram. | open | unchanged |
| 4 | `LeafSectorLaw e σ`, `e ≥ 5` ram. | open | unchanged |
| 5 | `E1IrrLeafDecision` | open (B-BOX-1) | unchanged (type22/type41 rows) |
| 8 | `UnramifiedBlockBridge δ e` | open | unchanged; ALSO the obstruction to a cite-free FC 2 inert leg (this unit's finding) |

**GONE from the list (THIS UNIT): the entire E2 sector** — E2L's row 7 replacement
(the three `ZcURLim (e2DdDecFam σ)` terms) is CLOSED CITE-FREE; `hE2` has no
successor premise.  (Row 6 was already gone — IFCG36 closed `e1SplitFam`/`e1IrrFam`.)

**Mass-4 rows after DDT** (the endgame for the 11 quartic types):
splitTail ★★★ CLOSED (Lean core + B.42) · inertTail ★★★ CLOSED (Lean core + B.42) ·
ramPair ⟸ `FactorCorrespondenceAt 2` alone · type22, type41 ⟸ {`E1IrrLeafDecision`,
`FactorCorrespondenceAt 2`} (ASM, unchanged) · all other types: closed previously.
**Signing the CTS cite at `D = 2` + closing B-BOX-1 now closes ALL of mass 4.**

## New definitions (trust boundary — flag for review)

`deepBox O K s` (the deep tail box; the ONLY new Set) — all other new declarations
are theorems about landed statements.  `e2DdDecFam`, `e2DecFam`, `ConeRemainderLaw`,
`DecidedSliceAt`, and every consumed statement are byte-untouched; nothing weakened.
Private replicas from IFCG51/53 (sanctioned replays): `ncard_biUnion_eq`, window
normal forms + tendstos, pair-count kit, `digTriples_*_val`, type-inequality kit.

## File map (`leanfinal/Uniformity/ChapI/IFCG54.lean`, 2393 lines)

§0 `deepBox` + `decidedAt_shiftClass(_iff)` (the REUSABLE translation decidedness
transport, any degree/level) · §1 `sv4_*` explicit quartic shift coefficients,
★ `shift_mem_deepBox`, ★ `shift_mem_ddFiber` · §2 `mem_ddPairs_iff`,
`dd_root_unique`, ★ `card_decided_ddFiber`, ★★ `card_decided_dd_stratum` ·
§3 the three `decided_*_inter_deepBox` identities + `card_decided_deepBox_*`
recursions · §4 `card_decided_e2DdBox`, ★ `tail_sum_geom`,
★★ `card_e2DdBox_unrolled` (generic in the genre term) · §5 ★ `tendsto_geom_sum_k`
(general `k`), `sum_weight_swap(_3)`, `geom_mul` · §5b pair-count value bridge ·
§6 `EBd` + vanishing · §7–§9 the three fires (main family, decomposition identity,
limit witness `(X−1)³ / [C 2·](X²−1)(X³−1)X^{6,7}`, sandwich) · §10 consequences ·
AxCheck footer (23 lines, all clean).
Imports: Mathlib + IFCG53 + IFCG51 + IFCG1.  Aggregator: one line in
`Uniformity/ChapI.lean` (IFCG54 between IFCG53 and ID12).

## Repair log (9 error rounds over 11 increments; every statement landed as designed)

1. `resOrd` lives in `Uniformity.Density.Induction` (H107); `e2Box` membership needs
   `Finite (ResidueField O)` in scope.
2. `Nat.choose` numerals: `norm_num` alone is nondeterministic (splits
   `mul_eq_mul_right_iff`) — supply `show Nat.choose i j = k from rfl` simp sets.
3. `Irreducible.not_unit` → `not_isUnit` (fourth corpus contact).
4. Manual `map_*` rw chains are order-fragile on nested sums — `simp only [map_*]`
   + `ring` instead.
5. `linarith` is useless in a general field — `sub_eq_zero.1` directly; singleton
   pair-set ascriptions must be `({(a, b)} : Set (F × F))`, never with an inner
   type ascription on the pair.
6. THE SELF-PATTERN TRAP (new, logged): rewriting with an identity whose RHS contains
   the LHS pattern (`decided ∩ deepBox = … ∪ (decided ∩ deepBox ∩ bd)`) loops onto
   the boundary term — `conv_lhs => rw [...]`.
7. `Nat.Ico_succ_left` doesn't exist at this pin — `Finset.Ico_add_one_left_eq_Ioo`.
8. `add_le_add_left` as a `refine` head sticks on `AddRightMono` metavariables —
   a local `hadd : ∀ a b c : ℝ, b ≤ c → a + b ≤ a + c := by linarith` is robust.
9. `Finset.sum_filter` closes the ite-form goal on its own (no congr continuation);
   `gcongr` discharges its own side goals (trim bullets).

## Consumption notes (for successors)

* `decidedAt_shiftClass_iff` + `coeffShiftEquivN` is a GENERAL instrument: any
  future linear-recentring census sector (any degree, any level) gets decidedness
  transport for free.  The deepBox self-similarity pattern (translate → re-partition
  → unroll) should be the template for every linear-key dd tower.
* `tendsto_geom_sum_k` generalizes IFCG53's `tendsto_geom_sum` to arbitrary stride
  `k ≥ 1` — any mixed-stride stratum resummation can consume it.
* The remaining mass-4 gate is exactly {`FactorCorrespondenceAt 2` (owner cite,
  CTS's package), `E1IrrLeafDecision` (B-BOX-1)}.  The FC-2 inert leg's cite-free
  obstruction is `UnramifiedBlockBridge` — closing row 8 first would open a
  cite-free path to FC 2's `D = 2` instance worth re-examining (split legs already
  reachable by explicit Krasner lifts; see charge disposition (1)).
