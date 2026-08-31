# UNIT SCB — VERDICT: THE SCOREBOARD IS NOW A THEOREM — `decidedSliceAt_all_of_MASTER`
lands the census front on FIVE premises (staged cite + four named laws); mass 4 rests on
`FactorCorrespondenceAt 2` ALONE; the capstone-level master states the WHOLE proof's
remaining surface as one Lean statement (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG55.lean` (402 lines, ZERO sorries,
zero errors, ZERO warnings; 8 AxCheck footer lines).  **Axiom fence, exactly as
designed:** `coneRemainderLaw_of_unwitnessed` is pure Lean core
`{propext, Classical.choice, Quot.sound}`; every census declaration (the §1 fires, the
§2 reconciled front, the §3 engine, ★★★ `decidedSliceAt_all_of_MASTER`) is Lean core +
EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited — never
re-consumed); ★★★ `capstoneHypotheses_of_MASTER` additionally inherits exactly the
previously-declared allowlisted cite `Uniformity.Density.Tower.agnprw_termination`
(ID12's `ns7Termination_of_cite`).  **No C.33 cite occurs anywhere.**
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG55.lean`
(6 increments, each GREEN; final: exactly the 8 expected axiom prints); targeted
`lake build Uniformity.ChapI.IFCG55` GREEN (9031 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the IFCG55 line after ID12 (the one
sanctioned touch to a landed file).  No git operations.

## ★ THE FLAGGED CROSS-CHECK, RECONCILED (charge item 1)

**Finding: no namespace or statement mismatch — DDT simply never imported RIS.**
IFCG54's imports are {Mathlib, IFCG53, IFCG51, IFCG1}; IFCG37 is not in that cone, so
IFCG54's rows kept `E1IrrLeafDecision` as a hypothesis.  The types compose EXACTLY:
`IFCG37.e1IrrLeafDecision : Uniformity.Density.IFCG34.E1IrrLeafDecision` (Lean-core,
no premises) is byte-identical to the `hL` premise of IFCG51's type22/type41 rows and
IFCG54's census fronts (IFCG54 opens `IFCG34 (… E1IrrLeafDecision …)` at line 98).
In IFCG55 (importing both) every composition is a direct application.  A SECOND stale
row fell out of the same walk: every post-INS wrapper (UZL, IFCG34, 36, 53, 54) still
carried `hBr : ∀ δ e ≥ 2, UnramifiedBlockBridge δ e`, but INS's
`IFCG32.unramifiedBlockBridge_all (hδ : 1 ≤ δ)` is UNCONDITIONAL Lean-core (IFCG35's
own wrapper had already consumed it) — so `hBr` is discharged everywhere too.  DDT's
scoreboard row 8 survives only as the informal obstruction note for a cite-free FC-2
inert leg, NOT as a census premise.

    theorem coneRemainderLaw_four_type22 : FactorCorrespondenceAt 2 → ConeRemainderLaw 4 type22
    theorem coneRemainderLaw_four_type41 : FactorCorrespondenceAt 2 → ConeRemainderLaw 4 type41
    theorem coneRemainderLaw_four_all    : FactorCorrespondenceAt 2 → ∀ σ, ConeRemainderLaw 4 σ  -- ★★★
    theorem decidedSliceAt_all_of_fc2_final :               -- DDT's front, hL + hBr GONE
      FactorCorrespondenceAt 2 → (e ≥ 5 generic laws) → ∀ n, DecidedSliceAt n

**MASS 4 RESTS ON `FactorCorrespondenceAt 2` ALONE — at every type at once**
(`coneRemainderLaw_four_all`, no degree/witness restriction: even-member types by the
forced sector partition with all four sector limits now closed — split/irr IFCG36 (+ RIS's
leaf), dd IFCG51 on FC 2, E2 IFCG54 unconditional; all other types by IFCG31's odd law).

## ★★★ THE MASTER (charge item 2) — the checked census scoreboard

    theorem decidedSliceAt_all_of_MASTER
        (hFC   : ∀ D, 2 ≤ D → FactorCorrespondenceAt D)
        (hEis  : composite m ≥ 6, guards* → EisFullSpanRemainderLaw m σ)
        (hSD   : e ≥ 5, guards* → SplitConvolutionDefectLaw e σ)
        (hPD   : e ≥ 5, guards* → PowerConvolutionDefectLaw e σ)
        (hLeaf : e ≥ 5, guards* → LeafSectorLaw e σ) :
        ∀ n, Uniformity.Density.DecidedSliceAt n
      -- guards* = (∀ k < e value laws) → σ.degree = e → Witnessed e σ → (∃ p ∈ σ.data, p.1 ≠ 1)

| # | master premise | kind | notes |
|---|---|---|---|
| 1 | `FactorCorrespondenceAt D`, every `D ≥ 2` | THE STAGED CITE (owner gate; CTS package) | `D = 2` alone fires ALL of mass 4; the family feeds ASM's composite full-span fire at divisor depths |
| 2 | `EisFullSpanRemainderLaw m σ`, composite `m ≥ 6`, witnessed ram., under `< m` value laws | open named law (ASM) | prime masses close by DTR; `m = 4` proved empty |
| 3 | `SplitConvolutionDefectLaw e σ`, `e ≥ 5` ram. witnessed | open (IFCG38 genre) | NOTE: `e ≥ 5`, not the charge's guessed `m ≥ 4` — `e = 4` is closed by the sector limits |
| 4 | `PowerConvolutionDefectLaw e σ`, `e ≥ 5` ram. witnessed | open (IFCG44 genre) | same mechanism family as row 3 |
| 5 | `LeafSectorLaw e σ`, `e ≥ 5` ram. witnessed | open | ONLY the leaf-cell COUNT — the decisions closed at every `(e', d)` by RIS (`decidedAt_of_spanning_irr`) |

**GONE from every earlier wrapper's list (all machine-checked inside):**
`E1IrrLeafDecision` (RIS, Lean-core) · `UnramifiedBlockBridge` (INS, Lean-core; the
ASM/DDT tables carried it stale) · `PowerFullSpanLaw` as an independent row (decomposed
through ASM's `powerFullSpanLaw_of_prime_or_correspondence`; ITS divisor-depth supplies
wired — see the engine) · ALL `e ≤ 4` remainder laws · the E1/E2 depth-0 + dd recursion
families (IFCG36/51/54) · the unramified laws at every mass (UZL) · the unwitnessed
sector (this unit's §0 zero law, the one new mechanism lemma: the remainder carrier
sits inside the empty decided set of an unwitnessed label).

**THE ENGINE** (`coneRemainderLaw_all_of_master`, §3 — the unit's real new content):
`ConeRemainderLaw e σ` for EVERY `e ≥ 2` and EVERY σ from the five premises, by strong
induction on the mass (bounded-induction form).  The previously-unwired step — ASM's
scoreboard note "descent-internal supplies… well-founded at all depths" — is now an
actual Lean recursion: at composite mass the correspondence fire's `DecidedValueLaw`
divisor supplies are the census induction hypothesis `hsm` verbatim (`D < 2·D ≤ e`),
and its `ZeroConeClause` supplies are THE ENGINE ITSELF at mass `D` composed with
`zeroConeClause_of_remainderLaw` (`D = 2` on `zeroConeClause_two`); the `∀ τ`
quantifier over degree-`D` types closes via unramified (UZL) + unwitnessed (§0) + the
mass-4 dichotomy + the sector assembly.  Compiled first-attempt, zero repairs.

## ★★★ THE CROSS-FRONT MASTER (charge item 3)

    theorem capstoneHypotheses_of_MASTER (n) :
      (ladder) → (deepTwist) → (the five census premises) → CapstoneHypotheses n

via ID12's `capstoneHypotheses_of_three` on the `a0` leg — the WHOLE proof's remaining
surface as ONE Lean statement: {ladder, deepTwist} (field types byte-copied from
`I10_I15_I18.lean` via ID12) + rows 1–5 above.  ID12's honesty frame applies verbatim:
the three I-D12 fields are supplied AS SIGNED (`True`-bodied at HEAD), so this
statement's conditionality is exactly the SIGNED capstone's — it certifies no window
pinning, no σ-decision, no tower census beyond that.

## HONESTY / trust boundary

Nothing weakened; every consumed statement byte-untouched; every composition
machine-checked; the premise guards make the master premises WEAKER (the theorem
stronger) than the scoreboards' bare-law rows.  ONE new mechanism lemma
(`coneRemainderLaw_of_unwitnessed`, Lean-core) — no new Set, no new Prop, no new law
definition; all other declarations are compositions of landed statements.  The only
landed-file touch is the sanctioned aggregator import line.

## File map (`leanfinal/Uniformity/ChapI/IFCG55.lean`, 402 lines)

§0 `coneRemainderLaw_of_unwitnessed` (Lean-core) · §1 the RIS-fire reconciliation
(`coneRemainderLaw_four_type22/type41`, ★★★ `coneRemainderLaw_four_all`) ·
§2 `decidedSliceAt_all_of_fc2_final` (DDT's front, hL + hBr gone) · §3 ★★★ the engine
`coneRemainderLaw_all_of_master` · §4 ★★★ `decidedSliceAt_all_of_MASTER` (docstring
carries the labeled premise table) · §5 ★★★ `capstoneHypotheses_of_MASTER` · AxCheck
footer (8 lines, all exactly as fenced).  Imports: Mathlib + IFCG54 + IFCG37 + ID12.

## Repair log (2 rounds, both mechanical)

1. `IFCG25.decidedSet_eq_empty_of_unwitnessed` takes `O` EXPLICIT — supply `(O := O)`.
2. `push_neg` deprecated at this pin — `push Not`.

## Consumption notes (for successors)

* The master premise shapes are the CANONICAL forms now — any unit closing rows 2–5
  should target exactly these guarded statements; any FC-staging unit should target
  `hFC`'s `∀ D ≥ 2` family (signing the cite at `D = 2` only unlocks mass 4 +
  `decidedSliceAt_all_of_fc2_final`'s route, not the full master).
* The engine is reusable: any future named-law replacement for rows 2–5 slots into
  `coneRemainderLaw_all_of_master` without touching the recursion.
* Scoreboard hygiene: ASM §3 row 8 and DDT §3 rows 5+8 are STALE as census premises
  (proved by INS/RIS); their tables should be read modulo this verdict.
