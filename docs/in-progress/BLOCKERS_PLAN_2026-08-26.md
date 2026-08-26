# Chapter-C chain blockers — enactment plan (2026-08-26)

## Verdict and scope

This plan covers exactly PROJECT_STATE §4 item 4: the C.35 `BlockFrontier` family,
the two named C.27 mechanisms, and RB3's two proof gaps
(`docs/PROJECT_STATE.md:95-99`). It does not authorize edits to the signed spec, landed
chapter files, or roll-ups.

The inherited probe file was run first, exactly as charged:

```text
cd leanfinal
lake env lean scratch/DEC4_check.lean
# exit 0
```

After the new probes described below were added, the same command again exited 0. Every
printed footprint is exactly `[propext, Classical.choice, Quot.sound]`; no project axiom,
cite axiom, or `sorryAx` occurs (`leanfinal/scratch/DEC4_check.lean:227-246`). The original
F2-2 prose needed one correction: its theorem supplied only B-to-A transfer from a nonzero
scalar *membership* witness, not a bare implication between norm-nonzero propositions
(`leanfinal/scratch/DEC4_check.lean:77-100`). The file now proves the reverse orientation too
and states the honest membership-assisted contract (`leanfinal/scratch/DEC4_check.lean:102-131`).

Sizing below means expected new Lean source lines excluding module documentation and axiom
footers. “Conditional landing” means an honestly renamed theorem with an explicit
`hfr : BlockFrontier L f`; it must not be installed under the exact signed name. The RB1
audit records why adding a hypothesis under a signed name is not an exact landing
(`runs/wave-b/verdict_RB1.md:64-73`).

## F1 — C.35 `BlockFrontier` and the eight conditional rows

### What is already landed, and what the condition means

`BlockContext`, `blockFactor`, and `mult₂` are already landed definitions
(`leanfinal/Uniformity/ChapC/C35.lean:124-144`). `BlockFrontier L f` says that a labelled
divisor `fS` exists, divides `f`, has the indispensable `D′ | deg fS` rider, and is maximal
among labelled divisors (`leanfinal/Uniformity/ChapC/C35.lean:241-249`). The rider cannot be
removed: C35b constructs a labelled cubic at a frame with `D′ = 2`
(`leanfinal/Uniformity/ChapC/C35b.lean:21-42`) and proves the universal divisibility claim false
(`leanfinal/Uniformity/ChapC/C35b.lean:375-390`).

The packaging layer is already complete: `blockFactor_eq_of_frontier` identifies the chosen
frontier witness with `blockFactor`, and `blockFactor_spec_of_frontier` returns label,
divisibility, exact degree, and positive `mult₂`
(`leanfinal/Uniformity/ChapC/C35.lean:251-282`). Probe F1-1 checks the exact four-read projection
shape used below (`leanfinal/scratch/DEC4_check.lean:133-145`).

The frontier itself is still new mathematics. The old blocked record isolates a one-slope
`dv`-graded Hensel existence/uniqueness engine and residual-primary extraction as the missing
mechanism (`leanfinal/Uniformity/ChapC/C34_BLOCKED_2026-08-18.md:85-106`,
`leanfinal/Uniformity/ChapC/C34_BLOCKED_2026-08-18.md:158-168`). The later declared cite
`fgmn_dv_exact_mul` supplies exact same-slope purity/product residuals only after both factors,
degree divisibilities, and positive degrees are already available
(`leanfinal/Uniformity/ChapC/C66b.lean:85-107`); it does not construct the factors.

### Frontier-construction nodes

| node | statement sketch | named landed inputs | mechanism | sizing / exit gate |
|---|---|---|---|---|
| F1.H0 | `dvResidualBezout`: split a normalized level residual as `r^m * s` with `IsCoprime (r^m) s`, including the `m > 0` consequence of `r ∣ R`. | `one_le_dvSideDeg_of_dvd_dvResPoly`, the single-class helpers, and the frontier packaging are already in C34 (`leanfinal/Uniformity/ChapC/C34_BLOCKED_2026-08-18.md:137-156`). | UFD arithmetic over `F.stageField`; no completeness yet. | 35–60 lines; Lean-core. |
| F1.H1 | `exists_dv_oneSlope_split`: lift F1.H0 to `g = fS * g'`, with `HasLabel L fS`, monic complement, complement residual not divisible by `r`, purity, and both `D′` degree riders. | F1.H0; landed Hensel solve/limit infrastructure is named by the blueprint but the order-1 `IsKey`-fenced machinery cannot be reused directly (`blueprint/CHAP-C_tower_grammar.md:2324-2338`; `leanfinal/Uniformity/ChapC/C34_BLOCKED_2026-08-18.md:87-103`). | **Genuinely new mechanism:** residual Bézout Newton correction in the `dvHgt` filtration, then the `IsAdicComplete` limit; use `fgmn_dv_exact_mul` only to certify exact product reads after the factors exist. | 140–240 lines, likely 2 files; first file is finite correction + invariants, second is convergence and factor identity. |
| F1.H2 | `dv_oneSlope_split_unique`: two monic `r`-primary/complement splits agree. | F1.H1 invariants; `fgmn_dv_exact_mul`; monic cancellation. Residue-field Hensel uniqueness is structurally unusable because the factors may share `x` modulo the base maximal ideal (`leanfinal/Uniformity/ChapC/C34_BLOCKED_2026-08-18.md:108-135`). | Uniqueness in the `dv`-graded filtration, not ordinary residue-field coprimality. | 100–180 lines; Lean-core plus the already declared FGMN cite if exact product reads are consumed. |
| F1.H3 | `blockFrontier_of_context (hctx : BlockContext L f) : BlockFrontier L f`. | `exists_dvDissection`, its factor equality cite, F1.H1–H2, and C35's degree tie. The intended route “slope factor, then residual-primary block” is recorded at `leanfinal/Uniformity/ChapC/C35_BLOCKED_2026-08-20.md:89-120`. | Select the `(u,ℓ)` slope factor, split its `r`-primary part, prove cross-slope and within-slope maximality, transport `D′ | deg`. | 70–120 lines. This is the single discharge point for all `_of_frontier` riders. |

### The eight-row conditional family

Each row first lands with an explicit `hfr`; after F1.H3 lands, a tiny exact-name wrapper may
apply it to `hctx`. The eight signed conclusions and binders are fixed at
`leanspec/Leanspec/ChapC.lean:1599-1632`, `leanspec/Leanspec/ChapC.lean:1677-1726`, and
`leanspec/Leanspec/ChapC.lean:2298-2319`.

| node | conditional statement sketch | named landed / earlier inputs | mechanism | sizing |
|---|---|---|---|---|
| F1.1 | `blockFactor_spec_of_frontier`: the signed four conjuncts. | Already landed `blockFactor_spec_of_frontier` (`leanfinal/Uniformity/ChapC/C35.lean:268-282`). | Projection of the frontier witness plus the protected degree theorem. | **0 new math**; optional 3–6 line alias only. |
| F1.2 | `block_complement_notdvd_of_frontier`: test-key divisor equivalence, residual non-divisibility of `f /ₘ blockFactor`, and finite complement support. | F1.1, F1.H1–H2, `IsTestKey`, monic division; the signed target is `leanspec/Leanspec/ChapC.lean:1614-1622`. | Use maximality for divisor placement; if the complement residual were `r`-divisible, F1.H1 would enlarge the block; support finiteness follows from nonzero monic complement. | 55–90 lines. `BlockFrontier` alone supplies identity reads, but the residual contradiction still consumes F1.H1; do not advertise this as a one-line projection. |
| F1.3 | `dv2Supp_translation_of_frontier`: translate the above-seam support by `ℓ₂ • complementConst`. | F1.1–F1.2, signed C.27 exactness when available, `dev` product calculus, and exact residual multiplication; the blueprint names these dependencies (`blueprint/CHAP-C_tower_grammar.md:2507-2521`). | Prove the complement contributes a constant value at every block slot, then translate the infimum. Split out `dv2Pin_mul_complement` if the proof exceeds 80 lines. | 70–120 lines including the helper; the old 44-line estimate omitted the missing no-interaction lemma. |
| F1.4 | `dv2ResPoly_scalar_of_frontier`: the full residual polynomial differs from the block residual by the displayed nonzero scalar involving `γg` and the cocycle. | F1.2–F1.3, `LevelDatum.cocycle`, twist/residue APIs; the signed scalar formula is `leanspec/Leanspec/ChapC.lean:1705-1715`. | Coefficientwise translation along the unchanged argmin set; prove `γg ≠ 0`, then telescope the normalization cocycle. | 55–90 lines. Land before F1.5 despite node-number order, as the blueprint makes radical equality depend on the scalar (`blueprint/CHAP-C_tower_grammar.md:2567-2574`). |
| F1.5 | `dv2ResPoly_radical_eq_of_frontier`: equal degree and the same monic irreducible divisors. | F1.3–F1.4 and polynomial unit/scalar divisibility; exact target at `leanspec/Leanspec/ChapC.lean:1680-1690`. | Rewrite by F1.4, cancel a nonzero constant unit in the field, preserve degree and prime divisors. | 20–35 lines, matching the blueprint's 20-line core once F1.4 exists (`blueprint/CHAP-C_tower_grammar.md:2567-2574`). |
| F1.6 | `mult₂_readable_of_frontier`: equality of side minima and side degrees for `f` and its block. | F1.3 and `dv2SideSet` definitions; signed target at `leanspec/Leanspec/ChapC.lean:2298-2306`. | Support translation by a constant preserves the on-side set, hence min/max/degree. | 25–45 lines. |
| F1.7 | `dv2_length_sum_of_frontier`: the block's endpoint pins and every above-seam side maximum are bounded by `mult₂`. | F1.1, F1.6, `blockFactor` monic/degree, `dev_top`, and side-index bounds; signed target at `leanspec/Leanspec/ChapC.lean:2311-2319`. | Read indices `0` and `mult₂` from the exact block degree; bound every side index by the top development index. | 45–75 lines. |
| F1.8 | `level2_peel_of_frontier`: singleton type, irreducibility, and a squarefree one-factor peel with the exact remaining degree. | F1.1–F1.2, landed C.61 only after the C.27→C.59 chain closes, `peel_once_of_squarefree`, and protected degree arithmetic. The blueprint explicitly depends on C.60/C.61 (`blueprint/CHAP-C_tower_grammar.md:2696-2708`). | Apply the type/irreducibility read to `Ψ`; squarefree cancellation gives `¬ Ψ ∣ fS'`; subtract one `keyDeg₂` block using the exact degree equation. | 45–70 lines after C.61; keep this last in the family. |

Rows such as repaired `multiplicity_tie`, `dv2Pin_translation_interior`, and repaired
`tie_pure_power` are downstream consumers, not members of this eight-row landing batch. Their
current dependence on the block chain is recorded separately
(`runs/wave-b/verdict_CCUR.md:94-98`, `runs/wave-b/verdict_CCUR.md:118-123`). Schedule them only
after F1.1–F1.8 rather than silently expanding this unit.

## F2 — C.27: quotient symmetry, ramified level-1 exactness, and the honest general tail

### Correction to the old obstruction inventory

The norm/resultant-symmetry half is no longer new mathematics. B53a's `quotKeyEquiv` is generic
in both polynomials and identifies the two principal-ideal quotients
(`leanfinal/Uniformity/ChapB/B53a.lean:90-101`). B53c exports a generic determinant–length
dictionary for any positive-rank finite free algebra and nonzero norm
(`leanfinal/Uniformity/ChapB/B53c.lean:114-140`). Probe F2-1 composes them into equality of the
two norm valuations (`leanfinal/scratch/DEC4_check.lean:42-66`). Probes F2-2a/b transfer a
nonzero scalar-membership certificate through the quotient equivalence and force the opposite
norm nonzero (`leanfinal/scratch/DEC4_check.lean:68-131`).

The remaining key-read mathematics is the ramified analogue of B53b. B53b works because an
order-1 key gives an unramified DVR upstairs and the evaluated polynomial is `π^c` times a unit
(`leanfinal/Uniformity/ChapB/B53b.lean:102-152`). At the frame key the desired equality is instead
`addVal (norm (A₀(β))) = f₁ * stageHeight(A₀)` for `deg A₀ < D′`; the current C27 record names
exactly this ramified level-1 gap (`leanfinal/Uniformity/ChapC/C27x.lean:60-75`). The signed C.27
has no completeness hypothesis (`leanspec/Leanspec/ChapC.lean:883-889`), so the proof must be
finite/graded and completion-free.

### Nodes

| node | statement sketch | named landed inputs | mechanism | sizing / exit gate |
|---|---|---|---|---|
| F2.1 | Land `normQuot_membership_transfer` in both orientations: a nonzero `c : O` lying in either generator ideal forces the norm of the opposite generator nonzero. | `quotKeyEquiv`; probe proofs F2-2a/b (`leanfinal/scratch/DEC4_check.lean:77-131`). | Transport `algebraMap c = 0` between quotients, extract principal-ideal membership, take norms, use `norm (algebraMap c) = c^rank`. | 45–60 lines total; **proof already elaborated**, Lean-core. |
| F2.2 | Land `addVal_norm_symm`: equality of the norm valuations for monic positive-degree `φ,g`, with the two nonzero norms explicit. | F2.1 for hypothesis discharge at consumers; `quotKeyEquiv`; `length_quot_eq_addVal_norm`; probe F2-1 (`leanfinal/scratch/DEC4_check.lean:48-66`). | Rewrite both valuations as quotient lengths and use the quotient linear equivalence. | 25–35 lines; **proof already elaborated**, Lean-core. |
| F2.3 | `RamifiedNormExactStatement`: package the completion-free target for monic frame key `F.key`, `A₀.degree < F.key.degree`, `A₀ ≠ 0`: `addVal (norm (mk F.key A₀)) = f₁ * stageHeight A₀`, plus an explicit nonzero scalar-membership certificate usable by F2.1. | `stageHeight_eq_coeff_inf`, frame purity/residual irreducibility, `AdjoinRoot.powerBasis'`; the old key-read slot half `dv2Hgt_key = u` is already landed (`leanfinal/Uniformity/ChapC/C27x.lean:41-43`). | Statement carrier and API split only. | 15–25 lines; no assertion yet. |
| F2.4 | `ramified_norm_lower_bound`: valuation of the multiplication determinant is at least `f₁ * stageHeight A₀`. | F2.3 vocabulary, coefficient valuation bounds from the attaining height, determinant expansion over the power basis. | Weighted filtration on the `1,β,…,β^(D′-1)` basis; every determinant term pays the required cleared weight. | 90–140 lines. |
| F2.5 | `ramified_initial_det_ne_zero`: the determinant's least-weight initial form is nonzero. | Frame `hpure`, coprime `h/e₁`, irreducible stage residual, slot/twist read APIs. | **Genuinely new mechanism:** identify the initial multiplication matrix over the stage residue field and show its determinant is the norm of the nonzero initial residual. This is the ramified no-cancellation step, not B53b's unramified unit argument. | 120–220 lines; prototype small matrices first if the basis permutation is unclear. |
| F2.6 | `ramified_addVal_norm_exact` and scalar membership. | F2.4–F2.5, determinant/norm API. | Match lower bound with the nonzero initial coefficient, read exact `addVal`; derive nonvanishing and a scalar in the principal ideal via the characteristic polynomial/adjugate or a Smith-form corollary. | 60–100 lines. Total F2.3–F2.6 estimate: **285–485 lines**. No `IsAdicComplete`; no new cite. |
| F2.7 | `slot2_exact_resigned_key`: the signed C.27 conclusion at `C := F.key`; then exact-name `ramLeg_dvd` and `tier1_typeOf` wrappers. | F2.1–F2.2, F2.6, `dv2Hgt_key`, label purity endpoint arithmetic. The existing report says this single read is the remaining input for general `ℓ` in C.59 (`runs/wave-b/verdict_AC15C27.md:99-106`). | Swap the norm to `AdjoinRoot F.key`, apply ramified exactness to `dev F.key g 0`, and use the label's one-side endpoint equation; handle `D′ | deg g` only where the consumer provides it. | 35–60 lines for the key read; 10–20 lines for C.59/C.61 wrappers. |

### Do not overstate what F2.1–F2.7 close

They close the third *consumer read*, not automatically the full signed theorem for arbitrary
`C`. The landed C27 analysis says general `C` additionally needs label heredity to monic factors
and per-factor level-2 exactness, and therefore sits strictly above the C.35 frontier
(`leanfinal/Uniformity/ChapC/C27x.lean:77-82`; `runs/wave-b/verdict_AC15C27.md:92-97`). Plan the
full signed theorem only after F1.H1–H3 as the blueprint's mandated three-way split:

| node | statement sketch | mechanism | sizing |
|---|---|---|---|
| F2.G1 | `slot2_norm_lower_bound` for arbitrary `deg C < D″`, under an explicit factor/label package produced by the F1 engine. | Expand in level-2 slots and prove every root/norm contribution is at least the slot minimum; blueprint route step 2 is `blueprint/CHAP-C_tower_grammar.md:1874-1880`. | 80–130 lines. |
| F2.G2 | `slot2_norm_noCancellation`: the attaining residual contribution is nonzero. | Iterated residual basis and F2.5's ramified initial-determinant method; this is blueprint route step 3 (`blueprint/CHAP-C_tower_grammar.md:1881-1884`). | 120–220 lines; genuine order-2 exactness. |
| F2.G3 | exact signed `slot2_exact` assembly. | F2.G1–G2, norm/resultant product assembly, factor package. Blueprint already mandates three pieces (`blueprint/CHAP-C_tower_grammar.md:1885-1895`). | 50–90 lines. |

This extra tail is deliberately priced separately. Calling the whole signed theorem a
285–485-line consequence of “the two mechanisms” would repeat the obsolete CCUR overstatement.

## F3 — RB3: refinement invariants and shadow persistence

The exact signed closures elaborate against the landed vocabulary (probe F3-1,
`leanfinal/scratch/DEC4_check.lean:147-188`). RB3 nevertheless found real proof gaps: a
corrected-key stability theorem for `refine_invariants`, and an upward coefficient-budget to
shadow-discrepancy height bridge for `shadow_persistence`
(`runs/wave-b/verdict_RB3.md:59-79`, `runs/wave-b/verdict_RB3.md:85-109`).

### F3A — `refine_invariants`

Run the examples-first certificate before Lean: add
`verification/dec4_refine_invariants_cert.py`, with at least the landed q=2 `s2Frame` genre and
one odd-prime genre. For each, enumerate nonzero `s` and several `lam > E₂`; check the
`k2DigitLift` degree bound, unchanged leading term, every C.13 test-key slot, and mutations at
`lam = E₂`, wrong `s`, and one exponent off. This is a proposed artifact, not a current corpus
claim.

| node | statement sketch | named landed inputs | mechanism | sizing |
|---|---|---|---|---|
| F3.1 | `n2Exp_spec` and summand bounds: solve the two-stage grade equation and bound the `X`/`F.key` exponents. | Definitions `n2Exp`/`k2DigitLift` (`leanfinal/Uniformity/ChapC/C56a.lean:41-64`), tower/frame coprimality and floor fields. C56a explicitly records that exact-height and `deg < D₂` companions remain fleet-time work (`leanfinal/Uniformity/ChapC/C56a.lean:21-30`). | Modular arithmetic at `(u₂,e₂)` followed by `(h,e₁)`; `omega` after the two coprime solves. | 80–130 lines. |
| F3.2 | `k2DigitLift_natDegree_lt` plus exact stage-height/residue reads for each nonzero coordinate. | F3.1, `stageCoord`, `resLift_spec`, stage lift height/read lemmas. | Bound every finite-sum term below `D₂`; isolate equal-height terms and prove their prescribed `K₂` read. | 120–220 lines. |
| F3.3 | `refinedKey_isTestKey`: for `lam > E₂`, `composedKey T - k2DigitLift T s lam` is monic, has degree `D₂`, and is `IsTestKey`. | F3.2, landed `composedKey_monic`, `composedKey_natDegree_D₂`, and `composedKey_isTestKey` (`leanfinal/Uniformity/ChapC/C47.lean:503-519`, `leanfinal/Uniformity/ChapC/C47.lean:694`). | Low-degree subtraction preserves leading data; strictly-above perturbation leaves every C.13 development height and twist residue unchanged. This is the **new one-step Hensel/refinement-stability mechanism**. Prove the stronger theorem without `f/hne/hres` if possible: the signed event hypotheses select `s,lam` but its conclusion is only corrected-key data (`leanspec/Leanspec/ChapC.lean:2134-2146`). | 140–240 lines, split shape/read preservation if over 180. |
| F3.4 | exact signed `refine_invariants` wrapper. | F3.3; carry the signed `hf/hne/hres` binders unchanged. | Projection of F3.3. No member-to-generator residual transport should be invented unless F3.3 actually needs it. | 8–15 lines. |

If the certificate falsifies the stronger F3.3, insert a narrowly stated
`event_residual_controls_refinement` node between F3.2 and F3.3; that would be the
member-to-generator mechanism RB3 anticipated (`runs/wave-b/verdict_RB3.md:66-73`). Do not add
it pre-emptively.

### F3B — `shadow_persistence`

The additivity half is now discharged at probe grade. `dev` additivity already fires at the
exact `Φ₂^μ₂ + g` shape (`leanfinal/scratch/DEC4_check.lean:190-201`). New probes prove
`biRead_add`, monicity of `biRead F (composedKey T)`, and `shadowDev_add`
(`leanfinal/scratch/DEC4_check.lean:203-226`). The proof uses landed `devQ_add`
(`leanfinal/Uniformity/ChapC/C127.lean:155-171`) and `reass_add`
(`leanfinal/Uniformity/ChapC/C127.lean:383-392`). Thus RB3's “additivity gap” is a 30–50 line
API landing, not a multi-hundred-line mechanism.

Before the height proof, add `verification/dec4_shadow_budget_cert.py`. On the existing GENTOW3
small frames, enumerate coefficient arrays satisfying the signed `hbudget`; verify discrepancy
height `≥ theta+1`, equality after adding the key power at every certificate coordinate, and
negative controls lowering one coefficient exactly one unit below `budgetFloor`. This is a
proposed artifact.

| node | statement sketch | named landed inputs | mechanism | sizing |
|---|---|---|---|---|
| F3.5 | Public `biRead_add`, `biRead_composedKey_monic`, and `shadowDev_add`. | Probe F3-2b/c/d; `biRead_coeff`, `xNF_monic`, `devQ_add`, `reass_add`. The coefficient formula is landed at `leanfinal/Uniformity/ChapC/C127.lean:288-306`, and `xNF_monic` at `leanfinal/Uniformity/ChapC/C131v.lean:244-249`. | Coefficientwise linearity, mapped monic normal form, then reassembly linearity. | 30–50 lines; **already elaborated**, Lean-core. |
| F3.6 | `shadow_discrepancy_floor_of_budget`: the signed coefficientwise `hbudget` implies `theta μ₂ j + 1 ≤ dv2Hgt (shadowDev T g j - dev Φ₂ g j)`. | `budgetFloor_le_iff` (`leanfinal/Uniformity/ChapC/C52.lean:85-93`), `le_WT_of_forall_wtCoeff` (`leanfinal/Uniformity/ChapC/C131w.lean:100-105`), `dev_coeff_paid_floor`, `dv2Hgt_dev_floor`, and `shadow_discrepancy` (`leanfinal/Uniformity/ChapC/C131w.lean:196-246`; `leanfinal/Uniformity/ChapC/C131w.lean:395-403`; `leanfinal/Uniformity/ChapC/C131v.lean:674`). | **New upward bridge:** reindex the signed nested `dev` coefficients as the two-variable normal-form grid, convert every budget floor to weight `μ₂E₂+1`, run the paid carry ledger, then pay `jE₂` to obtain `theta+1`. This reverses the *API direction* of the existing headline proof but should reuse its internal ledgers. | 140–240 lines; split “hbudget → WT” (60–100) from “WT → discrepancy” (80–140). |
| F3.7 | `shadow_discrepancy_add`: discrepancy of `a+b` is the sum of discrepancies. | F3.5 plus B32a `dev_add_of_monic`; the latter's exact shape is probed at `leanfinal/scratch/DEC4_check.lean:193-201`. | Ring normalization after the two additivity rewrites. | 10–20 lines. |
| F3.8 | exact signed `shadow_persistence`. | Touch certificate, F3.6–F3.7, and `dv2Hgt_add_eq_left_of_lt` (`leanfinal/Uniformity/ChapC/C131y.lean:557-584`). | First conjunct is F3.6. For the second, decompose the total discrepancy as key-power discrepancy plus the strictly deeper `g` discrepancy; `TouchCert` pins the first at `theta`, F3.6 puts the second at `≥ theta+1`, and strict-add stability preserves the first height. | 25–45 lines. |

## Ordering recommendation

1. **F2.1–F2.2 first.** They are already complete Lean proofs, carry no cite, and permanently
   remove the falsely advertised “new norm/resultant mathematics” from C.27.
2. **F3.5 next.** It is also probe-complete and reduces RB3's persistence work to one precise
   height bridge.
3. Run both RB3 Python certificates, then do **F3.1–F3.4** and **F3.6–F3.8**. These have local,
   falsifiable specifications and do not wait on `BlockFrontier`.
4. Run a small ramified determinant battery and execute **F2.3–F2.7**. This closes the missing
   frame-key read and therefore the high-leverage general-`ℓ` C.59/C.61 chain before attempting
   arbitrary-`C` exactness.
5. Execute **F1.H0–H3**, then the conditional family in dependency order
   F1.1 → F1.2 → F1.3 → F1.4 → {F1.5,F1.6} → F1.7 → F1.8.
6. Only then claim **F2.G1–G3**, because the corpus explicitly places arbitrary-`C` exactness
   above factor-label heredity.

This order starts with 75–110 lines whose proofs already exist, converts two broad diagnoses
into narrow research nodes, and postpones the largest `dv`-graded Hensel engine until its API
consumers have been written conditionally.

## Fence — held items not planned here

The following are deliberately outside every node table:

- C.100 `gentow2_Bp` and `gentow2_Bp_unit_iff`: held on **OPEN-EVAL-ISO**
  (`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md:15-18`).
- C.102 `letter_formula` and `gentow5w_one_shape`'s `htie`: held on **OPEN-LETTERS** (and the
  associated evaluation bridge); the signed commentary identifies `htie` as the missing law
  (`leanspec/Leanspec/ChapC.lean:3819-3824`).
- `peel_row_law`: held because `PeelLeg` is not yet designed; PROJECT_STATE records that exact
  fence (`docs/PROJECT_STATE.md:97-99`).
- `hprev`/`hcop` satisfiability at μ₃: owned by DEC3R, not this plan
  (`docs/PROJECT_STATE.md:85-88`, `docs/PROJECT_STATE.md:97-99`).

No node above may absorb, assume, or re-sign any of these obligations.
