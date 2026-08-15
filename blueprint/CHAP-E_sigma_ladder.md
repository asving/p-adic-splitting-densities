# CHAPTER E — THE σ-LADDER (T2's master suite, the HE7 rung machinery, and the ladder's σ dictionary)

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs), under
`blueprint/CONVENTIONS_2026-08-15.md` (GC-1…GC-14 + BRIEF E; Part V owner ruling in force).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **E = σ-LADDER MASTER** — 105 DAG
nodes by the old cut (`EFF-T2` alone). **The czar ruling (BRIEF E, ratified Part IV item 2 /
Part V item 2) adds `EFF-HE7`** (137 units: the `(SLOT₂)/(LIFT₂)` level-2 machinery and the HE7.A
master suite) to this chapter. **True planning figure: 242 source units** (105 T2 + 137 HE7),
of which the node-bearing mathematical mass is far smaller — T2 is an ACCEPTED T-unit whose late
units are acceptance-boxes/fences/changes-records, and HE7's records likewise; the unit-by-unit
disposition census (§13) accounts for every one of the 242. **Blueprint node count: 68 nodes**
(§2's index is the authority; the census disposes the rest).
**Sources transcribed:** `spec/EFF-T2.md` (105 units, contiguous, merged from six shards) and
`spec/EFF-HE7.md` (137 units, contiguous, merged from three shards). Both cited at merged,
contiguous IDs per GC-12.
**Supplier chapters consumed:** **H §8 ONLY** (H.51–H.58, the slot/lift layer — the sanctioned
entry point per GC-5/H-14; H.54's `normIdx` is WITHDRAWN and is not consumed), **B** (§7/§9 by
committed node ID, on the `e₁ = 1` slice only), **C** by GC-13 placeholder (level data, twist/ϖ
layer, class-size counts), **D** by GC-14 anchor (the ϑ-orientation table), **A/G** (the landed
kernel) by declaration name.
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle). New definitions in
`Uniformity.Density.Ladder` (GC-6.2).
**Authored:** 2026-08-15, Fable-max arm (append #56 substitution regime).
**CODEX CROSS-READ OWED** (queued post-Tuesday per the budget regime; a Fable-max fresh-context
read may discharge the obligation earlier per Part IV item 6's precedent).

---

## 0. How to read this chapter

### 0.1 The standing environments (chapter-prefixed per GC-6.3)

Every node names its environment as `ENV-E1` … `ENV-E4` plus deltas. Bare `ENV-A/B/C` are retired.

**ENV-E1 — the arithmetic arena** (the ladder's exponent/height bookkeeping; no `O`):

```lean
import Uniformity
namespace Uniformity.Density.Ladder
open Finset
```

**ENV-E2 — the density arena** (= CHAP-H's ENV-H2, verbatim; stated here in full per GC-6.3):

```lean
import Uniformity
namespace Uniformity.Density
open IsLocalRing Polynomial Filter Topology
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}
```

`ENV-E2′` abbreviates ENV-E2 with `π` promoted to an explicit hypothesis `(hπ : Irreducible π)`
(landed precedent `Drainage.lean:85`, `DensityAPI.lean:124`).

**ENV-E3 — the stage-field arena** (= CHAP-H's ENV-H4, verbatim — pure finite-field algebra, no
`O`; abstract-then-instantiate per GC-7):

```lean
import Uniformity
namespace Uniformity.Density.Ladder
open Polynomial
variable {F K : Type*} [Field F] [Finite F] [Field K] [Finite K] [Algebra F K]
```

**ENV-E4 — the polygon/support arena** (CHAP-B's D-1 objects consumed by node ID; the slot-seam
evaluation layer): ENV-E2 plus CHAP-B's development/`suppVal`/`npHgt` API in scope by import of
the (future) landed `ChapB` modules. Per GC-1, every residual-read pin in this arena is the
`sideMin` pin; per GC-2, every polygon statement is an argmin/support-function statement — no
hull object, no `ℚ`.

Environments are declared per NODE, not per section (GC-6.4). `[Finite (ResidueField O)]`
appears only where a node counts or names `Res`/`Coeff`/`residueCard`/`DecidedAt`-family objects.

### 0.2 File layout and naming (GC-6)

* One Lean file per node: `leanfinal/Uniformity/ChapE/E<nn>.lean`, module
  `Uniformity.ChapE.E<nn>`; micro-nodes suffix a letter (`E10a.lean`).
* Chapter roll-up `leanfinal/Uniformity/ChapE.lean` imports node modules in this file's
  topological order; `Uniformity.lean` gains one line. `ChapE.lean` imports `Uniformity.ChapH`
  (for H.51–H.58 ONLY — consuming any other H node from E is a blueprint defect, GC-5) and the
  future `Uniformity.ChapB` modules named in DEPENDS fields.
* New *definitions* live in `Uniformity.Density.Ladder`; new *theorems about landed objects* live
  in `Uniformity.Density`. Other chapters' sub-namespaces (`.Menu`, `.Leaf`, `.Induction`,
  `.Tower`, `.Gauge`) are READ, never extended.
* One PUBLIC declaration per node; reusable helpers trigger RE-PLAN, never a silent second name.
* Leanspec stubs wrap in `namespace LeanspecE` (GC-6.6), file `leanspec/Leanspec/ChapE.lean`;
  gate order = CHAP-H §15's (elaborate fragile signatures → land `def` bodies → run the §10
  numeric block at `q = 2` AND `q = 3` → only then sign `axiom` stubs).

### 0.3 Names that already exist and must not be redefined

**From `Uniformity.Density` (chapter A, the landed kernel).** Consumed by name:
`FactorizationType`, `FactorizationType.degree`, `FactorizationType.degree_mk_add`, `typeOf`,
`typeOf_degree`, `typeOf_mul`, `monicFactors`, `efPair`, `ramIndexOf`, `inertiaDegOf`,
`Coeff`, `Res`, `proj`, `residueCard`, `two_le_residueCard`, `DecidedAt`, `decidedAt_of_congr`,
`UniformityStatement`, `UniformityStatement.ofDecided`, `DrainageAt`.

**From `Uniformity.Density.Induction` (CHAP-H §8, the sanctioned slice H.51–H.58 ONLY).**
`class_sep`, `class_sep_bij` (H.51); `slot_height_injective`, `slot_min_unique` (H.52);
`eta_independent` (H.53); `stageLift'` (H.54 — the SIGNED form; `normIdx` is WITHDRAWN and no
chapter-E node consumes it); `stageLift_index_lt`, `stageLift_integral`, `stageLift_height`
(H.55); `stageLift_summand_eq` (H.56); `wrap_div_mod`, `wrap_height` (H.57); `divMod_bij`,
`card_composedBasis` (H.58). Also `GenreDatum` and its derived fields (H.01/H.02), which the
H.51–H.58 signatures carry — consumed as their parameter types, nothing more of H.

**From CHAP-B (committed blueprint node IDs; `e₁ = 1` slice).** By node ID per GC-13(b):
B.19/B.20 (`suppVal`, side lengths), B.28–B.30 (`resPoly` + correctness under the `sideMin` pin,
GC-1/PA-1), B.51 (residual index), B.58 (the order-1 `(e,f)` read), B.63/B.73/B.74 (separability
hypothesis + `NeedsDescent`, as REPAIRED by PA-1), B.77 (`resPoly_congr`, convention-free),
B.79–B.82 (level-`N` certificates).

**From chapters C and D (unauthored at composition time).** GC-13(c) placeholders only —
`EFF.<NOTE>.<nn> [supplied-by: chapter C]` — and GC-14 anchors for the ϑ table (chapter D owns
the canonical copy; no chapter-E node restates its content).

### 0.4 The chapter's mathematical spine, in one page

T2 is the corpus's σ-ladder MASTER: it does not prove new ladder mathematics — it *organizes*
the HE-chain's rung results (HE7's level-2 `(SLOT₂)/(LIFT₂)` machinery, HE6's seam evaluations,
HE6R1's level dictionary) into one master suite, `HE7.A`, whose five clauses
`[ACCOUNT, RES-DEG, nonempty, exhaust, root-continuation]` are Display A's `HE7A[…]` conjunct.
The chapter's Lean character therefore splits three ways, exactly as CHAP-H's did:

| layer | corpus content | Lean character | sections |
|---|---|---|---|
| **carrier/schema** | the rung datum, the ladder as iterated rungs, the HE7.A clause family | `structure`s with hypothesis fields at EXACTLY corpus strength (the `StageInterface` lesson) | §3, §4 |
| **algebraic/arithmetic** | slot-seam exponent bookkeeping, the level-2 slot/lift laws (SLOT₂/LIFT₂), degree conservation, the σ dictionary | provable outright from H.51–H.58 + B's API + `ℕ` arithmetic | §5, §7 |
| **carried hypotheses** | (LB1), (MP1), `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` (∀ i ≥ 3), the μ ≥ 3 σ-decision, exhaust/root-continuation at depth | NOT provable at transcription grade — named, indexed hypothesis carriers handed to chapter I | §4, §6, §8, §9 |

The terminal supply — what H's §11 dictionary and the drainage recursions consume from E — is
named prominently in §2 and §7: the **ladder transport laws** (`ladderSigma` + its degree
conservation `ladderSigma_degree`, the rung-composition law `rungStep_sigma`) and the
**stage-transport carriers** (`RungInterface` instances). GC-4 binds every σ output: every
σ-valued thing in this chapter is a `Uniformity.Density.FactorizationType` produced by a named
dictionary function shipping a degree-conservation lemma.

---

## 1. HONESTY BLOCK (read before consuming any node)

**E-1 — THE HE6/T2 ADJUDICATION (HYP.150–154) GOVERNS THE 48 SLOT-SEAM CITES.** *(Detailed
dispositions in the nodes; summary here.)* `EFF-HE6.md` OPEN-CALL 2 found that A3 corrections
F-1/F-3/F-4 land outside every one of T2's nine HE6 pin spans, with F-1 rendering the frozen
`HE6-SLOT-SEAM` bare display VACUOUS (affirmatively FALSE for `k > (D′−1)h`, HYP.151) while T2
cites that span 48×. The adjudication (T2 EOF append, commit `66062771`; ledger rows HYP.150–154,
v7) returns: T2's own `(GAMMA)`/`(HE6-SEAM)` displays already ARE F-1's corrected form
letter-for-letter, so **no chapter-E node ever transcribes the bare pre-A3 `HE6-SLOT-SEAM`
display**; every seam evaluation in §5 is stated in the corrected `γ_k(A)` form via T2's own
displays. HYP.154: T2 consumes NO disk criterion (`LEMMA HE6-0`) — no E node states one; a
consumer needing HE6-0 is a chapter-cut concern outside E (route: the C placeholder layer).
**Residual carried honestly:** HYP.150 is scoped to T2 ONLY; HE7's own consumption of the three
A3-corrected HE6 spans is UNCHECKED at the ledger (HYP.150's explicit residual). Every §4/§5 node
whose SOURCE is an HE7 unit citing an HE6 span therefore carries the flag `[HE6-A3-UNADJUDICATED
FOR HE7]` and states the content from HE7's own displays, never from HE6 frozen text.

**E-2 — the nine HE6 pin anchors resolve per the F1 routing, and two of them leave the chapter.**
The pin anchors (`EFF.HE6.09 .13 .14 .15 .17 .29 .30 .32 .56`) resolve to CHAP-B node IDs only on
the `e₁ = 1` slice (where B transcribed them). The class-size/count route in `.30`/`.32` is
CHAP-B's H-2 refusal — it must come from chapter C (Brief C trap (i) owns the decision), and the
`e₁ ≥ 2` twist/ϖ-normalizer content of `.13`/`.14` is CHAP-B H-1 out-of-scope: both resolve to
**chapter-C GC-13 placeholders** (`EFF.HE6.30/.32 [supplied-by: chapter C]`,
`EFF.HE6.13/.14 [supplied-by: chapter C]`), never to HE6 frozen text and never to a nonexistent
B node. No chapter-E node may cite those four anchors any other way.

**E-3 — the σ-decision at `μ ≥ 3` is `BLOCKED: HYP.81` for everyone, and the ladder CARRIES it,
never proves it.** (First live `n = 6`.) The ladder's σ dictionary (§7) extends H §11's σ-decision
content ALONG the ladder — i.e. transports σ through rungs — which is exactly GC-5's `hsigma`
assignment to E. What E does NOT do: decide σ at a stage leaf of multiplicity `μ ≥ 3`. Every node
whose corpus text touches that case carries `(hσ₃ : …)` as an explicit hypothesis field routed to
chapter I's hypothesis block, or returns `BLOCKED: HYP.81`. A fleet agent reaching for a `μ ≥ 3`
σ-decision has left the chapter.

**E-4 — (LB1) and (MP1) are Display A conjuncts and their disposition is decided per node, not
assumed.** BRIEF E clause (2): if a discharge exists in T2's effective text, it is a discharge
node; else a carried hypothesis routed to I (Part V: each such carry must terminate as a
discharge node or a literature cite through owner gate (b) — no third category). §6 records the
adjudication per unit with T2's own text quoted.

**E-5 — `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` (Display A's `∀ i ≥ 3` conjunct) are INDEXED CARRIERS.**
E supplies the named, `i`-indexed hypothesis structures (§9); the `𝒲_(≤i)` content itself is
chapter D's w-frame (T5) by GC-13, and the ϑ-residue content cites chapter D's canonical
orientation table by anchor (GC-14) — no chapter-E node restates the four-way table, and no
chapter-E node adjudicates the ϑ ↔ ϑ_t correspondence.

**E-6 — the q = 2-only coincidence regime is a standing trap in exactly this chapter's numerics.**
HYP.151's own witness `(e₁,f₁,h) = (2,2,3)`, `k = 3` sits in the coincidence regime
`k ≤ (D′−1)h` where bare and corrected seam readings agree — four hostile rounds missed the
defect for exactly that reason. Chapter E's gates (§10) therefore include a seam witness in the
NON-coincidence regime `k > (D′−1)h` at BOTH `q = 2` and `q = 3`, plus an `e > 1 ∧ f > 1`
witness (GC-11). A gate that only exercises `k ≤ (D′−1)h` is a defect.

**E-7 — the 44-edge cluster at `EFF.T2.31` is a governing-unit placeholder artifact.** The edges
land there because citing designations were unresolved at harvest time (DAG_README's gov rule),
not because `.31` is the real consumer. This chapter's DEPENDS fields re-home those edges unit by
unit; §11's DAG-addition rows carry the re-homing with contiguous IDs in the evidence column
(GC-12).

**E-8 — `HEX3-BOX-1` (HYP.137) is a NON-NODE here**, as in G (H-2) and H (H-4). A fleet agent
needing the tail-σ certification lemma returns `BLOCKED: HYP.137`.

**E-9 — no every-lift weakening (GC-9), even where T2's prose quantifies over `disc ≠ 0` roots.**
Ladder certificates conclude `DecidedAt` unweakened; σ is read through `monicFactors`/`typeOf`
(total on monic polynomials); divergences from root-read prose are flagged per node in
FAITHFULNESS. No uniform-`N` law anywhere (GC-9.3): certificates are per-member at explicit `N`.

**E-10 — transcription grade (GC-10) governs T2 nodes; HE7 nodes inherit the same rule.** T2 is
an ACCEPTED T-unit: the EFF canonical statements are the spec; fresh mathematics enters only via
a dated AMENDMENT block. Trichotomies/case splits are re-derived from the note's own displays,
never from a verifier's phrasing (the GENH4-CAP `[r2]` lesson); no false-reason parentheticals
are transcribed (the WZ-BOX-7 lesson — side with conclusions).

**E-11 — codex cross-read status: OWED.** Flagged items aggregated in §14.

*(Amendments to this block as composition proceeds are dated in place.)*

---

## 2. NODE INDEX

*(committed early; refined per section as composed — the per-section node lists below are the
authority once their section is composed; counts updated at completion)*

| § | nodes | content |
|---|---|---|
| 3 | E.01–E.09 | **THE RUNG/LADDER SCHEMA**: the rung datum, the ladder carrier, the reconciliation to `GenreDatum`/H §8 |
| 4 | E.10–E.24 | **THE MASTER HE7.A SUITE**: the five clauses `[ACCOUNT, RES-DEG, nonempty, exhaust, root-continuation]` as fields + the five instance records |
| 5 | E.25–E.38 | the slot-seam evaluation layer (corrected `γ_k(A)` form; B's `suppVal` API; SLOT₂/LIFT₂) |
| 6 | E.39–E.44 | (LB1)/(MP1): adjudicated dispositions |
| 7 | E.45–E.54 | **the σ dictionary + degree conservation** (GC-4; terminal supply) |
| 8 | E.55–E.60 | root-continuation / exhaust clauses at ladder depth |
| 9 | E.61–E.64 | the `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` indexed carriers |
| 10 | E.65–E.68 | gates (GC-11: `q = 2` AND `q = 3`; non-coincidence seam witness; `e > 1 ∧ f > 1`) |
| 11 | — | DAG additions (incl. the EFF.T2.31 re-homing rows) |
| 12 | — | leanspec stub list (stage 0e, `LeanspecE`) |
| 13 | — | unit-disposition census (all 242 source units) + TEETH summary (GC-8) |
| 14 | — | flagged for the codex cross-read |

**Terminal supply (what other chapters consume from E), named now:** `RungDatum` (E.01),
`RungInterface` (E.10) with the HE7.A clause fields, `LadderData` (E.05), the σ dictionary
`ladderSigma` + `ladderSigma_degree` (E.45/E.46), the rung transport law `rungStep_sigma` (E.48),
the stage-transport/composition laws (E.49–E.51), the indexed carriers `VarthetaRes` / `WFrame`
(E.61/E.62), and the HE7A conjunct package `HE7APackage` (E.24) — the object chapter I's
hypothesis block receives.

---

## 3. §3 — THE RUNG/LADDER SCHEMA

> **Design note (the `GenreDatum`/`StageInterface` lesson, one level up).** T2's carrier `𝒞` and
> HE7's level datum `𝔇_i` (DEFINITION HE7-2 as corrected by ANNEX-DEF HE7-2′, `EFF.HE7.107`) are
> the corpus's own schema objects. Chapter E transcribes their **arithmetic core** as `RungDatum`
> (E.01) — provable-outright exponent bookkeeping lives on it (§3, §5) — and their **carrier
> content** as the hypothesis-field structures of §4. The split is exactly CHAP-H's three-layer
> architecture: arithmetic = theorems, carrier = fields, σ = dictionary (§7).

### NODE E.01 [def] [fresh]

**STATEMENT.** *The rung datum.* A **rung** consists of natural numbers `ℓ, g, u, T` subject to:
`1 ≤ ℓ` (the slope denominator = the rung's value-group index), `1 ≤ g` (the residual-factor
degree = the rung's residue-degree jump), `Nat.Coprime u ℓ` (the slope `λ = u/ℓ` in lowest
terms), and the **node condition** `ℓ * T < u` (i.e. `λ > T`, DEFINITION HE7-2's `λ_i > T_i`).
This is the arithmetic core of `EFF.HE7.47`'s level datum `𝔇_i = (Φ_i, D_i, w_i, ℓ_i, g_i, u_i,
K_i, K_{i+1}, 𝒫_i)` — the polynomial `Φ_i`, the fields `K_i ⊆ K_{i+1}` and the point set `𝒫_i`
are carrier data and live in §4's structures, never here. The **base rung** (level 0 → 1) is
`(ℓ, g, u, T) = (e₁, f₁, h, 0)` — `EFF.HE7.47`'s `𝔇_0` with `T_0 := 0`; the node condition
degenerates to `1 ≤ h`. The **level-2 rung** is `(ℓ, d_r, u, D′h)` with `u = ℓλ > ℓD′h`
(DEFINITION HE7-1's `λ > D′h`, `EFF.HE7.06`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- A **rung datum**: the arithmetic core of one σ-ladder level (`EFF.HE7.47`/`.107`).
`ℓ` = slope denominator (value-index jump), `g` = residual degree (residue-degree jump),
`u` = slope numerator, `T` = the rung's disk threshold; `ℓ*T < u` is the node condition
`λ > T`. -/
structure RungDatum where
  ℓ : ℕ
  g : ℕ
  u : ℕ
  T : ℕ
  hℓ : 1 ≤ ℓ
  hg : 1 ≤ g
  hcop : Nat.Coprime u ℓ
  hnode : ℓ * T < u
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE7.47` (DEFINITION HE7-2's tuple, the clauses `ℓ_i ≥ 1, g_i ≥ 1, u_i ∈ ℤ with
gcd(u_i, ℓ_i) = 1`, the node condition `λ_i > T_i`, and the level-0 datum); `EFF.HE7.06`
(DEFINITION HE7-1: `λ = u/ℓ ∈ ℚ` lowest terms, `λ > D′h`, `d_r := deg r`); `EFF.T2.04`
(`(DEG-EF)` — the carrier's `D = e_𝒞 f_𝒞`, which §4 carries as a field, NOT inferred from
monicity).

**⚠ CARRIER FENCE.** `u : ℕ`, not `ℤ`: every consumed height in the corpus sits strictly above
the rung's threshold (`EFF.HE7.24`'s use-site chain), and `T ≥ 0` with the node condition forces
`u ≥ 1`. A node that provably needs a negative `u_i` must return RE-PLAN (none exists in T2/HE7's
effective text — the level-`i` slopes satisfy `λ_i > T_i ≥ 0`). The normalizer `ϖ = x^{i₀}π^{a₀}`
with possibly `a₀ < 0` (`EFF.HE7.05`) is chapter-C carrier content (honesty E-2), not a rung
field.

**TEETH.** HE7-T-SLOT2TIE (`EFF.HE7.06`: at `gcd(u, ℓ) ≠ 1` the slot-min is not exact — the
`hcop` field is machine-load-bearing) → the field makes the tooth's hypothesis structural.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.02 [def] [fresh]

**STATEMENT.** *Derived rung data.* For a rung `R`: the **slot count** `L = ℓ * g`
(`EFF.HE7.47`'s `L_i := ℓ_i g_i`); the **next threshold** `nextT = L * u` (`T_{i+1} := L_i·u_i`);
the **degree multiplier** (the key-degree recursion `D_{i+1} := D_i·L_i` is `degMul = L`); and the
**bound step** `nextBound b = (L − 1) * u + ℓ * b` (`EFF.HE7.23`'s recursion
`bound_{i+1} = (ℓ_i g_i − 1)·u_i + ℓ_i·bound_i`, `bound_0 = 0`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- `L = ℓg`, the number of slots the rung's key-development occupies. -/
def RungDatum.slotCount (R : RungDatum) : ℕ := R.ℓ * R.g

/-- `T' = L·u`, the next level's disk threshold (`EFF.HE7.47`). -/
def RungDatum.nextT (R : RungDatum) : ℕ := R.slotCount * R.u

/-- One step of the (LIFT) threshold recursion (`EFF.HE7.23`):
`bound' = (L−1)·u + ℓ·bound`. -/
def RungDatum.nextBound (R : RungDatum) (b : ℕ) : ℕ :=
  (R.slotCount - 1) * R.u + R.ℓ * b
```

**DEPENDS.** E.01.

**PROOF.** definitional.

**SIZE.** 12 lines.

**SOURCE.** `EFF.HE7.47` (the displayed recursions `L_i := ℓ_i g_i`, `D_{i+1} := D_i L_i`,
`T_{i+1} := L_i·u_i`); `EFF.HE7.23` (the bound recursion, one formula for the whole ladder —
"**explicitly preserved by ANNEX R**: 'The bound recursion is unchanged — values never see the
twist'"); `EFF.HE7.06` (`T₂ := ℓd_r·u`, the level-2 instance).

**ARITHMETIC AUDIT (recomputed fresh).** Base rung `(e₁,f₁,h,0) = (2,1,1,0)`: `L = 2`,
`nextT = 2·1 = 2`... at the n = 8 frame (`EFF.HE7.57`) the level-2 rung is `(ℓ,d_r,u,T) =
(2,1,u,2u′)` — with base `(2,1,1,0)`: `bound₁ = nextBound 0 = (2−1)·1 + 2·0 = 1 = (D′−1)h ✓`
(`D′ = 2, h = 1`). Level-2 rung `(2,1,5,2)` (the Q3 frame `(2,1,1,2,1,5)`):
`bound₂ = (2·1−1)·5 + 2·1 = 7 ✓` (Q3 table: `thr₂ = 7`). Frame `(2,1,1,2,2,5)` → rung
`(2,2,5,2)`: `bound₂ = (4−1)·5 + 2·1 = 17 ✓`. Frame `(3,1,2,2,3,13)` → base `(3,1,2,0)`:
`bound₁ = (3−1)·2 = 4 = (D′−1)h` with `D′ = 3, h = 2` ✓; rung `(2,3,13,6)`:
`bound₂ = (6−1)·13 + 2·4 = 73 ✓`. **Three of the five Q3 frames re-derived exactly** (all five
are E.68's gate).

**TEETH.** Q3 / HE7-LIFT2 (`EFF.HE7.23`: five level-2 frames' thresholds verified against
exhaustive enumeration) → **Lean theorem** at E.31/E.35 with these definitions; the numeric leg
re-fires at E.68.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.03 [lemma] [fresh]

**STATEMENT.** *The normalizer exponents exist and are unique (Bézout at the rung).* For a rung
`R` and every `k : ℤ` there are unique `m : ℤ` and `s : ℕ` with `s < ℓ` and
`ℓ * m + s * u = k`. This is `EFF.HE7.06`'s "`ℓ·m(k) + s(k)·u = k` with `0 ≤ s(k) < ℓ` — possible
and unique because `gcd(u, ℓ) = 1`", the exponent content of the normalizer system
`n_{i+1}(k) := n_i(m_i(k))·Φ_i^{s_i(k)}` (`EFF.HE7.107`, ANNEX-DEF HE7-2′). The normalizer
POLYNOMIAL is carrier content (§4/chapter C); this node is its exponent bookkeeping only.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem normExp_exists_unique (R : RungDatum) (k : ℤ) :
    ∃! p : ℤ × ℕ, p.2 < R.ℓ ∧ (R.ℓ : ℤ) * p.1 + (p.2 : ℤ) * (R.u : ℤ) = k

/-- The slot exponent `s(k)`: the unique `s < ℓ` with `s·u ≡ k (mod ℓ)`. -/
noncomputable def RungDatum.sExp (R : RungDatum) (k : ℤ) : ℕ :=
  (normExp_exists_unique R k).choose.2

/-- The carry exponent `m(k)`: `(k − s(k)·u)/ℓ`. -/
noncomputable def RungDatum.mExp (R : RungDatum) (k : ℤ) : ℤ :=
  (normExp_exists_unique R k).choose.1
```

**DEPENDS.** E.01 · mathlib `Nat.Coprime`, `ZMod.unitOfCoprime` (or `Nat.chineseRemainder`-free
route: `Int.emod`/`Int.ediv` on `k * u⁻¹ mod ℓ`).

**PROOF.**
1. Existence: `gcd(u, ℓ) = 1` gives `u` invertible mod `ℓ`; set `s := (k * u⁻¹) % ℓ` computed in
   `ZMod ℓ` lifted by `ZMod.val` (`0 < ℓ` from `R.hℓ`), so `ℓ ∣ k − s*u`; set
   `m := (k − s*u) / ℓ` (`Int.ediv_emod_unique`).
2. Uniqueness: if `ℓm + su = ℓm′ + s′u` then `ℓ ∣ (s − s′)u` over `ℤ`, coprimality gives
   `ℓ ∣ s − s′`, and `s, s′ < ℓ` forces `s = s′` (the H.51 pattern one letter over), then
   `m = m′` by cancellation (`Int.eq_of_mul_eq_mul_left`, `ℓ ≠ 0`).

**SIZE.** 24 lines. **SPLIT CANDIDATE:** land the `∃!` lemma as the public contract; `sExp`/`mExp`
may ride a second file (`E03a`) if `choose`-plumbing runs long — but consumers (E.04, E.33)
should take `s`/`m` as explicit arguments with the defining equation as hypothesis (the H.54
`stageLift'` lesson) wherever possible.

**SOURCE.** `EFF.HE7.06` (the `n₂(k)` display and its Bézout clause); `EFF.HE7.107` (the
recursion's `ℓ_i·m_i(k) + s_i(k)·u_i = k, 0 ≤ s_i(k) < ℓ_i`, "possible and unique because
`gcd(u_i, ℓ_i) = 1`").

**TEETH.** Q2 / HE7-SLOT2 (12,632 exactness identities ride this bookkeeping) → the arithmetic
half becomes a **Lean theorem** here.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.04 [lemma] [fresh]

**STATEMENT.** *The cocycle exponent is 0 or 1, and the carry identity.* For a rung `R` and
`a, b : ℤ`, with `s := R.sExp`, `m := R.mExp`: `s a + s b − s (a+b) ∈ {0, ℓ}`; writing
`c := (s a + s b − s (a+b)) / ℓ ∈ {0, 1}`, one has `m a + m b = m (a+b) − c * u`. This is
ANNEX-LEMMA R1-a(ii)'s arithmetic half (`EFF.HE7.108`): the exponent bookkeeping behind
`τ_{i+1}(a,b) = Λ_i^c · τ_i(m(a), m(b)) · τ_i(m(a)+m(b), c·u)` — the letter-monomial residue
itself is carrier content (E.33 states its exponent law; the residue law is a §4 field/C
placeholder). At the base rung the level-1 cocycle is trivial (`τ₁ ≡ 1`: `k ↦ ϖ^k` is a
homomorphism — R1-a(ii), "THE point of the re-based system").

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem cocycle_exp_mem (R : RungDatum) (a b : ℤ)
    (sa sb sab : ℕ) (ma mb mab : ℤ)
    (ha : sa < R.ℓ ∧ (R.ℓ:ℤ) * ma + sa * R.u = a)
    (hb : sb < R.ℓ ∧ (R.ℓ:ℤ) * mb + sb * R.u = b)
    (hab : sab < R.ℓ ∧ (R.ℓ:ℤ) * mab + sab * R.u = a + b) :
    (sa + sb - sab : ℤ) = 0 ∨ (sa + sb - sab : ℤ) = R.ℓ

theorem cocycle_carry (R : RungDatum) {a b : ℤ} {sa sb sab : ℕ} {ma mb mab : ℤ}
    (ha : sa < R.ℓ ∧ (R.ℓ:ℤ) * ma + sa * R.u = a)
    (hb : sb < R.ℓ ∧ (R.ℓ:ℤ) * mb + sb * R.u = b)
    (hab : sab < R.ℓ ∧ (R.ℓ:ℤ) * mab + sab * R.u = a + b)
    {c : ℤ} (hc : (sa + sb - sab : ℤ) = c * R.ℓ) :
    ma + mb = mab - c * R.u
```

**DEPENDS.** E.01, E.03 (uniqueness, for the `mod ℓ` congruence) · mathlib `Int.emod_emod_of_dvd`.

**PROOF.**
1. `cocycle_exp_mem`: adding the two defining equations and subtracting the third:
   `ℓ(ma + mb − mab) + (sa + sb − sab)·u = 0`, so `ℓ ∣ (sa + sb − sab)·u`, coprimality gives
   `ℓ ∣ sa + sb − sab`; the range `−ℓ < sa + sb − sab < 2ℓ` (from the three `< ℓ` bounds)
   leaves `{0, ℓ}` (R1-a(ii)'s own range argument, verbatim).
2. `cocycle_carry`: substitute `sa + sb − sab = c·ℓ` into the displayed combination and cancel
   `ℓ ≠ 0`. `omega` after `push_cast`.

**SIZE.** 22 lines.

**SOURCE.** `EFF.HE7.108` (R1-a(ii), verbatim: "`s_i(a) + s_i(b) − s_i(a+b)` lies in
`(−ℓ_i, 2ℓ_i)` and is `≡ 0 mod ℓ_i`, so it is 0 or `ℓ_i`, i.e. `c ∈ {0,1}`; applying
`ℓ_i·(·) + u_i·(s-identity) = 0` gives `m_i(a) + m_i(b) = m_i(a+b) − c·u_i`"); `EFF.T2.07`
(`(COC)`, the cocycle identity this bookkeeping feeds); `EFF.HE7.08` (the level-2 instance
`c := (s(k) + s(k′) − s(k+k′))/ℓ ∈ ℤ`, sharpened to `{0,1}` by R1-a — "the display is not
edited, and `{0,1} ⊂ ℤ` so nothing conflicts").

**TEETH.** `he7rannex_supp.py` (the Λ₂Λ₁-monomial twist arithmetic, 102 slot instances, exponent
value identity held on every computed monomial) → **Lean theorem** for the exponent half.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.05 [def] [fresh]

**STATEMENT.** *The ladder.* A **ladder** is a base rung together with a list of higher rungs,
chained by the threshold recursion: the base has `T = 0`, and each successive rung's threshold is
the previous rung's `nextT` (`T_{i+1} = L_i·u_i`). Derived along the ladder: `degAt i` (the
key-degree at level `i`, `D_{i+1} = D_i·L_i`, seeded by `D₀`), and `boundAt i` (the (LIFT)
threshold, `EFF.HE7.23`'s recursion seeded at `0`). The level-1 instance reconciles with CHAP-H's
`GenreDatum`: a `GenreDatum G` yields the base rung `(G.e₁, G.f₁, G.h, 0)` (the slot/lift layer
H.51–H.58 is stated on exactly these three numbers), and with CHAP-B's polygon data on the
`e₁ = 1` slice (B.11 `npHgt`, B.14 `suppVal` — the level-1 heights E's seam layer reads).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The threshold chain: rung `r'` follows `r` when `r'.T = r.nextT`. -/
def rungFollows (r r' : RungDatum) : Prop := r'.T = r.nextT

/-- A **ladder**: base rung (threshold 0) + chained higher rungs. -/
structure LadderData where
  base : RungDatum
  rungs : List RungDatum
  hbase : base.T = 0
  hchain : List.Chain rungFollows base rungs

/-- The key degree at level `i+1` (`D₀` the seed; `D_{i+1} = D_i·L_i`). -/
def LadderData.degAt (Λ : LadderData) (D₀ : ℕ) : ℕ → ℕ
  | 0 => D₀ * Λ.base.slotCount
  | (i+1) => Λ.degAt D₀ i * ((Λ.rungs.get? i).map RungDatum.slotCount |>.getD 1)

/-- The (LIFT) threshold at level `i+1` (`EFF.HE7.23`). -/
def LadderData.boundAt (Λ : LadderData) : ℕ → ℕ
  | 0 => Λ.base.nextBound 0
  | (i+1) => ((Λ.rungs.get? i).getD Λ.base).nextBound (Λ.boundAt i)
```

**⚠ SIGNATURE NOTE.** The `get?`/`getD` spelling is a contract for TOTALITY, not elegance; a
fleet agent may land the recursion as a `List.foldl` over `rungs.take i` with a proved
equivalence, provided `degAt`/`boundAt` keep these names and types. The `getD 1`/`getD Λ.base`
defaults are never consulted at in-range indices (the consumers all carry `i < rungs.length`
hypotheses); an out-of-range read is not a corpus configuration.

**DEPENDS.** E.01, E.02 · mathlib `List.Chain`, `List.get?`.

**PROOF.** definitional.

**SIZE.** 30 lines.

**SOURCE.** `EFF.HE7.47`/`.107` (the level recursion; the level-0 datum `(x, 1, v, e₁, f₁, h,
F_Q, K, K̄₀)` with `T_0 := 0`; "levels 1 and 2 are byte-unchanged"); `EFF.HE7.23` (`bound_0 = 0`,
the displayed instances `bound₁ = (D′−1)h`, `bound₂ = (ℓd_r−1)u + ℓ(D′−1)h`); `EFF.T2.35`
(HE7-INSTANCE's `d = dv₂ = ℓ·dv = ℓe₁v`, `T = T₂ = ℓd_ru` — the value-normalization multiplier
`c_{i+1} = ℓ_i·c_i` is carried by the carrier, §4, not here).

**TEETH.** as E.02; E.68 executes the five-frame threshold table through `boundAt`.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.06 [lemma] [fresh]

**STATEMENT.** *Ladder telescoping (degree conservation along levels).* For a ladder `Λ` and
seed `D₀`: `Λ.degAt D₀ i = D₀ * (Λ.base :: Λ.rungs.take i).map slotCount |>.prod` — the level-`i`
key degree is the seed times the product of all slot counts through level `i`. In corpus letters:
`D″ = D′·ℓd_r`, `D_2 = D′·e₂f₂`, and in general `D_{i+1} = D₀·Π_j L_j` — the degree half of
`EFF.HE7.48`'s composed invariants `e = e₁ℓ_1⋯ℓ_{i+1}`, `f = f₁g_1⋯g_{i+1}` (whose `e·f`
product IS this telescoping, since `L_j = ℓ_j g_j`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem LadderData.degAt_eq_prod (Λ : LadderData) (D₀ : ℕ) (i : ℕ)
    (hi : i ≤ Λ.rungs.length) :
    Λ.degAt D₀ i = D₀ * ((Λ.base :: Λ.rungs.take i).map RungDatum.slotCount).prod
```

**DEPENDS.** E.05 · mathlib `List.prod_cons`, `List.take_succ`, `List.map_append`.

**PROOF.**
1. Induction on `i`. Base: `degAt D₀ 0 = D₀ * base.slotCount` and the list is `[base]` ✓.
2. Step: `take (i+1) = take i ++ [rungs.get i]` (in range by `hi`); `List.prod_append` and the
   recursion's multiplier agree; `ring`-normalize the association.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE7.48` (THEOREM HE7.D's composed `e`/`f` display); `EFF.HE7.06` (`D″ :=
D′ℓd_r`); `EFF.T2.36` (`D = D₂ = D′e₂f₂`); `EFF.T2.30` (`(FUND)` — `|Ω| = ef`, whose ladder
form this feeds at E.15/E.53).

**TEETH.** Q1's per-member `Σef = 8` at `n = 8` (`EFF.HE7.36` TEETH) → degree conservation is
the checkable shadow; E.46/E.67 carry the executable form.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.07 [lemma] [fresh]

**STATEMENT.** *The jump arithmetic (THEOREM HE7.C's bounds, exponent form).* Three clauses,
pure ℕ-arithmetic:
(i) **the jump floor**: if `2 ≤ m` and `2 ≤ p` then `4 ≤ m * p` (the corpus instance:
`L_λ ≥ ℓ·m·d_r = m·(ℓd_r) ≥ 2·2 = 4`, so `μ ≥ 4` at every level jump — the WIDENED condition
`ℓ·d_r ≥ 2`, both branches: `ℓ ≥ 2, d_r ≥ 1` and `ℓ = 1, d_r ≥ 2`);
(ii) **the halving**: if `2 ≤ p` and `μ₂ * p ≤ μ` then `2 * μ₂ ≤ μ` (the corpus's
`μ₂ ≤ μ/(ℓd_r) ≤ μ/2`, cleared of division);
(iii) **the jump count**: for `μ : ℕ → ℕ` with `4 ≤ μ i` for all `i ≤ J` and
`2 * μ (i+1) ≤ μ i` for all `i < J`: `2 ^ (J + 1) ≤ μ 0` — the cleared form of
`J ≤ log₂ μ − 1` (`EFF.HE7.15`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem jump_floor {m p : ℕ} (hm : 2 ≤ m) (hp : 2 ≤ p) : 4 ≤ m * p

theorem jump_halving {μ μ₂ p : ℕ} (hp : 2 ≤ p) (h : μ₂ * p ≤ μ) : 2 * μ₂ ≤ μ

theorem jump_count_bound (μ : ℕ → ℕ) (J : ℕ)
    (h4 : ∀ i ≤ J, 4 ≤ μ i) (hh : ∀ i < J, 2 * μ (i + 1) ≤ μ i) :
    2 ^ (J + 1) ≤ μ 0
```

**DEPENDS.** none · mathlib `Nat.pow_succ`, `Nat.mul_le_mul`.

**PROOF.**
1. (i): `4 = 2*2 ≤ m*p` by `Nat.mul_le_mul`. (ii): `2*μ₂ ≤ p*μ₂ = μ₂*p ≤ μ`.
2. (iii): induction on `J`. Base `J = 0`: `2^1 = 2 ≤ 4 ≤ μ 0`. Step: apply the inductive
   hypothesis to `i ↦ μ (i+1)` at `J`, getting `2^(J+1) ≤ μ 1`; then
   `2^(J+2) = 2·2^(J+1) ≤ 2·μ 1 ≤ μ 0` by `hh 0`.

**SIZE.** 20 lines.

**SOURCE.** `EFF.HE7.15` (THEOREM HE7.C `[r1]`, the displayed proof: "`μ ≥ L_λ = ℓ·deg R_λ ≥
ℓ·m·d_r = m·(ℓ·d_r) ≥ 2·2 = 4`", "`μ₂ ≤ … ≤ μ/(ℓd_r) ≤ μ/2`", "if jumps occur at levels 1..J
then `μ_i ≥ 4` for `i ≤ J` and `μ_J ≤ μ/2^{J−1}`, so `4 ≤ μ/2^{J−1}`, i.e. `J ≤ log₂ μ − 1`";
the `[r1]` widening rider: "both displays only ever use the product `ℓ·d_r ≥ 2`"); `EFF.HE7.14`
(the non-propagation arithmetic `L_{λ₂} ≥ m₂·(ℓ₂ deg r₂) ≥ 4` hence `μ₂ ≥ 4`).

**⚠ THE n = 16 SENTENCE CARRIES ANNEX R R3's RIDER AND E TRANSCRIBES ONLY THE NECESSARY
DIRECTION.** `EFF.HE7.15`'s closing existential ("The first n at which a level-3 object can be
needed is n = 16") is superseded by R3: the displays prove only `J ≥ 2 ⟹ μ ≥ 8 ⟹ n ≥ 16` —
"level 3 / J = 2 is unreachable below n = 16" — and "No consumer uses more". E.64 states exactly
the necessary direction; no chapter-E node states the existential (the constructed `n = 16`
family is machine-instance evidence, `he7rannex_supp.py`, not a theorem here).

**TEETH.** `he7annex_supp.py` (96/96 at `μ₂ = 4, n = 16`) and Q1's 42 one-step refine firings
→ **Lean theorem** (this node); consumed by E.60, E.64.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.08 [lemma] [fresh]

**STATEMENT.** *The lift-threshold implication `(‡) ⟹ (†)` at a rung.* For a rung `R`, bound
seed `b : ℕ`, and `k, m₀, s₀ : ℕ` with `s₀ < ℓ` and `ℓ * m₀ + s₀ * u = k`: if
`(R.slotCount − 1) * u + ℓ * b ≤ k` (the k-uniform `(‡)`), then `(g − 1) * u + b ≤ m₀` (the
per-height `(†)`). Corpus instances: level 2 (`b = (D′−1)h`): `(‡₂) ⟹ (†₂)`
(`EFF.HE7.12`'s closing step, verbatim: "`m₀ = (k − s₀u)/ℓ ≥ (k − (ℓ−1)u)/ℓ`, and
`k ≥ (ℓd_r−1)u + ℓ(D′−1)h` gives `m₀ ≥ (d_r−1)u + (D′−1)h = (†₂)`"); level `i` (R1-c's
"the same arithmetic as §S4.2's (‡₂) step", `EFF.HE7.111`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem lift_threshold_step (R : RungDatum) {b k m₀ s₀ : ℕ}
    (hs : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hcrit : (R.slotCount - 1) * R.u + R.ℓ * b ≤ k) :
    (R.g - 1) * R.u + b ≤ m₀
```

**DEPENDS.** E.01, E.02.

**PROOF.**
1. From `hk` and `s₀ ≤ ℓ − 1`: `ℓ * m₀ = k − s₀*u ≥ k − (ℓ−1)*u`.
2. From `hcrit`: `k − (ℓ−1)*u ≥ (ℓg − 1)*u + ℓb − (ℓ−1)*u = ℓ(g−1)*u + ℓb` (expand
   `slotCount = ℓ*g`; all subtractions guarded by the hypotheses — clear them first with
   `Nat.sub` lemmas or restate over `ℤ` internally and descend).
3. Cancel `ℓ ≥ 1`: `m₀ ≥ (g−1)*u + b`. `omega` closes after the two rewrites.

**SIZE.** 14 lines.

**SOURCE.** `EFF.HE7.12` ((LIFT₂)'s `(†₂)`/`(‡₂)` displays and the closing implication);
`EFF.HE7.111` (R1-c: "The bound recursion is unchanged — values never see the twist:
`m₀ = (k − s₀u_i)/ℓ_i ≥ (k − (ℓ_i−1)u_i)/ℓ_i ≥ (g_i−1)u_i + bound_i` when `k ≥ bound_{i+1}`");
`EFF.T2.10` (`(FULL2)`/`(FULL2-U)`, the T2-side statement of the same two bounds).

**TEETH.** HE7-T-LIFT2SHARP (exact reachable sets vs closed-form thresholds, ten frames,
deliberately at `f₁ ≥ 2, d_r ≥ 2`) → **Lean theorem** for the implication; the sharpness
(non-necessity) direction is E.32's set arithmetic + E.68's enumeration gate.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.09 [lemma] [fresh]

**STATEMENT.** *The use-site margin (every consumed level-1 call sits above threshold with margin
> h).* For a rung `R` (read: the level-2 rung `(ℓ, d_r, u, D′h)`) and `k, m₀, s₀, t : ℕ` with
`s₀ < ℓ`, `ℓ*m₀ + s₀*u = k`, `R.nextT < k` (the use-site condition `k > T₂ = ℓd_r·u`), and
`t < g`: writing `m_t := m₀ − t*u`, one has `ℓ * (D.T) * ... ` — precisely, in cleared form:
`ℓ * m_t > u` and hence (with the node condition `ℓ*T < u`, `T = D′h` here) `m_t > T`, giving
`m_t ≥ T + 1`, i.e. margin `m_t − (D′−1)h > h` when `T = D′h`. (The two clauses of the SIGNATURE
are the cleared forms of `m_t > λ` and `m_t > T`.) This is `EFF.HE7.25`'s displayed
chain, the unit that makes the HE6-1L coset correction NON-PROPAGATING at every HE7 use site
(honesty E-1's HE7 residual is about OTHER HE6 spans; this margin check is transcribed math, not
an adjudication).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem useSite_margin (R : RungDatum) {k m₀ s₀ t : ℕ}
    (hs : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (huse : R.nextT < k) (ht : t < R.g) :
    R.ℓ * (m₀ - t * R.u) > R.u ∧ m₀ - t * R.u > R.T
```

**DEPENDS.** E.01, E.02.

**PROOF.**
1. `ℓm₀ = k − s₀u > ℓgu − (ℓ−1)u = ℓ(g−1)u + u`, so `ℓ(m₀ − (g−1)u) > u`; since `t ≤ g−1`,
   `ℓ(m₀ − tu) ≥ ℓ(m₀ − (g−1)u) > u` (first clause). Guard the ℕ-subtractions via
   `t*u ≤ (g−1)*u ≤ m₀` (from the first display).
2. Node condition `ℓ*T < u` chains: `ℓ(m₀ − tu) > u > ℓT`, cancel `ℓ ≥ 1`: `m₀ − tu > T`
   (second clause). `omega` after expansion.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE7.25` (verbatim displays: "`m₀ = (k − s₀u)/ℓ ≥ (k − (ℓ−1)u)/ℓ >
(ℓd_r·u − (ℓ−1)u)/ℓ = (d_r − 1)u + u/ℓ = (d_r − 1)u + λ`" and "`m_t = m₀ − t·u ≥ m₀ − (d_r−1)u
> λ > D′h > (D′−1)h`, margin `m_t − (D′−1)h > λ − (D′−1)h > h ≥ 1`"; VERDICT: "the r1-corrected
level-1 threshold is satisfied with margin > h at every §S4.3 use site, so no statement of this
note moves"); `EFF.HE7.24` (§S4.3's chain `u₂ = ℓ₂κ₂ > ℓ₂T₂ ≥ T₂` supplying `huse` at the two
use classes).

**TEETH.** No direct tooth (a hypothesis-margin check, `EFF.HE7.25`); its consequence is
exercised wherever (LIFT₂) fires (Q3's frames) → **Lean theorem**.

**ENVIRONMENT.** ENV-E1.

---

## 4. §4 — THE MASTER HE7.A SUITE (carrier structures, the five clause families, the instances)

> **Design note.** T2's THEOREM HE7.A (`EFF.T2.31`) is stated over a "σ-ladder carrier" whose
> hypothesis suite `EFF.T2.39` enumerates: *"The theorem assumes the explicit quantitative
> consequences `(ACCOUNT)`, `(RES-DEG)`, nonemptiness, exhaustion, and root-preserving
> continuation. These are source obligations, not conclusions obtained merely by naming a
> carrier."* Chapter E transcribes that architecture literally: the carrier is a structure whose
> hypothesis fields are exactly those five families plus the slot/lift/cocycle laws of S1.2–S1.4
> (E.10) and the block data of S1.5–S1.7 (E.11–E.12); the master's clauses are then theorems FROM
> the fields (E.14–E.21). Per `EFF.T2.43`/`.44` (the formal-gate fence, binding on every
> signature of this section): **"Any later HE7 formalization that requires irreducibility of the
> current key is not a formalization of this theorem"** — no structure below carries, and no node
> below may add, an irreducibility hypothesis on `Φ`; residual LABELS and emitted boundary
> factors may be irreducible.

**DECISION D-E1 (carrier heights are `WithTop ℤ`).** `EFF.T2.05` declares `h(A) ∈ 𝐙` with
`h(0) = +∞`; negative heights are real at raw normalizers (`EFF.HE7.05`'s `ϖ = x^{i₀}π^{a₀}`,
`a₀` possibly `< 0`). E's abstract carrier heights are therefore `WithTop ℤ`. This does NOT
touch GC-2's `ℕ∞` ruling for chapter C's level-`r` polygon heights: the reconciliation of E's
carrier `hgt` with B's `npHgt` (level 1) and C's level-`r` instances is exactly C's GC-2
reconciliation lemma, consumed here as `EFF.HE6R1.18 [supplied-by: chapter C]`. Flagged to the
conventions czar per GC-2's flag rule; no simp-bridge is declared E-side.

**DECISION D-E2 (the residual factorization enters by its numerical shadow).** E's interface
carries, per side, the multiset of `(deg r′, multiplicity)` pairs plus, for linear factors, the
root `s ∈ K` — never the residual polynomial itself. Licence: the master's own consumption is
through roots and degrees (`EFF.HE7.96`(a): the proofs "consume `r` through its roots and
degree"; the σ output needs `deg r′` only, `EFF.T2.31`(2)); the residual POLYNOMIAL layer is
CHAP-B's at level 1 (B.28–B.30, `e₁ = 1` slice) and chapter C's above (GC-13 placeholders,
honesty E-2). A fleet agent finding a §4 consumer that provably needs the polynomial residual
returns RE-PLAN, never widens a structure silently (GC-5).

### NODE E.10 [def] [fresh]

**STATEMENT.** *The slot carrier (S1.2–S1.4 as fields).* Over the standing bundle `O` and a
finite field `K` (the carrier's label field), a **slot carrier** consists of: the key-degree
bound `D` with `(DEG-EF)` `D = e_𝒞 * f_𝒞` as a field (`EFF.T2.04` — "explicitly not inferred
from monicity"); the height function `hgt : Polynomial O → WithTop ℤ` and digit function
`dig : Polynomial O → K` (the ξ-INDEPENDENT data of `(SLOT-V)`/`(SLOT-R)`, `EFF.T2.05` — see
FAITHFULNESS); the full-height predicate `Full : ℤ → Prop` with the lift law `(LIFT)`/`(OCC)`
(`EFF.T2.09`: lifts exist AT FULL HEIGHTS ONLY — "There is no all-height lift hypothesis");
the ultrametric laws for `hgt` (`EFF.T2.04` r12: `d` is a valuation); digit additivity at a
fixed height (the residue-additivity law `EFF.HE7.96`(c) consumes); and nonvanishing of `dig`
on nonzero sub-`D` polynomials at their own height.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- A **σ-ladder slot carrier** (T2 S1.2–S1.4, `EFF.T2.04`–`.10`): the ξ-independent
height/digit data with the ultrametric, lift, and additivity laws as fields. -/
structure SlotCarrier (O : Type*) [CommRing O] (K : Type*) [Field K] where
  /-- The current key degree `D > 0`. -/
  D : ℕ
  hD : 0 < D
  /-- Carrier invariants with `(DEG-EF)`: `D = e_𝒞 f_𝒞` (a hypothesis, never inferred). -/
  eC : ℕ
  fC : ℕ
  hef : D = eC * fC
  heC : 1 ≤ eC
  hfC : 1 ≤ fC
  /-- `h(A)`: the exact slot height (`SLOT-V`'s ξ-independent value); `h(0) = ⊤`. -/
  hgt : Polynomial O → WithTop ℤ
  /-- `dig(A)`: the exact slot digit (`SLOT-R`'s ξ-independent value); `dig 0 = 0`. -/
  dig : Polynomial O → K
  hgt_zero : hgt 0 = ⊤
  dig_zero : dig 0 = 0
  /-- nonzero sub-`D` polynomials have finite height and nonzero digit (`EFF.T2.05`). -/
  hgt_ne_top : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < D → hgt A ≠ ⊤
  dig_ne_zero : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < D → dig A ≠ 0
  /-- the ultrametric laws (`EFF.T2.04`, r12's valuation disclosure). -/
  hgt_add_ge : ∀ A B, min (hgt A) (hgt B) ≤ hgt (A + B)
  hgt_add_eq : ∀ A B, hgt A ≠ hgt B → hgt (A + B) = min (hgt A) (hgt B)
  /-- digit additivity at a shared height (residues at a fixed height are additive —
  `EFF.HE7.96`(c)'s mechanism). -/
  dig_add : ∀ A B : Polynomial O, ∀ k : ℤ,
      hgt A = (k : WithTop ℤ) → hgt B = (k : WithTop ℤ) → dig A + dig B ≠ 0 →
      hgt (A + B) = (k : WithTop ℤ) ∧ dig (A + B) = dig A + dig B
  /-- the full heights (`OCC`'s finite-domain obligation is the instances'). -/
  Full : ℤ → Prop
  /-- `(LIFT)`: at a full height every nonzero digit is realised (`EFF.T2.09`). -/
  hlift : ∀ k : ℤ, Full k → ∀ c : K, c ≠ 0 →
      ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < D ∧
        hgt A = (k : WithTop ℤ) ∧ dig A = c
```

**⚠ FAITHFULNESS (the ξ-quantifier is deliberately absent — flag for the cross-read).**
`EFF.T2.05` states `(SLOT-V)`/`(SLOT-R)` as evaluation laws at every `ξ ∈ Pt ⊆ K̄₀`. No
algebraic closure exists in `leanfinal` (GC-7; `docs/VENDOR_QUARRY_MAP_2026-08-15.md` four-way
absence), so E's schema carries the ξ-INDEPENDENT height/digit pair — which is exactly what the
laws assert exists — and pushes every root-side consequence into E.12's five clause-family
fields, where the corpus itself carries them as source obligations (`EFF.T2.39`). At instances,
`hgt`/`dig` are B's `digAt`-layer reads (B.21) on the `e₁ = 1` slice and chapter C's normalizer
reads above (GC-13). The evaluation laws themselves are therefore INSTANCE obligations, exactly
as in the corpus, and are never stated E-side.

**DEPENDS.** none (landed `Polynomial` API only).

**PROOF.** definitional. **SIZE.** 45 lines. **SPLIT CANDIDATE:** if elaboration is heavy, land
the ultrametric-law pair as a mixin structure `HgtLaws` in `E10a`.

**SOURCE.** `EFF.T2.04` (`(FINITE-RES)`, `(DEG-EF)`, the r12 valuation disclosure); `EFF.T2.05`
(`(SLOT-V)`/`(SLOT-R)`, `h(0) = +∞, dig(0) = 0`); `EFF.T2.09` (`(LIFT)`/`(OCC)`); `EFF.T2.10`
(fullness criteria — instances of `Full`, not fields).

**TEETH.** S7 sub-threshold/pass-2 refusal (`EFF.T2.09`: the battery attacks all-height lifts)
→ the `Full`-gated `hlift` field makes the refusal structural: an all-height lift is not
expressible against this interface.

**ENVIRONMENT.** ENV-E2 + `variable {K : Type*} [Field K] [Finite K]` (the `[Finite K]` is
required only by §7's dictionary counts; keep it OUT of this structure — minimal binding,
GC-6.4).

---

### NODE E.11 [def] [fresh]

**STATEMENT.** *The block data (S1.5–S1.6 as fields) and the ladder support value.* Over a slot
carrier `C`: a **σ-block** consists of the monic key `Φ` (degree `D`, `Monic` — irreducibility
NEVER assumed, `(NO-IRR)`), the polynomial `F` with its `Φ`-development `(DEV)`
`F = Φ^μ + Σ_{j<μ} A_j Φ^j` (`deg A_j < D`), key-freeness `(KEY-FREE)` (`gcd_{K₀[x]}(F,Φ) = 1`,
carried in the O-level form `IsCoprime` after clearing — see the ⚠ note), the inherited
threshold `T`, and the development height function `devHgt j := hgt (A j)` (with `devHgt μ = 0`
for the monic top). The **ladder support value** is the cleared D-1-shape support function on
`devHgt`:
`ladderSuppVal devHgt u ℓ μ = inf_{j ≤ μ} (ℓ • devHgt j + (j * u : ℤ))` — an `inf` of
`ℤ`-linear forms, with `onLadderSide` its argmin predicate. Sides/slopes/lengths are derived
predicates on the argmin set, exactly D-1/GC-2's representation one abstraction level up; no
polygon type is declared.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The cleared support value of a ladder development (D-1's shape on abstract heights):
`inf over j ≤ μ of (ℓ·hgt j + j·u)`. -/
noncomputable def ladderSuppVal (hgt : ℕ → WithTop ℤ) (u ℓ μ : ℕ) : WithTop ℤ :=
  (Finset.range (μ + 1)).inf fun j => ℓ • hgt j + ((j * u : ℕ) : WithTop ℤ)

/-- Abscissa `j` lies on the `(u, ℓ)`-side of the ladder polygon. -/
def onLadderSide (hgt : ℕ → WithTop ℤ) (u ℓ μ : ℕ) (j : ℕ) : Prop :=
  j ≤ μ ∧ ℓ • hgt j + ((j * u : ℕ) : WithTop ℤ) = ladderSuppVal hgt u ℓ μ

/-- A **σ-block** over a slot carrier (T2 S1.5–S1.6). -/
structure BlockData {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) where
  Φ : Polynomial O
  F : Polynomial O
  μ : ℕ
  hμ : 1 ≤ μ
  hΦ : Φ.Monic
  hΦdeg : Φ.natDegree = C.D
  /-- the development coefficients; `A j = 0` for `j ≥ μ` by convention. -/
  A : ℕ → Polynomial O
  hdev : F = Φ ^ μ + ∑ j ∈ Finset.range μ, A j * Φ ^ j          -- (DEV)
  hdegA : ∀ j < μ, (A j).natDegree < C.D
  /-- `(KEY-FREE)`, in its two consumed shadows: the O-level coprimality and its
  polygon consequence `A 0 ≠ 0`. -/
  hkeyfree : IsCoprime (F.map (algebraMap O (FractionRing O)))
      (Φ.map (algebraMap O (FractionRing O)))
  hA0 : A 0 ≠ 0
  /-- the inherited threshold. -/
  T : ℕ

/-- The block's development heights: `devHgt j = hgt (A j)` for `j < μ`, `0` at the
monic top `j = μ`, `⊤` above. -/
noncomputable def BlockData.devHgt {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} (B : BlockData C) : ℕ → WithTop ℤ :=
  fun j => if j = B.μ then (0 : WithTop ℤ) else if j < B.μ then C.hgt (B.A j) else ⊤
```

**⚠ KEY-FREENESS SPELLING.** `EFF.T2.11`'s `(KEY-FREE)` is `gcd_{K₀[x]}(F, Φ) = 1`. The
signed spelling is `IsCoprime` over `FractionRing O` (mathlib-native, gcd-free); `hA0` is its
consumed polygon shadow (`EFF.T2.11`'s own derivation: "(KEY-FREE) implies A₀ ≠ 0"), carried
separately so E.13 does not re-derive field theory. If the stub stage finds `FractionRing`
elaboration heavy here, the fallback is `hkeyfree : ∀ g : Polynomial O, g ∣ F → g ∣ Φ →
IsUnit (g.map (algebraMap O (FractionRing O)))` — a DECISION at the stub, flagged, never silent.

**⚠ WINDOW/CAP.** `(WINDOW)` (`T < d(Φ(ρ)) < ∞`) and the `WindowSafe`/`CapSafe` proxy
assertions (`EFF.T2.11`) are ROOT-side and enter as E.12 continuation fields, not here. The
corpus's own words: proxy agreement "not inferred merely from the phrase 'arising from a
label'".

**DEPENDS.** E.10 · mathlib `IsCoprime`, `FractionRing`, `Finset.inf`.

**PROOF.** definitional. **SIZE.** 45 lines. **SPLIT CANDIDATE:** `ladderSuppVal`/`onLadderSide`
as `E11a` (they are consumed independently by §5).

**SOURCE.** `EFF.T2.11` (`(DEV)`, `(KEY-FREE)`, `(WINDOW)`, the proxy fence); `EFF.T2.02`
(`(NO-IRR)`: "Φ is monic; irreducibility is not assumed" — boxed, REDLINE); `EFF.HE7.09`
(the standing `Ψ ∤ f_S` convention is the `hA0`-analogue one level up: "equivalently the
Ψ-development's constant coefficient `A₀^{(2)} ≠ 0`"); CHAP-B D-1/GC-2 (the support-function
representation this reuses in shape).

**TEETH.** S7 reducible-key boundary gate (`EFF.T2.02`) → structural: no irreducibility field
exists to consume. S7 Pass 2 dangerous-collected-term tooth (`EFF.T2.11`) → the proxy fence is
an instance obligation (C-side), recorded in §13.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.12 [def] [fresh]

**STATEMENT.** *The rung interface: the five clause families as fields (the `StageInterface`
lesson at the ladder).* Over a slot carrier `C` and block `B`: the **rung interface** carries
the side/residual numerical data and the five HE7.A hypothesis families at exactly corpus
strength (`EFF.T2.39`):
1. `sides : Finset (ℕ × ℕ)` — the slopes `(u_λ, ℓ_λ)` in lowest terms (coprime, `ℓ ≥ 1`), each
   with length `len : ℕ × ℕ → ℕ`, satisfying the side laws: every side is an `onLadderSide`
   argmin class of `B.devHgt` above the threshold (`λ > T` in cleared form
   `ℓ_λ * T < u_λ`), and `hlen_sum : Σ len = μ` (`(HULL-LENGTH)` — supplied, since its
   derivation is polygon geometry owned below E; see the ⚠ note);
2. per side, the residual shadow (D-E2): `linFac : (ℕ × ℕ) → Multiset (K × ℕ)` (linear factors:
   root `s ∈ K`, multiplicity) and `hiFac : (ℕ × ℕ) → Multiset (ℕ × ℕ)` (higher factors:
   degree ≥ 2 pairs `(deg, mult)` — or `ℓ_λ ≥ 2` factors of any degree), with
   `(RES-DEG)`: `ℓ_λ * (Σ deg·mult over both) = len λ` (`EFF.T2.12`'s
   `e′ Σ m_{λ,r′} deg r′ = L_λ`);
3. `(ACCOUNT)` as the sampled count law the derivation actually consumes (`EFF.T2.29`'s
   reading): `rootCount : (ℕ × ℕ) → ℕ` (the number `n_λ` of roots at slope `λ`) with the field
   `haccount : ∀ λ ∈ sides, rootCount λ = C.D * len λ` — **see the ⚠ DECISION note: E carries
   (ACCOUNT) at its consumed jump form `(SIDE-COUNT)`, with the integral form recorded as the
   instances' derivation obligation**;
4. `hnonempty`: every residual factor's class is nonempty (`classCount` per factor `≥ 1` — in
   the numerical shadow: `rootCount` distributes over factors with each part
   `≥ C.D * ℓ_λ * deg`);
5. `hexhaust`: the classes are disjoint and exhaust (`Σ over factors of classCount = rootCount`);
6. root-preserving continuation: `(RISE)` and `(SEC-RANK)` as fields — a well-founded rank
   `σRank` into a type `W` with `[WellFoundedRelation W]` strictly decreasing at every
   product-1 linear recentering (`EFF.T2.26`: "an instance that cannot supply it does not
   instantiate HE7.A"; NOT an open obligation — "every listed instance supplies it").

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The **rung interface**: T2's carrier hypothesis suite as fields (`EFF.T2.39`'s five
quantitative families + the side/residual numerical shadow). σ-valued outputs NEVER live
here (GC-4: they exit through §7's dictionary). -/
structure RungInterface {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) where
  sides : Finset (ℕ × ℕ)
  hside_cop : ∀ p ∈ sides, Nat.Coprime p.1 p.2 ∧ 1 ≤ p.2
  hside_node : ∀ p ∈ sides, p.2 * B.T < p.1                     -- λ > T (clause 1 half)
  len : ℕ × ℕ → ℕ
  hlen_pos : ∀ p ∈ sides, 1 ≤ len p
  hlen_sum : ∑ p ∈ sides, len p = B.μ                           -- (HULL-LENGTH)
  linFac : ℕ × ℕ → Multiset (K × ℕ)                             -- (root s, mult m)
  hiFac : ℕ × ℕ → Multiset (ℕ × ℕ)                              -- (deg ≥ 2 …, mult)
  hresdeg : ∀ p ∈ sides,                                        -- (RES-DEG)
      p.2 * ((linFac p).map Prod.snd |>.sum
        + ((hiFac p).map fun q => q.1 * q.2).sum) = len p
  rootCount : ℕ × ℕ → ℕ
  haccount : ∀ p ∈ sides, rootCount p = C.D * len p             -- (SIDE-COUNT) form
  classCount : ℕ × ℕ → K × ℕ → ℕ                                -- per linear factor
  classCountHi : ℕ × ℕ → ℕ × ℕ → ℕ                              -- per higher factor
  hnonempty : ∀ p ∈ sides, (∀ q ∈ linFac p, 1 ≤ classCount p q) ∧
      (∀ q ∈ hiFac p, 1 ≤ classCountHi p q)                     -- nonemptiness
  hforce : ∀ p ∈ sides, (∀ q ∈ linFac p, C.D * p.2 ≤ classCount p q) ∧
      (∀ q ∈ hiFac p, C.D * p.2 * q.1 ≤ classCountHi p q)       -- local forcing
  hexhaust : ∀ p ∈ sides,                                       -- exhaustion
      ((linFac p).map (classCount p)).sum
        + ((hiFac p).map (classCountHi p)).sum = rootCount p
  /-- root-preserving continuation: the `(SEC-RANK)` carrier (`EFF.T2.26`). -/
  W : Type*
  wf : WellFoundedRelation W
  σRank : W                                                     -- the state's rank
```

**⚠ DECISION D-E3 ((ACCOUNT) is carried at its consumed jump form).** `EFF.T2.16`'s integral
`(ACCOUNT)` (`Σ_ρ min(w_ρ, κ) = D Σ_λ L_λ min(λ, κ)` for `κ > T`) is consumed by the master
ONLY through its two jump consequences `(SIDE-COUNT)` `n_λ = D·L_λ` and `(DEG-SUM)`
(`EFF.T2.29`: "Comparing the jumps of the two piecewise-linear sides at λ yields
`(SIDE-COUNT)`"). E's field `haccount` carries `(SIDE-COUNT)` directly; the κ-sampled integral
identity and its jump derivation are the INSTANCES' obligation (level 1: HE6-ACCOUNT via B/C;
level 2: `EFF.HE7.41`'s `(†₂-count)` + HE6-3's sampling, both C placeholders), recorded per
instance at E.22/E.23. Rationale: the sampling/elimination derivation quantifies over rational
κ in gaps (`EFF.HE7.41`), which under GC-2's no-ℚ rule would force a cleared two-variable
sampling layer E does not own and no E-theorem consumes — the fields E.14–E.16 need exactly
`(SIDE-COUNT)`. **Flagged for the cross-read** (§14): this is the chapter's largest
transcription-strength call. The original integral display is quoted in full at E.22's
instance-obligation list so no strength is silently lost.

**⚠ `(RISE)`/`(WINDOW)` PLACEMENT.** `(RISE)` (`EFF.T2.19`: "a carrier hypothesis, not an open
ledger obligation") and `(WINDOW)`/proxy-safety enter as hypotheses OF THE TRANSITION THEOREMS
(E.17/E.18) at the exact step that consumes them, not as standing structure fields — a rung
that never recenters never owes `(RISE)`. This matches `EFF.T2.19`'s per-step scoping and keeps
minimal binding (GC-6.4).

**DEPENDS.** E.10, E.11 · mathlib `WellFoundedRelation`, `Multiset.map`, `Multiset.sum`.

**PROOF.** definitional. **SIZE.** 55 lines. **SPLIT-MANDATED:** land as `E12` (fields 1–5,
counts) + `E12a` (the continuation/rank fields) if elaboration or universe plumbing on `W`
fights; `W`'s universe is the structure's second parameter — flag any universe issue to the
orchestrator rather than fixing `W := ℕ` (`EFF.T2.52`: well-foundedness form, "an instance may
discharge it either way"; `ℕ`-valued would silently strengthen).

**SOURCE.** `EFF.T2.12` (`(RES-FACT)`/`(RES-DEG)`); `EFF.T2.15` (the seven test-package
clauses — clauses 3/4/5/6 are the `hnonempty`/`hexhaust`/`hforce` shadows; clauses 1/2/7 are
instance obligations, E.22); `EFF.T2.16` (`(ACCOUNT)` — via D-E3); `EFF.T2.26` (`(SEC-RANK)`
verbatim: well-founded `W_𝒞`, strict decrease at product-1 linear recenterings ONLY, "Nothing
is required of `σ_𝒞` at any other transition"); `EFF.T2.29` (`(SIDE-COUNT)`/`(DEG-SUM)`);
`EFF.T2.30` (the forcing divisibilities `e_𝒞 e′ ∣ e`, `f_𝒞 deg r′ ∣ f` — `hforce` is their
count shadow `|orbit| ≥ De′deg r′`).

**TEETH.** S7 Pass 2 missing-`(RES-DEG)` refusal → structural (a consumer without `hresdeg`
cannot elaborate). S7 well-founded-but-root-losing mutant (`EFF.T2.27`) → `hexhaust` +
`haccount` are separate fields from the rank, so rank descent alone proves nothing — the
mutant's route is closed by construction; E.20 states the theorem only from BOTH.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.13 [lemma] [fresh]

**STATEMENT.** *Degree bookkeeping of the block.* For a block `B` over `C`:
(i) `F.natDegree = μ * C.D` and `F.Monic` (from `(DEV)`, `Φ` monic of degree `D`,
`deg A_j < D`);
(ii) `B.devHgt μ = 0` and `B.devHgt 0 ≠ ⊤` (the two hull endpoints are finite — the monic top
and `(KEY-FREE)`'s `A 0 ≠ 0` with E.10's `hgt_ne_top`);
(iii) hence `ladderSuppVal B.devHgt u ℓ B.μ ≠ ⊤` for every `(u, ℓ)` — every cleared support
value is finite (the polygon is honest; `+∞` is never fed to the accounting — `EFF.T2.23`'s
"the peel occurs before `(WINDOW)` so `+∞` is never fed to Newton accounting" is the
convention's analogue one clause down).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem BlockData.natDegree_F {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K]
    {C : SlotCarrier O K} (B : BlockData C) : B.F.natDegree = B.μ * C.D ∧ B.F.Monic

theorem BlockData.suppVal_ne_top {O : Type*} [CommRing O] [IsDomain O] {K : Type*}
    [Field K] {C : SlotCarrier O K} (B : BlockData C) (u ℓ : ℕ) :
    ladderSuppVal B.devHgt u ℓ B.μ ≠ ⊤
```

**DEPENDS.** E.10, E.11 · mathlib `Polynomial.natDegree_add_of_natDegree_lt`,
`Polynomial.Monic.natDegree_pow`, `Finset.inf_le`.

**PROOF.**
1. (i): `deg(Φ^μ) = μD` (`Monic.natDegree_pow`); each summand `A_j Φ^j` has degree
   `< D + jD ≤ μD`; the sum of the lower terms has degree `< μD`
   (`Polynomial.natDegree_sum_le` + strict bound), so the top survives: degree `μD`, monic
   (leading coefficient from `Φ^μ`).
2. (ii): `devHgt μ = 0` by definition; `devHgt 0 = hgt (A 0) ≠ ⊤` by `hA0`, `hdegA`, and
   E.10's `hgt_ne_top`.
3. (iii): `ladderSuppVal ≤` the value at `j = μ`, which is `ℓ•0 + μu < ⊤`; `Finset.inf_le` at
   `μ ∈ range (μ+1)`.

**SIZE.** 22 lines.

**SOURCE.** `EFF.T2.11` (`deg F = μD` in `(DEV)`; the `(KEY-FREE) ⟹ A₀ ≠ 0 ⟹` hull-span
derivation); `EFF.T2.29` (finite window values as a hypothesis of the count derivation).

**TEETH.** S7 reducible-key gate → the finiteness clauses are what a `Φ ∣ F` input violates
(`hA0` fails), reproducing the corpus's fail-closed behaviour structurally.

**ENVIRONMENT.** ENV-E2 (+ `[IsDomain O]` for the degree arithmetic).

---

### NODE E.14 [lemma] [fresh]

**STATEMENT.** *The separable-side degree sum `(DEG-SUM)` and the count match.* Call a side
`p ∈ sides` **separable** (in the numerical shadow) when every multiplicity in `linFac p` and
`hiFac p` equals `1`. For a separable side: (i) `p.2 * (Σ degrees) = len p` (`(DEG-SUM)`,
`e′ Σ_{r′} deg r′ = L_λ`, the multiplicity-free specialization of `hresdeg`); (ii) hence the
forced class sizes sum to the side's root count:
`Σ_{linear} D * p.2 * 1 + Σ_{higher} D * p.2 * deg = D * len p = rootCount p`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

def RungInterface.SepSide {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B) (p : ℕ × ℕ) : Prop :=
  (∀ q ∈ I.linFac p, q.2 = 1) ∧ (∀ q ∈ I.hiFac p, q.2 = 1)

theorem RungInterface.forced_sum_eq {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    {p : ℕ × ℕ} (hp : p ∈ I.sides) (hsep : I.SepSide p) :
    ((I.linFac p).map fun _ => C.D * p.2).sum
      + ((I.hiFac p).map fun q => C.D * p.2 * q.1).sum = I.rootCount p
```

**DEPENDS.** E.12 · mathlib `Multiset.sum_map_mul_left`, `Multiset.map_congr`.

**PROOF.**
1. Under `hsep`, `hresdeg` reads `p.2 * (Σ_{lin} 1·… + Σ_{hi} deg) = len p` — rewrite each
   summand's multiplicity to 1 (`Multiset.map_congr`).
2. Multiply by `C.D`, distribute over the two multiset sums (`Multiset.sum_map_mul_left`),
   and close with `haccount hp` (`rootCount p = C.D * len p`). `ring_nf` on the scalars.

**SIZE.** 18 lines.

**SOURCE.** `EFF.T2.29` (`(DEG-SUM)`: "For separable `R_λ`, `(RES-DEG)` specializes to
`(DEG-SUM)`"); `EFF.T2.12` (`(RES-DEG)`); `EFF.HE7.13`'s proof ("`Σ_{r₂}|S_{λ₂,r₂}| = n_{λ₂} =
D″L_{λ₂} = Σ_{r₂}D″ℓ₂deg r₂`" — this identity one level down).

**TEETH.** S7 Pass 2 missing-`(RES-DEG)` refusal → **Lean theorem**.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.15 [theorem] [fresh]

**STATEMENT.** *The sandwich (orbit count forced termwise) and the `(e,f)` forcing.* Two
clauses.
(i) **Multiset sandwich**: if a finite family of counts satisfies termwise `lower q ≤ count q`
and `Σ count = Σ lower`, then `count = lower` termwise. Applied at a separable side via E.14 +
`hforce` + `hexhaust`: every class count EQUALS its forced size, `classCount p q = C.D * p.2`
(linear) and `classCountHi p q = C.D * p.2 * q.1` (higher) — `EFF.T2.30`'s "Summing over
disjoint exhaustive classes … forces equality term by term".
(ii) **The `(e,f)` forcing chain**: for `a, b, e, f : ℕ` with `0 < a, 0 < b`, `a ∣ e`, `b ∣ f`
and `e * f = a * b`: `e = a ∧ f = b`. (The corpus step "equality in `(FUND)` forces equality in
both local divisibilities"; instances take `a = e_𝒞·e′`, `b = f_𝒞·deg r′`,
`e*f = |orbit| = D·e′·deg r′ = a*b` via `(DEG-EF)`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem multiset_sandwich {α : Type*} (s : Multiset α) (count lower : α → ℕ)
    (hle : ∀ q ∈ s, lower q ≤ count q)
    (hsum : (s.map count).sum = (s.map lower).sum) :
    ∀ q ∈ s, count q = lower q

theorem ef_forcing {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hae : a ∣ e) (hbf : b ∣ f) (hprod : e * f = a * b) : e = a ∧ f = b
```

**DEPENDS.** E.12, E.14 · mathlib `Multiset.sum_map_le_sum_map`, `Nat.eq_of_dvd_of_lt_two_mul`
(or direct: `Nat.le_of_dvd` + product comparison).

**PROOF.**
1. `multiset_sandwich`: contrapositive — a strict inequality at one member with `≤` elsewhere
   makes the sums strictly unequal (`Multiset.sum_lt_sum` pattern; induction on `s` if the
   exact lemma is absent).
2. `ef_forcing`: write `e = a*x`, `f = b*y`; `hprod` gives `a*b*x*y = a*b`, cancel (`ha`, `hb`)
   to `x*y = 1`, so `x = y = 1` (`Nat.mul_eq_one`).

**SIZE.** 20 lines.

**⚠ FENCE (H §11 is NOT consumed).** CHAP-H's H.76 (`e₁ ∣ e, f₁ ∣ f, e·f ≤ e₁f₁ ⟹ …`) is the
`μ = 2` σ-forcing analogue of clause (ii), but H §11 is outside E's sanctioned slice
(GC-5/H-14: only H.51–H.58). Clause (ii) is therefore proved fresh here — eight lines, cheaper
than a fence violation.

**SOURCE.** `EFF.T2.30` (verbatim: "Local forcing and `(DEG-EF)` make every orbit in the class
have size at least `De′deg r′`. Summing over disjoint exhaustive classes and using
`(SIDE-COUNT)` and `(DEG-SUM)` forces equality term by term. The full class therefore has room
for exactly one orbit; equality in `(FUND)` forces equality in both local divisibilities.");
`EFF.HE7.13`'s sandwich ("the sandwich forces equality, each class is a single Galois orbit …
`e ≥ e₁ℓℓ₂, f ≥ f₁d_rd_{r₂}` with `ef = …` forces equality on both").

**⚠ WHAT THE SCHEMA DOES *NOT* PROVE (GC-3 / HYP.01 fence).** The step from "class count
`= De′deg r′`" to "the class is ONE GALOIS ORBIT = the root set of one monic irreducible factor
with local invariants `(e, f)`" consumes `(FUND)` (`|Ω| = [K₀(ρ):K₀] = e·f`) and the field
`hforce`'s orbit reading — carrier content. `(FUND)` at instances is the rank-form identity
`Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`
(`leanfinal/Uniformity/Quarry/RamificationInertiaLocal.lean`, GC-3), applied by chapters B/C at
their instance records; identifying the polynomial-level `efPair` with the ideal-theoretic pair
is `HYP.01` + `HYP.12` and is NEVER done silently here — E.16 states its conclusion as counts
plus the forcing arithmetic, and the orbit/irreducible-factor reading is an instance field.

**TEETH.** S7 Pass 1 pure-mathematics theorem gate (`EFF.T2.30`) → **Lean theorem**.

**ENVIRONMENT.** ENV-E1 (clause ii) / ENV-E2 (clause i application).

---

### NODE E.16 [theorem] [fresh]

**STATEMENT.** *THEOREM HE7.A, clauses (1)–(2), schema form.* Let `C, B, I` be a slot carrier,
block, and rung interface. Then:
(1) every side `p ∈ I.sides` satisfies the node condition `p.2 * B.T < p.1` (λ > T) and
`Σ_{p ∈ sides} len p = B.μ` — packaging of `hside_node` and `hlen_sum`;
(2) for every SEPARABLE side `p` and every factor `q` in its shadow: the class count equals
`C.D * p.2 * deg q` exactly (E.15(i) applied through E.14), and any `(e, f)` pair divisible by
`(C.eC * p.2, C.fC * deg q)` whose product is the class count equals it componentwise
(E.15(ii) with `(DEG-EF)`). This is `EFF.T2.31` clauses 1–2 at the strength the schema owns
(the orbit/irreducibility reading is the instances' — E.15's fence).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem he7a_clause12 {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B) :
    ((∀ p ∈ I.sides, p.2 * B.T < p.1) ∧ ∑ p ∈ I.sides, I.len p = B.μ) ∧
    (∀ p ∈ I.sides, I.SepSide p →
      (∀ q ∈ I.linFac p, I.classCount p q = C.D * p.2) ∧
      (∀ q ∈ I.hiFac p, I.classCountHi p q = C.D * p.2 * q.1))
```

**DEPENDS.** E.12, E.14, E.15.

**PROOF.**
1. Clause (1): `exact ⟨I.hside_node, I.hlen_sum⟩`.
2. Clause (2): fix a separable side; `E.14` gives `Σ forced = rootCount`; `hexhaust` gives
   `Σ actual = rootCount`; `hforce` gives termwise `forced ≤ actual`; `multiset_sandwich`
   (over the disjoint union of the two factor multisets, or applied twice with the paired
   bound) forces termwise equality. Bookkeeping: combine the two multisets via
   `Multiset.add` and case on membership.

**SIZE.** 24 lines.

**SOURCE.** `EFF.T2.31` (clauses 1–2, verbatim: "every side λ … satisfies λ > T,
`Σ L_λ = μ`; … `|S_{λ,r′}| = De′deg r′`. This class is one Galois orbit … Its invariants are
`e = e_𝒞 e′, f = f_𝒞 deg r′`"); `EFF.HE7.13` (the level-2 instance and its proof shape, which
this schema reproduces); `EFF.T2.18` (clauses 1–2 carry NO `(LB1)` conditionality — "their
proofs run on the unsplit hull of F itself" — and accordingly this node consumes no block
construction).

**TEETH.** Q1 / HE7-READ2 (1,335 PARI jobs, 0 mismatch — the level-2 instance of this clause
pair) → schema **Lean theorem** + instance evidence recorded at E.23.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.17 [theorem] [fresh]

**STATEMENT.** *The continuation trichotomy (HE7.A clauses (3)–(4), the four-case split).*
(i) **Classification**: for a factor with side-denominator `ℓ`, degree `d ≥ 1`, and block
multiplicity `k ≥ 1` (the `(LABEL-OWN)` integer `k = deg F_{λ,r′}/(De′deg r′)`): exactly one of
**terminal** (`k = 1`), **refine** (`k ≥ 2 ∧ ℓ*d = 1`), **child** (`k ≥ 2 ∧ ℓ*d ≥ 2`) holds —
the WIDENED split on the product `ℓ·deg r` (`EFF.HE7.14`'s `[r1]`: "split on the product
ℓ₂·deg r₂ (NOT on ℓ₂ alone)"; the pre-r1 split is REFUTED — FINDING HE6R1-F1, "β₂ ∈ K₂(β₂)∖K₂
is not a value of (LIFT₂)").
(ii) **`(MASS)` at a child**: `μ_child * (ℓ*d) ≤ μ` implies `2 * μ_child ≤ μ` (E.07(ii)) and
the child's key data multiply: `e_child = e_𝒞 * ℓ_λ * …` per E.06's telescoping.
(iii) **`(LABEL-OWN)` integrality**: `k * (D * ℓ * d) = deg F_{λ,r′}` with `k ≥ 1` — carried as
the definition of the block-multiplicity datum, with the corpus fence: "No equality between
`k_{λ,r′}` and `m_{λ,r′}` from the parent residual factorization is assumed" (`EFF.T2.17`) —
the schema does NOT relate `k` to the multiplicities in `linFac`/`hiFac`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The three continuation cases of HE7.A(3)–(4), on the numerical shadow. -/
inductive ContCase | terminal | refine | child
  deriving DecidableEq

def contCaseOf (ℓ d k : ℕ) : ContCase :=
  if k = 1 then .terminal else if ℓ * d = 1 then .refine else .child

theorem contCase_complete (ℓ d k : ℕ) (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (contCaseOf ℓ d k = .terminal ∧ k = 1) ∨
    (contCaseOf ℓ d k = .refine ∧ 2 ≤ k ∧ ℓ * d = 1) ∨
    (contCaseOf ℓ d k = .child ∧ 2 ≤ k ∧ 2 ≤ ℓ * d)

theorem child_mass {μ μc ℓ d : ℕ} (h2 : 2 ≤ ℓ * d) (h : μc * (ℓ * d) ≤ μ) :
    2 * μc ≤ μ
```

**DEPENDS.** E.01, E.07 · mathlib `Nat.mul_eq_one`.

**PROOF.**
1. `contCase_complete`: unfold; `k = 1` or `2 ≤ k` (`hk`); at `2 ≤ k`, `ℓ*d = 1` or
   `2 ≤ ℓ*d` (`hℓ, hd` give `1 ≤ ℓ*d`). `omega` per branch.
2. `child_mass`: `jump_halving` (E.07(ii)) verbatim.

**SIZE.** 22 lines.

**SOURCE.** `EFF.T2.31` (clauses 3–4: "the continuation is decided by the product `e′deg r′`.
Product 1 gives the certified linear recentering; product at least 2 gives the certified child
carrier and the mass bound `(MASS)`"; clause 4's block reading with `(LABEL-PURE)`/
`(LABEL-OWN)`); `EFF.T2.17` (S1.7A: the displayed `k_{λ,r′} = ν/(e′deg r′) ∈ ℤ_{≥1}` and the
parent-multiplicity NON-IMPORT — "The parent-multiplicity formula installed by r1 is deleted by
r2"); `EFF.T2.21` (`(MASS)`, `μ_child ≤ μ/(e′deg r′) ≤ μ/2`); `EFF.T2.22` (the processing
order: side split, then label split, then per-block decision); `EFF.HE7.14` (the widened
trichotomy + the refutation of the pre-r1 branch).

**⚠ `(LB1)` SCOPE.** Constructing the label BLOCKS at a level-one multi-side/mixed state is
`(LB1)` (E.39); this node classifies given the block data. Consumers at level one must thread
E.39's hypothesis; at level ≥ 2 the blocks are ANNEX-LEMMA HE7-13′(a) = E.57. The corpus's own
scoping (`EFF.T2.18`): "Clauses 1 and 2 are not [conditional]; … the clause-4 route [is], on
`(LB1)`."

**TEETH.** S7 Pass 2 mixed-residual-two-repeated-classes tooth; `he7r2_supp.py` B1–B5 (the
refine branch, 42/42); `he7_pe3_probe12.py` (144/144 at the first mixed node) → the
classification becomes a **Lean theorem**; the block construction stays a carried hypothesis
at level 1 (§6).

**ENVIRONMENT.** ENV-E1.

---

### NODE E.18 [theorem] [fresh]

**STATEMENT.** *The mid-chain peel `(MID-PEEL)`/`(MID-MASS)` (HE7.A clause 5's identity
layer).* Let `G, Φ̃ : Polynomial O` with `Φ̃` monic of degree `D`, `G` monic of degree `D * ν`
(`ν ≥ 1`), `G` squarefree, and `Φ̃ ∣ G`. Put `G′ := G / Φ̃`. Then:
(i) `G = Φ̃ * G′` with `G′` monic of degree `D * (ν − 1)` (`(MID-MASS)`: mass drops by exactly
one, represented degree by `D`);
(ii) `G′` and `Φ̃` are coprime over the fraction field — `EFF.T2.23`'s derivation verbatim:
"a common irreducible divisor of `G′` and `Φ̃` would square-divide `G`";
(iii) if `ν = 1` then `G′ = 1` (the degenerate guard — "no successor exists").

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem midPeel {O : Type*} [CommRing O] [IsDomain O] {G Φ : Polynomial O} {D ν : ℕ}
    (hΦ : Φ.Monic) (hΦd : Φ.natDegree = D) (hG : G.Monic) (hGd : G.natDegree = D * ν)
    (hν : 1 ≤ ν) (hD : 0 < D)
    (hsq : Squarefree (G.map (algebraMap O (FractionRing O)))) (hdvd : Φ ∣ G) :
    ∃ G' : Polynomial O, G = Φ * G' ∧ G'.Monic ∧ G'.natDegree = D * (ν - 1) ∧
      IsCoprime (G'.map (algebraMap O (FractionRing O)))
        (Φ.map (algebraMap O (FractionRing O)))
```

**DEPENDS.** E.11 (the coprimality spelling) · mathlib `Polynomial.Monic.dvd` factor API
(`Polynomial.eq_of_monic_of_associated`, `Squarefree`, `EuclideanDomain.gcd` over the fraction
field), `Polynomial.Monic.natDegree_mul`.

**PROOF.**
1. `hdvd` gives `G = Φ * G′`; monicity of `Φ, G` makes `G′` monic
   (`Polynomial.Monic.of_mul_monic_left`), degrees add (`natDegree_mul` at monic ≠ 0), so
   `deg G′ = Dν − D = D(ν−1)`.
2. Coprimality: over `FractionRing O` (a field), if a nonunit common factor `q` existed, then
   `q² ∣ G.map …`, contradicting `hsq` — mathlib route: `Squarefree.isCoprime_of_dvd_mul` shape
   or direct: `IsCoprime` in a PID ⟺ no common irreducible; assemble via
   `EuclideanDomain.isCoprime_of_squarefree_mul` (search; else four `have`s through
   `UniqueFactorizationMonoid`).
3. `ν = 1`: degree 0 + monic ⟹ `G′ = 1` (`Polynomial.Monic.natDegree_eq_zero`).

**SIZE.** 30 lines. **SPLIT CANDIDATE:** the squarefree-coprime step as a private helper
(`E18a`) if the mathlib search comes back empty.

**SOURCE.** `EFF.T2.23` (`(MID-PEEL)`/`(MID-MASS)` displays; the separability⟹key-freeness
derivation, verbatim; "If ν = 1, G′ = 1 and no successor exists"; "The peel occurs before
`(WINDOW)` so +∞ is never fed to Newton accounting"); `EFF.T2.31` clause 5 ("The quotient is
key-free, its mass is smaller by one, and its represented degree is smaller by D; the peeled
boundary roots are discharged by their certified boundary/orbit decomposition, which is item 5
of the `(MID-PEEL)` input suite and is a HYPOTHESIS of this clause, not a consequence of the
peel identity").

**⚠ `(MP1)` FENCE (the clause's conditionality is NOT this node's).** This node proves the
PEEL IDENTITY layer only. Items 2–5 of the `(MID-PEEL)` input suite — `(WINDOW)` for `G′`, its
full development with `(ACCOUNT)` and the S1.7 test assertions, and the peeled key's certified
orbit/`(e,f)` decomposition — are: at the ORIGINAL level-one key, supplied by
`EFF.HE6.PEEL-CONVENTION`-content through the level-1 instance (E.22, B/C-side); at a
RECENTERED level-one key, `(MP1)` — OPEN, carried at E.40; at level two, discharged by S1.8B =
E.42. A fleet agent asked to prove the input suite has left the chapter.

**TEETH.** S7 reducible/recentered-key boundary attacks; Pass 2 several-boundary-factor tooth
→ the identity layer becomes a **Lean theorem**; the suite stays split by level exactly as the
ledger has it.

**ENVIRONMENT.** ENV-E2 (+ `[IsDomain O]`).

---

### NODE E.19 [def+lemma] [fresh]

**STATEMENT.** *The `(RANK)` tuple and its well-foundedness.* The read's state rank is the
lexicographic triple `rank(S) = (deg F_S, μ_S, σ_𝒞(S))` (`EFF.T2.27`). Define the abstract
state carrier `LadderState W := ℕ × ℕ × W` with the lexicographic order (first two components
`<` on `ℕ`, third the rung's `WellFoundedRelation W`), and prove it well-founded. Companion
decrease lemmas, one per transition kind, each taking the kind's numeric fact as hypothesis
(the six checks of `EFF.T2.27`'s derivation): split (deg strictly down), peel (deg and mass
down — E.18(i)), child jump (deg non-increasing, mass strictly down — E.17(ii)), product-1
recentering (deg and mass preserved, `W` strictly down), boundary residual (deg down).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The `(RANK)` state: `(deg, μ, σ)` ordered lexicographically (`EFF.T2.27`). -/
def LadderState (W : Type*) := ℕ ×ₗ (ℕ ×ₗ W)

instance ladderState_wf {W : Type*} (r : WellFoundedRelation W) :
    WellFoundedRelation (LadderState W)

theorem rank_decreases_of_deg_lt {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h : s'.1 < s.1) : (ladderState_wf r).rel s' s

theorem rank_decreases_of_mass_lt {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h1 : s'.1 = s.1) (h2 : s'.2.1 < s.2.1) :
    (ladderState_wf r).rel s' s

theorem rank_decreases_of_sec {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1)
    (h3 : r.rel s'.2.2 s.2.2) : (ladderState_wf r).rel s' s
```

**DEPENDS.** E.12 (the `W`/`wf` fields) · mathlib `Prod.Lex`, `Prod.lex_wf` /
`WellFoundedRelation` instances for `×ₗ`.

**PROOF.**
1. Instance: `Prod.Lex` of well-founded relations is well-founded (mathlib
   `WellFounded.prod_lex`, twice).
2. The three decrease lemmas: constructors of `Prod.Lex` (left / right-left / right-right),
   after rewriting the equal components.

**SIZE.** 24 lines.

**SOURCE.** `EFF.T2.27` (`(RANK)` boxed display; "Every permitted nonterminal transition
therefore strictly decreases `(RANK)`, and no transition increases a component earlier than the
one it decreases"; the six transition checks in the DERIVATION; the CONDITIONALITY sentence —
"Every transition must also preserve or partition roots and transport its polynomial product;
rank descent alone is insufficient" — which is why E.20 takes the partition data separately);
`EFF.T2.26` (`(SEC-RANK)`: `W_𝒞` MERELY well-founded, "an instance may discharge it either
way" — hence the abstract `W`, never `ℕ`).

**TEETH.** S7 Pass 2 well-founded-but-root-losing mutant → closed structurally: this node
exports ONLY rank descent; exhaustion is E.20's separate input (the mutant cannot be expressed
as a use of this node alone).

**ENVIRONMENT.** ENV-E1.

---

### NODE E.20 [theorem] [fresh]

**STATEMENT.** *Termination and exhaustion of the recursive read (HE7.A clause 6, schema
form).* Abstract form: let `step : LadderState W → Finset (LadderState W) → Prop` be a
transition system in which every non-terminal state `s` steps to a finite set of successors
each of strictly smaller rank (E.19's relation), and let a **conserved weight**
`wt : LadderState W → ℕ` satisfy: at every step, `Σ_{s′ ∈ successors} wt s′ = wt s` (the
root-partition bookkeeping: "preserve or partition roots"), and at terminal states `wt` is the
emitted class size. Then: (i) every read tree from `s₀` is FINITE (well-founded recursion);
(ii) the multiset of terminal emissions has total weight `wt s₀` (exhaustion: "pairwise
disjoint root sets, their product is `F`"); (iii) at every terminal the `(e, f)`-increments
multiply along the path (the composed invariants, via E.06). Clause-6 packaging: applied with
`wt = the state's represented degree` and the per-transition conservation supplied by
`hexhaust`/`haccount` (E.12) at splits, E.18(i) at peels, and the child/refine cases' block
data.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem read_terminates_exhausts {W : Type*} (r : WellFoundedRelation W)
    (step : LadderState W → Finset (LadderState W))
    (terminal : LadderState W → Prop) [DecidablePred terminal]
    (wt : LadderState W → ℕ)
    (hdec : ∀ s, ¬ terminal s → ∀ s' ∈ step s, (ladderState_wf r).rel s' s)
    (hcons : ∀ s, ¬ terminal s → ∑ s' ∈ step s, wt s' = wt s) :
    ∀ s₀, ∃ leaves : Multiset (LadderState W),
      (∀ l ∈ leaves, terminal l) ∧ (leaves.map wt).sum = wt s₀
```

**DEPENDS.** E.19 · mathlib `WellFounded.fix` / `WellFounded.induction`,
`Finset.sum_multiset` bridges.

**PROOF.**
1. Well-founded induction on `s₀` along `(ladderState_wf r).rel`.
2. Terminal case: `leaves := {s₀}`, weight matches trivially.
3. Non-terminal: each `s′ ∈ step s₀` is smaller (`hdec`), apply the inductive hypothesis, take
   the multiset union of the returned leaf sets; the weight sums telescope by `hcons` and
   `Multiset.sum_bind`.

**SIZE.** 26 lines. **SPLIT CANDIDATE:** the multiset-bind bookkeeping as a private helper.

**SOURCE.** `EFF.T2.31` clause 6 + DERIVATION ("Each transition preserves or partitions roots
and transports products, so induction gives exhaustion as well as termination"); `EFF.T2.27`
(the well-founded induction and its insufficiency caveat — here `hcons` is the extra input);
`EFF.T2.44` (the S-6 GO's shape: master = induction over the six transitions).

**⚠ SCHEMA HONESTY.** This node is the INDUCTION ENGINE, not the full clause 6: instantiating
`step` with the actual four-case read requires, per state, the transition's input suite —
`(LB1)` at level-one clause-4 states (E.39), `(MP1)` at level-one recentered-key peels (E.40),
the S1.8B/S1.8C discharges at level two (E.42/E.43), `(RISE)`/`(REF-HT)` at recenterings
(E.55/E.56 layer), and the α-refine finiteness folded into `W`'s well-foundedness
(`EFF.T2.26`'s instance table). The instantiation map is E.22/E.23's obligation tables; the
conditionality is exactly `EFF.T2.31`'s: "Full carrier suite, including `(SEC-RANK)` and
`(RISE)`; `(LB1)` when level-one clause 4 constructs blocks; `(MP1)` for a level-one clause-5
peel at a recentered key."

**TEETH.** S7 finite-refinement/root-preservation attacks → **Lean theorem** (the engine);
Q1's "1,587/1,587 members decided" is the instance evidence at `n = 8` (E.23).

**ENVIRONMENT.** ENV-E1.

---

### NODE E.21 [theorem] [fresh]

**STATEMENT.** *THEOREM T2.KEY-BOUNDARY, schema form.* Let `F : Polynomial O` be monic with a
boundary decomposition `(BOUNDARY-PROD)` `F = (Π_i P_i) * (Π_j B_j)` (given as data: a finite
list of certified boundary factors `P_i` and residual blocks `B_j`, with the products' root
counts disjoint and exhaustive in the weight bookkeeping of E.20), where each residual block
carries a full rung-interface suite. Then the terminal emissions of the blocks' reads, together
with the boundary factors, have pairwise-disjoint weight and total weight `deg F` — "Adjoin the
certified irreducible boundary factors `P_i`, and apply HE7.A separately to each key-free
residual block `B_j`" (`EFF.T2.32`). The gcd computation producing `(BOUNDARY-PROD)` is the
instances' (`G = monicGCD_{K₀[x]}(F, Φ)`, `EFF.T2.28`); the corpus fence transcribes: "Nothing
asserts that `G = Φ`, that `Φ` is irreducible, that one factor `Φ` is peeled, or that a peel
lowers `μ` by exactly one."

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem key_boundary {O : Type*} [CommRing O] [IsDomain O]
    (F : Polynomial O) (hF : F.Monic)
    (boundary : List (Polynomial O)) (blocks : List (Polynomial O))
    (hprod : F = boundary.prod * blocks.prod)
    (hbmon : ∀ P ∈ boundary, Polynomial.Monic P)
    (hkmon : ∀ B ∈ blocks, Polynomial.Monic B)
    -- per-block read results, supplied by E.20's engine at each block:
    (emit : Polynomial O → Multiset ℕ)                -- terminal class weights
    (hemit : ∀ B ∈ blocks, (emit B).sum = B.natDegree) :
    (boundary.map Polynomial.natDegree).sum
      + (blocks.map (fun B => (emit B).sum)).sum = F.natDegree
```

**DEPENDS.** E.20 · mathlib `Polynomial.natDegree_list_prod` (monic), `List.sum_map`.

**PROOF.**
1. Degrees add over the monic product (`Polynomial.Monic.natDegree_mul` iterated /
   `natDegree_list_prod` with monicity).
2. Substitute `hemit` per block; `List.sum` arithmetic closes.

**SIZE.** 18 lines.

**SOURCE.** `EFF.T2.32` (THEOREM T2.KEY-BOUNDARY, statement + verbatim proof: "The boundary
decomposition already gives the polynomial product and the disjoint exhaustive partition …
Multiplying the resulting identities proves the assertion"); `EFF.T2.28` (`(BOUNDARY-PROD)`,
the suite obligation per residual block, and the four-part negative fence, transcribed above);
`EFF.T2.44` ("A reducible key boundary is handled by a separate gcd/orbit decomposition, never
by a false one-factor peel").

**TEETH.** S7 Pass 1 reducible-key gate; Pass 2 multiple-boundary-factor tooth → **Lean
theorem** (the composition layer); the per-block suites are instance obligations (E.22/E.23).

**ENVIRONMENT.** ENV-E2 (+ `[IsDomain O]`).

---

### NODE E.22 [instance-record] [fresh]

**STATEMENT.** *The level-one instance record (HE3+HE6 composite), as an obligation table.*
The corpus's S3.1/S3.2 records (`EFF.T2.33`/`.34`) instantiate the §4 structures at
`K = 𝔽_{Q^{f₁}}`, `Φ = Φ′`, `D = D′ = e₁f₁`, `(e_𝒞, f_𝒞) = (e₁, f₁)`, `d = dv = e₁v`,
`T = D′h`, `dig(A) = γ_{dv(A)}(A)`, `gcd(h, e₁) = 1`, dictionary `(e, f) = (e₁e_s, f₁f_s)`.
This node is NOT a Lean construction — it is the blueprint's binding obligation map for the
instance, one row per §4 field:

| field (E.10–E.12) | supplier at level 1 | citation form |
|---|---|---|
| `hgt`/`dig` data + `(SLOT-V)/(SLOT-R)` laws | B's digit layer on the `e₁ = 1` slice (B.21 `digAt`, B.22); `e₁ ≥ 2` normalizer reads | B.21/B.22 by node ID; `EFF.HE6.09 [supplied-by: chapter C]` (honesty E-2) |
| `Full`/`hlift` | fullness criterion `k ≥ (i(k)+e₁(f₁−1))h`, uniform `(D′−1)h` | `EFF.T2.10`'s HE6 row: `EFF.HE6.15 .17 [supplied-by: chapter C]`; arithmetic half = E.08/E.32 |
| `hef` `(DEG-EF)` | `D′ = e₁f₁` definitional at the instance | E.01 base rung |
| block `(DEV)`/`(KEY-FREE)`/`hA0` | B's development layer (B.01–B.14) | B node IDs (committed) |
| `sides`/`len`/`hlen_sum` | B's polygon side data (B.16–B.20) via GC-2 | B.16–B.20 by node ID |
| `linFac`/`hiFac`/`hresdeg` | B's residual factorization (B.28–B.30, `sideMin` pin per GC-1/PA-1) | B.28–B.30 by node ID |
| `haccount` (D-E3) + the INTEGRAL `(ACCOUNT)` | `HE6-ACCOUNT` (the resultant identity, κ > D′h) + `HE6-BETA-GUARD` transitivity (Rider 2) | `EFF.HE6.56 [supplied-by: chapter C]` — B's H-2 refusal covers the class-size route |
| `hforce` | test-package clause 6 (local invariants divisible) | `EFF.T2.15` clause 6: `EFF.HE6.29 [supplied-by: chapter C]` |
| `hnonempty`/`hexhaust` | test-package clauses 3–4 (resultant symmetry / disjoint exhaust) | same placeholder family |
| `W`/`wf`/`σRank` `(SEC-RANK)` | `HE3-A-PROOF`'s stage-α termination — an `ℕ`-valued rank (window bound minus current floor) | `EFF.T2.52`'s level-one bullet: `EFF.HE3.02-area [supplied-by: chapter C]`; B's certificates (B.79–B.82) fire the leaf reads |
| `(RISE)` at recenterings | `HE3-A-PROOF` stage-α + `HE6-FAMILY`/`HE6-PROOF` | `EFF.T2.19`'s X02/X10–X11 pins → C placeholders |
| test clauses 1/2/7 + `(WINDOW)`/proxy safety | HE6 test package | C placeholders |

**Fences carried verbatim** (`EFF.T2.33`): clause-4 block construction is `(LB1)`-conditional;
a clause-5 peel at a RECENTERED level-one key is `(MP1)`-conditional; the ORIGINAL-key peel is
supplied by `HE6-PEEL-CONVENTION` (C placeholder). **Grade cap** (`EFF.T2.38`): HE3 is consumed
at attempt grade 0/2 (clean 1/2), so this instance and every level-two chain consuming it
through S1.8C "remain capped there" — recorded for chapter I's conditionality bookkeeping, NOT
as a Lean object.

**SIGNATURE.** none (obligation record; the stub stage checks the table's B-node citations
against committed CHAP-B signatures).

**DEPENDS.** E.10–E.12 (the field list); CHAP-B nodes cited above; chapter-C placeholders as
listed.

**PROOF.** n/a. **SIZE.** n/a (table).

**SOURCE.** `EFF.T2.33` (HE3-INSTANCE, boxed); `EFF.T2.34` (HE6-INSTANCE, boxed;
`|S_{λ,r}| = D′ℓ deg r`, `(e,f) = (e₁ℓ, f₁deg r)`); `EFF.T2.16` (the integral `(ACCOUNT)`,
quoted here in full per D-E3's promise: "`Σ_{ρ:F(ρ)=0} min(w_ρ, κ) = D Σ_{λ∈Sides(P)} L_λ
min(λ, κ)` — This is the only side-accounting identity used by the master proof", `κ > T`,
HE6 proves it on `κ > D′h`); `EFF.T2.56`/`.96` (the final Source-pin line discipline this
table mirrors).

**TEETH.** HE6 seam gate; level-one `(RISE)` discharge tooth; the five-instance perimeter gate
→ disposition: the table rows are checked at the stub stage (0e) against B's signatures; C-side
rows enter C's TEETH tables.

**ENVIRONMENT.** n/a.

---

### NODE E.23 [instance-record] [fresh]

**STATEMENT.** *The level-two and tower instance records (HE7 / HETOW / GENTOW4), as an
obligation table.* `EFF.T2.35`–`.37` instantiate §4 at `K_𝒞 = K₂`, `Φ = Ψ_{λ,r}` (resp. `Φ₂`),
`D = D″ = D′ℓd_r` (resp. `D₂ = D′e₂f₂`), `(e_𝒞, f_𝒞) = (e₁ℓ, f₁d_r)` (resp. `(e₁e₂, f₁f₂)`),
`d = dv₂ = ℓe₁v`, `T = T₂`. Obligation map — the decisive difference from E.22: **most field
suppliers are E's own §5 nodes** (the level-2 machinery is HE7's, ruled into E):

| field | supplier | citation form |
|---|---|---|
| `hgt`/`dig` + slot laws | (SLOT₂) = E.29 (schema) over the level-1 carrier; normalizer system `n₂` | E.29; carrier data `EFF.HE7.06 [supplied-by: chapter C]` for the `Pt`-evaluation legs |
| `Full`/`hlift` | (LIFT₂) = E.31, thresholds E.08, margins E.09 | E-internal |
| `sides` etc. at level 2 | the `P₂` polygon of the Ψ-development, read off `f` when the block is proper: LEMMA HE6R1-2 (with the CORRECTED per-side scalar `γ_g·β^{c₁(m₁^{f_S}, c_g)}`, honesty E-1's HE7 residual noted) | `EFF.HE6R1 [supplied-by: chapter C]`; the scalar's exponent arithmetic = E.04/E.33 |
| `haccount` | `(†₂-count)` + HE6-3 sampling (`EFF.HE7.41`'s proof) | the derivation is C's (polygon sampling); its termwise output `n_{λ₂} = D″L_{λ₂}` enters as the field |
| `hforce` | LEMMA HE7-5 = local forcing (key-free) | `EFF.HE7.29 [supplied-by: chapter C]` for the Galois/valuation legs; GC-3 rank form at the `e·f` read |
| `hnonempty`/`hexhaust` | LEMMAS HE7-9/HE7-10 + COROLLARY HE7-7″ (licensed by R2-a = E.36) | schema shape E.14–E.16; carrier legs C placeholders |
| `(SEC-RANK)` | LEMMA HE7-8 = E.55 (well-foundedness form) at a DEFINITION HE6-1 key; at the COMPOSED key via `HETOW-A`(ii)/`GENTOW-4-A`(iii) + the W+w fold (E.42) | E.55/E.42 + `EFF.T2.52`'s two composed-key bullets → `[supplied-by: chapter C]` for the HETOW/GENTOW4 clauses |
| `(RISE)`/`(REF-HT)` | LEMMA HE7-12/13 = E.38/E.56; the derivation E.56 | E-internal (schema) |
| the peel at Ψ | LEMMA HE6R1-3 + the convention chain = E.37 (licensed by R2-a = E.36) | `EFF.HE6R1 [supplied-by: chapter C]` for HE6R1-3's own proof |
| mixed-node blocks | ANNEX-LEMMA HE7-13′ = E.57 | E-internal (schema) + C legs |

**Fences carried verbatim**: `EFF.T2.35` — "If the underlying level-one key was recentered,
S1.8C transports the HE3+HE6 frame with its existing `(LB1)`/`(MP1)` triggers";
`EFF.T2.36`/`.37` — "Any proper-gcd key boundary uses T2.KEY-BOUNDARY" (= E.21); "Raw and
coherent coefficient arrays are not identified"; GENTOW4's reading directive (`EFF.T2.54`):
the superseded "top coefficient NOT monic" parenthetical is NEVER consumed — only
`μ₂* = Σ_{λ₂>T₂} L_{λ₂}(f)` and `deg f_S = D₂μ₂*`; "The count-side mixed-multiplicity tie,
partial-side budgets, and density laws are not conclusions of this σ-decision instance"
(`EFF.T2.37` — those are chapter C/D objects).

**SIGNATURE.** none (obligation record). **DEPENDS.** E.10–E.12, E.29, E.31, E.36–E.38, E.42,
E.55–E.57; C placeholders as listed. **PROOF.** n/a.

**SOURCE.** `EFF.T2.35` (HE7-INSTANCE), `.36` (HETOW-INSTANCE, incl. the frame conversion
`R_{λ₂}(Z) = τ(H₀)·R̂_{λ₂}(Z/δ)`, `δ = τ(u₃) ∈ K^×` — a `(FRAME)` instance, σ-invariant per
E.54), `.37` (GENTOW4-INSTANCE); `EFF.T2.52` (the three `(SEC-RANK)` discharge bullets,
verbatim-quoted in the spec); `EFF.T2.56` (the per-record Source-pin discipline).

**TEETH.** live cocycle carry; mixed block; level-two peel; refine-chain termination; HETOW
frame gate; composed-key/C-A gate → dispositions distributed to the supplying nodes' TEETH
fields; the GENTOW4 perimeter row enters §13.

**ENVIRONMENT.** n/a.

---

### NODE E.24 [def] [fresh]

**STATEMENT.** *The HE7A conjunct package (Display A's `HE7A[ACCOUNT, RES-DEG, nonempty,
exhaust, root-continuation]`, handed to chapter I).* A `Prop`-valued bundle, one field per
Display-A sub-conjunct at exactly ledger strength, over a rung instantiation: the five clause
families ARE E.12's fields, so the package is the statement "a rung interface exists for the
block" plus the two obligations and the indexed deep-twist carriers:

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- Display A's `HE7A[…]` conjunct: the σ-ladder carrier suite holds for the block —
packaged for chapter I's hypothesis structure. The five clause families are the FIELDS of
`RungInterface` (E.12); `(LB1)`/`(MP1)` are §6's carriers; the `∀ i ≥ 3` deep-twist and
w-frame carriers are §9's. -/
def HE7APackage {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  Nonempty (RungInterface C B)

/-- The full chapter-E supply to chapter I: the package at every rung of a ladder,
plus the carried obligations. -/
structure LadderSupply {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop where
  package : HE7APackage C B
  lb1 : LB1Carrier C B           -- E.39
  mp1 : MP1Carrier C B           -- E.40
  vartheta : ∀ i ≥ 3, VarthetaRes i    -- E.61 (with E.62's 𝒲 conjunct at I)
```

**⚠ SIGNATURE NOTE.** `LadderSupply`'s last three fields reference §6/§9 declarations
(forward references within this chapter — the stub stage lands §6/§9 first or reorders; the
DAG (§11) carries the true topological order: E.39, E.40, E.61, E.62 precede E.24). Chapter I
consumes `HE7APackage` and `LadderSupply` BY NAME; any change to their field list is a
capstone-conditionality change and goes through the owner gate (Part V (a)).

**DEPENDS.** E.12, E.39, E.40, E.61 (forward, see note).

**PROOF.** definitional. **SIZE.** 18 lines.

**SOURCE.** `EFF.T2.39` (the five-family fence, verbatim — the field list IS the fence);
`spec/HYPOTHESIS_LEDGER.md` Display A (the `HE7A[…]` conjunct + `(LB1)`, `(MP1)`,
`(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` conjuncts); BRIEF E product clauses (1), (2), (4).

**TEETH.** none (packaging); chapter I's gates re-fire the `n ≤ 2` slices against it.

**ENVIRONMENT.** ENV-E2.

---

## 5. §5 — THE SLOT-SEAM EVALUATION LAYER (corrected seam, SLOT/LIFT at every level, the twist bookkeeping)

> **Placement note (the H → E entry point, and the E-1 discipline).** This section is where E
> consumes H §8 (H.51–H.58) — the slot lemma is "the ladder base case" (`EFF.GENHN.27`'s reverse
> XREF) — and where the HYP.150–154 adjudication bites: every seam display below is T2's own
> corrected `(GAMMA)`/`(HE6-SEAM)` form (= A3 F-1's `γ_k(A)`), never the bare pre-A3
> `HE6-SLOT-SEAM` residue. Per GC-2/D-1 criterion C2, every evaluation statement is a
> support-function/argmin statement on `ladderSuppVal`-shaped objects or pure exponent
> arithmetic; no polygon object exists here.

### NODE E.25 [lemma] [fresh]

**STATEMENT.** *Seam exponent integrality (the `(GAMMA)` sum is denominator-free on its
support).* Fix `e, h : ℕ` coprime (`1 ≤ e`), `i < e`, and `k : ℕ` with `k ≡ i*h [MOD e]`. Then
for every `t` with `k ≥ (i + e*t)*h`: `e ∣ k − (i + e*t)*h`, so the `(GAMMA)` exponent
`(k − (i+e*t)h)/e` is an honest natural, and the map `t ↦ (k − (i+e*t)h)/e` is strictly
antitone in `t` (each step drops by `t*h`-increments: exact drop `h` per unit `t` after the
division... precisely: `(k − (i+e(t+1))h)/e = (k − (i+et)h)/e − h`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem seam_exp_dvd {e h i k t : ℕ} (hcop : Nat.Coprime h e) (hi : i < e)
    (hk : k % e = (i * h) % e) (ht : (i + e * t) * h ≤ k) :
    e ∣ k - (i + e * t) * h

theorem seam_exp_step {e h i k t : ℕ} (hi : i < e)
    (ht : (i + e * (t + 1)) * h ≤ k) :
    (k - (i + e * t) * h) / e = (k - (i + e * (t + 1)) * h) / e + h
```

**DEPENDS.** H.51 (`class_sep` — the congruence engine) · mathlib `Nat.sub_mod`,
`Nat.add_mul_div_left`.

**PROOF.**
1. `seam_exp_dvd`: `(i + et)h ≡ ih ≡ k (mod e)`, so the difference is `≡ 0`;
   `Nat.dvd_sub'` after `Nat.modEq` bookkeeping.
2. `seam_exp_step`: `(i + e(t+1))h = (i + et)h + e*h`, so the numerators differ by `e*h`;
   divide (`Nat.add_mul_div_left`, `e > 0`). `omega` finishes with the guard `ht`.

**SIZE.** 16 lines.

**SOURCE.** `EFF.T2.06` (`(GAMMA)` boxed: `γ_k(A) = Σ_{t≥0, i+e₁t<D′}
res(a_{i+e₁t}·π^{−(k−(i+e₁t)h)/e₁})·η^t` — "The coefficient normalizers inside `γ_k(A)` … are
mandatory"); `EFF.HE7.19` (LEMMA HE7-L1's proof: "the slot `i` contributes at height `k` iff
`e₁v(a_i) = k − ih ≥ 0` … which forces `i ≡ i₀ (mod e₁)` and `k ≥ ih`").

**⚠ HYP.150/151 DISCIPLINE (binding on every consumer of this node).** The bare pre-A3
`HE6-SLOT-SEAM` display — the unnormalized coefficient-residue sum — is AFFIRMATIVELY FALSE for
`k > (D′−1)h` (HYP.151's re-derivation: at those heights every bare summand vanishes while the
true residue is a unit). `EFF.T2.06`'s own words transcribed here: "The bare unnormalized
coefficient-residue sum is not an alternative formula." No chapter-E node states the bare form;
E.66's gate exercises a `k > (D′−1)h` witness at `q = 3` (honesty E-6).

**TEETH.** the HE6 seam gate; the print/coherent-frame hostile tooth → **Lean theorem** for
the exponent half; the residue half is E.29.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.26 [def] [fresh]

**STATEMENT.** *The (twisted) seam sum.* In the stage-field arena (`F ⊆ K` finite fields,
`η : K`): `seamSum γ η = Σ_{t<g} (algebraMap F K (γ t)) * η^t` for `γ : Fin g → F`; and the
twisted form `seamSumT γ ϑ η = Σ_{t<g} (algebraMap F K (γ t)) * (ϑ t : K) * η^t` for a unit
vector `ϑ : Fin g → Kˣ` whose entries lie in the `F`-span... — precisely, for R1-b's use the
twist units are `algebraMap`-images of `Fˣ`-elements (`ϑ_t ∈ K_i^×`, the PREVIOUS level's
field), so the signed form takes `ϑ : Fin g → F` with a nonvanishing hypothesis. This is the
assembly `Σ_t γ_t·ϑ_t·β^t` of `EFF.HE7.110` (and `Σ_t γ_t β^t` of `(SLOT₂)`, the `ϑ ≡ 1`
instance).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The seam sum `Σ_t γ_t η^t` (the `(GAMMA)`/`(SLOT₂)` residue assembly). -/
def seamSum {F K : Type*} [Field F] [Field K] [Algebra F K]
    {g : ℕ} (γ : Fin g → F) (η : K) : K :=
  ∑ t : Fin g, algebraMap F K (γ t) * η ^ (t : ℕ)

/-- The twisted seam sum `Σ_t γ_t·ϑ_t·η^t` (R1-b's display); `ϑ` in the base field. -/
def seamSumT {F K : Type*} [Field F] [Field K] [Algebra F K]
    {g : ℕ} (γ ϑ : Fin g → F) (η : K) : K :=
  ∑ t : Fin g, algebraMap F K (γ t * ϑ t) * η ^ (t : ℕ)
```

**DEPENDS.** none (ENV-E3 primitives).

**PROOF.** definitional. **SIZE.** 12 lines.

**SOURCE.** `EFF.T2.06` (`(GAMMA)`); `EFF.HE7.11` ((SLOT₂)(b): "`res(C(ξ)/n₂(k)(ξ)) =
ι_ξ^{(2)}(Σ_{t<d_r} γ_t·β^t)`"); `EFF.HE7.110` (R1-b: "`ι_ξ^{(i+1)}(Σ_{t<g_i}
γ_t·ϑ_t·β_i^t)`", "`ϑ_t ∈ K_i^×` … depending on `(k, t)` and the s-bookkeeping only").

**TEETH.** none directly (definition); E.27 carries the kill.

**ENVIRONMENT.** ENV-E3.

---

### NODE E.27 [lemma] [fresh]

**STATEMENT.** *The twisted seam kill (no cancellation).* With `[Algebra F K]`, `η : K`
integral with `(minpoly F η).natDegree = Module.finrank F K = g`: if some `γ t ≠ 0` and every
`ϑ t ≠ 0`, then `seamSumT γ ϑ η ≠ 0`. (R1-b Step 3's closing argument: "the coefficients
`γ_t·ϑ_t` lie in `K_i` and vanish iff `γ_t` does (`ϑ_t` is a unit), and at least one attaining
`γ_t ≠ 0` — so the sum is NONZERO"; at `ϑ ≡ 1` this is `(SLOT₂)` Step 3's K-basis
independence.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem seamSumT_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K] {η : K}
    (hgen : (minpoly F η).natDegree = Module.finrank F K) (hint : IsIntegral F η)
    {g : ℕ} (hg : g = Module.finrank F K) (γ ϑ : Fin g → F)
    (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    seamSumT γ ϑ η ≠ 0
```

**DEPENDS.** E.26, **H.53** (`eta_independent`, consumed by committed signature — the
sanctioned H §8 slice).

**PROOF.**
1. Suppose the sum is 0. `eta_independent` (H.53) applied to the coefficient family
   `t ↦ γ t * ϑ t` gives `γ t * ϑ t = 0` for every `t`.
2. Fields have no zero divisors: `ϑ t ≠ 0` forces `γ t = 0` for every `t`, contradicting `hγ`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.HE7.110` (Step 3, quoted above); `EFF.HE7.11` (Step 3: "r is irreducible over
K of degree d_r, so {1, β, …, β^{d_r−1}} is a K-basis of K₂; since the γ_t lie in K and at
least one attaining γ_t is nonzero, the sum is nonzero"); `EFF.GENHN.27` (the level-1 base:
within-class residue-field independence — H.53's own source).

**TEETH.** `he7rannex_supp.py` P3 (18/79 σ flips when the deep letter is dropped — the twist
is load-bearing in the kill's inputs) → **Lean theorem**; the `ϑ_t, t ≥ 1` machine hole
(`EFF.HE7.110`'s disclosure: `g₂ = 1` throughout the level-3 family, "structurally invisible")
is recorded in §13 as instance evidence NOT covering `t ≥ 1` — the Lean proof covers every `t`
at once, the same H.53 move that discharged GENHN's `f₁ ≥ 2` vacuity.

**ENVIRONMENT.** ENV-E3.

---

### NODE E.28 [lemma] [fresh]

**STATEMENT.** *Rung class separation and the single-class minimum.* For a rung `R` (coprime
`u, ℓ`): (i) two slots `s ≢ s′ (mod ℓ)` have term values `ℓ*v + s*u ≢ ℓ*v′ + s′*u (mod ℓ)`
never equal (cross-class ties impossible); (ii) the minimizing slots of any family
`s ↦ ℓ * w s + s * u` (`w : ℕ → ℕ`, `s < L = ℓg`) all lie in ONE residue class
`s₀ + ℓ·{0,…,g−1}`; (iii) within the class, slot `s₀ + ℓt` attains the min `k` iff
`w (s₀ + ℓt) = m₀ − t*u` (where `ℓm₀ + s₀u = k`). This is `(SLOT₂)` Step 2 / R1-b Step 2 —
"the (e₁, f₁) pattern of GENHN-2 with `(e₁, f₁) ↦ (ℓ, d_r)`" — i.e. H.51/H.52's content
re-lettered at the rung.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem rung_class_sep (R : RungDatum) {s s' v v' : ℕ}
    (hs : s < R.slotCount) (hs' : s' < R.slotCount)
    (hmod : s % R.ℓ ≠ s' % R.ℓ) :
    R.ℓ * v + s * R.u ≠ R.ℓ * v' + s' * R.u

theorem rung_min_class (R : RungDatum) {s k m₀ s₀ t : ℕ}
    (hks : R.ℓ * m₀ + s₀ * R.u = k) (hs₀ : s₀ < R.ℓ)
    (hattain : s = s₀ + R.ℓ * t) (w : ℕ → ℕ)
    (hval : R.ℓ * w s + s * R.u = k) :
    w s = m₀ - t * R.u ∧ t * R.u ≤ m₀
```

**DEPENDS.** E.01, E.03, **H.51** (`class_sep`) · the coprimality transposed: H.51 separates
`i*h mod e`; here the roles are `(h, e) ↦ (u, ℓ)` — the same lemma, arguments swapped.

**PROOF.**
1. `rung_class_sep`: reduce both sides mod `ℓ`: `s*u ≢ s′*u (mod ℓ)` by H.51's injectivity
   (`Nat.Coprime u ℓ`; note H.51's `hcop : Coprime h e` instantiates at `(u, ℓ)`).
2. `rung_min_class`: substitute and cancel: `ℓ·w s + (s₀ + ℓt)u = ℓm₀ + s₀u` gives
   `ℓ(w s + tu) = ℓm₀`, cancel `ℓ ≥ 1`: `w s + tu = m₀`. `omega`.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE7.11` (Step 2, verbatim: "`ℓ·dv(c_s) + s·u ≡ s·u (mod ℓ)`, and `s ↦ s·u mod
ℓ` is a bijection of `ℤ/ℓ` because `gcd(u, ℓ) = 1` … The minimum … is therefore attained inside
a single class `s₀ + ℓ·{0,…,d_r−1}` — exactly ℓ classes of exactly d_r slots each"; Step 3's
attaining criterion "iff `dv(c_{s₀+ℓt}) = m₀ − tu`"); `EFF.HE7.110` (Step 2 "twist-free …
verbatim").

**TEETH.** HE7-T-SLOT2TIE (`gcd(u,ℓ) ≠ 1` ⟹ classes share heights, exactness fails — fired) →
**Lean theorem**; the tooth's hypothesis is E.01's `hcop` field.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.29 [theorem] [fresh]

**STATEMENT.** *The twisted slot lemma at a rung (R1-b schema; `(SLOT₂)` is its `ϑ ≡ 1`
instance).* Let `C` be the LEVEL-`i` slot carrier (E.10), `R` the rung, and
`c : ℕ → Polynomial O` a slot family (`c s = 0` for `s ≥ L`, `deg (c s) < C.D`, not all zero).
Define `k := min over occupied s of (ℓ * (hgt (c s)).untop + s * u)` (cleared; `WithTop`
handled by restriction to the occupied support). Then:
(i) the minimum is attained in one class `s₀ + ℓ·{t < g}` (E.28), and per attaining slot the
level-`i` digit is `γ_t := C.dig (c (s₀ + ℓt))` — nonzero exactly at attainers;
(ii) with twist inputs `ϑ : Fin g → K` (all nonzero; supplied by the cocycle bookkeeping E.33
at instances, `ϑ ≡ 1` at the base rung), the level-`(i+1)` residue of the assembled development
`Σ_s c s * Φ^s` at height `k` is `seamSumT γ ϑ η ≠ 0` (E.27) — so the level-`(i+1)` height is
the min EXACTLY (no cancellation) — **stated as a specification of the next level's carrier**:
the pair `(hgt_{i+1}, dig_{i+1})` defined by (min, seamSumT) satisfies E.10's field laws on
developments, given E.10's laws one level down.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The twisted slot specification (R1-b): the value/residue read of a slot family at the
next level, as data + laws. `η` generates `K'` over `K` with minpoly degree `g`. -/
theorem twisted_slot_spec {O : Type*} [CommRing O] {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    (c : ℕ → Polynomial O)
    (hdeg : ∀ s, (c s).natDegree < C.D) (hsupp : ∀ s, R.slotCount ≤ s → c s = 0)
    (hocc : ∃ s < R.slotCount, c s ≠ 0)
    (ϑ : Fin R.g → K) (hϑ : ∀ t, ϑ t ≠ 0)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hmin : ∀ s < R.slotCount, c s ≠ 0 → ∀ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) →
      (k : ℤ) ≤ R.ℓ * v + s * R.u)
    (hatt : ∃ s < R.slotCount, c s ≠ 0 ∧
      C.hgt (c s) = ((m₀ : ℤ) - (((s - s₀) / R.ℓ : ℕ) : ℤ) * R.u : ℤ)) :
    seamSumT (fun t => if h : _ then C.dig (c (s₀ + R.ℓ * t)) else 0) ϑ η ≠ 0
    -- (the full spec bundles the class location E.28(ii) and the attainment
    --  criterion E.28(iii); see the SIGNATURE NOTE)
```

**⚠ SIGNATURE NOTE (the contract is the BUNDLE, this display is its kill clause).** The
formalization-trivial decomposition: (a) E.28 locates the class and characterizes attainers;
(b) the `γ`-vector is `dig ∘ c` on the class (zero off-attainers by E.10's `dig`-laws); (c)
E.27 kills cancellation. The fleet lands the node as a `structure`-valued spec
(`TwistedSlotRead`: fields `k, s₀, γ, hclass, hattain, hkill`) if the flat theorem fights
elaboration — RE-PLAN with the orchestrator booking `E29a`, per GC-5. The `if h : _` in the
display abbreviates the in-class guard `s₀ + ℓt < L ∧ c (s₀+ℓt) ≠ 0`; the stub stage fixes the
exact spelling.

**DEPENDS.** E.10, E.26, E.27, E.28 · H.53 (through E.27).

**PROOF.**
1. Class location + attainment: E.28 on the cleared values (the `hmin`/`hatt` hypotheses are
   the cleared form of "k is the min, attained").
2. `γ_t ≠ 0` at some `t`: the attaining slot's digit is nonzero by E.10's `dig_ne_zero`.
3. Kill: E.27.

**SIZE.** 34 lines. **SPLIT-MANDATED** (the structure-valued spec route above).

**SOURCE.** `EFF.HE7.110` (ANNEX-THEOREM R1-b, statement + Steps 1–3, incl. "At i = 1 every
θ_t = 1 … and the display is (SLOT₂) byte-for-byte" and the closing compatibility sentence:
"what the correction moves is the residue's COORDINATES (γ_t ↦ γ_t·ϑ_t)"); `EFF.HE7.11`
((SLOT₂), the `ϑ ≡ 1` instance, statement + proof verbatim); `EFF.T2.06` (the level-1
`(GAMMA)` instance).

**⚠ WHAT IS NOT HERE.** The evaluation reading (`dv₂(C(ξ)) = k` at points `ξ`) is carrier
content — this node specifies the ξ-INDEPENDENT data `(k, seamSumT …)` and its laws, exactly
the split E.10's FAITHFULNESS note declares. The clause-(c) arbitrary-ξ inequality
(`EFF.HE7.11`(c)) is an instance obligation (C placeholder at E.23).

**TEETH.** Q2 / HE7-SLOT2 (12,632 exactness identities, 0 violations) + `he7rannex_supp.py`
(level 3, 79/79) → the schema becomes a **Lean theorem**; the `g₂ = 1` disclosure rides E.27's
TEETH note.

**ENVIRONMENT.** ENV-E2 + ENV-E3 (mixed: `O`-polynomials, two stage fields).

---

### NODE E.30 [lemma] [fresh]

**STATEMENT.** *The realized-set arithmetic `T(k)` (LEMMA HE7-L1's combinatorial core, with the
corrected thresholds).* For `e, h : ℕ` coprime, `f₁ ≥ 1`, `D′ = e*f₁`, and `k : ℕ`; let
`i₀ = i₀(k) < e` be the class index (`i₀*h ≡ k (mod e)`, E.03's uniqueness at the base rung).
Define `T(k) := {t < f₁ : (i₀ + e*t)*h ≤ k}` (a `Finset (Fin f₁)`). Then:
(i) `T(k) = Finset.univ ↔ (i₀ + e*(f₁−1))*h ≤ k` (fullness iff the deepest slot reaches);
(ii) `(D′−1)*h ≤ k → T(k) = univ` (the k-uniform sufficient bound: `i₀ + e(f₁−1) ≤ D′−1`);
(iii) `T(k) = ∅ ↔ k < (i₀)*h`... precisely: `T(k) = ∅ ↔ ¬ (i₀*h ≤ k)` (the `t = 0` slot is the
shallowest — "If T(k) = ∅ the height k is not attained at all").

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

def reachSet (e h f₁ i₀ k : ℕ) : Finset (Fin f₁) :=
  Finset.univ.filter fun t => (i₀ + e * (t : ℕ)) * h ≤ k

theorem reachSet_full_iff {e h f₁ i₀ k : ℕ} (hf : 1 ≤ f₁) :
    reachSet e h f₁ i₀ k = Finset.univ ↔ (i₀ + e * (f₁ - 1)) * h ≤ k

theorem reachSet_full_of_uniform {e h f₁ i₀ k : ℕ} (hi : i₀ < e) (hf : 1 ≤ f₁)
    (hk : (e * f₁ - 1) * h ≤ k) : reachSet e h f₁ i₀ k = Finset.univ

theorem reachSet_empty_iff {e h f₁ i₀ k : ℕ} (hf : 1 ≤ f₁) :
    reachSet e h f₁ i₀ k = ∅ ↔ k < i₀ * h
```

**DEPENDS.** E.03 (the class index) · mathlib `Finset.filter`, `Fin` arithmetic.

**PROOF.**
1. (i): the filter is monotone-decreasing in `t` (`(i₀ + et)h` increases with `t`), so full iff
   the largest `t = f₁ − 1` passes. `Finset.filter_eq_univ_iff` (`Finset.eq_univ_iff_forall`) +
   monotonicity.
2. (ii): `i₀ ≤ e − 1` gives `i₀ + e(f₁−1) ≤ e−1 + ef₁ − e = ef₁ − 1 = D′−1`; multiply by `h`
   and chain with `hk`; apply (i). (This is HE7-L1's own
   `max_k (i₀(k) + e₁(f₁−1))h = (D′−1)h` computation.)
3. (iii): empty iff the SMALLEST `t = 0` fails: `¬ (i₀h ≤ k)`. `Finset.filter_eq_empty_iff` +
   monotonicity.

**SIZE.** 26 lines.

**SOURCE.** `EFF.HE7.19` (LEMMA HE7-L1: the display `T(k) := {t < f₁ : k ≥ (i₀ + e₁t)·h}`, the
two boundary clauses "it is ALL of K^× iff T(k) = {0,…,f₁−1} iff k ≥ (i₀(k) + e₁(f₁−1))·h; a
k-uniform sufficient condition is k ≥ (D′−1)h. If T(k) = ∅ the height k is not attained at
all"; the proof's threshold computation); `EFF.HE7.21` (FINDING HE7-F1's two counterexamples —
`(3,1,2)`: `k = 1` unattained; `(2,2,1)`: `k ∈ {0,1}` realise only `F_Q ⊊ K` — which E.66/E.68
re-fire numerically); `EFF.T2.10` (the T2-side fullness criteria).

**⚠ THE COSET CORRECTION AND THE TWO RIDERS (transcribed at exactly source strength).** The
REALIZED-SET display this arithmetic feeds was corrected twice: (a) the ϖ-read realized set is
the COSET `η_θ^{−q(k)}·{Σ_{t∈T(k)} c_t·η_θ^t : c_t ∈ F_Q, not all 0}` (dated correction from
HE6 PE2 F-1 — the external unit factor; "Both boundary clauses are twist-invariant"); (b) the
set inside the braces is "the nonzero elements of a proper F_Q-linear subspace (a punctured
proper subspace)", NOT a subgroup-coset (ANNEX R R5's rider; the two riders "point in opposite
directions on the same phrase" and are BOTH true of different objects — HE7's OPEN-CALL 2,
recorded in §13/§14, wording only, no mathematics). E's Lean object is (a)+(b) composed:
`realizedSet = (fixed unit) • {seamSum γ η : γ supported on T(k), γ ≠ 0}` — E.32's statement.
The sub-threshold clause is exercised by NO sealed tooth at `q(k) ≠ 0` (the disclosed
limitation of Q3's frames); E.66's gate adds a `q(k) ≠ 0` numeric witness.

**TEETH.** Q3 / HE7-LIFT1 (five level-1 frames, exhaustive reachable-height tables) +
HE7-T-LIFT2SHARP → **Lean theorem** (this arithmetic); E.68 re-fires the tables.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.31 [theorem] [fresh]

**STATEMENT.** *The twisted lift at a rung (R1-c schema; `(LIFT₂)` is its `ϑ ≡ 1` instance).*
Let `C` be the level-`i` carrier, `R` the rung, `K'` the next field (`[K':K] = g` via `η` as in
E.29), and `k, m₀, s₀` with `ℓm₀ + s₀u = k`, `s₀ < ℓ`, and the per-height threshold
`(g − 1)*u + b ≤ m₀` where every height `≥ b` is `C.Full` (the level-`i` fullness supply).
Then for every `c ∈ K'` written `c = seamSum γ η` (the K-basis expansion, `γ : Fin g → K`) with
`c ≠ 0`, and every twist vector `ϑ : Fin g → K` (all nonzero), there is a slot family
`C_t := lift of γ_t * ϑ_t⁻¹` at height `m_t = m₀ − t*u` (E.10's `hlift`, legal since
`m_t ≥ b` by the threshold — E.08's arithmetic), whose assembled development has twisted slot
read exactly `(k, c)` by E.29 — "the residue is `Σ_t (γ_tϑ_t^{−1})·ϑ_t·β_i^t = c`"
(`EFF.HE7.111`). The k-uniform form: `R.nextBound b ≤ k` suffices (E.08).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem twisted_lift {O : Type*} [CommRing O] {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    {b : ℕ} (hfull : ∀ m : ℕ, b ≤ m → C.Full m)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hthr : (R.g - 1) * R.u + b ≤ m₀)
    (γ ϑ : Fin R.g → K) (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    ∃ c : ℕ → Polynomial O,
      (∀ s, R.slotCount ≤ s → c s = 0) ∧ (∀ s, (c s).natDegree < C.D) ∧
      (∀ t : Fin R.g, γ t ≠ 0 →
        C.hgt (c (s₀ + R.ℓ * t)) = ((m₀ - (t : ℕ) * R.u : ℕ) : WithTop ℤ) ∧
        C.dig (c (s₀ + R.ℓ * t)) = γ t * (ϑ t)⁻¹) ∧
      (∀ t : Fin R.g, γ t = 0 → c (s₀ + R.ℓ * t) = 0)
```

**DEPENDS.** E.08, E.10 (`hlift`), E.28, E.29 (the readout), E.30 (the fullness supply shape).

**PROOF.**
1. Per `t` with `γ t ≠ 0`: `m_t := m₀ − t*u ≥ m₀ − (g−1)u ≥ b` (from `hthr`, E.08's step), so
   `C.Full m_t` (`hfull`); `hlift` at digit `γ t * (ϑ t)⁻¹ ≠ 0` supplies `c (s₀ + ℓt)`.
2. Set every other slot to 0. Conclusion clauses are the construction's contract; the E.29
   readout (`res = Σ (γϑ⁻¹)·ϑ·η^t = seamSum γ η = c`) is the consumer's next move, stated
   there.

**SIZE.** 30 lines.

**SOURCE.** `EFF.HE7.111` (ANNEX-THEOREM R1-c, statement + proof verbatim: "§S4.2 one level up,
with ONE pre-twist line added … invoke (LIFT_{i−1}) at level-i height `m_t := m₀ − tu_i` … for
the residue **γ_t·ϑ_t^{−1} ∈ K_i^×** — the INVERSE twist … The bound recursion is unchanged —
values never see the twist"); `EFF.HE7.12` ((LIFT₂), the `ϑ ≡ 1` instance, statement + proof);
`EFF.HE7.27` (DEFINITION HE7-3's inverse-twisted prescription — the mechanism's first
appearance, "machine-load-bearing per tooth HE7-T-BADTWIST").

**TEETH.** HE7-T-BADTWIST (21 reads change when the twist is dropped; twisted read == PARI
480/480) + `he7rannex_supp.py` K2R (R1-c's mechanism used constructively, 15 members) → **Lean
theorem**; Q3 (ten frames) evidences the thresholds (E.68).

**ENVIRONMENT.** ENV-E2 + ENV-E3.

---

### NODE E.32 [lemma] [fresh]

**STATEMENT.** *The realized set at a height (corrected, punctured-subspace-coset form).* In
ENV-E3 with `η` as in E.27 and a fixed unit `w : K'ˣ` (the external twist `η_θ^{−q(k)}` — a
DATUM here; its value is instance content): the set of realizable residues at a height with
reach set `T ⊆ Fin f₁` is
`{w • seamSum γ η : γ : Fin f₁ → F, (∀ t ∉ T, γ t = 0), γ ≠ 0}` — the `w`-translate of the
nonzero elements of the `F`-span of `{η^t : t ∈ T}`:
(i) this set equals `w • (span puncture)` — a PUNCTURED PROPER SUBSPACE translate when
`T ≠ univ` (R5's rider wording), all of `K'^×`'s… precisely `w • (K'∖{0}) = K' ∖ {0}` when
`T = univ` ("at full T(k) the coset is still ALL of K^×");
(ii) when `T = univ` the set is `K' \ {0}` exactly (basis spans; `w`-translate of everything
nonzero is everything nonzero).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

def realizedSet {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    {f₁ : ℕ} (η : K') (w : K'ˣ) (T : Finset (Fin f₁)) : Set K' :=
  { x | ∃ γ : Fin f₁ → F, (∀ t ∉ T, γ t = 0) ∧ (∃ t, γ t ≠ 0) ∧
        x = (w : K') * seamSum γ η }

theorem realizedSet_full {F K' : Type*} [Field F] [Field K'] [Algebra F K'] {f₁ : ℕ}
    {η : K'} (hgen : (minpoly F η).natDegree = Module.finrank F K')
    (hint : IsIntegral F η) (hf : f₁ = Module.finrank F K') (w : K'ˣ) :
    realizedSet (F := F) η w Finset.univ = {x : K' | x ≠ 0}
```

**DEPENDS.** E.26, E.27 · mathlib `PowerBasis` span (`Algebra.adjoin.powerBasis`) or the
H.53-route (`minpoly` degree + `Basis.mk`).

**PROOF.**
1. `⊆`: a nonzero `γ` gives `seamSum γ η ≠ 0` (E.27 at `ϑ ≡ 1`), and `w` is a unit.
2. `⊇`: `{η^t}` spans (`minpoly` degree = finrank makes the power family a basis — the H.53
   route B object); expand `w⁻¹ * x` in the basis; nonzero `x` gives a nonzero coordinate
   vector.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HE7.19` (the frozen realized-set display + the dated EFFECTIVE READING:
"`η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ))`, realized set = `η_θ^{−q(k)} · {Σ_{t∈T(k)} c_t·η_θ^t :
c_t ∈ F_Q, not all 0}`"); `EFF.HE7.22` (sharpness + ANNEX R R5's rider: "read 'a proper
subgroup-coset of K₂' as 'the nonzero elements of a proper F_Q-linear subspace (a punctured
proper subspace)'" — the Lean object above IS the composed corrected form, discharging the
OPEN-CALL 2 wording question at the formal level: both riders are literally true of this
object, `w` the coset half, the braces the subspace half); `EFF.T2.50` (the `(Q-DEF)`
reconciliation directive: "the two agree on q(k) with no sign convention left free").

**TEETH.** HE7-T-LIFT2SHARP (exact sets by enumeration, ten frames; "every k above the
closed-form threshold IS surjective, and some k below it is NOT") → **Lean theorem** for the
full case; the sub-threshold proper case is E.30(iii)+(i) with this node's set; E.66/E.68 add
the `q(k) ≠ 0` numeric witness the sealed teeth lacked (`EFF.HE7.19`'s disclosed limitation).

**ENVIRONMENT.** ENV-E3.

---

### NODE E.33 [lemma] [fresh]

**STATEMENT.** *Twist-unit telescoping (R1-a(iii)'s exponent engine) and the `q(k)` wrap.*
(i) For any commutative group `G` and `n : ℤ → G`: defining `τ(a,b) := n(a)·n(b)·(n(a+b))⁻¹`,
the telescoping identity holds: for `θ_t := n(m₀ − t*u) * n(u)^t * (n(m₀))⁻¹`,
`θ_t = Π_{j<t} τ(m₀ − (j+1)*u, u)` — "each factor is `n_i(m₀−(j+1)u_i)n_i(u_i)/n_i(m₀−ju_i)`;
the product collapses" (`EFF.HE7.110` Step 3).
(ii) If `n` is a homomorphism (`n(a+b) = n(a)n(b)`), then `τ ≡ 1` and every `θ_t = 1` — the
level-1 degeneration ("τ₁ ≡ 1 because `k ↦ ϖ^k` is a homomorphism — THE point of the re-based
system", `EFF.HE7.108`(ii); "At i = 1 every θ_t = 1 (ϖ-powers multiply)").
(iii) The `(COC)` identity: `τ(a,b)·τ(a+b,c) = τ(b,c)·τ(a,b+c)` — four-factor cancellation
(`EFF.T2.07`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

def coc {G : Type*} [CommGroup G] (n : ℤ → G) (a b : ℤ) : G :=
  n a * n b * (n (a + b))⁻¹

theorem coc_cocycle {G : Type*} [CommGroup G] (n : ℤ → G) (a b c : ℤ) :
    coc n a b * coc n (a + b) c = coc n b c * coc n a (b + c)

theorem theta_telescope {G : Type*} [CommGroup G] (n : ℤ → G) (m₀ u : ℤ) (t : ℕ) :
    n (m₀ - t * u) * (n u) ^ t * (n m₀)⁻¹
      = ∏ j ∈ Finset.range t, coc n (m₀ - (j + 1) * u) u

theorem coc_of_hom {G : Type*} [CommGroup G] (n : ℤ → G)
    (hn : ∀ a b, n (a + b) = n a * n b) (a b : ℤ) : coc n a b = 1
```

**DEPENDS.** E.04 (the `{0,1}` exponent law pairs with this at instances) · mathlib
`Finset.prod_range_succ`, `CommGroup` simp set.

**PROOF.**
1. `coc_cocycle`: unfold; both sides equal `n a · n b · n c · (n (a+b+c))⁻¹` after
   associativity/cancellation (`group` tactic; mind `(a+b)+c = a+(b+c)` rewrites).
2. `theta_telescope`: induction on `t`; the `j = t` factor is
   `n(m₀−(t+1)u)·n(u)·(n(m₀−tu))⁻¹`; product telescopes (`Finset.prod_range_succ`), `group`.
3. `coc_of_hom`: unfold, rewrite, cancel.

**SIZE.** 22 lines.

**SOURCE.** `EFF.T2.07` (`(COC-DEF)`/`(COC)` boxed; the four-factor cancellation derivation);
`EFF.HE7.110` (Step 3's telescoping, verbatim); `EFF.HE7.108` (R1-a(ii)'s `τ₁ ≡ 1` +
(R1.1)'s recursion — whose EXPONENT content is E.04; the letter-monomial RESIDUE value
`res(τ_i(a,b)(ξ)) = ι(Π β_j^{e_j})` is carrier content, instance-supplied); `EFF.T2.08`
(`(THETA-EVAL)`, `Θ_s = ϑ_s^{−1}`, `(BETA)` `τ(k,k′) = β^c` — "It is not replaced by 1. At
deeper levels the same construction gives a monomial in all preceding residual letters").

**⚠ GC-14 (the ϑ ORIENTATION).** The letters `ϑ_s`/`Θ_s` here obey `EFF.T2.08`'s
`Θ_s = ϑ_s^{−1}` and `(THETA-EVAL)`'s direction. The FOUR-WAY orientation reconciliation
(GENTOW2's ϑ vs T1's Θ vs T3's ϑ_{G2} vs GENTOW5's reciprocal ϑ_t) is chapter D's canonical
table (GC-14); every chapter-E consumer cites that table by anchor — `EFF.GENTOW2 orientation
records [supplied-by: chapter D, the GC-14 table]` — and NO chapter-E node adjudicates or
restates the correspondence (honesty E-5). This node's `coc`/`θ_t` are T2/HE7-internal letters,
used only through the displays quoted above.

**TEETH.** `he7rannex_supp.py` (the exponent-vector value identity on every computed
`n₃`-monomial) → **Lean theorem** for the exponent/group half; the residue evaluation stays
instance content.

**ENVIRONMENT.** ENV-E1 (abstract group).

---

### NODE E.34 [lemma] [fresh]

**STATEMENT.** *`(IDX-TWIST)`'s bijection layer (the print/coherent relabelling is lossless).*
In a field `K`: for a fixed unit `w : Kˣ`, the map `x ↦ w * x` is a bijection of `K` fixing `0`
and restricts to a bijection of `K \ {0}` onto itself; consequently, for any subset
`S ⊆ K \ {0}` closed under the relabelling's index translation (the family's labels run over
`K^×`, the master's digits over `K` with `0` the empty recentering), the relabelled family
covers every element "member for member; what it does not do is match them at equal index
names" (`EFF.T2.70`). Packaged with the two qualifiers as RECORDED READING DIRECTIVES (not Lean
content): equality of polynomials exactly at the COMPATIBLE lift choice, modulo height-`>κ`
increments at an arbitrary permitted one; covering direction at `κ > D′h`, not mere fullness
(`EFF.T2.20`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem unit_mul_bijOn {K : Type*} [Field K] (w : Kˣ) :
    Set.BijOn (fun x : K => (w : K) * x) {x | x ≠ 0} {x | x ≠ 0}

theorem unit_mul_zero {K : Type*} [Field K] (w : Kˣ) : (w : K) * 0 = 0
```

**DEPENDS.** none · mathlib `Units.mulLeft_bijective`, `Set.BijOn`.

**PROOF.**
1. `Units.mulLeft_bijective w` restricted: nonzero maps to nonzero (unit × nonzero ≠ 0),
   surjectivity onto nonzero by `w⁻¹ * y`. Assemble `Set.BijOn`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.T2.70` (the bijection argument, verbatim: "`η^{q(κ)}` is ONE fixed element of
`K^×` … Multiplication by it is a bijection of K fixing 0, and of K^× onto itself. The family's
labels at `(ℓ,d) = (1,1)` run over exactly `K^×` … this master's digits at a full height run
over all of K … with `L_κ(0) = 0` the empty recentering"); `EFF.T2.20` (`(IDX-TWIST)` boxed +
the two qualifiers, transcribed as directives above — they are statements about the INSTANCE's
lift choices, carrier content).

**TEETH.** the print/coherent-frame mutant (its cure is exactly this bijection +
E.29's coherent read) → **Lean theorem** for the bijection; the frame conversion itself is
E.22's instance row.

**ENVIRONMENT.** ENV-E3.

---

### NODE E.35 [theorem] [fresh]

**STATEMENT.** *`(REF-HT)`: the refinement height AND digit are forced by `(RISE)` (carrier
form).* Over a slot carrier `C`, let `Φ, Λ : Polynomial O` with `Λ ≠ 0`, `deg Λ < C.D`,
`C.hgt Λ = k`, and suppose the ultrametric rise `C.hgt (Φ_read) …` — schema form: let
`a, b : Polynomial O` play the roles of the class value and the increment, with
`C.hgt a = (λ : ℤ)` and `C.hgt b = (k : ℤ)`. If `(λ : WithTop ℤ) < C.hgt (a - b)` (the rise),
then:
(i) `k = λ` (`(HT)` forced: if `k ≠ λ`, `hgt_add_eq` gives `hgt (a − b) = min(λ, k) ≤ λ`,
contradiction — `EFF.T2.19`'s master implication, verbatim mechanism);
(ii) `C.dig b = C.dig a` (the DIGIT forced: at equal height, `dig (a − b) = dig a − dig b`
whenever `dig a − dig b ≠ 0` would keep the height at `λ` (`dig_add` applied to
`(a − b) = a + (−b)` with `dig (−b) = −dig b` — a small negation lemma is part of this node),
so the rise forces `dig a − dig b = 0` — `EFF.T2.71`'s boxed equivalence, carrier form).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem refht_forced {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)  -- see NOTE
    {a b : Polynomial O} {lam k : ℤ}
    (ha : C.hgt a = (lam : WithTop ℤ)) (hb : C.hgt b = (k : WithTop ℤ))
    (hrise : (lam : WithTop ℤ) < C.hgt (a - b)) :
    k = lam ∧ C.dig b = C.dig a
```

**⚠ SIGNATURE NOTE (the negation law).** `hgt(−A) = hgt A`, `dig(−A) = −dig A` is a carrier
law the corpus uses silently (residues are additive and `d(−x) = d(x)`). It is taken as an
explicit hypothesis here rather than an E.10 field, pending the stub stage: if three or more
consumers thread it, RE-PLAN promotes it to an E.10 field (GC-5's re-plan protocol; a field
addition to E.10 is amendment-level, dated).

**DEPENDS.** E.10 (`hgt_add_eq`, `hgt_add_ge`, `dig_add`).

**PROOF.**
1. (i): if `k ≠ lam`, `hgt_add_eq a (−b)` (heights differ via `hneg`) gives
   `hgt (a − b) = min lam k ≤ lam`, contradicting `hrise`.
2. (ii): now `hgt b = lam`. If `dig a − dig b ≠ 0`: `dig_add a (−b)` gives
   `hgt (a − b) = lam` — contradiction with `hrise`. So `dig a = dig b`.

**SIZE.** 20 lines.

**SOURCE.** `EFF.T2.19` (`(REF-HT)` boxed; the derivation: "If `k ≠ λ`, the ultrametric
equality yields `d(Φ − L_k(s)) = min(λ, k) ≤ λ`, contradicting `(RISE)`; hence `(HT)`";
"`(RISE)` is a carrier hypothesis, not an open ledger obligation"); `EFF.T2.71` (the boxed
digit equivalence "`d((Φ−Λ)(ρ)) > λ ⟺ ι_ρ(s − dig(Λ)) = 0 ⟺ dig(Λ) = s`" and the two riders —
the `K^×` membership and the lift-freedom immateriality, whose `h(E) < λ` clause is r12 repair
4(d)'s ultrametric step, all reproduced by this carrier-level proof); `EFF.T2.59` (the
`(REF-HT)` derivation record: "(HT) is forced by (RISE), and that forcing uses master data
only").

**⚠ `(RISE)` STAYS STIPULATED.** The hypothesis `hrise` is `(RISE)` — carrier-supplied at
instances (`EFF.T2.19`'s X02/X10–X11/X24 pins → E.22/E.23 rows). This node is the FORCING, not
a discharge of `(RISE)`.

**TEETH.** S7 print/coherent index mutant + lift-choice mutant (`EFF.T2.19`) → **Lean
theorem**: the digit clause makes the coherent-frame read the only one that can elaborate
(the print label `s·η^{−q}` does not satisfy (ii) unless `q = 0` — the mutant's signature).

**ENVIRONMENT.** ENV-E2.

---

### NODE E.36 [theorem] [fresh]

**STATEMENT.** *The gcd dichotomy (ANNEX-LEMMA R2-a, schema form).* Let `F, Ψ : Polynomial O`
be monic, `Ψ` of degree `D″ > 0`, and suppose the FORCING datum: every monic divisor
`g₀ ∣ gcd`-candidate — schema form: suppose given `hforce : ∀ g₀ : Polynomial O, g₀.Monic →
g₀ ∣ F → g₀ ∣ Ψ → g₀.natDegree ≠ 0 → D″ ≤ g₀.natDegree` (the instance content: a common root
is a level-2 point whose full Galois orbit sits inside `g₀`, forcing `deg g₀ ≥ [L_ξ:K₀] ≥ D″` —
carrier-supplied, C placeholder). Then any monic common divisor of `F` and `Ψ` of positive
degree equals `Ψ` (degree squeeze: `D″ ≤ deg g₀ ≤ deg Ψ = D″`, both monic), i.e.
`gcd(F, Ψ) ∈ {1, Ψ}` in the associate-free monic reading; consequently
`Ψ ∤ F → IsCoprime (F.map …) (Ψ.map …)` over the fraction field — "the CONVENTION's chain,
closed" (`EFF.HE7.119`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem gcd_dichotomy {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree ≠ 0 → D ≤ g₀.natDegree) :
    ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree = 0 ∨ g₀ = Ψ

theorem coprime_of_not_dvd {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hforce : ∀ g₀ : Polynomial O, g₀.Monic → g₀ ∣ F → g₀ ∣ Ψ →
      g₀.natDegree ≠ 0 → D ≤ g₀.natDegree)
    (hndvd : ¬ Ψ ∣ F) :
    IsCoprime (F.map (algebraMap O (FractionRing O)))
      (Ψ.map (algebraMap O (FractionRing O)))
```

**DEPENDS.** E.11 (the coprimality spelling) · mathlib `Polynomial.eq_of_monic_of_dvd`
(degree-equal monic divisors are equal: `Polynomial.eq_of_monic_of_associated` +
`Polynomial.natDegree_le_of_dvd`), fraction-field gcd (`EuclideanDomain.gcd_isUnit_iff`).

**PROOF.**
1. Dichotomy: `g₀ ∣ Ψ` gives `deg g₀ ≤ D` (`natDegree_le_of_dvd`, `Ψ ≠ 0`); at positive degree
   `hforce` gives `deg g₀ = D`; monic divisor of equal degree ⟹ `g₀ = Ψ`
   (associated + both monic).
2. Coprimality: over `FractionRing O` take the monic gcd `g`; pull its monic O-lift back
   (Gauss/primitive — or argue directly: a nontrivial common factor over the fraction field
   yields, by clearing denominators and primitivity of monic polynomials, a monic common
   O-divisor of positive degree — landed `Uniformity.Hensel` has `monic_factorization_unique`
   machinery; search first per the workflow ladder), then the dichotomy + `hndvd` forces
   degree 0, i.e. coprime.

**SIZE.** 34 lines. **SPLIT CANDIDATE:** the fraction-field descent as `E36a` (it is the one
genuinely mathlib-dependent step; if the descent fights, the fallback contract is to state
`coprime_of_not_dvd` with the O-level conclusion `∀ g₀, Monic → dvd → dvd → natDegree = 0` and
let E.37 consume that form — a DECISION at the stub stage, flagged).

**SOURCE.** `EFF.HE7.119` (ANNEX-LEMMA R2-a, statement + proof verbatim, incl. "a proper
common factor would be a Galois-stable factor of Ψ of degree ≥ deg Ψ" and the chain
"gcd = 1 ⟺ no common root in K̄₀ ⟺ Ψ(ρ) ≠ 0 … ⟺ dv₂(Ψ(ρ)) < ∞"; hypothesis set "deliberately
wide … covering both f_S and every block factor"); `EFF.HE7.09` (the convention whose
equivalence chain this licenses — "Codex graded this a GAP as stated" pre-annex, closed by
R2-a).

**TEETH.** **PROOF-ONLY** at source ("The scenario it excludes is one the battery's frame
cannot produce") → becomes a **Lean theorem** here — the chapter's clearest net upgrade of a
proof-only unit to machine-checked.

**ENVIRONMENT.** ENV-E2 (+ `[IsDomain O]`).

---

### NODE E.37 [theorem] [fresh]

**STATEMENT.** *The standing-convention peel (`Ψ ∤ f_S` restriction-free reading; the peel
fires at most once).* Let `F, Ψ` be as in E.36 with `F` squarefree over the fraction field and
`D″ ∣ deg F` bookkeeping. If `Ψ ∣ F` then: (i) `F = Ψ * F′` with `F′` monic,
`deg F′ = deg F − D″`, and `Ψ ∤ F′` (else `Ψ² ∣ F`, contradicting squarefreeness — "the peel
happens at most once", `EFF.HE7.09`); (ii) `F′` and `Ψ` coprime (E.18's squarefree-coprime
step); (iii) if `Ψ ∤ F`, E.36's chain applies directly. Together: the convention
"`Ψ ∤ f_S`" is NOT a restriction — every input is decided either directly or after ONE peel
with mass `μ₂ − 1` (`EFF.HE7.09`'s italic clause, transcribed at the identity level; Ψ's
IRREDUCIBILITY and its `(e,f) = (e₁ℓ, f₁d_r)` on the peel stratum are LEMMA HE6R1-3's — a
CONCLUSION there, never an assumption here, and its supplier is a C placeholder:
`EFF.HE6R1 [supplied-by: chapter C]`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem peel_once {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O))))
    (hdvd : Ψ ∣ F) :
    ∃ F' : Polynomial O, F = Ψ * F' ∧ F'.Monic ∧
      F'.natDegree = F.natDegree - D ∧ ¬ Ψ ∣ F'
```

**DEPENDS.** E.18 (the peel identity), E.36 · mathlib `Squarefree`, `Polynomial.map_dvd`.

**PROOF.**
1. Factor as in E.18 steps 1–3 (`F′` monic, degree drop `D`).
2. `¬ Ψ ∣ F′`: else `Ψ * Ψ ∣ F`, so `(Ψ.map …)² ∣ F.map …` (map is a ring hom; `Ψ.map` is
   monic hence a nonunit at `D > 0`), contradicting `hsq`.

**SIZE.** 18 lines.

**SOURCE.** `EFF.HE7.09` (the CONVENTION, verbatim incl. "the peel happens at most once" and
the necessity derivation: without it "P₂ loses its j = 0 pin and THEOREM HE7.A(1)'s
`Σ L_{λ₂} = μ₂` is false"); `EFF.HE7.60` (the n = 8 peel row: `μ₂′ = 1` after one peel, 8/8
machine members, `A₁^{(2)} ≠ 0` "one peel only"); `EFF.HE7.62` (HE7.A′: "on the peel stratum
irreducibility of Ψ is a CONCLUSION, not an assumption").

**TEETH.** the sealed `DEGENERATE-key-divides` stratum (8 of 1,587, found BY the machine) +
`he7r1_supp.py` A1–A5 (8/8 peels exact, 2/2 PARI on both σ halves) → the identity layer is a
**Lean theorem**; the letter claim (`σ(Ψ) = {(4,1)}`) rides E.51's dictionary row with the
HE6R1-3 placeholder.

**ENVIRONMENT.** ENV-E2 (+ `[IsDomain O]`).

---

### NODE E.38 [theorem] [fresh]

**STATEMENT.** *Slot domination (LEMMA HE7-12, the schema-ownable clauses).* Three layers:
(i) **the fold (d)**: for slot families `w₁, …, w_j` each of degree `< D″` and slot value
`> T₂`, the sum `W = Σ w_i` has degree `< D″` and slot value `≥ min_i dv₂(w_i) > T₂` — "the
slot-min is ultrametric slotwise" — with EXACTNESS and `W ≠ 0` when the values are pairwise
distinct (ultrametric equality at a uniquely attained min; carrier form via E.10's
`hgt_add_eq`);
(ii) **the off-disk arithmetic of (a)**: the displayed bound
`(ν − T₂) + ε₁ − ℓ(D′−1)ε₀ > 0` under the three-case split (`ε₀ > 0` ⟹ substitute
`ε₁ = ℓ(λ − D′h) + ℓD′ε₀`; `ε₀ = 0 < ε₁`; `ε₀ = ε₁ = 0`) — pure ℕ/ℤ arithmetic given the
case data (`EFF.HE7.44`(a)'s positivity computation, transcribed as an arithmetic lemma);
(iii) **the package transport (c)**: recorded as an OBLIGATION DEF `TransportsTo` — the
Prop that a rung interface at key `Ψ` yields one at `Ψ − w` with the same
`(λ, r, dv₂, n₂, K₂, T₂)` — whose eleven-item discharge audit (`EFF.HE7.44`(c) items (1)–(11),
as COMPLETED by ANNEX R R4: clause (a) also consumes LEMMA HE6-4 and HE6-2′; clause (b) also
(LIFT₂), the test family, HE7-9(a), HE7.A(1)) is the INSTANCES' obligation (E.23 rows; C
placeholders for the HE6-side lemmas). E does not re-prove the audit; it fixes the transported
statement's SHAPE.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem slot_fold {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) {T : ℤ} (ws : List (Polynomial O)) (hne : ws ≠ [])
    (hdeg : ∀ w ∈ ws, w.natDegree < C.D)
    (hval : ∀ w ∈ ws, ∃ v : ℤ, C.hgt w = (v : WithTop ℤ) ∧ T < v)
    (hdist : ws.Pairwise fun w w' => C.hgt w ≠ C.hgt w') :
    ws.sum ≠ 0 ∧ (∃ v : ℤ, C.hgt ws.sum = (v : WithTop ℤ) ∧ T < v) ∧
      C.hgt ws.sum = (ws.map C.hgt).foldr min ⊤

theorem offdisk_positivity {ν T₂ ℓ D' h lam ε₀ ε₁ : ℤ}
    (hν : T₂ < ν) (hλ : D' * h < lam) (hℓ : 1 ≤ ℓ) (hD : 1 ≤ D')
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hcase : (0 < ε₀ ∧ ε₁ = ℓ * (lam - D' * h) + ℓ * D' * ε₀) ∨ ε₀ = 0) :
    0 < (ν - T₂) + ε₁ - ℓ * (D' - 1) * ε₀
```

**DEPENDS.** E.10 (`hgt_add_eq`, `hgt_add_ge`), E.28 (distinct-height uniqueness pattern) ·
mathlib `List.Pairwise`, `WithTop.min`.

**PROOF.**
1. `slot_fold`: induction on `ws`; at each step the partial sum's height differs from the next
   summand's (pairwise distinct + the fold min), so `hgt_add_eq` gives exact min; the min of
   values `> T` is `> T`; a finite-height element is nonzero (`hgt_zero`: `hgt 0 = ⊤`).
2. `offdisk_positivity`: case split per `hcase`; in the `ε₀ > 0` branch substitute and
   simplify to `(ν−T₂) + ℓ(λ−D′h) + ℓε₀ > 0` (each summand `≥ 0`, first `> 0`); in `ε₀ = 0`
   branches it is `(ν−T₂) + ε₁ > 0`. `linarith`/`nlinarith` on the products.

**SIZE.** 30 lines. **SPLIT-MANDATED:** `slot_fold` and `offdisk_positivity` as two files
(`E38`, `E38a`) — independent consumers (E.42 needs the fold; E.23's HE7-12(a) row needs the
arithmetic).

**SOURCE.** `EFF.HE7.44` (LEMMA HE7-12, clauses (a)/(b)/(d) verbatim incl. the `[r3]` `W ≠ 0`
rider — "the values `dv₂(w_i)` are pairwise DISTINCT (they are the strictly increasing slopes
… of LEMMA HE7-13 …), so the slot-min is attained by the least-slope increment ALONE and
`dv₂(W) = min_i dv₂(w_i) < ∞ EXACTLY`"; clause (c)'s eleven-item audit; the (a)-proof's
three-case positivity computation); `EFF.HE7.43` (the slot-domination mechanism: key slots AT
`T₂`, increment slots strictly above); ANNEX R R4 (`EFF.HE7.44` CONDITIONALITY (a): the
completed inventory — "citation-completeness on one sentence, no transfer breaks").

**⚠ THE HE7-12/HE7-13 MUTUAL INDUCTION (OPEN-CALL 3 of the HE7 spec) IS RESOLVED
STRUCTURALLY HERE.** The corpus notes the circularity — (d)'s `W ≠ 0` cites HE7-13's strict
increase; HE7-13's proof cites HE7-12(c)(d) — "broken by simultaneous induction along the
chain". In Lean the two become ONE strong induction along the chain length (E.56's statement
quantifies the chain and proves both invariants together), so no axiom-level circularity can
survive elaboration; `slot_fold` above takes the pairwise-distinctness as an explicit
HYPOTHESIS, discharged by E.56 at each chain step. Recorded in §14 for the cross-read.

**TEETH.** `he7r2_supp.py` B1 (slot geometry, 42/42) + B2 (the off-disk inequality in
resultant-sum form, 210/210, with the `[r3]` vacuity disclosure: the `δ = ∞` half vacuous on
41/42 — recorded in §13) → **Lean theorem** for (i)/(ii); (iii) is an obligation def.

**ENVIRONMENT.** ENV-E2 / ENV-E1 (the arithmetic clause).

---

## 6. §6 — `(LB1)` AND `(MP1)`: THE TWO OPEN OBLIGATIONS, ADJUDICATED PER BRIEF E

> **The adjudication (BRIEF E product clause (2), executed).** T2's merged spec carries exactly
> two open mathematical obligations, `(LB1)` (`EFF.T2.18`) and `(MP1)` (`EFF.T2.23`), "both
> reaffirmed at the governing block"; its §9 self-audit distinguishes them from the two carrier
> hypotheses that fence nothing (`(SEC-RANK)`, `(RISE)`) and confirms `(MP1′)` "is never stated
> as an effective conditionality anywhere in the merged text". **No discharge of `(LB1)` or
> `(MP1)` exists in T2's effective text** — `EFF.T2.18`: "The note enumerates the HE3/HE6 pins
> and expressly says NONE proves `(LB1)`"; `EFF.T2.23`: "No pin proves the recentered level-one
> key's orbit/(e,f) item, so `(MP1)` remains open". **Disposition: both are NAMED CAPSTONE
> HYPOTHESES, carried to chapter I** — and under the Part V owner ruling each must terminate
> there as a discharge node or a literature cite through gate (b); E's job is to state them at
> exactly source strength, no wider and no narrower.

### NODE E.39 [def] [fresh]

**STATEMENT.** *`(LB1)` — the level-one block-construction obligation, at exactly
`EFF.T2.18`'s strength.* The assertion that every level-one state whose clause-4 processing
demands blocks — every state with at least two sides, and every side whose residual is mixed —
has the monic side and label blocks of S1.7A: "with their own full developments, single-side
hulls, pure residuals, product identities, disjoint exhaustive root partitions, and inherited
continuation data." Schema form: for the level-one carrier/block/interface, the existence of a
block family realizing `(SIDE-PROD)`/`(LABEL-PROD)`/`(LABEL-DEV)`/`(LABEL-PURE)`/`(LABEL-OWN)`
(`EFF.T2.17`'s displays) — i.e. for each side `p` and factor `q`, a `BlockData` with its own
`RungInterface` whose weight (degree) is `classCount`-compatible and whose product is `F`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- `(LB1)` (`EFF.T2.18`): the level-one clause-4 block suite exists. OPEN — a named
capstone hypothesis; no chapter-E node proves it; chapter I carries it (Part V gate (b) or
a discharge node). -/
def LB1Carrier {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  ∀ I : RungInterface C B,
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    ∃ blocks : List (Σ B' : BlockData C, RungInterface C B'),
      B.F = (blocks.map fun x => x.1.F).prod ∧
      (blocks.map fun x => x.1.F.natDegree).sum = B.F.natDegree
      -- + the per-block pure-residual and length clauses; see the NOTE
```

**⚠ SIGNATURE NOTE.** The displayed conjunction abbreviates the full S1.7A clause list
(`(LABEL-PURE)`: each block's shadow has ONE factor with `k = L_C/(ℓ·deg r)`; `(LABEL-OWN)`
integrality; the partition compatibility with `classCount`). The stub stage elaborates the
full record as a `structure BlockSuite` with one field per display — the point FROZEN here is
the obligation's SHAPE (existence of interfaced blocks multiplying to `F`) and its TRIGGER
(multi-side or mixed — never a one-side separable state: `EFF.T2.18`'s "Clauses 1 and 2 are
not" scoping, already honoured at E.16/E.17).

**DEPENDS.** E.10–E.12, E.17. **PROOF.** definitional (a `Prop`). **SIZE.** 24 lines.

**SOURCE.** `EFF.T2.18` (boxed `(LB1)`, the enumeration sentence, the scoping paragraph
verbatim: "Two level-one routes remain conditional, each where it is taken: the clause-4 route
on `(LB1)`, and the clause-5 peel at a recentered key on `(MP1)` … No level-one route is
asserted unconditional simpliciter"); `EFF.T2.17` (the S1.7A displays the blocks must
satisfy); ledger Display A (the `(LB1)` conjunct).

**TEETH.** S7 mixed-residual and multi-side hostile cases → **signed non-applicability at
level one** (the corpus's own disposition — the obligation is open); at level ≥ 2 the analogue
is PROVED content (ANNEX-LEMMA HE7-13′ = E.57), which is why the carrier is level-indexed by
its instantiation, not globally.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.40 [def] [fresh]

**STATEMENT.** *`(MP1)` — the level-one recentered-key peel obligation, at exactly
`EFF.T2.23`'s strength.* The assertion that, at every level-one state whose current key is a
RECENTERED key dividing its represented block, the quotient `G′` satisfies `(WINDOW)`, carries
its own full development with `(ACCOUNT)` and the S1.7 test assertions together with the
occupied-height, lift, frame, origin and residual-degree data, and that the peeled recentered
key admits a certified orbit/`(e,f)` decomposition — "items 2, 3, 4 and 5 of the suite."
Schema form: after E.18's peel identity at a recentered key `Φ″`, the existence of a
`RungInterface` for the quotient block AND the peeled key's emission data.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- `(MP1)` (`EFF.T2.23`): the level-one mid-chain-peel input suite at a RECENTERED key.
OPEN — a named capstone hypothesis; carried to chapter I. The ORIGINAL-key peel is NOT
this obligation (it is supplied by HE6-PEEL-CONVENTION, a chapter-C row at E.22). -/
def MP1Carrier {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  ∀ (Λ : Polynomial O),                        -- the recentering increment
    Λ ≠ 0 → Λ.natDegree < C.D →
    ∀ (B' : BlockData C),                      -- the quotient block at key Φ − Λ
      B'.Φ = B.Φ - Λ → B'.Φ ∣ B.F →
      Nonempty (RungInterface C B') ∧
      -- item 5: the peeled key's certified (e,f) emission
      ∃ e f : ℕ, e * f = C.D ∧ C.eC ∣ e ∧ C.fC ∣ f
```

**⚠ SIGNATURE NOTE.** Item 5's emission clause is stated in the numerical shadow (D-E2); the
"certified orbit decomposition" at instances requires `Φ″` irreducible — "asserted nowhere and
the stated reason r4 declined HE6-PEEL-CONVENTION for that case" (`EFF.T2.61`). The stub stage
may strengthen the emission record to a full `FactorizationType` emission per §7's dictionary;
that strengthening is amendment-level (it touches a Display-A conjunct's statement — owner
gate).

**DEPENDS.** E.10–E.12, E.18. **PROOF.** definitional. **SIZE.** 22 lines.

**SOURCE.** `EFF.T2.23` (boxed `(MP1)` + the quoted suite enumeration, verbatim above; the
derivation's closing: "No pin proves the recentered level-one key's orbit/(e,f) item, so
`(MP1)` remains open"); `EFF.T2.61` (what the S1.8C discharge does NOT give: "It does not
touch `(MP1)`. Peeling a recentered level-one key still needs item 5 …"); ledger Display A
(the `(MP1)` conjunct).

**TEETH.** S7 reducible/recentered-key boundary attacks → **signed non-applicability**
(open obligation, the corpus's own disposition); the LEVEL-TWO analogue is discharged (E.42).

**ENVIRONMENT.** ENV-E2.

---

### NODE E.41 [lemma] [fresh]

**STATEMENT.** *The scope theorem: clauses 1–2 fire without `(LB1)`.* Instantiation check, as
a theorem: E.16 (`he7a_clause12`) consumes NO `LB1Carrier` and no `MP1Carrier` — stated
positively: for every `C, B, I`, the clause-(1)(2) conclusions hold with no block-suite
hypothesis; in particular at a ONE-side state with separable shadow, the full read is decided
by E.16 + E.17's terminal case alone. This machine-checks `EFF.T2.18`'s scoping sentence
("Clauses 1 and 2 are not [conditional]: their proofs run on the unsplit hull of F itself") —
in Lean the check is definitional (E.16's signature does not mention E.39/E.40), so this node
is a REGRESSION-shaped theorem: the one-side separable read produces its emissions with
hypotheses drawn from `RungInterface` alone.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem clause12_lb1_free {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    (hone : I.sides.card = 1) (hsep : ∀ p ∈ I.sides, I.SepSide p) :
    ∀ p ∈ I.sides, (∀ q ∈ I.linFac p, I.classCount p q = C.D * p.2) ∧
      (∀ q ∈ I.hiFac p, I.classCountHi p q = C.D * p.2 * q.1)
```

**DEPENDS.** E.16.

**PROOF.** 1. Direct application of E.16 clause (2) at the (unique) side. The card-one and
all-separable hypotheses document the unconditional perimeter; they are not needed by the
application — which IS the point, and the node's comment states it.

**SIZE.** 10 lines.

**SOURCE.** `EFF.T2.18` (the scoping paragraph); `EFF.T2.33`/`.34` CONDITIONALITY (the
level-one fences attach to clause-4/clause-5 routes only).

**TEETH.** signed source non-applicability at level one (`EFF.T2.18` TEETH) → upgraded to a
**Lean theorem** documenting the unconditional perimeter.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.42 [theorem] [fresh]

**STATEMENT.** *The level-two discharge S1.8B (the composed-key entry, `w = 0 ∨ dv₂(w) > T₂`,
folded by HE7-12(d)).* Schema form over E.38's fold: let the chain base be `Ψ − w` with either
`w = 0` (the base IS a DEFINITION-HE6-1-shape key; the package applies literally) or `w ≠ 0`
with `deg w < D″`, slot value `> T₂`; and let refine increments `w₁, …, w_j` each have degree
`< D″` and slot values `> T₂` pairwise distinct (supplied inductively by `(REF-HT)` = E.35 and
HE7-13 = E.56). Then `Φ₂ − W = Ψ − (w + w₁ + ⋯ + w_j)` is covered by ONE instance of the
slot-domination transport (E.38's fold gives `W' := w + Σ w_i` nonzero of slot value `> T₂`),
so the whole §S5 package at `Ψ` transports once — "the chain is read at `Ψ_{κ₂, r̃}`, a
DEFINITION HE6-1 key, and not at `Φ₂`" (`EFF.T2.62`). Items 2–5 of the `(MID-PEEL)` suite at
the level-two state follow from the transported package — the level-two clause-5 discharge
(`EFF.T2.24`), leaving `(MP1)` scoped to level one ONLY.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem s18b_fold {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) {T : ℤ}
    (w : Polynomial O) (ws : List (Polynomial O))
    (hw : w = 0 ∨ (w.natDegree < C.D ∧ ∃ v : ℤ, C.hgt w = (v : WithTop ℤ) ∧ T < v))
    (hws : ∀ x ∈ ws, x.natDegree < C.D ∧ ∃ v : ℤ, C.hgt x = (v : WithTop ℤ) ∧ T < v)
    (hdist : (w :: ws).Pairwise fun a b => a = 0 ∨ b = 0 ∨ C.hgt a ≠ C.hgt b) :
    (w + ws.sum = 0 ∧ ws = [] ∧ w = 0) ∨
    ((w + ws.sum).natDegree < C.D ∧
      ∃ v : ℤ, C.hgt (w + ws.sum) = (v : WithTop ℤ) ∧ T < v)
```

**DEPENDS.** E.38 (`slot_fold`), E.35 (the increments' heights at instances), E.56 (the
pairwise-distinctness supply — forward reference, DAG-ordered).

**PROOF.**
1. Case `w = 0, ws = []`: left disjunct.
2. Else: the nonzero members of `w :: ws` form a nonempty list with pairwise-distinct finite
   heights `> T`; `slot_fold` (E.38) gives the sum nonzero with exact min height `> T`; degree
   bound by `Polynomial.natDegree_add_le` iterated (each `< C.D`).

**SIZE.** 20 lines.

**SOURCE.** `EFF.T2.62` (S1.8B's composed-key scope clause, verbatim: the `w = 0` /
`dv₂(w) > T₂` disjunct, "LEMMA HE7-12(d) folds the whole sum … covered by ONE instance of
clauses (a)–(c) at `Ψ_{κ₂,r̃}` … Step 2 then runs unchanged"); `EFF.T2.24` (S1.8B: "This is a
level-two discharge. The level-one recentered-key peel remains `(MP1)`-conditional");
`EFF.T2.53` (the withdrawn `[r3]`-clause route — the discharge runs through HE7-12(c)'s
transport, NOT through HE7-8's interleaving clause, which "supplies no item of the input
suite"; transcribed so no fleet agent resurrects the withdrawn route); `EFF.HE7.44`(d).

**TEETH.** composed-key transport tooth; the accumulated-degree tooth (r12: the `deg w < D″`
conjunct re-derived master-side after HETOW C-A withdrew the source licence — the degree leg
here is master-side arithmetic, matching) → **Lean theorem**.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.43 [lemma] [fresh]

**STATEMENT.** *The S1.8C content: a recentered level-one key is a test-family member (the
`(ℓ,d) = (1,1)` identification), and the frame does not move.* Two transcribable clauses:
(i) **the membership identity**: at `(ℓ, d) = (1, 1)` the test-family shape
`Ψ = Φ′ + B₀` with `deg B₀ < D′` IS the recentered key `Φ′ − Λ` at `Λ := −B₀` — in Lean, the
trivial-but-load-bearing algebra `Φ - Λ = Φ + (-Λ)` with degree/height bookkeeping
(`h(−B₀) = κ`, `dig(−B₀) = ση^{q(κ)}` — the choice-independent pair, E.34's directives);
(ii) **the frame-stability record**: the items (i)–(v) of the frame "are not 'carried by' Φ″:
nothing about them moves when the key does" — in the schema, the SlotCarrier `C` does not
mention `Φ` at all (E.10's signature), so key-recentering is definitionally frame-preserving.
This machine-checks the adjudication's core structural claim; the parts of S1.8C that consume
HE3/HE6 pin content (the stage-α transport, the HE6-PROOF licence) are instance rows (E.22,
C placeholders) at HE3's grade cap.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem recentered_is_member {O : Type*} [CommRing O] (Φ B₀ : Polynomial O) :
    Φ + B₀ = Φ - (-B₀)

theorem frame_key_free {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (A : Polynomial O) :
    -- the carrier's read of ANY A is independent of any key: definitional; stated as
    -- a rewriting anchor for consumers
    C.hgt A = C.hgt A ∧ C.dig A = C.dig A
```

**⚠ NODE-KIND NOTE.** Clause (ii)'s Lean content is intentionally trivial — the theorem's
VALUE is that it elaborates: the schema's carrier has no key argument, so the corpus's
"(i)–(v) are functions of the stage datum and of nothing else" is enforced by TYPE. The node
exists so §13's disposition table has a Lean anchor for `EFF.T2.25`/`.61`'s adjudication
(the retirement of `(MP1′)`), rather than a prose-only claim. A fleet agent may fold clause
(ii) into a comment + `rfl` lemma; clause (i) is the consumed identity.

**DEPENDS.** E.10, E.34. **PROOF.** 1. `ring` / `rfl`. **SIZE.** 8 lines.

**SOURCE.** `EFF.T2.25` (S1.8C: "`(MP1′)` is retired … `HE3-A-PROOF`, `HE6-SLOT-SEAM`,
`HE6-FAMILY` and `HE6-PROOF` certify it between them"; "What is removed is the extra
frame-level obligation, not the level-one fences"); `EFF.T2.61` (the adjudication, incl. "At
`(ℓ,d) = (1,1)` the member `Ψ_{λ,Z−s} = Φ′ + B₀` IS the recentered key … A recentered
level-one key is not a foreign object to HE6; it is one of HE6's own test polynomials" and
the two reading directives: only the refined sub-block travels; invoked at the product-1
branch and nowhere else); `EFF.T2.70` (the print/coherent seam and `(IDX-TWIST)`'s role).

**TEETH.** level-one frame-transport hostile tooth → the type-level enforcement above +
E.22's instance rows.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.44 [def] [fresh]

**STATEMENT.** *The obligations record for chapter I.* Bundles the §6 dispositions in one
place, with the adjudication verdicts as docstrings: `(LB1)` CARRIED-OPEN (E.39); `(MP1)`
CARRIED-OPEN (E.40); `(MP1′)` RETIRED — "denotes a consequence of the pins, not an obligation.
No instance record carries it and no ledger item fences it" (`EFF.T2.25`) — NO carrier is
declared for it (declaring one would resurrect a retired name); `(SEC-RANK)`/`(RISE)` are
carrier hypotheses that fence nothing ("the acceptance record states it 'fences no read'",
`EFF.T2.52`) — they live as E.12 fields / E.35 hypotheses, NOT as chapter-I conjuncts.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The chapter-E obligations record: what chapter I receives from the σ-ladder. -/
structure LadderObligations {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop where
  lb1 : LB1Carrier C B
  mp1 : MP1Carrier C B
```

**DEPENDS.** E.39, E.40. **PROOF.** definitional. **SIZE.** 8 lines.

**SOURCE.** `EFF.T2.44` (acceptance: "The two open obligations and the HE3 supplier cap
survive"); EFF-T2 §9 (the two-obligation census, quoted in this section's header); Part V
(the two-gate ruling this record feeds).

**TEETH.** none (bookkeeping); chapter I's row-disposition census consumes this record's
field list as ground truth for the `(LB1)`/`(MP1)` Display-A conjuncts.

**ENVIRONMENT.** ENV-E2.

---

## 7. §7 — THE σ DICTIONARY AND THE TRANSPORT LAWS (GC-4; **TERMINAL SUPPLY**)

> **This is the chapter's terminal supply.** What chapter H's §11 dictionary, the drainage
> recursions, and chapter F's σ-law faces consume from E: `ladderSigma` + `ladderSigma_degree`
> (E.45/E.46), the rung transport law `rungStep_sigma` (E.48), and the μ₂ = 2 dictionary with
> its three-letter alphabet (E.49–E.52). GC-4 binds: every σ output is a
> `Uniformity.Density.FactorizationType`, produced by a NAMED dictionary function with a
> degree-conservation lemma; inductive leaf labels are dictionary DOMAINS only. Ordering /
> multiset normalization is `HYP.12` [CORE-SET] — no node here re-decides it; everything is
> stated against the landed `FactorizationType` API.

### NODE E.45 [def] [fresh]

**STATEMENT.** *The ladder leaf and the σ dictionary.* A **ladder leaf** is the numerical
record of one terminal emission: the per-level jump data `path : List (ℕ × ℕ)` (each entry
`(ℓ_i, g_i)` — value-index and residue-degree jumps of the levels traversed) and the terminal
read `term : ℕ × ℕ` (`(ℓ′, deg r′)` of the deciding separable-side factor). Its `(e, f)` at
base `(e₀, f₀)` is the composed product
`leafEF (e₀,f₀) leaf = (e₀ * Π ℓ_i * ℓ′, f₀ * Π g_i * deg r′)` — HE7.A clause 6's "multiplying
the successive displayed `e`- and `f`-increments" / THEOREM HE7.D's
`e = e₁ℓ_1⋯ℓ_{i+1}, f = f₁g_1⋯g_{i+1}`. The **dictionary**:
`ladderSigma (e₀ f₀) (leaves : Multiset LadderLeaf) : FactorizationType` — the multiset image
under `leafEF`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- One terminal emission of the σ-ladder read (numerical shadow, D-E2). -/
structure LadderLeaf where
  path : List (ℕ × ℕ)
  term : ℕ × ℕ
  deriving DecidableEq

/-- The composed `(e, f)` of a leaf at base `(e₀, f₀)` (`EFF.HE7.48`'s display). -/
def LadderLeaf.ef (l : LadderLeaf) (e₀ f₀ : ℕ) : ℕ × ℕ :=
  (e₀ * (l.path.map Prod.fst).prod * l.term.1,
   f₀ * (l.path.map Prod.snd).prod * l.term.2)

/-- **The σ dictionary** (GC-4): ladder leaves → the landed factorization type. -/
def ladderSigma (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) :
    Uniformity.Density.FactorizationType :=
  ⟨leaves.map fun l => l.ef e₀ f₀⟩
```

**⚠ GC-4 CONFORMANCE.** Output carrier: landed `FactorizationType`, by anonymous constructor
against its landed definition (the CHAP-B `typeOf g = ⟨{(ℓ, m·d)}⟩` pattern) — if the landed
type's constructor is not the raw multiset (e.g. carries an invariant field), the stub stage
adapts THROUGH the landed API (`FactorizationType.ext`), never by a parallel type. `LadderLeaf`
is an allowed dictionary DOMAIN (decidable, inductive-free record).

**DEPENDS.** none E-internal · landed `Uniformity.Density.FactorizationType`.

**PROOF.** definitional. **SIZE.** 20 lines.

**SOURCE.** `EFF.T2.31` clause 6 ("their ramification and residue degrees are obtained by
multiplying the successive displayed e- and f-increments"); `EFF.HE7.48` (the composed
invariants display); `EFF.T2.33`–`.37` (the five instance dictionaries:
`(e,f) = (e₁e_s, f₁f_s)`, `(e₁ℓ, f₁deg r)`, `(e₁ℓℓ₂, f₁d_r deg r₂)`, `(e₁e₂ℓ₂, f₁f₂deg r₂)`).

**TEETH.** Q1 (1,335 PARI σ agreements at n = 8 — every one is a value of this dictionary) →
instance evidence; the dictionary itself is definitional; E.46 is its mandatory invariant.

**ENVIRONMENT.** ENV-E1 + landed kernel.

---

### NODE E.46 [lemma] [fresh]

**STATEMENT.** *Degree conservation (GC-4's mandatory invariant).*
`(ladderSigma e₀ f₀ leaves).degree = Σ_{l ∈ leaves} (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2` — and,
under the weight bookkeeping of E.20/E.21 (each leaf's `e·f` = its emitted block degree,
summing to `deg F`), `= F.natDegree`. Stated in two clauses: the unconditional multiset
identity, and the conditional block-degree form with the weight hypothesis explicit.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem ladderSigma_degree (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) :
    (ladderSigma e₀ f₀ leaves).degree
      = (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum

theorem ladderSigma_degree_eq_deg {O : Type*} [CommRing O]
    (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) (F : Polynomial O)
    (hwt : (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum = F.natDegree) :
    (ladderSigma e₀ f₀ leaves).degree = F.natDegree
```

**DEPENDS.** E.45 · landed `FactorizationType.degree`, `FactorizationType.degree_mk_add`.

**PROOF.**
1. Unfold `degree` on the constructed multiset (landed `degree_mk_add` / the landed
   definition's `Multiset.sum` shape); `Multiset.map_map` collapses the two maps.
2. Second clause: rewrite with `hwt`.

**SIZE.** 12 lines.

**SOURCE.** GC-4 (the mandatory invariant, `stageSigma_degree`/`typeOf_degree` pattern);
`EFF.HE7.36` (`D″ ∣ deg f_S` and the orbit-size sum — the weight bookkeeping's source);
`EFF.T2.30` (`(FUND)` `|Ω| = ef`).

**TEETH.** Q1's `Σef = 8` per member → **Lean theorem** + E.67's executable gate.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.47 [lemma] [fresh]

**STATEMENT.** *Rung composition of leaves (associativity of the ladder product).* Prepending
a rung `(ℓ, g)` to a leaf's path multiplies its `(e, f)` componentwise:
`(LadderLeaf.mk ((ℓ,g) :: p) t).ef e₀ f₀ = (LadderLeaf.mk p t).ef (e₀ * ℓ) (f₀ * g)` — the
dictionary commutes with descending one level. Consequence (the form C's tower grammar
consumes): `ladderSigma e₀ f₀ (leaves.map (prepend (ℓ,g))) = ladderSigma (e₀*ℓ) (f₀*g) leaves`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

def LadderLeaf.prepend (r : ℕ × ℕ) (l : LadderLeaf) : LadderLeaf :=
  ⟨r :: l.path, l.term⟩

theorem ladderSigma_prepend (e₀ f₀ : ℕ) (r : ℕ × ℕ) (leaves : Multiset LadderLeaf) :
    ladderSigma e₀ f₀ (leaves.map (LadderLeaf.prepend r))
      = ladderSigma (e₀ * r.1) (f₀ * r.2) leaves
```

**DEPENDS.** E.45 · mathlib `List.prod_cons`, `Multiset.map_map`.

**PROOF.** 1. `ef` unfolds; `List.prod_cons` + `mul_comm`/`mul_assoc` normalize; `Multiset.map`
congruence; `FactorizationType` constructor congruence.

**SIZE.** 12 lines.

**SOURCE.** `EFF.T2.21` (the child carrier's inherited invariants `e_child = e_𝒞 e′,
f_child = f_𝒞 deg r′` — prepending IS the child jump's bookkeeping); `EFF.HE7.16`(ii) (the
level-i composition); `EFF.GENHN.17`-side surviving composition formulas (via CHAP-H H-10's
ruling — the composed-key σ composition is exactly this law; E consumes nothing else of
GENHN).

**TEETH.** `he7rannex_supp.py` (level-3 σ = PARI 79/79 — three-level compositions) → instance
evidence; the law is a **Lean theorem**.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.48 [theorem] [fresh]

**STATEMENT.** *The rung σ-transport law (σ is multiplicative over the block split).* For
monic `F = Π blocks` over `O` (the `(SIDE-PROD)`/`(LABEL-PROD)`/`(BOUNDARY-PROD)` situations):
`typeOf F = Σ_blocks typeOf block` — via the LANDED product law `typeOf_mul` (chapter A
kernel), iterated over the list. Combined with the dictionary: if each block's read emits
`ladderSigma`-leaves matching its `typeOf` (the instance hypothesis), the whole state's σ is
the multiset SUM of the blocks' σ — the transport law the drainage recursions and H §11's
`composedSigma` consume from E, and the σ-half of HE7.A clauses 4/6 and T2.KEY-BOUNDARY.

**SIGNATURE.**
```lean
namespace Uniformity.Density
-- (a theorem about landed objects: lives in the owning namespace, GC-6.2)

theorem typeOf_list_prod {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (l : List (Polynomial O))
    (hm : ∀ g ∈ l, Polynomial.Monic g) (hcond : True) :
    -- hcond placeholder: typeOf_mul's actual side conditions (coprimality/monicity),
    -- to be instantiated VERBATIM from the landed typeOf_mul signature at stub time
    typeOf l.prod = (l.map typeOf).sum
```

**⚠ SIGNATURE NOTE (the landed side-condition is the contract).** The landed `typeOf_mul`'s
exact hypotheses (monicity; possibly coprimality of the factors' reductions or root-set
disjointness) BIND this node: the stub stage copies them verbatim into `hcond`'s place; the
blueprint freezes the SHAPE (`typeOf` of a monic product = sum). If `typeOf_mul` requires
coprimality that the ladder's blocks supply only through their disjoint root sets (carrier
content), the node takes that as an explicit hypothesis and E.23 routes it — never a silent
strengthening of the landed lemma. Flagged for the stub stage's 0e type-diff.

**DEPENDS.** landed `typeOf_mul`, `monicFactors_mul` · E.45 (the dictionary this feeds).

**PROOF.** 1. Induction on `l`; `typeOf_mul` at each cons; sum bookkeeping.

**SIZE.** 12 lines.

**SOURCE.** `EFF.T2.17` (`(SIDE-PROD)`/`(LABEL-PROD)` — "Every emitted label block is read
from its own development"); `EFF.T2.32` (T2.KEY-BOUNDARY's "Multiplying the resulting
identities proves the assertion"); `EFF.T2.31` clause 6 ("their product is F").

**TEETH.** Q1's member-by-member σ against PARI (each member's σ is assembled by exactly this
sum) → **Lean theorem** modulo the landed side-conditions.

**ENVIRONMENT.** ENV-E2 (+ the landed kernel's instances).

---

### NODE E.49 [def+lemma] [fresh]

**STATEMENT.** *The μ₂ = 2 dictionary (the n = 8 six-row table, `EFF.HE7.58`).* Dictionary
domain: the six-row case type `Mu2Row` (rows 1–4 the polygon cases, row 5 the α-refine
pointer, row 6 the peel); dictionary function at the n = 8 frame (base `(e₁ℓ, f₁d_r) = (4,1)`,
`K₂ = F_q`):
row 1 (`one side, len 2, λ₂ ∉ ℤ`) ↦ `⟨{(8,1)}⟩`; row 2 (`λ₂ ∈ ℤ, R₂ inert`) ↦ `⟨{(4,2)}⟩`;
rows 3/4 (`R₂ split` / `two sides len 1`) ↦ `⟨{(4,1),(4,1)}⟩`; row 5 (α-refine) ↦ recurse
(E.52's loop, terminating by E.55/E.56); row 6 (peel) ↦ `⟨{(4,1),(4,1)}⟩`. Lemma half: the
value map on decided rows is total and lands in the three-letter alphabet.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- The μ₂ = 2 dictionary rows (`EFF.HE7.58`'s table; rows 5/6 route onward). -/
inductive Mu2Row
  | oneSideHalf      -- row 1: λ₂ ∉ ℤ (ℓ₂ = 2)
  | oneSideInert     -- row 2: λ₂ ∈ ℤ, R₂ irreducible quadratic
  | oneSideSplit     -- row 3: λ₂ ∈ ℤ, R₂ split
  | twoSides         -- row 4
  | refineRow        -- row 5: R₂ = (Z−s₂)² — α-refine, re-read
  | peelRow          -- row 6: Ψ ∣ f — peel
  deriving DecidableEq

/-- The decided-row σ values at the n = 8 frame. -/
def mu2Sigma : Mu2Row → Option Uniformity.Density.FactorizationType
  | .oneSideHalf  => some ⟨{(8, 1)}⟩
  | .oneSideInert => some ⟨{(4, 2)}⟩
  | .oneSideSplit => some ⟨{(4, 1), (4, 1)}⟩
  | .twoSides     => some ⟨{(4, 1), (4, 1)}⟩
  | .refineRow    => none        -- re-read at the refined key (E.52)
  | .peelRow      => some ⟨{(4, 1), (4, 1)}⟩

theorem mu2Sigma_degree : ∀ r v, mu2Sigma r = some v → v.degree = 8
```

**DEPENDS.** E.45 (GC-4 conformance shape) · landed `FactorizationType`.

**PROOF.** 1. `decide`-style case check on the five decided rows (degrees `8·1`, `4·2`,
`4+4`, `4+4`, `4+4`).

**SIZE.** 24 lines.

**SOURCE.** `EFF.HE7.58` (the table, transcribed row-for-row — the source's own six-row
markdown form; row 5's "→ one of the above" upgraded at `EFF.HE7.59` = E.52's licence; row 6
per `EFF.HE7.60`); `EFF.HE7.57` (the n = 8 frame: `D″ = 4, K₂ = K = F_q, T₂ = 2u, μ₂ = 2`).

**TEETH.** Q1 ("exactly the three outputs of THEOREM HE7.A's μ₂ = 2 dictionary (§S8), and no
fourth value ever appears", 1,335/1,335) + `he7r1_supp.py` (row 6, 8/8 + 2/2 + 2/2) →
the value map is a **Lean def + decidable lemma**; E.65/E.67 fire it numerically.

**ENVIRONMENT.** ENV-E1 + landed kernel.

---

### NODE E.50 [lemma] [fresh]

**STATEMENT.** *The three-letter alphabet ("no fourth value possible").* The image of
`mu2Sigma` on decided rows is exactly
`{⟨{(8,1)}⟩, ⟨{(4,2)}⟩, ⟨{(4,1),(4,1)}⟩}` — three values; and row 5's recursion lands in the
same alphabet (given E.52: the re-read terminates in a decided row). This is `EFF.HE7.61`'s
decorrelation anchor: the alphabet MATCHES HE6's independently observed σ-alphabet
(HE6-T-CASEB) — the match itself is instance evidence, recorded here as the docstring, not a
Lean claim.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem mu2Sigma_alphabet :
    ∀ r v, mu2Sigma r = some v →
      v = ⟨{(8, 1)}⟩ ∨ v = ⟨{(4, 2)}⟩ ∨ v = ⟨{(4, 1), (4, 1)}⟩
```

**DEPENDS.** E.49. **PROOF.** 1. `decide` / case check. **SIZE.** 8 lines.

**SOURCE.** `EFF.HE7.58` (exhaustiveness WITH row 6 — "The exhaustiveness claim holds only
WITH row 6"); `EFF.HE7.61` (the alphabet-match fence); `EFF.HE7.60` ("the three-σ alphabet and
the 'no fourth value possible' claim survive verbatim").

**TEETH.** HE7-T-CASEB-SEP (three distinct PARI σ inside ONE outer family, 8/8 predicted) →
**Lean theorem** for the alphabet; the family-realization half stays machine evidence (§13).

**ENVIRONMENT.** ENV-E1.

---

### NODE E.51 [theorem] [fresh]

**STATEMENT.** *The peel-row law (row 6, given the peel supplier).* At the n = 8 frame: if the
peel emission hypothesis holds — `Ψ` emits `(e,f) = (4,1)` (LEMMA HE6R1-3's conclusion,
supplied as `EFF.HE6R1 [supplied-by: chapter C]`) — and the quotient `f′` (degree 4, every
root a level-2 point, `μ₂′ = 1`) emits one factor with `4 ∣ e*f` and `e*f = 4` forcing
`(e,f) = (4,1)` (the divisibility from local forcing = `hforce`'s shadow; the arithmetic:
`ef = 4 ∧ 4 ∣ ef`-forced orbit gives the unique split), then
`σ(f) = ⟨{(4,1), (4,1)}⟩` with degree 8 — `EFF.HE7.60`'s displayed derivation, schema form.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem peel_row_law
    (hpeel : True)   -- placeholder anchoring the HE6R1-3 emission supplier
                     -- [supplied-by: chapter C]; stub stage replaces by the
                     -- typed emission record per GC-13 resolution
    {e f : ℕ} (hforce4 : 4 ∣ e * f) (hef : e * f = 4)
    (he : 4 ∣ e ∨ (e = 4 ∧ f = 1)) :   -- the forcing shadow at μ₂′ = 1
    e = 4 ∧ f = 1
```

**⚠ SIGNATURE NOTE.** The honest Lean content of the quotient leg is the arithmetic
`4 ∣ ef ∧ ef = 4 ∧ (forcing e-side) ⟹ (e,f) = (4,1)` — the rest is the C-supplied emission.
The `hpeel : True` placeholder is DELIBERATE and survives only until GC-13 resolution: the
orchestrator replaces it with C's typed HE6R1-3 record at freeze; a fleet agent must NOT prove
this node while the placeholder is `True` (it would be vacuous) — the node is BLOCKED until
resolution, and §12's stub list marks it so.

**DEPENDS.** E.15 (`ef_forcing` shape), E.49 · C placeholder as displayed.

**PROOF.** 1. `omega`/`interval_cases` on `ef = 4` with the divisibility. (Post-resolution:
compose with C's emission record.)

**SIZE.** 12 lines.

**SOURCE.** `EFF.HE7.60` (the peel row, verbatim derivation: "LEMMA HE6R1-3 gives Ψ
irreducible over O of degree D″ = 4 with `(e,f) = (4,1)` … `deg f′ = 4 = D″` and `μ₂′ = 1` —
and at `μ₂′ = 1` every root of f′ is a level-2 point, so `D″ = 4` divides its local degree
(LEMMA HE6-0′), forcing f′ irreducible with `(e,f) = (4,1)`"); `EFF.HE7.09` (the peel
convention).

**TEETH.** `he7r1_supp.py` A4/A5 (2/2 PARI on σ(f) AND σ(Ψ) — "the latter a direct oracle
test of the peel's irreducibility-and-letter claim", which "no textual argument of this note
supplies") → the oracle evidence is recorded in §13 as the supplier's machine leg; E's
arithmetic shell is a **Lean theorem**.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.52 [theorem] [fresh]

**STATEMENT.** *THEOREM HE7.A′ schema (the n = 8 bite decided, refine loop included).* At the
n = 8 frame with the E.23 instance suite: every member is decided by the six-row dictionary —
rows 1–4/6 directly (E.49/E.51), row 5 by re-reading at the refined key `Ψ − w` (licensed by
the transported package = E.38(iii)'s obligation discharged at this frame + E.42's fold), the
re-read landing at a STRICTLY larger slope (E.56) so the loop terminates (E.55's finiteness /
E.07's bounds at `μ₂ = 2`: at most finitely many refines, then a decided row). Conditionality
transcribed: "unconditionally" is scoped to the n = 8 box configuration with `disc f ≠ 0`; the
peel leg rests on HE6R1-3 (C placeholder); "no base change, no irreducibility of Ψ **as a
hypothesis** … and no order-≥2 citation".

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem he7a_prime_schema
    -- the decided-read statement at the n = 8 frame, over the instance suite:
    (read : ℕ → Mu2Row)                  -- the row at refine-step i
    (hterm : ∃ i, read i ≠ .refineRow)   -- termination supply (E.55/E.56 at μ₂ = 2)
    : ∃ i v, mu2Sigma (read i) = some v ∧
        (v = ⟨{(8,1)}⟩ ∨ v = ⟨{(4,2)}⟩ ∨ v = ⟨{(4,1),(4,1)}⟩)
```

**⚠ SIGNATURE NOTE.** The schema takes the refine trajectory as a function and its
termination as the hypothesis E.55/E.56 discharge at instances — `Nat.find` on `hterm` yields
the deciding index. The full HE7.A′ (member-level, with the actual polygon reads producing
`read`) is the instance composition at E.23 + gates E.65. The blueprint deliberately does NOT
promise a member-level Lean theorem at n = 8 — that is the leancheck-style certificate
layer's job (B.79–B.82 pattern at level 2), a POST-blueprint target recorded in §14.

**DEPENDS.** E.49, E.50, E.51, E.55, E.56 (termination supply, forward), E.38/E.42 (the
refined-key licence).

**PROOF.** 1. `Nat.find hterm` gives the first decided row; E.49 evaluates it; E.50 gives the
alphabet.

**SIZE.** 14 lines.

**SOURCE.** `EFF.HE7.62` (THEOREM HE7.A′, verbatim incl. the three "no …" clauses and the
peel-stratum conclusion-not-assumption sentence; the "five-row dictionary" off-by-one is the
source's — recorded as HE7 source defect 6, §13); `EFF.HE7.59` (row 5's displayed upgrade:
"read AT THE REFINED KEY, which LEMMA HE7-12 licenses … strictly larger slope by LEMMA
HE7-13, so the loop terminates (LEMMA HE7-8)").

**TEETH.** Q1 + `he7r1_supp.py` + `he7r2_supp.py` jointly: "1,587/1,587 members decided … 0
mis-decisions" → instance evidence; the schema is a **Lean theorem**.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.53 [lemma] [fresh]

**STATEMENT.** *The GC-3 bridge fence (the dictionary's `(e,f)` vs the ideal-theoretic pair).*
A statement-shaped fence node: the dictionary's leaf values `(e, f)` satisfy
`e * f = <block degree>` (E.46's conservation), and AT INSTANCES the block degree is
`Module.finrank K₀ L` of the emitted factor's field — the rank-form fundamental identity
`Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`
(`leanfinal/Uniformity/Quarry/RamificationInertiaLocal.lean`, the GC-3 primed generation).
The node's Lean content is the CONSERVATION composition (E.46 + the finrank hypothesis); the
identification of the dictionary's `(e, f)` with `(ramificationIdx', inertiaDeg')` is
**`HYP.01` + `HYP.12` [CORE-SET] and is NOT made** — any consumer needing it states it as an
explicit hypothesis or returns `BLOCKED: HYP.01` (GC-3's fence, verbatim).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem leaf_ef_finrank {e f n : ℕ} (hef : e * f = n)
    (hrank : n = n) :  -- anchor: instances substitute finrank K₀ L here via the
                       -- quarry identity; the fence forbids more
    e * f = n
```

**⚠ NODE-KIND NOTE.** Deliberately thin (the Lean half is arithmetic already proved at E.46);
the node EXISTS to give §13's GC-3/HYP.01 row a blueprint anchor and to forbid, in writing,
the silent identification — the inertiaDegOf-lesson class of defect. The stub stage may
retire the Lean stub to a comment block + the E.46 citation if the czar prefers; either way
the FENCE TEXT is the contract.

**DEPENDS.** E.46 · [quarry:
`Uniformity/Quarry/RamificationInertiaLocal.lean` — cited, not consumed].

**PROOF.** trivial. **SIZE.** 6 lines.

**SOURCE.** GC-3 ("KEPT APART, on pain of HYP.01"); `EFF.T2.30` (`(FUND)`); ledger HYP.01 /
HYP.12 rows (CORE-SET, human-review).

**TEETH.** none (fence). **ENVIRONMENT.** ENV-E1.

---

### NODE E.54 [lemma] [fresh]

**STATEMENT.** *Frame/origin invariance of σ (the `(FRAME)`/`(ORIGIN)` discipline at the
dictionary).* The landed kernel already carries the σ-invariances the frame changes need:
`typeOf_shift` (recentering `x ↦ x + c`), `typeOf_scaleRoots`/`typeOf_scale` (the `Y ↦ bY`,
`c·` moves). This node packages them at the ladder's use shape: for monic `F` and a frame
change of the residual read (scalar `c ≠ 0`, variable scale `b ≠ 0`, origin monomial `Y^ν`
removed BEFORE factoring — `(ORIGIN)`'s "recorded and removed"), the emitted factor DEGREES
and MULTIPLICITIES — hence `ladderSigma`'s inputs — are unchanged: "Frame changes preserve
factor degrees, multiplicities, separability, and transported root classes. Literal
coefficient strings are not asserted to be invariant" (`EFF.T2.13`). Lean form: the numerical
shadow's invariance is definitional (degrees/multiplicities of a multiset are unchanged by a
relabelling bijection = E.34's unit multiplication acting on roots); stated as: `ladderSigma`
depends only on the `(deg, mult)` shadow, which the frame acts on trivially.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem ladderSigma_frame_invariant (e₀ f₀ : ℕ) (leaves leaves' : Multiset LadderLeaf)
    (h : leaves = leaves') :  -- the shadow equality the frame change induces
    ladderSigma e₀ f₀ leaves = ladderSigma e₀ f₀ leaves'
```

**⚠ NODE-KIND NOTE.** Trivial as stated (`congrArg`) — DELIBERATELY: the mathematical content
("the frame change induces `h`") is the instances' (`EFF.T2.13`/`.14` are IMPORTED frame
conversions; `EFF.T2.36`'s `R_{λ₂}(Z) = τ(H₀)·R̂(Z/δ)` instance is C's). The landed
`typeOf_shift`/`typeOf_scaleRoots`/`typeOf_scale` citations are the REAL teeth at the
`typeOf`-level and are consumed by name wherever an instance needs the polynomial-level move.
The node anchors §13's `(FRAME)`/`(ORIGIN)` row and the twist-invariance clause of
`EFF.HE7.08` ("Every statement used below is twist-invariant … vanishing/non-vanishing at a
residue, degree, and the multiset of irreducible factors up to `K₂^×`-scaling").

**DEPENDS.** E.45 · landed `typeOf_shift`, `typeOf_scaleRoots`, `typeOf_scale` (cited).

**PROOF.** `congrArg`. **SIZE.** 6 lines.

**SOURCE.** `EFF.T2.13` (`(FRAME)`, verbatim); `EFF.T2.14` (`(ORIGIN)`: "The factor `Y^ν` is
recorded and removed before the normalized residual is factored"; "A nonzero origin shift is
not silently discarded"); `EFF.HE7.08` (twist-invariance as the load-bearing scope fence,
with tooth HE7-T-BADTWIST showing dropping the twist mispredicts σ).

**TEETH.** HE7-T-BADTWIST + S7 HETOW frame gate / nonzero-origin tooth → dispositions at §13;
the E-side shell is a **Lean theorem** (thin by design).

**ENVIRONMENT.** ENV-E1.

---

## 8. §8 — ROOT-CONTINUATION AND EXHAUST: THE REFINE CHAIN, THE BLOCK SPLIT, TERMINATION

> **The two hard nodes of the chapter live here** (E.55, E.57), plus the mutual-induction
> resolution (E.56) and the arithmetic gates that keep `μ₂ ≤ 3` clean (E.59, E.60).

### NODE E.55 [theorem] [fresh] — **HARD NODE**

**STATEMENT.** *α-refine chains are finite (LEMMA HE7-8, (REF-TERM), characteristic-free).*
Over the carrier with the coefficient link (see hypotheses): suppose an INFINITE chain of
α-refines — keys `Ψ^{(0)} = Ψ`, `Ψ^{(j+1)} = Ψ^{(j)} − w_j` with `deg w_j < D″`,
`hgt w_j = λ^{(j)}` STRICTLY increasing integers, each step at a node whose development
satisfies the single-side floor `hgt (A_m^{(j)}) ≥ (μ₂ − m)·λ^{(j)}` for every `m < μ₂` — and
`μ₂ ≥ 2`. Then `F = (Ψ − W)^{μ₂}` for the π-adic limit `W` of the partial sums, so `F` is not
squarefree over the fraction field — contradiction. Hence every α-refine chain is finite. "The
argument needs no 'binomial kill' … the node condition … plus `λ^{(j)} → ∞` is all that is
used."

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem refine_chain_finite {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {K : Type*} [Field K] (C : SlotCarrier O K)
    -- the coefficient link: heights control O-coefficient valuations
    (hcoeff : ∀ (A : Polynomial O) (v : ℤ), A.natDegree < C.D →
      (v : WithTop ℤ) ≤ C.hgt A → ∀ i, ((v : WithTop ℤ) ≤ hOcoeff (A.coeff i)))
    -- (hOcoeff abbreviates the O-valuation read into WithTop ℤ; see NOTE)
    {F Ψ : Polynomial O} {μ₂ : ℕ} (hμ : 2 ≤ μ₂)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O))))
    (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hdeg : ∀ j, (w j).natDegree < C.D * μ₂)     -- deg < D″; see NOTE on D″
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hmono : StrictMono lam)
    (A : ℕ → ℕ → Polynomial O)
    (hdev : ∀ j, F = (Ψ - ∑ i ∈ Finset.range j, w i) ^ μ₂
      + ∑ m ∈ Finset.range μ₂, A j m * (Ψ - ∑ i ∈ Finset.range j, w i) ^ m)
    (hfloor : ∀ j, ∀ m < μ₂, ((μ₂ - m : ℕ) : ℤ) * lam j ≤ … )  -- cleared floor; NOTE
    : False
```

**⚠ SIGNATURE NOTE (three spelling calls, all stub-stage).** (a) `hOcoeff` is the DVR
valuation `addVal`-read of an `O`-element into `WithTop ℤ` — spell against the landed
`Uniformity` valuation API (`addVal`/`pow_dvd_iff_le_addVal` family, chapter-A kernel), not a
new definition. (b) The degree bound is against `D″ = C.D * μ₂`… no — at the ladder the
refine increments have `deg < D″` where `D″` is the CURRENT key degree `C.D`-at-the-rung;
instances fix it; the blueprint freezes `deg w_j < <current key degree>` with the parameter
made explicit at stub time. (c) `hfloor`'s right side is `hgt (A j m)` cleared into the same
`WithTop ℤ` order — the display is elided here; the stub elaborates it as
`((μ₂ - m : ℕ) : ℤ) • (lam j) ≤ C.hgt (A j m)`-shaped. None of the three calls changes the
theorem's strength; each is flagged in §12.

**DEPENDS.** E.10 (heights), E.38 (`slot_fold` for the partial sums' heights) · mathlib
`IsAdicComplete`, `Polynomial.coeff` limits, `Squarefree`.

**PROOF (the corpus's, in Lean steps).**
1. Partial sums `W_j` converge coefficientwise: for each coefficient index `i`, the tail
   increments' coefficients have `addVal → ∞` (via `hh`, `hmono`, `hcoeff` — `lam j → ∞`
   since strictly monotone integer sequence), so the coefficient sequence is Cauchy in the
   `maximalIdeal`-adic topology; `IsAdicComplete` gives limits; assemble `W` (degree `< D″`,
   coefficientwise).
2. The floors force `A j m → 0` coefficientwise (same mechanism through `hfloor`).
3. Pass to the limit in `hdev` at each fixed polynomial coefficient (all sums are finite in
   each coefficient): `F = (Ψ − W)^{μ₂}`.
4. `μ₂ ≥ 2` makes `(Ψ − W)^{μ₂}`'s image not squarefree
   (`Squarefree` fails on `p^k, k ≥ 2, p` nonunit — mathlib `Squarefree.pow`-contrapositive /
   `sq_dvd`); contradiction with `hsq`.

**SIZE.** 60 lines. **SPLIT-MANDATED ×3:** `E55a` (step 1, the coefficientwise completeness
limit — reusable), `E55b` (step 3, the limit-passing in a polynomial identity), `E55` (the
assembly + step 4). This is the chapter's hardest genuinely-provable node; claim it early
(the CHAP-H H.60/H.70 scheduling lesson).

**SOURCE.** `EFF.HE7.53` (LEMMA HE7-8, statement + proof verbatim — the convergence argument
is the source's own: "dv₂(A) → ∞ forces the Φ′-development coefficients of A, hence its
O-coefficients, to converge π-adically to 0 … The partial sums W_j therefore converge in the
(complete) O-module of polynomials of degree < D″ … Passing to the limit … gives
f_S = (Ψ − W)^{μ₂} in O[x] … With μ₂ ≥ 2 this makes disc f_S = 0"; the no-binomial-kill
NON-IMPORT); `EFF.T2.26` (`HE7-REF-TERM` as the pinned `(SEC-RANK)` supplier at a DEFINITION
HE6-1 key — THIS node is that supplier's Lean form, discharging `(SEC-RANK)` "in its
well-foundedness form … it refutes infinite α-refine chains directly", `EFF.T2.52`).

**TEETH.** Q1's 42 one-step refines + PE2's first 2-step chains + `he7annex_supp.py` P4 (the
WRONG continuation cycles 48/48 — the tooth showing termination is not free) → **Lean
theorem**; the completeness hypothesis is declared per GC-6.4 (only here and its splits).

**ENVIRONMENT.** ENV-E2 + `[IsAdicComplete (maximalIdeal O) O]`.

---

### NODE E.56 [theorem] [fresh]

**STATEMENT.** *The strict slope increase along the chain (LEMMA HE7-13), with the HE7-12(d)
mutual induction resolved as ONE chain invariant.* Carrier mechanism, two clauses:
(i) **the per-step jump** (the refined class rises): if `hgt a = hgt b = (λ : ℤ)` and
`dig a = dig b`, then `(λ : WithTop ℤ) < hgt (a − b)` — the SAME-residue kill (LEMMA HE7-13's
own mechanism per root; HE7-13′(b)); taken from the carrier law `hsame` (hypothesis, promotion
candidate — the E.35 note's counterpart);
(ii) **the chain invariant** (the simultaneous induction of `EFF.HE7.44`(d)'s `[r3]` rider and
HE7-13, resolved): along a refine chain where step `j`'s increment `w_j` is read at the
current slope `λ^{(j)}` (its `hgt`) and each refined class rises past it (clause (i)), the
slope sequence is STRICTLY MONOTONE and the increments' heights are pairwise distinct — by
strong induction on the chain length, proving [distinctness + strict increase + the fold's
`W ≠ 0` exactness (E.38's `slot_fold` at the pairwise-distinct heights)] TOGETHER at each
step. No circularity survives: the invariant is one induction hypothesis.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem same_digit_rises {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    {a b : Polynomial O} {k : ℤ} (ha : C.hgt a = (k : WithTop ℤ))
    (hb : C.hgt b = (k : WithTop ℤ)) (hd : C.dig a = C.dig b) :
    (k : WithTop ℤ) < C.hgt (a - b)

theorem chain_invariant {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hstep : ∀ j, lam j < lam (j + 1))   -- supplied per step by the refined read
    : StrictMono lam ∧ ∀ i j, i < j → C.hgt (w i) ≠ C.hgt (w j)
```

**⚠ SIGNATURE NOTE (what the induction actually buys).** `hstep` — one step's increase — is
what the refined-at-the-new-key READ supplies (the new node's slope is the new min, above the
old by clause (i) applied at every root of the refined class + the polygon re-read; the
polygon re-read is the instances' E.23 row via the transported package E.38(iii)/E.42). The
theorem's content is the PACKAGING: step-local increase ⟹ global strict monotonicity +
pairwise-distinct heights — exactly what E.38's `slot_fold` and E.55's `hmono` consume. So the
corpus's "the two lemmas induct together along the chain" is realized as: E.56 packages the
invariant; E.38 consumes distinctness; E.55 consumes monotonicity; no cycle. (Flagged in §14
for the cross-read as the resolution of HE7's OPEN-CALL 3.)

**DEPENDS.** E.10, E.35 (the sibling forcing), E.38.

**PROOF.**
1. `same_digit_rises`: exact `hsame` (the node exists to NAME the law and its promotion
   candidacy — same protocol as E.35's `hneg`).
2. `chain_invariant`: `strictMono_nat_of_lt_succ hstep`; distinctness: `i < j` gives
   `lam i < lam j` (monotone), so the heights differ (`Nat.cast` injectivity into
   `WithTop ℤ`).

**SIZE.** 18 lines.

**SOURCE.** `EFF.HE7.45` (LEMMA HE7-13 `[r2]`: "the strict slope increase along the refine
chain — DERIVED, not assumed"); `EFF.HE7.44`(d) (the `[r3]` rider: "the values dv₂(w_i) are
pairwise DISTINCT (they are the strictly increasing slopes … the two lemmas induct together
along the chain, the base W = w₁ being a single nonzero (LIFT₂) polynomial)"; the OPEN-CALL 3
flag at the spec's RESOLUTION TRACE: "Flagged, not repaired"); `EFF.HE7.96`(b) (the per-root
mechanism: "a difference of two elements of the same dv₂ and the SAME residue — LEMMA
HE7-13's own mechanism, per root").

**TEETH.** PE2's 2-step chains (634/634 members, independent instrument) + `he7annex_supp.py`
P3 (0 floor violations across 148 refines) → **Lean theorem** (the packaging); the per-step
supply is instance content.

**ENVIRONMENT.** ENV-E2.

---

### NODE E.57 [theorem] [fresh] — **HARD NODE**

**STATEMENT.** *The mixed-node block split (ANNEX-LEMMA HE7-13′(a), schema form).* Given the
rung interface `I` for block `B` (key `Ψ̃`, all-roots-on-disk situation) plus the carrier legs
as hypotheses (the Galois-stability/orbit-forcing data, C-supplied — the E.36 `hforce`
pattern): the label classes partition into BLOCK data — for each side `p` and each factor `q`
of its shadow, a block `B_{p,q} : BlockData C` with: (i) `B.F = Π f_{p,q}` and degree
additivity; (ii) each block's OWN interface has a SINGLE side of slope `p` with length
`L_{p,q} = deg f_{p,q} / (C.D … )` and pure residual shadow (one factor, multiplicity
`k = L_{p,q}/(p.2 * deg q) ∈ ℤ_{≥1}`); (iii) side lengths add: `Σ_q L_{p,q} = len p`;
(iv) the per-block trichotomy gate: a level-3 block has `L_{p,q} = k·p.2·deg q ≥ 4`, so the
block's `μ ≥ 4` (E.59). This is the PROVED level-≥2 counterpart of `(LB1)` (E.39) — annex
grade at source, full displayed proof, promoted here to a proof target.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem block_split {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    -- carrier legs (C-supplied at instances; the schema's explicit hypotheses):
    (hblocks : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCount p q)
    (hblocksHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCountHi p q)
    (hpart : True)  -- the product/disjointness leg; typed at stub per the NOTE
    : ∃ blocks : List (Polynomial O),
        B.F = blocks.prod ∧
        (blocks.map Polynomial.natDegree).sum = B.F.natDegree
```

**⚠ SIGNATURE NOTE (schema honesty; the annex-grade caveat).** The conclusion shape displayed
is the PRODUCT/EXHAUSTION layer; the full contract adds, per block, the single-side and
pure-residual interface clauses of (ii)–(iv) as a `BlockSuite` record (the E.39 note's
structure, INSTANTIATED here rather than hypothesized — this is the level-≥2 vs level-1
asymmetry the corpus draws). The `hpart : True` placeholder marks the disjointness/product
carrier leg (the classes partition the roots — `EFF.HE7.96`(a)'s "the label's factor is the
minimal polynomial" argument, K-theoretic, C-supplied); typed at GC-13 resolution — the node
is BLOCKED for the fleet until then (§12). **Grade note carried:** the source is ANNEX GRADE
("never hostile-passed as written", later covered by the annex stack's 2/2); this chapter's
Lean target, once proved, strictly upgrades it.

**DEPENDS.** E.12, E.14–E.16 (the per-block count laws), E.36 (the dichotomy shape), E.59 ·
C placeholders as displayed.

**PROOF (the corpus's, mapped).**
1. Per class: Galois-stable root set ⟹ monic `O`-divisor (the `hblocks` legs).
2. Per block: HE7-9/HE7-10 re-run on `f_C` (the E.14–E.16 shapes at the block's own
   interface) give the single side + length; residual uniqueness by the
   minimal-polynomial argument (carrier leg) gives the pure shadow `c·r^k`.
3. Length additivity: the partition sums class counts (`hexhaust`) against `haccount` per
   block.
4. The trichotomy gate: E.59's arithmetic.

**SIZE.** 50 lines. **SPLIT-MANDATED ×2:** `E57` (product/lengths) + `E57a` (the per-block
pure-residual interface record).

**SOURCE.** `EFF.HE7.96` (ANNEX-LEMMA HE7-13′, clauses (a)–(e) verbatim + the full proof;
"a mixed node is a bouquet of PURE nodes"); `EFF.HE7.119` rider (ii) (the `Ψ̃ ∤ f_C` one-liner
this consumes through E.36/E.37); ANNEX F-1 (the wiring: "the refine is the α-refine OF THE
REPEATED CLASS'S OWN BLOCK, whose node IS pure"; first live `μ₂ = 3, n = 12`; "vacuous at
every machine-certified degree (μ₂ = 2 forces pure)").

**TEETH.** `he7_pe3_probe12.py` (144/144 at μ₂ = 3, n = 12 — the first mixed-node machine
contact) + `he7annex_supp.py` P2/P5 (128/128 parked residuals exact; 16/16 mixed/pure
boundary) → proof target; the annex-grade source status is recorded in §13.

**ENVIRONMENT.** ENV-E2 (+ `[IsDomain O]`).

---

### NODE E.58 [lemma] [fresh]

**STATEMENT.** *The per-class refine quartet (HE7-13′(b)–(e), carrier arithmetic).* Let `C` be
the carrier with the `hsame` law (E.56) and negation law (E.35's `hneg`); let `Ψ̃, w` have
`hgt w = (λ : ℤ)` with digit `s := dig w`. For an element `a` (the read of `Ψ̃` "at a root",
schema: any polynomial with the stated height/digit):
(b) `hgt a = λ ∧ dig a = s` ⟹ `λ < hgt (a − w)` (the refined class jumps — E.56(i));
(c) `hgt a = λ ∧ dig a ≠ s` ⟹ `hgt (a − w) = λ ∧ dig (a − w) = dig a − s ≠ 0` (companions
persist exactly, labels translated — `dig_add` on `a + (−w)`);
(d) `hgt a = (μ : ℤ)` with `μ < λ` ⟹ `hgt (a − w) = (μ : ℤ) ∧ dig (a − w) = dig a` (lower
sides untouched — `hgt_add_eq` + the height-μ digit read unchanged; the digit clause needs the
fixed-height digit read of a sum where one summand sits strictly higher: a small companion law
`dig_add_high`, hypothesis with promotion candidacy);
(e) `hgt a = (ν : ℤ)` with `λ < ν` ⟹ `hgt (a − w) = λ ∧ dig (a − w) = −s` (steeper sides
collapse onto `λ` — same mechanism, roles swapped; "(e) is what governs, and refutes, the
naive whole-f_S continuation").

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem refine_quartet {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hneg : ∀ A, C.hgt (-A) = C.hgt A ∧ C.dig (-A) = - C.dig A)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    (hhigh : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      (k : WithTop ℤ) < C.hgt b → C.hgt (a + b) = (k : WithTop ℤ) ∧
        C.dig (a + b) = C.dig a)
    {w : Polynomial O} {lam : ℤ} (hw : C.hgt w = (lam : WithTop ℤ)) :
    (∀ a, C.hgt a = (lam : WithTop ℤ) → C.dig a = C.dig w →
      (lam : WithTop ℤ) < C.hgt (a - w)) ∧
    (∀ a, C.hgt a = (lam : WithTop ℤ) → C.dig a ≠ C.dig w →
      C.hgt (a - w) = (lam : WithTop ℤ) ∧ C.dig (a - w) = C.dig a - C.dig w) ∧
    (∀ a (μ : ℤ), μ < lam → C.hgt a = (μ : WithTop ℤ) →
      C.hgt (a - w) = (μ : WithTop ℤ) ∧ C.dig (a - w) = C.dig a) ∧
    (∀ a (ν : ℤ), lam < ν → C.hgt a = (ν : WithTop ℤ) →
      C.hgt (a - w) = (lam : WithTop ℤ) ∧ C.dig (a - w) = - C.dig w)
```

**DEPENDS.** E.10 (`dig_add`, `hgt_add_eq`), E.35, E.56.

**PROOF.**
1. (b): E.56(i). (c): `dig a − dig w ≠ 0`; `dig_add a (−w)` (via `hneg`) gives both clauses.
2. (d): `hhigh a (−w)` at `hgt(−w) = λ > μ`. (e): `hhigh (−w) a`-shape with roles swapped:
   `hgt(a − w) = hgt(−w) = λ` (the strictly-lower summand is `−w`… careful: here `−w` is the
   LOWER one; apply `hhigh (−w) a` then translate; `dig = dig(−w) = −s`).

**SIZE.** 24 lines.

**SOURCE.** `EFF.HE7.96` clauses (b)–(e) + proof, verbatim (incl. the PE3-charge answer:
"the mechanism is NOT slot disjointness … What protects the companion classes on-disk is
RESIDUE SEPARATION, clause (c)'s calculation: same value, different residue"; the translation
law `r₂^τ(Z) = r₂(Z + s₂)` is the shadow's label move, carried by the instances' factor
bookkeeping); `EFF.HE7.44`(a) (clause (d)/(e)'s off-disk sibling).

**TEETH.** `he7annex_supp.py` P2 (clause (c) verified as polynomial EQUALITY, 128/128), P3
(clause (b), 148 refines), P4 (clause (e)'s cycle tooth, 48/48), P5 (16/16) → **Lean
theorem**; the three carrier laws (`hneg`/`hsame`/`hhigh`) are the promotion-candidate
cluster — if E.10 grows fields, all three go together (one dated amendment).

**ENVIRONMENT.** ENV-E2.

---

### NODE E.59 [lemma] [fresh]

**STATEMENT.** *The per-block level-jump gate (μ ≥ 4 at any jump; non-propagation at
μ₂ ≤ 3).* For a block with single-side length `L = k * (ℓ * d)` (`k` the pure-residual
multiplicity, `ℓ*d` the factor's product): if `k ≥ 2` and `ℓ*d ≥ 2` (the jump configuration)
then `L ≥ 4`; hence any interface containing that block has `μ = Σ len ≥ L ≥ 4`. Contrapositive
(the NON-PROPAGATION consumed by E.52 and chapter I's degree-indexing): at `μ ≤ 3` no jump
configuration exists — every node is decided by rows 1–4/6 or a pure refine.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem block_jump_gate {k ℓ d L : ℕ} (hk : 2 ≤ k) (hld : 2 ≤ ℓ * d)
    (hL : L = k * (ℓ * d)) : 4 ≤ L

theorem no_jump_of_mu_le_three {μ L : ℕ} (hμ : μ ≤ 3) (hLμ : L ≤ μ) : ¬ 4 ≤ L
```

**DEPENDS.** E.07 (`jump_floor`).

**PROOF.** 1. `jump_floor` + `hL`; 2. `omega`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.HE7.96`(a) ("the μ₂ ≥ 4 gate is unchanged: `L_{λ,r} = k·ℓ₂ deg r ≥ 4`, so
`μ₂ ≥ L_λ ≥ L_{λ,r} ≥ 4`, so the μ₂ ≤ 3 non-propagation of HE7.A(3) — hence COROLLARY
HE7.B(i)'s n ≤ 15 coverage — is unchanged by the block reduction"); `EFF.HE7.14` (the
non-propagation display).

**TEETH.** `he7annex_supp.py` (96/96 at μ₂ = 4 — the first live jump row) → **Lean theorem**.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.60 [theorem] [fresh]

**STATEMENT.** *THEOREM HE7.C, schema form (the ladder is finite at every degree).* Packaging
of E.07 + E.55: in any read history, (i) every level jump sits at a state with `μ ≥ 4`
(E.59/E.07(i) with clause (1)'s `Σ len = μ`); (ii) the jump target's mass halves
(E.07(ii)/E.17(ii)); (iii) hence the jump count satisfies `2^(J+1) ≤ μ₀` (E.07(iii)) — the
cleared `J ≤ log₂ μ − 1 ≤ log₂ n − 2`; (iv) interleaved α-refines are finite (E.55); every
other step strictly decreases μ (E.17/E.18) — so the read tree is finite. Corollary instances,
as separate small clauses: at `μ₀ = 4` (`n = 8`, `D′ = 2`): `J ≤ 1` and the one jump lands at
`μ₂ ≤ 2` (`2^(J+1) ≤ 4` forces `J ≤ 1`; halving gives `μ₂ ≤ 2`); at `μ₀ ≤ 7` (`n ≤ 15`,
`D′ ≥ 2`): every jump target has `μ₂ ≤ 3` (halving + floor); **the `n = 16` clause is stated
in R3's rider form ONLY**: `J ≥ 2 → μ₀ ≥ 8` (necessary direction; E.64 does the `n`-reading).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem ladder_finite_bounds (μ : ℕ → ℕ) (J : ℕ)
    (h4 : ∀ i ≤ J, 4 ≤ μ i) (hh : ∀ i < J, 2 * μ (i + 1) ≤ μ i) :
    2 ^ (J + 1) ≤ μ 0 ∧ (μ 0 = 4 → J ≤ 1) ∧ (μ 0 ≤ 7 → ∀ i, 1 ≤ i → i ≤ J → μ i ≤ 3)
    ∧ (2 ≤ J → 8 ≤ μ 0)
```

**DEPENDS.** E.07, E.17, E.55 (the α-refine leg, cited in the packaging comment — the
theorem's statement is pure arithmetic; the READ-finiteness composition is E.20's engine with
E.55 discharging the within-level `W`).

**PROOF.**
1. First clause: E.07(iii). Second: `2^(J+1) ≤ 4` forces `J + 1 ≤ 2`. Third: halving from
   `μ 0 ≤ 7` gives `μ 1 ≤ 3` (2μ₁ ≤ 7 ⟹ μ₁ ≤ 3), and inductively `μ i ≤ 3` for `i ≥ 1`.
   Fourth: `2^3 ≤ μ 0`. `omega` + `Nat.pow` lemmas throughout.

**SIZE.** 18 lines.

**SOURCE.** `EFF.HE7.15` (THEOREM HE7.C `[r1]`, statement + proof verbatim; the widening
rider; **ANNEX R R3's rider transcribed**: "read both sentences as 'level 3 / J = 2 is
unreachable below n = 16; n = 16 is the first degree NOT EXCLUDED by the bound.' No consumer
uses more"); `EFF.HE7.16`(i) (the `μ ≤ 7 ⟹ μ₂ ≤ ⌊7/2⌋ = 3` floor, the `[r2, HE7-PE1 F-3]`
repair — the ℕ-division form above IS the floored form, so the pre-r2 defect cannot recur);
`EFF.HE7.57` (the n = 8 frame's `μ₂ = 2`).

**TEETH.** Q1 (n = 8: one jump, μ₂ = 2, everywhere) + `he7annex_supp.py` (n = 16 constructed
family — the machine-instance evidence for the NOT-EXCLUDED direction, never cited as the
existential theorem) → **Lean theorem** (necessary directions only).

**ENVIRONMENT.** ENV-E1.

---

## 9. §9 — THE `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` INDEXED CARRIERS (Display A's `∀ i ≥ 3` conjunct)

### NODE E.61 [def] [fresh]

**STATEMENT.** *The deep-twist residue carrier `(H-VARTHETA-RES)_i`.* For each level `i ≥ 3`,
the named hypothesis that the within-class deep twist units `ϑ_t` of the level-`i` slot read
(E.29's inputs at that level) are CORRECTLY SUPPLIED: each `ϑ_t` is the residue symbol of the
letter monomial `θ_t` (E.33's telescoped product) under the level-`i` transport — a fixed
nonzero element of the previous level's field, "depending on `(k, t)` and the s-bookkeeping
only, NOT on `C` or `ξ`" (R1-a(iii)). Carried as an indexed `Prop`-family over the ladder
data; the CONTENT at instances is chapter C's letter/transport layer (the residues of the
`Λ_j`-monomials — carrier evaluation), so the definition here is the named carrier with the
supply as its single field; the ϑ ORIENTATION cites chapter D's canonical table by anchor
(GC-14; honesty E-5) — no content of that table is restated.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- `(H-VARTHETA-RES)_i` (Display A, ∀ i ≥ 3): the level-i deep-twist units are the
letter-monomial residues, correctly oriented per chapter D's canonical ϑ table
[GC-14 anchor: EFF.GENTOW2 orientation records, supplied-by chapter D]. -/
structure VarthetaRes (i : ℕ) : Prop where
  supplied : True   -- typed at GC-13/GC-14 resolution: the level-i twist-supply
                    -- proposition over chapter C's letter layer; see the NOTE
```

**⚠ SIGNATURE NOTE.** The `True` placeholder is the SAME protocol as E.51's: the carrier's
field is typed when C's letter layer freezes (the orchestrator's GC-13 resolution pass); until
then the blueprint freezes the carrier's NAME, INDEX, and consumption route (chapter I's
Display-A block consumes `∀ i ≥ 3, VarthetaRes i` through E.24's `LadderSupply`). What is NOT
open: at `i ≤ 2` no carrier exists — R1-a(iv): "The twist is trivial at level 1, a
single-letter power at level 2, and a genuine multi-letter monomial first at level 3 — which
is why nothing at n ≤ 15 moves" (E.63 is that statement's arithmetic shadow).

**DEPENDS.** E.33 (the exponent engine) · C/D placeholders as displayed.

**PROOF.** definitional. **SIZE.** 10 lines.

**SOURCE.** `EFF.HE7.110` (R1-b's ϑ_t and its closing compatibility sentence); `EFF.HE7.108`
(R1-a(iii): the fixed letter-monomial residue); `EFF.HE7.112` (the composite twist unit);
ledger Display A (the `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` `∀ i ≥ 3` conjunct); GC-14 (the
orientation table's ownership).

**TEETH.** `he7rannex_supp.py`'s disclosure (ii) — `ϑ_t, t ≥ 1` machine-invisible at the
level-3 family — is WHY this is a carried conjunct and not a discharged one; recorded at §13.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.62 [def] [fresh]

**STATEMENT.** *The w-frame carrier `𝒲_(≤i)`.* The indexed conjunct's second half: the
w-frame data through level `i` (T5's `𝒲` apparatus — gauge letters, their normalization
anchors, and the frame bookkeeping the deep reads assume). E declares the named indexed
carrier; ALL content is chapter D's (T5, `EFF.T5 [supplied-by: chapter D]`) — Brief D product
(4) hands the `𝒲_(≤i)` carriers to E/I by name, and this node is the E-side socket.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

/-- `𝒲_(≤i)` (Display A, ∀ i ≥ 3): the w-frame holds through level i.
Content [supplied-by: chapter D (T5)]; E declares the socket. -/
structure WFrame (i : ℕ) : Prop where
  supplied : True   -- typed at GC-13 resolution against chapter D's T5 layer
```

**DEPENDS.** D placeholder (`EFF.T5 [supplied-by: chapter D]`).

**PROOF.** definitional. **SIZE.** 8 lines.

**SOURCE.** ledger Display A (the conjunct); BRIEF D product (4) ("the `𝒲_(≤i)` carriers that
Display A's `∀ i ≥ 3` conjunct consumes (hand off to E/I by name)"); BRIEF E product (4).

**TEETH.** none (socket). **ENVIRONMENT.** ENV-E1.

---

### NODE E.63 [lemma] [fresh]

**STATEMENT.** *The conjunct is packaged indexed, and vacuous below level 3.* The Display-A
conjunct `∀ i ≥ 3, (H-VARTHETA-RES)_i ∧ 𝒲_(≤i)`, as one named def `DeepTwistConjunct`; plus
the vacuity shadow: with E.61's note (`τ₁ ≡ 1`; level-2 twist is the single letter `Λ₁^c`,
already carried by the level-2 machinery E.29/E.33 WITHOUT this conjunct), the conjunct
constrains nothing at ladder depth `≤ 2` — stated as: `DeepTwistConjunct` restricted to
ladders of `rungs.length ≤ 1` (base + one rung = levels 1–2) is trivially satisfiable. (The
`n`-reading — depth ≥ 3 unreachable below `n = 16` — is E.64.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

def DeepTwistConjunct : Prop := ∀ i, 3 ≤ i → VarthetaRes i ∧ WFrame i

theorem deepTwist_vacuous_shallow (Λ : LadderData) (h : Λ.rungs.length ≤ 1) :
    -- the levels of Λ are ≤ 2, so no consumer of DeepTwistConjunct's indices
    -- exists on Λ's reads: stated as the index bound
    ∀ i, 3 ≤ i → Λ.rungs.length + 1 < i ∨ True
```

**⚠ NODE-KIND NOTE.** The second declaration's Lean content is an index-arithmetic
triviality; its blueprint value is the RECORD: consumers at `n ≤ 15` never instantiate the
conjunct (E.64 + E.60's `μ₂ ≤ 3` gate), matching R1-d's "the first level at which any new
symbol (a ϑ_t ≠ 1 …) can appear is level 3, unreachable below n = 16". The stub stage may
tighten the statement to the honest consumer form once chapter I's Display-A block fixes its
degree-indexing shape; flagged in §12.

**DEPENDS.** E.61, E.62, E.05. **PROOF.** trivial/arithmetic. **SIZE.** 10 lines.

**SOURCE.** `EFF.HE7.114` (R1-d's level-3 sentence); `EFF.HE7.108`(iv); ledger Display A (the
`∀ i ≥ 3` indexing, degree-indexed per CHAP-H H-7's precedent).

**TEETH.** none (packaging). **ENVIRONMENT.** ENV-E1.

---

### NODE E.64 [lemma] [fresh]

**STATEMENT.** *Depth ≥ 3 is unreachable below `n = 16` (the necessary direction, R3-rider
form).* If a read history performs `J ≥ 2` level jumps then `μ₀ ≥ 8` (E.60's fourth clause),
hence `n = D₀·μ₀ ≥ 2·8 = 16` when `D₀ ≥ 2` (composite stages have `D′ ≥ 2`). Stated with the
`n`-bookkeeping explicit: `2 ≤ D₀ → 2 ≤ J → 16 ≤ D₀ * μ₀`. NO existential converse is stated
(ANNEX R R3; the constructed `n = 16` family is machine evidence only).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder

theorem depth3_needs_16 {D₀ μ₀ J : ℕ} (hD : 2 ≤ D₀) (hJ8 : 2 ≤ J → 8 ≤ μ₀)
    (hJ : 2 ≤ J) : 16 ≤ D₀ * μ₀
```

**DEPENDS.** E.60. **PROOF.** 1. `hJ8 hJ`; `Nat.mul_le_mul hD` at `8 ≤ μ₀`. **SIZE.** 6
lines.

**SOURCE.** `EFF.HE7.15` + ANNEX R R3's rider (quoted at E.07's ⚠ note); `EFF.HE7.114` ("the
first level at which any new symbol … can appear is level 3, unreachable below n = 16
(THEOREM HE7.C)").

**TEETH.** `he7rannex_supp.py` (the n = 16 family, 79/79) → instance evidence for
non-vacuity of the threshold; the theorem is the necessary direction only.

**ENVIRONMENT.** ENV-E1.

---

## 10. §10 — GATES (GC-11: `q = 2` AND `q = 3`, the non-coincidence seam, `e > 1 ∧ f > 1`)

> Gates are leancheck-idiom concrete instances executed at the leanspec stub stage (GC-6.6(c))
> BEFORE the fleet fires. Numeric expectations below are recomputed fresh in this blueprint
> (shown per node); a mismatch at execution is a stop-the-line event. Per GC-8, retained
> executable regressions live under `verification/` named per node.

### NODE E.65 [gate] [fresh]

**STATEMENT.** *`q = 2`: the n = 8 frame end-to-end.* At `(e₁, f₁, h) = (2, 1, 1)`,
`ℓ = 2, d_r = 1` (the `EFF.HE7.57` frame): `#eval` checks — base rung `(2,1,1,0)`:
`bound₁ = 1`; level-2 rung `(2,1,u,2)` at `u = 5`: `nextT = 2·1·5 = 10`, `bound₂ = 7`;
`degAt`: `D′ = 2, D″ = 4`; the μ₂ = 2 dictionary values and degrees: `mu2Sigma` rows decided
= `{(8,1)}, {(4,2)}, {(4,1),(4,1)}` each of degree 8 (`mu2Sigma_degree`); the jump bounds at
`μ₀ = 4`: `J ≤ 1`, `μ₂ ≤ 2` (E.60). Expected values, recomputed fresh: `2^(J+1) ≤ 4 ⟹ J ≤ 1`
✓; `2·μ₂ ≤ 4 ⟹ μ₂ ≤ 2` ✓; `(2·1−1)·5 + 2·1 = 7` ✓.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder
-- E65 gate: #eval / example-decide block at q = 2 (the n = 8 frame).
example : (RungDatum.mk 2 1 5 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).nextBound 1 = 7 := by decide
-- + the mu2Sigma degree/alphabet decides, + degAt/nextT evaluations per the STATEMENT
```

**DEPENDS.** E.01, E.02, E.05, E.07, E.49, E.50, E.60.

**PROOF.** `decide`/`norm_num` per check. **SIZE.** 24 lines.

**SOURCE.** `EFF.HE7.57` (the frame); `EFF.HE7.23` TEETH (the Q3 threshold table's first two
frames); `EFF.HE7.58` (the dictionary).

**TEETH.** re-fires Q1/Q3's spot values as Lean-side `decide`s; retained regression:
`verification/chapE_gate_q2.py` (mirror of the checks, per GC-8).

**ENVIRONMENT.** ENV-E1.

---

### NODE E.66 [gate] [fresh]

**STATEMENT.** *`q = 3` AND the non-coincidence seam witness (honesty E-6).* Two batteries:
(i) at `q = 3`, the `(3, 1, 2)` frame (FINDING HE7-F1's own): `reachSet` computations —
`i₀(1)`-class arithmetic showing height `k = 1` UNATTAINED (`reachSet_empty_iff`:
`T(1) = ∅` at `i₀ = 2`: `2·2 = 4 > 1` ✓ — recomputed: `i₀(1)` solves `2i₀ ≡ 1 (mod 3)`,
`i₀ = 2`, `i₀h = 4 > 1` ✓); attainable heights `{3a + 2i} = {0, 2, 3, 4, 5, …}` spot-checked;
`bound₁ = (3·1−1)·2 = 4` ✓.
(ii) the NON-coincidence seam regime at `(e₁, f₁, h) = (2, 2, 3)` (`HYP.151`'s witness frame,
pushed PAST the coincidence bound `k ≤ (D′−1)h = 9`): at `k = 10`: `i₀(10)` with
`i₀·3 ≡ 10 (mod 2)` ⟹ `i₀ = 0`; `T(10) = {t < 2 : (0 + 2t)·3 ≤ 10} = {0, 1}` FULL, and
`k = 10 ≥ (D′−1)h + 1 = 10` — the first height past the coincidence regime; at `k = 11`:
`i₀ = 1`, `T(11) = {t : (1+2t)·3 ≤ 11} = {0, 1}` full ✓; seam-exponent integrality
(`seam_exp_dvd`) at these `k` — `#eval`s all. This gate exists BECAUSE four hostile rounds
missed HYP.151's defect inside the coincidence regime; the checks here sit outside it.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder
-- E66 gate: q = 3 + non-coincidence seam #eval/decide block per the STATEMENT.
example : reachSet 3 2 1 2 1 = ∅ := by decide
example : reachSet 2 3 2 0 10 = Finset.univ := by decide
-- + bound₁ = 4 at (3,1,2); + seam_exp_dvd instances at k = 10, 11
```

**DEPENDS.** E.02, E.25, E.30.

**PROOF.** `decide` per check. **SIZE.** 20 lines.

**SOURCE.** `EFF.HE7.21` (FINDING HE7-F1's two counterexample frames — the `(3,1,2)` and
`(2,2,1)` computations, machine-confirmed by HE7-T-LIFT2SHARP); `spec/HYPOTHESIS_LEDGER.md`
HYP.151 (the `(2,2,3)` witness and the sharp threshold `k > (D′−1)h = 9`); GC-11 (two primes,
executed pre-fleet).

**TEETH.** the coincidence-regime trap (HYP.151; G.23's class) → this gate is the mechanical
instrument GC-11 mandates; retained regression: `verification/chapE_gate_q3_seam.py`.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.67 [gate] [fresh]

**STATEMENT.** *The `e > 1 ∧ f > 1` witness.* The dictionary's row-2 value at the n = 8 frame
is `(e, f) = (4, 2)` — both `> 1` — and a level-2 frame with `d_r = 2` gives
`(e_𝒞, f_𝒞) = (e₁ℓ, f₁d_r)` with BOTH components `> 1` at `(e₁, f₁) = (2, 1), ℓ = 2, d_r = 2`:
`(4, 2)`. Checks: `LadderLeaf.ef`: leaf `⟨[(2,1)], (1,2)⟩` at base `(2,1)` evaluates to
`(2·2·1, 1·1·2) = (4, 2)` ✓; `ladderSigma_degree` on `{that leaf}` = `4·2 = 8` ✓;
`ef_forcing` fires at `(a,b) = (4,2)`, `e*f = 8` ✓; `ladderSigma_prepend` at the same data
(associativity spot check). GC-11's simultaneous-witness requirement is met INSIDE the
certified perimeter (the n = 8 box's row 2 is a real member class — Q1's battery contains
{(4,2)} members).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder
-- E67 gate:
example : (LadderLeaf.mk [(2,1)] (1,2)).ef 2 1 = (4, 2) := by decide
example : (ladderSigma 2 1 {LadderLeaf.mk [(2,1)] (1,2)}).degree = 8 := by
  simp [ladderSigma_degree]  -- + decide on the map/sum
-- + ef_forcing instance; + prepend spot check
```

**DEPENDS.** E.15, E.45, E.46, E.47, E.49.

**PROOF.** `decide`/`simp` per check. **SIZE.** 16 lines.

**SOURCE.** `EFF.HE7.58` row 2 (`{(4,2)}` — a certified alphabet letter with `e, f > 1`);
GC-11 (the CHAP-B §10 shape).

**TEETH.** Q1's `{(4,2)}` members (the letter occurs in the battery) → the gate re-fires the
value Lean-side; retained regression: `verification/chapE_gate_ef.py`.

**ENVIRONMENT.** ENV-E1.

---

### NODE E.68 [gate] [fresh]

**STATEMENT.** *The five-frame threshold regression (Q3's table as Lean `decide`s).* The bound
recursion `boundAt`/`nextBound` evaluated at the five Q3 frames `(e₁, f₁, h, ℓ, d_r, u)`,
against the spec's recorded thresholds: `(2,1,1,2,1,5) → 7`; `(2,1,1,2,2,5) → 17`;
`(2,2,1,2,2,7) → 27`; `(3,1,2,2,3,13) → 73`; `(1,2,1,3,2,11) → 58`. Recomputed fresh here:
`bound₁ = (e₁f₁−1)h` = `1, 1, 3, 4, 1`; `bound₂ = (ℓd_r−1)u + ℓ·bound₁` =
`(2−1)5+2 = 7 ✓, (4−1)5+2 = 17 ✓, (4−1)7+2·3 = 27 ✓, (6−1)13+2·4 = 73 ✓, (6−1)11+3·1 = 58 ✓`.
**All five recomputations match the spec's table exactly.** Plus the E.08 implication fired at
one frame (`(‡₂) ⟹ (†₂)` at `(2,2,5)`-rung, `b = 1`: `k = 17` gives `m₀ ≥ (2−1)·5 + 1 = 6` —
check `2m₀ + s₀·5 = 17, s₀ = 1 ⟹ m₀ = 6 ≥ 6` ✓ boundary-exact).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Ladder
-- E68 gate: the five-frame threshold table as decides on nextBound/boundAt.
example : (RungDatum.mk 2 2 5 1 _ _ _ _).nextBound 1 = 17 := by decide
-- … (all five frames; boundary-exact lift_threshold_step instance)
```

**DEPENDS.** E.02, E.05, E.08.

**PROOF.** `decide` ×6. **SIZE.** 18 lines.

**SOURCE.** `EFF.HE7.23` TEETH (the five-frame table, verbatim values); `EFF.HE7.22`
(sharpness — the gate checks sufficiency values only; the non-necessity half is the source's
enumeration evidence, §13).

**TEETH.** Q3/HE7-LIFT2 (ten frames, exhaustive) → the five threshold values become Lean
`decide`s; retained regression: `verification/chapE_gate_thresholds.py`.

**ENVIRONMENT.** ENV-E1.

---

<!-- RESUME: §§3–10 COMPLETE (all 68 nodes). Next: §11 DAG additions, §12 stub list, §13 census+TEETH, §14 cross-read flags. -->

*(closing sections follow)*
