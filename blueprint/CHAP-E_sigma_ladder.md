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

<!-- RESUME: §4 COMPLETE (E.10–E.24). Next: §5 (E.25–E.38, slot-seam evaluation layer). -->

*(sections §5–§14 follow)*
