# CHAPTER G — BASE CASES AND MENUS

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **G = BASE CASES AND MENUS**
(notes `HMENU3`, `HEX3`, `W11`, `JD0`; 223 DAG nodes; consumer-first order position last-but-one,
immediately above the landed Lean kernel `A`).
**Sources transcribed:** `spec/EFF-W11.md` (42 units), `spec/EFF-HMENU3.md` (72 units),
`spec/EFF-HEX3.md` (71 units). `JD0` is **not** transcribed here — see the honesty block, item H-7.
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle).
**Authored:** 2026-08-14, Opus arm (Asvin-authorized substitution #51). **CODEX CROSS-READ OWED.**

---

## 0. How to read this chapter

### 0.1 The three standing environments

Every node names its environment as `ENV-A`, `ENV-B` or `ENV-C` plus deltas. The three blocks are:

**ENV-A — the density arena (default).**

```lean
import Uniformity
namespace Uniformity.Density
open IsLocalRing Polynomial Filter Topology
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}
```

**ENV-B — ENV-A plus completeness** (needed by every node that lifts through Hensel):

```lean
variable [IsAdicComplete (maximalIdeal O) O]
```

**ENV-C — the residue-field arena** (pure finite-field counting, no `O`):

```lean
import Uniformity
namespace Uniformity.Density
open Polynomial
variable {K : Type*} [Field K] [Finite K]
```

`ENV-A'` abbreviates "ENV-A with `π` promoted to an explicit hypothesis `(hπ : Irreducible π)`",
which is how every node that names `π` actually takes it (the landed files use exactly this
pattern: `Drainage.lean:85`, `DensityAPI.lean:124`).

### 0.2 File layout and naming

* One Lean file per node: `leanfinal/Uniformity/G/G<nn>_<slug>.lean`, module
  `Uniformity.G.G<nn>_<slug>`.
* Chapter roll-up `leanfinal/Uniformity/G.lean` imports all node modules; `Uniformity.lean` gains
  one line `import Uniformity.G`.
* **Namespaces are the landed ones**: `Uniformity.Density` for everything about `typeOf` /
  `genuineDensity` / `Coeff`; `UniformityCheck` only where a landed contract name already lives
  there (`card_certSet_gen`). New *definitions* of this chapter live in the sub-namespace
  `Uniformity.Density.Menu` to keep the top-level namespace collision-free; new *theorems about
  landed objects* live directly in `Uniformity.Density`.
* One PUBLIC declaration per node (the contract declaration named in its SIGNATURE); private
  helpers may live below it in the same file. A helper that is reusable triggers a RE-PLAN
  request to the orchestrator, never a silent second public name.

### 0.3 Names that already exist and must not be redefined

The blueprint targets the **landed** API. The declarations below are consumed by name and never
re-proved: `FactorizationType`, `FactorizationType.degree`, `typeOf`, `typeOf_degree`,
`monicPoly`, `monicPoly_monic`, `monicPoly_natDegree`, `monicPoly_two_expand`,
`monicPoly_two_eval`, `monicPoly_two_deriv_eval`, `Coeff`, `Res`, `proj`, `proj_surjective`,
`resFactor`, `resFactor_surjective`, `card_res`, `card_coeff`, `residueCard`,
`two_le_residueCard`, `DecidedAt`, `PossibleAt`, `decidedSet`, `possibleSet`, `decidedCount`,
`possibleCount`, `decidedSeq`, `possibleSeq`, `decidedDensity`, `genuineDensity`, `gapSeq`,
`UndecidedVanishes`, `undecidedSet`, `undecidedCount`, `undecidedSeq`, `UndecidedAt`,
`CoveringMenu`, `decidedSet_disjoint`, `decidedSeq_le_decidedDensity`,
`genuineDensity_le_possibleSeq`, `sum_decidedDensity_le_one`, `one_le_sum_genuineDensity`,
`sum_genuineDensity_eq_one_of_drainage`, `genuineDensity_eq_of_drainage`,
`genuineDensity_eq_decidedDensity_two`, `drainage_two`, `typeOf_two_cases`, `coveringMenu_two`,
`linType`, `splitType`, `inertType`, `ramType`, `quadForm`, `Anisotropic`, `AniForm`,
`aniForm_iff`, `exists_aniForm`, `exists_anisotropic`, `rootPairMap`, `rootPairMap_injective`,
`exists_rootPairMap_iff`, `qval`, `qder`, `qval_shift`, `qder_shift`, `Tang`, `Tang_mono`,
`CertSplit`, `CertRam`, `CertInert`, `typeOf_of_certSplit`, `typeOf_of_certRam`,
`typeOf_of_certInert`, `cert_of_not_tang`, `decidedAt_of_not_tang`, `class_pinned`,
`undecidedCount_le`, `gapSeq_le_undecidedSeq`, `mem_maximalIdeal_pow_iff_dvd`,
`pow_dvd_iff_le_addVal`, `addVal_eq_of_dvd_not_dvd`, `pow_dvd_right_of_mul`,
`isUnit_of_not_dvd`, `exists_roots_of_not_irreducible`, `typeOf_mul_linear`,
`typeOf_split_of_root`, `typeOf_ram_of_eisenstein`, `typeOf_inert_of_anisotropic`,
`exists_residual_root`, `not_dvd_of_anisotropic`, `proj_eq_iff_dvd`, `decidedAt_of_congr`,
`decidedDensity_ge_of_subset`, `genuineDensity_le_of_superset`, `drainage_of_undecided_comp`,
`gapSeq_antitone_general`, `card_certSet_gen`, `towerSection`, `resFactor_towerSection`,
`typeOf_mul`, `monicFactors_mul`, `typeOf_prod_X_sub_C`, `typeOf_of_residual_coprime`,
`typeOf_eisenstein`, `typeOf_inert_of_irreducible_map`, `norm_adjoinRoot_root`,
`exists_coveringMenu`, `efPair_pos_of_mem`, `efPair_mul_le_natDegree`,
`exists_monic_factorization_finset`, `exists_monic_scaleRoots`, `dvd_sub_coeff_of_scaleRoots`,
`exists_monicPoly_eq`, `typeOf_shift`, `typeOf_scaleRoots`, `typeOf_scale`,
`FactorizationType.degree_mk_add`, `UniformityStatement`, `TotalMassOne`, `DrainageAt`.

### 0.4 The chapter's mathematical spine, in one page

The chapter re-derives, **inside `leanfinal`'s own definitions**, the base-case content of W-11
(degree 2, complete), of HMENU3 (degree 3, menu) and of HEX3 (the exact residue law). It does so
through one organising object that the corpus states in OM-classifier language and that the Lean
kernel already carries in engine-free form: the **tangency-depth filtration** at `n = 2`
(`Tang`, `Drainage.lean:511`).

Write `F(γ) = qval a γ = γ² + a₁γ + a₀` and `F'(γ) = qder a γ = 2γ + a₁`. `Tang π a t γ` says
`π^t ∣ F(γ)` and `π^⌈t/2⌉ ∣ F'(γ)`. For a level-`N` class `c` put

    tangSet π N t = { c : Coeff O 2 N | some (hence every) lift has a centre of depth ≥ t }.

The chapter proves, at general `O`, both characteristics, no `q`-parity or tameness hypothesis:

| result | statement | node |
|---|---|---|
| the filtration count | `#(tangSet π N t) = q^(2N−t)` for `t ≤ N` | G.17 |
| depth strata | `#(depthSet π N t) = (q−1)·q^(2N−t−1)` for `t < N` | G.20 |
| odd depth ⟹ RAM | every class of odd depth `t < N` is `ramType`-decided | G.24, G.25 |
| even depth ⟹ residual dichotomy | anisotropic residual ⟹ INERT, separable-split residual ⟹ SPLIT, no third case | G.26, G.27, G.28 |
| the residue census | `#{anisotropic pairs} = #{distinct-root pairs} = q(q−1)/2`, `#{double-root pairs} = q` | G.38–G.40 |
| **the exact drainage law** | `undecidedCount O 2 N = q^N` | G.36 |
| **every-window split = inert** | `decidedCount O 2 splitType N = decidedCount O 2 inertType N` | G.43 |
| **the exact densities** | `split = inert = q/(2(q+1))`, `ram = 1/(q+1)`, `Σ = 1` | G.46–G.49 |
| **the capstone at `n = 2`** | the `n = 2` slice of `UniformityStatement`, unconditional | G.51 |

Every W-11 number is reproduced. The dictionary between W-11's seven families (`EFF.W11.07`) and
the depth filtration is:

| W-11 family (`EFF.W11.07`) | depth-filtration description | W-11 whole-space count (`EFF.W11.09`) | this chapter |
|---|---|---|---|
| SEP-SPLIT | depth `0`, residual pair with two distinct roots | `((q²−q)/2)·q^(2N−2)` | G.28 + G.42 (`k = 0`) |
| SEP-INERT | depth `0`, residual pair anisotropic | `((q²−q)/2)·q^(2N−2)` | G.27 + G.41 (`k = 0`) |
| RAM(h), `h` odd | depth exactly `h` | `q·(q−1)q^(2N−h−2) = (q−1)q^(2N−h−1)` | G.20 + G.25 |
| 2SIDED(w₁,w₂) | depth `2w₁`, residual pair with two distinct roots, one of them `0` at the deeper read | (inside the depth-`2w₁` split stratum) | G.28 |
| SPLITEQ(k) | depth `2k`, residual pair with two distinct **nonzero** roots | (inside the depth-`2k` split stratum) | G.28 |
| INERTDEEP(k) | depth exactly `2k`, residual anisotropic | `q·((q−1)/2)q^(2N−2k−2)` | G.27 + G.41 |
| SPLIT-TAIL(w) | depth `2w` classes whose value is hidden past the window | (inside the depth-`2w` split stratum) | G.28 |

**Why the filtration is finer than the family list is coarse.** W-11's clause (ii) counts each
family separately and its clause (iii) sums them; C7-F1 (`EFF.W11.08`) then re-types SPLIT-TAIL as
a *window cell*, not a `typeOf` key, precisely because its members' shapes are not determined by
the window. The depth filtration never needs that distinction: it keys strata by
`(depth, residual class)`, which **is** determined by the window, and the σ-value is determined by
the residual class alone. 2SIDED, SPLITEQ and SPLIT-TAIL all land in the *same* stratum
(`depth = 2k`, residual separable-split) and the chapter never has to separate them — which is
exactly why the every-window `split = inert` identity, which W-11 needs a finite telescope for
(`EFF.W11.27`, an identity the note itself transcribes from a pass report), becomes here the
one-line residue-field fact `#{anisotropic} = #{distinct-root} = q(q−1)/2`.

At `n = 3` the same organising idea is the **species partition** of HEX3's LEMMA H-1
(`EFF.HEX3.13`) and it is *not* completed in this chapter: see the honesty block.

---

## 1. HONESTY BLOCK (read before consuming any node)

**H-1 — what this chapter does NOT prove.** The `n = 3` exact conservative-residue law
(THEOREM HEX3.A, `EFF.HEX3.08`) is **not** a chapter-G Lean deliverable. Chapter G lands its
**arithmetic layer** in full and unconditionally (the recursions `R`, `u`, the telescoping
identity, the vanishing bound — nodes G.65–G.72, which are statements about `ℕ`- and
`ℚ`-valued recursions and consume no `O` at all), and it lands the **σ-undecided lower bound**
`q^N ≤ undecidedCount O 3 N` (G.76). The bridge that would turn the arithmetic layer into a
statement about `undecidedCount O 3 N` — i.e. the Lean analogue of HEX3's LEMMA H-1 partition,
H-2 shear and H-3 block re-entry — is **out of chapter-G scope** and is the named frontier.
Consequently **no node of this chapter proves `DrainageAt 3`**, and every `n = 3` total-mass
statement here (G.53) carries drainage as an explicit hypothesis.

**H-2 — `HEX3-BOX-1` / ledger `HYP.137` is an EXPLICIT NON-NODE.** The tail-σ-certification
lemma ("when does a `B₀ = 0` exit state's visible data pin σ for all `disc ≠ 0` lifts?",
`EFF.HEX3.37`) has **no node in this chapter and must not be given one**. Its ledger disposition
is disclosure-without-promotion: it is *not* a conjunct of the capstone's hypothesis block,
because the `(hExhaust-3)` discharge provably never needed it (`HEX3` L692–693, quoted in
`EFF.HMENU3.30`), and its only live consumer is GENIND's S8.2 W-12.B corroboration aside. Chapter
G inherits that disposition unchanged: the `n = 3` bound this chapter's frontier would deliver is
the **conservative** one, which is an upper bound for the σ-residue by `EFF.HEX3.06`
(`U₃^σ ≤ U₃^conv`), and that inequality is all any downstream drainage consumer uses. A fleet
agent who finds itself needing the tail-σ lemma has left the chapter and must return
`BLOCKED: HYP.137` rather than assume it.

**H-3 — the `n = 3` menu is proved only at its SEP and leaf tiers.** HMENU3's THEOREM HM3.B
(`EFF.HMENU3.11`) with ANNEX B's **53 formal families** (`EFF.HMENU3.67`, `.69`; 11 tier-I + 11
tier-II + 24 B-tier + 4 DBL + 3 SEP) is transcribed here as a **family-index type with a proved
cardinality** (G.62–G.64) and a **uniform certificate schema** (G.05–G.08), not as 53 proved
counts. Chapter G proves the certificates and exact level-`N` counts for the **three SEP families
and the two ramified leaves** (G.55–G.61). The deep tiers (α-prefix histories, the three β
routes) are schema instances whose *count* obligations are chapter-G-out-of-scope, for the same
reason as H-1: they consume the H-2/H-3 transports.

**H-4 — COROLLARY HM3.D's five cubic densities are NOT claimed here.** The five closed forms
`R_τ(q)` with `Φ = q⁴+q³+q²+q+1` (`EFF.HMENU3.17`) rest on W-12.D's Steps 1–4 applied to the full
menu; chapter G proves the *type list* (exactly five types occur, G.49–G.50), the *menu*
(`CoveringMenu O 3`, G.51), the SEP-tier *lower bounds* (G.61), and `Σ_τ R_τ = 1` **given**
drainage (G.53). The five exact values are a chapter-H/J deliverable and are recorded here only
as the target the chapter's lower bounds must eventually meet.

**H-5 — the `n = 2` results are unconditional, and that is the chapter's load.** Everything in
§§1–4 (nodes G.09–G.51) is proved from Lean core over the standing bundle, with no axiom, no
hypothesis-carrying, no tameness and no residue-characteristic restriction. In particular the
exact `n = 2` drainage rate `q^(−N)` (G.37) **sharpens** the landed `drainage_two`
(`Drainage.lean:838`), whose supporting bound `undecidedCount O 2 (2M) ≤ q^(3M)`
(`Drainage.lean:757`) is lossy by a factor `q^M` — the landed file says so itself
("The count `q^(3M)` is deliberately lossy: W-11's exact law is `q^N` undecided classes at level
`N`"). Chapter G closes exactly that gap.

**H-6 — the COARSE DAG edges this chapter refines.** `spec/DAG.tsv` carries chapter-G edges whose
endpoints are governing-unit placeholders (`resolution=…gov`), notably every edge landing on
`EFF.HEX3.08`, `EFF.HMENU3.08` and `EFF.W11.07` from another note. The node-level DEPENDS fields
below are the first statement-level dependency structure for this material (`spec/DAG_README.md`:
"no intra-note dependency edges exist" — 65% of nodes isolated). The chapter's DAG additions
(§10) are therefore *new* edges, not re-resolutions of old ones, and they do not silently retire
any COARSE edge: the coarse rows stay for the cross-read.

**H-7 — `JD0` is in the chapter cut but not in this file.** The 0c cut assigns `JD0` to chapter G.
`JD0`'s count-blindness content is consumed here only as a *frame*: both W-11 (`EFF.W11.16`,
NON-IMPORT N-8: "J-D0 is a frame, not a premise, at the instance") and HEX3 (`EFF.HEX3` N-6:
"corroborated, not load-bearing for the counts") state that their censuses are proved directly.
This chapter's residue-census nodes (G.38–G.40) are likewise proved directly and are
characteristic-uniform *as theorems*, which is the Lean content of the gauge-blindness claim. A
separate JD0 transcription unit is owed; it is **not** blocked by anything here.

**H-8 — codex-cross-read status: OWED.** Like every 0a/0b/0c artifact of this week, this chapter
is Opus-authored and has **not** been cross-read by codex. The specific items flagged for that
read are listed in §12.

**H-9 — `leancheck` is EVIDENCE and a RE-DERIVATION TARGET, never an import.** The `n ≤ 3` layer
in `leancheck/UniformityCheck/` (21 files, 5,344 lines, zero `sorry`, Lean-core axioms) already
carries, **at general `O` over the standing bundle**, a complete `n = 2` exact-density census and a
substantial `n = 3` layer. Chapter G's nodes re-derive the relevant parts in `leanfinal`. Two
consequences a fleet agent must hold simultaneously:

* *Feasibility is not in doubt* for every node marked **RE-DERIVATION TARGET**: a working proof of
  the same statement exists, with a known size. Those nodes are the chapter's low-risk mass.
* *The leancheck text is not a licence.* `leancheck` imports `leanfinal`; the dependency cannot be
  reversed, and its declarations live in a different namespace with (sometimes) different
  statement shapes. A node is DONE only when proved in `leanfinal` from `leanfinal`'s API.

The specific already-landed leancheck results this chapter re-derives are named per node. The
headline ones: `Counting.card_certSet` (the `n = 2` census lemma), `RamCensus.card_ramSet`,
`InertCensus.card_inertSet`, `AniCount.card_aniPairSet`, `FiniteFieldQuad.two_mul_card_aniK`,
`N2Base.decidedDensity_of_census`, `N2Exact.{ram,inert,split}_decidedDensity_two`,
`N2Exact.density_two_exact`, `N3Base.{c3split,c3linInert,c3inert,c3linRam,c3ram}`,
`N3Struct.cubic_trichotomy`, `N3Struct.cubic_structure`, `N3Certs.*`,
`N3Norm.typeOf_ram3_of_eisenstein`, `CubicCount.three_mul_card_noRootCubic`,
`SplitCount.six_mul_card_split3`, `N3Gates.lowers_three`, `N3Drain.drainage_three_of_triple`,
`N3Exact.decidedCount_inert3_one`.

**H-10 — what is genuinely NEW in this chapter (not in `leancheck`, not in `leanfinal`).** Four
things, and they are the chapter's actual mathematical content:
1. the **exact** `n = 2` drainage law `undecidedCount O 2 N = q^N` (G.36) — `leanfinal` and
   `leancheck` both carry only the lossy `≤ q^(3M)` at level `2M`;
2. the **every-window count** identity `decidedCount split N = decidedCount inert N` (G.43) —
   `leancheck` has the *density* identity only, obtained by subtraction, which is strictly weaker;
3. `typeOf_three_cases` and the explicit cubic `CoveringMenu` (G.52–G.54) — `leancheck`'s
   `N3Drain` docstring names the missing `n = 3` analogue of `typeOf_two_cases` as an open item;
4. the HEX3 **arithmetic layer** (`R`, `u`, the telescoping identity, the vanishing bound;
   G.65–G.72) — nowhere in either repo.

---

## 2. NODE INDEX

| § | nodes | content |
|---|---|---|
| 3 | G.01–G.08 | chapter primitives + the certificate schema |
| 4 | G.09–G.23 | `n = 2`: the tangency filtration and its exact level census |
| 5 | G.24–G.31 | `n = 2`: type classification by depth |
| 6 | G.32–G.37 | `n = 2`: the exact drainage law `undecidedCount = q^N` |
| 7 | G.38–G.51 | `n = 2`: exact counts, exact densities, the capstone slice |
| 8 | G.52–G.61 | `n = 3`: the five types, the menu, the leaf certificates |
| 9 | G.62–G.72 | `n = 3`: the 53-family index and the HEX3 arithmetic layer |
| 10 | G.73–G.78 | `n = 3`: the σ-undecided lower bound and the conditional assembly |

**Kind census:** 13 `def`, 43 `lemma`, 19 `theorem`, 3 `gate` — **78 nodes**.
**Landed-node census:** 0 nodes are `landed:` (chapter G adds no re-labels of existing
declarations); 34 distinct landed declarations are consumed by name across the DEPENDS fields.
**Split-mandated nodes** (the fleet will see more than 78 units of work): G.60 → 3, G.61 → 5+1,
G.67 → 2, G.69 → 2, G.75 → 2, plus the split *candidates* flagged at G.02, G.07, G.11, G.17,
G.18, G.23, G.34, G.42, G.44, G.65. Planning figure for the fleet: **≈ 90 Lean files.**

**Graph shape** (computed from the DEPENDS fields, `spec/DAG_BLUEPRINT_G.tsv`): 137 intra-chapter
edges, **acyclic**, **critical path 13**, layer widths
`19, 22, 12, 7, 3, 3, 2, 2, 2, 1, 1, 1, 2`. Nineteen nodes are fireable immediately (they depend
only on landed API). The critical path runs
`G.01 → G.02 → G.11 → G.18 → G.17 → G.20 → G.23 → G.41 → G.43 → G.47 → G.48 → G.51`, i.e. through
the census spine to the capstone slice — that chain is the chapter's schedule risk, and G.23 (the
node with the declared proof-route defect) sits in the middle of it.

---

## 3. §3 — CHAPTER PRIMITIVES AND THE CERTIFICATE SCHEMA

### NODE G.01 [def] [fresh]

**STATEMENT.** For `π` in a DVR `O`, `k : ℕ` and `x : O`, say `x` has *exact valuation* `k`
when `π^k ∣ x` and `¬ π^(k+1) ∣ x`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- `ExactVal π k x` : `x` has valuation exactly `k` with respect to the uniformizer `π`. -/
def ExactVal (π : O) (k : ℕ) (x : O) : Prop := π ^ k ∣ x ∧ ¬ π ^ (k + 1) ∣ x
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 4 lines.

**SOURCE.** `EFF.W11.15` (the node trichotomy reads `u = v(A₀)`, `w = v(A₁)` as exact
valuations); `EFF.HEX3.13` (every H-1 species locus is phrased by an exact valuation).

**TEETH.** none (a definition; guarded through its consumers).

**ENVIRONMENT.** ENV-A.

---

### NODE G.02 [lemma] [fresh]

**STATEMENT.** `ExactVal π k x` holds iff `x ≠ 0` and `addVal O x = k`; and `ExactVal π k x`
with `ExactVal π k' x` forces `k = k'`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem exactVal_iff_addVal (hπ : Irreducible π) {k : ℕ} {x : O} :
    ExactVal π k x ↔ IsDiscreteValuationRing.addVal O x = (k : ℕ∞)

theorem exactVal_unique (hπ : Irreducible π) {k k' : ℕ} {x : O}
    (h : ExactVal π k x) (h' : ExactVal π k' x) : k = k'
```

**DEPENDS.** G.01 · landed `Uniformity.Density.addVal_eq_of_dvd_not_dvd`
(`Drainage.lean:101`), `Uniformity.Density.pow_dvd_iff_le` (`Drainage.lean:95`),
`Uniformity.Density.exists_addVal_eq` (`Drainage.lean:90`).

**PROOF.**
1. (→) unfold `ExactVal`; apply `addVal_eq_of_dvd_not_dvd hπ h.1 h.2`.
2. (←) from `addVal O x = k` get `π^k ∣ x` by `pow_dvd_iff_le hπ h k |>.2 (le_refl k)`.
3. and `¬ π^(k+1) ∣ x` by `pow_dvd_iff_le hπ h (k+1)`, whose right side is `k+1 ≤ k`, false by
   `Nat.not_succ_le_self`.
4. `exactVal_unique`: rewrite both through step 1 and use `Nat.cast_injective` on `ℕ∞`.

**SIZE.** 14 lines. **Two public declarations** — permitted here because they are the same fact
in two shapes and every consumer needs both; if the merge queue objects, `exactVal_unique` moves
to a private helper of G.13 and G.19.

**SOURCE.** `EFF.W11.15`; `EFF.HEX3.13`.

**TEETH.** `W11-CENSUS` (`EFF.W11.34`, executable regression; every `(leaf,params)` key it checks
is an exact-valuation key) → **Lean theorem** (this node is the exact-valuation primitive those
keys are stated in).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.03 [def] [fresh]

**STATEMENT.** At a level-`N` centre class `γ : Res O N`, re-coordinatise the level-`N` coefficient
box of monic quadratics by the pair (value at `γ`, derivative at `γ`): the map
`(a₀, a₁) ↦ (γ² + a₁γ + a₀, 2γ + a₁)` is a bijection of `(O ⧸ 𝔪^N)²`, because each coordinate is a
translation once the other is fixed.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The `(value, derivative)` re-coordinatisation of the level-`N` box at the centre class `γ`. -/
def readEquiv {N : ℕ} (γ : Res O N) : Coeff O 2 N ≃ (Res O N × Res O N) where
  toFun c := (c 0 + c 1 * γ + γ ^ 2, 2 * γ + c 1)
  invFun p := ![p.1 - (p.2 - 2 * γ) * γ - γ ^ 2, p.2 - 2 * γ]
  left_inv := by intro c; funext i; fin_cases i <;> simp <;> ring
  right_inv := by intro p; simp <;> ring
```

**DEPENDS.** landed `Uniformity.Density.Coeff`, `Uniformity.Density.Res` (`LocalData.lean:75,131`).

**PROOF.** definitional; `left_inv`/`right_inv` are `ring` after `fin_cases`.

**SIZE.** 12 lines. If the `Matrix.cons` normal forms fight `simp`, split the two inverse
identities into private helper lemmas over `Fin 2 → Res O N` first.

**⚠ RE-DERIVATION TARGET.** `leancheck/UniformityCheck/Counting.lean` lands exactly this
declaration (`readEquiv (γ : Res O N) : Coeff O 2 N ≃ Res O N × Res O N`) and it is consumed by
both landed censuses there. Chapter G re-derives it in `leanfinal`; the leancheck text is
**evidence of feasibility and a permitted reference**, never an import (`leancheck` imports
`leanfinal`, not conversely). The centre argument is at `Res O N`, not `O`, precisely because
`UniformityCheck.card_certSet_gen` takes `read : Res O N → (Coeff O n N ≃ D)`.

**SOURCE.** `EFF.W11.14` (the per-centre recentering, "a measure-preserving bijection per
centre"); `EFF.W11.15` (the read is on `(u, w) = (v(A₀), v(A₁))` after recentering).

**TEETH.** `W11-W10TIE` (`EFF.W11.34`, executable regression; the recentering bijection is the
object it ties pointwise) → **Lean theorem** (this node *is* the bijection, now proved rather than
cited).

**ENVIRONMENT.** ENV-A.

---

### NODE G.04 [lemma] [fresh]

**STATEMENT.** `readEquiv` computes the value and derivative of any lift: if `proj O 2 N a = c`
and `γ` is the class of `g : O`, then the two coordinates of `readEquiv γ c` are the classes of
`qval a g` and `qder a g`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem readEquiv_proj {N : ℕ} (g : O) (a : Fin 2 → O) :
    readEquiv (Ideal.Quotient.mk _ g) (proj O 2 N a)
      = (Ideal.Quotient.mk _ (qval a g), Ideal.Quotient.mk _ (qder a g))
```

**DEPENDS.** G.03 · landed `Uniformity.Density.qval`, `Uniformity.Density.qder`
(`Drainage.lean:206,209`), `Uniformity.Density.proj` (`LocalData.lean:136`).

**PROOF.**
1. unfold `readEquiv`, `proj`, `qval`, `qder`.
2. both coordinates are ring-hom images of polynomial expressions in `a 0`, `a 1`, `g`;
   `Prod.ext` then `map_add`/`map_mul`/`map_pow`; close by `ring`.

**SIZE.** 10 lines. **RE-DERIVATION TARGET:** `leancheck` lands `readEquiv_proj` in the same
shape.

**SOURCE.** `EFF.W11.15`.

**TEETH.** signed non-applicable (a compatibility identity; no battery row reads it).

**ENVIRONMENT.** ENV-A.

---

### NODE G.05 [def] [fresh]

**STATEMENT.** *The certificate schema.* A **level-`N` certified family** over `O` consists of:
a centre-modulus `m ≤ N`; a centre-indexed certificate `cert : O → Coeff O n N → Prop`; a
splitting type `σ`; a target type `D` with a centre-indexed bijection `read : O → (Coeff O n N ≃ D)`
and an admissible set `S : Set D`; subject to
(i) *readability*: `cert γ c ↔ read γ c ∈ S`;
(ii) *shift-stability*: `cert γ c → γ' ≡ γ (mod 𝔪^m) → cert γ' c`;
(iii) *centre-uniqueness*: `cert γ c → cert γ' c → γ' ≡ γ (mod 𝔪^m)`;
(iv) *forcing*: `cert γ (proj O n N a) → typeOf (monicPoly a) = σ`.
Its **certified set** is `{c | ∃ γ, cert γ c}`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- A level-`N` certified family: a centre-indexed certificate that (i) reads through a
bijection, (ii) survives centre moves inside a fixed coset, (iii) pins the centre's coset, and
(iv) forces one splitting type on every lift. -/
structure CertFamily (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (n N : ℕ) where
  m : ℕ
  hm : m ≤ N
  D : Type
  cert : Res O N → Coeff O n N → Prop
  read : Res O N → (Coeff O n N ≃ D)
  S : Set D
  σ : FactorizationType
  hcert : ∀ γ c, cert γ c ↔ read γ c ∈ S
  hshift : ∀ γ γ' c, cert γ c → resFactor (O := O) hm γ' = resFactor hm γ → cert γ' c
  huniq : ∀ γ γ' c, cert γ c → cert γ' c → resFactor (O := O) hm γ' = resFactor hm γ
  hforce : ∀ γ (a : Fin n → O), cert γ (proj O n N a) → typeOf (monicPoly a) = σ

/-- The set of level-`N` classes certified by some centre. -/
def CertFamily.set {n N : ℕ} (F : CertFamily O n N) : Set (Coeff O n N) := {c | ∃ γ, F.cert γ c}
```

**⚠ SIGNATURE NOTE (centres live at `Res O N`).** All four hypothesis fields quantify centres at
`Res O N`, matching `card_certSet_gen`. An instance whose certificate is naturally stated at an
`O`-centre (as `CertRam`, `CertInert` are) discharges `hcert`/`hforce` by choosing an `O`-lift of
`γ` — the standard move in `leancheck`'s `ramCert_iff` / `inertCert_iff`, which is exactly this
up/down window transfer (28 lines there, the largest support lemma of either census file).

**DEPENDS.** landed `Uniformity.Density.Coeff`, `Res`, `resFactor`, `proj`, `monicPoly`, `typeOf`,
`FactorizationType`.

**PROOF.** definitional.

**SIZE.** 32 lines.

**SOURCE.** the schema is the blueprint's own organisation of `EFF.W11.07`/`.09` (family = shape
data + σ + exact count) and `EFF.HMENU3.11`/`.13` (the (A1)-admissibility contract: "parameter set
a shifted product of arithmetic progressions … one `c_F(q)` per family … Disjointness: aggregation
collects disjoint raw-key fibers of the deterministic read"). The four fields (i)–(iv) are exactly
the hypotheses `UniformityCheck.card_certSet_gen` (`CensusGen.lean:64`) already demands, plus the
forcing clause `decidedAt_of_congr` (`DensityAPI.lean:140`) already demands.

**TEETH.** `HM3-AGG` (`EFF.HMENU3.44`, executable regression, "both directions on every row") →
**Lean theorem** at G.07 (the count law) and G.06 (the decidedness law); this node is their
common interface.

**ENVIRONMENT.** ENV-A. `D : Type` is deliberately at universe 0 (every instance in this chapter
uses `Res O N × Res O N` or a `Finset`-indexed type, all in `Type`), matching
`card_certSet_gen`'s `{D : Type*}` at the instantiation.

---

### NODE G.06 [lemma] [fresh]

**STATEMENT.** Every class of a certified family's set is `σ`-decided at level `N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem CertFamily.decidedAt {n N : ℕ} (F : CertFamily O n N) {c : Coeff O n N}
    (hc : c ∈ F.set) : DecidedAt O n F.σ N c
```

**DEPENDS.** G.05 · landed `Uniformity.Density.DecidedAt` (`GenuineDensity.lean:66`),
`Uniformity.Density.proj_surjective` (`LocalData.lean:138`).

**PROOF.**
1. `obtain ⟨γ, hγ⟩ := hc`.
2. `intro a ha` (so `proj O n N a = c`).
3. rewrite `hγ` along `ha.symm` to get `F.cert γ (proj O n N a)`.
4. conclude by `F.hforce γ a`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.W11.15` (each decided leaf's certificate reads only in-window data, so it
transfers to every lift); `EFF.HMENU3.28` (A0), read in ANNEX A's corrected form — see the note
below.

**NOTE (transcription fidelity, mandatory).** HMENU3's (A0) is `disc ≠ 0`-restricted: ANNEX A
(`EFF.HMENU3.14`, `.28`) reads "Ore certifies EVERY lift" as "every lift **with `disc ≠ 0`**",
and ANNEX C insists this is a *strict weakening*, not a clarification. The Lean schema field
`hforce` is **not** the corpus's Ore clause and carries no `disc ≠ 0` restriction: it is a
hypothesis each instance must discharge for *all* lifts by its own certificate, which the
`n = 2` instances of §5 do (they are valuation-theoretic, not Ore-theoretic, and `typeOf` is
total). No instance in this chapter may be justified by citing HMENU3's (A0).

**TEETH.** `HM3-ORACLE` (`EFF.HMENU3.47`, `[IND]` PARI leg, mixed characteristic only) →
**signed non-applicability**: the oracle is characteristic-blind by construction
(`EFF.HMENU3.65`: "blind, not wrong"), so it evidences no clause of this node; the node's content
is carried by its own proof.

**ENVIRONMENT.** ENV-A.

---

### NODE G.07 [lemma] [fresh]

**STATEMENT.** *The family count law.* A certified family's set has exactly `q^m · #S` members.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem CertFamily.card {n N : ℕ} (F : CertFamily O n N) :
    Nat.card F.set = residueCard O ^ F.m * Nat.card F.S
```

**DEPENDS.** G.05 · landed `UniformityCheck.card_certSet_gen` (`CensusGen.lean:64`).

**PROOF.**
1. unfold `CertFamily.set`.
2. `exact card_certSet_gen F.hm F.read F.S F.cert F.hcert F.hshift F.huniq`.

**SIZE.** 8 lines. The schema's four fields were chosen to be *literally* `card_certSet_gen`'s
hypotheses, so this node is the one-line application; all the work is in the instances.
**Feasibility evidence:** `leancheck`'s own `card_certSet` (`Counting.lean:228`, 33 lines,
6 `have`s) is the `n = 2`, `D = Res O N × Res O N` instance of the same statement, and both of its
consumers (`card_ramSet`, `card_inertSet`) apply it in exactly this one-step way.

**SOURCE.** `EFF.W11.09` (every window-visible row's count is one `q`-polynomial, exact);
`EFF.W11.25` (the per-centre × centre-count convention); `EFF.HEX3.13` ("Every letter/pin count
above is a digit-slot count").

**TEETH.** `W11-CENSUS` / P-2 (`EFF.W11.35`, 0 violations on 30 rows) → **Lean theorem** (this is
the general law those 375 checks instantiate). `HEX3-SPECIES` (`EFF.HEX3.46`, both directions) →
**Lean theorem**, same reason.

**ENVIRONMENT.** ENV-A.

---

### NODE G.08 [lemma] [fresh]

**STATEMENT.** A certified family gives a density lower bound: `q^m·#S / q^(n·N) ≤ decidedDensity O n σ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem CertFamily.decidedDensity_ge {n N : ℕ} (F : CertFamily O n N) :
    ((residueCard O : ℝ) ^ F.m * (Nat.card F.S : ℝ)) / (residueCard O : ℝ) ^ (n * N)
      ≤ decidedDensity O n F.σ
```

**DEPENDS.** G.06, G.07 · landed `Uniformity.Density.decidedDensity_ge_of_subset`
(`DensityAPI.lean:160`).

**PROOF.**
1. `have hsub : F.set ⊆ decidedSet O n F.σ N := fun c hc => F.decidedAt hc` (G.06).
2. `have := decidedDensity_ge_of_subset hsub`.
3. rewrite `Nat.card F.set` by G.07; `push_cast`; `exact this`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.W11.07` (the per-row limit densities are the `N → ∞` values of exactly these
ratios); `EFF.HMENU3.11`.

**TEETH.** `HM3-RTAU` (`EFF.HMENU3.48`, symbolic, guards the densities) → **executable
regression** retained at `verification/` (the symbolic sum is not re-done in Lean at this node).

**ENVIRONMENT.** ENV-A.

---

## 4. §4 — `n = 2`: THE TANGENCY FILTRATION AND ITS EXACT LEVEL CENSUS

### NODE G.09 [def] [fresh]

**STATEMENT.** `tangSet π N t` is the set of level-`N` classes having a lift with a centre of
tangency depth at least `t`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- Level-`N` classes admitting a lift with a centre of tangency depth `≥ t`. -/
def tangSet (π : O) (N t : ℕ) : Set (Coeff O 2 N) :=
  {c | ∃ a : Fin 2 → O, proj O 2 N a = c ∧ ∃ γ : O, Tang π a t γ}
```

**DEPENDS.** landed `Uniformity.Density.Tang` (`Drainage.lean:511`), `proj`.

**PROOF.** definitional.

**SIZE.** 5 lines.

**SOURCE.** `EFF.W11.22` (the σ-undecided residue is `{A₀ ≡ 0 mod π^N, w > (N−1)/2}` per node
instance — precisely `Tang` at depth `N`); `EFF.W11.26` (the drainage law counts exactly these).

**TEETH.** `W11-EXHAUST` / P-4 (`EFF.W11.35`, "undecided = q^N EXACTLY on all 30 rows") →
**Lean theorem** at G.36; this node is the object counted there.

**ENVIRONMENT.** ENV-A.

---

### NODE G.10 [lemma] [fresh]

**STATEMENT.** *Centre-shift stability.* If `γ` has depth `≥ t` for `a` and `π^⌈t/2⌉ ∣ (γ' − γ)`,
then `γ'` has depth `≥ t` for `a`. (`⌈t/2⌉` is `(t+1)/2` in `ℕ`-division.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem tang_shift {a : Fin 2 → O} {t : ℕ} {γ γ' : O} (h : Tang π a t γ)
    (hδ : π ^ ((t + 1) / 2) ∣ (γ' - γ)) : Tang π a t γ'
```

**DEPENDS.** landed `Uniformity.Density.Tang`, `Uniformity.Density.qval_shift`
(`Drainage.lean:214`), `Uniformity.Density.qder_shift` (`Drainage.lean:218`).

**PROOF.**
1. `obtain ⟨δ, hδ'⟩ := hδ`; note `γ' = γ + δ*π^((t+1)/2)`; write `s := δ * π^((t+1)/2)`, so
   `π^((t+1)/2) ∣ s`.
2. `qval a (γ + s) = qval a γ + qder a γ * s + s^2` by `qval_shift`.
3. `π^t ∣ qval a γ` by `h.1`.
4. `π^t ∣ qder a γ * s`: `π^((t+1)/2) ∣ qder a γ` by `h.2` and `π^((t+1)/2) ∣ s`, so the product
   is divisible by `π^(2*((t+1)/2))`, and `t ≤ 2*((t+1)/2)` by `omega`.
5. `π^t ∣ s^2` by the same exponent inequality.
6. add: `π^t ∣ qval a (γ + s)`.
7. `qder a (γ + s) = qder a γ + 2*s` by `qder_shift`; both summands are divisible by
   `π^((t+1)/2)`.
8. assemble `⟨_, _⟩`.

**SIZE.** 22 lines.

**SOURCE.** `EFF.W11.20` (the refinement isomorphism: "recenter by `s = z·π^k` … the map is
affine invertible"; the shift-stability is the half that says the locus is a union of cosets);
`EFF.HEX3.14` ("the chain recenters by `s = ẑπ^m` … depths strictly increase").

**TEETH.** `W11-CENSUS` (history-depth census, `EFF.W11.34`) → **Lean theorem**.

**ENVIRONMENT.** ENV-A.

---

### NODE G.11 [lemma] [fresh]

**STATEMENT.** *Centre uniqueness.* Two centres of depth `≥ t` for the same `a` are congruent
mod `π^⌈t/2⌉`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem tang_centre_unique (hπ : Irreducible π) {a : Fin 2 → O} {t : ℕ} {γ γ' : O}
    (h : Tang π a t γ) (h' : Tang π a t γ') : π ^ ((t + 1) / 2) ∣ (γ' - γ)
```

**DEPENDS.** G.02 · landed `qval_shift`, `qder_shift`, `Uniformity.Density.pow_dvd_iff_le`,
`exists_addVal_eq`, `pow_dvd_right_of_mul` (`Drainage.lean:116`).

**PROOF.**
1. set `δ := γ' - γ`; if `δ = 0` the claim is `dvd_zero`.
2. `qval a γ' = qval a γ + δ * (qder a γ + δ)` — from `qval_shift` after `ring_nf`.
3. `π^t ∣ qval a γ` and `π^t ∣ qval a γ'`, so `π^t ∣ δ * (qder a γ + δ)`.
4. suppose for contradiction `¬ π^((t+1)/2) ∣ δ`; let `x := addVal O δ`, so `x < (t+1)/2`
   (by `pow_dvd_iff_le`).
5. `π^((t+1)/2) ∣ qder a γ` by `h.2`, and `x < (t+1)/2` gives `addVal O (qder a γ + δ) = x`
   (valuation of a sum with distinct valuations).
6. hence `addVal O (δ * (qder a γ + δ)) = 2*x`, and step 3 gives `t ≤ 2*x`.
7. `x < (t+1)/2` and `t ≤ 2*x` contradict by `omega`.

**SIZE.** 30 lines. **Split candidate:** step 5 (valuation of a sum with unequal valuations) is a
reusable fact; if it is not one tactic, land it as the private helper
`addVal_add_eq_of_lt` and **return a RE-PLAN request** (it is reusable at G.32 and G.34).

**SOURCE.** `EFF.W11.20` (the refine locus maps *isomorphically* onto the post node — injectivity
is exactly this uniqueness); `EFF.W11.26` (the drainage count consumes it: the centre contributes
`q^⌈(N−1)/2⌉` distinct classes, not more).

**TEETH.** `W11-EXHAUST` / P-4 → **Lean theorem** (an over-count here would break `undecided = q^N`
in the direction the tooth checks).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.12 [lemma] [fresh]

**STATEMENT.** *Depth is a property of the class.* For `t ≤ N`, if one lift of `c` has a centre
of depth `≥ t` then every lift does.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem tang_of_proj_eq (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {a b : Fin 2 → O}
    (hab : proj O 2 N a = proj O 2 N b) {γ : O} (h : Tang π a t γ) : Tang π b t γ
```

**DEPENDS.** landed `Uniformity.Density.congAt_of_proj_eq` (`Drainage.lean:639`),
`qval_congr` (`Drainage.lean:437`), `qder_congr` (`Drainage.lean:443`),
`dvd_transfer` (`Drainage.lean:449`).

**PROOF.**
1. `have hcong : CongAt π N a b := congAt_of_proj_eq hπ hab`.
2. value: `dvd_transfer (le_of_eq rfl ▸ ht) (qval_congr hcong γ) h.1` gives `π^t ∣ qval b γ`
   (exponent side condition `t ≤ N`).
3. derivative: `(t+1)/2 ≤ N` by `omega` from `ht`; `dvd_transfer` with `qder_congr hcong γ` and
   `h.2`.
4. assemble.

**SIZE.** 12 lines.

**SOURCE.** `EFF.W11.22` (the tail cell is defined by in-window data, so it is a set of classes);
`EFF.HEX3.16` (window coherence: consulted digits sit strictly below the ghost zones).

**TEETH.** `HEX3-XREAD` (`EFF.HEX3.47`, pointwise tie of a fresh reader to the sealed one) →
**executable regression** (retained; the Lean statement is the class-invariance, which the reader
tie exercises indirectly).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.13 [lemma] [fresh]

**STATEMENT.** For `t ≤ N`, membership in `tangSet π N t` is equivalent to the `∀`-form: every
lift has a centre of depth `≥ t`. Consequently `tangSet` is antitone in `t`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem mem_tangSet_iff (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {c : Coeff O 2 N} :
    c ∈ tangSet π N t ↔ ∀ a : Fin 2 → O, proj O 2 N a = c → ∃ γ : O, Tang π a t γ

theorem tangSet_antitone (hπ : Irreducible π) {N t t' : ℕ} (h : t ≤ t') :
    tangSet π N t' ⊆ tangSet π N t
```

**DEPENDS.** G.09, G.12 · landed `proj_surjective`, `Tang_mono` (`Drainage.lean:517`).

**PROOF.**
1. (→) `obtain ⟨a, ha, γ, hγ⟩`; `intro b hb`; `exact ⟨γ, tang_of_proj_eq hπ ht (ha.trans hb.symm) hγ⟩`.
2. (←) `obtain ⟨a, ha⟩ := proj_surjective O 2 N c`; apply the hypothesis to `a`.
3. antitone: `rintro c ⟨a, ha, γ, hγ⟩; exact ⟨a, ha, γ, Tang_mono h hγ⟩` (no `t ≤ N` needed).

**SIZE.** 14 lines. Two public declarations, same justification as G.02.

**SOURCE.** `EFF.W11.22`.

**TEETH.** signed non-applicable (a reformulation).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.14 [lemma] [fresh]

**STATEMENT.** The two valuation strata of `Res O N` and their exact sizes, **stated without
`ℕ`-subtraction and without division** (the level is written `k + r`, so the answers are
`q^r` and `q^(r+1) − q^r` in additive form):
`#{x : Res O (k+r) | π^k ∣ x} = q^r`, and
`#{x : Res O (k+r+1) | v(x) = k exactly} + q^r = q^(r+1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The classes of valuation `≥ k`. -/
def dvdSet (π : O) (k N : ℕ) : Set (Res O N) :=
  {x | ∃ y : O, Ideal.Quotient.mk _ (π ^ k * y) = x}

/-- The classes of valuation exactly `k`. -/
def exactSet (π : O) (k N : ℕ) : Set (Res O N) := dvdSet π k N \ dvdSet π (k + 1) N

theorem card_dvdSet (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (dvdSet π k (k + r)) = residueCard O ^ r

theorem card_exactSet_add (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (exactSet π k (k + r + 1)) + residueCard O ^ r = residueCard O ^ (r + 1)
```

**DEPENDS.** landed `Uniformity.Density.resFactor`, `resFactor_surjective`, `card_res`
(`LocalData.lean:215,221,228`), `card_preimage_of_surjective` (`LocalData.lean:192`),
`mem_maximalIdeal_pow_iff_dvd` (`Drainage.lean:635`).

**PROOF.**
1. `dvdSet π k N = (resFactor (h : k ≤ N)) ⁻¹' {0}` — one direction by
   `mem_maximalIdeal_pow_iff_dvd`, the other by `Ideal.Quotient.eq_zero_iff_mem`.
2. `card_preimage_of_surjective` for the additive hom `resFactor h` with `t = {0}` gives
   `Nat.card (dvdSet π k N) = Nat.card (ker)`.
3. the same lemma with `t = Set.univ` plus `card_res` twice gives
   `q^(k+r) = Nat.card ker * q^k`, whence `Nat.card ker = q^r` by cancellation
   (`Nat.eq_of_mul_eq_mul_right` with `residueCard_pos`).
4. `card_exactSet_add`: `exactSet` is a set difference with `dvdSet π (k+1) (k+r+1) ⊆
   dvdSet π k (k+r+1)`, so `Nat.card (A \ B) + Nat.card B = Nat.card A`
   (`Set.ncard_diff_add_ncard_of_subset`, finiteness from `instFiniteRes`); apply step 3 twice
   at `(k, r+1)` and `(k+1, r)`.

**SIZE.** 30 lines across three declarations. **Three public declarations** (two defs + two
theorems) are permitted here as one indivisible census primitive.

**⚠ RE-DERIVATION TARGET, with its statement discipline.**
`leancheck/UniformityCheck/Counting.lean` lands `dvdSet`, `exactSet`, `card_dvdSet` and
`card_exactSet_add` in **exactly these shapes**, and the additive/index-shifted phrasing is
deliberate there: it keeps every count statement free of `ℕ`-subtraction and of division, so the
statements hold verbatim in residue characteristic 2 and 3 with no side conditions. **Chapter G
adopts that discipline for every count node.** (The same discipline governs
`three_mul_card_noRootCubic`, `two_mul_card_linAni`, `six_mul_card_split3`, `two_mul_card_aniK`
downstream.)

**SOURCE.** `EFF.W11.14` (`#C(a,b) = q^(N−a)·q^(N−b)` — this node is one factor of that display);
`EFF.HEX3.13` (every H-1 locus is a slot count of exactly this shape).

**TEETH.** `W11-CENSUS` → **Lean theorem**.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.15 [def] [fresh]

**STATEMENT.** The depth-`t` family: centre modulus `⌈t/2⌉`, read `readAt`, admissible set
`{(F, F') | π^t ∣ F ∧ π^⌈t/2⌉ ∣ F'}` expressed by vanishing of the truncations.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The admissible set of the depth-`t` family in `(value, derivative)` coordinates. -/
def tangAdm (π : O) (t N : ℕ) : Set (Res O N × Res O N) :=
  (dvdSet π t N) ×ˢ (dvdSet π ((t + 1) / 2) N)
```

**DEPENDS.** G.14 · landed `Res`.

**PROOF.** definitional.

**SIZE.** 8 lines.

**SOURCE.** `EFF.W11.22`; `EFF.HEX3.13` (the `B0ZERO` species is the `t = N` instance).

**TEETH.** none (definition).

**ENVIRONMENT.** ENV-A.

---

### NODE G.16 [lemma] [fresh]

**STATEMENT.** At level `N = t + r`, `#tangAdm · q^⌈t/2⌉ = q^(t + 2r)` — the subtraction-free form
of `#tangAdm = q^(N−t) · q^(N−⌈t/2⌉)`. (The factor `q^⌈t/2⌉` is exactly the centre factor
`card_certSet_gen` will contribute, so this phrasing makes G.17 a rewrite with no arithmetic.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_tangAdm (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangAdm π t (t + r)) * residueCard O ^ ((t + 1) / 2)
      = residueCard O ^ (t + 2 * r)
```

**DEPENDS.** G.14, G.15.

**PROOF.**
1. `tangAdm` is a `Set.prod`; `Nat.card_prod` through `Equiv.Set.prod`.
2. first factor: `card_dvdSet` at `(k, r) = (t, r)`, giving `q^r`.
3. second factor: `card_dvdSet` at `(k, r') = ((t+1)/2, t + r − (t+1)/2)`, legal because
   `(t+1)/2 ≤ t + r` (`omega`), giving `q^(t + r − (t+1)/2)`.
4. multiply and collect exponents: `r + (t + r − (t+1)/2) + (t+1)/2 = t + 2r`, by `pow_add` and
   `omega` (the `ℕ`-subtraction is discharged by `omega` from `(t+1)/2 ≤ t + r`).

**SIZE.** 16 lines.

**SOURCE.** `EFF.W11.14`.

**TEETH.** `W11-CENSUS` → **Lean theorem**.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.17 [theorem] [fresh]

**STATEMENT.** **The filtration count.** At level `N = t + r`,
`#(tangSet π (t+r) t) = q^(t + 2r)` — i.e. `q^(2N−t)` classes admit a centre of tangency depth
`≥ t`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- **The tangency-filtration count.** At level `N = t + r`, exactly `q^(t+2r) = q^(2N−t)` classes
admit a centre of tangency depth `≥ t`. This is the level-exact form of W-11's per-node drainage
census, and its `r = 0` case is W-11 clause (iii)'s exact drainage law. -/
theorem card_tangSet (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangSet π (t + r) t) = residueCard O ^ (t + 2 * r)
```

**DEPENDS.** G.03, G.04, G.09, G.10, G.11, G.13, G.15, G.16, G.18 · landed
`UniformityCheck.card_certSet_gen`.

**PROOF.**
1. put `N := t + r`, `m := (t+1)/2`, `hm : m ≤ N` by `omega`.
2. `obtain ⟨cert, hcert, hshift, huniq, hset⟩ := tangCert hπ t r` (G.18).
3. `card_certSet_gen hm (fun g => readEquiv g) (tangAdm π t N) cert hcert hshift huniq` gives
   `Nat.card {c | ∃ g, cert g c} = q^m * Nat.card (tangAdm π t N)`.
4. rewrite the left side by `hset` (G.18's last conjunct) to `Nat.card (tangSet π N t)`.
5. rewrite the right side by G.16 (`mul_comm` first): `q^m * Nat.card (tangAdm π t N)
   = q^(t + 2*r)`.

**SIZE.** 14 lines (the family construction is G.18).

**⚠ RE-DERIVATION EVIDENCE.** The two landed censuses of the same shape in `leancheck`
(`card_ramSet`, 48 lines / 9 `have`s; `card_inertSet`, 32 / 5) are the size calibration for the
G.18 + G.17 pair: expect ~45 lines total, with the mass in G.18's `hshift`/`huniq`.

**SOURCE.** `EFF.W11.26` (the drainage law: per node instance `q^⌈(N−1)/2⌉`, bracket
`q^⌊(N−1)/2⌋`, × `q` centres = `q^N` — this node is its level-exact generalisation to every `t`,
with the same two factors appearing as `q^m` and `q^(N−m)`); `EFF.W11.23` (the instance bracket
`q^(k−1)`, which in this formulation *is* the centre-coset count `q^m`).

**⚠ ARITHMETIC CROSS-CHECK (mandatory for the cross-read).** At `t = N` this gives `q^N`, which is
W-11's clause-(iii) drainage law exactly (`EFF.W11.10`). At `t = 0` it gives `q^(2N)`, the whole
box. Numerically at `q = 2, N = 2`: `t = 0,1,2` give `16, 8, 4`; the depth strata are `8, 4` and
the undecided set `4`; the W-11 census at `(Zp,2,2)` has whole-space undecided `q^N = 4` ✓.

**TEETH.** `W11-EXHAUST` / P-4 (30 rows, "undecided = q^N EXACTLY") → **Lean theorem** (the
`t = N` instance); `W11-CENSUS` / P-2 → **Lean theorem** (the general `t`).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.18 [lemma] [fresh]

**STATEMENT.** The depth-`t` certified family in the sense of G.05, minus the forcing field:
centre modulus `⌈t/2⌉`, read `readAt`, admissible set `tangAdm`, with `hcert`, `hshift`, `huniq`
discharged.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The depth-`t` census datum: the three `card_certSet_gen` hypotheses, discharged, together with
the identification of the certified set with `tangSet`. -/
theorem tangCert (hπ : Irreducible π) (t r : ℕ) :
    ∃ cert : Res O (t + r) → Coeff O 2 (t + r) → Prop,
      (∀ g c, cert g c ↔ readEquiv g c ∈ tangAdm π t (t + r))
      ∧ (∀ g g' c, cert g c → resFactor (O := O) (by omega : (t+1)/2 ≤ t + r) g'
            = resFactor _ g → cert g' c)
      ∧ (∀ g g' c, cert g c → cert g' c → resFactor (O := O) (by omega : (t+1)/2 ≤ t + r) g'
            = resFactor _ g)
      ∧ (∀ c, (∃ g, cert g c) ↔ c ∈ tangSet π (t + r) t)
```

**DEPENDS.** G.03, G.04, G.09, G.10, G.11, G.13, G.15 · landed `mem_maximalIdeal_pow_iff_dvd`,
`proj_surjective`, `Ideal.Quotient.mk_surjective`.

**PROOF.**
1. take `cert g c := readEquiv g c ∈ tangAdm π t (t + r)`; `hcert` is `Iff.rfl`.
2. **the bridge lemma** (land it as a private helper, `cert_iff_tang`): for `g = ⟦γ⟧` and
   `c = proj O 2 N a`, `cert g c ↔ Tang π a t γ`. Proof: `readEquiv_proj` (G.04) rewrites both
   coordinates to `⟦qval a γ⟧`, `⟦qder a γ⟧`; membership in `dvdSet` is then divisibility
   downstairs by `mem_maximalIdeal_pow_iff_dvd` (both exponents are `≤ N`, by `omega`).
3. `hshift`: given `cert g c` and `resFactor _ g' = resFactor _ g`, choose `O`-lifts `γ, γ'` of
   `g, g'`; the hypothesis says `π^((t+1)/2) ∣ (γ' − γ)`; step 2 and G.10 conclude.
4. `huniq`: symmetric, using G.11.
5. last conjunct, (→): from `cert g c` pick a lift `a` of `c` (`proj_surjective`) and a lift `γ`
   of `g`; step 2 gives `Tang π a t γ`, hence `c ∈ tangSet`.
6. last conjunct, (←): `c ∈ tangSet` gives a lift `a` and a centre `γ` with `Tang π a t γ`; take
   `g := ⟦γ⟧` and apply step 2 (using G.12 to move from that particular lift to the class).

**SIZE.** 42 lines. **Split candidate (recommended):** land step 2 as its own node
`G.18a cert_iff_tang` (~14 lines) and keep G.18 at ~28. Calibration: `leancheck`'s analogous
bridge lemmas `ramCert_iff` and `inertCert_iff` are 28 and ~20 lines respectively and are the
single largest support lemmas of their files.

**SOURCE.** as G.17.

**TEETH.** as G.17.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.19 [def] [fresh]

**STATEMENT.** `depthSet π N t` = classes of depth **exactly** `t`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- Level-`N` classes whose maximal centre depth is exactly `t`. -/
def depthSet (π : O) (N t : ℕ) : Set (Coeff O 2 N) := tangSet π N t \ tangSet π N (t + 1)
```

**DEPENDS.** G.09.

**PROOF.** definitional.

**SIZE.** 4 lines.

**SOURCE.** `EFF.W11.15` (the trichotomy is stated at the *deepest* centre: "the last step before
a predicate first fails" — the landed `exists_max_step`, `Drainage.lean:556`).

**TEETH.** none (definition).

**ENVIRONMENT.** ENV-A.

---

### NODE G.20 [lemma] [fresh]

**STATEMENT.** At level `N = t + 1 + r` (so `t < N`), the depth-exactly-`t` stratum satisfies
`#(depthSet) + q^(t+2r+1) = q^(t+2r+2)` — the subtraction-free form of
`#(depthSet π N t) = (q−1)·q^(2N−t−1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_depthSet (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (depthSet π (t + 1 + r) t) + residueCard O ^ (t + 2 * r + 1)
      = residueCard O ^ (t + 2 * r + 2)
```

**DEPENDS.** G.13, G.17, G.19.

**PROOF.**
1. `tangSet π N (t+1) ⊆ tangSet π N t` (G.13, `tangSet_antitone`).
2. `Set.ncard_diff_add_ncard_of_subset` (finiteness from `instFiniteCoeff`) gives
   `Nat.card (depthSet π N t) + Nat.card (tangSet π N (t+1)) = Nat.card (tangSet π N t)`.
3. `card_tangSet` at `(t+1, r)`: `Nat.card (tangSet π ((t+1)+r) (t+1)) = q^(t+1+2r)`; the level
   matches `N = t+1+r` definitionally.
4. `card_tangSet` at `(t, 1+r)`: `Nat.card (tangSet π (t+(1+r)) t) = q^(t+2(1+r)) = q^(t+2r+2)`;
   the level matches `N` after `omega`-normalising `t + (1+r) = t+1+r`.
5. substitute and `ring_nf` the exponents (`t+1+2r = t+2r+1`).

**SIZE.** 18 lines.

**⚠ ARITHMETIC CROSS-CHECK.** Read multiplicatively this is `#depthSet = (q−1)q^(2N−t−1)`. At
`t = 2j+1` odd it is `(q−1)q^(2N−2j−2)`, and W-11's **whole-space** RAM(h) count with `h = 2j+1`
is `q·(q−1)q^(2N−h−2) = (q−1)q^(2N−2j−2)` ✓ — the chapter's stratum and W-11's family agree
exactly, centre factor included.

**SOURCE.** `EFF.W11.09` (the RAM row `(q−1)q^(2N−2k−1)` per centre is the odd-`t` instance;
`EFF.W11.24`).

**⚠ ARITHMETIC CROSS-CHECK.** At `t = 2j+1` odd this is `(q−1)q^(2N−2j−2)`, and W-11's whole-space
RAM(h) count with `h = 2j+1` is `q·(q−1)q^(2N−h−2) = (q−1)q^(2N−2j−2)` ✓ — the chapter's stratum
and W-11's family agree exactly, including the centre factor.

**TEETH.** `W11-CENSUS` / P-2 (the RAM rows on 30 census rows) → **Lean theorem**.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.21 [def] [fresh]

**STATEMENT.** *The residual pair at an even-depth centre.* For a centre `γ` with
`π^(2k) ∣ qval a γ` and `π^k ∣ qder a γ`, the residual pair is
`(qval a γ / π^(2k), qder a γ / π^k)` reduced mod `𝔪`, an element of `ResidueField O ×
ResidueField O`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The residual pair `(b₀, b₁)` read at a centre of even depth `2k`, in the residue field. -/
noncomputable def residualPair (π : O) (k : ℕ) (a : Fin 2 → O) (γ : O) :
    IsLocalRing.ResidueField O × IsLocalRing.ResidueField O :=
  (IsLocalRing.residue O (Classical.choose (id (⟨_, rfl⟩ : ∃ y, qval a γ = π ^ (2 * k) * y))),
   IsLocalRing.residue O (Classical.choose (id (⟨_, rfl⟩ : ∃ y, qder a γ = π ^ k * y))))
```

**DEPENDS.** landed `qval`, `qder`, `IsLocalRing.residue`.

**PROOF.** definitional. **Design note for the formalizer:** the two `Classical.choose` witnesses
must be taken from *hypotheses supplied at the use site*, not from the vacuous `⟨_, rfl⟩` above,
which is a placeholder the SIGNATURE cannot express without hypotheses. Land the real definition
as a function of two divisibility proofs:
`residualPair (h0 : π ^ (2*k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ) : ResidueField O × ResidueField O
 := (residue O h0.choose, residue O h1.choose)`, and export the two computation rules
`qval a γ = π^(2k) * (lift of the first coordinate)` etc. **This is a SIGNATURE defect the
blueprint declares rather than hides**: the fleet lands the two-hypothesis form and the
orchestrator books the amended signature.

**SIZE.** 12 lines.

**SOURCE.** `EFF.W11.15` (the residual quadratic `R(y) = y² + c₁y + c₀`, `c₁ = digit_k(A₁)`,
`c₀ = digit_2k(A₀)`); `EFF.HEX3.13` (the same read at `n = 3`).

**TEETH.** `W11-CENSUS` (the residual census rows) → **Lean theorem** at G.22/G.41.

**ENVIRONMENT.** ENV-A.

---

### NODE G.22 [def] [fresh]

**STATEMENT.** `resStratum π N k p` = the classes of depth exactly `2k` whose residual pair at a
depth-`2k` centre reduces to `p`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- Classes of depth exactly `2k` carrying the residual pair `p`. -/
def resStratum (π : O) (N k : ℕ) (p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O) :
    Set (Coeff O 2 N) :=
  {c | c ∈ depthSet π N (2 * k) ∧
    ∃ (a : Fin 2 → O) (γ : O), proj O 2 N a = c ∧ Tang π a (2 * k) γ ∧
      ∃ (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ), residualPair h0 h1 = p}
```

**DEPENDS.** G.19, G.21.

**PROOF.** definitional. (The `Tang π a (2*k) γ` hypothesis already supplies `h0`, `h1` because
`⌈2k/2⌉ = k`; they are named separately only so `residualPair` can consume them.)

**SIZE.** 10 lines.

**SOURCE.** `EFF.W11.16` (the residual census table: the strata are indexed by the type of `R`);
`EFF.W11.15`.

**TEETH.** `W11-CENSUS` → **Lean theorem** at G.23.

**ENVIRONMENT.** ENV-A.

---

### NODE G.23 [lemma] [fresh]

> **AMENDMENT BANNER 2026-08-15 — `card_resStratum` (G.23a) IS REFUTED; NEITHER DECLARED ROUTE
> GOVERNS.** The true per-pair count is `q^(2N−2k−1)/#Stab(p)`, not `q^(2N−2k−2)`; the strata over
> a residue-field translation orbit coincide, so the "sum over `q²−q` pairs" certainty argument
> below double-counts by the orbit size. `depthSet_eq_iUnion_resStratum` (G.23b) survives (the
> union is **not** disjoint). Read **AMENDMENT §A-1** at the end of this file before consuming
> anything here; it carries the counterexample and the replacement route (which removes this node
> from the critical path). **Do not assign G.23a as a proof target.** Nothing below is edited.
> **UPDATE 2026-08-15 (fourth append):** that replacement route is now expanded into twelve
> fireable nodes **G.23R1–G.23R12** at **AMENDMENT §A-8**, all LANDED in `leanfinal`. G.41/G.42
> consume `card_resClassSet` (G.23R9), not this node.

**STATEMENT.** *The residual refinement of a depth stratum.* For `2k < N` and `p` **not** a
double-root pair (i.e. `y² − p.2·y + p.1` has no repeated root; equivalently
`p ∉ rootPairMap '' {diagonal}`), `#(resStratum π N k p) = q^(2N−2k−2)`; and the strata over the
`q² − q` non-double-root pairs partition `depthSet π N (2k)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_resStratum (hπ : Irreducible π) {N k : ℕ} (hk : 2 * k < N)
    {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O}
    (hp : ∀ z : IsLocalRing.ResidueField O, p ≠ (z * z, z + z)) :
    Nat.card (resStratum π N k p) = residueCard O ^ (2 * N - 2 * k - 2)

theorem depthSet_eq_iUnion_resStratum (hπ : Irreducible π) {N k : ℕ} (hk : 2 * k < N) :
    depthSet π N (2 * k)
      = ⋃ p ∈ {p | ∀ z : IsLocalRing.ResidueField O, p ≠ (z * z, z + z)}, resStratum π N k p
```

**DEPENDS.** G.17, G.18, G.20, G.22 · landed `card_certSet_gen`, `card_res`,
`exists_residual_root` (`Drainage.lean:523`).

**PROOF.**
1. Refine the family of G.18 at `t = 2k` by pinning two further digits: extend the admissible set
   from `tangAdm O (2k ≤ N) (k ≤ N)` to
   `tangAdm₂ p := {x | resFactor _ x.1 = 0 ∧ resFactor _ x.2 = 0 ∧ (digit reads equal p)}`,
   where the digit reads are `resFactor (2k+1 ≤ N) x.1` and `resFactor (k+1 ≤ N) x.2` compared
   against the images of `p` under the (injective) maps `ResidueField O → Res O (2k+1)`,
   `→ Res O (k+1)` induced by multiplication by `π^(2k)`, `π^k`.
2. `hshift`/`huniq` are inherited from G.18 *provided* the residual pair is invariant under
   centre moves inside the coset mod `π^k` — this is where `p` not being a double-root pair is
   used: for `δ` with `v(δ) ≥ k`, `qval a (γ+δ) = qval a γ + qder a γ·δ + δ²` shifts `b₀` by
   `b₁·d + d²` and `b₁` by `2d` where `d = δ/π^k mod 𝔪`; so the residual pair moves by the
   substitution `y ↦ y + d`, which fixes `p` only for `d = 0` **unless** `p` is a double-root
   pair. Take the sub-coset `mod π^(k+1)` as the family's centre modulus `m := k+1`.
3. `#tangAdm₂ p = q^(N−2k−1) · q^(N−k−1)` (two more digits pinned than G.16).
4. `card_certSet_gen` with `m = k+1`: `q^(k+1) · q^(N−2k−1) · q^(N−k−1) = q^(2N−2k−1)`.
5. That counts classes of depth `≥ 2k` with residual `p`; those of depth `≥ 2k+1` inside it are
   exactly the ones with `b₀ ≡ 0`, excluded because `p` is not a double-root pair and
   `(0, b₁)` is a double-root pair iff `b₁ = 0`… **hence** step 4 already lands inside
   `depthSet π N (2k)`, and the count needs one further division by `q` coming from the
   `depthSet` restriction — see step 6.
6. Reconcile with G.20: summing step 4's count over the `q²−q` admissible `p` must give
   `(q−1)q^(2N−2k−1)`. So the per-`p` count is `(q−1)q^(2N−2k−1)/(q²−q) = q^(2N−2k−2)` ✓. Land
   this as the *statement* and prove it by the refined census of steps 1–4 with the corrected
   modulus (`m = k`, not `k+1`, once the residual pair is pinned: the pinned residual already
   rigidifies the centre).

**⚠ BLUEPRINT DEFECT DECLARED (do not paper over).** Steps 2–6 contain an unresolved choice of
centre modulus (`k` vs `k+1`) whose two readings differ by the factor `q` that step 6 reconciles
by arithmetic rather than by proof. The **arithmetic is certain** (the sum over the `q²−q`
non-degenerate pairs must reproduce G.20, which is proved independently), and the *statement* of
`card_resStratum` is therefore certain. The *proof route* must be settled by the formalizer:
either (a) modulus `m = k` with the residual pinned (the centre is then pinned mod `π^k` only,
and the residual reading is invariant under the residual translation `y ↦ y + d` only for
`d = 0`, which is what pinning `p` buys), or (b) modulus `k+1` plus an explicit quotient step.
**Route (a) is the blueprint's recommendation.** A formalizer who cannot close either returns
`BLOCKED` with the proof state, and the orchestrator books a codex revision. Nothing downstream
depends on the route, only on the statement.

**SIZE.** 40 lines (route (a)). **Split candidate:** the refined admissible set and its count
(steps 1, 3) as `G.23a`; the census application (step 4) as `G.23b`.

**SOURCE.** `EFF.W11.16` (the residual census: "Pairs `(c₁, c₀) ∈ F_q × F_q^*`, counted by the
type of `R`" — with the three row counts `(q−1)(q−2)/2`, `q(q−1)/2`, `q−1`);
`EFF.W11.15` (the trichotomy's third bullet).

**TEETH.** `W11-CENSUS` / P-2 → **Lean theorem**; `HEX3-SPECIES` → **executable regression**
(retained: the `n = 3` analogue is not proved here).

**ENVIRONMENT.** ENV-A'.

---

## 5. §5 — `n = 2`: TYPE CLASSIFICATION BY DEPTH

### NODE G.24 [lemma] [fresh]

**STATEMENT.** A class of odd depth exactly `t = 2j+1` carries the RAM certificate at window
`t+1`: at a witnessing centre the value has exact valuation `2j+1` and the derivative valuation
`≥ j+1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem certRam_of_depth_odd (hπ : Irreducible π) {N j : ℕ} {a : Fin 2 → O}
    (hmem : proj O 2 N a ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    CertRam π a (2 * j + 2)
```

**DEPENDS.** G.09, G.12, G.19 · landed `Uniformity.Density.CertRam` (`Drainage.lean:251`),
`Tang` (`Drainage.lean:511`).

**PROOF.**
1. `hmem.1` gives a lift `b` and a centre `γ` with `Tang π b (2j+1) γ`; G.12 moves it to `a`
   (legal: `2j+1 ≤ N`).
2. so `π^(2j+1) ∣ qval a γ` and `π^(j+1) ∣ qder a γ` — the latter because
   `((2j+1)+1)/2 = j+1`.
3. `¬ π^(2j+2) ∣ qval a γ`: otherwise `Tang π a (2j+2) γ` would hold, since its derivative
   requirement is `π^((2j+2+1)/2) = π^(j+1) ∣ qder a γ`, already in hand by step 2 — contradicting
   `hmem.2` (via G.12 again, `2j+2 ≤ N`).
4. assemble `⟨γ, j, le_refl _, step 2, step 3, step 2⟩`.

**SIZE.** 18 lines.

**SOURCE.** `EFF.W11.15`, first bullet ("`u` odd, `w ≥ (u+1)/2` — one side, slope `u/2`,
denominator `e = 2` … **RAM(u)**, decided"); `EFF.W11.17` (the σ-assignment: "RAM(h): Eisenstein
after the slope-`h/2` scaling — irreducible, totally ramified `e = 2`, `f = 1`").

**TEETH.** `W11-ORACLE` / P-6 (`EFF.W11.38`, `[IND]` PARI, per-polynomial `(σ,e,f,v(disc))`) →
**executable regression** (retained at `verification/`; the Lean side proves the implication, the
oracle independently confirms the σ on `8,252` polynomials, mixed characteristic only per BOX-4).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.25 [lemma] [fresh]

**STATEMENT.** A class of odd depth `< N` is `ramType`-decided at level `N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem decidedAt_ram_of_depth_odd (hπ : Irreducible π) {N j : ℕ} {c : Coeff O 2 N}
    (hmem : c ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    DecidedAt O 2 ramType N c
```

**DEPENDS.** G.24 · landed `typeOf_of_certRam` (`Drainage.lean:286`), `CertRam_congr`
(`Drainage.lean:463`), `congAt_of_proj_eq` (`Drainage.lean:639`), `proj_surjective`.

**PROOF.**
1. `intro a ha` (`proj O 2 N a = c`).
2. `certRam_of_depth_odd` (G.24) applied to `a` via `ha ▸ hmem` gives `CertRam π a (2j+2)`.
3. `typeOf_of_certRam hπ` gives `typeOf (monicPoly a) = ramType`.

**SIZE.** 10 lines. (Note the certificate is produced *for each lift separately*, so no
`CertRam_congr` step is needed — but it is listed as a DEPENDS fallback if the formalizer prefers
to certify one lift and transport.)

**SOURCE.** `EFF.W11.15`; `EFF.W11.10` (clause (iii): the decided families partition with the
undecided residue).

**TEETH.** as G.24.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.26 [lemma] [fresh]

**STATEMENT.** *The even-depth dichotomy.* At a witnessing centre of even depth exactly `2k`,
write `qval a γ = π^(2k)·b₀`, `qder a γ = π^k·b₁`. Then **either** `![b₀, b₁]` is anisotropic,
**or** the residual quadratic `y² + b₁y + b₀` has a root `z̄` mod `𝔪` at which it is *simple*
(i.e. `π ∤ (b₁ + 2z)`). The remaining case — a residual double root — is impossible, because it
would produce a centre of depth `2k+1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem depth_even_dichotomy (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a (2 * k) γ) (hmax : ¬ ∃ γ', Tang π a (2 * k + 1) γ')
    {b₀ b₁ : O} (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁) :
    Anisotropic ![b₀, b₁] ∨ ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) ∧ ¬ π ∣ (b₁ + 2 * z)
```

**DEPENDS.** landed `Anisotropic` (`QuadCert.lean:340`), `exists_residual_root`
(`Drainage.lean:523`), `qval_shift`, `qder_shift`, `Tang`.

**PROOF.**
1. `by_cases haniso : Anisotropic ![b₀, b₁]`; the left disjunct closes.
2. otherwise `exists_residual_root hπ haniso` gives `z` with `π ∣ (z² + b₁z + b₀)`.
3. `by_cases hdd : π ∣ (b₁ + 2z)`; if not, the right disjunct closes with this `z`.
4. if `hdd` holds, recentre at `γ' := γ + π^k z` and show `Tang π a (2k+1) γ'`, contradicting
   `hmax`:
   * value: `qval a γ' = qval a γ + qder a γ·(π^k z) + (π^k z)²
     = π^(2k)(b₀ + b₁z + z²)` by `qval_shift`, `h0`, `h1` and `ring`; step 2 supplies
     `π ∣ (b₀ + b₁z + z²)`, so `π^(2k+1) ∣ qval a γ'`;
   * derivative: `qder a γ' = π^k(b₁ + 2z)` by `qder_shift`, `h1`, `ring`; `hdd` gives
     `π^(k+1) ∣ qder a γ'`, and `((2k+1)+1)/2 = k+1`.
5. `exact absurd ⟨γ', ⟨_, _⟩⟩ hmax`.

**SIZE.** 32 lines. This node is a re-cut of the landed `cert_of_not_tang`'s even branch
(`Drainage.lean:589–619`), which performs exactly this case split inline; the chapter needs it
standalone because the census keys strata by the residual class.

**SOURCE.** `EFF.W11.15`, third bullet (the `u = 2k` case: "`R` separable with two roots:
**SPLITEQ(k)**; `R` irreducible: **INERTDEEP(k)**; `R = (y − z̄)², z̄ ≠ 0`: NOT decided —
**REFINE**"); `EFF.W11.20` (the refinement isomorphism, which is why the third case raises the
depth).

**TEETH.** `W11-CENSUS` / P-2 (the residual-census rows) → **Lean theorem**.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.27 [lemma] [fresh]

**STATEMENT.** Anisotropic residual at an even-depth centre ⟹ the INERT certificate at window
`2k+1`; hence the class is `inertType`-decided at every level `N ≥ 2k+1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem decidedAt_inert_of_ani (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hani : Anisotropic ![b₀, b₁]) :
    DecidedAt O 2 inertType N (proj O 2 N a)
```

**DEPENDS.** landed `CertInert` (`Drainage.lean:258`), `typeOf_of_certInert`
(`Drainage.lean:329`), `CertInert_congr` (`Drainage.lean:484`), `congAt_of_proj_eq`.

**PROOF.**
1. `have hcert : CertInert π a N := ⟨γ, k, b₀, b₁, hN, h0, h1, hani⟩`.
2. `intro b hb`; `have hcong : CongAt π N a b := congAt_of_proj_eq hπ hb.symm`.
3. `CertInert_congr hπ hcong hcert` gives `CertInert π b N`.
4. `typeOf_of_certInert hπ` closes.

**SIZE.** 10 lines.

**SOURCE.** `EFF.W11.15` ("`R` irreducible: **INERTDEEP(k)** (inert: `f` irreducible, unramified,
residual degree 2)"); `EFF.W11.17` (INERTDEEP's σ and `v(disc) = 2k`).

**TEETH.** `W11-T-SIGMA` (`EFF.W11.38`, 3,020 firings: "once per decided inert member per oracle
row") → **executable regression** (retained; independent σ confirmation of exactly this
implication, mixed characteristic).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.28 [lemma] [fresh]

> **AMENDMENT BANNER 2026-08-15 — SIGNATURE AMENDED: `hN : 2 * k + 1 ≤ N`** (was `2 * k + 2 ≤ N`,
> which is one stronger than this node's own proof uses). The amended form is what the fleet
> lands, and it is what G.42 needs at `r = 0`. See **AMENDMENT §A-2**. Nothing below is edited.

**STATEMENT.** A simple residual root at an even-depth centre ⟹ the SPLIT certificate at window
`2k+2`; hence the class is `splitType`-decided at every level `N ≥ 2k+2`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem decidedAt_split_of_sep (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N k : ℕ} {a : Fin 2 → O} {γ z : O}
    {b₀ b₁ : O} (hN : 2 * k + 2 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hz : π ∣ (z ^ 2 + b₁ * z + b₀)) (hs : ¬ π ∣ (b₁ + 2 * z)) :
    DecidedAt O 2 splitType N (proj O 2 N a)
```

**DEPENDS.** G.26 · landed `CertSplit` (`Drainage.lean:245`), `typeOf_of_certSplit`
(`Drainage.lean:407`), `CertSplit_congr` (`Drainage.lean:455`), `qval_shift`, `qder_shift`,
`congAt_of_proj_eq`.

**PROOF.**
1. put `γ' := γ + π^k z`.
2. `qder a γ' = π^k (b₁ + 2z)` (`qder_shift`, `h1`, `ring`), so `π^k ∣ qder a γ'` and
   `¬ π^(k+1) ∣ qder a γ'` — the latter from `hs` by cancelling `π^k`
   (`mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero)`), exactly the landed pattern at
   `Drainage.lean:615–619`.
3. `qval a γ' = π^(2k)(b₀ + b₁z + z²)` (`qval_shift`, `h0`, `h1`, `ring`), and `hz` gives
   `π^(2k+1) ∣ qval a γ'`.
4. `have hcert : CertSplit π a N := ⟨γ', k, hN', step 2a, step 2b, step 3⟩` with
   `hN' : 2*k+1 ≤ N` from `hN`.
5. `intro b hb`; `CertSplit_congr (congAt_of_proj_eq hπ hb.symm) hcert`; `typeOf_of_certSplit hπ`.

**SIZE.** 24 lines.

**SOURCE.** `EFF.W11.15`, third bullet, first sub-case ("`R` separable with two roots:
**SPLITEQ(k)** (split; roots at equal valuation `k`, distinct leading digits)") and second bullet
(2SIDED, which is the same certificate with the value hidden deeper); `EFF.W11.08` (SPLIT-TAIL is
also this certificate — "Every lift has `u = v(A₀) ≥ N > 2w` and hence lies in the split two-sided
case").

**⚠ TRANSCRIPTION NOTE.** W-11 distinguishes 2SIDED, SPLITEQ and SPLIT-TAIL as three families;
this node covers all three, because in the depth filtration they are one stratum
(`depth = 2k`, residual separable-split). See §0.4's dictionary. That collapse is what makes
C7-F1's `typeOf`-vs-window-cell distinction (`EFF.W11.08`) unnecessary in the Lean development:
the chapter never asserts a `typeOf` *shape* for a boundary cell, only its σ, which is exactly
what C7-F1 says is certified.

**TEETH.** `W11-CENSUS` / P-2 (the SPLIT-TAIL `w`-independence row, "SPLIT-TAIL(1)=(2)=(3)=128 —
the w-independence law visible raw") → **executable regression** (retained; the Lean chapter does
not prove the family-level `w`-independence, only the stratum count that implies it).

**ENVIRONMENT.** ENV-B (completeness is needed: `typeOf_of_certSplit` uses Hensel).

---

### NODE G.29 [lemma] [fresh]

**STATEMENT.** Every class of depth `< N` is decided (for the type of any of its lifts), and every
class of depth `≥ N` is undecided. Hence `undecidedSet O 2 N = tangSet π N N` **as sets** once
G.33–G.34 supply the second half.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem decidedAt_of_depth_lt (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N : ℕ} {c : Coeff O 2 N}
    (hc : c ∉ tangSet π N N) {a : Fin 2 → O} (ha : proj O 2 N a = c) :
    DecidedAt O 2 (typeOf (monicPoly a)) N c
```

**DEPENDS.** G.09, G.12 · landed `decidedAt_of_not_tang` (`Drainage.lean:652`).

**PROOF.**
1. `have : ¬ ∃ γ, Tang π a N γ := fun ⟨γ, hγ⟩ => hc ⟨a, ha, γ, hγ⟩`.
2. `ha ▸ decidedAt_of_not_tang hπ this`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.W11.22` (the finite-window partition: "every `u ≤ N−1` case is fully observable
(all pinned digits sit at positions `≤ N−1`)").

**TEETH.** `W11-EXHAUST` / P-4 → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.30 [lemma] [fresh]

> **AMENDMENT BANNER 2026-08-15 — THE `⚠ BOUNDARY CONDITION, DECLARED` BLOCK BELOW IS WITHDRAWN,
> INCLUDING ITS FALLBACK.** The split certificate fits the window at the top even stratum
> `t = N − 1`; G.28's amended hypothesis `2 * k + 1 ≤ N` is all this node needs, so the even branch
> requires only `t < N` and no stratum is lost. The proposed fallback (restrict to `t + 2 ≤ N`)
> would leave G.42 unprovable as stated at `r = 0`. See **AMENDMENT §A-2**. Nothing below is
> edited.

**STATEMENT.** *The stratum-to-type map.* For `t < N`: if `t = 2j+1` is odd, every class of
`depthSet π N t` is `ramType`-decided; if `t = 2k` is even, every class of `depthSet π N t` is
`inertType`-decided or `splitType`-decided, according to the dichotomy of G.26, and these two
alternatives are mutually exclusive.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem depth_type (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {N t : ℕ} (ht : t < N) {c : Coeff O 2 N} (hc : c ∈ depthSet π N t) :
    (∃ j, t = 2 * j + 1 ∧ DecidedAt O 2 ramType N c)
      ∨ (∃ k, t = 2 * k ∧ (DecidedAt O 2 inertType N c ∨ DecidedAt O 2 splitType N c))
```

**DEPENDS.** G.19, G.25, G.26, G.27, G.28 · landed `decidedSet_disjoint`
(`GenuineDensity.lean:92`), `inertType_ne_ramType`, `splitType_ne_inertType`.

**PROOF.**
1. `rcases Nat.even_or_odd t`.
2. odd: G.25 with `2j+2 ≤ N` from `ht`.
3. even `t = 2k`: pick a lift `a` and a witnessing centre `γ` (`hc.1`, G.12); the maximality
   `hc.2` gives G.26's hypothesis; `rcases` its disjunction; the anisotropic branch is G.27
   (`2k+1 ≤ N` from `ht`), the separable branch is G.28 (`2k+2 ≤ N` — **needs `t+1 < N`**, see
   the boundary note).
4. exclusivity: `decidedSet_disjoint` with `splitType_ne_inertType`.

**⚠ BOUNDARY CONDITION, DECLARED.** G.28 needs window `2k+2 ≤ N`, i.e. `t + 2 ≤ N`, whereas G.27
needs only `t + 1 ≤ N`. So at the **top even stratum** `t = N − 1` (`N` odd) the separable branch's
certificate does not fit in the window. This is not a gap in the mathematics — it is the reason
W-11's SPLIT-TAIL family exists (`EFF.W11.08`: at the window boundary "σ = split is certified,
whereas no single `typeOf` shape is certified"). Resolution for the Lean chapter: the split
certificate at the boundary uses the *value* hidden past the window, i.e. `CertSplit π a N` with
`2w+1 ≤ N` where the value divisibility `π^(2w+1) ∣ qval` holds because `π^N ∣ qval` and
`2w+1 ≤ N`. **Formalizer instruction:** state G.28 with the weaker window hypothesis
`2*k+1 ≤ N` and derive `π^(2k+1) ∣ qval a γ'` from `hz` *plus* the case distinction on whether
`2k+1 < N` (interior: as in G.28) or `2k+1 = N` (boundary: the value vanishes mod `π^N`, so any
lift's value is `π^N`-divisible and the certificate holds at the *lift* level). If the boundary
case resists, return `BLOCKED` and the orchestrator restricts G.30's even branch to `t + 2 ≤ N`,
which costs one stratum in G.43's identity and is booked as a known `q^(−N)`-order discrepancy.

**SIZE.** 30 lines.

**SOURCE.** `EFF.W11.15`; `EFF.W11.08`; `EFF.W11.22`.

**TEETH.** `W11-CENSUS`, `W11-EXHAUST` → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.31 [lemma] [fresh]

**STATEMENT.** *The level-`N` partition.* The three decided sets and the undecided set partition
the level-`N` box exactly, and the decided sets are the unions of their strata:
`decidedSet ram = ⋃_{t odd, t<N} depthSet t`, `decidedSet inert = ⋃_{k, 2k<N} inertStratum k`,
`decidedSet split = ⋃_{k, 2k<N} splitStratum k`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The inert/split halves of an even stratum. -/
def inertStratum (π : O) (N k : ℕ) : Set (Coeff O 2 N) :=
  {c ∈ depthSet π N (2 * k) | DecidedAt O 2 inertType N c}

def splitStratum (π : O) (N k : ℕ) : Set (Coeff O 2 N) :=
  {c ∈ depthSet π N (2 * k) | DecidedAt O 2 splitType N c}

theorem decidedSet_ram_eq (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    decidedSet O 2 ramType N = ⋃ j ∈ Finset.range N, depthSet π N (2 * j + 1)
```

**DEPENDS.** G.19, G.29, G.30 · landed `decidedSet`, `decidedSet_disjoint`, `typeOf_two_cases`
(`Drainage.lean:866`), `undecidedSet`.

**PROOF.**
1. (⊇) each stratum is ram-decided by G.30.
2. (⊆) let `c` be ram-decided. Then `c ∉ tangSet π N N`: a class in `tangSet π N N` has two lifts
   of different types (G.33, G.34), so no type is decided on it. Hence `c` has a maximal depth
   `t < N` (`exists_max_step`, landed at `Drainage.lean:556`, applied to
   `Q t := ∃ γ, Tang π a t γ`), i.e. `c ∈ depthSet π N t`.
3. G.30 at that `t`: if `t` were even, `c` would be inert- or split-decided, contradicting
   `decidedSet_disjoint` with the ram-decidedness. So `t` is odd.
4. the index bound `j < N` from `2j+1 < N`.

**SIZE.** 30 lines. Three public declarations (two defs + one theorem); the two companion
theorems `decidedSet_inert_eq`, `decidedSet_split_eq` are **separate nodes' work** and are folded
into G.41/G.42's proofs rather than stated here.

**SOURCE.** `EFF.W11.10` (clause (iii): "The families of (i) plus the σ-undecided residue
partition all `q^(2N)` polynomials"); `EFF.W11.08` (the corrected partition: "six genuine
decided-shape families ⊔ SPLIT-TAIL_N boundary cells ⊔ σ-UNDECIDED cells").

**TEETH.** `W11-EXHAUST` / P-4 ("all 90 classical-sandwich inequalities hold as exact rationals")
→ **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

## 6. §6 — `n = 2`: THE EXACT DRAINAGE LAW

### NODE G.32 [lemma] [fresh]

**STATEMENT.** Over a finite field, for every nonzero `b₁` there is a `b₀` making `X² − b₁X + b₀`
irreducible. (False for `b₁ = 0` in characteristic 2 — every element is a square there — which is
exactly why G.34 must choose the depth at the *exact* valuation of the derivative.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem exists_aniForm_of_ne_zero (K : Type*) [Field K] [Finite K] {b₁ : K} (hb : b₁ ≠ 0) :
    ∃ b₀ : K, AniForm (b₀, b₁)
```

**DEPENDS.** landed `AniForm` (`AnisotropicForms.lean:55`).

**PROOF.**
1. consider `φ : K → K`, `φ y = b₁ * y - y ^ 2`; `AniForm (b₀, b₁)` fails iff `b₀ ∈ Set.range φ`
   (a root `y` of `y² − b₁y + b₀` is exactly a preimage).
2. `φ y = φ y' ↔ (y − y') * (b₁ − (y + y')) = 0`, so `φ y' = φ y` iff `y' = y` or `y' = b₁ − y`.
3. hence every fibre of `φ` has at least two elements *except* the fibre of `y = b₁ − y`, which
   exists for at most one `y`; so `2 * Nat.card (Set.range φ) ≤ Nat.card K + 1`.
4. `Nat.card K ≥ 2` (`Finite.one_lt_card`), so `Nat.card (Set.range φ) < Nat.card K` by `omega`.
5. therefore `Set.range φ ≠ Set.univ`; take `b₀` outside it.

**SIZE.** 26 lines.

**SOURCE.** `EFF.W11.16` (the residual census: irreducible count `q(q−1)/2` per the table, which
is `≥ 1` for every `q ≥ 2` — this node is the qualitative corollary the drainage argument needs);
`EFF.W11.22` (the `[r1, F6]` scoping: "per MEMBER, split and inert lifts BOTH always exist … but a
ram lift can be ABSENT — a char-2 member with exact `w = N/2` has only split and inert lifts, its
residual `c₁ ≠ 0` blocking the refine a ram lift would need").

**⚠ THIS NODE IS THE LEAN FORM OF W-11's `[r1, F6]` CORRECTION.** The struck text claimed the
undecided residue contains split, inert *and* ram lifts per member; the corrected text says split
and inert always exist and ram can be absent. G.33 + G.34 prove exactly the corrected statement,
and this node is why the inert half survives in characteristic 2.

**TEETH.** `W11-CENSUS` (the residual-census rows, both characteristics) → **Lean theorem**.

**ENVIRONMENT.** ENV-C.

---

### NODE G.33 [lemma] [fresh]

**STATEMENT.** A class with a depth-`N` centre has a `splitType` lift: kill the value at the
centre.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem exists_split_lift (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = splitType
```

**DEPENDS.** landed `typeOf_split_of_root` (`Drainage.lean:263`), `proj_eq_iff_dvd`
(`DensityAPI.lean:124`), `qval`.

**PROOF.**
1. put `b := ![a 0 - qval a γ, a 1]`.
2. `qval b γ = qval a γ - qval a γ = 0` by `simp [qval]; ring`.
3. `typeOf_split_of_root` gives `typeOf (monicPoly b) = splitType`.
4. `proj O 2 N b = proj O 2 N a`: by `proj_eq_iff_dvd hπ`, coordinatewise; the `1`-coordinate is
   equal, the `0`-coordinate differs by `qval a γ`, which `hT.1` says is `π^N`-divisible.

**SIZE.** 14 lines.

**SOURCE.** `EFF.W11.22` (`[r1, F6]`: split lifts always exist); `EFF.W11.19` (the `disc = 0`
two-case statement's mixed-characteristic witness `(x+2)²` is an instance of this construction).

**TEETH.** `W11-ORACLE` (the double-lift leg, "0 double-lift disagreements among the 1,070 decided
members") → **executable regression** (retained).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.34 [lemma] [fresh]

**STATEMENT.** A class with a depth-`N` centre has an `inertType` lift. Construction: read the
derivative's **exact** valuation `m` at the centre (or manufacture `m = N` by moving `a₁` inside
the class when the derivative vanishes), note `2m ≥ N`, and perturb `a₀` by `π^(2m)·u` with `u`
chosen so that the residual pair `(u, qder/π^m)` is anisotropic — possible by G.32, because
`qder/π^m` is a **unit**.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem exists_inert_lift (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = inertType
```

**DEPENDS.** G.02, G.32, G.33 · landed `typeOf_of_certInert` (`Drainage.lean:329`), `CertInert`,
`Anisotropic`, `aniForm_iff` (`AnisotropicForms.lean:59`), `proj_eq_iff_dvd`,
`IsLocalRing.residue_surjective`, `exists_addVal_eq`.

**PROOF.**
1. **Case A — `qder a γ ≠ 0`.** Let `m := addVal O (qder a γ)` (finite, G.02) and write
   `qder a γ = π^m * v` with `v` a unit (`exists_unit_mul_pow_of_addVal_eq`,
   `StrongHensel.lean:232`).
2. `m ≥ (N+1)/2` from `hT.2`, hence `2m ≥ N` (`omega`).
3. `G.32` applied to `K := ResidueField O` and `b₁ := residue O v ≠ 0` gives `b̄₀` with
   `AniForm (b̄₀, residue O v)`; lift to `u : O` by `residue_surjective`.
4. put `b := ![a 0 - qval a γ + π^(2*m) * u, a 1]`.
5. `qval b γ = π^(2m) * u` and `qder b γ = π^m * v` (`simp [qval, qder]; ring`).
6. `Anisotropic ![u, v]` by `aniForm_iff` + step 3 (anisotropy only reads the residues —
   the landed `Anisotropic_congr`, `Drainage.lean:472`, is the same observation).
7. `CertInert π b (2*m+1) := ⟨γ, m, u, v, le_refl _, step 5a, step 5b, step 6⟩`, then
   `typeOf_of_certInert hπ`.
8. `proj O 2 N b = proj O 2 N a`: the `0`-coordinate differs by `−qval a γ + π^(2m) u`, and
   `π^N` divides both summands (`hT.1`; `2m ≥ N`).
9. **Case B — `qder a γ = 0`.** Put `a' := ![a 0, a 1 + π^N]`, so `proj O 2 N a' = proj O 2 N a`
   and `qder a' γ = π^N`; `Tang π a' N γ` still holds (the value is unchanged, the derivative is
   `π^N`-divisible and `(N+1)/2 ≤ N`). Apply Case A to `a'` with `m = N`.

**SIZE.** 40 lines. **Split candidate:** Case A as `G.34a`, Case B's reduction as `G.34b`.

**SOURCE.** `EFF.W11.22` (`[r1, F6]`, the corrected member-level statement); `EFF.W11.15`
(the INERTDEEP leaf whose certificate this constructs).

**⚠ ARITHMETIC CROSS-CHECK.** The construction needs `2m ≥ N`, which is exactly `hT.2`'s content
`m ≥ ⌈N/2⌉`. It does **not** need `m ≤ N`, and indeed Case B produces `m = N`. This is the step
where the naive "make a RAM lift instead" fails: a ram lift needs an odd exact value valuation
`M` with `N ≤ M ≤ 2m − 1`, which is empty when `m = ⌈N/2⌉` and `N` is even — precisely W-11's
char-2 counterexample. The inert route has no such constraint.

**TEETH.** `W11-CENSUS` / `W11-EXHAUST` → **Lean theorem**.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.35 [lemma] [fresh]

**STATEMENT.** `undecidedSet O 2 N = tangSet π N N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem undecidedSet_eq_tangSet (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    undecidedSet O 2 N = tangSet π N N
```

**DEPENDS.** G.09, G.12, G.29, G.33, G.34 · landed `undecidedSet`, `UndecidedAt`
(`Drainage.lean:676`), `splitType_ne_inertType` (`QuadCert.lean:67`), `proj_surjective`.

**PROOF.**
1. (⊇) let `c ∈ tangSet π N N`, with lift `a` and centre `γ`. Suppose `σ` is decided on `c`.
   G.33 gives a lift `b₁` of type `splitType`, G.34 a lift `b₂` of type `inertType`; both project
   to `c` (their `proj` equals `proj a = c`). Decidedness forces `splitType = σ = inertType`,
   contradicting `splitType_ne_inertType`.
2. (⊆) contrapositive: if `c ∉ tangSet π N N` then G.29 decides it, so `c ∉ undecidedSet`.

**SIZE.** 18 lines.

**SOURCE.** `EFF.W11.26` (the drainage law's defining locus); `EFF.W11.22`.

**TEETH.** `W11-EXHAUST` / P-4 → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.36 [theorem] [fresh]

**STATEMENT.** **THE EXACT `n = 2` DRAINAGE LAW.** `undecidedCount O 2 N = q^N`, for every
complete DVR with finite residue field, every `N`, both characteristics.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **W-11 clause (iii), exactly: the `n = 2` σ-undecided count is `q^N`.** Every complete DVR
with finite residue field, every level `N`, both characteristics, wild residue characteristic
included. This is the exact form of the landed bound `undecidedCount_le` (which gives only
`q^(3M)` at level `2M`). -/
theorem undecidedCount_two_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedCount O 2 N = residueCard O ^ N
```

**DEPENDS.** G.17, G.35 · landed `undecidedCount` (`Drainage.lean:683`),
`IsDiscreteValuationRing.exists_irreducible`.

**PROOF.**
1. `obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O`.
2. `rw [undecidedCount, undecidedSet_eq_tangSet hπ N]` (G.35).
3. `card_tangSet hπ N 0` (G.17 with `t := N`, `r := 0`; the level `N + 0` is `N` by `Nat.add_zero`)
   gives `q^(N + 2*0) = q^N`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.W11.10` (clause (iii): "the σ-undecided count is EXACTLY `q^N`");
`EFF.W11.26` (the derivation: "undecided per center = `q^⌈(N−1)/2⌉·q^⌊(N−1)/2⌋ = q^(N−1)`;
× `q` centers = **`q^N` EXACTLY**").

**⚠ THIS IS THE CHAPTER'S HEADLINE `n = 2` NODE.** It sharpens `Drainage.lean`'s own disclosure
("The count `q^(3M)` is deliberately lossy: W-11's exact law is `q^N` undecided classes at level
`N` (here `q^(2M)`, so the bound is off by the factor `q^M`)") to the exact law, and it does so
without the per-centre census the landed docstring says would be required — the depth filtration
replaces it.

**TEETH.** `W11-EXHAUST` / P-4 (`EFF.W11.35`, "undecided = `q^N` on every row"; 0/150 violations
on 30 census rows, both characteristics) → **Lean theorem**. `W11-T-DRAIN` (30 firings) →
**Lean theorem**.

**ENVIRONMENT.** ENV-B (note: stated in `Uniformity.Density`, not `Menu`, because it is a theorem
about a landed object).

---

### NODE G.37 [theorem] [fresh]

**STATEMENT.** The exact drainage **rate**: `undecidedSeq O 2 N = (1/q)^N`, and therefore
`gapSeq O 2 σ N ≤ (1/q)^N` for every `σ` — the exact `q^(−N)` law W-11 clause (iii) states.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem undecidedSeq_two_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedSeq O 2 N = (1 / (residueCard O : ℝ)) ^ N

theorem gapSeq_two_le [IsAdicComplete (maximalIdeal O) O] (σ : FactorizationType) (N : ℕ) :
    gapSeq O 2 σ N ≤ (1 / (residueCard O : ℝ)) ^ N
```

**DEPENDS.** G.36 · landed `undecidedSeq` (`Drainage.lean:686`), `gapSeq_le_undecidedSeq`
(`Drainage.lean:716`), `qpow_pos`.

**PROOF.**
1. `rw [undecidedSeq, undecidedCount_two_eq]`.
2. `(q^N : ℝ) / q^(2*N) = (1/q)^N`: `div_pow`, `pow_mul`, `field_simp` with `qpow_ne`.
3. second statement: `gapSeq_le_undecidedSeq 2 N σ` composed with step 1.

**SIZE.** 12 lines.

**SOURCE.** `EFF.W11.10`; `EFF.W11.26` ("Normalized: `q^(−N) → 0`. ∎(hExhaust at `n = 2`, exact
rate)"); `EFF.W11.30` (the capstone tie: "the bracket width is `q^(−N)` exactly").

**TEETH.** `W11-T-DRAIN` → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

## 7. §7 — `n = 2`: EXACT COUNTS, EXACT DENSITIES, THE CAPSTONE SLICE

### NODE G.38 [lemma] [fresh]

**STATEMENT.** Over a finite field, the anisotropic pairs number `q(q−1)/2`, stated
subtraction-free: `2·#{p | AniForm p} + q = q·q`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem two_mul_card_aniForm (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // AniForm p} + Nat.card K = Nat.card K * Nat.card K
```

**DEPENDS.** landed `AniForm`, `rootPairMap`, `rootPairMap_injective`, `exists_rootPairMap_iff`,
`two_mul_choose_two` (`AnisotropicForms.lean:55–124`), mathlib `Sym2.natCard`.

**PROOF.**
1. `{p | ¬ AniForm p} = Set.range (rootPairMap K)` by `exists_rootPairMap_iff`.
2. `Nat.card (Set.range (rootPairMap K)) = Nat.card (Sym2 K)` by `rootPairMap_injective`.
3. `Sym2.natCard`: `Nat.card (Sym2 K) = Nat.choose (Nat.card K + 1) 2`.
4. `two_mul_choose_two`: `2 * Nat.choose (q+1) 2 = q * (q+1)`.
5. the two subtypes are complementary in `K × K`, so
   `Nat.card {p // AniForm p} + Nat.card {p // ¬ AniForm p} = Nat.card K * Nat.card K`
   (`Nat.card_eq_fintype_card`, `Fintype.card_subtype_compl`, `Nat.card_prod`).
6. multiply step 5 by 2 and substitute steps 3–4; `omega`.

**SIZE.** 20 lines.

**⚠ RE-DERIVATION TARGET.** `leancheck/UniformityCheck/FiniteFieldQuad.lean` lands exactly this
statement as `two_mul_card_aniK` (11 lines, 3 `have`s) on top of its own `AniK`; the leanfinal
predicate `AniForm` is definitionally the same and all four support lemmas are already in
`leanfinal`. Expect ≤ 20 lines.

**SOURCE.** `EFF.W11.16` (the residual census, row "irreducible": count `q(q−1)/2`, both
characteristics — "THE LOCI DIFFER ACROSS CHARACTERISTICS; THE COUNTS DO NOT").

**TEETH.** `W11-CENSUS` (the residual-census constants) → **Lean theorem**; `HEX3-CHAR`
(`EFF.HEX3.49`, 17 cross-characteristic pairs) → **Lean theorem** (this node *is* the
characteristic-uniformity of the count, now a theorem rather than a measured tally).

**ENVIRONMENT.** ENV-C.

---

### NODE G.39 [lemma] [fresh]

**STATEMENT.** Over a finite field, the pairs whose quadratic has **two distinct roots** number
`q(q−1)/2` — the same count as the anisotropic ones. Subtraction-free:
`2·#{p | SepPair p} + q = q·q`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- `p = (b₀, b₁)` is a *separable-split* pair: `X² − b₁X + b₀` has two distinct roots. -/
def SepPair {K : Type*} [Field K] (p : K × K) : Prop :=
  ∃ y z : K, y ≠ z ∧ p = (y * z, y + z)

theorem two_mul_card_sepPair (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // SepPair p} + Nat.card K = Nat.card K * Nat.card K
```

**DEPENDS.** G.38 · landed `rootPairMap`, `rootPairMap_injective`, `exists_rootPairMap_iff`,
mathlib `Sym2.natCard`, `Sym2.IsDiag`.

**PROOF.**
1. `{p | SepPair p} = rootPairMap K '' {s | ¬ s.IsDiag}` (a `Sym2` element is off-diagonal iff its
   two entries differ).
2. `rootPairMap_injective` transports the count: `Nat.card {p // SepPair p}
   = Nat.card {s : Sym2 K // ¬ s.IsDiag}`.
3. the diagonal is the image of `K` under `s ↦ Sym2.mk (y, y)`, injective, so
   `Nat.card {s // s.IsDiag} = Nat.card K`.
4. `Nat.card {s // ¬ IsDiag} + Nat.card K = Nat.card (Sym2 K) = Nat.choose (q+1) 2`.
5. multiply by 2, apply `two_mul_choose_two`, `omega`.

**SIZE.** 24 lines.

**SOURCE.** `EFF.W11.16` (row "separable split": count `(q−1)(q−2)/2` **per `c₁`-normalisation** —
see the cross-check).

**⚠ ARITHMETIC CROSS-CHECK (this is the one place where a naive transcription of W-11 would
mis-state the count).** W-11's residual census table (`EFF.W11.16`) counts pairs
`(c₁, c₀) ∈ F_q × F_q^*` — the constant term is **restricted to be nonzero**, because at a genuine
refine node `c₀ = digit_{2k}(A₀) ≠ 0`. Its rows are `(q−1)(q−2)/2` (split), `q(q−1)/2`
(irreducible), `q−1` (double root), summing to `q(q−1)` ✓. This chapter's strata are indexed by
**all** pairs `(b₀, b₁) ∈ F_q²`, because the depth filtration does not normalise `b₀` away; its
rows are `q(q−1)/2` (split), `q(q−1)/2` (irreducible), `q` (double root), summing to `q²` ✓. The
two tables are consistent: the split row gains the `q−1` pairs with `b₀ = 0, b₁ ≠ 0` (which are
W-11's 2SIDED/SPLIT-TAIL entries, counted separately there), and the double-root row gains the one
pair `(0,0)`; the irreducible row is unchanged because an irreducible quadratic has `b₀ ≠ 0`
automatically. **`(q−1)(q−2)/2 + (q−1) = (q−1)q/2` ✓ and `(q−1) + 1 = q` ✓.** A cross-reader must
not "correct" G.39 to W-11's `(q−1)(q−2)/2`.

**TEETH.** `W11-CENSUS` → **Lean theorem**.

**ENVIRONMENT.** ENV-C.

---

### NODE G.40 [lemma] [fresh]

**STATEMENT.** The double-root pairs number exactly `q`, and the three classes (anisotropic,
separable-split, double-root) partition `K × K`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

def DblPair {K : Type*} [Field K] (p : K × K) : Prop := ∃ y : K, p = (y * y, y + y)

theorem card_dblPair (K : Type*) [Field K] [Finite K] :
    Nat.card {p : K × K // DblPair p} = Nat.card K

theorem pair_trichotomy {K : Type*} [Field K] (p : K × K) :
    AniForm p ∨ SepPair p ∨ DblPair p
```

**DEPENDS.** G.38, G.39 · landed `AniForm`, `exists_rootPairMap_iff`.

**PROOF.**
1. `card_dblPair`: `y ↦ (y*y, y+y)` is injective (its first coordinate determines `y` up to sign
   and the second pins it: from `y*y = z*z` and `y+z ≠ 0` one gets `y = z`; if `y + z = 0` then
   `y + y = z + z` forces `2y = -2y`, and in every characteristic `(y*y, y+y) = (z*z, z+z)` with
   `y*y = z*z` gives `(y−z)² = y² − 2yz + z² = 2y² − 2yz = 2y(y−z)`, so `(y−z)(y−z−2y) = 0`,
   i.e. `y = z` or `z = −y`; in the second case `y+y = z+z = −(y+y)` so `4y = 0`… **land this as
   the private helper `dblPair_inj` and prove it uniformly by:** `(y*y, y+y) = (z*z, z+z)` implies
   `y` and `z` are both roots of `X² − (y+y)X + y*y = (X − y)²`, hence `z = y`).
2. `pair_trichotomy`: if `¬ AniForm p`, the quadratic has a root `y`; then the other root is
   `p.2 − y` and `p = ((p.2−y)*y, (p.2−y)+y)`; `by_cases y = p.2 − y` splits `DblPair` from
   `SepPair`.
3. exhaustiveness of the counts is then `2·(q(q−1)/2) + q = q²` (G.38 + G.39 + this node) — a
   consistency check the formalizer should `omega` at the end of the file.

**SIZE.** 22 lines.

**SOURCE.** `EFF.W11.16` (row "double root ≠ 0", count `q−1`; plus the excluded `c₀ = 0` pair —
see G.39's cross-check).

**TEETH.** `W11-CENSUS` → **Lean theorem**.

**ENVIRONMENT.** ENV-C.

---

### NODE G.41 [theorem] [fresh]

**STATEMENT.** **The inert stratum count.** At level `N = 2k+1+r`,
`2·#(inertStratum π N k) + q^(2k+2r+1) = q^(2k+2r+2)` — i.e. `#inertStratum = ((q−1)/2)·q^(2N−2k−1)`,
which is W-11's whole-space INERTDEEP(k) count.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_inertStratum (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (inertStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2)
```

**DEPENDS.** G.21, G.22, G.23, G.26, G.27, G.31, G.38 · landed `card_certSet_gen`.

**PROOF.**
1. `inertStratum π N k = ⋃ (p : AniForm) resStratum π N k p` — by G.30's dichotomy (a class of
   depth `2k` is inert-decided iff its residual pair is anisotropic; the "only if" needs
   `decidedSet_disjoint` against the split branch).
2. the union is over the finite index `{p // AniForm p}` and is disjoint (the residual pair of a
   class is well defined up to the centre coset, G.23's pinning).
3. `Nat.card` of a finite disjoint union is the sum (`Nat.card_biUnion` / `Set.ncard_iUnion` for
   pairwise-disjoint families over a `Finset` index).
4. each summand is `q^(2N−2k−2) = q^(2k+2r)` by G.23.
5. so `#inertStratum = Nat.card {p // AniForm p} * q^(2k+2r)`; multiply by 2 and apply G.38:
   `2·#Ani·q^(2k+2r) + q·q^(2k+2r) = q²·q^(2k+2r)`, i.e. the statement after `pow_succ`.

**SIZE.** 30 lines.

**⚠ RE-DERIVATION TARGET AND INDEPENDENT CROSS-CHECK.** `leancheck`'s landed
`InertCensus.card_inertSet` is **the same statement, verbatim**:
`2 * Nat.card (inertSet π k (2*k+1+r)) + residueCard O ^ (2*k+2*r+1) = residueCard O ^ (2*k+2*r+2)`
— but proved by a *different route* (a direct `card_certSet` census with `S = aniPairSet`, 32
lines / 5 `have`s, resting on `AniCount.card_aniPairSet`, 29/8, and its bijection lemma
`card_aniPairSet_eq`, 76/17). **The agreement of the two routes is a genuine check on this
chapter's depth-filtration design**, and it is the reason the filtration route may be abandoned
for the leancheck route if G.23's declared defect proves fatal: the *statement* is the same, so
nothing downstream changes. The orchestrator should treat "G.41 by the leancheck route" as a
sanctioned fallback, not a re-plan.

**SOURCE.** `EFF.W11.09` (INERTDEEP(k): `((q−1)/2)·q^(2N−2k−2)` per centre); `EFF.W11.07`
(limit density `(q−1)/(2q^(2k+1))` whole-space); `EFF.W11.16`.

**TEETH.** `W11-CENSUS` / P-2 (the INERTDEEP rows on 30 census rows) → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.42 [theorem] [fresh]

**STATEMENT.** **The split stratum count.** At level `N = 2k+1+r`,
`2·#(splitStratum π N k) + q^(2k+2r+1) = q^(2k+2r+2)` — numerically identical to G.41.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_splitStratum (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (splitStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2)
```

**DEPENDS.** G.21–G.23, G.26, G.28, G.30, G.31, G.39.

**PROOF.** verbatim G.41 with `AniForm` replaced by `SepPair` and G.38 by G.39.

**SIZE.** 30 lines (or ~6 if the formalizer factors G.41/G.42 through a shared private lemma
parametrised by the residual predicate — **recommended**, and it triggers a RE-PLAN request:
`card_stratum_of_residualClass` is reusable at `n = 3`).

**SOURCE.** `EFF.W11.09` (2SIDED, SPLITEQ, SPLIT-TAIL rows — jointly this stratum, per §0.4's
dictionary); `EFF.W11.16`; `EFF.W11.25` (the SPLIT-TAIL boundary mass).

**TEETH.** `W11-CENSUS` / P-2 → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.43 [theorem] [fresh]

**STATEMENT.** **THE EVERY-WINDOW `split = inert` IDENTITY.** For every level `N`,
`decidedCount O 2 splitType N = decidedCount O 2 inertType N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **W-11's every-window identity, exactly:** at every level the split-decided and inert-decided
classes are equinumerous — not merely equal in the limit. The mechanism is the residue-field
coincidence `#{anisotropic pairs} = #{separable-split pairs} = q(q−1)/2`. -/
theorem decidedCount_split_eq_inert [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedCount O 2 splitType N = decidedCount O 2 inertType N
```

**DEPENDS.** G.31, G.41, G.42 · landed `decidedCount`.

**PROOF.**
1. `obtain ⟨π, hπ⟩ := exists_irreducible O`.
2. `decidedSet O 2 splitType N = ⋃_{k : 2k < N} splitStratum π N k` and the same for inert
   (G.31's companions, proved inside G.41/G.42).
3. both counts are `∑_{k < ⌈N/2⌉}` of their stratum counts, over the same index range.
4. G.41 and G.42 give the same value for each `k` (both satisfy the same equation with the same
   right-hand side; cancel by `Nat.add_right_cancel` and `Nat.eq_of_mul_eq_mul_left two_pos`).
5. `Finset.sum_congr rfl`.

**SIZE.** 20 lines.

**SOURCE.** `EFF.W11.10` (clause (iii)'s last sentence: "Moreover split-decided = inert-decided
EXACTLY at EVERY window (not just in the limit)"); `EFF.W11.27` (W-11's own proof, via the finite
telescope transcribed from `W11_passPE2_report.md` @ 473a993).

**⚠ PROOF-ROUTE DIVERGENCE, DECLARED.** W-11 proves this by a *finite telescoping identity* over
the split legs at fixed `A₁`-valuation, whose deficit is filled by the SPLIT-TAIL cell, and the
note itself flags the step's unusual provenance (a pass report, not the note's own voice —
`EFF-W11` §8 item 4). **This chapter proves it by a different mechanism**: the two residue-field
counts of G.38 and G.39 coincide. The two routes agree on every number; the chapter's route is
shorter and does not need the boundary family. PE4's disc-fibration derivation
(`EFF.W11.40`: "third independent derivation of every-window split = inert") is a third route,
and this node makes a fourth. **A cross-reader should verify that the chapter's route is not
circular**: G.38/G.39 are pure finite-field facts with no `n = 2` input, and G.41/G.42 differ only
in which residue predicate indexes the union.

**TEETH.** `W11-EXHAUST` / P-4 ("split-decided = inert-decided EXACTLY on all 30 rows") →
**Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.44 [lemma] [fresh]

**STATEMENT.** The level-`N` decided proportions of `ram` and `inert` as finite sums:
`decidedSeq O 2 ramType N = ∑_{j < ⌈N/2⌉} (q−1)/q^(2j+2)` and
`decidedSeq O 2 inertType N = ∑_{k < ⌈N/2⌉} (q−1)/(2·q^(2k+1))`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem decidedSeq_two_ram_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 ramType N
      = ∑ j ∈ Finset.range ((N + 1) / 2),
          ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ (2 * j + 2)

theorem decidedSeq_two_inert_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 inertType N
      = ∑ k ∈ Finset.range ((N + 1) / 2),
          ((residueCard O : ℝ) - 1) / (2 * (residueCard O : ℝ) ^ (2 * k + 1))
```

**DEPENDS.** G.20, G.25, G.31, G.41 · landed `decidedSeq`, `decidedCount`, `qpow_ne`.

**PROOF.**
1. ram: `decidedCount O 2 ramType N = ∑_{j : 2j+1 < N} Nat.card (depthSet π N (2j+1))` (G.31),
   each term `(q−1)q^(2N−2j−2)` (G.20 read multiplicatively).
2. divide by `q^(2N)` and simplify each term to `(q−1)/q^(2j+2)` (`div_div_eq_div_mul`,
   `pow_sub` guarded by `2j+2 ≤ 2N`).
3. the index set `{j | 2j+1 < N}` is `Finset.range ((N+1)/2)` — `omega` after `Finset.ext`.
4. inert: same, with G.41's `#inertStratum = ((q−1)/2)q^(2N−2k−1)` (divide the G.41 equation by 2
   in `ℝ`, where the division is legal).

**SIZE.** 34 lines. **Split candidate:** the two statements as separate nodes G.44a/G.44b.

**SOURCE.** `EFF.W11.09`; `EFF.W11.07` (the per-row limit densities `(q−1)/q^(h+1)` and
`(q−1)/(2q^(2k+1))`).

**⚠ ARITHMETIC CROSS-CHECK.** Summing the ram series to infinity: `∑_{j≥0}(q−1)q^(−2j−2)
= (q−1)q^(−2)/(1−q^(−2)) = (q−1)/(q²−1) = 1/(q+1)` ✓ W-11's ram total. Summing the inert series:
`∑_{k≥0}(q−1)/(2q^(2k+1)) = ((q−1)/(2q))·(1/(1−q^(−2))) = (q−1)q/(2(q²−1)) = q/(2(q+1))` ✓ W-11's
inert total. Both match `EFF.W11.10` exactly.

**TEETH.** `W11-CENSUS` → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.45 [lemma] [fresh]

**STATEMENT.** The geometric-limit bridge: for `c : ℝ` and `q ≥ 2`,
`Tendsto (fun N => ∑_{i < f N} c/q^(2i+d)) atTop (𝓝 (c·q^(−d)·q²/(q²−1)))` whenever `f N → ∞`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem tendsto_geom_partial (c : ℝ) (d : ℕ) {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun N => ∑ i ∈ Finset.range (f N), c / (residueCard O : ℝ) ^ (2 * i + d)) atTop
      (𝓝 (c / (residueCard O : ℝ) ^ d * ((residueCard O : ℝ) ^ 2
        / ((residueCard O : ℝ) ^ 2 - 1))))
```

**DEPENDS.** landed `qR_pos`, `one_lt_residueCard` (`LocalData.lean:95`) · mathlib
`hasSum_geometric_of_lt_one`, `HasSum.tendsto_sum_nat`, `Filter.Tendsto.comp`.

**PROOF.**
1. rewrite the summand as `(c/q^d) * (q^(−2))^i`.
2. `hasSum_geometric_of_lt_one` at ratio `q^(−2) ∈ [0,1)` (`one_lt_residueCard`), giving the sum
   `1/(1 − q^(−2)) = q²/(q²−1)`.
3. `HasSum.tendsto_sum_nat` for the partial sums along `Finset.range`.
4. compose with `hf`.

**SIZE.** 22 lines.

**⚠ RE-DERIVATION TARGET.** `leancheck/UniformityCheck/N2Base.lean` lands the same bridge in
closed form (`census_sum`, plus `decidedDensity_of_census` at 65 lines / 20 `have`s, which is the
*whole* census⟹density pipeline). Chapter G splits that monolith into G.44 + G.45 + G.46, which
is why each piece is small.

**SOURCE.** `EFF.W11.12` (C7-F2's four aggregate geometric sums, each of exactly this shape);
`EFF.W11.27`.

**TEETH.** `HM3-RTAU` / `W11-CENSUS` → **executable regression** (the symbolic summation stays in
`verification/`).

**ENVIRONMENT.** ENV-A.

---

### NODE G.46 [theorem] [fresh]

**STATEMENT.** `decidedDensity O 2 ramType = 1/(q+1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem decidedDensity_two_ram_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
```

**DEPENDS.** G.44, G.45 · landed `decidedSeq_tendsto` (`GenuineDensity.lean:286`).

**PROOF.**
1. `decidedSeq_tendsto 2 ramType` : the sequence tends to `decidedDensity O 2 ramType`.
2. G.44 rewrites the sequence as the partial sums of G.45 with `c = q−1`, `d = 2`,
   `f N = (N+1)/2` (which tends to `atTop` by `omega`-style monotonicity).
3. G.45 gives the limit `((q−1)/q²)·(q²/(q²−1)) = (q−1)/(q²−1) = 1/(q+1)`
   (`field_simp` with `q ≠ 0`, `q² ≠ 1`; the last step needs `q + 1 ≠ 0`).
4. `tendsto_nhds_unique`.

**SIZE.** 18 lines.

**⚠ RE-DERIVATION TARGET.** `leancheck`'s `N2Exact.ram_decidedDensity_two` is the same statement
(41 lines / 9 `have`s) at general `O`.

**SOURCE.** `EFF.W11.10` (clause (iii): "ram-total = `1/(q+1)`"); `EFF.W11.07` (the RAM(h) row).

**TEETH.** `W11-EXHAUST` (the classical sandwich, exact rationals) → **Lean theorem**;
`gate_bracket_w11_two`/`_three` (landed in `Gates.lean:573,581`) → **Lean theorem** (this node
replaces the containment check by the value).

**ENVIRONMENT.** ENV-B.

---

### NODE G.47 [theorem] [fresh]

**STATEMENT.** `decidedDensity O 2 inertType = decidedDensity O 2 splitType = q/(2(q+1))`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem decidedDensity_two_inert_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))

theorem decidedDensity_two_split_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
```

**DEPENDS.** G.43, G.44, G.45, G.46 · landed `decidedSeq_tendsto`,
`sum_three_decidedDensities_eq_one` (`Drainage.lean:962`).

**PROOF.**
1. inert: as G.46 with `c = (q−1)/2`, `d = 1`, limit `((q−1)/(2q))·(q²/(q²−1)) = q/(2(q+1))`.
2. split, **route 1 (independent)**: G.43 makes the two sequences equal at every `N`, so the
   limits agree.
3. split, **route 2 (cross-check, must also be recorded)**: `sum_three_decidedDensities_eq_one`
   gives `split = 1 − ram − inert = 1 − 1/(q+1) − q/(2(q+1)) = q/(2(q+1))` by `field_simp`.
   **Both routes are required in the node file**, as a mutual check; they use disjoint inputs
   (route 1 uses the every-window identity, route 2 uses the landed total-mass theorem).

**SIZE.** 26 lines.

**⚠ RE-DERIVATION TARGET.** `leancheck`'s `N2Exact.inert_decidedDensity_two` and
`split_decidedDensity_two` land exactly these values at general `O`; there, split is obtained by
route 2 only (subtraction), so **route 1 is new** and is what upgrades the corpus's every-window
claim from a density statement to a count statement.

**SOURCE.** `EFF.W11.10`; `EFF.W11.12` (the aggregate route: `Σ2SIDED + ΣSPLITEQ = 1/(2q(q+1))
= ΣINERTDEEP`, so `split = (q−1)/(2q) + 1/(2q(q+1)) = q/(2(q+1))`).

**TEETH.** `W11-EXHAUST` → **Lean theorem**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.48 [theorem] [fresh]

**STATEMENT.** The same three values over **THE** density `genuineDensity`, and `Σ = 1`; every
other type has density `0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **THE `n = 2` DENSITY FUNCTION, EXACTLY.** Over every complete DVR with finite residue field,
both characteristics, wild residue characteristic included. -/
theorem genuineDensity_two_exact [IsAdicComplete (maximalIdeal O) O] :
    genuineDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
    ∧ (∀ σ : FactorizationType, σ ≠ splitType → σ ≠ inertType → σ ≠ ramType →
        genuineDensity O 2 σ = 0)
```

**DEPENDS.** G.46, G.47 · landed `genuineDensity_eq_decidedDensity_two` (`Drainage.lean:858`),
`genuineDensity_two_eq_zero` (`Drainage.lean:1037`), `sum_three_densities_eq_one`
(`Drainage.lean:1080`).

**PROOF.** each conjunct is `rw [genuineDensity_eq_decidedDensity_two]` followed by G.46/G.47; the
fourth is the landed `genuineDensity_two_eq_zero` verbatim.

**SIZE.** 14 lines.

**SOURCE.** `EFF.W11.10`; `EFF.W11.27` ("totals: split = inert = `(q−1)/(2q) + 1/(2q(q+1))
= q/(2(q+1))`. Sum: `2·q/(2(q+1)) + 1/(q+1) = 1`. ∎(i)(ii)(iii)").

**⚠ ARITHMETIC CROSS-CHECK.** `2·q/(2(q+1)) + 1/(q+1) = q/(q+1) + 1/(q+1) = 1` ✓, matching the
landed `sum_three_densities_eq_one` — so this node's values are *consistent with* a theorem
already in the repo, which is a real (if weak) check that they are not a transcription slip.

**TEETH.** `W11-EXHAUST`; `W11-ORACLE` → **Lean theorem** / **executable regression**
respectively.

**ENVIRONMENT.** ENV-B.

---

### NODE G.49 [gate] [fresh]

**STATEMENT.** The `ℤ_[2]` and `ℤ_[3]` instances: `split = inert = ram = 1/3` at `q = 2`;
`split = inert = 3/8`, `ram = 1/4` at `q = 3`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem gate_two_padic_two_exact :
    genuineDensity ℤ_[2] 2 splitType = 1 / 3 ∧ genuineDensity ℤ_[2] 2 inertType = 1 / 3
      ∧ genuineDensity ℤ_[2] 2 ramType = 1 / 3

theorem gate_two_padic_three_exact :
    genuineDensity ℤ_[3] 2 splitType = 3 / 8 ∧ genuineDensity ℤ_[3] 2 inertType = 3 / 8
      ∧ genuineDensity ℤ_[3] 2 ramType = 1 / 4
```

**DEPENDS.** G.48 · landed `residueCard_padicInt` (`LocalData.lean:343`).

**PROOF.** instantiate G.48 at `O := ℤ_[p]`, `rw [residueCard_padicInt p]`, `norm_num`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.W11.30` (the capstone tie at `q = 2`: `1/4 + 1/12 = 1/3`); `EFF.W11.34`
(the smoke table's `(Zp,2,4)` row).

**⚠ GATE SEMANTICS.** These values sit strictly inside the landed brackets
`gate_bracket_padic_two` (`[1/4, 11/16]`, `[1/4, 11/16]`, `[1/16, 1/2]`) and
`gate_bracket_padic_three` — the landed `gate_bracket_w11_two`/`_three` theorems assert exactly
that containment as `norm_num` facts. **This node closes those brackets to points.** A regression
here is a stop-the-line event.

**TEETH.** `gate_bracket_w11_two`, `gate_bracket_w11_three` (landed) → **Lean theorem**.

**ENVIRONMENT.** ENV-B (no variables; both statements are about concrete `ℤ_[p]`).

---

### NODE G.50 [lemma] [fresh]

**STATEMENT.** Every degree-2 splitting type is one of the three, so the density function at
`n = 2` is completely determined by G.48.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem degree_two_type_cases {σ : FactorizationType} (hσ : σ.degree = 2) :
    σ = splitType ∨ σ = inertType ∨ σ = ramType ∨
      (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        genuineDensity O 2 σ = 0)
```

**DEPENDS.** landed `genuineDensity_two_eq_zero`.

**PROOF.**
1. `by_cases` the three equalities.
2. otherwise the fourth disjunct is `genuineDensity_two_eq_zero` applied per `O`.

**SIZE.** 10 lines. **Design note:** the fourth disjunct is deliberately *not* a claim that no
other degree-2 type exists as a `FactorizationType` (e.g. `⟨{(1,1)}⟩ + ⟨{(1,1)}⟩` in a different
`Multiset` presentation is `splitType`, but `⟨{(2,2)}⟩` has degree 4 and `⟨{(1,1),(1,1),(1,1)}⟩`
degree 3); it is the density statement, which is what the capstone needs.

**SOURCE.** `EFF.W11.10`.

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-A (statement quantifies `O` internally).

---

### NODE G.51 [theorem] [fresh]

**STATEMENT.** **THE CAPSTONE AT `n = 2`, UNCONDITIONAL.** For every degree-2 splitting type
there is one rational function of `q`, valid over every complete DVR with finite residue field,
giving `genuineDensity O 2 σ`. This is the `n = 2` instance of `UniformityStatement`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **`UniformityStatement` at `n = 2`.** One rational function per degree-2 type, valid at every
complete DVR with finite residue field — wild residue characteristic included, both
characteristics. Unconditional: no drainage hypothesis, no axiom, Lean core only. -/
theorem uniformityStatement_two (σ : FactorizationType) (hσ : σ.degree = 2) :
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O 2 σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
```

**DEPENDS.** G.48, G.50 · landed `UniformityStatement` (`Statement.lean:71`),
`two_le_residueCard`.

**PROOF.**
1. `rcases degree_two_type_cases hσ` (G.50).
2. split/inert: `num := X`, `den := 2*(X+1)`; `den ≠ 0` by `Polynomial.ne_zero_of_natDegree_gt`
   or direct evaluation; `den.eval q = 2(q+1) ≠ 0` because `q ≥ 2` (`two_le_residueCard`,
   cast to `ℚ`); the value is G.48's first two conjuncts, with the `ℚ → ℝ` coercion pushed by
   `push_cast`.
3. ram: `num := 1`, `den := X + 1`.
4. the fourth case: `num := 0`, `den := 1`; the value is `0` by G.50's fourth disjunct.

**SIZE.** 34 lines.

**SOURCE.** `EFF.W11.05` (the Divergence box: "the `R_τ ∈ ℚ(q)` tie falls out at `n = 2` as a
corollary (every menu row and every σ-total is one rational function of `q`, S2.5/S5) — delivered
as display, not as the general-`r` theorem"); `EFF.W11.32`.

**⚠ WHAT THIS IS AND IS NOT.** It is the `n = 2` slice of the repo's capstone target, proved. It
is **not** `UniformityStatement`, which quantifies over all `n > 0`; the general statement needs
every degree. Nobody may record "the capstone is proved" on the strength of this node. The honest
sentence is: *the uniformity theorem is proved at `n = 1` (landed, `Gates.lean`) and at `n = 2`
(this node), unconditionally, over every complete DVR with finite residue field.*

**TEETH.** `W11-ORACLE` (per-polynomial PARI on 8,252 polynomials) → **executable regression**;
`gate_bracket_w11_two`/`_three` → **Lean theorem**.

**ENVIRONMENT.** ENV-B (the statement carries its own `∀ O` binder, as `UniformityStatement`
does; the section variables are not used).

---

## 8. §8 — `n = 3`: THE FIVE TYPES, THE MENU, THE LEAF CERTIFICATES

### NODE G.52 [def] [fresh]

> **AMENDMENT BANNER 2026-08-15 — SIGNATURE AMENDED: `c3_pairwise_ne` (G.52g) now STATES the ten
> inequalities** (it was the literal placeholder `/- the ten inequalities -/ True`, i.e. vacuous —
> stage-0e defect **D3**). The real conjunction and its proof are in **AMENDMENT §A-6**, landed in
> `leanfinal` and re-signed in `leanspec`. The five `def`s and `c3_degrees` are unchanged. Nothing
> below is edited.

**STATEMENT.** The five degree-3 splitting types, with their degrees and pairwise distinctness.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- `{(1,1),(1,1),(1,1)}` — three unramified linear factors. -/
def c3split : FactorizationType := ⟨{(1, 1), (1, 1), (1, 1)}⟩
/-- `{(1,1),(1,2)}` — a linear factor and an unramified quadratic. -/
def c3linInert : FactorizationType := ⟨{(1, 1), (1, 2)}⟩
/-- `{(1,3)}` — one unramified cubic factor. -/
def c3inert : FactorizationType := ⟨{(1, 3)}⟩
/-- `{(1,1),(2,1)}` — a linear factor and a ramified quadratic. -/
def c3linRam : FactorizationType := ⟨{(1, 1), (2, 1)}⟩
/-- `{(3,1)}` — one totally ramified cubic factor. -/
def c3ram : FactorizationType := ⟨{(3, 1)}⟩

theorem c3_degrees :
    c3split.degree = 3 ∧ c3linInert.degree = 3 ∧ c3inert.degree = 3
      ∧ c3linRam.degree = 3 ∧ c3ram.degree = 3

theorem c3_pairwise_ne : /- the ten inequalities -/ True
```

**DEPENDS.** landed `FactorizationType`, `FactorizationType.degree`.

**PROOF.** definitional; the degrees by `simp [FactorizationType.degree]`; the ten inequalities by
`decide` after reducing to multiset inequality (`Multiset.card` or membership separates each
pair).

**SIZE.** 30 lines across 5 defs + 2 theorems (the ten inequalities are one-liners).

**⚠ RE-DERIVATION TARGET.** `leancheck/UniformityCheck/N3Base.lean` lands all five definitions
with exactly these names and the fifteen `decide`-backed degree/distinctness one-liners
(6.7 lines per declaration — the cheapest node family in the chapter).

**SOURCE.** `EFF.HMENU3.17` (COROLLARY HM3.D's five rows: `(1,1)³`, `(1,2),(1,1)`, `(1,3)`,
`(2,1),(1,1)`, `(3,1)`).

**TEETH.** `HM3-RTAU` → **executable regression** (the symbolic densities keyed by these types).

**ENVIRONMENT.** ENV-A.

---

### NODE G.53 [theorem] [fresh]

**STATEMENT.** **The `n = 3` analogue of `typeOf_two_cases`.** Every monic cubic over a DVR has
one of the five types. **The proof is purely combinatorial**: `typeOf_degree` forces
`Σ eᵢfᵢ = 3` and `efPair_pos_of_mem` forces every `eᵢ, fᵢ ≥ 1`, so the multiset of products is a
partition of `3` into positive parts (`{3}`, `{2,1}`, `{1,1,1}`), and `e·f = 3` with `3` prime
gives `(e,f) ∈ {(1,3),(3,1)}`, `e·f = 2` gives `(1,2)` or `(2,1)`, `e·f = 1` gives `(1,1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **Exactly five splitting types occur in degree 3.** No Newton polygon, no Hensel: the
statement is a consequence of `typeOf_degree` and the positivity of every `(e,f)` pair. -/
theorem typeOf_three_cases (a : Fin 3 → O) :
    typeOf (monicPoly a) = c3split ∨ typeOf (monicPoly a) = c3linInert
      ∨ typeOf (monicPoly a) = c3inert ∨ typeOf (monicPoly a) = c3linRam
      ∨ typeOf (monicPoly a) = c3ram
```

**DEPENDS.** G.52 · landed `typeOf_degree` (`TypeOf.lean:372`), `efPair_pos_of_mem`
(`TypePositivity.lean:55`), `efPair_mul_le_natDegree` (`TypePositivity.lean:69`),
`monicPoly_monic`, `monicPoly_natDegree`, `FactorizationType.ext`.

**PROOF.**
1. put `M := (typeOf (monicPoly a)).data`; `typeOf_degree` + `monicPoly_natDegree` give
   `(M.map (fun p => p.1 * p.2)).sum = 3`.
2. every element of `M.map (·.1 * ·.2)` is `≥ 1` (`efPair_pos_of_mem` and
   `Nat.one_le_iff_ne_zero`), so `Multiset.card M ≤ 3`
   (`Multiset.card_nsmul_le_sum`, the argument landed verbatim in `CoveringMenus.lean:88–96`).
3. `interval_cases` on `Multiset.card M ∈ {1,2,3}` (`card = 0` contradicts the sum `3`).
4. `card = 1`: `Multiset.card_eq_one` gives `M = {p}` with `p.1 * p.2 = 3`; `Nat.eq_one_of_...`
   / `Nat.Prime.eq_one_of_pos_of_dvd` on `Nat.prime_three` gives `p = (1,3)` or `(3,1)`.
5. `card = 2`: `M = {p, p'}` with `p.1p.2 + p'.1p'.2 = 3` and both `≥ 1`, so `{1, 2}` in some
   order; the `2`-part is `(1,2)` or `(2,1)`, the `1`-part is `(1,1)`.
6. `card = 3`: all three products are `1`, so all three pairs are `(1,1)`.
7. in each case `FactorizationType.ext` closes against the corresponding `c3…` definition
   (multiset equality up to `Multiset` commutativity — `Multiset.cons_swap` / `decide` on the
   small multisets).

**SIZE.** 40 lines. **Split candidate:** steps 4–6 as three private helpers keyed by the card.

**⚠ THIS NODE IS NEW.** `leancheck`'s `N3Drain.lean` docstring names its absence explicitly:
the converse of `drainage_three_of_triple` "would need the `n = 3` analogue of
`typeOf_two_cases`". Chapter G supplies it, and it is the input to G.54.

**SOURCE.** `EFF.HMENU3.17` (the five-row density table is exactly this type list);
`EFF.HMENU3.27` ("Cross-stratum disjointness: level-0 factorization type separates SEP/DBL/TRP").

**TEETH.** `HM3-ORACLE` (`EFF.HMENU3.47`, PARI confirms the σ multiset of every deep-decided
member on four rows, 9,952 members) → **executable regression** (retained; it confirms the σ
*values*, whereas this node proves the *exhaustiveness of the list*, which no battery can).

**ENVIRONMENT.** ENV-A.

---

### NODE G.54 [theorem] [fresh]

**STATEMENT.** The five types form a covering menu at degree 3; every other type has genuine
density `0` at `n = 3`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem coveringMenu_three :
    CoveringMenu O 3 ({c3split, c3linInert, c3inert, c3linRam, c3ram} : Finset FactorizationType)

theorem genuineDensity_three_eq_zero {σ : FactorizationType} (hs : σ ≠ c3split)
    (hi : σ ≠ c3linInert) (hc : σ ≠ c3inert) (hr : σ ≠ c3linRam) (ht : σ ≠ c3ram) :
    genuineDensity O 3 σ = 0
```

**DEPENDS.** G.52, G.53 · landed `CoveringMenu` (`GenuineDensity.lean:458`),
`genuineDensity_eq_zero_of_forall_ne` (`DensityAPI.lean:69`).

**PROOF.**
1. `coveringMenu_three`: `intro a`; `rcases typeOf_three_cases a` (G.53); `simp` in each branch.
2. `genuineDensity_three_eq_zero`: `genuineDensity_eq_zero_of_forall_ne` applied to
   `fun a => by rcases typeOf_three_cases a with h|h|h|h|h <;> rw [h] <;> assumption`
   (each branch contradicts one of the five hypotheses).

**SIZE.** 16 lines.

**SOURCE.** `EFF.HMENU3.14` (THEOREM HM3.C's menu list `{SEP3, SEPLQ, SEPC} ∪ {DBL-…} ∪ TRP`, of
which this is the *type*-level shadow); `EFF.HMENU3.17`.

**⚠ SCOPE NOTE.** `CoveringMenu` is a statement about **types**, not about HMENU3's **families**.
This node does **not** prove HM3.C's menu (which is a statement about decided *strata* with exact
counts, and rests on the two-species grammar). Do not cite this node as `(hMenu-3)` — see H-3.

**TEETH.** `HM3-MENU` (`EFF.HMENU3.42`, 1,031 checks) → **executable regression** (retained: the
family-level menu is not proved here).

**ENVIRONMENT.** ENV-A.

---

### NODE G.55 [lemma] [fresh]

**STATEMENT.** *SEP3 leaf.* A monic cubic whose reduction has three distinct roots in the residue
field splits into three monic linear factors, so its type is `c3split`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem typeOf_split3_of_residue [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (ρ₁ ρ₂ ρ₃ : O) (h12 : IsUnit (ρ₁ - ρ₂)) (h13 : IsUnit (ρ₁ - ρ₃)) (h23 : IsUnit (ρ₂ - ρ₃))
    (hres : (monicPoly a).map (residue O)
      = (X - C (residue O ρ₁)) * (X - C (residue O ρ₂)) * (X - C (residue O ρ₃))) :
    typeOf (monicPoly a) = c3split
```

**DEPENDS.** G.52 · landed `exists_monic_factorization_finset` (CN-17, `MultiHensel.lean:111`),
`typeOf_prod_X_sub_C` (CN-14, `TypeOfAlgebra.lean:90`), `typeOf_mul` (CN-03),
`typeOf_of_natDegree_one`.

**PROOF.**
1. the three residual linear factors are pairwise coprime (`IsCoprime` of two monic linears with
   distinct roots over a field: `isCoprime_of_isUnit_of_...`, or directly by exhibiting the Bézout
   pair `(ρᵢ − ρⱼ)⁻¹`).
2. `exists_monic_factorization_finset` over `s := Finset.univ : Finset (Fin 3)` lifts to monic
   `g₁ g₂ g₃` with `monicPoly a = g₁g₂g₃` and `natDegree gᵢ = 1`.
3. each `gᵢ` is `X − C rᵢ` (`Monic.eq_X_add_C`), so `typeOf_prod_X_sub_C` gives the type
   `⟨Multiset.replicate 3 (1,1)⟩ = c3split`.

**SIZE.** 40 lines.

**⚠ RE-DERIVATION TARGET, WITH A KNOWN VACUITY.** `leancheck`'s `N3Certs.typeOf_split3_of_residue`
(51 lines / 14 `have`s) is the same statement. Its docstring records that the hypothesis is
**vacuous at `q = 2`** (there is no monic cubic over `F₂` with three distinct roots), which is why
`leancheck` also lands the *deep* split certificate `typeOf_split3_of_deep` (84 lines / 35 `have`s
— the largest proof in that layer, using the window-3 class of `X(X−1)(X−π)`). **Chapter G lands
the residue certificate here and the deep one at G.74**, because the deep one is also the split
half of the `n = 3` undecided lower bound.

**SOURCE.** `EFF.HMENU3.27` (SEP families: "W-12 S2.1/S2.3 (level-0 separable patterns are decided
at level 0, counts `C₀(q)·q^(3(N−1))`; point families, `d_F = 0`)").

**TEETH.** `HM3-ORACLE` → **executable regression**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.56 [lemma] [fresh]

**STATEMENT.** *SEPLQ leaf.* A monic cubic whose reduction factors as a linear times an
irreducible quadratic has type `c3linInert`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem typeOf_linInert_of_residue [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    {ρ : O} {g₀ : Polynomial (ResidueField O)} (hg₀ : g₀.Monic) (hdeg : g₀.natDegree = 2)
    (hirr : Irreducible g₀)
    (hres : (monicPoly a).map (residue O) = (X - C (residue O ρ)) * g₀) :
    typeOf (monicPoly a) = c3linInert
```

**DEPENDS.** G.52 · landed `typeOf_of_residual_coprime` (CN-18, `TypeOfAlgebra.lean:131`),
`typeOf_inert_of_irreducible_map` (CN-21, `InertLeaf.lean:179`), `typeOf_of_natDegree_one`,
`typeOf_mul`.

**PROOF.**
1. `X − C ρ̄` and `g₀` are coprime: `g₀` is irreducible of degree 2 and does not vanish at `ρ̄`
   (else it would have a linear factor).
2. `typeOf_of_residual_coprime` splits `monicPoly a = g·h` with `g` monic of degree 1, `h` monic
   of degree 2, `h.map (residue O) = g₀`, and `(typeOf (monicPoly a)).data
   = (typeOf g).data + (typeOf h).data`.
3. `typeOf g = ⟨{(1,1)}⟩` by `typeOf_of_natDegree_one`.
4. `typeOf h = ⟨{(1,2)}⟩` by `typeOf_inert_of_irreducible_map` (its hypothesis is exactly
   `Irreducible (h.map (residue O))`, i.e. `hirr` after rewriting by step 2's `hmap`).
5. `FactorizationType.ext` on the multiset sum.

**SIZE.** 30 lines. **RE-DERIVATION TARGET:** `leancheck`'s `N3Certs.typeOf_linInert_of_residue`
is the same statement in *coefficient* form (`Anisotropic ![β₀, β₁]` plus three congruences,
45 lines / 10 `have`s). The `leanfinal` form above is shorter because CN-18 and CN-21 are landed
there; a formalizer may take either statement shape, but **the coefficient form is the one G.61
consumes**, so land both if they diverge (the second as a private corollary).

**SOURCE.** `EFF.HMENU3.27`; `EFF.HMENU3.17` (the `(1,2),(1,1)` row).

**TEETH.** `HM3-ORACLE` → **executable regression**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.57 [lemma] [fresh]

**STATEMENT.** *SEPC leaf.* A monic cubic with irreducible reduction has type `c3inert`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem typeOf_inert3_of_irreducible_map [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (h : Irreducible ((monicPoly a).map (residue O))) : typeOf (monicPoly a) = c3inert
```

**DEPENDS.** G.52 · landed `typeOf_inert_of_irreducible_map` (CN-21), `monicPoly_monic`,
`monicPoly_natDegree`.

**PROOF.** `typeOf_inert_of_irreducible_map (monicPoly_monic a) (by rw [monicPoly_natDegree];
norm_num) h` gives `⟨{(1, 3)}⟩` after rewriting `natDegree = 3`; that is `c3inert` by `rfl`.

**SIZE.** 8 lines — **the cheapest certificate in the chapter**, because CN-21 is landed at
general `n`.

**SOURCE.** `EFF.HMENU3.27`; `EFF.HMENU3.17` (the `(1,3)` row).

**TEETH.** `HM3-ORACLE` → **executable regression**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.58 [lemma] [fresh]

**STATEMENT.** *The totally ramified leaf.* An Eisenstein monic cubic has type `c3ram`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem typeOf_ram3_of_eisenstein {a : Fin 3 → O}
    (hlow : ∀ i : Fin 3, a i ∈ maximalIdeal O) (h0 : a 0 ∉ (maximalIdeal O) ^ 2) :
    typeOf (monicPoly a) = c3ram
```

**DEPENDS.** G.52 · landed `typeOf_eisenstein` (CN-20, `NormLeaves.lean:93`),
`monicPoly_coeff_lt` (`Transport.lean:34`), `monicPoly_monic`, `monicPoly_natDegree`.

**PROOF.**
1. `typeOf_eisenstein` needs `∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O` and
   `f.coeff 0 ∉ 𝔪²`; `monicPoly_coeff_lt` identifies `(monicPoly a).coeff i` with `a ⟨i, _⟩` for
   `i < 3`.
2. it returns `⟨{(f.natDegree, 1)}⟩ = ⟨{(3,1)}⟩ = c3ram` after `monicPoly_natDegree`.

**SIZE.** 14 lines. **RE-DERIVATION NOTE:** `leancheck` proves this from scratch at 45 lines /
14 `have`s (`N3Norm.typeOf_ram3_of_eisenstein`) because CN-20 did not exist when it was written;
in `leanfinal` it is a two-step instantiation. **This is the clearest single illustration of what
the landed CN batch bought.**

**SOURCE.** `EFF.HMENU3.17` (the `(3,1)` row, "wild at `p = 3`"); `EFF.HEX3.13` (the RAM3 depth-0
species).

**TEETH.** `HM3-ORACLE` (the `(Zp,3,5)` wild deep row: "972 deep-RAM3 members = wild totally
ramified cubics behind a refinement step — all confirmed `{(3,1)}`") → **executable regression**.

**ENVIRONMENT.** ENV-A (no completeness needed — CN-20 does not use it).

---

### NODE G.59 [lemma] [fresh]

**STATEMENT.** *The partially ramified leaf.* A monic cubic with `a₂` a unit and `a₁, a₀ ∈ 𝔪`,
`a₀ ∉ 𝔪²`, has type `c3linRam`: Hensel peels a unit-root linear factor and the remaining quadratic
is Eisenstein.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem typeOf_linRam_of_residue [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (h2 : IsUnit (a 2)) (h1 : a 1 ∈ maximalIdeal O) (h0 : a 0 ∈ maximalIdeal O)
    (h0' : a 0 ∉ (maximalIdeal O) ^ 2) : typeOf (monicPoly a) = c3linRam
```

**DEPENDS.** G.52 · landed `typeOf_of_residual_coprime` (CN-18), `typeOf_ram_of_eisenstein`
(`QuadCert.lean:283`), `typeOf_of_natDegree_one`, `typeOf_mul`.

**PROOF.**
1. the reduction is `X³ + ā₂X² = X²(X + ā₂)` with `ā₂ ≠ 0`, so it factors as `g₀ h₀` with
   `g₀ = X + ā₂` (degree 1) and `h₀ = X²`, which are coprime because `ā₂ ≠ 0`.
2. CN-18 lifts: `monicPoly a = g·h`, `g` monic degree 1, `h` monic degree 2 with `h.map = X²`,
   i.e. both lower coefficients of `h` in `𝔪`.
3. `h`'s constant coefficient is `a 0 / g's constant coefficient` up to a unit, so it is in
   `𝔪 \ 𝔪²` (the unit factor cannot move the valuation) — **this is the step to be careful with**:
   from `monicPoly a = g·h`, comparing constant terms gives `a 0 = g(0)·h(0)` with `g(0)` a unit
   (since `ḡ(0) = ā₂ ≠ 0`), so `h(0) ∈ 𝔪 \ 𝔪²` follows from `h0`, `h0'`.
4. `typeOf_ram_of_eisenstein` on `h` gives `ramType = ⟨{(2,1)}⟩`; `typeOf_of_natDegree_one` on `g`
   gives `⟨{(1,1)}⟩`; CN-03 adds them to `c3linRam`.

**SIZE.** 34 lines. **RE-DERIVATION TARGET:** `leancheck`'s `N3Certs.typeOf_linRam_of_residue`,
same statement, 39 lines / 13 `have`s.

**SOURCE.** `EFF.HMENU3.17` (the `(2,1),(1,1)` row, "partially ramified; wild at `p = 2`");
`EFF.HMENU3.09` (the dictionary row `RAM(u) ↦ ('RAM2LIN', 3m+u, m)` — the same object in raw-key
coordinates).

**TEETH.** `HM3-ORACLE`; `HM3-XREAD` → **executable regression**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.60 [lemma] [fresh]

**STATEMENT.** The residue-field cubic census, subtraction-free:
`3·#{no root} + q = q³`, `2·#{linear × irreducible quadratic} + q² = q³`,
`6·#{three distinct roots} + 3q² = q³ + 2q`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

def NoRootCubic {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∀ y : K, y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 ≠ 0

def LinAni {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ (ρ : K) (p : K × K), AniForm p ∧ c = ![-(ρ * p.1), p.1 + ρ * p.2, -(p.2 + ρ)]

def Split3 {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ r s t : K, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ c = ![-(r * s * t), r*s + r*t + s*t, -(r + s + t)]

theorem three_mul_card_noRootCubic (K : Type*) [Field K] [Finite K] :
    3 * Nat.card {c : Fin 3 → K // NoRootCubic c} + Nat.card K = Nat.card K ^ 3

theorem two_mul_card_linAni (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {c : Fin 3 → K // LinAni c} + Nat.card K ^ 2 = Nat.card K ^ 3

theorem six_mul_card_split3 (K : Type*) [Field K] [Finite K] :
    6 * Nat.card {c : Fin 3 → K // Split3 c} + 3 * Nat.card K ^ 2 = Nat.card K ^ 3 + 2 * Nat.card K
```

**DEPENDS.** G.38 · mathlib `Finset.inclusion_exclusion_card_inf_compl`,
`Finset.sum_powerset_apply_card`, `Nat.choose`.

**PROOF.** three independent counts:
1. `three_mul_card_noRootCubic` — inclusion–exclusion over the root sets: `#{c | c has a root}`
   is computed from `#(⋂_{y ∈ t} {c | c(y) = 0}) = q^(3−#t)` for `#t ≤ 3` and `0` beyond, and a
   cubic has at most 3 roots.
2. `two_mul_card_linAni` — the explicit parametrisation `(ρ, p) ↦ ![-(ρ p.1), p.1 + ρ p.2,
   -(p.2 + ρ)]` is injective, so the count is `q · #{p | AniForm p}`; apply G.38.
3. `six_mul_card_split3` — the map `c ↦ {r, s, t}` is a bijection onto 3-element subsets of `K`,
   so the count is `Nat.choose q 3`; then `6·C(q,3) = q(q−1)(q−2) = q³ − 3q² + 2q`.

**SIZE.** 3 nodes' worth: 50 (inclusion–exclusion) + 22 (bijection) + 30 (bijection) lines.
**SPLIT MANDATED:** land as **G.60a/G.60b/G.60c**, one per count.

**⚠ RE-DERIVATION TARGET.** `leancheck` lands all three verbatim
(`CubicCount.three_mul_card_noRootCubic` 47/7, `CubicCount.two_mul_card_linAni` 20/2,
`SplitCount.six_mul_card_split3` 12/1 on top of `card_split3` 22/5), together with the
inclusion–exclusion input `card_inf_cubicRootSet` (41/3). Chapter G re-derives them in `leanfinal`
against `AniForm` instead of `AniK`.

**SOURCE.** `EFF.HMENU3.27` (the SEP counts `C₀(q)·q^(3(N−1))`); `EFF.HMENU3.17` (the five
densities, whose SEP parts are these three counts divided by `q³`).

**⚠ ARITHMETIC CROSS-CHECK.** The five residue-level cubic classes must exhaust `q³`:
`#(3 distinct roots) + #(1 root + irr. quadratic) + #(no root) + #(double+simple) + #(triple)`
`= q(q−1)(q−2)/6 + q·q(q−1)/2 + (q³−q)/3 + q(q−1) + q`. At `q = 2`: `0 + 2 + 2 + 2 + 2 = 8` ✓;
at `q = 3`: `1 + 9 + 8 + 6 + 3 = 27` ✓. The last two classes are *not* counted in this node —
they are the residually-degenerate strata, which chapter G does not certify (H-3).

**TEETH.** `HM3-MENU` / `HM3-AGG` → **executable regression**.

**ENVIRONMENT.** ENV-C.

---

### NODE G.61 [theorem] [fresh]

**STATEMENT.** The five general-`O` decided-density lower bounds at `n = 3`, from the level-1 and
level-2 certificates and their counts.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem lowers_three [IsAdicComplete (maximalIdeal O) O] :
    1 / (residueCard O : ℝ) ^ 9 ≤ decidedDensity O 3 c3split
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3linInert
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3inert
    ∧ ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3linRam
    ∧ ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3ram
```

**DEPENDS.** G.55–G.60, G.74 · landed `decidedDensity_ge_of_subset` (CN-09),
`decidedAt_of_congr` (CN-08), `proj_eq_iff_dvd` (CN-07).

**PROOF.** five independent instances of the same pattern: exhibit an injection from a counted
index set into `decidedSet O 3 σ N` (level `1` for `linInert`, `inert`; level `2` for `ram`,
`linRam`; level `3` for `split`), then apply CN-09. The certificates are G.55–G.59 lifted to
classes by CN-08.

**SIZE.** 5 sub-nodes, 20–40 lines each; **SPLIT MANDATED** into G.61a…G.61e.

**⚠ RE-DERIVATION TARGET.** `leancheck`'s `N3Gates.lowers_three` is this exact statement at
general `O` (the five `gate_*_lower` proofs are 4–38 lines each, median 20/5, all through the
workhorse `N3Density.decidedDensity_ge_of_inj`, 13 lines — **the blueprint recommends landing that
workhorse first as G.61.0**: "only an injection is needed, never an exact count").

**SOURCE.** `EFF.HMENU3.17` (the five target values `R_τ`); `EFF.HMENU3.27`.

**⚠ THESE ARE LOWER BOUNDS, NOT THE DENSITIES.** The HM3.D targets (`EFF.HMENU3.17`) are
`q³(q²−q+1)/(6(q+1)Φ)`, `q³(q²+q+1)/(2(q+1)Φ)`, `q³(q+1)/(3Φ)`, `q(q³+q+1)/((q+1)Φ)`,
`(q²+1)/Φ` with `Φ = q⁴+q³+q²+q+1`. **This node proves none of them** (H-4).

**MANDATORY NUMERIC CONSISTENCY CHECK (computed for this blueprint, `q = 2`).** targets
`(4/93, 28/93, 8/31, 22/93, 5/31) ≈ (0.0430, 0.3011, 0.2581, 0.2366, 0.1613)`; this node's bounds
`(1/512, 1/4, 1/4, 1/16, 1/16) ≈ (0.0020, 0.2500, 0.2500, 0.0625, 0.0625)`. Every bound is below
its target ✓, with the two SEP bounds tight to within `5–17%` and the two ramified ones loose by
`~4×` (they are level-2 single-stratum bounds). At `q = 3` the targets are
`(63/968, 351/968, 36/121, 93/484, 10/121) ≈ (0.0651, 0.3626, 0.2975, 0.1922, 0.0826)` and the
bounds are `(1/19683, 1/3, 8/27, 4/81, 2/81) ≈ (0.00005, 0.3333, 0.2963, 0.0494, 0.0247)` ✓.
**A cross-reader should re-run this check**: a bound exceeding its target would be a genuine
contradiction (`decidedDensity ≤ genuineDensity` is landed), and it is the cheapest available
falsifier of either the bounds or the transcribed targets.

**TEETH.** `HM3-RTAU` (30 checks, symbolic) → **executable regression**; `HM3-ORACLE` →
**executable regression**.

**ENVIRONMENT.** ENV-B.

---

## 9. §9 — THE 53-FAMILY INDEX AND THE HEX3 ARITHMETIC LAYER

### NODE G.62 [def] [fresh]

> **AMENDMENT BANNER 2026-08-15 — `CubicFamilyIndex.schema` (G.62b) NOW HAS A BODY, DERIVED FROM
> `EFF-HMENU3`** (it was a `def` with no body, underdetermined by the prose here — stage-0e defect
> **D2**). The full 53 → 33 assignment table and its per-step derivation are in **AMENDMENT §A-5**;
> the body is landed in `leanfinal` and re-signed as a real `def` in `leanspec`. The
> `CubicFamilyIndex` inductive and the `schema` **signature** are unchanged. Nothing below is
> edited.

**STATEMENT.** *The cubic family index (ANNEX B).* HMENU3's menu, after ANNEX B's fixed-λ and
`b(m)`-regime refinements, consists of **53 formal families** organised as
`3` SEP + `4` DBL + `11` tier-I + `11` tier-II + `24` B-tier, refining `33` shape schemas
(`3 + 4 + 7 + 7 + 12`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The ANNEX-B index of the cubic core menu: 53 formal families in five tiers. This is an INDEX,
not a family: it carries no counts and no certificates. See the chapter honesty block H-3. -/
inductive CubicFamilyIndex
  | sep    : Fin 3  → CubicFamilyIndex
  | dbl    : Fin 4  → CubicFamilyIndex
  | tierI  : Fin 11 → CubicFamilyIndex
  | tierII : Fin 11 → CubicFamilyIndex
  | bTier  : Fin 24 → CubicFamilyIndex
  deriving DecidableEq, Fintype

/-- The shape schema underlying each formal family (ANNEX B's "33 shape schemas"). -/
def CubicFamilyIndex.schema : CubicFamilyIndex → Fin 33
```

**DEPENDS.** none (a finite index type).

**PROOF.** definitional; `schema` is an explicit table (`3 + 4 + 7 + 7 + 12 = 33` targets, with
tier-I's 11 formal families mapping onto 7 schemas, tier-II's 11 onto 7, the B-tier's 24 onto 12 —
each pair `(m = 0, m ≥ 1)` or `(λ = (1,1), λ = (2))` collapsing to one schema).

**SIZE.** 24 lines.

**SOURCE.** `EFF.HMENU3.67` (ANNEX B), `EFF.HMENU3.69` (the family arithmetic),
`EFF.HMENU3.62` (the acceptance record's re-read: "complete **53-formal-family** cubic core menu
(33 shape schemas before the fixed-λ and b-regime refinements)"), `EFF.HMENU3.11` (the tier list),
`EFF.HMENU3.09` (the dictionary rows that already fix λ on the β side — which is why ANNEX B's
refinement bites only on tiers I and II).

**⚠ WHAT THIS NODE IS.** ANNEX B is a **counter re-reading**, not a mathematical correction: its
own closing sentence fences it — "This annex repairs a formal indexing gap. It changes no raw-key
law, density, complement, splitting-type formula, machine result or conditionality"
(`EFF.HMENU3` resolution rule 3). This node therefore formalises *the index arithmetic only*, and
`card = 53` (G.63) is the entire Lean content of ANNEX B. **Nobody may read this node as the cubic
menu.**

**TEETH.** none — ANNEX B is `AUDIT`-produced (`EFF.HMENU3` §6.4: "an arithmetic recount"; no
battery row can produce or falsify it).

**ENVIRONMENT.** ENV-A (no `O`; the index is a bare finite type).

---

### NODE G.63 [lemma] [fresh]

**STATEMENT.** `#CubicFamilyIndex = 53` and the schema map is surjective onto `Fin 33`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_cubicFamilyIndex : Nat.card CubicFamilyIndex = 53

theorem schema_surjective : Function.Surjective CubicFamilyIndex.schema
```

**DEPENDS.** G.62.

**PROOF.** `decide` (both statements are finite checks); if `decide` times out,
`Fintype.card_sum`-style arithmetic on the five constructors: `3+4+11+11+24 = 53`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.HMENU3.67`, `EFF.HMENU3.69`.

**⚠ ARITHMETIC CROSS-CHECK.** `3 + 4 + 11 + 11 + 24 = 53` ✓ and `3 + 4 + 7 + 7 + 12 = 33` ✓ —
ANNEX B's two totals, which supersede HM3-BOX-5's withdrawn "≤ 45 TRP aggregate families + 4 DBL
+ 3 SEP" (`EFF.HMENU3` chain row C-6) and the acceptance record's "33-family" (row C-7). A
consumer must apply **all four** of C-4/C-5/C-6/C-7 or none (`EFF.HMENU3` §1, same-span collision
note (b)).

**TEETH.** none (see G.62).

**ENVIRONMENT.** ENV-A.

---

### NODE G.64 [def] [fresh]

**STATEMENT.** *The HEX3 residual recursion `R`.* `R(q, M)` counts the level-`M` block states
whose `n = 2` chain reaches `A₀ = 0`; its closed form is
`R(M) = q^(M−1) + ⌊(M−1)/2⌋·(q−1)·q^(M−2)`, with `R(1) = 1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- HEX3's `R(M)`: the `n = 2` conservative-drain count per centre at window `M`
(`EFF.HEX3.26`, LEMMA H-4). Pure arithmetic — this definition mentions no ring. -/
def hex3R (q M : ℕ) : ℕ := q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 4 lines.

**SOURCE.** `EFF.HEX3.26` (LEMMA H-4, with its derivation: the `w`-summand
`(q−1)q^(M−1−w)·q^(w−1) = (q−1)q^(M−2)` is independent of `w`, so the sum collapses).

**⚠ THE IDENTIFICATION A CROSS-READER SHOULD MAKE.** `R(M)` is exactly W-11's *shape-truncated*
undecided count per centre: `q^(M−1)` is W-11's σ-undecided aggregate and
`⌊(M−1)/2⌋(q−1)q^(M−2)` is its SPLIT-TAIL aggregate (`EFF.W11.25`, `EFF.W11.30`'s second
convention). So `q·R(N)` is the whole-space count of the shape-truncated convention, and
`undecidedCount O 2 N = q^N` (G.36) is the σ-convention. **The two conventions differ by exactly
the SPLIT-TAIL mass** — this is W11-BOX-5 (`EFF.W11.33`), and G.36 proves the σ-convention half.
Chapter G does **not** prove `q·hex3R q N` equals any Lean-side count.

**TEETH.** `HEX3-T-FLOOR` (`EFF.HEX3.50`, exactly 10 rows, guards `R(M)`'s floor term) →
**executable regression** (retained; the Lean side has no `O`-level tie to `R`).

**ENVIRONMENT.** ENV-A (no `O`).

---

### NODE G.65 [lemma] [fresh]

**STATEMENT.** The `R`-recursion: `R(M) = q^(M−1) + (q−1)·∑_{j ≥ 1, 2j ≤ M−1} q^j·R(M−2j)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem hex3R_rec (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    hex3R q M
      = q ^ (M - 1) + (q - 1) * ∑ j ∈ Finset.Icc 1 ((M - 1) / 2), q ^ j * hex3R q (M - 2 * j)
```

**DEPENDS.** G.64.

**PROOF.** by strong induction on `M`, or directly: substitute the closed form on the right and
evaluate the sum. Each summand is `q^j·(q^(M−2j−1) + ⌊(M−2j−1)/2⌋(q−1)q^(M−2j−2))`; summing over
`j = 1 … ⌊(M−1)/2⌋` and multiplying by `(q−1)` telescopes to
`⌊(M−1)/2⌋(q−1)q^(M−2)`. **Formalizer note:** the telescoping is over `ℕ` with three
`ℕ`-subtractions in exponents; the recommended route is to prove the identity multiplied through
by `q^2` and with `M` written as `2m+1+ε`, `ε ∈ {0,1}` (`rcases Nat.even_or_odd M`), which makes
every exponent literal.

**SIZE.** 34 lines. **Split candidate:** the two parities as separate private helpers.

**SOURCE.** `EFF.HEX3.27` (the R-recursion, "the first-step form of the same count … evaluates to
the same closed form by the identical bracket telescoping").

**⚠ THE SOURCE FLAGS THIS STEP AS ASSERTED.** `EFF.HEX3.27` records that HEX3 states the
equivalence of the two forms without displaying it, and that the 0a compiler verified it
**numerically** (`q ∈ {2,3,4,5,7,8,9,11,13}`, `M = 1..20`, 360 checks, 0 failures) rather than
symbolically. **This node is where that justification seam is closed in Lean** — a genuine
addition to the corpus's evidence, not a transcription.

**TEETH.** `HEX3-T-FLOOR` → **executable regression**; the 0a numeric verification → **Lean
theorem** (this node).

**ENVIRONMENT.** ENV-A.

---

### NODE G.66 [def] [fresh]

**STATEMENT.** *The HEX3 conservative-residue function `u`,* in its telescoped (direct-sum) form:
`u(q,N) = q^(2N−2) + (q−1)·∑_{k=1}^{⌊(N−1)/3⌋} q^(4k−1)·(q^(N−3k) − 1)·R(N−3k)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- HEX3's `u(q, N)` — the per-centre conservative-undecided count of the cubic TRP stratum
(`EFF.HEX3.08`, THEOREM HEX3.A), in telescoped form. Pure arithmetic. -/
def hex3U (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (q - 1) * ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
        q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))
```

**DEPENDS.** G.64.

**PROOF.** definitional.

**SIZE.** 8 lines.

**SOURCE.** `EFF.HEX3.08` (THEOREM HEX3.A's first display).

**⚠ ARITHMETIC CROSS-CHECK (computed for this blueprint, three anchors).**
`u(q,1) = q^0 + (empty sum) = 1` ✓ (HEX3-BOX-5's seed convention, `EFF.HEX3.41`);
`u(q,2) = q²` ✓, `u(q,3) = q⁴` ✓ (the `k`-sum is empty for `N ≤ 3`);
`u(q,4) = q⁶ + (q−1)·q³·(q−1)·R(1) = q⁶ + (q−1)²q³` ✓ (`EFF.HEX3.12`'s anchor: `72` at `q = 2`,
`837` at `q = 3` — check: `64 + 1·8 = 72` ✓, `729 + 4·27 = 837` ✓);
`u(2,7)`: `2^12 = 4096`; `k = 1`: `2³·(2⁴−1)·R(4) = 8·15·12 = 1440` (with
`R(4) = 2³ + ⌊3/2⌋·1·2² = 8 + 4 = 12`); `k = 2`: `2⁷·(2−1)·R(1) = 128`; total
`4096 + 1440 + 128 = 5664` ✓ — **exactly the note's anchor, including its telescoped-form
decomposition `1440 + 128`** (`EFF.HEX3.12`, which also warns that the *first-step* form
decomposes the same total as `1504 + 64`).

**TEETH.** `HEX3-LAW` (`EFF.HEX3.45`, 92 checks on 46 rows) → **executable regression**
(retained; and note the fit disclosure — the law was FITTED on 14 of the 29 pairs, so the
independent force is the twelve never-measured pairs).

**ENVIRONMENT.** ENV-A.

---

### NODE G.67 [theorem] [fresh]

**STATEMENT.** *The telescoping theorem.* `hex3U` satisfies HEX3's first-step recursion — stated
additively, so no `ℕ`-subtraction appears:

    u(N) + ∑_k (q−1)q^(3k)·q^(2(N−3k)−2)
      = q^(2N−2) + ∑_k (q−1)q^(3k)·( u(N−3k) + (q^(N−3k) − 1)·R(N−3k) ).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem hex3U_rec (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
        (q - 1) * q ^ (3 * k) * q ^ (2 * (N - 3 * k) - 2)
      = q ^ (2 * N - 2) + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
          (q - 1) * q ^ (3 * k) * (hex3U q (N - 3 * k)
            + (q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))
```

**DEPENDS.** G.64, G.66.

**PROOF.** the induction of `EFF.HEX3.30`: substitute `hex3U`'s definition for each
`u(N−3k)` on the right; the coefficient of `t(N−3l) := (q^(N−3l)−1)R(N−3l)` on the right is
`(q−1)q^(3l) + (q−1)²·∑_{k+j=l, k,j ≥ 1} q^(3k)·q^(4j−1) = (q−1)q^(4l−1)`, which is exactly its
coefficient on the left; and the `q^(2(N−3k)−2)` terms cancel against the substituted heads.
Steps:
1. `induction N using Nat.strong_induction_on`.
2. expand the right-hand `hex3U q (N−3k)` by `G.66`.
3. exchange the two sums (`Finset.sum_comm` after re-indexing `(k, j) ↦ l = k + j`).
4. the inner coefficient identity `(q−1)q^(3l) + (q−1)²∑_{k=1}^{l−1} q^(3k+4(l−k)−1)
   = (q−1)q^(4l−1)` — a finite geometric sum; prove it as the private helper `coeff_collapse`.
5. cancel the head terms and conclude.

**SIZE.** 40 lines. **SPLIT MANDATED:** step 4 (`coeff_collapse`) as its own node **G.67a**
(~20 lines); the assembly as G.67 (~25 lines).

**SOURCE.** `EFF.HEX3.30` (S5.2, the telescoping, with its generating-function rider
`1 − ∑_{k≥1}(q−1)q^(3k)x^(3k) = (1−q⁴x³)/(1−q³x³)`); `EFF.HEX3.29` (the first-step assembly).

**⚠ SOURCE-EVIDENCE NOTE.** `EFF.HEX3.30` records that the coefficient identity of step 4 was
verified by the 0a compiler **numerically** (`q ∈ {2,3,5}`, `l = 1..8`, 24 cases) and by PE2's
fresh route only up to `N ≤ 40`. **The Lean node is the first symbolic proof for all `l`.**

**TEETH.** `HEX3-LAW` → **executable regression** (aggregate only; `EFF.HEX3` §6.2 classes S5.2
as "weakly guarded").

**ENVIRONMENT.** ENV-A.

---

### NODE G.68 [lemma] [fresh]

**STATEMENT.** `2·R(M) ≤ (M+1)·q^(M−1)` for `M ≥ 1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem two_mul_hex3R_le (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    2 * hex3R q M ≤ (M + 1) * q ^ (M - 1)
```

**DEPENDS.** G.64.

**PROOF.** `2R(M) = 2q^(M−1) + 2⌊(M−1)/2⌋(q−1)q^(M−2) ≤ 2q^(M−1) + (M−1)(q−1)q^(M−2)`, and
`(q−1)q^(M−2) ≤ q^(M−1)`, so `2R(M) ≤ (2 + (M−1))q^(M−1) = (M+1)q^(M−1)`. Two `ℕ`-subtraction
guards, both `omega` from `hM` and `hq`.

**SIZE.** 14 lines.

**SOURCE.** `EFF.HEX3.31` (S5.3: "`R(M) ≤ q^(M−1)(M+1)/2` (as `2q + (M−1)(q−1) ≤ q(M+1) ⟺ M ≥ 1`)"
— the note's own equivalence, which the 0a audit re-derived and confirmed exact).

**TEETH.** `HEX3-T-FLOOR` → **executable regression**.

**ENVIRONMENT.** ENV-A.

---

### NODE G.69 [theorem] [fresh]

**STATEMENT.** *The HEX3.B vanishing bound.* `u(q,N) ≤ N·q^(2N−2)` for `N ≥ 2`, `q ≥ 2`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem hex3U_le (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N ≤ N * q ^ (2 * N - 2)
```

**DEPENDS.** G.64, G.66, G.68.

**PROOF.** the five steps of `EFF.HEX3.31`, each `ℕ`-safe:
1. the `k`-term is `(q−1)q^(4k−1)(q^M − 1)R(M)` with `M = N − 3k`; bound `(q^M − 1) ≤ q^M` and
   `2R(M) ≤ (M+1)q^(M−1)` (G.68) to get `2·(k-term) ≤ (q−1)(M+1)q^(2N−2k−2)`.
2. `M + 1 = N − 3k + 1 ≤ N − 2` for `k ≥ 1`.
3. sum the geometric series `∑_{k≥1} q^(−2k) = 1/(q²−1)`; in `ℕ` this is done as
   `∑_{k=1}^{K} q^(2N−2k−2) · (q²−1) ≤ q^(2N−2)`.
4. combine: `2·(u(N) − q^(2N−2)) ≤ (q−1)(N−2)q^(2N−2)/(q²−1) ≤ (N−2)q^(2N−2)/(q+1)`.
5. `u(N) ≤ q^(2N−2)(1 + (N−2)/(2(q+1))) ≤ N·q^(2N−2)` for `N ≥ 2, q ≥ 2`.

**Formalizer instruction:** do the whole computation multiplied by `2(q+1)` to stay in `ℕ`, or
cast to `ℚ` at step 1 and stay there (**recommended** — the source's own chain is a `ℚ`
computation).

**SIZE.** 40 lines. **SPLIT MANDATED:** step 3's geometric bound as **G.69a**.

**SOURCE.** `EFF.HEX3.09` (THEOREM HEX3.B); `EFF.HEX3.31` (its proof, whose seven steps the 0a
audit re-derived and found sound).

**TEETH.** none — `EFF.HEX3` §6.2 classes THEOREM HEX3.B as **PROOF-ONLY**: "Six units carry their
interesting content in a proof no battery touches." **Lean theorem** is therefore the *only*
available disposition, and this node supplies it.

**ENVIRONMENT.** ENV-A.

---

### NODE G.70 [theorem] [fresh]

**STATEMENT.** The normalized conservative residue vanishes:
`(q·u(q,N) : ℝ)/q^(3N) ≤ N/q^(N+1) → 0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem hex3U_div_tendsto_zero (q : ℕ) (hq : 2 ≤ q) :
    Filter.Tendsto (fun N : ℕ => (q * hex3U q N : ℝ) / (q : ℝ) ^ (3 * N))
      Filter.atTop (nhds 0)
```

**DEPENDS.** G.69 · mathlib `tendsto_pow_atTop_nhds_zero_of_lt_one`,
`Filter.Tendsto.const_mul`, `squeeze_zero`.

**PROOF.**
1. for `N ≥ 2`, G.69 gives `q·u(q,N) ≤ N·q^(2N−1)`, so the ratio is `≤ N/q^(N+1)`.
2. `N/q^(N+1) → 0` (`tendsto_nat_div_pow_atTop_nhds_zero`-style; if mathlib lacks the exact form,
   use `Nat.cast_div_le` with `n ≤ 2^n` and `tendsto_pow_atTop_nhds_zero_of_lt_one`).
3. `squeeze_zero` with nonnegativity.

**SIZE.** 20 lines.

**SOURCE.** `EFF.HEX3.09` ("`undecided(3, q, N) / q^(3N) ≤ (1 + N)·q^(−N) → 0`").

**⚠ SCOPE FENCE (this is H-1 in Lean form).** This node is about the **arithmetic function**
`hex3U`, not about `undecidedCount O 3 N`. It does **not** prove `DrainageAt 3`, and it must never
be cited as doing so. The missing bridge is exactly HEX3's LEMMA H-1 partition + H-2 shear + H-3
block re-entry, which chapter G does not formalise.

**TEETH.** none (PROOF-ONLY, as G.69).

**ENVIRONMENT.** ENV-A.

---

### NODE G.71 [theorem] [fresh]

**STATEMENT.** The chapter's `n = 3` conditional drainage statement, in the shape the capstone
consumes: **if** the undecided proportion at `n = 3` is eventually bounded by the normalized
conservative residue, **then** every type drains.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem drainage_three_of_hex3_bound [IsAdicComplete (maximalIdeal O) O]
    (h : ∀ N : ℕ, (undecidedCount O 3 N : ℝ)
      ≤ (residueCard O : ℝ) * (Menu.hex3U (residueCard O) N : ℝ))
    (σ : FactorizationType) : UndecidedVanishes O 3 σ
```

**DEPENDS.** G.66, G.70 · landed `drainage_of_undecided_comp` (CN-11, `DensityAPI.lean:213`),
`undecidedSeq`, `gapSeq_le_undecidedSeq`.

**PROOF.**
1. `undecidedSeq O 3 N = undecidedCount O 3 N / q^(3N) ≤ q·hex3U q N / q^(3N)` by `h`.
2. the majorant tends to `0` by G.70 (with `q := residueCard O`, `hq := two_le_residueCard O`).
3. `squeeze_zero` gives `undecidedSeq O 3 → 0`.
4. `drainage_of_undecided_comp` with `φ = id` (`tendsto_id`).

**SIZE.** 18 lines.

**⚠ THE HYPOTHESIS `h` IS THE CHAPTER'S FRONTIER.** It is HEX3's THEOREM HEX3.A + the
`U₃^σ ≤ U₃^conv` inequality (`EFF.HEX3.06`) in Lean form, and it is **not proved here** (H-1).
This node exists so that the frontier has a single named interface: when the bridge lands, exactly
one hypothesis is discharged and `DrainageAt 3` follows. **A cross-reader should check that `h` is
not vacuous or accidentally provable**: it is not, since `hex3U q N ≈ q^(2N−2)` while the trivial
bound on `undecidedCount O 3 N` is `q^(3N)`.

**SOURCE.** `EFF.HEX3.09`; `EFF.HEX3.06`; `EFF.HMENU3.29` (the `(A2)` complement `r(N)`, whose TRP
term is `q·u(q,N)` "THEOREM HEX3.A, consumed at pin").

**TEETH.** `HEX3-LAW`, `HEX3-SPECIES` → **executable regression** (they evidence the hypothesis,
not the implication).

**ENVIRONMENT.** ENV-B.

---

### NODE G.72 [theorem] [fresh]

**STATEMENT.** `Σ_σ R_σ = 1` at `n = 3`, over the five-type menu, **given drainage** — the `n = 3`
instance of `TotalMassOne`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem totalMass_three_of_drainage [IsAdicComplete (maximalIdeal O) O]
    (hd : ∀ σ : FactorizationType, UndecidedVanishes O 3 σ) :
    genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram = 1

theorem one_le_sum_three :
    1 ≤ genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram
```

**DEPENDS.** G.52, G.53, G.54 · landed `sum_genuineDensity_eq_one_of_drainage`
(`GenuineDensity.lean:513`), `one_le_sum_genuineDensity` (`GenuineDensity.lean:501`).

**PROOF.**
1. `coveringMenu_three` (G.54) supplies the menu.
2. `sum_genuineDensity_eq_one_of_drainage` gives `∑ σ ∈ S, genuineDensity O 3 σ = 1`.
3. unfold the `Finset` sum over the explicit 5-element menu (`Finset.sum_insert` four times, with
   the four distinctness side conditions from G.52's `c3_pairwise_ne`).
4. `one_le_sum_three` is the same expansion applied to `one_le_sum_genuineDensity`, which needs
   **no** drainage.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HMENU3.17` (`Σ_τ R_τ = 1` exactly); `EFF.HMENU3.31` (the assembly:
`(q−1)/q + (q−1)/q² + 1/q² = 1`).

**⚠ CONDITIONALITY, STATED EXACTLY.** The `≥ 1` half is **unconditional** (and is landed
machinery: the possible sets cover). The `≤ 1` half needs drainage at `n = 3`, which chapter G does
not prove (H-1). This node is therefore the honest `n = 3` total-mass statement, and it is
**not** COROLLARY HM3.D: it gives the sum, never the five individual values (H-4).

**TEETH.** `HM3-RTAU` (`EFF.HMENU3.48`, symbolic, 30 checks, guards `Σ_τ R_τ = 1`) →
**executable regression** (retained; the individual values stay in `verification/`).

**ENVIRONMENT.** ENV-B.

---

## 10. §10 — `n = 3`: THE σ-UNDECIDED LOWER BOUND

### NODE G.73 [def] [fresh]

**STATEMENT.** *The W12-S3.2 species.* The level-`N` cubic classes with `a₀ ≡ a₁ ≡ 0 (mod π^N)`
and `a₂` free — `q^N` classes.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

/-- The `q^N`-element species of `EFF.HEX3.07` / LEMMA W12-S3.2: separation data hidden, `b₂`
free and visible. -/
def species3 (N : ℕ) : Set (Coeff O 3 N) := {c | c 0 = 0 ∧ c 1 = 0}

theorem card_species3 (N : ℕ) : Nat.card (species3 (O := O) N) = residueCard O ^ N
```

**DEPENDS.** landed `Coeff`, `card_res`.

**PROOF.** the map `c ↦ c 2` is a bijection `species3 N ≃ Res O N` (inverse `x ↦ ![0, 0, x]`);
`card_res`.

**SIZE.** 14 lines.

**SOURCE.** `EFF.HEX3.07` (the constructed species giving `q^N ≤ U₃^σ`, with the `[r4]`
correction's description: "W12-S3.2's species is `b₁ = b₀ = 0` with `b₂` FREE (`q` centers ×
`q^(N−1)` free `b₂`)").

**⚠ COORDINATE NOTE.** The corpus counts `q` centres × `q^(N−1)` recentred states; this node
counts one centre (`γ = 0`) with `a₂` free over the *whole* of `Res O N`. Both give `q^N` — the
translation bijection (`EFF.HEX3.02`) is exactly the identification of the two pictures, and the
Lean node takes the simpler one. **This is a real (harmless) divergence from the source's
bookkeeping and a cross-read item.**

**TEETH.** `HEX3-SPECIES` → **executable regression**.

**ENVIRONMENT.** ENV-A.

---

### NODE G.74 [lemma] [fresh]

**STATEMENT.** Every class of `species3 N` has a `c3split` lift: `x²(x + a₂)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem exists_split3_lift {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧ typeOf (monicPoly a) = c3split
```

**DEPENDS.** G.52, G.73 · landed `typeOf_prod_X_sub_C` (CN-14), `typeOf_mul` (CN-03),
`monicPoly`, `proj_eq_iff_dvd` (CN-07), `proj_surjective`.

**PROOF.**
1. pick any lift `a` of `c` (`proj_surjective`) and replace its first two coordinates by `0`:
   `b := ![0, 0, a 2]`. Then `proj O 3 N b = c` because `c 0 = c 1 = 0` (`hc`).
2. `monicPoly b = X³ + a₂X² = X·X·(X + a₂)` (`monicPoly` expanded at `n = 3`; `ring`).
3. `typeOf` of that product is `⟨{(1,1),(1,1),(1,1)}⟩ = c3split`, either by
   `typeOf_prod_X_sub_C` with `r := ![0, 0, −a 2]` after rewriting the product, or by two
   applications of `typeOf_mul` plus `typeOf_of_natDegree_one`.

**SIZE.** 20 lines.

**SOURCE.** `EFF.HEX3.37` (HEX3-BOX-1's `[r4]` bracket: the species members are ambiguous because
the separation data `(B₁, B₀)` are hidden).

**TEETH.** `HEX3-SPECIES` → **executable regression**.

**ENVIRONMENT.** ENV-A.

---

### NODE G.75 [lemma] [fresh]

**STATEMENT.** Every class of `species3 N` also has a **ramified** lift, of type `c3ram` (when
`a₂ = 0`) or `c3linRam` (when `a₂ ≠ 0`). Hence no type is decided on it.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem exists_ram3_lift [IsAdicComplete (maximalIdeal O) O] (hπ : Irreducible π)
    {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧
      (typeOf (monicPoly a) = c3ram ∨ typeOf (monicPoly a) = c3linRam)
```

**DEPENDS.** G.52, G.58, G.59, G.73 · landed `typeOf_eisenstein` (CN-20), `typeOf_scale`
(`TypeOfInvariance.lean:521`), `exists_monic_scaleRoots` (CN-12, `ScaleExtraction.lean:92`),
`typeOf_of_residual_coprime` (CN-18), `typeOf_of_certRam` (`Drainage.lean:286`), `typeOf_mul`.

**PROOF.** two cases on `a₂ := ` any lift of `c 2`.
1. **`a₂ = 0`.** Take `b := ![π^M, 0, 0]` with `M ≥ N` and `3 ∤ M`, e.g. `M := 3N + 1`.
   Then `proj O 3 N b = c` (both changed coordinates are `π^N`-divisible), and `monicPoly b
   = X³ + π^M`. Scale: `exists_monic_scaleRoots` with `m := (M−1)/3` extracts a monic `G` with
   `monicPoly b = G.scaleRoots (π^m)`; `typeOf_scaleRoots` transports, and `G` is Eisenstein
   (`v(G.coeff 0) = M − 3m = 1`), so `typeOf_eisenstein` gives `c3ram`.
   *(Simpler alternative if `M := 3N+1` is used directly: `X³ + π^(3N+1)` is not Eisenstein, so
   the scaling step is required. A formalizer may instead take `M := 1` when `N = 1`; in general
   the scaling is unavoidable and is exactly what CN-12 is for.)*
2. **`a₂ ≠ 0`.** Let `e := addVal O a₂` (finite) and take `b := ![π^M, 0, a₂]` with
   `M ≥ max(N, 3e+1)` and `M − e` odd.
   * scale by `π^e`: `monicPoly b = G.scaleRoots (π^e)` with `G = X³ + (a₂/π^e)X² + π^(M−3e)`,
     whose `X²`-coefficient is a **unit**; `typeOf_scale` gives `typeOf (monicPoly b) = typeOf G`.
   * `G`'s reduction is `X²(X + ū)` with `ū ≠ 0`: two coprime residual factors, so CN-18 peels
     `G = g·h` with `g` monic linear (reducing to `X + ū`) and `h` monic quadratic (reducing to
     `X²`).
   * comparing constant terms, `h.coeff 0 = π^(M−3e)/g.coeff 0` up to a unit, so
     `v(h.coeff 0) = M − 3e`; comparing `X`-coefficients (`G.coeff 1 = 0`) gives
     `h.coeff 1 = −h.coeff 0 / g.coeff 0`, so `v(h.coeff 1) = M − 3e` as well.
   * `CertRam` for `h` at `γ = 0` with `2j+1 := M − 3e` (odd, since `M − e` odd and `2e` even):
     the value has exact valuation `M−3e`, the derivative valuation `M−3e ≥ j+1` ✓. So
     `typeOf h = ramType = ⟨{(2,1)}⟩`.
   * `typeOf g = ⟨{(1,1)}⟩`; CN-03 adds them to `c3linRam`.

**SIZE.** 55 lines. **SPLIT MANDATED:** case 1 as **G.75a** (~18 lines), case 2 as **G.75b**
(~40 lines).

**SOURCE.** `EFF.HEX3.07`, `EFF.HEX3.37` (the species and why its members are ambiguous);
`EFF.HMENU3.17` (the `c3linRam` and `c3ram` rows).

**⚠ THE CONSTRUCTION IS THIS CHAPTER'S, NOT THE CORPUS'S.** HEX3 asserts the species is
σ-ambiguous by citing LEMMA W12-S3.2; the two explicit lifts (G.74, G.75) are the blueprint's own
reconstruction of that assertion, and they are what make the Lean bound unconditional. A
cross-reader should check the parity bookkeeping of case 2 (`M − e` odd ⟹ `M − 3e` odd) — it is
the one place a sign/parity slip would silently produce a `c3split` lift instead.

**TEETH.** `HEX3-SPECIES` → **executable regression**; `HM3-ORACLE` → **executable regression**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.76 [theorem] [fresh]

**STATEMENT.** **`q^N ≤ undecidedCount O 3 N`** — the `n = 3` σ-undecided lower bound, at general
`O`, unconditional.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- The `n = 3` σ-undecided count is at least `q^N`: the `q^N` classes with both separation
coordinates hidden admit both a split lift and a ramified lift. -/
theorem card_le_undecidedCount_three [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    residueCard O ^ N ≤ undecidedCount O 3 N
```

**DEPENDS.** G.52, G.73, G.74, G.75 · landed `undecidedCount`, `UndecidedAt`, `DecidedAt`.

**PROOF.**
1. `species3 N ⊆ undecidedSet O 3 N`: for `c` in the species and any `σ`, a decidedness of `σ`
   on `c` would force the split lift (G.74) and the ramified lift (G.75) to have the same type,
   contradicting `c3split ≠ c3ram` and `c3split ≠ c3linRam` (G.52).
2. `Nat.card_le_card_of_injective` on the inclusion, then `card_species3` (G.73).

**SIZE.** 16 lines.

**SOURCE.** `EFF.HEX3.07` ("LEMMA W12-S3.2's constructed species gives `q^N ≤ U₃^σ`");
`EFF.HEX3.09` (the bracket `q^N ≤ U₃^σ ≤ U₃^conv`); `EFF.HEX3.37` (HEX3-BOX-1's own statement of
the bracket).

**⚠ WHAT THIS BOUND DOES AND DOES NOT DO.** It is the **lower** half of HEX3-BOX-1's bracket, and
it is compatible with drainage: normalized, `q^N/q^(3N) = q^(−2N) → 0`. It therefore obstructs
nothing. It is recorded because (i) it is the only half of the bracket chapter G can prove, and
(ii) it makes `undecidedCount O 3 N` provably nonzero, which forecloses any "the cubic undecided
set is empty" shortcut.

**TEETH.** `HEX3-SPECIES` → **executable regression**; `HEX3-LAW` → **executable regression**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.77 [gate] [fresh]

**STATEMENT.** The `n = 3` numeric gate: at `q = 2` and `q = 3` the chapter's proved lower bounds
sit strictly below HMENU3's target densities, and the `n = 3` undecided count is at least `2^N`
resp. `3^N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem gate_three_padic_two :
    (1 : ℝ) / 512 ≤ decidedDensity ℤ_[2] 3 c3split
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3linInert
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3inert
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3linRam
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3ram

theorem gate_three_hmenu3_containment_two :
    (1 : ℝ) / 512 ≤ 4 / 93 ∧ (1 : ℝ) / 4 ≤ 28 / 93 ∧ (1 : ℝ) / 4 ≤ 8 / 31
      ∧ (1 : ℝ) / 16 ≤ 22 / 93 ∧ (1 : ℝ) / 16 ≤ 5 / 31
```

**DEPENDS.** G.61 · landed `residueCard_padicInt`.

**PROOF.** instantiate G.61 at `ℤ_[2]`, `rw [residueCard_padicInt 2]`, `norm_num`; the second
theorem is pure `norm_num`.

**SIZE.** 14 lines.

**SOURCE.** `EFF.HMENU3.18` (the numerical anchors `q = 2: (4/93, 28/93, 8/31, 22/93, 5/31)`).

**⚠ GATE SEMANTICS.** The second theorem is the *containment* check: it asserts that the proved
bounds are consistent with HMENU3's transcribed targets. It is `norm_num` on rationals and proves
nothing about densities — its value is that a future change to either side breaks the build. This
is the same device as the landed `gate_bracket_w11_two`.

**TEETH.** `HM3-RTAU` → **executable regression**.

**ENVIRONMENT.** ENV-B.

---

### NODE G.78 [gate] [fresh]

**STATEMENT.** The chapter's axiom-footprint census: every public declaration of chapter G has
Lean-core-only axioms.

**SIGNATURE.**
```lean
-- leanfinal/Uniformity/G/G78_AxCheck.lean
section AxCheck
#print axioms Uniformity.Density.undecidedCount_two_eq
#print axioms Uniformity.Density.decidedCount_split_eq_inert
#print axioms Uniformity.Density.genuineDensity_two_exact
#print axioms Uniformity.Density.uniformityStatement_two
#print axioms Uniformity.Density.typeOf_three_cases
#print axioms Uniformity.Density.coveringMenu_three
#print axioms Uniformity.Density.lowers_three
#print axioms Uniformity.Density.card_le_undecidedCount_three
#print axioms Uniformity.Density.totalMass_three_of_drainage
#print axioms Uniformity.Density.Menu.hex3U_rec
#print axioms Uniformity.Density.Menu.hex3U_le
-- … one line per public contract declaration of §§3–10
end AxCheck
```

**DEPENDS.** every node.

**PROOF.** not a proof — a build-time census, in the style of the landed `Gates.lean:589` and
`Drainage.lean:1160` blocks.

**SIZE.** 80 lines (one line per public declaration).

**SOURCE.** repo policy (`CLAUDE.md`: "Ground truth for the trusted base"; `leanfinal/README.md`:
"no axioms beyond Lean core").

**TEETH.** the repo's own axiom policy → **Lean theorem** (the census is the check).

**ENVIRONMENT.** no namespace; a bare file at the end of the chapter roll-up.

---

## 11. DAG ADDITIONS

Written by `spec/dag_build.py`'s contract (9 columns: `from-ID, to-ID, edge-kind, chapter, status,
edge-class, resolution, kind-basis, evidence`), edge direction **consumer → supplier**.

| file | rows | what |
|---|---:|---|
| `spec/DAG_BLUEPRINT_G.tsv` | 327 | the canonical copy of this chapter's edges (survives a `dag_build.py` rebuild) |
| `spec/DAG.tsv` (appended) | +327 | the same rows, merged into the global edge list |
| `spec/DAG_NODES.tsv` (appended) | +78 | one `BP.G.<nn>` node row each, `node-kind = blueprint-node`, `class = blueprint`, `chapter = G`, `status = OPEN` |

Every added row carries `chapter = G`, `edge-class = blueprint`, `kind-basis = blueprint`,
`resolution = from:exact,to:exact` (blueprint edges are exact by construction — they are read off
declared DEPENDS/SOURCE fields, not harvested from prose), and an `evidence` field beginning
`source=blueprint | CHAP-G NODE G.<nn>`.

**Edge census by target class:** `EFF.*` 151 (transcription edges, from each node's SOURCE),
`BP.G.*` 138 (intra-chapter dependency edges, of which 137 are node→node and 1 is the capstone
edge below), `lean:*` 34 (landed-API dependencies that already exist as DAG nodes), `HYP.*` 4.

**The five structural edges added by hand** (they are the chapter's interface to the rest of the
graph, and each is a claim a cross-reader should check):

| edge | meaning |
|---|---|
| `CAP:UniformityStatement → BP.G.51` | the capstone's `n = 2` slice is this chapter's G.51 |
| `BP.G.36 → HYP.27` | G.36 discharges `(A2)` drainage **at `n = 2`** with the exact rate |
| `BP.G.71 → HYP.29` | G.71 names `(hExhaust-3)` as its explicit hypothesis (frontier, H-1) |
| `BP.G.72 → HYP.28` | G.72 is the *type-level shadow* of `(hMenu-3)`, not its discharge (H-3) |
| `BP.G.76 → HYP.137` | G.76 proves the LOWER half of HEX3-BOX-1's bracket; the tail-σ lemma stays a NON-NODE (H-2) |

**Checker status after the append** (`python3 spec/dag_check.py`): dangling-ID check PASS; cycle
detection PASS (no new SCC — the chapter's own 137 edges are acyclic with critical path 13);
capstone reachability rises **540 → 599 nodes (22.0% → 23.7%)**, of which 40 of the 78 new nodes
are reachable and 38 are connected-but-unreachable (the `n = 3` menu, the ANNEX-B index and the
HEX3 arithmetic layer — expected, since none of them is wired to the capstone until the `n = 3`
bridge lands); the seven ledger NOT-REACHED rows stay consistent 7/7.

**⚠ ORCHESTRATOR ITEM.** `spec/dag_build.py` opens `DAG.tsv` and `DAG_NODES.tsv` in `'w'` mode, so
a rebuild **discards** these appended rows. `spec/DAG_BLUEPRINT_G.tsv` is the durable copy; the
builder needs a merge step (`read every spec/DAG_BLUEPRINT_*.tsv and emit after the harvested
rows`). Booked here, not done — it is a change to a 0c artifact this chapter does not own.

---

## 12. LEANSPEC STUB LIST (stage 0e)

Per REVISION 2 stage **0e**, every signature lands first in the isolated `leanspec/` project as an
`axiom` stub with the real namespace, universes, instance arguments and attributes, in topological
order, **before** the fleet fires; after a node lands in `leanfinal` its normalised environment
type is diffed against the signed stub.

**Stub count: 110** (one per declaration in a SIGNATURE block; 82 `theorem`, 26 `def`,
1 `structure`, 1 `inductive`). All 110 names are distinct — checked mechanically over this file,
and checked against the landed name list of §0.3 (no collision; the two near-misses are handled by
namespacing: this chapter's `readEquiv`/`dvdSet`/`exactSet` live in `Uniformity.Density.Menu`
while `leancheck`'s identically-named declarations live in `UniformityCheck`, and the two repos
are never in the same environment).

Stub file layout, mirroring the node files:

```
leanspec/Leanspec/G/G01_ExactVal.lean        -- 1 def
leanspec/Leanspec/G/G02_ExactValAPI.lean     -- 2 theorems
…
leanspec/Leanspec/G/G78_AxCheck.lean         -- (no stub: a census block, not a declaration)
leanspec/Leanspec/G.lean                     -- imports all, in topological order
```

Rules for the stub-landing agent:
1. **Definitions land as real bodies, not axioms** (0e: "definition/structure BODIES land first"),
   so `ExactVal`, `readEquiv`, `CertFamily`, `tangSet`, `tangAdm`, `depthSet`, `residualPair`,
   `resStratum`, `inertStratum`, `splitStratum`, `SepPair`, `DblPair`, `NoRootCubic`, `LinAni`,
   `Split3`, `c3*`, `CubicFamilyIndex`, `hex3R`, `hex3U`, `species3` are **real code** in
   `leanspec`. Only the 82 theorems become `axiom` stubs.
2. `G.21`'s signature is **known defective** (see its PROOF note): the stub lands in the
   two-hypothesis form, and the orchestrator books the amended signature before any dependent
   stub.
3. Elaboration failures in a stub are **blueprint defects**, not formalization work: they go back
   to this file, versioned in place, never patched in `leanspec`.

---

## 13. TEETH DISPOSITION SUMMARY

Per source battery row guarding chapter-G content (template rule: every guarded row gets a
disposition in `{Lean theorem, executable regression, signed non-applicability}`).

**80 dispositions across the 78 nodes: 42 Lean theorem, 34 executable regression, 4 signed
non-applicability.**

| battery family | source | dispositions in this chapter |
|---|---|---|
| `W11-CENSUS` / P-2 | `EFF.W11.34`, `.35` | **Lean theorem** at G.02, G.07, G.14, G.16, G.20, G.23, G.26, G.32, G.38, G.39, G.40, G.41, G.42, G.44; **executable regression** retained for the family-level `w`-independence (G.28) |
| `W11-EXHAUST` / P-4 | `EFF.W11.35`, `.38` | **Lean theorem** at G.09, G.11, G.17, G.29, G.31, G.34, G.35, G.36, G.43, G.46, G.47, G.48 |
| `W11-T-DRAIN` (30 firings) | `EFF.W11.38` | **Lean theorem** at G.36, G.37 |
| `W11-W10TIE` (0/1,235,872) | `EFF.W11.34` | **Lean theorem** at G.03 (the recentering bijection, now proved) |
| `W11-ORACLE` / P-6 `[IND]` | `EFF.W11.38` | **executable regression** retained at G.24, G.25, G.33, G.48, G.51 — mixed characteristic only (BOX-4) |
| `W11-T-SIGMA` (3,020) | `EFF.W11.38` | **executable regression** at G.27 |
| `W11-T-TAMEDISC` (1,440) | `EFF.W11.38` | **signed non-applicability** in equal characteristic (C7-F4: "supplies no equal-characteristic evidence"); no chapter-G node depends on it |
| `HM3-MENU`, `HM3-AGG`, `HM3-DRAIN`, `HM3-DBLTIE` | `EFF.HMENU3.42`–`.46` | **executable regression** retained at G.05, G.54, G.60 (the family-level menu is not proved here — H-3) |
| `HM3-ORACLE` `[IND]` | `EFF.HMENU3.47` | **signed non-applicability** at G.06 (the oracle is characteristic-blind by construction, `EFF.HMENU3.65`); **executable regression** at G.53, G.55–G.59, G.75 |
| `HM3-RTAU` (symbolic) | `EFF.HMENU3.48` | **executable regression** at G.08, G.45, G.52, G.61, G.72, G.77 |
| `HEX3-LAW` (92 checks, 46 rows) | `EFF.HEX3.45` | **executable regression** at G.66, G.67, G.71, G.76 — with the note's own **fit disclosure** carried: the law was FITTED on 14 of 29 pairs, so the independent force is the twelve never-measured pairs |
| `HEX3-SPECIES` (172, both directions) | `EFF.HEX3.46` | **executable regression** at G.23, G.73, G.74, G.75, G.76 — scoped by Correction C to the realized `N ≤ 9` keys |
| `HEX3-T-FLOOR` (exactly 10 rows) | `EFF.HEX3.50` | **executable regression** at G.64, G.65, G.68 |
| `HEX3-CHAR` (17 pairs) | `EFF.HEX3.49` | **Lean theorem** at G.38 (characteristic-uniformity of the residue count becomes a theorem, not a tally) |
| `HEX3-XREAD` (158,204 states) | `EFF.HEX3.47` | **executable regression** at G.12 |
| THEOREM HEX3.B (`EFF.HEX3.09`) | **PROOF-ONLY** in the source (`EFF.HEX3` §6.2) | **Lean theorem** at G.69, G.70 — the only available disposition, and the chapter supplies it |
| the R-recursion (`EFF.HEX3.27`) | **PROOF-ONLY**, 0a-verified numerically only | **Lean theorem** at G.65 |
| ANNEX B (`EFF.HMENU3.67`) | `AUDIT`-produced, no battery can reach it | **signed non-applicability** at G.62, G.63 |
| the four W-11 C7 corrections | `EFF.W11.08`, `.12`, `.18`, `.25` | **signed non-applicability** as battery items (all are specification-language); their *content* is carried at G.28 (C7-F1's boundary cell), G.44 (C7-F2's aggregates), G.42 (C7-F3's boundary mass). C7-F4 (the char-2 wildness case split) has **no chapter-G node**: it is terminology over a count this chapter proves characteristic-uniformly, so nothing depends on the distinction |

---

## 14. FLAGGED FOR THE CODEX CROSS-READ

> **AMENDMENT BANNER 2026-08-15 — ITEMS 1–4 ARE ADJUDICATED** at the stage-0e gate (the fleet fires
> before the codex read): item 1 **refuted** the G.23a statement, item 2 found **no defect** but
> amended G.28's signature, items 3 and 4 **confirm** the blueprint as written. See **AMENDMENT
> §§A-1…A-4** at the end of this file. Items 5–12 remain owed. Item 11 (`dag_build.py`) is
> **done** — the builder now merges every `spec/DAG_BLUEPRINT_*.tsv` on rebuild (commit
> `c8c8ea7f`). Nothing below is edited.

Ordered by how much a wrong answer would cost.

1. **G.23's declared proof-route defect** (the residual-stratum census: centre modulus `k` vs
   `k+1`, reconciled arithmetically rather than by proof). The *statement* is certain — it is
   forced by G.20, which is independent — but the route is not settled, and G.23 sits on the
   critical path. Sanctioned fallback: the `leancheck` census route (G.41's note).
2. **G.30's boundary condition** (the top even stratum at `t = N−1`, where the split certificate's
   window does not fit). The chapter's proposed resolution uses the hidden value; if it fails, one
   stratum is lost and G.43's identity acquires a `q^(−N)`-order error term. **This is exactly
   where W-11 needs its SPLIT-TAIL boundary family, so a cross-reader should expect difficulty
   here and should not accept a hand-wave.**
3. **The G.39 count `q(q−1)/2` versus W-11's `(q−1)(q−2)/2`.** The chapter's residual census is
   over *all* pairs, W-11's over `F_q × F_q^*`; the reconciliation is displayed at G.39 and must
   be checked, because a wrong choice here changes the split density.
4. **G.43's proof-route divergence from W-11's finite telescope.** The chapter's route (two
   residue-field counts coincide) is shorter and does not use the boundary family. Check for
   circularity: G.38/G.39 must not depend on anything `n = 2`.
5. **G.34's two-case construction** (inert lift at the exact derivative valuation; the `qder = 0`
   case). This is the Lean form of W-11's `[r1, F6]` correction, and getting the case split wrong
   would make G.36 false.
6. **G.75's parity bookkeeping** (`M − e` odd ⟹ `M − 3e` odd) — a slip produces a split lift and
   silently kills G.76.
7. **G.53's combinatorial proof of `typeOf_three_cases`.** It claims the five-type list follows
   from `typeOf_degree` + positivity alone, with no Newton polygon. If that is wrong, G.54 and
   G.72 fall.
8. **The `readEquiv` centre convention** (`Res O N` rather than `O`), adopted to match
   `card_certSet_gen`. Check that every certificate node can actually discharge `hcert` at a
   `Res`-level centre — `leancheck`'s `ramCert_iff`/`inertCert_iff` are the evidence that it can,
   but they are the largest support lemmas of their files.
9. **H-1/H-2's scope**: that the chapter really does not smuggle in the tail-σ lemma anywhere.
   G.71's hypothesis `h` is the single interface; check that no other node's PROOF quietly assumes
   an `n = 3` upper bound.
10. **G.73's coordinate divergence** from the corpus's `q` centres × `q^(N−1)` bookkeeping (the
    chapter counts one centre with `a₂` free over all of `Res O N`). Both give `q^N`; confirm the
    identification.
11. **The `spec/dag_build.py` rebuild hazard** (§11's orchestrator item).
12. **`JD0` has no transcription unit** in this chapter although the 0c cut assigns it to
    chapter G (H-7). Confirm that nothing in chapters A–J is waiting on a JD0 node from here.

---

*END OF CHAPTER G BLUEPRINT — 78 nodes, 110 declarations, 327 DAG edges.*

---

## AMENDMENT 2026-08-15 (dated append; stage-0e gate, Opus arm) — items 1–4 of §14 adjudicated

**Status of this block.** A dated append in the `EFF-W12` convention: **nothing in §§0–14 is edited
in place**. Where a node's content is superseded, the amendment banner at that node's entry points
here and this block governs. Four of §14's twelve cross-read items were adjudicated ahead of the
codex read because the chapter-G fleet fires before the read lands. **A-1 refutes a node
statement**; A-2 corrects a signature; A-3 and A-4 confirm the blueprint as written.

**Wave-1 exposure** (wave 1 = the 19 layer-0 nodes, i.e. those with no intra-chapter DEPENDS:
G.01, G.03, G.05, G.09, G.10, G.12, G.14, G.21, G.26, G.27, G.32, G.33, G.38, G.45, G.50, G.52,
G.62, G.64, G.73): **no wave-1 node's statement changes.** A-2 changes a **layer-1** signature
(G.28, whose only DEPENDS is the wave-1 node G.26), so it must land before wave 2 fires. A-1
blocks a layer-6 node (G.23) and re-cuts the proof route of two layer-7 nodes (G.41, G.42).

---

### A-1 — G.23 `card_resStratum`: **STATEMENT REFUTED. NEITHER ROUTE GOVERNS.**

**Banner for the node entry:** `G.23 [STATEMENT REFUTED 2026-08-15 — see AMENDMENT §A-1; do not
assign as a proof target]`.

**The finding.** The residual pair is **not an invariant of the class**. It is well defined only
modulo the residue-field translation action, so the strata over distinct pairs in one translation
orbit are **equal as sets**, and §14 item 1's certainty argument ("the sum over the `q²−q`
non-degenerate pairs must reproduce G.20, which is proved independently") **double-counts by the
orbit size**.

**The mechanism, explicitly.** Fix a centre `γ` of depth `≥ 2k` for the lift `a`, and write
`qval a γ = π^(2k)·b₀`, `qder a γ = π^k·b₁`. For any `d : O` the centre `γ' = γ + π^k·d` also has
depth `≥ 2k`, because

    qval a (γ + π^k d) = π^(2k)·(b₀ + b₁·d + d²)        (qval_shift)
    qder a (γ + π^k d) = π^k·(b₁ + 2·d)                  (qder_shift)

so the residual pair moves by `(b₀, b₁) ↦ (b₀ + b₁·d̄ + d̄², b₁ + 2·d̄)`, `d̄ = d mod 𝔪` — i.e. by the
substitution `y ↦ y + d̄` on the residual quadratic `R(y) = y² + b₁y + b₀`. G.23's PROOF step 2
identifies this action correctly; what it gets wrong is the conclusion drawn from it. The
stabiliser is

    Stab(p) = {d̄ : R(y + d̄) = R(y)} = {d̄ : 2d̄ = 0 ∧ d̄² + b₁d̄ = 0},

so for `p` **not** a double-root pair:

* residue characteristic `≠ 2`: `Stab(p) = {0}`, orbit size `q`;
* residue characteristic `2`: `Stab(p) = {0, b₁}` (and `b₁ ≠ 0`, since `b₁ = 0` in characteristic
  `2` forces the double-root pair `R = (y + √b₀)²`), orbit size `q/2`.

Therefore `resStratum π N k p = resStratum π N k p'` for every `p'` in the orbit of `p`, and

    #(resStratum π N k p) = q^(2N−2k−1) / #Stab(p)
                          = q^(2N−2k−1)          (residue char ≠ 2)
                          = q^(2N−2k−1)/2        (residue char 2),

**not** `q^(2N−2k−2)`. The two agree exactly when `q = 2` — which is why every numeric
cross-check in this chapter (all computed at `q = 2`) missed it.

**Counterexample (machine-checked, and small enough to check by hand).** `O = ℤ_[3]`, `q = 3`,
`N = 1`, `k = 0`, `p = (1, 0)` (not a double-root pair: the double-root pairs over `𝔽₃` are
`(0,0), (1,2), (1,1)`; `p` is anisotropic). G.23a asserts `#(resStratum) = q^(2·1−0−2) = 1`. The
truth is `3`: the three classes `(a₀,a₁) ∈ {(1,0), (2,1), (2,2)}` each admit a centre reading `p`
— `γ = 0, 1, 2` respectively — and each has depth exactly `0`. A brute-force enumeration over
`(p, N, k) ∈ {(3,1,0), (3,2,0), (2,1,0), (2,2,0), (3,3,1)}` returns per-pair strata
`3, 27, 1, 4, 27` against the blueprint's `1, 9, 1, 4, 9`: **odd residue characteristic is wrong
by the factor `q` in every case, `q = 2` is right in every case.**

**What is NOT affected.** G.20 (`card_depthSet`) is independent and correct. **G.41 and G.42 have
correct STATEMENTS**: their proofs as written commit two compensating errors — the union over
pairs is not disjoint (over-counts by the orbit size) and the per-pair count is too small by
exactly the orbit size — and the two cancel. Verified against the orbit picture in both
characteristics:

| | residue char ≠ 2 | residue char 2 |
|---|---|---|
| anisotropic pairs | `q(q−1)/2` | `q(q−1)/2` |
| orbit size | `q` | `q/2` |
| anisotropic **orbits** | `(q−1)/2` | `q−1` |
| classes per orbit | `q^(2N−2k−1)` | `q^(2N−2k−1)/2` |
| `#inertStratum` | `((q−1)/2)·q^(2N−2k−1)` | `((q−1)/2)·q^(2N−2k−1)` |

— which is G.41's statement in both columns, and the same table with `SepPair` for `AniForm` is
G.42's. G.43 and everything downstream (G.44–G.51) are untouched.

**THE REPLACEMENT ROUTE (governs; it removes G.23 from the critical path).** Do not certify an
individual pair `p`. Certify a **translation-invariant residual CLASS** `𝒫 ⊆ K × K` — the
predicate, not the point. Both classes the chapter needs are translation-invariant, because
`y ↦ y + d̄` does not change how `R` factors:

    cert_𝒫 γ c  :=  readEquiv γ c ∈ tangAdm π (2k) N  ∧  (digit_2k of the value,
                    digit_k of the derivative) ∈ 𝒫.

* `hshift` at modulus `m = k` now **holds** (it is exactly the translation-invariance of `𝒫`), and
  it is what route (a) needed and did not have;
* `huniq` at `m = k` is G.11 verbatim;
* `#S = #𝒫 · q^(N−2k−1) · q^(N−k−1)`, so `card_certSet_gen` gives
  `#{c} = q^k · #S = #𝒫 · q^(2N−2k−2)`.

Instantiating `𝒫 := {p | AniForm p}` (`#𝒫 = q(q−1)/2`, G.38) yields
`#inertStratum = ((q−1)/2)·q^(2N−2k−1)` — **G.41 exactly, in one step, both characteristics** —
and `𝒫 := {p | SepPair p}` (G.39) yields G.42. This is the shared private lemma
`card_stratum_of_residualClass` that G.42's SIZE note already recommends; it is hereby promoted
from "recommended factoring" to **the route**, and it needs neither route (a) nor route (b) nor
G.23.

**Why both declared routes fail.** Route (a) (`m = k`, residual pinned): `hshift` is **false** —
moving the centre inside its mod-`π^k` coset changes the pinned pair. Route (b) (`m = k+1`):
`huniq` is **false in residue characteristic 2** — the stabiliser `{0, b₁}` puts two distinct
mod-`π^(k+1)` centres on the same class. (Route (b) does produce the correct count
`q^(2N−2k−1)` in odd residue characteristic, so it is a valid route for that half only.)

**Fleet instruction.** G.23a `card_resStratum` is **withdrawn** — it must not be assigned, and its
`leanspec` stub is commented out as REFUTED. G.23b `depthSet_eq_iUnion_resStratum` is **TRUE as
stated** (every class of depth exactly `2k` reads some non-double pair, and `(0,0)` — the only pair
that could be read at depth `≥ 2k+1` — is a double-root pair) and stays; note only that the union
is **not** disjoint. G.41/G.42 fire against the replacement route above. Nodes G.21 and G.22 (the
`residualPair` and `resStratum` definitions) are **unchanged**.

---

### A-2 — G.30's window boundary: **NO DEFECT. G.28's WINDOW HYPOTHESIS IS OVER-STRONG BY ONE.**

**Banner for the node entries:** `G.28 [SIGNATURE AMENDED 2026-08-15 — hN : 2*k+1 ≤ N; see
AMENDMENT §A-2]`, `G.30 [BOUNDARY NOTE WITHDRAWN 2026-08-15 — see AMENDMENT §A-2]`.

**Verdict.** The split certificate **does** fit in the window at the top even stratum. G.28's
declared hypothesis `hN : 2*k+2 ≤ N` is one stronger than its own proof uses — the proof's step 4
derives `hN' : 2*k+1 ≤ N` and never uses more. The amended signature is

```lean
theorem decidedAt_split_of_sep (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N k : ℕ} {a : Fin 2 → O} {γ z : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)                      -- was `2 * k + 2 ≤ N`
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hz : π ∣ (z ^ 2 + b₁ * z + b₀)) (hs : ¬ π ∣ (b₁ + 2 * z)) :
    DecidedAt O 2 splitType N (proj O 2 N a)
```

**The evidence, from the landed text.** `CertSplit π a N` (`Drainage.lean:245`) asks for
`2*w+1 ≤ N`, and at `γ' = γ + π^k z` the certificate holds with `w := k`: the derivative has exact
valuation `k` (from `hs`) and the value is `π^(2k+1)`-divisible (from `hz`) — both **read inside
the window** when `2k+1 = N`. Transport to every other lift is `CertSplit_congr`
(`Drainage.lean:455`), whose only exponent side conditions are discharged `by omega` from
`hw : 2*w+1 ≤ N` — equality included. And `typeOf_of_certSplit` (`Drainage.lean:407`) **discards
the window bound entirely** (`obtain ⟨γ, w, -, hd1, hd2, hv⟩`). Nothing anywhere needs `2k+2 ≤ N`.

Sanity instance: `O = ℤ_[3]`, `N = 1`, `k = 0`, class `(a₀,a₁) ≡ (0,1)`. Depth is exactly
`0 = N−1`, the residual quadratic is `X(X+1)` — separable-split with both roots simple — and every
lift reduces to `X² + X mod 3`, so Hensel splits **every** lift: the class is `splitType`-decided
at level `1`. The stratum is not lost.

**Consequences.** G.30's even branch needs only `t < N`, so the top even stratum survives, no
stratum is dropped, and **G.43's identity acquires no `q^(−N)`-order error term**. The
`⚠ BOUNDARY CONDITION, DECLARED` block at G.30 is withdrawn, including its fallback.

**The fallback was not available anyway** — recording this, because it is the load-bearing half of
the verdict. G.41 and G.42 are stated at level `N = 2*k+1+r` for **every** `r ≥ 0`, and `r = 0` is
precisely the boundary stratum `2k = N−1`. Restricting G.30's even branch to `t + 2 ≤ N`, as the
withdrawn block proposed, would leave G.42 **unprovable as stated at `r = 0`**, not merely
imprecise. Any fleet agent that finds itself reaching for that fallback has hit a different bug.

**On W-11's SPLIT-TAIL.** W-11 needs a boundary family because it classifies by the *shape*
`(u, w) = (v(A₀), v(A₁))`, and at `u ≥ N` the shape is not window-determined (`EFF.W11.08`,
C7-F1). The chapter never asserts a shape at the boundary — only `σ` — and C7-F1's own sentence is
that `σ = split` **is** certified there. §0.4's dictionary already says the three W-11 families
collapse into one depth stratum; A-2 is that collapse discharging its last obligation.

---

### A-3 — G.39's `q(q−1)/2` versus W-11's `(q−1)(q−2)/2`: **RECONCILIATION VERIFIED.**

The displayed reconciliation at G.39 is **correct as written; do not "correct" G.39**. The check,
made independently of the display:

* W-11's residual census (`EFF.W11.16`) counts pairs `(c₁, c₀) ∈ F_q × F_q^*` — `c₀ ≠ 0` — with
  rows `(q−1)(q−2)/2` split, `q(q−1)/2` irreducible, `q−1` double, summing to `q(q−1)` ✓.
* The chapter counts all of `F_q × F_q`. The pairs W-11 excludes are exactly those with `b₀ = 0`,
  i.e. `X² − b₁X = X·(X − b₁)`: for `b₁ ≠ 0` two **distinct** roots (`q−1` pairs, joining the split
  row); for `b₁ = 0` the double root `0` (one pair, joining the double row); **none** anisotropic,
  since `0` is always a root — which is why the irreducible row is unchanged.
* Hence `(q−1)(q−2)/2 + (q−1) = q(q−1)/2` ✓ and `(q−1) + 1 = q` ✓, and the three chapter rows
  `q(q−1)/2`, `q(q−1)/2`, `q` sum to `q²` ✓.
* Independent leg (no W-11 input): the separable-split pairs are in bijection with the 2-element
  subsets of `K`, so their number is `C(q,2) = q(q−1)/2`, which is G.39's statement
  `2·#SepPair + q = q·q` ✓; the anisotropic count is then `q² − q(q−1)/2 − q = q(q−1)/2` ✓ = G.38.

**Rider (the chapter's convention is the right one, not merely a rescaling).** The `b₀ = 0`,
`b₁ ≠ 0` pairs are **realized** by the depth filtration: a class of depth exactly `2k` has `b₀ = 0`
iff `π^(2k+1) ∣ qval` while `π^(k+1) ∤ qder`, which is exactly W-11's 2SIDED/SPLIT-TAIL. And
`(0,0)` is **never** realized at depth exactly `2k` (it is Tang at `2k+1`). So the chapter's larger
pair space is the correct index for its strata, and W-11's `c₀ ≠ 0` normalisation is correct for
its own refine-node convention. Both tables are right about their own object.

---

### A-4 — G.43's non-telescope route: **NON-CIRCULAR, VERIFIED.**

`G.38` (`two_mul_card_aniForm`) and `G.39` (`two_mul_card_sepPair`) are statements about
`K × K` for a finite field `K`, under ENV-C — no `O`, no `Coeff`, no `proj`, no `Tang`, no
`decidedSet`, no density. Their DEPENDS are the landed `AniForm`, `rootPairMap`,
`rootPairMap_injective`, `exists_rootPairMap_iff`, `two_mul_choose_two` and mathlib's `Sym2`. **No
`n = 2` input reaches them**, so the chain `G.38/G.39 → G.41/G.42 → G.43` is acyclic and the
identity is not proved from itself. The route stands as a fourth independent derivation of
every-window `split = inert`, beside W-11's finite telescope (`EFF.W11.27`), PE4's disc-fibration
(`EFF.W11.40`) and the aggregate route (`EFF.W11.12`).

Two riders a consumer must carry:

1. **G.43 inherits A-1's repair through its suppliers.** G.41 and G.42's *statements* are correct
   (A-1's table), but their proof route is re-cut; G.43's own statement and proof are unaffected.
2. **Shared-mechanism caveat, not circularity.** G.38 and G.39 both factor through
   `rootPairMap_injective` + `Sym2.natCard`. An error there would move *both* counts together, so
   the `split = inert` identity would survive while the *values* at G.46–G.48 would not. The
   decorrelated leg is G.47's mandated **route 2** (split obtained by subtraction from the landed
   `sum_three_decidedDensities_eq_one`), which shares no input with route 1. G.47's requirement
   that **both routes be recorded in the node file** is therefore load-bearing and must not be
   dropped as redundant.

---

### Amendment bookkeeping

| item | §14 item | verdict | nodes touched | wave-1 impact |
|---|---|---|---|---|
| A-1 | 1 (G.23) | **statement refuted**; replacement route governs | G.23a withdrawn; G.23b kept (union not disjoint); G.41/G.42 re-routed | none (G.23 is layer 6; G.41/G.42 layer 7) |
| A-2 | 2 (G.30) | no defect; G.28 signature amended `2k+2 → 2k+1` | G.28 signature; G.30's boundary block withdrawn | none, but **G.28 is layer 1** — land before wave 2 |
| A-3 | 3 (G.39) | reconciliation verified as displayed | none | none |
| A-4 | 4 (G.43) | non-circular | none | none |

Declaration census after this amendment: **109 contract declarations** (110 minus the withdrawn
G.23a). The `leanspec` stubs (`leanspec/Leanspec/ChapG.lean`, commit `dfa34cd6`) are updated to
match: G.23a commented out with a REFUTED marker, G.28's stub carrying the amended hypothesis.
Items 5–12 of §14 remain **owed to the codex cross-read**.

---

## AMENDMENT 2026-08-15 (second dated append; Opus arm) — stage-0e defects D2 and D3 CURED

**Status of this block.** A second dated append in the same convention as the block above:
**nothing in §§0–14 is edited in place**; the banners at the G.62 and G.52 node entries point
here and this block governs. It discharges two of the five blueprint defects raised at the
stage-0e leanspec gate (`leanspec/Leanspec/ChapG.lean`, header list D1–D5) — the two that the gate
recorded as *owing a blueprint amendment* rather than as cosmetic:

* **D2 — G.62b `CubicFamilyIndex.schema`: DEF WITH NO BODY.** CURED at §A-5: the body is derived
  from `EFF-HMENU3` (ANNEX B) and displayed as a total table.
* **D3 — G.52g `c3_pairwise_ne`: PLACEHOLDER STATEMENT (`True`).** CURED at §A-6: the ten
  inequalities are stated.

**Declaration census: unchanged at 109.** Neither cure adds or withdraws a declaration; D2 fixes a
body, D3 fixes a proposition. **Wave-1 exposure:** both G.52 and G.62 are wave-1 (layer-0) nodes
and both have already landed in `leanfinal`; each cure is therefore a **signature/body repair of an
already-landed file**, sanctioned as such (G62.lean replaces a `BLOCKED` marker with the derived
body at the unchanged signature; G52.lean replaces the vacuous `True` with the real conjunction).
No other node's statement changes, and no landed proof is invalidated: `schema` had **no**
consumer in the landed corpus (G.63 is not landed), and `c3_pairwise_ne : True` had none either
(its only declared consumer is G.72's step 3, unlanded, which needs the real form).

---

### A-5 — G.62b `CubicFamilyIndex.schema`: **D2 CURED: schema body derived from EFF-HMENU3 .62/ANNEX B**

**Banner for the node entry:** `G.62 [BODY DERIVED 2026-08-15 — see AMENDMENT §A-5]`.

**What was missing.** The G.62 SIGNATURE declares `def CubicFamilyIndex.schema : CubicFamilyIndex
→ Fin 33` and the G.62 PROOF says only that it "is an explicit table (`3 + 4 + 7 + 7 + 12 = 33`
targets, with tier-I's 11 formal families mapping onto 7 schemas, tier-II's 11 onto 7, the B-tier's
24 onto 12 — each pair `(m = 0, m ≥ 1)` or `(λ = (1,1), λ = (2))` collapsing to one schema)". The
table itself was never written down. It is recovered below from the primary text.

#### The derivation, step by step (every step cites its EFF unit)

**Step 1 — the domain is ANNEX B's five-tier family list.** `EFF.HMENU3.69`'s corrected-counts
table fixes the five tiers and their formal-family counts: SEP `3`, DBL `4`, tier I `11`, tier II
`11`, B-tier `24`. This is exactly the `CubicFamilyIndex` inductive's constructor arity list
(`Fin 3`, `Fin 4`, `Fin 11`, `Fin 11`, `Fin 24`), landed verbatim at
`leanfinal/Uniformity/ChapG/G62.lean`. **The domain shape is not in question; only the map is.**

**Step 2 — the codomain splits into the same five blocks, of sizes `3 | 4 | 7 | 7 | 12`.** Same
table, schema column: SEP `3`, DBL `4`, tier I `7`, tier II `7`, B-tier `12`, MENU TOTAL `33`;
independently reconstructed in `EFF.HMENU3.62`'s mandatory arithmetic audit ("tier I `7` + tier II
`7` + B `12` = 26 TRP schemas, plus 4 DBL + 3 SEP = **33**"). The G.62 STATEMENT quotes the same
decomposition in the same order (`3 + 4 + 7 + 7 + 12`) as the constructor order, which is what
licenses reading `Fin 33` as those five consecutive blocks:

| `Fin 33` range | block | size |
|---|---|---|
| `0 … 2` | SEP | 3 |
| `3 … 6` | DBL | 4 |
| `7 … 13` | tier I | 7 |
| `14 … 20` | tier II | 7 |
| `21 … 32` | B-tier | 12 |

**Step 3 — the SEP and DBL fibers are singletons.** `EFF.HMENU3.69`'s table gives the SEP row as
`3 → 3` and the DBL row as `4 → 4`, both with "how the refinement acts" **empty**: neither tier is
refined, so `schema` restricted to `sep`/`dbl` is a **bijection onto its block**. The member names
come from `EFF.HMENU3.14` (THEOREM HM3.C, frozen display): `{SEP3, SEPLQ, SEPC}` and
`{DBL-RAM, DBL-2SIDED, DBL-SPLITEQ, DBL-INERTDEEP}`, in that order.

**Step 4 — inside a TRP tier, exactly three of the seven schemas retain `λ`.** `EFF.HMENU3.67`
(ANNEX B's opening, verbatim) names them: `('VERT1', u₀, k, λ)`, `('VERT2', u₀, t, λ)`,
`('FULL', k, λ)`. Hence the seven schemas are `4` λ-free `+ 3` λ-retaining, and **only the
λ-retaining three have non-singleton fibers**.

**Step 5 — the four λ-free schemas are named.** `EFF.HMENU3.69`, corrected counts, verbatim:
"Tier I consists of four λ-free families (RAM3, 3LIN, LINRAM2, RAM2LIN), two VERT1 families, two
VERT2 families and three FULL families: 4+2+2+3 = 11."

**Step 6 — the fiber sizes over the three λ-retaining schemas are `2, 2, 3`.** Same sentence
(`.69`). The *reason* — which is what makes the assignment derived rather than stipulated — is
`EFF.HMENU3.68`'s fixed-label refinement lemma together with its CONDITIONALITY paragraph, which
names the two label sets: `Λ₂ = {(1,1), (2)}` for a degree-2 residual and
`Λ₃ = {(1,1,1), (1,2), (3)}` for a degree-3 residual. VERT1 and VERT2 carry a **quadratic**
residual, so each splits into `#Λ₂ = 2`; FULL carries a **cubic** residual, so it splits into
`#Λ₃ = 3`. `EFF.HMENU3.69`'s census table supplies exactly those two Λ's (rows: degree 2 with
`(1,1)`, `(2)`; degree 3 with `(1,1,1)`, `(1,2)`, `(3)`) and its CONDITIONALITY confirms the λ → σ
reading is the three unramified types of COROLLARY HM3.D (`EFF.HMENU3.17`).

**Step 7 — tier II is a verbatim copy of tier I.** `EFF.HMENU3.69`: "Tier II has the same fixed-λ
refinement and therefore has 11 families." `EFF.HMENU3.11` supplies the structural reason: tier II
is `DEEP-X(m; params) = (q−1)q^{4m−1} × [X's law at window N−3m]`, i.e. the **same seven `X`** as
tier I under a prefix bracket. **The tier-II fiber pattern is therefore forced to equal tier I's**,
schema for schema.

**Step 8 — every B-tier fiber has size exactly `2`, and the pairing is by `b(m)` regime, not by
`λ`.** `EFF.HMENU3.69`, verbatim: "B1/B2/B3 with L ∈ {RAM, 2SIDED, SPLITEQ, INERTDEEP} give twelve
fixed-σ schemas. As already required by HM3.B and HM3-BOX-5, each splits into its m = 0 and m ≥ 1
regimes because b(m) has two formulas. Hence B contributes 12·2 = 24 formal families." The
`B1/B2/B3` × `L` product is `EFF.HMENU3.11`'s own list, in its own order. That the doubling is the
regime split and **not** a λ split is `EFF.HMENU3.09`'s finding (the dictionary already fixes
`SPLITEQ ↦ λ=(1,1)` and `INERTDEEP ↦ λ=(2)`, so "the β side was **already** fixed-λ before ANNEX
B … ANNEX B's refinement therefore bites only on tiers I and II"), and `EFF.HMENU3.37`'s effective
HM3-BOX-5 states it directly ("b(m)'s two regimes mean each B-family is formally TWO (A1) families
(m = 0; m ≥ 1)"). **The B block is therefore 12 fibers of size 2, and nothing else is consistent
with the source.**

**Step 9 — arithmetic closure.** Fibers: `3·1 + 4·1 + (4·1 + 2 + 2 + 3) + (4·1 + 2 + 2 + 3) +
12·2 = 3 + 4 + 11 + 11 + 24 = 53` ✓ and schemas `3 + 4 + 7 + 7 + 12 = 33` ✓ — ANNEX B's two
totals, re-audited at `EFF.HMENU3.69` and again at `EFF.HMENU3.62`. The map is total and
surjective by construction (every block is hit).

#### The assignment (the table D2 owed)

Enumeration convention, fixed once: **inside every block, the sources' own list order, with each
non-singleton fiber occupying a contiguous run** — which is precisely the G.62 PROOF's own reading,
"each **pair** `(m = 0, m ≥ 1)` or `(λ = (1,1), λ = (2))` collapsing to one schema".

| constructor | family index | formal (A1) family | schema | `Fin 33` |
|---|---|---|---|---|
| `sep` | 0 | SEP3 | SEP3 | 0 |
| `sep` | 1 | SEPLQ | SEPLQ | 1 |
| `sep` | 2 | SEPC | SEPC | 2 |
| `dbl` | 0 | DBL-RAM | DBL-RAM | 3 |
| `dbl` | 1 | DBL-2SIDED | DBL-2SIDED | 4 |
| `dbl` | 2 | DBL-SPLITEQ | DBL-SPLITEQ | 5 |
| `dbl` | 3 | DBL-INERTDEEP | DBL-INERTDEEP | 6 |
| `tierI` | 0 | RAM3 | RAM3 | 7 |
| `tierI` | 1 | 3LIN | 3LIN | 8 |
| `tierI` | 2 | LINRAM2 | LINRAM2 | 9 |
| `tierI` | 3 | RAM2LIN | RAM2LIN | 10 |
| `tierI` | 4 | VERT1, `λ = (1,1)` | VERT1 | 11 |
| `tierI` | 5 | VERT1, `λ = (2)` | VERT1 | 11 |
| `tierI` | 6 | VERT2, `λ = (1,1)` | VERT2 | 12 |
| `tierI` | 7 | VERT2, `λ = (2)` | VERT2 | 12 |
| `tierI` | 8 | FULL, `λ = (1,1,1)` | FULL | 13 |
| `tierI` | 9 | FULL, `λ = (1,2)` | FULL | 13 |
| `tierI` | 10 | FULL, `λ = (3)` | FULL | 13 |
| `tierII` | 0 … 10 | `DEEP-`(the tier-I row) | `DEEP-`(the tier-I schema) | tier-I value `+ 7` |
| `bTier` | `2s` | (B-schema `s`), `m = 0` | B-schema `s` | `21 + s` |
| `bTier` | `2s+1` | (B-schema `s`), `m ≥ 1` | B-schema `s` | `21 + s` |

with the twelve B-schemas indexed `s = 0 … 11` in `EFF.HMENU3.11`'s order
`(B1,RAM), (B1,2SIDED), (B1,SPLITEQ), (B1,INERTDEEP), (B2,RAM), …, (B3,INERTDEEP)` — `L` fastest
inside `Bj`. Explicitly, `tierII i = tierI i + 7` and `bTier i = 21 + i / 2`.

#### The body (Lean, as landed)

```lean
/-- The shape schema underlying each formal family (ANNEX B's "33 shape schemas"). -/
def CubicFamilyIndex.schema : CubicFamilyIndex → Fin 33
  | .sep i    => ![0, 1, 2] i
  | .dbl i    => ![3, 4, 5, 6] i
  | .tierI i  => ![7, 8, 9, 10, 11, 11, 12, 12, 13, 13, 13] i
  | .tierII i => ![14, 15, 16, 17, 18, 18, 19, 19, 20, 20, 20] i
  | .bTier i  => ![21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26,
                   27, 27, 28, 28, 29, 29, 30, 30, 31, 31, 32, 32] i
```

#### What is derived and what is convention (honesty note)

**Derived from the source, and forced:** the *fiber partition* of the 53 families — which families
share a schema, and how many schemas each block carries. That is the entire mathematical content
of a map into an **unlabelled** `Fin 33`, and steps 1–9 fix it uniquely: `3` singletons, `4`
singletons, `(4 singletons, 2, 2, 3)`, the same again, and `12` doubletons.

**Convention, and immaterial:** the order in which the families are enumerated inside each
`Fin k`, and the order in which the schemas are enumerated inside `Fin 33`. Any other choice
differs from this one by a permutation of `Fin 33` composed with permutations of the five domain
blocks. `CubicFamilyIndex`'s constructors carry no labels (they are bare `Fin`s — the G.62
STATEMENT's own "this is an INDEX, not a family: it carries no counts and no certificates"), and
the sole declared consumer, G.63's `schema_surjective`, is invariant under any such relabelling.
**No family is left ambiguous; no constructor needs a `[FOR-CROSS-READ]` default.**

#### Machine checks run against the landed body

`Fintype.card CubicFamilyIndex = 53` by `decide` ✓; `Function.Surjective CubicFamilyIndex.schema`
by `decide` (needs `maxRecDepth 8000`) ✓ — so **G.63 is now fireable**, both halves by `decide`;
the fiber-size profile over all 33 schemas evaluates to
`[1,1,1, 1,1,1,1, 1,1,1,1,2,2,3, 1,1,1,1,2,2,3, 2,2,2,2,2,2,2,2,2,2,2,2]`, summing to `53` ✓ —
which is step 9's arithmetic read back off the landed definition.

---

### A-6 — G.52g `c3_pairwise_ne`: **D3 CURED: the ten inequalities stated**

**Banner for the node entry:** `G.52 [SIGNATURE AMENDED 2026-08-15 — see AMENDMENT §A-6]`.

**What was missing.** The G.52 SIGNATURE is literally `theorem c3_pairwise_ne : /- the ten
inequalities -/ True`. The comment names the intent; the proposition is `True`, so the declaration
as contracted is **vacuous** and was landed as such in both `leanspec` (stage-0e) and `leanfinal`.

**The intended statement, recovered from the node's own context.** G.52's STATEMENT is "the five
degree-3 splitting types, with their degrees and **pairwise distinctness**"; the five constants are
the `FactorizationType`s `c3split, c3linInert, c3inert, c3linRam, c3ram` defined in the same
SIGNATURE block (source: `EFF.HMENU3.17`, COROLLARY HM3.D's five rows `(1,1)³`, `(1,2),(1,1)`,
`(1,3)`, `(2,1),(1,1)`, `(3,1)`); "the ten inequalities" is `C(5,2) = 10`, i.e. **the five constants
pairwise distinct as `FactorizationType`s**. The consumer confirms the reading: G.72's PROOF step 3
expands a `Finset` sum over the explicit 5-element menu by `Finset.sum_insert` four times "with the
four distinctness side conditions from G.52's `c3_pairwise_ne`" — side conditions of the form
`σ ∉ {…}`, which are exactly conjunctions of these ten `≠`s. The blueprint's own PROOF line already
prescribes the proof ("the ten inequalities by `decide` after reducing to multiset inequality"),
and the ⚠ RE-DERIVATION TARGET names `leancheck/UniformityCheck/N3Base.lean`, which lands the same
ten as ten separate `decide`-backed one-liners. **The amended signature keeps the blueprint's ONE
declaration and its name**, so the ten are conjoined, in `N3Base`'s enumeration order.

**Amended SIGNATURE.**

```lean
namespace Uniformity.Density

theorem c3_pairwise_ne :
    c3split ≠ c3linInert ∧ c3split ≠ c3inert ∧ c3split ≠ c3linRam ∧ c3split ≠ c3ram
      ∧ c3linInert ≠ c3inert ∧ c3linInert ≠ c3linRam ∧ c3linInert ≠ c3ram
      ∧ c3inert ≠ c3linRam ∧ c3inert ≠ c3ram
      ∧ c3linRam ≠ c3ram
```

**PROOF (landed, 3 lines).** `FactorizationType` is a one-field structure over
`Multiset (ℕ × ℕ)` whose `DecidableEq` instance is `Classical.decEq` (`LocalData.lean:56`), so
`decide` cannot see the type itself; transport each goal along the field projection first, exactly
as the blueprint's PROOF line says:

```lean
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact mt (congrArg FactorizationType.data) (by decide)
```

`Multiset (ℕ × ℕ)` has a genuine `DecidableEq`, so each `by decide` discharges one multiset
inequality. Footprint: `[propext, Classical.choice, Quot.sound]` — Lean core only.

**Non-vacuity check.** The ten `≠`s are pairwise-distinct *degree-3* multisets, so no pair
collapses: their cardinalities are `3, 2, 1, 2, 1` and the two card-`2` types differ in their
second pair (`(1,2)` vs `(2,1)`), the two card-`1` types likewise (`(1,3)` vs `(3,1)`). Nothing
here is provable from `c3_degrees` alone (all five have degree 3), which is why the node contracts
a second theorem at all.

---

### Amendment bookkeeping (second append)

| item | defect | verdict | nodes touched | files changed |
|---|---|---|---|---|
| A-5 | D2 (G.62b) | **body derived** from `EFF.HMENU3` `.09/.11/.14/.17/.37/.62/.67/.68/.69`; assignment total, no `[FOR-CROSS-READ]` residue | G.62 (body only; signature unchanged) | `leanfinal/…/ChapG/G62.lean`, `leanspec/Leanspec/ChapG.lean` |
| A-6 | D3 (G.52g) | **statement recovered** from G.52's own context + G.72's consumer; proof landed | G.52 (G.52g signature only) | `leanfinal/…/ChapG/G52.lean`, `leanspec/Leanspec/ChapG.lean` |

Declaration census: **109**, unchanged. Stage-0e defects still open: **D1** (G.18 `tangCert`
placeholder — repaired in `leanspec` by the minimal `(by omega : …)` fill, blueprint entry still
owes the fill), **D4** (ENV-A under-binds `[Finite (ResidueField O)]`, systematic across 22 stubs),
**D5** (cosmetic, `ring_nf` vs `ring1` at G.03). Items 5–12 of §14 remain owed to the codex
cross-read.

**Verification performed for this append.** `leanfinal` builds green, `sorry`-free, 8,601 jobs, with
`c3_pairwise_ne` reporting `[propext, Classical.choice, Quot.sound]` and `c3_degrees`
`[propext, Quot.sound]`. The stage-0e **type diff** was run for both re-signed stubs against their
landed `leanfinal` twins and passes definitionally: `CubicFamilyIndex.schema = ⟨the stub body⟩`
by `rfl` and `c3_pairwise_ne`'s stub proposition is the landed one.

**⚠ RECORDED FOR THE FLEET (pre-existing, not caused by this append): `leanspec` no longer builds
green.** `leanspec/Leanspec/ChapG.lean` re-declares contract names inside `Uniformity.Density`
and `Uniformity.Density.Menu` while importing the real `Uniformity` package, so every stub whose
node has since landed in `leanfinal` now fails with *"has already been declared"* — **32 such
collisions at the start of this append** (`ExactVal`, `readEquiv`, `CertFamily`, `tangSet`,
`dvdSet`, `residualPair`, `c3split`…`c3ram`, `c3_pairwise_ne`, …), growing by one every time a
chapter-G node lands. The gate's own note "Name collisions: none. All 110 names elaborate in an
environment that already contains all of `leanfinal`" was true when `leanfinal` held no chapter-G
node and is now stale. **This append adds the 33rd collision** (`CubicFamilyIndex.schema`, which
became a real `def` in `leanfinal` at §A-5); D3's re-sign adds none, since `c3_pairwise_ne` was
already colliding. The condition is structural — it is the price of the current "stubs live in the
production namespace" design — and its repair (wrap the contract file in its own namespace, or
retire each stub as its node lands) is a repo-level decision outside a defect-cure unit's scope.
**Nothing about the contract is lost meanwhile**: the type diff above is exactly the check the
stub file exists to support, and it can be run per declaration without elaborating the whole file.

---

## AMENDMENT 2026-08-15 (third dated append; Opus arm) — G.31's DEPENDENCY GAP CURED

**Status of this block.** A third dated append in the same convention as the two above:
**nothing in §§0–14 is edited in place**; the banner prescribed at §A-7 for G.31's node entry
points here and this block governs. It discharges the **open obstruction** the wave-3 fleet
booked against G.31 (recorded in `leanspec/Leanspec/ChapG.lean`'s header: "G.31 needs
`Finset.range N` in `decidedSet_ram_eq` justified by showing `depthSet π N t = ∅` for `t ≥ N`,
which is not among its DEPENDS and was not established"). The cure adds **one micro-node**, so
the declaration census rises **109 → 110**.

---

### A-7 — G.31's missing supplier: **GAP CURED by a new micro-node G.30a; G.31's own STATEMENT is CORRECT as signed**

**Banner for the node entry:** `G.31 [DEPENDS AMENDED 2026-08-15 — see AMENDMENT §A-7; statement
unchanged, previously BLOCKED]`.

**The gap, exactly.** G.31's conclusion is

```lean
decidedSet O 2 ramType N = ⋃ j ∈ Finset.range N, depthSet π N (2 * j + 1)
```

The blueprint's PROOF discharges the `⊆` inclusion (steps 1–4: a ram-decided class has a maximal
depth `t < N`, odd by G.30, giving `j < N`) but the `⊇` inclusion needs more than step 1 supplies.
`Finset.range N` runs `j = 0 … N−1`, i.e. odd depths `2j+1` up to `2N−1`, whereas G.30 — the
supplier that makes a stratum ram-decided — is only available at `t < N`. The union therefore
**overshoots**: for `N ≤ 2j+1 ≤ 2N−1` the blueprint offers nothing about `depthSet π N (2j+1)`,
and the inclusion fails unless those strata are empty. That is the fleet's obstruction, and it is
real.

**Adjudication.** The fact the fleet asked for — `depthSet π N t = ∅` for **all** `t ≥ N` — is
**FALSE** (counterexample below, residue characteristic 2, even `t`). The restriction to **odd**
`t` is **TRUE**, provable in ~15 lines from the landed `depthSet`/`Tang` definitions, and is
exactly what an odd-indexed union consumes. So:

* **G.31's STATEMENT is correct as signed** — no defect, no repair, and it is now landed
  (`leanfinal/Uniformity/ChapG/G31.lean`);
* the missing supplier is signed below as **MICRO-NODE G.30a** and landed as
  `leanfinal/Uniformity/ChapG/G30a.lean`;
* any future consumer tempted by the general form must not assume it — see the counterexample.

**Why the node is called `G.30a` and not `G.31a`.** `G.31a`/`G.31b`/`G.31c` are already in use as
the DECLARATION letters of node G.31's three declarations (`inertStratum`, `splitStratum`,
`decidedSet_ram_eq`; see `leanspec/Leanspec/ChapG.lean`), in the same convention that gives
`G.23a`, `G.52g`, `G.62b` elsewhere in this document. The new node is a node in its own right,
topologically between G.30 and G.31 (its only intra-chapter DEPENDS is G.19), so it takes a
node-level letter at G.30, whose single declaration carries no letter. Node names are always
introduced by a `### NODE` heading; declaration letters never are.

#### The mechanism: why ODD works and EVEN fails

Fix a level-`N` class `c`, a lift `a`, a centre `γ` with `Tang π a t γ`, i.e.
`π^t ∣ qval a γ` and `π^((t+1)/2) ∣ qder a γ` (`Drainage.lean:511`). Assume `t ≥ N`. Ask whether
`c` can be pushed to depth `t+1` **without leaving its class**.

**Move 1 — the value is free above the window, always.** Replace `a` by
`b := ![a 0 − qval a γ, a 1]` (G.33's move). Then `qval b γ = 0` and `qder b γ = qder a γ`, and `b`
is a lift of the *same* class because `a 0 − b 0 = qval a γ` is `π^t`-divisible, hence
`π^N`-divisible as `t ≥ N`. The value requirement at depth `t+1` is therefore free.

**Move 2 — the derivative requirement moves only at even `t`.** Depth `t+1` asks
`π^((t+2)/2) ∣ qder`.

* `t = 2j+1` **odd**: `(t+2)/2 = (2j+3)/2 = j+1 = (2j+2)/2 = (t+1)/2`. The requirement does not
  move, so Move 1 alone finishes: **`depthSet π N (2j+1) = ∅` whenever `N ≤ 2j+1`.**
* `t = 2k` **even**: `(t+1)/2 = k` but `(t+2)/2 = k+1`. The requirement genuinely increases by one,
  and the class may be unable to meet it.

**The even obstruction, in coordinates.** For a fixed lift, every centre of depth `≥ 2k` is
`γ + π^k z` (if `π^(2k)` divides both `qval a γ` and `qval a γ'`, then writing `h = γ' − γ` and
`qval a γ' = qval a γ + qder a γ·h + h²`, a valuation `v(h) < k` would force
`v(qval a γ') = 2v(h) < 2k`). Writing `qval a γ = π^(2k) b₀`, `qder a γ = π^k b₁`,

```
qval a (γ + π^k z) = π^(2k) · (z² + b₁ z + b₀),      qder a (γ + π^k z) = π^k · (b₁ + 2z)
```

so reaching depth `2k+1` means the residual quadratic acquires a **double** root mod `π`:
`∃ z, π ∣ z² + b₁z + b₀ ∧ π ∣ b₁ + 2z`. The freedom available inside the class is exactly
`δ₀, δ₁ ∈ π^N·O` added to the two coefficients, which moves `b₀` by `(δ₁γ + δ₀)/π^(2k)` — **all of
`O` mod `π`, since `N ≤ 2k`** — but moves `b₁` only by `π^(N−k)·O`. In the entire overshoot regime
`N ≤ 2k < 2N` we have `k < N`, so **`b₁ mod π` is pinned by the class**. If the residue
characteristic is odd this costs nothing (`z := −b₁/2` kills `b₁ + 2z`, and the free `b₀` is then
set to `b₁²/4`); in residue characteristic **2**, `b₁ + 2z ≡ b₁`, so the double root exists only
when `π ∣ b₁` — a condition the class can neither supply nor repair.

**Counterexample to the general form (`t ≥ N`, even `t`).** `O = ℤ₂`, `π = 2`, `N = 2`, `t = 2`,
`c = proj O 2 2 ![0, 2]`.

* `c ∈ tangSet 2 2 2`: take the lift `![0,2]` and `γ = 0` — `qval = 0` (so `4 ∣ qval`) and
  `qder = 2` (so `2 = π^((2+1)/2) ∣ qder`).
* `c ∉ tangSet 2 2 3`: a lift is `b = ![4l, 2+4m]`; depth 3 asks `4 ∣ qder b γ = 2γ + 2 + 4m`,
  forcing `γ` **odd**, and then `qval b γ = γ² + (2+4m)γ + 4l` is **odd**, so `8 ∤ qval b γ`.

Hence `depthSet 2 2 2 ≠ ∅` although `t = N`. A second instance with `t > N`: `N = 3`, `t = 4`,
`c = proj O 2 3 ![0, 4]`. Both were verified twice — by the hand argument above and by exhaustive
search over lifts and centres mod `2^8` (`verification/`-style scratch check, 2026-08-15).

**Consistency with the chapter's counts.** Nothing else in chapter G asserts the general form:
G.17 `card_tangSet` is stated only at `N = t+r` (`t ≤ N`) and G.20 `card_depthSet` only at
`N = t+1+r` (`t < N`), so no landed count reaches above the window, and the nonempty even stratum
at `N = t = 2`, `q = 2` disturbs neither `card_tangSet π N N = q^N` nor the drainage law of §6.

---

### NODE G.30a [lemma] [fresh, added by AMENDMENT §A-7]

**STATEMENT.** *Odd strata above the window are empty.* At level `N`, no class has exact depth
`2j+1` once `N ≤ 2j+1`: the value at the centre can be killed without leaving the class, and at
odd depth the derivative requirement does not increase.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem depthSet_odd_eq_empty (hπ : Irreducible π) {N j : ℕ} (hN : N ≤ 2 * j + 1) :
    depthSet π N (2 * j + 1) = (∅ : Set (Coeff O 2 N))
```

**DEPENDS.** G.19 · landed `proj_eq_iff_dvd` (`DensityAPI.lean:124`), `qval`, `qder`, `Tang`.

**PROOF.**
1. `Set.eq_empty_iff_forall_notMem`; take `c` in the stratum and destructure `hc.1` into a lift
   `a`, a centre `γ` and `hTang : Tang π a (2j+1) γ`.
2. exhibit `![a 0 − qval a γ, a 1]` as a witness for `c ∈ tangSet π N (2j+1+1)`, contradicting
   `hc.2`.
3. same class: `proj_eq_iff_dvd hπ` coordinatewise; the `1`-coordinate is equal, the
   `0`-coordinate differs by `qval a γ`, and `π^N ∣ qval a γ` by `pow_dvd_pow π hN` composed with
   `hTang.1`.
4. value: `qval ![a 0 − qval a γ, a 1] γ = 0` by `simp only [qval, …]; ring`, then `dvd_zero`.
5. derivative: `qder` is unchanged, and `(2j+1+1+1)/2 = (2j+1+1)/2` by `omega`, so `hTang.2` is
   already the goal. **This step is the whole content: it is what fails at even depth.**

**SIZE.** 15 lines. One public declaration.

**SOURCE.** None — derived at this amendment from the landed `depthSet`/`Tang` definitions. No
`EFF` unit states it; W-11's census units stop at the window (`EFF.W11.22`), which is why the gap
survived the blueprint freeze.

**TEETH.** None of its own; it is a supplier for G.31's `W11-EXHAUST` / P-4 teeth.

**ENVIRONMENT.** ENV-A' (`Irreducible π`; **no** completeness — this node does not need ENV-B).

---

### G.31's corrected DEPENDS

The landed proof (`leanfinal/Uniformity/ChapG/G31.lean`) uses:

**DEPENDS.** G.12, G.19, G.25, G.30, **G.30a**, G.33 · landed `decidedSet`
(`GenuineDensity.lean:74`), `proj_surjective`, `exists_max_step` (`Drainage.lean:556`),
`Tang_zero`, `splitType_ne_ramType`, `inertType_ne_ramType`.

Three changes against the blueprint's `G.19, G.29, G.30 · landed decidedSet,
decidedSet_disjoint, typeOf_two_cases, undecidedSet`:

1. **G.30a added** — the cure, consumed in the `⊇` branch `N ≤ 2j+1`.
2. **G.29 drops out; G.33 and G.12 come in.** The blueprint's step 2 wants "a class in
   `tangSet π N N` has two lifts of different types (G.33, G.34)". Only **one** is needed: if a
   ram-decided class had a depth-`N` centre, G.33's `exists_split_lift` produces a `splitType`
   lift of that same class, and `splitType_ne_ramType` closes it. G.29 states the converse
   implication (depth `< N` ⇒ decided) and is not used. G.12 `tang_of_proj_eq` is needed to
   transfer the maximality of the depth across lifts of the class.
3. **`decidedSet_disjoint` and `typeOf_two_cases` drop out.** G.30's even branch is refuted
   directly: it hands a second decided type for the same class, so applying both `DecidedAt`s to
   one lift gives `inertType = ramType` (resp. `splitType = ramType`).

The blueprint's PROOF steps 1–4 are otherwise landed as written; step 4's index bound `j < N` from
`2j+1 < N` is the `⊆` half only, and the `⊇` half is the new step "`2j+2 ≤ N`: G.25; otherwise
G.30a".

---

### Amendment bookkeeping (third append)

| item | obstruction | verdict | nodes touched | files changed |
|---|---|---|---|---|
| A-7 | wave-3's G.31 BLOCK (`depthSet π N t = ∅ for t ≥ N` missing) | **gap cured**; the general form is **refuted** at even `t` in residue char 2, the ODD form is proved and suffices | **G.30a NEW**; G.31 DEPENDS corrected (statement unchanged) | `leanfinal/…/ChapG/G30a.lean` (new), `leanfinal/…/ChapG/G31.lean` (new), `leanfinal/…/ChapG.lean`, `leanspec/Leanspec/ChapG.lean` |

Declaration census: **110** (109 + G.30a's one theorem). Contract count in
`leanspec/Leanspec/ChapG.lean` rises to 110 accordingly. Stage-0e defects still open: **D1**
(G.18's placeholder, blueprint entry still owes the fill), **D4** (ENV-A under-binds
`[Finite (ResidueField O)]`), **D5** (cosmetic). Items 5–12 of §14 remain owed to the codex
cross-read. **G.23 remains the chapter's only standing BLOCK** (statement refuted at §A-1); with
this append **G.31 is no longer blocked**.

**Verification performed for this append.** `leanfinal` builds green and `sorry`-free with both
new modules wired into the `Uniformity.ChapG` roll-up;
`Uniformity.Density.Menu.depthSet_odd_eq_empty` and `Uniformity.Density.Menu.decidedSet_ram_eq`
each report `[propext, Classical.choice, Quot.sound]` (Lean core only). `leanspec` builds green
with G.30a and all three of G.31's declarations retired to the `example := <landed name>`
form, which machine-checks that the landed types are the signed ones.

---

## AMENDMENT 2026-08-15 (fourth dated append; Opus arm) — §A-1's REPLACEMENT ROUTE EXPANDED INTO FIREABLE NODES (G.23R1–G.23R12), ALL LANDED

**Status of this block.** A fourth dated append in the same convention as the three above:
**nothing in §§0–14 is edited in place**; one line is added to the existing G.23 amendment banner
pointing here. §A-1 refuted `card_resStratum` (G.23a) and *derived* a replacement route — certify
a **translation-invariant residual CLASS** at centre modulus `m = k` instead of an individual
pair — but stopped at the derivation: it named no signatures, no DEPENDS, no proof steps, so no
agent could fire it, and the G.41–G.51 exact-density tail stayed gated. This block expands that
route into **twelve node entries**, and records that all twelve are **landed in `leanfinal`,
`sorry`-free, Lean-core-only**. Declaration census rises **110 → 135**.

**Nothing in §A-1 is revised.** Every step below is §A-1's own derivation, formalized: `hshift`
at `m = k` is the translation-invariance of `𝒫`; `huniq` at `m = k` is G.11 verbatim;
`#S = #𝒫 · q^(N−2k−1) · q^(N−k−1)`; `card_certSet_gen` contributes `q^k`. The one thing §A-1 did
not say, and which the formalization had to supply, is **how** `#S` is counted: not by a
digit-extraction function on `Res O N` (which needs a well-definedness proof at every use site)
but by exhibiting `S` as the **preimage of a TOP-level set** `resTop ⊆ Res O (2k+1) × Res O (k+1)`
under the two-coordinate truncation, where the two digits are exactly determined and the set is a
literal copy of `𝒫`. That is nodes G.23R1/R4/R5/R6, and it is the only design decision in this
append that §A-1 did not already fix.

**No step of the route resisted proof as derived.** No obstruction is recorded below, because
none was found; the honesty clause of this unit's charge is discharged vacuously.

---

### A-8.0 — the route in one page, and what each node supplies

Fix `N = 2k+1+r` and a residual class `P ⊆ K × K`, `K = ResidueField O`.

| node | supplies |
|---|---|
| G.23R1 | `prodResFactor`: the truncation `Res O N × Res O N →+ Res O m₀ × Res O m₁`, and its **subtraction-free fibre count** |
| G.23R2 | the digit read is well posed: `π^j·y`'s class determines `ȳ` (below `N`), and conversely at level `j+1` |
| G.23R3 | `transPair` / `TransInvariant`, and the two classes the chapter needs are invariant AND double-root-free |
| G.23R4 | `resTop`, `resAdm`, `resClassSet`, and `resAdm = prodResFactor ⁻¹' resTop` |
| G.23R5 | `#resTop = #P` |
| G.23R6 | `#resAdm = #P · q^(k+2r)` — §A-1's `#S = #𝒫 · q^(N−2k−1) · q^(N−k−1)` |
| G.23R7 | the certificate bridge: what the read at a centre means in `(b₀, b₁)` coordinates |
| G.23R8 | `resCert`: the certified family at `m = k`, with `hcert`/`hshift`/`huniq` discharged |
| **G.23R9** | **THE COUNT FORMULA** `#resClassSet = #P · q^(2k+2r)` |
| G.23R10 | the `residualPair` computation rule — links the route to G.21/G.22's phrasing |
| G.23R11 | a double-root-free class lands in `depthSet π N (2k)`, i.e. depth **exactly** `2k` |
| G.23R12 | the `O ↔ K` bridges `Anisotropic ↔ AniForm` and `SepPair ↔ (simple residual root)` |

**Naming.** The route's nodes take the letters `R1 … R12` at node G.23 because `G.23a`/`G.23b` are
already the DECLARATION letters of G.23's two declarations (§A-7's convention: declaration letters
are lowercase and never carry a `### NODE` heading; these are nodes in their own right and do).

---

### NODE G.23R1 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The two-coordinate truncation and its fibre count.* The map
`(x₀, x₁) ↦ (resFactor x₀, resFactor x₁)` is a surjective additive homomorphism, and the preimage
of any `S` satisfies `#(f ⁻¹' S) · q^(m₀+m₁) = q^N · q^N · #S` — subtraction-free, the kernel size
`q^(N−m₀)·q^(N−m₁)` never named.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

def prodResFactor {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N) :
    (Res O N × Res O N) →+ (Res O m₀ × Res O m₁)

theorem card_preimage_prodResFactor {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N)
    (S : Set (Res O m₀ × Res O m₁)) :
    Nat.card (prodResFactor (O := O) h₀ h₁ ⁻¹' S) * (residueCard O ^ m₀ * residueCard O ^ m₁)
      = residueCard O ^ N * residueCard O ^ N * Nat.card S
```

**DEPENDS.** landed `resFactor`, `resFactor_surjective`, `card_res`,
`card_preimage_of_surjective` (`LocalData.lean:192,215,221,228`).

**PROOF.**
1. the hom: `toFun`, `map_zero'`, `map_add'` all by `simp`; surjectivity coordinatewise from
   `resFactor_surjective`.
2. apply `card_preimage_of_surjective` **twice** — at `S` and at `Set.univ` — exactly as
   `card_dvdSet` (G.14) does; the second instance evaluates `#ker · (q^m₀·q^m₁) = q^N·q^N`.
3. substitute and `ring`. No cancellation, hence no positivity side condition.

**SIZE.** 40 lines (2 signed declarations + 2 support lemmas `prodResFactor_apply`,
`prodResFactor_surjective`). **LANDED** `leanfinal/Uniformity/ChapG/G23R1.lean`.

**SOURCE.** `EFF.W11.14` (the two-factor admissible count this generalises the shape of); the
proof pattern is G.14's, re-cut for a product.

**TEETH.** none of its own; supplier for G.41/G.42's `W11-CENSUS` / P-2 teeth.

**ENVIRONMENT.** ENV-A.

---

### NODE G.23R2 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The digit read is well posed.* For `j < N`, the class of `π^j·y` in `Res O N`
determines `y mod 𝔪`; for `N ≤ j+1`, equal digits give equal classes. (Uniqueness is what makes
the route's residual read a function of the class; realization is what makes the level-`(j+1)`
read a bijection onto its image, which is G.23R5's surjectivity leg.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem residue_eq_of_mk_pow_mul_eq (hπ : Irreducible π) {j N : ℕ} (hj : j < N) {y y' : O}
    (h : (Ideal.Quotient.mk _ (π ^ j * y) : Res O N) = Ideal.Quotient.mk _ (π ^ j * y')) :
    IsLocalRing.residue O y = IsLocalRing.residue O y'

theorem mk_pow_mul_eq_of_residue_eq (hπ : Irreducible π) {j N : ℕ} (hN : N ≤ j + 1) {y y' : O}
    (h : IsLocalRing.residue O y = IsLocalRing.residue O y') :
    (Ideal.Quotient.mk _ (π ^ j * y) : Res O N) = Ideal.Quotient.mk _ (π ^ j * y')
```

**DEPENDS.** landed `mem_maximalIdeal_pow_iff_dvd`, `mem_maximalIdeal_iff_dvd`
(`Drainage.lean:635,192`).

**PROOF.**
1. uniqueness: `Ideal.Quotient.eq` gives `π^N ∣ π^j·(y−y')`; write `π^N = π^j·π^(N−j)` and cancel
   `π^j` (`mul_dvd_mul_iff_left`, `O` a domain, `π ≠ 0`); `N−j ≥ 1` gives `π ∣ y−y'`.
2. realization: `π ∣ y−y'` gives `π^(j+1) ∣ π^j·(y−y')`, and `π^N ∣ π^(j+1)` by `pow_dvd_pow`.

**SIZE.** 30 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R2.lean`.

**SOURCE.** None — derived at this amendment. The digit vocabulary is `EFF.W11.15`'s
(`c₁ = digit_k(A₁)`, `c₀ = digit_2k(A₀)`); nothing in W-11 states its well-definedness, which is
precisely the gap §A-1's route (a) fell into at the *pair* level.

**TEETH.** none of its own.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R3 [def+lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The residual translation action, and the two invariant classes.* `transPair d p`
is the coefficient pair of `R(y+d)` for `R(y) = y² + p.2·y + p.1`, i.e. §A-1's
`(b₀, b₁) ↦ (b₀ + b₁d + d², b₁ + 2d)`; a class is `TransInvariant` when closed under it. `AniForm`
and `SepPair` are invariant (translation does not change how `R` factors) and both are disjoint
from `DblPair`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

def transPair {K : Type*} [CommRing K] (d : K) (p : K × K) : K × K :=
  (p.1 + p.2 * d + d * d, p.2 + 2 * d)

def TransInvariant {K : Type*} [CommRing K] (P : Set (K × K)) : Prop :=
  ∀ (d : K) (p : K × K), p ∈ P → transPair d p ∈ P

theorem aniForm_transInvariant {K : Type*} [Field K] : TransInvariant {p : K × K | AniForm p}
theorem sepPair_transInvariant {K : Type*} [Field K] : TransInvariant {p : K × K | SepPair p}
theorem aniForm_not_dblPair {K : Type*} [Field K] {p : K × K} (h : AniForm p) : ¬ DblPair p
theorem sepPair_not_dblPair {K : Type*} [Field K] {p : K × K} (h : SepPair p) : ¬ DblPair p
```

**DEPENDS.** G.38 (`AniForm`), G.39 (`SepPair`), G.40 (`DblPair`, `dblPair_inj`'s idea).

**PROOF.**
1. `aniForm_transInvariant`: a root `y` of the translated quadratic gives the root `y − d` of the
   original — one `linear_combination`.
2. `sepPair_transInvariant`: `(uv, u+v) ↦ ((u+d)(v+d), (u+d)+(v+d))` by `ring`, and `u ≠ v` gives
   `u+d ≠ v+d` by `add_right_cancel`.
3. `aniForm_not_dblPair`: `(y·y, y+y)` has the root `y`.
4. `sepPair_not_dblPair`: from `uv = y²` and `u+v = 2y`, `(u−y)(v−y) = 0`, and either branch plus
   the sum forces `u = v`.

**SIZE.** 35 lines (6 signed declarations, all short). **LANDED**
`leanfinal/Uniformity/ChapG/G23R3.lean`.

**SOURCE.** §A-1's orbit computation (`qval_shift`/`qder_shift` ⇒ `y ↦ y + d̄`); `EFF.W11.16`'s
row types are the invariants.

**TEETH.** `W11-CENSUS` (the row types are translation-invariant — a fact the census table
assumes and never states) → **Lean theorem**.

**ENVIRONMENT.** ENV-C (binds its own `K`).

---

### NODE G.23R4 [def+lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The route's three sets, and the preimage identity.* `resAdm π P k N` is §A-1's
admissible set `S`: the `(value, derivative)` reads of shape `(π^(2k)·y₀, π^k·y₁)` with digit pair
in `P`. `resTop π P k` is the same read at the levels `(2k+1, k+1)`. `resClassSet π P k N` is the
certified set. And `resAdm = prodResFactor ⁻¹' resTop`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

def resTop (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k : ℕ) :
    Set (Res O (2 * k + 1) × Res O (k + 1)) :=
  {x | ∃ y₀ y₁ : O,
      x = (Ideal.Quotient.mk _ (π ^ (2 * k) * y₀), Ideal.Quotient.mk _ (π ^ k * y₁))
        ∧ (IsLocalRing.residue O y₀, IsLocalRing.residue O y₁) ∈ P}

def resAdm (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
    (k N : ℕ) : Set (Res O N × Res O N) :=
  {x | ∃ y₀ y₁ : O,
      x = (Ideal.Quotient.mk _ (π ^ (2 * k) * y₀), Ideal.Quotient.mk _ (π ^ k * y₁))
        ∧ (IsLocalRing.residue O y₀, IsLocalRing.residue O y₁) ∈ P}

def resClassSet (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
    (k N : ℕ) : Set (Coeff O 2 N) :=
  {c | ∃ (a : Fin 2 → O) (γ b₀ b₁ : O), proj O 2 N a = c ∧
      qval a γ = π ^ (2 * k) * b₀ ∧ qder a γ = π ^ k * b₁ ∧
      (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) ∈ P}

theorem resAdm_eq_preimage (hπ : Irreducible π) {P} {k N : ℕ}
    (h₀ : 2 * k + 1 ≤ N) (h₁ : k + 1 ≤ N) :
    resAdm π P k N = prodResFactor (O := O) h₀ h₁ ⁻¹' resTop π P k
```

**DEPENDS.** G.23R1, G.23R2 · landed `Res`, `resFactor_mk`, `qval`, `qder`, `proj`.

**PROOF.** (⊆) `resFactor_mk` on both coordinates. (⊇) the private helper
`exists_digit_of_resFactor`: lift `x.i` to `w ∈ O`; `π^(j+1) ∣ w − π^j·y` gives
`w = π^j·(y + π·s)`, and `y + π·s` has the same digit.

**Design note (the one decision §A-1 left open).** `resClassSet` is phrased with **explicit**
`b₀ b₁` rather than through G.21's `residualPair` (whose `Classical.choose` witnesses are awkward
at use sites); G.23R10 supplies the equivalence, so no consumer is constrained by the choice.

**SIZE.** 40 lines (4 signed declarations + 1 private helper). **LANDED**
`leanfinal/Uniformity/ChapG/G23R4.lean`.

**SOURCE.** §A-1's `cert_𝒫` display, verbatim (`resAdm` refines `tangAdm π (2k) N` by the digit
condition, which is A-1's conjunction).

**TEETH.** none (definitions).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R5 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The TOP-level admissible set is a copy of `P`.* `#(resTop π P k) = #P`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_resTop (hπ : Irreducible π)
    (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k : ℕ) :
    Nat.card (resTop π P k) = Nat.card P
```

**DEPENDS.** G.23R2, G.23R4 · landed `Ideal.Quotient.mk_surjective`.

**PROOF.**
1. take `sec := Function.surjInv` of `IsLocalRing.residue O` and map
   `p ↦ (⟦π^(2k)·sec p.1⟧, ⟦π^k·sec p.2⟧)`; well defined because `residue (sec β) = β`.
2. injective: G.23R2's uniqueness at `(j, N) = (2k, 2k+1)` and `(k, k+1)` (both `j < N`).
3. surjective: G.23R2's realization at the same two places (both `N ≤ j+1`, with equality).

**SIZE.** 35 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R5.lean`.

**SOURCE.** §A-1's `#S = #𝒫 · q^(N−2k−1) · q^(N−k−1)` — this node is the `#𝒫` factor, isolated.

**TEETH.** none of its own.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R6 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *§A-1's admissible count.* At `N = 2k+1+r` (so `N−2k−1 = r`, `N−k−1 = k+r`),
`#(resAdm π P k N) = #P · q^(k+2r)` — subtraction-free.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem card_resAdm (hπ : Irreducible π)
    (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k r : ℕ) :
    Nat.card (resAdm π P k (2 * k + 1 + r)) = Nat.card P * residueCard O ^ (k + 2 * r)
```

**DEPENDS.** G.23R1, G.23R4, G.23R5 · landed `residueCard_pos`.

**PROOF.** `resAdm_eq_preimage` + `card_preimage_prodResFactor` + `card_resTop` give
`X · q^(3k+2) = q^(k+2r) · q^(3k+2) · #P`; cancel the positive `q^(3k+2)`
(`Nat.eq_of_mul_eq_mul_right`). Exponent bookkeeping by `omega` inside two `pow_add` rewrites.

**SIZE.** 20 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R6.lean`.

**SOURCE.** `EFF.W11.14`; §A-1's `#S` display.

**TEETH.** `W11-CENSUS` / P-2 → **Lean theorem** (jointly with G.23R9).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R7 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The certificate bridge* (the route's analogue of G.18's `cert_iff_tang`). For
`2k < N` and `k < N`, reading `proj O 2 N a` at the centre class `⟦γ⟧` lands in `resAdm π P k N`
iff the **integral** value and derivative factor as `π^(2k)·b₀`, `π^k·b₁` with `(b̄₀, b̄₁) ∈ P`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem resAdm_read_iff (hπ : Irreducible π) {P} {k N : ℕ} (h₀ : 2 * k < N) (h₁ : k < N)
    (γ : O) (a : Fin 2 → O) :
    readEquiv (Ideal.Quotient.mk _ γ) (proj O 2 N a) ∈ resAdm π P k N
      ↔ ∃ b₀ b₁ : O, qval a γ = π ^ (2 * k) * b₀ ∧ qder a γ = π ^ k * b₁ ∧
          (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) ∈ P
```

**DEPENDS.** G.04 (`readEquiv_proj`), G.23R2, G.23R4 · landed `mem_maximalIdeal_pow_iff_dvd`.

**PROOF.**
1. `readEquiv_proj` rewrites the read to `(⟦qval a γ⟧, ⟦qder a γ⟧)`.
2. (→) the class equation gives `π^N ∣ qval a γ − π^(2k)·y₀`; since `2k ≤ N` this upgrades to
   `π^(2k) ∣ qval a γ`, producing an integral `b₀`; G.23R2's uniqueness (here `2k < N` is used)
   identifies `b̄₀ = ȳ₀`. Same at `k`.
3. (←) immediate.

**SIZE.** 30 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R7.lean`.

**SOURCE.** G.18 step 2's shape; §A-1's `cert_𝒫`.

**TEETH.** none of its own.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R8 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The residual-class census datum at centre modulus `m = k`.* The three
`card_certSet_gen` hypotheses for `cert γ c := readEquiv γ c ∈ resAdm π P k N`, discharged, plus
the identification of the certified set with `resClassSet π P k N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem resCert (hπ : Irreducible π) {P} (hP : TransInvariant P) (k r : ℕ) :
    ∃ cert : Res O (2 * k + 1 + r) → Coeff O 2 (2 * k + 1 + r) → Prop,
      (∀ g c, cert g c ↔ readEquiv g c ∈ resAdm π P k (2 * k + 1 + r))
      ∧ (∀ g g' c, cert g c → resFactor (O := O) (by omega : k ≤ 2 * k + 1 + r) g'
            = resFactor (by omega : k ≤ 2 * k + 1 + r) g → cert g' c)
      ∧ (∀ g g' c, cert g c → cert g' c → resFactor (O := O) (by omega : k ≤ 2 * k + 1 + r) g'
            = resFactor (by omega : k ≤ 2 * k + 1 + r) g)
      ∧ (∀ c, (∃ g, cert g c) ↔ c ∈ resClassSet π P k (2 * k + 1 + r))
```

**DEPENDS.** G.11, G.23R3, G.23R7 · landed `proj_surjective`, `Ideal.Quotient.mk_surjective`,
`qval_shift`, `qder_shift`, `mem_maximalIdeal_pow_iff_dvd`.

**PROOF.**
1. `hcert` is `Iff.rfl`.
2. **`hshift` at `m = k` — the point of the whole route.** `resFactor` equality gives
   `γ' = γ + π^k·d`; `qval_shift`/`qder_shift` give `qval a γ' = π^(2k)·(b₀+b₁d+d²)` and
   `qder a γ' = π^k·(b₁+2d)`, so the residual pair moves by `transPair d̄`, absorbed by `hP`.
   (Residue is a ring hom; the two `map_add`/`map_mul` rewrites are explicit, not `simp`, because
   `simp` mis-normalises `residue (2·d)`.)
3. **`huniq` at `m = k` is G.11 verbatim**: `cert` gives `Tang π a (2k) γ` since `(2k+1)/2 = k`,
   and `tang_centre_unique` returns `π^k ∣ γ' − γ`.
4. the last conjunct is G.23R7 read in both directions on a lift of `c` and a lift of `g`.

**SIZE.** 45 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R8.lean`.

**SOURCE.** §A-1 ("`hshift` at modulus `m = k` now **holds**… `huniq` at `m = k` is G.11
verbatim"); G.18's shape.

**TEETH.** `W11-CENSUS` / P-2 → **Lean theorem** (jointly with G.23R9).

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R9 [theorem] [fresh, added by AMENDMENT §A-8] — **THE COUNT FORMULA**

**STATEMENT.** **The replacement route's headline, and G.23a's replacement on the critical path.**
At level `N = 2k+1+r`, the classes carrying a residual pair in a *translation-invariant* class `P`
at a centre of depth `≥ 2k` number `#P · q^(2k+2r)` — i.e. `#P · q^(2N−2k−2)`.

**SIGNATURE (landed byte-for-byte).**
```lean
namespace Uniformity.Density.Menu

theorem card_resClassSet (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : TransInvariant P) (k r : ℕ) :
    Nat.card (resClassSet π P k (2 * k + 1 + r))
      = Nat.card P * residueCard O ^ (2 * k + 2 * r)
```

**DEPENDS.** G.23R6, G.23R8 · landed `UniformityCheck.card_certSet_gen` (`CensusGen.lean:64`).

**PROOF.** `card_certSet_gen` at `m = k` on `resCert`'s family; rewrite the certified set by
`resCert`'s last conjunct and the admissible count by G.23R6; then
`q^k · (#P · q^(k+2r)) = #P · q^(2k+2r)`.

**SIZE.** 20 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R9.lean`.

**⚠ ARITHMETIC CROSS-CHECK.** At `P = {p | AniForm p}` (`#P = q(q−1)/2`, G.38) this is
`((q−1)/2)·q^(2N−2k−1)` — **G.41's value, in both residue characteristics**, matching §A-1's
two-column table (char ≠ 2: `(q−1)/2` orbits × `q^(2N−2k−1)`; char 2: `q−1` orbits ×
`q^(2N−2k−1)/2`). The refuted G.23a would have given `q^(2N−2k−2)` per pair and `q²−q` pairs,
i.e. a factor `q` too small per pair and a factor `q` (resp. `q/2`) over-counted in the union;
this node has neither error because it never counts a single pair.

**SOURCE.** `EFF.W11.09` (INERTDEEP/2SIDED/SPLIT rows), `EFF.W11.16` (the residual census),
`EFF.W11.07`; §A-1's replacement-route display.

**TEETH.** `W11-CENSUS` / P-2 (the residual-census rows on 30 census rows) → **Lean theorem**.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R10 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *G.21's computation rule, and `resClassSet` in `residualPair` coordinates.*
Whenever the value and derivative factor explicitly, `residualPair h0 h1 = (b̄₀, b̄₁)`; hence
`resClassSet` may be read either way.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem residualPair_eq (hπ : Irreducible π) {k : ℕ} {a : Fin 2 → O} {γ b₀ b₁ : O}
    (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ)
    (e0 : qval a γ = π ^ (2 * k) * b₀) (e1 : qder a γ = π ^ k * b₁) :
    residualPair h0 h1 = (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁)

theorem mem_resClassSet_iff_residualPair (hπ : Irreducible π) {P} {k N : ℕ} {c : Coeff O 2 N} :
    c ∈ resClassSet π P k N
      ↔ ∃ (a : Fin 2 → O) (γ : O) (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ),
          proj O 2 N a = c ∧ residualPair h0 h1 ∈ P
```

**DEPENDS.** G.21, G.23R4.

**PROOF.** `h0.choose_spec` and `e0` give `π^(2k)·h0.choose = π^(2k)·b₀`; cancel `π^(2k)`
(`mul_left_cancel₀`, `π ≠ 0`), so the `Classical.choose` witness **is** `b₀` — an equality in `O`,
not merely mod `𝔪`. Same at `k`. The membership equivalence is then bookkeeping.

**SIZE.** 25 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R10.lean`. This discharges the
"export the two computation rules" instruction of G.21's PROOF note.

**SOURCE.** G.21's declared SIGNATURE defect and its repair instruction.

**TEETH.** none of its own.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R11 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *A double-root-free residual class sits in the stratum of depth EXACTLY `2k`.* If
no member of `P` is a `DblPair`, then `resClassSet π P k N ⊆ depthSet π N (2k)` for `2k+1 ≤ N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem resClassSet_subset_depthSet (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : ∀ p ∈ P, ¬ DblPair p) {k N : ℕ} (hN : 2 * k + 1 ≤ N) :
    resClassSet π P k N ⊆ depthSet π N (2 * k)
```

**DEPENDS.** G.11, G.12, G.19, G.23R3, G.23R4 · landed `Tang_mono`, `qval_shift`, `qder_shift`,
`mem_maximalIdeal_iff_dvd`.

**PROOF.**
1. `c ∈ tangSet π N (2k)` is immediate from the witnessing `(a, γ)`.
2. suppose `c ∈ tangSet π N (2k+1)`, witnessed by `(a', γ')`; G.12 transfers to the lift `a`.
3. G.11 puts `γ'` in `γ`'s coset mod `π^k`: `γ' = γ + π^k·d`.
4. `qval a γ' = π^(2k)·(b₀+b₁d+d²)` and `qder a γ' = π^k·(b₁+2d)`; the depth-`(2k+1)`
   divisibilities cancel `π^(2k)`, `π^k` and give `b̄₀ + b̄₁d̄ + d̄² = 0`, `b̄₁ + 2d̄ = 0`.
5. hence `b̄₁ = −2d̄` and `b̄₀ = d̄²`, i.e. the pair is `((−d̄)(−d̄), (−d̄)+(−d̄))` — a `DblPair`,
   excluded. (This is §A-1's observation that the *only* pair readable at depth `≥ 2k+1` is a
   double-root pair, made precise at an arbitrary centre.)

**SIZE.** 40 lines. **LANDED** `leanfinal/Uniformity/ChapG/G23R11.lean`.

**SOURCE.** §A-1 ("`(0,0)` — the only pair that could be read at depth `≥ 2k+1` — is a
double-root pair"), corrected for the centre translation.

**TEETH.** none of its own; supplier for G.41/G.42.

**ENVIRONMENT.** ENV-A'.

---

### NODE G.23R12 [lemma] [fresh, added by AMENDMENT §A-8]

**STATEMENT.** *The two `O ↔ K` bridges.* The `O`-level `Anisotropic ![b₀, b₁]` is exactly
`AniForm` of the residual pair; and `SepPair` of the residual pair is exactly the existence of a
simple residual root, i.e. G.28's hypothesis pair. Both characteristic-free.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Menu

theorem residue_eq_zero_iff_dvd (hπ : Irreducible π) (x : O) :
    IsLocalRing.residue O x = 0 ↔ π ∣ x

theorem aniso_iff_aniForm (hπ : Irreducible π) (b₀ b₁ : O) :
    Anisotropic ![b₀, b₁] ↔ AniForm (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁)

theorem sepPair_iff_exists_simple_root (hπ : Irreducible π) (b₀ b₁ : O) :
    SepPair (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁)
      ↔ ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) ∧ ¬ π ∣ (b₁ + 2 * z)
```

**DEPENDS.** G.39 · landed `Anisotropic`, `quadForm` (`QuadCert.lean:336,340`), `AniForm`,
`aniForm_iff` (`AnisotropicForms.lean:55,59`), `mem_maximalIdeal_iff_dvd`, `not_dvd_of_isUnit`.

**PROOF.**
1. `aniso_iff_aniForm` (→): a residual root `ȳ` lifted to `u` makes `quadForm ![b₀,b₁] u 1 ∈ 𝔪`,
   so anisotropy would force `1 ∈ 𝔪`. (←) is `exists_anisotropic`'s inner argument via
   `aniForm_iff`.
2. `sepPair_iff_exists_simple_root` (→): with `p = (uv, u+v)`, lift `−u` to `z`; then
   `z²+b₁z+b₀ ↦ u² − (u+v)u + uv = 0` and `b₁+2z ↦ v−u ≠ 0`. (←): from `ζ²+β₁ζ+β₀ = 0` and
   `β₁+2ζ ≠ 0`, take `u := −ζ`, `v := β₁+ζ`; then `uv = β₀`, `u+v = β₁` and `u ≠ v`.

**⚠ SIGN CONVENTION (read before consuming).** `AniForm`/`SepPair` key on `X² − b₁X + b₀`, while
`qval`/`qder` read the residual quadratic `R(y) = y² + b₁y + b₀`. The two differ by `y ↦ −y`,
which changes neither predicate; every landed statement above is in the `AniForm` convention on
the left and the `qval` convention on the right, and the bridge absorbs the flip.

**SIZE.** 40 lines (3 signed declarations). **LANDED**
`leanfinal/Uniformity/ChapG/G23R12.lean`.

**SOURCE.** `EFF.W11.16` (the row predicates); G.26/G.27/G.28's `O`-level phrasing.

**TEETH.** `HEX3-CHAR` (`EFF.HEX3.49`: the loci differ across characteristics, the counts do not)
→ **Lean theorem**, in the sense that the bridge is stated with no characteristic hypothesis.

**ENVIRONMENT.** ENV-A'.

---

### A-8.1 — how G.41 and G.42 assemble (for the wave that owns them; NOT landed here)

Both are `card_resClassSet` + one set identity + G.38/G.39. **The arithmetic leg was
machine-checked at this append** (scratch `example`, not landed): given
`inertStratum π (2k+1+r) k = resClassSet π {p | AniForm p} k (2k+1+r)`, the chain

```
2·#inertStratum + q^(2k+2r+1)
  = (2·#{p | AniForm p} + q)·q^(2k+2r)        -- card_resClassSet + pow_succ
  = (q·q)·q^(2k+2r)                            -- G.38 two_mul_card_aniForm
  = q^(2k+2r+2)
```

type-checks verbatim, `Nat.card ↥{p | AniForm p}` unifying definitionally with G.38's
`Nat.card {p // AniForm p}`. G.42 is the same with `SepPair` and G.39.

The remaining obligation is the **set identity**, whose two halves are both supplied:

* `⊇`: `resClassSet {p | AniForm p} ⊆ depthSet π N (2k)` by G.23R11 with
  `aniForm_not_dblPair` (G.23R3), and `DecidedAt … inertType` by G.27 `decidedAt_inert_of_ani`
  fed through `aniso_iff_aniForm` (G.23R12); the window hypothesis `2k+1 ≤ N` is exactly §A-2's
  amended one, available at `r = 0`.
* `⊆`: a class of depth exactly `2k` has a witnessing centre; G.26 `depth_even_dichotomy` splits
  anisotropic (done) from a simple residual root, and the latter is `splitType`-decided by G.28,
  contradicting inert-decidedness through the landed `decidedSet_disjoint`.
* for G.42 replace `AniForm`/G.27/`aniso_iff_aniForm` by `SepPair`/G.28/
  `sepPair_iff_exists_simple_root` and run the same two halves.

**G.41's `⚠ RE-DERIVATION TARGET` note stands unchanged**: `leancheck`'s `card_inertSet` is the
same statement by a different route, and remains a sanctioned fallback. It is no longer needed as
a rescue — the filtration route now has a complete supply line — but it is still the decorrelated
check, and §A-4's rider 2 (G.47 must record BOTH routes) is untouched.

---

### Amendment bookkeeping (fourth append)

| item | obstruction | verdict | nodes touched | files changed |
|---|---|---|---|---|
| A-8 | §A-1's replacement route existed only as prose; G.41–G.51 gated | **route expanded and LANDED** as 12 nodes / 25 declarations, no step resisted | **G.23R1–G.23R12 NEW**; G.23's banner gains a pointer; G.41/G.42 keep their statements and gain a complete supply line | `leanfinal/…/ChapG/G23R{1..12}.lean` (12 new), `leanfinal/…/ChapG.lean`, `leanspec/Leanspec/ChapG.lean` |

Declaration census: **135** (110 + 25). Contract count in `leanspec/Leanspec/ChapG.lean` rises to
135 accordingly, with all 25 signed **and immediately retired** to the
`example := <landed name>` form (they land in the same unit that signs them).

**G.23's standing BLOCK is now scoped, not cleared.** `card_resStratum` (G.23a) remains
**REFUTED and withdrawn** — nothing here revives it — and `depthSet_eq_iUnion_resStratum` (G.23b)
remains **unlanded** (true as stated, union not disjoint; no consumer needs it now that the route
does not go through per-pair strata). What is cleared is the *consequence* of the block: G.41 and
G.42 are no longer waiting on G.23.

**Verification performed for this append.** `leanfinal` builds green (8657 jobs) and
`sorry`-free with all twelve modules wired into the `Uniformity.ChapG` roll-up; every one of the
25 declarations reports `[propext, Classical.choice, Quot.sound]` (Lean core only; `transPair`
and `TransInvariant` report `[propext]` alone). `leanspec` builds green with all 25 retired to
the `example := <landed name>` form, which machine-checks that the landed types are the signed
ones. No new axiom, no `sorry`, no statement of any pre-existing node changed.

---

## AMENDMENT 2026-08-15 (fifth dated append; Opus arm, the CLOSING TAIL) — §A-9: **CHAPTER G CLOSED**

This append lands the chapter's remaining nodes — the `n = 2` count layer G.41–G.44, the exact
density chain G.46–G.49/G.51, the `n = 3` lower-bound node G.61 with its infrastructure, and the
two gates G.77/G.78 — and then closes the chapter with a census. As with every append,
**nothing in §§0–14 or in §§A-1…A-8 is edited in place**; the banners prescribed below belong on
the affected node entries.

### A-9.1 — G.44a's ram index set: **DEFECT. `Finset.range ((N+1)/2)` is FALSE at odd `N`; the
genuine index is `Finset.range (N/2)`.**

**Banner for the node entry:** `G.44 [SIGNATURE AMENDED 2026-08-15 — see AMENDMENT §A-9.1;
G.44b (inert) unchanged]`.

The signed ram statement is

```lean
decidedSeq O 2 ramType N = ∑ j ∈ Finset.range ((N + 1) / 2), (q - 1) / q ^ (2 * j + 2)
```

**It fails at every odd `N`, first at `N = 1`.** Two independent derivations of the failure, with
disjoint inputs:

*Leg 1 (structural; machine-checked at this append).* `decidedSet_ram_eq` (G.31) writes the
ram-decided set as `⋃ j ∈ Finset.range N, depthSet π N (2*j+1)`. At `N = 1` the only index is
`j = 0` and `depthSet π 1 1 = ∅` by G.30a (`depthSet_odd_eq_empty`, hypothesis `N ≤ 2*j+1`, here
`1 ≤ 1`). So `decidedCount O 2 ramType 1 = 0` and `decidedSeq O 2 ramType 1 = 0`, while the signed
right-hand side is `∑ j ∈ Finset.range 1, (q-1)/q^2 = (q-1)/q^2`, which is `> 0` because
`q ≥ 2` (`two_le_residueCard`). Contradiction.

*Leg 2 (arithmetic; independent of G.30a and of the depth filtration's emptiness lemmas).* At
`N = 1` the level-1 census closes exactly: the landed G.36 gives `undecidedCount O 2 1 = q`, and
G.41/G.42 at `k = 0, r = 0` give `2·#inertStratum + q = q²`, i.e.
`#inertStratum = #splitStratum = (q²−q)/2`. The `q²` level-1 classes are partitioned into the
three decided sets and the undecided set, so
`(q²−q)/2 + (q²−q)/2 + #ramDecided + q = q²`, forcing `#ramDecided = 0` — again `0 ≠ (q−1)/q²`.
(The same closure at `N = 2` reads `(q⁴−q³)/2 + (q⁴−q³)/2 + (q³−q²) + q² = q⁴` ✓, and there the
two index conventions agree, which is why the defect is invisible at even `N`.)

**The correction.** The genuine ram index set is `{j | 2*j+2 ≤ N}` — the hypothesis
`decidedAt_ram_of_depth_odd` (G.25) actually requires, and the range on which `card_depthSet`
(G.20) returns a nonzero count — and `{j | 2*j+2 ≤ N} = Finset.range (N/2)` (`omega`). The inert
index set `{k | 2*k+1 ≤ N} = Finset.range ((N+1)/2)` is **CORRECT as signed**, so G.44b is
untouched: the two halves genuinely have different index sets, and the blueprint's error was to
reuse one expression for both.

**Nothing downstream changes.** G.46 consumes G.44a only through G.45's limit, and
`N/2 → ∞` exactly as `(N+1)/2 → ∞`; the limit `(q−1)/q² · q²/(q²−1) = 1/(q+1)` is unaffected.
G.47, G.48, G.49 and G.51 are downstream of the limit only.

---

### A-9.2 — G.61's MANDATORY NUMERIC CONSISTENCY CHECK: **RE-RUN, ALL TEN INEQUALITIES HOLD, and
the tightest has a 0.41% margin**

The G.61 node entry asks a cross-reader to re-run its bound-versus-target table, on the ground that
"a bound exceeding its target would be a genuine contradiction (`decidedDensity ≤ genuineDensity`
is landed), and it is the cheapest available falsifier of either the bounds or the transcribed
targets". Re-run at this append in exact rationals, independently of the blueprint's own arithmetic:

| `q` | | split | linInert | inert | linRam | ram | Σ targets |
|---|---|---|---|---|---|---|---|
| 2 | target | `4/93` | `28/93` | `8/31` | `22/93` | `5/31` | **`1`** ✓ |
| 2 | bound | `1/512` | `1/4` | `1/4` | `1/16` | `1/16` | |
| 2 | slack | 95.5% | 17.0% | **3.1%** | 73.6% | 61.3% | |
| 3 | target | `63/968` | `351/968` | `36/121` | `93/484` | `10/121` | **`1`** ✓ |
| 3 | bound | `1/19683` | `1/3` | `8/27` | `4/81` | `2/81` | |
| 3 | slack | 99.9% | 8.1% | **0.41%** | 74.3% | 70.1% | |

All ten inequalities hold, and the five HM3.D targets sum to exactly `1` at both primes — which is
an independent check on the transcription of `R_τ` and of `Φ = q⁴+q³+q²+q+1`, since a slip in any
one closed form would almost surely break the sum.

**The check has real force at one entry.** The inert bound at `q = 3` is `8/27 = 0.296296…` against
the target `36/121 = 0.297520…`: cross-multiplying, `8·121 = 968 < 972 = 36·27`, a margin of
`4/3267 ≈ 0.41%`. A single transcription slip in either the level-1 `NoRootCubic` census
(`(q³−q)/(3q³)`) or in HM3.D's `q³(q+1)/(3Φ)` would have flipped that inequality and produced a
visible contradiction with the landed `decidedDensity ≤ genuineDensity`. It did not. This is the
strongest available corroboration that G.60's residue-field cubic census and HMENU3's transcribed
cubic densities are the same mathematics read two ways.

