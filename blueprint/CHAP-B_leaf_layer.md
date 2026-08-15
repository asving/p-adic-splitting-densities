# CHAPTER B — THE LEAF / ORDER-1 LAYER

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **B = HENSEL-SLOT CORE**
(notes `HE3`, `HE6`, `HE6R1`, `HE7`; 319 DAG nodes; consumer-first order position fifth,
`E > D > C > B > H`).
**Scope (the charge):** the polygon + residual-factorization **LEAF THEOREM at general `O`** — the
corpus's Ore/GMN citation, resolved to **[GN15] Thm 2.3** scope by
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` rows NS-1, NS-2, NS-6. In Lean nothing is cited: every
consumed leaf fact is a node or an explicit hypothesis.
**Sources transcribed:** `spec/EFF-HE6.md` (62 units; T2's nine pin anchors `.09 .13 .14 .15 .17
.29 .30 .32 .56` are this chapter's unit map), `spec/EFF-HE3.md` (72 units; the level-1 recursion
base), `spec/EFF-W12.md` (88 units, contiguous merged namespace; the order-1 digit calculus and the
leaf-certification units `.08 .23 .24 .25 .27 .51 .83`–`.87`). `EFF-HE6R1.md` and `EFF-HE7.md` are
**not** transcribed here — see H-3 and H-4.
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle).
**Authored:** 2026-08-15, Opus arm. **CODEX CROSS-READ OWED** (§14).

---

## 0. How to read this chapter

### 0.1 The four standing environments

Every node names its environment as `ENV-A`, `ENV-A'`, `ENV-B`, `ENV-C` or `ENV-D` plus deltas.

**ENV-A — the polynomial arena (default).** No completeness, no finiteness. Most of the
development/polygon machinery lives here and it is worth keeping it here: a node that does not need
Hensel must not bind `IsAdicComplete`, and a node that does not count must not bind
`Finite (ResidueField O)`.

```lean
import Uniformity
namespace Uniformity.Density.Leaf
open IsLocalRing Polynomial
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
```

**ENV-A'** — ENV-A with `π` promoted to an explicit hypothesis `(hπ : Irreducible π)`. This is how
every node that names `π` actually takes it; the landed precedent is
`Drainage.lean:85`, `StrongHensel.lean:244`, `DensityAPI.lean:124`.

**ENV-B** — ENV-A plus completeness (every node that lifts through Hensel):

```lean
variable [IsAdicComplete (maximalIdeal O) O]
```

**ENV-C** — ENV-B plus finiteness of the residue field:

```lean
variable [Finite (ResidueField O)]
```

**⚠ ENV-C IS MANDATORY FOR EVERY NODE THAT NAMES `Res`, `Coeff`, `proj`, `residueCard`,
`DecidedAt`, `PossibleAt`, `decidedSet`, `typeOf`-density objects, OR THAT FACTORS A RESIDUAL
POLYNOMIAL.** Chapter G's stage-0e gate recorded defect **D4** — "ENV-A under-binds
`[Finite (ResidueField O)]`, systematic across 22 stubs". This chapter fixes that class of defect by
construction: the finiteness instance is bound in exactly one environment block, and §2's index
records the environment of every node so the stub-landing agent can check the binding mechanically.
`Uniformity.Density.Res` (`LocalData.lean:75`) is declared inside a
`variable (O) … [Finite (ResidueField O)]` section, so a stub that mentions `Res O N` without that
instance does not elaborate.

**ENV-D — the residue arena** (pure residue-field algebra, no `O` at all):

```lean
import Uniformity
namespace Uniformity.Density.Leaf
open Polynomial
variable {F : Type*} [Field F]
```

with `[Finite F]` added only where a node counts or uses perfectness/separability of a finite field.

### 0.2 File layout and naming

* One Lean file per node: `leanfinal/Uniformity/ChapB/B<nn>.lean`, module `Uniformity.ChapB.B<nn>`
  (the landed chapter-G convention, `leanfinal/Uniformity/ChapG/G05.lean`).
* Chapter roll-up `leanfinal/Uniformity/ChapB.lean` imports all node modules in topological order;
  `Uniformity.lean` gains one line `import Uniformity.ChapB`.
* **Namespaces are the landed ones.** New *definitions* of this chapter live in the sub-namespace
  `Uniformity.Density.Leaf` (mirroring chapter G's `Uniformity.Density.Menu`); new *theorems about
  landed objects* (`typeOf`, `inertiaDegOf`, `DecidedAt`, `Hensel.*`) live directly in
  `Uniformity.Density` or `Uniformity.Hensel`, whichever already owns the object.
* One PUBLIC declaration per node (the contract declaration named in its SIGNATURE); private
  helpers may live below it in the same file. A helper that is reusable triggers a RE-PLAN request
  to the orchestrator, never a silent second public name.

### 0.3 Names that already exist and must not be redefined

Consumed by name, never re-proved. `Uniformity.Density`: `FactorizationType`,
`FactorizationType.degree`, `FactorizationType.ext`, `FactorizationType.degree_mk_add`, `typeOf`,
`typeOf_data`, `typeOf_degree`, `typeOf_of_natDegree_one`, `monicFactors`, `monicFactors_spec`,
`monicFactors_eq`, `monicFactorization_exists`, `monicFactorization_unique`, `IsMonicFactorization`,
`monicFactors_mul`, `typeOf_mul`, `typeOf_prod_X_sub_C`, `typeOf_of_residual_coprime`,
`typeOf_eisenstein`, `typeOf_inert_of_irreducible_map`, `natDegree_dvd_addVal_norm`,
`isMaximal_map_maximalIdeal_adjoinRoot`, `isUnit_of_notMem_map_maximalIdeal`,
`minpoly_adjoinRoot_root`, `norm_adjoinRoot_root`, `norm_algebraMap_rootBasis`, `rootBasis`,
`normValues`, `normDivisors`, `inertiaDegOf`, `ramIndexOf`, `efPair`, `one_mem_normDivisors`,
`normDivisors_bddAbove`, `inertiaDegOf_mem_normDivisors`, `inertiaDegOf_pos`, `inertiaDegOf_dvd`,
`le_inertiaDegOf`, `inertiaDegOf_eq_of`, `inertiaDegOf_eq_one_of_coprime`,
`natDegree_mem_normValues`, `normValues_nonempty`, `inertiaDegOf_dvd_natDegree`,
`ramIndexOf_mul_inertiaDegOf`, `inertiaDegOf_of_algEquiv`, `normValues_of_algEquiv`,
`normDivisors_of_algEquiv`, `efPair_shift`, `typeOf_shift`, `efPair_scaleRoots`,
`inertiaDegOf_scaleRoots`, `typeOf_scaleRoots`, `typeOf_scale`, `eq_scaleRoots_of_comp`,
`monicFactors_scaleRoots`, `irreducible_scaleRoots_iff`, `scaleHom`, `norm_scaleHom`,
`efPair_pos_of_mem`, `efPair_mul_le_natDegree`, `natDegree_pos_of_mem_monicFactors`,
`exists_monic_scaleRoots`, `exists_monic_scaleRoots_typeOf`, `dvd_sub_coeff_of_scaleRoots`,
`monicPoly`, `monicPoly_monic`, `monicPoly_natDegree`, `monicPoly_degree`, `monicPoly_coeff_lt`,
`exists_monicPoly_eq`, `Res`, `Coeff`, `proj`, `proj_surjective`, `resFactor`,
`resFactor_surjective`, `coeffFactor`, `coeffFactor_proj`, `card_res`, `card_coeff`, `residueCard`,
`two_le_residueCard`, `DecidedAt`, `PossibleAt`, `decidedSet`, `possibleSet`, `decidedCount`,
`UndecidedAt`, `CoveringMenu`, `exists_coveringMenu`, `decidedAt_of_congr`, `proj_eq_iff_dvd`,
`decidedDensity_ge_of_subset`, `genuineDensity_le_of_superset`, `towerSection`, `card_certSet_gen`,
`UniformityStatement`, `DrainageAt`. `Uniformity.Hensel`: `coeffIdeal`, `mem_coeffIdeal`,
`coeffIdeal_mono`, `C_mem_coeffIdeal`, `mul_mem_coeffIdeal_mul`, `map_mk_eq_zero_iff`,
`map_residue_eq_zero_iff`, `sub_mem_coeffIdeal_maximalIdeal_iff`, `exists_solve_field`,
`exists_solve_mod`, `exists_solve_step`, `exists_adicLimit_of_degree_lt`, `exists_monic_lift`,
`natDegree_eq_of_map_eq`, `degree_sub_lt_of_monic_of_natDegree_eq`, `exists_monic_factorization`,
`exists_monic_factorization_dvr`, `exists_monic_factorization_finset`,
`exists_eq_add_mul_of_degree_lt`, `isCoprime_of_map_eq`, `monic_factorization_unique`,
`exists_linear_factorization`, `eq_sum_range_of_degree_lt`,
`degree_sum_range_C_mul_X_pow_lt`, `coeff_sum_range_C_mul_X_pow`, `newton_step`,
`exists_root_of_strongHensel`, `root_unique_of_strongHensel`, `strongHensel`,
`strongHensel_addVal`, `maximalIdeal_pow_eq_span`, `exists_unit_mul_pow_of_addVal_eq`,
`pow_dvd_iff_le_addVal`, `isUnit_add_of_mem_maximalIdeal`.

### 0.4 The chapter's mathematical spine, in one page

Fix the standing bundle `O` (complete DVR, uniformizer `π`, residue field `F` with `q = #F`), a
monic `φ ∈ O[X]` of degree `m` whose reduction `φ̄` is **irreducible** over `F`, and a monic
`f ∈ O[X]` with `f̄ = φ̄^μ`. The chapter formalises, at general `O` and in both characteristics:

| step | content | nodes |
|---|---|---|
| the development | `f = Σ_j a_j φ^j`, `deg a_j < m`, unique | B.02–B.06 |
| the heights | `H j := gaussVal (a_j)`, a total `ℕ∞`-valued function | B.07–B.10 |
| the polygon | the **cleared support function** `S(u,ℓ) := inf_j (ℓ·H j + u·j)`; sides, slopes, lengths as argmin data | **B.11–B.20 (DECISION D-1)** |
| the residual field | `Fφ = F[y]/(φ̄)`, finite, `[Fφ:F] = m`, `#Fφ = q^m` | B.21–B.24 |
| the residual polynomial | `R_{u,ℓ}(f) ∈ Fφ[Y]`, degree `d`, `R(0) ≠ 0` | B.25–B.30 |
| the product law | `S(u,ℓ)` additive and `R_{u,ℓ}` multiplicative on products | B.31–B.36 |
| the two dissections | distinct slopes split; distinct residual factors split | B.37–B.48 |
| the `(e,f)` read | a multiplicity-1 residual factor `ψ` of degree `d` on a side of slope `−u/ℓ` (lowest terms) gives ONE factor of degree `ℓ·m·d` with `typeOf = ⟨{(ℓ, m·d)}⟩` | B.49–B.62 |
| NS-6 | descent stops at order 1 iff every residual is separable | B.63–B.66 |
| `typeOf` transport | order-0 peel, the order-0 leaf law, the development-to-`typeOf` bridge | B.67–B.74 |
| decidedness | level-`N` certificates: the visible polygon + residual pins `typeOf` | B.75–B.82 |
| gates | `q = 2` and `q = 3` firing instances with `e > 1` **and** `f > 1` | B.83–B.86 |

**The one identity the whole chapter turns on.** `EFF.HE3.31`'s byte-frozen display `(★)`,
consumer-pinned by HE6 and HE7:

```
h_F(κ) = min_j (dv(A_j) + j·κ) = Σ_{slopes λ} L_λ · min(λ, κ).
```

Cleared of denominators (`κ = u/ℓ`, `dv = addVal`, `ℓ·h_F(u/ℓ) = S(u,ℓ)`) this is a statement about
an `inf` of `ℕ`-linear forms over a `Finset` — no rational arithmetic, no hull construction, no
convex-duality import. Everything in §§3–6 is a consequence of that one object's two properties:
it is **additive on products** (B.32) and its **argmin set is `ℓ`-spaced** (B.17).

**The `(e,f)` argument in four lines** (`EFF.HE3.26` + `EFF.HE3.34` + `EFF.HE6.32`, transposed to
`leanfinal`'s `typeOf`). Let `g` be the factor cut out by the pair `(slope −u/ℓ, residual factor ψ)`
with `ord_ψ R = 1`, `deg g = ℓ·m·d`. For **every** `(e', f') ∈ (typeOf g).data`: `m·d ∣ f'`
(B.55) and `ℓ ∣ e'` (B.57), so `e'·f' ≥ ℓ·m·d = deg g`. Landed `typeOf_degree` says
`Σ e'f' = deg g` and landed `efPair_pos_of_mem` says every `e'f' ≥ 1`; a multiset of positive
integers each `≥ n` summing to `n > 0` is a singleton `{n}`. Hence `typeOf g = ⟨{(ℓ, m·d)}⟩`
(B.58). **No irreducibility proof, no Galois orbit count, no class-size count `|S_{λ,r}| = D′ℓ·deg r`
is needed** — that count (`EFF.HE6.18`, THEOREM HE6.A) is the corpus's route through resultants and
the valuation on `K̄₀`; §7 replaces it with the divisibility-plus-degree route, which is why this
chapter needs no algebraic closure. The divergence is flagged for the cross-read (§14 item 2).

---

## 1. HONESTY BLOCK (read before consuming any node)

**H-1 — this chapter is the `e₁ = 1` slice of HE6's frame, and that is a genuine scope cut.**
`EFF.HE6.08` fixes `Φ′` monic irreducible of degree `D′ = e₁f₁` whose **roots have valuation
`h/e₁`**, and works with `dv := e₁·v`, the normalizer `ϖ := x^{i₀}π^{a₀}` (`EFF.HE6.11`, which is in
`K₀[x]` and **not** in `O[x]` because `a₀` may be negative), the residue `η_θ` and the twist
`η_θ^{−q(k)}` (`EFF.HE6.13` RIDER). Chapter B is the case **`e₁ = 1`, `h = 0`, `D′ = f₁ = m`**: `φ`
is a lift of an irreducible residual factor, i.e. an **order-0 key**. In that case `dv = addVal`,
`ϖ = π`, `i₀ = 0`, `q(k) = 0` and **the twist is identically trivial** — which is why §§3–6 contain
no `η`, no `ϖ`, and no `ι_ξ`. The `e₁ ≥ 2` frame, its `ϖ`-normalizer bookkeeping and the level-2
cocycle `c₁(a,b) = (s(a)+s(b)−s(a+b))/ℓ` are the **tower** chapters' business (chapter C:
`GENTOW1/3/4/5/6`, `HETOW`) and are deliberately NOT transcribed here. Corroboration that the twist
really is a positive-`e₁`/level-2 phenomenon: `EFF.HE6R1.29`'s tooth `HE6R1-T-TWIST0` measured
"level-2 twist exponents all zero at `ℓ = 1`", 1,276 exponents. **A fleet agent who finds itself
needing `η_θ`, `ϖ` or `ι_ξ` has left the chapter and must return `BLOCKED: out-of-scope (H-1)`.**

**H-2 — `THEOREM HE6.A`'s class-size count is NOT a node of this chapter.** `EFF.HE6.18`
(`|S_{λ,r}| = D′ℓ·deg r`, base-change-free) and its four-step sandwich proof `EFF.HE6.32` rest on
the resultant account `(RES)` of `EFF.HE6.30`, the enlarged test family `Ψ_{κ,r}` at *fractional*
`dv`-height (`EFF.HE6.14`), the disk criterion `EFF.HE6.16`, Galois equivariance `EFF.HE6.31`, and
therefore on the valuation `v` extended to a **fixed algebraic closure `K̄₀`** with its Galois
invariance (`EFF.HE6.06`, imported classically). None of that is available in `leanfinal` and none of
it is quarriable (see H-6). §7 reaches the same `(e,f)` conclusion by the divisibility-plus-degree
route of §0.4. **Consequence:** this chapter proves *what the leaf's `typeOf` is*, and does **not**
prove *how many roots carry a given label*. Any downstream consumer that needs the class size (the
tower's block-length prediction) must get it from chapter C, not here.

**H-3 — `HE6R1` and `HE7` are in the chapter cut but not in this file.** The 0c cut assigns
`HE3, HE6, HE6R1, HE7` to chapter B. `EFF-HE6R1.md` is the **level-2** reconciliation (its own
`.06`/`.18` fix the level-2 frame `dv₂, T₂, n₂, s(·)`, `D″ = D′ℓd_r`, `K₂ = K(β)`, `μ₂`), and
`EFF-HE7.md` is the σ-ladder's level-2 machinery `(SLOT₂)/(LIFT₂)`. Both are **one order up** from
this chapter and both are consumed by the tower, so they are left to chapter C together with H-1's
twist layer. Booked, not done. Two named items of theirs that a chapter-B reader will meet and must
not confuse with a chapter-B obligation: `LEMMA HE6R1-1`'s jump condition `ℓ_i·deg r_i ≥ 2`
(`EFF.HE6R1.09`, re-displayed under owner directive at `.47`) is the *level-jump* trigger, whereas
this chapter's NS-6 node B.63 is the *order-1 stopping* criterion; and `LEMMA HE6R1-3`
(`EFF.HE6R1.15`) is the level-2 peel `Ψ ∣ f_S`, not this chapter's order-0 peel B.67.

**H-4 — `HE3` is graded 1/2 and is NOT accepted; `HE6` is ACCEPTED 2/2 and FROZEN.**
`EFF.HE3.64` records HE3's grade as **TERMINAL 1/2** (one clean pass, not the two consecutive clean
passes acceptance requires), and five further REAL findings (`R8-1`…`R8-5`, `EFF.HE3.67`–`.71`)
postdate its clean pass and are awaiting discharge-confirmation. `EFF.HE6.54` records HE6 as
ACCEPTED 2/2 FROZEN. Where the two notes give the same mathematics this chapter transcribes **HE6's
statement and HE3's arithmetic**, and every SOURCE field says which. No node of this chapter cites
HE3 as an accepted note, and no node's PROOF rests on a passage that `R8-1`…`R8-5` corrected unless
the corrected text is the one transcribed (B.75 and B.79 transcribe `R8-1`'s *rewritten* recursive
certificate, `EFF.HE3.67`, never the superseded `LEMMA HE3-5` display of `EFF.HE3.37`).

**H-5 — `HE3-BOX-6` (ledger `HYP.143`) is disclosed, is NOT this chapter's blocker, and is NOT
silently inherited.** `EFF.HE3.44` names it "THE ONE SURVIVING GAP": at a side with `ℓ ≥ 2` and
residual degree `d ≥ 2`, "no element of `R` has non-integer `dv` … so NO test key of the form
`Φ′ + w`, `w ∈ R`, can sit at such a side's height", and the substitute ramified base change
`O ↝ O[Π]/(Π^ℓ − π)` is "stated too cheaply: **`Φ′` need not remain irreducible over `O₂`**". It is
scoped to `D′ ≥ 2 ∧ μ ≥ 4`, i.e. `n ≥ 8`. Two of its branches were closed inside HE3 —
`EFF.HE3.68` (`LEMMA HE3-4U`, the unramified branch) and `EFF.HE3.69` (`LEMMA HE3-4D1`, the `D′ = 1`
case, "unconditional at every `μ`") — and `EFF.HE6.35` records that HE6.A **supersedes** both
remaining branches rather than repairing them. **This chapter's route is immune to the obstruction
by construction**, because it never builds a test key and never performs a base change: the
divisibility-plus-degree argument of §0.4 needs no element of any ring at a fractional height. That
immunity is a *claim about the route*, and it is §14 item 1 — the single most important thing for the
cross-read to attack. What the chapter does inherit is disclosed at H-7.

**H-6 — nothing in this chapter is `quarry:`, and that is a survey result, not an omission.** A
four-way search (our pinned mathlib `v4.31.0`, `vendor/LocalClassFieldTheory`, `vendor/FLT`,
`vendor/norm_extensions`, `vendor/local_fields_journal`) found **no Newton-polygon API, no
MacLane/Vaquié key-polynomial machinery and no Okutsu–Montes material anywhere**
(`docs/VENDOR_QUARRY_MAP_2026-08-15.md` §2.1; independently confirmed for mathlib: zero hits for
`newtonpolygon`/`newton_polygon` in the pin). `lean/LeanUrat/OM/` **does** carry a proved polygon
layer — `NewtonPolygon.lean` (828 lines, 60 declarations, imports `Mathlib` only), plus
`Order0Hull.lean` (19), `ResidualPolynomial.lean` (19), `HullStability.lean` (39),
`PadicValuation.lean` (7): a flat 5-module, 144-declaration closure with no further OM dependency —
and a copy is **rejected on the merits** by DECISION D-1 below, not on cost. The two vendor Lean-4
repos are additionally on incompatible mathlib pins (LocalClassFieldTheory 9 minor releases behind,
FLT 3 ahead with a confirmed breaking rename: FLT uses the post-migration
`(IsLocalRing.maximalIdeal S).ramificationIdx R`, our pin is mid-migration and still carries
`Ideal.ramificationIdx` alongside `Ideal.ramificationIdx'`), and the LocalClassFieldTheory files a
leaf theorem would want are themselves `sorry`-ridden (`DiscreteValuationRing/Ramification.lean`:
its single lemma is a `sorry`; `LocalField/GaloisConnection.lean`: 27; `LocalField/Basic.lean`: 40;
`DiscreteValuationRing/Extensions.lean`: 12). **Every polygon/residual node below is `[fresh]`.**

**H-7 — the residue-degree LOWER bound at `d ≥ 2` is this chapter's one open box: `B-BOX-1`.**
The `(e,f)` argument needs `m·d ∣ f'` for every `(e', f') ∈ (typeOf g).data` (B.55). The chapter
proves it **unconditionally at `d = 1`** (B.53: `m ∣ inertiaDegOf` from the local structure of
`AdjoinRoot g`, whose residue field is exactly `Fφ`, by the strong induction of landed
`natDegree_dvd_addVal_norm`), and it proves the matching **upper** bound `inertiaDegOf g ∣ m·d`
unconditionally at every `d` (B.54, from landed `norm_adjoinRoot_root` and
`norm_algebraMap_rootBasis` applied to `φ(α)` and `π` plus `Nat.Coprime u ℓ`). At `d ≥ 2` the lower
bound needs the residual root to be realised in the residue field of the leaf, i.e. the order-1
analogue of `EFF.HE6.29`'s root label — and that is a statement about the valuation ring of
`K(α)`, not about `AdjoinRoot g`. **`B-BOX-1` is therefore stated as an explicit hypothesis on
B.55/B.58 and is not assumed anywhere else.** Its identified repair route (B.56, an OPTIONAL node
the orchestrator may or may not fire) is the mathlib spectral-norm layer: `spectralNorm_unique` /
`spectralNorm_unique_field_norm_ext`
(`Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:695,766`), `spectralNorm_eq_norm_coeff_zero_rpow`
(`:987`, which is `|x|_L = |N_{L/K}(x)|_K^{1/[L:K]}`), `spectralValue`+`norm_root_le_spectralValue`
(`:115,237`), and `IsKrasner`/`IsKrasner.of_completeSpace`
(`Mathlib/Analysis/Normed/Field/Krasner.lean:56,117`). **RISK, named:** that layer is
**multiplicative and ℝ-valued** while all of `leanfinal` is additive and `ℕ∞`-valued, so B.56 pays
for a norm-to-`addVal` bridge; it is sized opus-tier and is the chapter's largest single risk.
Related ledger rows, disclosed and NOT discharged here: `HYP.01` (`typeOf` faithfulness, class
`lean-open-statement`, disposition **NODE [CORE-SET]** — a human definitional audit, explicitly not
liftable by the Q4 policy) and `HYP.12` (the `(e,f)` ordering convention, same disposition).
`inertiaDegOf` is a gcd over the **order** `AdjoinRoot g`, not over the maximal order, and this
chapter never assumes the two agree.

**H-8 — what stays cited nowhere.** In Lean there are no citations. The three Ore/GMN facts the
corpus consumes by citation become nodes here, and this is the dictionary:

| corpus citation | corpus site | this chapter |
|---|---|---|
| Ore's theorem of the polygon, order 1 (GMN Thm 1.15) = NS-1 | `EFF.W12.09`, `.27`, `.46`; `EFF.HE3.03` | **B.42** (proved) |
| Ore's theorem of the residual polynomial + leaf dichotomy with explicit `(e,f)` (GMN Thm 1.19 + Cor 1.20) = NS-2 | `EFF.W12.27` verbatim ("classical, cited not re-proved"), `EFF.HE3.26`, `EFF.HE6.32` | **B.48** + **B.58** (proved; B.58 conditional on `B-BOX-1` at `d ≥ 2`) |
| the descent trigger (GMN Lemma 3.11(3)) = NS-6, ledger `HYP.14` | `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 + §3 F-1 | **B.63** (⇐) + **B.64** (⇒) |
| fact (I): the order-1 residual field is finite of degree `m` = NS-4 | `docs/GMN_citations.md` §0 | **B.22**, **B.23** |
| fact (II): the polygon is a lattice object = NS-5 ("a *definition*, not a theorem … the cheapest row in the whole table") | `docs/GMN_citations.md` §0 | **DECISION D-1** + B.11–B.20 |

`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` verdicts for NS-1/NS-2/NS-4/NS-5 are all
**COVERS-ALL-O**; NS-6's is **COVERS-ALL-O as a composite** with the note "**PARTIAL** if the corpus
wants a one-line cite of the biconditional", re-proof cost "~½ page, LOW risk" — B.63/B.64 are that
half-page. **NS-7 (termination, GMN Thm 4.18/Cor 4.19) is NOT a chapter-B node**: the resolution
doc's own verdict is that it is "the one row that is only PARTIAL", and it belongs with the tower's
descent bookkeeping.

**H-9 — the COARSE DAG edges this chapter refines, and the `W12` namespace hazard.**
`spec/DAG.tsv` carries chapter-B edges whose endpoints are governing-unit placeholders
(`resolution=…gov`); the node-level DEPENDS fields below are the first statement-level dependency
structure for this material. The chapter's DAG additions (§11) are *new* edges and retire no COARSE
row. **⚠ Hazard for the merge:** `spec/DAG_README.md` states that `W12` "exist[s] only as shard
pairs … with shard-local ID namespaces and no merge run", but `spec/EFF-W12.md` **is** a completed
merge (self-titled `(MERGED)`, compiled 2026-08-14 22:54, contiguous namespace `EFF.W12.01`–`.88`,
shard-2 offset `+52`) and it declares that it "supersedes the two shards as the citable unit for all
downstream consumption". The README is stale. This chapter cites the **contiguous** `EFF.W12.NN`
IDs; `dag_build.py` still harvests `EFF.W12.sKof2.NN`, so **every `EFF.W12.*` row this chapter adds
will read as a dangling ID until `dag_build.py` is re-run against the merge.** Mitigation applied in
§11: the chapter's W12 SOURCE edges are emitted against the **shard-local** IDs that exist in
`DAG_NODES.tsv` today, and the contiguous ID is carried in the `evidence` column so the remap is
mechanical. Booked as an orchestrator item; it is a change to a 0c artifact this chapter does not
own.

**H-10 — `LEMMA W12-HT` is NOT transcribed, and here is why that is the right call.**
`EFF.W12.83`–`.87` (the all-degree order-1 history transfer, `(HT-rec)`/`(HT-branch)`/`(HT-global)`)
is the note's own highest-value append and `EFF.W12.87` OPEN-CALL 6 discloses its status: "composed
by a model (gpt-5.6-sol) from a conjectured law, hand-verified by an orchestrator, machine-
corroborated only on grid `n∈{3,4}, q∈{2,3}, N≤6`", with no hostile-arc pass. It is nonetheless a
**count law** — `#T(N) = κ₀(T)C₀(q)∏…`, exponents `B_v(N)`, `D_v(N)`, orbit factors `κ_v`, censuses
`S_λ(Q)` — and counting level-`N` cells is chapters C/H's object, not this chapter's. What chapter B
owes `HT` is exactly its **step 5–6 content** (`EFF.W12.86`: "the recursion consequently terminates
… every terminal residual is separable … S2.3's order-1 Ore theorem then certifies, for every
disc-nonzero lift, one étale piece for each terminal side factor with its displayed `(e, f)`"), and
that is B.63 + B.58 + B.79. The three ingredients `HT` needs from here and will consume by name:
B.20 (`ℓ(N⁻)` and the on-side lattice-point count `L_v`), B.30 (`resPoly` degree `d` with
`R(0) ≠ 0`), B.58 (the `(e,f)` read). **The count layer must not be built on top of anything in this
chapter that H-7 leaves boxed:** `B-BOX-1` sits inside B.55/B.58, so an `HT` transcription at
`d ≥ 2` inherits it.

**H-11 — the `disc ≠ 0` quantifier is a proved correction, not a hypothesis, and this chapter keeps
it.** `EFF.W12.27` states the certification "**and (A0)-strongly (every `disc ≠ 0` lift has this σ
[—in fact *every lift* struck as FALSE in equal characteristic at wild decided shapes])**", with the
explicit counter-instance (a `TRP-RAM3(h)` member, `3 ∤ h`, `b₁ = b₂ = 0` in-window, lift
`F = y³ + b₀` with `F′ ≡ 0` in equal characteristic 3, hence `disc = 0` and **no σ at all**), and
`EFF.W12.51` (BOX-7) pins the definiendum: "Decided = certified on window digits for all `disc ≠ 0`
lifts". `leanfinal`'s `DecidedAt` (`GenuineDensity.lean:66`) quantifies over **every** lift
`a : Fin n → O` with `proj O n N a = c`, with no `disc ≠ 0` restriction. **This chapter does not
weaken `DecidedAt`.** Instead every decidedness node (§9) carries the separability of the *residual*
data as a hypothesis and derives `typeOf` for **every** lift of the class — which is possible
precisely because the residual separability is a statement about the window, and `typeOf` is defined
for every monic polynomial including inseparable ones (`typeOf` needs only unique factorization,
`TypeOf.lean:43`). Where the corpus's `disc ≠ 0` restriction is genuinely needed — the corpus needs
it because its σ is read through roots — this chapter does not need it, because its σ is read
through `monicFactors`. That divergence is §14 item 5.

**H-12 — codex-cross-read status: OWED.** This chapter is Opus-authored and has **not** been
cross-read. The specific items flagged for that read are §14.

**H-13 — `leanspec` stubs for this chapter live in their OWN namespace.** Chapter G's stage-0e note
records a structural failure: "`leanspec/Leanspec/ChapG.lean` re-declares contract names inside
`Uniformity.Density` and `Uniformity.Density.Menu` while importing the real `Uniformity` package, so
every stub whose node has since landed in `leanfinal` now fails with *has already been declared* —
**32 such collisions**, growing by one every time a chapter-G node lands". Chapter B's stub file
wraps every declaration in `namespace LeanspecB` (§12), so the collision count for this chapter is
structurally zero and the 0e type diff is run per declaration against the fully-qualified
`leanfinal` twin.

---

## 2. NODE INDEX

| § | nodes | content | env |
|---|---|---|---|
| 3 | B.01–B.20 | the development, the heights, and the **polygon representation** (DECISION D-1) | A / A' |
| 4 | B.21–B.30 | the order-1 residual field and the residual polynomial | D / A' |
| 5 | B.31–B.36 | the product law: `suppVal` additive, `resPoly` multiplicative | A' |
| 6 | B.37–B.48 | the two dissections (theorem of the polygon; theorem of the residual polynomial) | B |
| 7 | B.49–B.62 | the `(e,f)` assignment and the leaf theorem | B / C |
| 8 | B.63–B.74 | NS-6, the order-0 peel, the order-0 leaf law, `typeOf` transport | B |
| 9 | B.75–B.82 | level-`N` decidedness certificates in full generality | C |
| 10 | B.83–B.86 | gates: `q = 2` and `q = 3` firing instances, and the axiom census | C |

**Kind census:** 21 `def`, 45 `lemma`, 16 `theorem`, 4 `gate` — **86 nodes**.
**Landed-node census:** 0 nodes are `landed:`; 0 nodes are `quarry:` (H-6); 41 distinct landed
declarations are consumed by name across the DEPENDS fields, of which 20 are DAG nodes
(`lean:*`) and 21 are landed declarations with no DAG node of their own.
**Split-mandated nodes** (the fleet will see more than 86 units of work): B.13 → 2, B.32 → 3,
B.42 → 4, B.44 → 3, B.48 → 3, B.55 → 2, B.56 → 4, B.79 → 2, plus the split *candidates* flagged at
B.05, B.17, B.20, B.30, B.40, B.58, B.70, B.81. Planning figure for the fleet: **≈ 110 Lean files.**

**Graph shape** (computed from the DEPENDS fields, `spec/DAG_BLUEPRINT_B.tsv`): 214 intra-chapter
edges, **acyclic**, **critical path 16**, layer widths
`17, 13, 11, 8, 7, 6, 5, 4, 4, 3, 3, 2, 1, 1, 1, 1`. Seventeen nodes are fireable immediately (they
depend only on landed API or on nothing). The critical path runs
`B.02 → B.05 → B.08 → B.12 → B.16 → B.26 → B.32 → B.38 → B.42 → B.48 → B.51 → B.55 → B.58 → B.63
→ B.79 → B.82`, i.e. development → polygon → residual → product law → dissections → `(e,f)` → NS-6
→ decidedness. **B.42 (the theorem of the polygon) and B.56 (`B-BOX-1`'s repair) are the chapter's
two schedule risks**, and B.42 sits on the critical path.

---

## 3. §3 — THE DEVELOPMENT, THE HEIGHTS, AND THE POLYGON REPRESENTATION

### DECISION D-1 — THE NEWTON-POLYGON REPRESENTATION

> **This block is a Phase-0d interface decision made here, for Asvin's fresh-eyes audit.** It was
> deliberately deferred: `spec/CERTAIN_NODES_2026-08-14.md` **REJECTED R1** records "Newton-polygon
> primitives over `O[X]` (hull, vertices, sides, slopes). FAILS F1 AND F2 … Whether the leanfinal
> polygon reads a `Finset (ℕ × ℕ)`, a function `ℕ → ℕ∞` (matching
> `IsDiscreteValuationRing.addVal`), or ℚ-slope data is exactly a Phase-0d interface decision …
> **Verdict: quarry-copy vs fresh-prove must NOT be decided by this list.**" `BLUEPRINT_PHASE_DESIGN`
> v1 §7 item 3 names it too. It is core-set-adjacent because three further R-class deferrals
> (R6 the recentred-cubic polygon case analysis, R7 `HYP.07` the non-integral-slope `CertRam3`,
> R13 the hypothesis-manufacturing lemmas for strong Hensel) are blocked on it by name.

**THE DECISION.** The Newton polygon is represented by its **cleared support function** — a total
`ℕ∞`-valued function of the polynomial and of an integral slope pair — and by **nothing else**.
Concretely, three objects and no more:

1. **heights**: `npHgt φ f : ℕ → ℕ∞`, `npHgt φ f j = gaussVal (dev φ f j)` (B.11). Total; the value
   `⊤` encodes "the `j`-th development coefficient is `0`", i.e. "the abscissa `j` is not in the
   support". No `Finset` of support points is ever formed.
2. **the cleared support value**: for `u ℓ : ℕ` with `0 < ℓ`,
   `suppVal φ f u ℓ : ℕ∞ = (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • npHgt φ f j + u * j)`
   (B.14). This is `(★)` cleared of denominators: `ℓ · h_F(u/ℓ) = suppVal φ f u ℓ`.
3. **sides, slopes, lengths, vertices**: all **derived predicates on the argmin set**
   `onSide φ f u ℓ = {j | ℓ • npHgt φ f j + u * j = suppVal φ f u ℓ}` (B.16–B.20). A slope is a pair
   `(u, ℓ)` whose argmin set is not a singleton; the side's length is `max − min` of the argmin; the
   residual degree is `(max − min)/ℓ`; a vertex is an abscissa in the argmin of two distinct slopes.

No `ℚ` appears in any statement of this chapter. No hull is ever constructed. No lower-convex-hull
*object* exists; the hull **height** is a derived definition (B.19) supplied only because chapters
C/H's count layer needs `⌈P(j)⌉` (`EFF.W12.24`'s `B(N) = mN − Σ_{j<m}⌈P(j)⌉ − L`), and it is defined
as a `Finset.sup` over the finitely many candidate slope pairs with a bridging lemma (B.20).

**THE CRITERIA, and how each candidate scores.** The charge names the criteria: *what the slot
machinery and the tower chapters will consume.*

| criterion | evidence | cleared support fn | `Finset (ℕ×ℕ)` + `sup'` hull | vertex list as data | ℚ-slope-first |
|---|---|---|---|---|---|
| **C1. It is what the corpus's own load-bearing read IS** | `EFF.HE3.31` `(★)` is **byte-frozen** and consumer-pinned by HE6 and HE7; `EFF.HE6.17`(d) `h_F(κ) := min_j(dv(A_j)+jκ)`; `EFF.HE6.30`'s central identity `(†) Σ_λ n_λ min(λ,κ) = D′h_F(κ)` samples "at every rational `κ > D′h`"; `EFF.HE6R1.13`(b) is a **translation identity for the support function** (`h_{F₂,f}(κ₂) = h_{F₂,f_S}(κ₂) + c_g`) with no hull analogue | ✅ is literally it | ⚠ the hull is the corpus's *definition*, the support function its *computation*; `EFF.HE6` §7 says a Lean formalization "must supply both and their equivalence" — the support-first choice makes the hull a derived def (B.19) instead of a second primitive | ❌ | ❌ |
| **C2. The slot machinery's evaluation lemmas are support-function statements** | `EFF.HE6.15` (SLOT-SEAM): `dv(A(ξ)) = min_i(e₁v(a_i)+ih)` **exactly** — a `min` of linear forms, which at `e₁=1, h=0` is `gaussVal`; `EFF.HE6.17`(c): `dv(Ψ_{κ,r}(ξ)) = ℓd·min(δ,κ)+ε(ξ)` | ✅ B.36 and B.33 are these | ⚠ needs the hull→support bridge first | ❌ | ⚠ |
| **C3. Integer sampling is provably insufficient; rational sampling is what kills `(SEP)`** | `EFF.HE6.30`(c): integer sampling "cannot separate three slopes inside one open interval, but rational sampling … can, because the gaps `(λ_i,λ_{i+1})` are always nonempty in ℚ" | ✅ the pair `(u,ℓ)` ranges over *all* coprime pairs; sampling at `u/ℓ` costs nothing | ⚠ | ❌ | ✅ |
| **C4. Heights must be `ℤ`/`ℕ`-valued and slopes `ℚ`-valued, kept apart** | `EFF.HE3.11`: "`dv(A_j) ≥ (μ−j)D′h+1` **since `dv` is ℤ-valued on the `A_j`**"; `EFF.HE3.44`: "no element of `R` has non-integer `dv`" is *the* obstruction; `EFF.HE6R1.09`'s audit: "the heights in `ℤ` (`dv₂` ℤ-valued)" is load-bearing for the cocycle exponent, and `EFF.HE6R1.39` (PE3 F-1) found a **real defect** from conflating an ℤ-valued domain requirement with a ℚ-valued line value `h(λ₂) = m₁+j₁λ₂` that "need not be an integer off the first side" | ✅ heights `ℕ∞`, slopes only ever the **pair** `(u,ℓ)`; a ℚ is never formed, so the defect class `EFF.HE6R1.39` found cannot be written | ⚠ `npHeight` is ℚ-valued (`NewtonPolygon.lean:148`) so line values are ℚ by construction | ⚠ | ❌ this is exactly the shape that produced a real defect |
| **C5. Canonicity — is the object a function of the polynomial?** | the quarry's own record: `npVertices` is **not** determined by `npHeight` ("it reads which collinear interior dots are present in `S`"), `npVertices_not_stable_of_hull_preserved` (`NewtonPolygon.lean:784`) is a **proved negative result** with witness `S={(0,0),(1,0)}`, `S'={(0,0)}`, and the repair needed 1744 lines and a **third** hypothesis (`HullStability.lean:1279`, `habs`: abscissa containment). That repair was **the campaign's one banked `sorry`** | ✅ `npHgt φ f` is a function of `(φ, f)`; there is no representation to preserve, so no stability lemma exists to need | ❌ the 1744-line `HullStability` proof exists *because* the representation is not canonical | ❌ provably insufficient as data | ⚠ |
| **C6. The theorem of the product comes for free** | the product law is what both dissections rest on | ✅ `suppVal` is a twisted Gauss valuation, hence **additive on products** (B.32); the polygon-of-a-product = Minkowski sum is then a corollary rather than a construction | ❌ Minkowski sum of hulls must be built | ❌ | ❌ |
| **C7. The tower reuses it unchanged at order `r`** | `dv_r` is `ℤ`-valued after the `e₁⋯e_{r−1}` normalization (`EFF.HE3.10`, `.20`; `EFF.HE6R1.18`'s level-2 dictionary `D″ = D′ℓd_r`, `T₂ = ℓd_rλ`) | ✅ the cleared form is invariant under `(u,ℓ,c) ↦ (cu,cℓ,c·)`, so one predicate serves every order; the level-2 translation identity `EFF.HE6R1.13`(b) is a statement *about this object* | ⚠ requires re-normalizing the ℚ heights per order | ⚠ | ❌ `Rat.num`/`Rat.den` extraction per order |
| **C8. It matches `leanfinal`'s stated house style** | `ScaleExtraction.lean:14` **verbatim**: "in the one polygon formulation that is **representation-free**"; `:76-80`: "the Newton polygon of `f` … lies on or above the line through `(n,0)` and `(0,mn)` … Written without any polygon representation, that condition is the coefficient divisibility `π^(m(n-i)) ∣ f.coeff i`"; `TypeOf.lean:43`: `typeOf` uses "no Newton polygon, no classifier"; `LocalData.lean:25`: "Nothing here mentions … a Newton polygon" | ✅ CN-12's landed read `exists_monic_scaleRoots` is **exactly** `suppVal` at `(u,ℓ) = (m,1)` for `φ = X` (B.15 proves the identification) | ❌ would be the first `Finset (ℕ×ℕ)` object in the target, against a stated design choice | ❌ | ❌ |
| **C9. Library support** | four-way absence (H-6); mathlib has `addVal : AddValuation O ℕ∞` (`DiscreteValuationRing/Basic.lean:406`) and the landed bridge `pow_dvd_iff_le_addVal` (`StrongHensel.lean:244`) | ✅ builds on mathlib's own valuation and on a landed bridge | ⚠ the quarry's 144 declarations are `PadicValuation`-wired and ℕ-height/ℚ-slope, so they are **not** copyable at general `O` without re-generalizing all five modules | ⚠ | ⚠ mathlib's `ConvexOn` machinery is the one thing this route buys |

**WHAT THE DECISION GIVES UP, stated plainly.** (i) The quarry's proved combinatorics —
`dropCollinear` corner-invariance, sorted-list surgery, chord-attainment gluing, and the repaired
`npVertices_stable_of_hull_preserved_core` — do **not** transfer; §3 re-derives the side
combinatorics it needs from scratch, and it needs much less (B.17's `ℓ`-spacing lemma is four lines
of `Nat.Coprime` arithmetic and replaces the whole vertex-stability apparatus). (ii) mathlib's
`ConvexOn` API is unavailable, since convexity of the support function is not stated; the chapter
never needs it, because every consumer is an argmin statement, not a convexity statement.
(iii) `MultiSlopeMenu.lean`'s existing consumer pattern (`Side`/`toSideFace` packaged into
`ShapeCell.polygon`) has no analogue here; a future Montes-engine port would have to build one.
**These three are the decision's whole cost and they are recorded for the audit.**

**FALSIFIER for the decision** (what would overturn it): a chapter-C/H node that provably needs the
*hull* as an object rather than as a height — e.g. a statement quantifying over the sides of a
polygon as a `List` with an induction on that list. If such a node appears, B.19/B.20 are the
extension point (add `npSides` as a derived `List` with a bridging lemma), and nothing in §§4–10
changes, because no node below mentions a side except through `onSide`.

---

### NODE B.01 [def] [fresh]

**STATEMENT.** *The order-1 key data.* An **order-1 key** over `O` is a monic `φ ∈ O[X]` of positive
degree whose reduction `φ.map (residue O)` is irreducible over the residue field. Write `m` for
`φ.natDegree`. (The reduction of a monic polynomial is monic of the same degree, so `φ̄` is monic
irreducible of degree `m`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `IsKey φ` : `φ` is monic of positive degree with irreducible reduction — an order-1 key. -/
structure IsKey (φ : Polynomial O) : Prop where
  monic : φ.Monic
  pos : 0 < φ.natDegree
  irred : Irreducible (φ.map (IsLocalRing.residue O))
```

**DEPENDS.** none (mathlib `Polynomial.Monic`, `Irreducible`, `IsLocalRing.residue`).

**PROOF.** definitional.

**SIZE.** 8 lines.

**FAITHFULNESS.** The classical object is "a monic lift of a monic irreducible factor of `f̄`"
(`EFF.W12.23`: "`Φ` the read's fixed monic lift of `P̄`"; `docs/GMN_citations.md` Def 1.21: "a type
of order zero is a monic irreducible `t = ψ₀(y) ∈ F[y]`"). This node records the *lift*, not the
*type*: the type-of-order-zero is `φ̄` and is recovered as `φ.map (residue O)`. Two conventions are
deliberately NOT imposed: (i) `φ̄ ≠ y` — GN15 imposes it for key polynomials, and this chapter does
not, because the `φ̄ = X` case is the ordinary Newton polygon and is the one case where CN-12's
landed read applies verbatim (B.15); (ii) irreducibility of `φ` itself over `O` — it follows from
`irred` by `Monic.irreducible_of_irreducible_map`, and is derived where needed (B.21) rather than
assumed. **Flagged for human review as a new definition** (parent CLAUDE.md trust boundary).

**SOURCE.** `EFF.W12.23`; `EFF.HE6.08` (at `e₁ = 1`); `docs/GMN_citations.md` Def 1.21.

**TEETH.** signed non-applicable (a definition; guarded through its consumers).

**ENVIRONMENT.** ENV-A.

---

### NODE B.02 [def] [fresh]

**STATEMENT.** *The `φ`-adic development.* For monic `φ` of positive degree and any `f ∈ O[X]`,
define the `j`-th development coefficient by iterated monic division:
`dev φ f 0 = f %ₘ φ` and `dev φ f (j+1) = dev φ (f /ₘ φ) j`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `dev φ f j` : the `j`-th coefficient of the `φ`-adic development of `f`. -/
noncomputable def dev (φ : Polynomial O) : Polynomial O → ℕ → Polynomial O
  | f, 0 => f %ₘ φ
  | f, (j + 1) => dev φ (f /ₘ φ) j
```

**DEPENDS.** none (mathlib `Polynomial.modByMonic`, `Polynomial.divByMonic`).

**PROOF.** definitional. The recursion is structural in `j`, so no well-foundedness obligation
arises; `f` is the varying argument and `φ` is fixed, which is why `φ` is a parameter and `f` is not.

**SIZE.** 6 lines.

**FAITHFULNESS.** `EFF.W12.23` verbatim: "Monic division gives the UNIQUE `Φ`-adic development
`f = Φ^m + Σ_{j<m} a_j Φ^j`, `a_j ∈ (O/π^N)[x]_{<d}`". This node defines the coefficients *by* that
division rather than *characterising* them; B.05 proves the sum identity and B.06 the uniqueness, so
the characterisation is available and the definition is not load-bearing beyond it. The definition
does not require `φ̄` irreducible, only `φ` monic — deliberately, since B.32's product law is proved
for any monic `φ`.

**SOURCE.** `EFF.W12.23`; `EFF.HE3.13`; `EFF.HE6.10`.

**TEETH.** `W12-SHAPE` (`EFF.W12.54`, 0/164 violations over 23 rows; every row's key is a
development-coefficient valuation) → **executable regression** retained (the note's battery reads
developments over `ℤ_p`; this node is their general-`O` object).

**ENVIRONMENT.** ENV-A.

---

### NODE B.03 [lemma] [fresh]

**STATEMENT.** Each development coefficient has degree below `deg φ`: for `φ` monic with
`0 < deg φ`, `(dev φ f j).degree < φ.degree` for every `f` and `j`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem degree_dev_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    ∀ (f : Polynomial O) (j : ℕ), (dev φ f j).degree < φ.degree
```

**DEPENDS.** B.02 · mathlib `Polynomial.degree_modByMonic_lt`.

**PROOF.**
1. Induction on `j`, generalising `f`.
2. `j = 0`: `dev φ f 0 = f %ₘ φ` by `rfl`; apply `degree_modByMonic_lt f hφ`.
3. `j+1`: `dev φ f (j+1) = dev φ (f /ₘ φ) j` by `rfl`; apply the induction hypothesis at
   `f /ₘ φ`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.W12.23` ("`deg A_j < D′`"); `EFF.HE3.13`; `EFF.HE6.10`.

**TEETH.** signed non-applicable (a degree bound; no battery row reads it).

**ENVIRONMENT.** ENV-A.

---

### NODE B.04 [lemma] [fresh]

**STATEMENT.** The development vanishes past the degree: if `φ` is monic with `0 < deg φ` and
`f.natDegree < j * φ.natDegree` then `dev φ f j = 0`. In particular `dev φ f j = 0` for every
`j > f.natDegree` (since `1 ≤ φ.natDegree`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem dev_eq_zero_of_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    ∀ (f : Polynomial O) (j : ℕ), f.natDegree < j * φ.natDegree → dev φ f j = 0
```

**DEPENDS.** B.02 · B.03 · mathlib `Polynomial.natDegree_divByMonic`,
`Polynomial.modByMonic_eq_self_iff`, `Polynomial.degree_lt_iff_natDegree_lt`.

**PROOF.**
1. Induction on `j`, generalising `f`.
2. `j = 0`: the hypothesis reads `f.natDegree < 0`, impossible; close by `omega`.
3. `j+1`: by `natDegree_divByMonic f hφ`, `(f /ₘ φ).natDegree = f.natDegree − φ.natDegree`
   whenever `φ.natDegree ≤ f.natDegree`, and `f /ₘ φ = 0` otherwise.
4. Case `f.natDegree < φ.natDegree`: then `f /ₘ φ = 0` (`divByMonic_eq_zero_iff`), and
   `dev φ 0 j = 0` by a separate induction (`dev φ 0 j = 0` for all `j`, since `0 %ₘ φ = 0` and
   `0 /ₘ φ = 0`) — this is the private helper `dev_zero`.
5. Case `φ.natDegree ≤ f.natDegree`: apply the induction hypothesis at `f /ₘ φ`, whose degree
   bound `f.natDegree − φ.natDegree < j * φ.natDegree` follows from the hypothesis by `omega`.

**SIZE.** 20 lines, plus the 4-line private helper `dev_zero`.

**SOURCE.** `EFF.W12.23` (the development is finite: `j` ranges over `j ≤ m`);
`EFF.HE3.13` (`A_μ = 1`, i.e. the development stops).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-A.

---

### NODE B.05 [lemma] [fresh]

**STATEMENT.** *The development sums to `f`.* For monic `φ` with `0 < deg φ` and any `f`, and any
`k` with `f.natDegree < k * φ.natDegree`,
`f = Σ_{j ∈ range k} dev φ f j * φ ^ j`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem sum_dev_eq {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : Polynomial O)
    {k : ℕ} (hk : f.natDegree < k * φ.natDegree) :
    ∑ j ∈ Finset.range k, dev φ f j * φ ^ j = f
```

**DEPENDS.** B.02 · B.04 · mathlib `Polynomial.modByMonic_add_div`, `Finset.sum_range_succ'`.

**PROOF.**
1. Induction on `k`, generalising `f`.
2. `k = 0`: the hypothesis reads `f.natDegree < 0`, impossible.
3. `k+1`: split the sum with `Finset.sum_range_succ'` into `dev φ f 0 + (Σ_{j<k} dev φ f (j+1) * φ^(j+1))`.
4. `dev φ f (j+1) = dev φ (f /ₘ φ) j` by `rfl`, so the tail is `(Σ_{j<k} dev φ (f /ₘ φ) j * φ^j) * φ`
   after `Finset.mul_sum` and `pow_succ`.
5. Case `f.natDegree < φ.natDegree`: then `f /ₘ φ = 0`, the tail is `0`, and
   `dev φ f 0 = f %ₘ φ = f` by `modByMonic_eq_self_iff hφ` and `degree_lt_iff_natDegree_lt`.
6. Case `φ.natDegree ≤ f.natDegree`: the induction hypothesis at `f /ₘ φ` (degree bound by `omega`
   from `natDegree_divByMonic`) rewrites the tail to `(f /ₘ φ) * φ`, and
   `modByMonic_add_div f hφ : f %ₘ φ + φ * (f /ₘ φ) = f` closes by `ring_nf`.

**SIZE.** 26 lines. **SPLIT CANDIDATE**: if step 6's rewriting fights `ring_nf`, split steps 3–4
(the sum-reindexing identity, a statement about any `a : ℕ → Polynomial O`) into a private helper.

**SOURCE.** `EFF.W12.23`; `EFF.HE3.13`; `EFF.HE6.10`.

**TEETH.** `W12-BLOCK` (`EFF.W12.55`, 0/1,594,670 — "Hensel product identity `g·l == f`"; the
development identity is the same shape of check at the branch level) → **Lean theorem** (this node
is the identity, now proved at general `O`).

**ENVIRONMENT.** ENV-A.

---

### NODE B.06 [lemma] [fresh]

**STATEMENT.** *Uniqueness of the development.* If `φ` is monic with `0 < deg φ`, and
`a : ℕ → Polynomial O` satisfies `(a j).degree < φ.degree` for all `j` and
`Σ_{j ∈ range k} a j * φ^j = f`, then `a j = dev φ f j` for every `j < k`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem dev_unique {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} {a : ℕ → Polynomial O} {k : ℕ}
    (hdeg : ∀ j, (a j).degree < φ.degree)
    (hsum : ∑ j ∈ Finset.range k, a j * φ ^ j = f) :
    ∀ j < k, a j = dev φ f j
```

**DEPENDS.** B.02 · B.03 · mathlib `Polynomial.modByMonic_eq_self_iff`,
`Polynomial.modByMonic_eq_zero_iff_dvd` (via `Monic.dvd_iff_modByMonic_eq_zero`),
`Polynomial.divByMonic_eq_of_eq_mul_add`.

**PROOF.**
1. Induction on `k`, generalising `f` and `a`; the statement for `j` follows from the statement for
   `0` applied to the shifted data, so prove the `j = 0` case and reindex.
2. `j = 0` case: write `hsum` as `f = a 0 + φ * (Σ_{j<k−1} a (j+1) * φ^j)` (`sum_range_succ'`,
   `Finset.mul_sum`, `pow_succ`).
3. `a 0` has degree `< φ.degree`, so by the uniqueness clause of monic division
   (`modByMonic_add_div` plus the degree-uniqueness of the remainder, available as
   `Polynomial.modByMonic_eq_of_eq_add_mul` in the pinned mathlib; if that name is absent, prove the
   uniqueness clause as a private helper from `Monic.dvd_iff_modByMonic_eq_zero` applied to
   `a 0 − f %ₘ φ`, whose degree is `< φ.degree` and which is divisible by `φ`) we get
   `a 0 = f %ₘ φ = dev φ f 0`.
4. Reindex: for `j+1 < k`, apply the induction hypothesis to `f /ₘ φ` with the shifted family
   `fun i => a (i+1)`, whose sum is `f /ₘ φ` by step 3 and `divByMonic` uniqueness.

**SIZE.** 30 lines. **Two named risks, both bounded**: the exact mathlib name for the
remainder-uniqueness clause must be confirmed by `exact?`/local `rg` before writing step 3 (the
private-helper fallback is spelled out); and step 4's reindexing needs `Finset.sum_range_succ'`, not
`Finset.sum_range_succ`.

**SOURCE.** `EFF.W12.23` ("the **UNIQUE** `Φ`-adic development").

**TEETH.** signed non-applicable (uniqueness is consumed only to justify that the corpus's `A_j` and
this chapter's `dev φ f j` are the same object).

**ENVIRONMENT.** ENV-A.

---

### NODE B.07 [def] [fresh]

**STATEMENT.** *The Gauss valuation.* For `a ∈ O[X]`, define
`gaussVal a : ℕ∞ = (Finset.range (a.natDegree + 1)).inf (fun i => addVal O (a.coeff i))`, the
minimum of the valuations of the coefficients. (`gaussVal 0 = ⊤`, since every coefficient of `0` has
valuation `⊤`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

open IsDiscreteValuationRing in
/-- `gaussVal a` : the minimum `π`-valuation of the coefficients of `a` (`⊤` iff `a = 0`). -/
noncomputable def gaussVal (a : Polynomial O) : ℕ∞ :=
  (Finset.range (a.natDegree + 1)).inf (fun i => addVal O (a.coeff i))
```

**DEPENDS.** mathlib `IsDiscreteValuationRing.addVal` (`DiscreteValuationRing/Basic.lean:406`),
`Finset.inf`.

**PROOF.** definitional. `Finset.inf` (not `inf'`) is used deliberately: `ℕ∞` has `OrderTop`, so
`Finset.inf` is total and the empty-`Finset` corner is `⊤` rather than a side condition. The range is
`a.natDegree + 1` and not all of `ℕ`: coefficients above `natDegree` vanish and would contribute `⊤`,
which cannot lower an `inf`, so the truncation is harmless — and B.08 proves it.

**FAITHFULNESS.** `EFF.HE6.10` verbatim: "`dv(A_j) := min_i(e₁v(a_{j,i}) + ih)`", which at `e₁ = 1`,
`h = 0` is `min_i v(a_{j,i})`. `EFF.W12.23` verbatim: "`v(a_j) := min coefficient valuation = the
height of the lowest nonzero slot". Both are this definition. **Flagged for human review.**

**SIZE.** 6 lines.

**SOURCE.** `EFF.HE6.10`; `EFF.W12.23`.

**TEETH.** `HE-NORM` (`EFF.HE3.50`, 72,134 identities, 0 violations; the identity is stated in
`dv` of development coefficients) → **executable regression** retained.

**ENVIRONMENT.** ENV-A.

---

### NODE B.08 [lemma] [fresh]

**STATEMENT.** *The divisibility characterisation of `gaussVal`.* For `hπ : Irreducible π`, `k : ℕ`
and `a ∈ O[X]`: `(k : ℕ∞) ≤ gaussVal a ↔ ∀ i, π ^ k ∣ a.coeff i`. Consequently
`gaussVal a = ⊤ ↔ a = 0`, and `gaussVal a` is unchanged if the `inf` is taken over any
`Finset.range M` with `a.natDegree < M`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem le_gaussVal_iff (hπ : Irreducible π) {k : ℕ} {a : Polynomial O} :
    (k : ℕ∞) ≤ gaussVal a ↔ ∀ i, π ^ k ∣ a.coeff i

theorem gaussVal_eq_top_iff {a : Polynomial O} : gaussVal a = ⊤ ↔ a = 0

theorem gaussVal_range (a : Polynomial O) {M : ℕ} (hM : a.natDegree < M) :
    gaussVal a = (Finset.range M).inf (fun i => IsDiscreteValuationRing.addVal O (a.coeff i))
```

**DEPENDS.** B.07 · landed `Uniformity.Hensel.pow_dvd_iff_le_addVal` (`StrongHensel.lean:244`) ·
mathlib `Finset.le_inf_iff`, `Polynomial.coeff_eq_zero_of_natDegree_lt`,
`IsDiscreteValuationRing.addVal_zero`, `Polynomial.ext_iff`.

**PROOF.**
1. `le_gaussVal_iff`, (→): `Finset.le_inf_iff` gives `(k:ℕ∞) ≤ addVal O (a.coeff i)` for `i` in the
   range; `pow_dvd_iff_le_addVal hπ` converts each to `π^k ∣ a.coeff i`. For `i` outside the range,
   `coeff_eq_zero_of_natDegree_lt` gives `a.coeff i = 0` and `π^k ∣ 0`.
2. (←): `Finset.le_inf` with `pow_dvd_iff_le_addVal hπ` in the other direction.
3. `gaussVal_eq_top_iff`, (→): `Finset.inf_eq_top_iff` gives `addVal O (a.coeff i) = ⊤` for `i` in
   the range, hence `a.coeff i = 0` (`addVal_eq_top_iff`, or: `addVal` of a nonzero element of a
   DVR is not `⊤`); with step 1's out-of-range case, `Polynomial.ext_iff` gives `a = 0`.
4. (←): `a = 0` makes every coefficient `0` and every `addVal` `⊤`, so the `inf` is `⊤`.
5. `gaussVal_range`: both `inf`s are over supersets/subsets of the support; the extra indices
   contribute `addVal O 0 = ⊤`, which is the `inf`'s neutral element
   (`Finset.inf_eq_inf_filter`-style argument, or directly: `Finset.inf_union` after splitting
   `range M = range (natDegree+1) ∪ Ico (natDegree+1) M`).

**SIZE.** 26 lines. **Three public declarations** — permitted because they are the same fact in the
three shapes every consumer needs (`le_gaussVal_iff` for divisibility transport,
`gaussVal_eq_top_iff` for the support, `gaussVal_range` so that B.14 may take a *uniform* range for
all `j`); if the merge queue objects, `gaussVal_range` becomes a private helper of B.14.

**SOURCE.** `EFF.HE6.10`; `EFF.W12.23`.

**TEETH.** `HE-NORM`, `HE-PSI` (`EFF.HE3.50`, `.51`) → **Lean theorem** (the divisibility reading of
`dv` becomes a theorem rather than a convention).

**ENVIRONMENT.** ENV-A'.

---

### NODE B.09 [lemma] [fresh]

**STATEMENT.** *`gaussVal` is additive on products (Gauss's lemma).* For `hπ : Irreducible π` and
`a b ∈ O[X]`: `gaussVal (a * b) = gaussVal a + gaussVal b`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem gaussVal_mul (hπ : Irreducible π) (a b : Polynomial O) :
    gaussVal (a * b) = gaussVal a + gaussVal b
```

**DEPENDS.** B.07 · B.08 · mathlib `Polynomial.map_mul`, `Polynomial.mul_ne_zero`,
`IsLocalRing.residue`, and the fact that `Polynomial (ResidueField O)` is a domain
(`Polynomial.instNoZeroDivisors` over a field).

**PROOF.**
1. Both sides are `⊤` iff `a = 0` or `b = 0` (B.08's `gaussVal_eq_top_iff` and
   `mul_eq_zero`); dispose of those cases.
2. Otherwise write `gaussVal a = (α : ℕ∞)`, `gaussVal b = (β : ℕ∞)` with `α β : ℕ`
   (`WithTop.ne_top_iff_exists`).
3. `≥`: by B.08, `π^α ∣` every coefficient of `a` and `π^β ∣` every coefficient of `b`; each
   coefficient of `a*b` is a sum of products, so `π^(α+β)` divides it; B.08 again.
4. `≤`: let `a₀ := a` divided coefficientwise by `π^α` — formally, choose `a' ` with
   `a = C (π^α) * a'`... **the clean route avoids division**: reduce mod `π^(α+β+1)`. Instead use
   the residue route: let `A := (a.divByPow α)` be the private helper produced by
   `Polynomial.exists_eq_C_pow_mul` (a private helper of this node: from B.08's `π^α ∣ a.coeff i`
   for all `i`, `choose` the quotients and assemble `a'` with `a = C (π^α) * a'`, using
   `Polynomial.ofFinsupp`/`Polynomial.ext`; `gaussVal a' = 0` because `α` was maximal).
5. `gaussVal a' = 0` means some coefficient of `a'` is a unit, i.e. `a'.map (residue O) ≠ 0`
   (B.08 at `k = 1`, contrapositive). Same for `b'`.
6. `Polynomial (ResidueField O)` is a domain, so `(a' * b').map (residue O) ≠ 0`, i.e.
   `gaussVal (a' * b') = 0`.
7. `a * b = C (π^(α+β)) * (a' * b')`, and `gaussVal (C (π^k) * c) = k + gaussVal c` (a second
   private helper, immediate from `coeff_C_mul` and `addVal` of a product).

**SIZE.** 34 lines, plus two private helpers (`exists_eq_C_pow_mul` ≈ 12 lines,
`gaussVal_C_pow_mul` ≈ 8 lines). **SPLIT MANDATED if the two helpers exceed 20 lines together**:
`exists_eq_C_pow_mul` is reusable (B.28 needs it to define residual coefficients), so its extraction
triggers a **RE-PLAN request** — the orchestrator should expect to book it as node **B.09a**.

**SOURCE.** `EFF.HE6.06` (classical import: "resultant symmetry, ultrametric ineq."); the additivity
itself is the corpus's unstated background fact — it is what makes `EFF.HE3.31`'s `(★)` a valuation.

**TEETH.** `HE-PSI` (`EFF.HE3.51`, 43,528 checks) → **Lean theorem**.

**ENVIRONMENT.** ENV-A'.

---

<!-- CHAP-B APPEND POINT — do not remove; sections are appended here in order -->
