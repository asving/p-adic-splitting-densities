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

### NODE B.10 [lemma] [fresh]

**STATEMENT.** *The development is level-stable.* Monic division commutes with coefficient
reduction: if `π ^ N` divides every coefficient of `f - f'` then `π ^ N` divides every coefficient of
`dev φ f j - dev φ f' j`, for every `j`. Consequently `(N : ℕ∞) ≤ gaussVal (f - f')` implies
`(N : ℕ∞) ≤ gaussVal (dev φ f j - dev φ f' j)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem dev_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (h : ∀ i, π ^ N ∣ (f - f').coeff i) :
    ∀ j i, π ^ N ∣ (dev φ f j - dev φ f' j).coeff i
```

**DEPENDS.** B.02 · B.08 · mathlib `Polynomial.map_modByMonic`, `Polynomial.map_divByMonic`
(both require `Monic`; **confirm the exact names by local `rg` in the pinned mathlib before writing —
they exist as `Polynomial.map_modByMonic`/`Polynomial.map_divByMonic` for a ring hom and a monic
divisor, and if the pin spells them differently the fallback is stated below**).

**PROOF.**
1. Reformulate as a statement about `Polynomial.map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))`:
   `π^N ∣ (a - b).coeff i` for all `i` is equivalent to `a.map ρ = b.map ρ` for
   `ρ := Ideal.Quotient.mk ((maximalIdeal O)^N)`, by `Ideal.Quotient.eq_zero_iff_mem`,
   `mem_maximalIdeal_pow_iff_dvd` (landed, `Drainage.lean`) and `Polynomial.ext_iff`.
2. So it suffices to prove `(dev φ f j).map ρ = dev (φ.map ρ) (f.map ρ) j` for every `j` — a
   statement about one polynomial, not two.
3. Induction on `j`. `j = 0`: `map_modByMonic` with `hφ` (monicity is preserved by `map`).
4. `j+1`: `map_divByMonic` with `hφ` gives `(f /ₘ φ).map ρ = (f.map ρ) /ₘ (φ.map ρ)`, then the
   induction hypothesis at `f /ₘ φ`.
5. Apply step 2 to `f` and to `f'` and combine with the hypothesis rewritten by step 1.
6. **Fallback if `map_modByMonic`/`map_divByMonic` are absent from the pin:** prove them as private
   helpers from `Polynomial.modByMonic_add_div` — `f = f %ₘ φ + φ * (f /ₘ φ)` maps to
   `f.map ρ = (f %ₘ φ).map ρ + (φ.map ρ) * ((f /ₘ φ).map ρ)` with
   `((f %ₘ φ).map ρ).degree < (φ.map ρ).degree` (by `degree_map_le` and `Monic.degree_map`), and the
   remainder-uniqueness clause of B.06 identifies the two decompositions.

**SIZE.** 22 lines (or 40 with the fallback helpers).

**SOURCE.** `EFF.W12.23` (the development is read on `(O/π^N)[x]`, i.e. it is defined at level `N`);
`EFF.HE3.27`(c) ("every new digit consulted lies strictly inside its class's window and is
determined by old digits at weakly lower `dv`-heights").

**TEETH.** `HE-T-CAP` (`EFF.HE3.54`, "the strongest tooth": a planted mutant reader that drops
out-of-window digits, 17 (`p=5`) / 43 (`p=7`) disagreements) → **Lean theorem** (this node is the
level-stability the tooth's honest reader relies on).

**ENVIRONMENT.** ENV-A'.

---

### NODE B.11 [def] [fresh]

**STATEMENT.** *The polygon's height function.* For an order-1 key `φ` and any `f`, define
`npHgt φ f j : ℕ∞ = gaussVal (dev φ f j)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `npHgt φ f j` : the height of the `φ`-adic Newton polygon's `j`-th support point (`⊤` when the
`j`-th development coefficient vanishes, i.e. when the abscissa `j` carries no point). -/
noncomputable def npHgt (φ f : Polynomial O) (j : ℕ) : ℕ∞ := gaussVal (dev φ f j)
```

**DEPENDS.** B.02 · B.07.

**PROOF.** definitional.

**FAITHFULNESS.** This is the **primary object of DECISION D-1**. The corpus's polygon is "the lower
hull of `{(j, dv(A_j))}_{j≤μ}`" (`EFF.HE3.13`, `EFF.HE6.10`, `EFF.W12.23` all verbatim); this node
declares the *point set as a function* `j ↦ dv(A_j)` and D-1 declares that the hull is never formed.
The `⊤` value replaces the corpus's convention of *omitting* an abscissa from the support: a zero
development coefficient has `dv = ∞`, which in the corpus's own words is guarded away by the peel
convention `EFF.HE6.09` ("a root `ρ` with `Φ′(ρ) = 0` has `dv(Φ′(ρ)) = ∞` and carries NO finite side
label"). Here nothing is guarded away: `⊤` is a value of `ℕ∞`, an `inf` absorbs it, and the peel
convention is a *consequence* (B.13's `npHgt φ f μ = 0` plus B.20's finiteness), not an assumption.
**Flagged for human review as the chapter's central new definition.**

**SIZE.** 5 lines.

**SOURCE.** `EFF.HE3.13`; `EFF.HE6.10`; `EFF.W12.23`.

**TEETH.** `W12-SHAPE` (`EFF.W12.54`, 0/164, both directions) → **executable regression** retained.

**ENVIRONMENT.** ENV-A.

---

### NODE B.12 [lemma] [fresh]

**STATEMENT.** `npHgt φ f j = ⊤ ↔ dev φ f j = 0`; and for `φ` monic with `0 < deg φ`,
`npHgt φ f j = ⊤` whenever `f.natDegree < j`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem npHgt_eq_top_iff {φ f : Polynomial O} {j : ℕ} : npHgt φ f j = ⊤ ↔ dev φ f j = 0

theorem npHgt_eq_top_of_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f : Polynomial O) {j : ℕ} (hj : f.natDegree < j) : npHgt φ f j = ⊤
```

**DEPENDS.** B.04 · B.08 · B.11.

**PROOF.**
1. First claim: unfold `npHgt` and apply B.08's `gaussVal_eq_top_iff`.
2. Second claim: `f.natDegree < j ≤ j * φ.natDegree` since `1 ≤ φ.natDegree`; apply B.04 then the
   first claim.

**SIZE.** 8 lines.

**SOURCE.** `EFF.HE6.09` (the `dv = ∞` corner).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-A.

---

### NODE B.13 [lemma] [fresh]

**STATEMENT.** *The top of the polygon.* Let `φ` be monic with `m := φ.natDegree > 0` and let `f` be
monic with `f.natDegree = μ * m`. Then `dev φ f μ = 1`, hence `npHgt φ f μ = 0`; and
`npHgt φ f j = ⊤` for every `j > μ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem dev_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) : dev φ f μ = 1

theorem npHgt_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) : npHgt φ f μ = 0
```

**DEPENDS.** B.02 · B.03 · B.11 · mathlib `Polynomial.Monic.natDegree_divByMonic`
(or `Polynomial.natDegree_divByMonic` plus `Monic.divByMonic`), `Polynomial.Monic.divByMonic`
(the quotient of a monic by a monic is monic when the degrees allow),
`Polynomial.eq_one_of_monic_natDegree_zero`.

**PROOF.**
1. `dev_top` by induction on `μ`, generalising `f`.
2. `μ = 0`: `f.natDegree = 0` and `f` monic force `f = 1`
   (`eq_one_of_monic_natDegree_zero`); `dev φ 1 0 = 1 %ₘ φ = 1` because `1.degree = 0 < φ.degree`
   (`modByMonic_eq_self_iff hφ`).
3. `μ+1`: `f /ₘ φ` is monic of degree `f.natDegree − m = μ * m` (`natDegree_divByMonic` and the
   monicity of the quotient of monics); apply the induction hypothesis to it, and
   `dev φ f (μ+1) = dev φ (f /ₘ φ) μ` by `rfl`.
4. `npHgt_top`: `npHgt φ f μ = gaussVal 1 = 0`, since `(1 : Polynomial O).coeff 0 = 1` has
   `addVal = 0` and the `inf` over `range 1` is that value.
5. The tail claim is B.12's second clause at `j > μ`, using `f.natDegree = μ*m < j*m` for `j > μ`.

**SIZE.** 24 lines. **SPLIT MANDATED → 2** (`dev_top` and `npHgt_top` land as separate files
`B13a.lean`, `B13b.lean`): step 3's monicity-of-the-quotient obligation is the largest single piece
and the fleet should not carry it and step 4 in one unit.

**SOURCE.** `EFF.HE3.13` verbatim ("`A_μ = 1`, `dv = 0`"); `EFF.HE6.10` ("`dv(A_μ) = 0`");
`EFF.W12.23` (the polygon includes the terminal point `(m, 0)`).

**TEETH.** `W12-SHAPE` → **Lean theorem** (the polygon's terminal point becomes a theorem).

**ENVIRONMENT.** ENV-A.

---

### NODE B.14 [def] [fresh]

**STATEMENT.** *The cleared support value.* For an order-1 key `φ`, a polynomial `f`, and
`u ℓ : ℕ`, define
`suppVal φ f u ℓ : ℕ∞ = (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • npHgt φ f j + u * j)`.
For `0 < ℓ` this is `ℓ` times the corpus's support function at the slope `u/ℓ`:
`suppVal φ f u ℓ = ℓ · h_F(u/ℓ)` where `h_F(κ) = min_j (dv(A_j) + jκ)` is `EFF.HE3.31`'s `(★)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `suppVal φ f u ℓ` : the cleared support value of `f`'s `φ`-adic polygon at the slope `−u/ℓ`,
i.e. `ℓ` times the corpus's `h_F(u/ℓ) = min_j (dv(A_j) + j·u/ℓ)`. -/
noncomputable def suppVal (φ f : Polynomial O) (u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • npHgt φ f j + (u * j : ℕ))
```

**DEPENDS.** B.11 · mathlib `Finset.inf`, the `ℕ∞` `AddCommMonoidWithOne`/`SMul ℕ` structure.

**PROOF.** definitional. Two choices are load-bearing and deliberate: (i) `ℓ • x` rather than
`(ℓ : ℕ∞) * x`, because scalar multiplication by a natural number on `ℕ∞` has the `nsmul` simp set
and avoids `⊤ * 0` corner cases (`ℓ • ⊤ = ⊤` for `ℓ > 0`, and `0 • ⊤ = 0`, which is exactly why
`0 < ℓ` is a hypothesis of every consumer); (ii) the range is `f.natDegree + 1`, uniform in `u, ℓ`,
which by B.12's tail clause and B.08's `gaussVal_range` loses nothing.

**FAITHFULNESS.** The corpus's own two displays, both transcribed here at `e₁ = 1`:
`EFF.HE3.31` (byte-frozen, consumer-pinned by HE6 and HE7) `h_F(κ) = min_j (dv(A_j) + jκ) =
Σ_{slopes λ} L_λ · min(λ, κ)` and `EFF.HE6.17`(d) `h_F(κ) := min_j(dv(A_j) + jκ)`. The *second*
equality of `(★)` — the sum over slopes — is **not** part of this definition; it is a theorem about
it and is NOT a chapter-B node (it is the counting layer's, chapter C/H). **Flagged for human
review; this is DECISION D-1's second object.**

**SIZE.** 6 lines.

**SOURCE.** `EFF.HE3.31` (`(★)`, byte-frozen); `EFF.HE6.17`(d); `EFF.HE6.30` (`(†)`);
`EFF.HE3.22` (`LEMMA HE3-1′`: `dv(B₀) = min_j(dv(A_j) + jκ)` generically).

**TEETH.** `HE-PSI` (`EFF.HE3.51`, 43,528 checks, guarding `.22`, `.29`, `.31` — i.e. guarding `(★)`
itself) → **Lean theorem** (`(★)`'s first equality becomes this definition; its content moves to
B.32 and B.36).

**ENVIRONMENT.** ENV-A.

---

### NODE B.15 [lemma] [fresh]

**STATEMENT.** *The DECISION's compatibility check: `suppVal` at `φ = X` is CN-12's landed read.* Let
`f` be monic of degree `n > 0`, `hπ : Irreducible π`, and `M : ℕ`. Then

* `dev X f j = C (f.coeff j)` and `npHgt X f j = addVal O (f.coeff j)` for every `j`; and
* `((M * n : ℕ) : ℕ∞) ≤ suppVal X f M 1 ↔ ∀ i < n, π ^ (M * (n - i)) ∣ f.coeff i`.

The right-hand side is verbatim the hypothesis of the landed
`Uniformity.Density.exists_monic_scaleRoots` (`ScaleExtraction.lean:92`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem dev_X (f : Polynomial O) (j : ℕ) : dev X f j = Polynomial.C (f.coeff j)

theorem npHgt_X (f : Polynomial O) (j : ℕ) :
    npHgt X f j = IsDiscreteValuationRing.addVal O (f.coeff j)

theorem suppVal_X_iff (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (hn : 0 < f.natDegree) (M : ℕ) :
    ((M * f.natDegree : ℕ) : ℕ∞) ≤ suppVal X f M 1 ↔
      ∀ i < f.natDegree, π ^ (M * (f.natDegree - i)) ∣ f.coeff i
```

**DEPENDS.** B.02 · B.08 · B.11 · B.14 · landed `Uniformity.Hensel.pow_dvd_iff_le_addVal`
(`StrongHensel.lean:244`) · mathlib `Polynomial.modByMonic_X`, `Polynomial.divByMonic_X`
(**confirm names**; the fallback is `Polynomial.divX` plus `f = C (f.coeff 0) + X * f.divX`).

**PROOF.**
1. `dev_X`: induction on `j`. `j = 0`: `f %ₘ X = C (f.coeff 0)` (mathlib `modByMonic_X`, or from
   `Polynomial.divX_mul_X_add` and remainder uniqueness). `j+1`: `f /ₘ X = f.divX` and
   `(f.divX).coeff j = f.coeff (j+1)` (`Polynomial.coeff_divX`), then the induction hypothesis.
2. `npHgt_X`: `gaussVal (C a) = addVal O a`, because `(C a).natDegree = 0` and the `inf` over
   `range 1` is `addVal O ((C a).coeff 0) = addVal O a`.
3. `suppVal_X_iff`, (→): `Finset.le_inf_iff` gives, for each `i ≤ n`,
   `M*n ≤ 1 • addVal O (f.coeff i) + M*i`, i.e. `M*n - M*i ≤ addVal O (f.coeff i)` in `ℕ∞`
   (`WithTop`-safe: move the finite summand `M*i` across by
   `ENat.add_le_add_iff_right`/`WithTop.add_le_add_iff_right` with `M*i ≠ ⊤`), i.e.
   `M*(n-i) ≤ addVal O (f.coeff i)`, i.e. the divisibility by `pow_dvd_iff_le_addVal hπ`.
4. (←): `Finset.le_inf`; for `i < n` use the hypothesis, and for `i = n` use `f.coeff n = 1`
   (`hf`), whose `addVal` is `0`, so the term is `0 + M*n = M*n`.

**SIZE.** 30 lines. **Three public declarations** — permitted because `dev_X` and `npHgt_X` are the
`φ = X` dictionary every later `φ = X` specialisation needs (B.83's gate, and chapters C/H's ordinary
Newton polygon), and `suppVal_X_iff` is the DECISION's compatibility certificate.

**⚠ THIS NODE IS DECISION D-1's CRITERION-C8 CERTIFICATE.** `ScaleExtraction.lean:76-80` states,
verbatim, that CN-12's divisibility hypothesis *is* the polygon condition "written without any
polygon representation". This node proves that the representation chosen by D-1 reproduces that
condition exactly, so the DECISION does not fork `leanfinal`'s existing polygon read — it extends it.
If this node fails to prove, **D-1 is refuted** and the cross-read must be told before any node of
§§4–10 fires.

**SOURCE.** `EFF.W12.23`; `spec/CERTAIN_NODES_2026-08-14.md` CN-12 and REJECTED R1
("the two representation-free polygon reads, CN-12 … and CN-13").

**TEETH.** signed non-applicable as a battery item (a compatibility identity), but it is the
chapter's **internal decision gate** — see the warning above.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.16 [def] [fresh]

**STATEMENT.** *The side of a slope.* For `u ℓ : ℕ` say the abscissa `j` is **on the `(u,ℓ)`-side**
of `f`'s `φ`-adic polygon when `ℓ • npHgt φ f j + u * j = suppVal φ f u ℓ`, i.e. when the `j`-th
support point attains the cleared support value.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `OnSide φ f u ℓ j` : the abscissa `j` lies on the side of slope `−u/ℓ`. -/
def OnSide (φ f : Polynomial O) (u ℓ j : ℕ) : Prop :=
  ℓ • npHgt φ f j + (u * j : ℕ) = suppVal φ f u ℓ

/-- The on-side abscissae, as a `Finset`. -/
noncomputable def sideSet (φ f : Polynomial O) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (OnSide φ f u ℓ)
```

**DEPENDS.** B.11 · B.14.

**PROOF.** definitional. `sideSet` is a `Finset.filter` with `Classical` decidability — the landed
precedent for `open Classical in` inside a definition is `Uniformity.Density.monicFactors`
(`TypeOf.lean:154`).

**FAITHFULNESS.** The corpus's on-side condition is `EFF.W12.23`'s three-way membership law, verbatim:
"`j` a **VERTEX** of `P`: `v(a_j) = P(j)` exactly and `digit_{P(j)}(a_j) ≠ 0`; `j` an **on-side
lattice point** (side `S`): `v(a_j) ≥ P(j)`, with `digit_{P(j)}(a_j)` = the residual coefficient
`r_j`; every other `j < m`: … `v(a_j) ≥ ⌈P(j)⌉`". `OnSide` is the *first* clause's equality
`v(a_j) = P(j)` in cleared form; the *digit* half of the vertex clause is B.28's residual coefficient
and its nonvanishing is B.30. The third clause (the "automatic ceiling") is not a condition at all in
this representation: `suppVal` is an `inf`, so `suppVal ≤ ℓ•H j + u*j` holds for every `j` by
definition, which is exactly "every point lies weakly above the polygon". **That the ceiling clause
becomes vacuous is a real simplification and is claimed as such** — see §14 item 3.

**SIZE.** 10 lines.

**SOURCE.** `EFF.W12.23`; `EFF.HE3.14` (the side's "lattice abscissas `j₀ + ℓk`").

**TEETH.** `W12-SHAPE`, `HEX3`-side rows: not applicable here (a definition).

**ENVIRONMENT.** ENV-A.

---

### NODE B.17 [lemma] [fresh]

**STATEMENT.** *The `ℓ`-spacing of a side.* Let `0 < ℓ`, `Nat.Coprime u ℓ`, and let `j, j'` both be
on the `(u,ℓ)`-side with `suppVal φ f u ℓ ≠ ⊤`. Then `ℓ ∣ (j - j')` as integers, i.e.
`j ≡ j' [MOD ℓ]`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem onSide_modEq (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O} {j j' : ℕ}
    (htop : suppVal φ f u ℓ ≠ ⊤) (hj : OnSide φ f u ℓ j) (hj' : OnSide φ f u ℓ j') :
    j ≡ j' [MOD ℓ]
```

**DEPENDS.** B.11 · B.14 · B.16 · mathlib `Nat.Coprime.dvd_of_dvd_mul_left`, `Nat.ModEq`,
`WithTop.ne_top_iff_exists`.

**PROOF.**
1. From `htop` and `hj`, `ℓ • npHgt φ f j ≠ ⊤`, so `npHgt φ f j ≠ ⊤` (as `0 < ℓ`); write
   `npHgt φ f j = (H : ℕ∞)` with `H : ℕ`, and likewise `H'` at `j'`.
2. The two `OnSide` equalities give, after `Nat.cast_injective` on `ℕ∞`, the `ℕ`-equality
   `ℓ * H + u * j = ℓ * H' + u * j'`.
3. Pass to `ℤ`: `ℓ * (H - H') = u * (j' - j)`. Hence `(ℓ : ℤ) ∣ u * (j' - j)`.
4. `Nat.Coprime u ℓ` gives `IsCoprime (u : ℤ) (ℓ : ℤ)` (`Nat.isCoprime_iff_coprime`), so
   `(ℓ : ℤ) ∣ (j' - j)`, which is `j ≡ j' [MOD ℓ]` (`Int.natCast_mod_cast` / `Nat.modEq_iff_dvd`).

**SIZE.** 18 lines. **SPLIT CANDIDATE**: if the `ℕ∞ → ℕ → ℤ` transport in steps 1–3 exceeds ~10
lines, extract it as a private helper `onSide_nat_eq` returning the `ℕ`-equality of step 2, which
B.20 and B.28 also want.

**⚠ THE `Nat.Coprime u ℓ` HYPOTHESIS IS LOAD-BEARING AND THE CORPUS PROVED IT SO BY
COUNTEREXAMPLE.** `EFF.HE6.52`'s tooth `HE6-T-BADKEY` fired on exactly this: "`gcd(u,ℓ) = 1`
hypothesis is load-bearing (`κ = 6/2` gives 2 factors, different residues)". Dropping coprimality
makes this lemma false (`u = ℓ = 2`: the spacing is `1`, not `2`) and silently corrupts B.28's
residual coefficients and B.30's degree. **Minimum-hypothesis check:** `htop` cannot be dropped
(without it both sides may be `⊤` and any `j` is "on side"); `0 < ℓ` cannot be dropped (`ℓ = 0`
makes `OnSide` say `u*j = suppVal` and the conclusion is vacuous but the proof's step 1 fails);
`Nat.Coprime u ℓ` cannot be weakened to `0 < u`.

**SOURCE.** `EFF.HE3.14` verbatim ("lattice abscissas `j₀ + ℓk` (`k = 0, …, d_λ`)");
`EFF.HE6.52` (the tooth); `EFF.HE3.13` ("slope `λ = u/ℓ` **in lowest terms**").

**TEETH.** `HE6-T-BADKEY` (`EFF.HE6.52`) → **Lean theorem** (the tooth's content — that coprimality
is necessary — is here the necessity of a hypothesis, and the *sufficiency* is this theorem).

**ENVIRONMENT.** ENV-A.

---

### NODE B.18 [lemma] [fresh]

**STATEMENT.** *The support value is attained, and its finiteness criterion.* Let `φ` be monic with
`0 < deg φ` and let `f` be monic with `f.natDegree = μ * φ.natDegree`. Then

* `suppVal φ f u ℓ ≠ ⊤` for every `u ℓ`, and in fact `suppVal φ f u ℓ ≤ (u * μ : ℕ)`;
* there exists `j ≤ f.natDegree` with `OnSide φ f u ℓ j` (the `inf` is attained);
* `sideSet φ f u ℓ` is nonempty.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem suppVal_ne_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) (u ℓ : ℕ) :
    suppVal φ f u ℓ ≤ ((u * μ : ℕ) : ℕ∞)

theorem sideSet_nonempty {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) (u ℓ : ℕ) :
    (sideSet φ f u ℓ).Nonempty
```

**DEPENDS.** B.13 · B.14 · B.16 · mathlib `Finset.inf_le`, `Finset.exists_mem_eq_inf`
(**confirm**: for a `Finset` in a `LinearOrder` with `OrderTop`, the `inf` over a nonempty `Finset`
is attained; the pinned name may be `Finset.exists_mem_eq_inf'` on `inf'`, in which case convert
with `Finset.inf'_eq_inf`).

**PROOF.**
1. `suppVal_ne_top`: `μ ≤ f.natDegree` when `0 < φ.natDegree` (from `hdeg`, by `Nat.le_mul_of_pos_right`
   — and when `μ = 0` the bound is `0 ≤ 0`), so `μ ∈ Finset.range (f.natDegree + 1)`; `Finset.inf_le`
   at `j = μ` gives `suppVal ≤ ℓ • npHgt φ f μ + u*μ = ℓ • 0 + u*μ = u*μ` by B.13's `npHgt_top`.
2. `sideSet_nonempty`: `Finset.range (f.natDegree + 1)` is nonempty, so the `inf` is attained at some
   `j` in it; that `j` satisfies `OnSide` by definition and hence lies in the filter.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE3.13` (`A_μ = 1` is what makes the polygon's right end finite);
`EFF.HE6.30`(a) (the length argument `Σ_λ L_λ = μ`, whose premise is this finiteness).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-A.

---

### NODE B.19 [lemma] [fresh]

**STATEMENT.** *Two distinct slopes share at most one abscissa (the vertex property).* Let `0 < ℓ`,
`0 < ℓ'`, `suppVal φ f u ℓ ≠ ⊤`, `suppVal φ f u' ℓ' ≠ ⊤`, and `u * ℓ' ≠ u' * ℓ` (the two slopes
`u/ℓ` and `u'/ℓ'` are distinct). If `j` and `j'` are both on the `(u,ℓ)`-side **and** both on the
`(u',ℓ')`-side, then `j = j'`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem eq_of_onSide_onSide (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') {φ f : Polynomial O} {u u' j j' : ℕ}
    (hne : u * ℓ' ≠ u' * ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (htop' : suppVal φ f u' ℓ' ≠ ⊤)
    (hj : OnSide φ f u ℓ j) (hj' : OnSide φ f u ℓ j')
    (hk : OnSide φ f u' ℓ' j) (hk' : OnSide φ f u' ℓ' j') : j = j'
```

**DEPENDS.** B.11 · B.14 · B.16 · B.17's private helper `onSide_nat_eq` · mathlib `Int` arithmetic.

**PROOF.**
1. As in B.17 steps 1–2, extract `H := npHgt φ f j` and `H' := npHgt φ f j'` as naturals and the two
   `ℕ`-equalities `ℓ*H + u*j = ℓ*H' + u*j'` and `ℓ'*H + u'*j = ℓ'*H' + u'*j'`.
2. In `ℤ`: `ℓ*(H − H') = u*(j' − j)` and `ℓ'*(H − H') = u'*(j' − j)`.
3. Multiply the first by `ℓ'` and the second by `ℓ`: `ℓ'*u*(j' − j) = ℓ*u'*(j' − j)`, i.e.
   `(u*ℓ' − u'*ℓ)*(j' − j) = 0`.
4. `hne` gives `(u*ℓ' − u'*ℓ : ℤ) ≠ 0`, so `j' − j = 0` by `mul_eq_zero`, i.e. `j = j'`
   (`Int.natCast_inj`).

**SIZE.** 16 lines.

**WHY THIS REPLACES THE HULL.** In the `Finset (ℕ × ℕ)` representation the analogous fact is the
vertex/collinearity bookkeeping that `HullStability.lean` spends 1744 lines on, and whose naive form
is **provably false** (`NewtonPolygon.lean:784`, `npVertices_not_stable_of_hull_preserved`, witness
`S = {(0,0),(1,0)}`, `S' = {(0,0)}`). Here it is sixteen lines of `ℤ`-arithmetic with no
representation to stabilise. This node is DECISION D-1's **criterion-C5 certificate** and the largest
single piece of evidence for the decision; if it fails, the decision's canonicity claim is empty.

**SOURCE.** `EFF.HE3.13` ("each side has a `dv`-slope … in lowest terms"); `EFF.HE6.10`.

**TEETH.** signed non-applicable as a battery item; internal decision evidence (see above).

**ENVIRONMENT.** ENV-A.

---

### NODE B.20 [def] [fresh]

**STATEMENT.** *The side's numerical data.* For `0 < ℓ` and `Nat.Coprime u ℓ`, with
`suppVal φ f u ℓ ≠ ⊤`, define the side's **left endpoint** `sideMin := (sideSet φ f u ℓ).min'`, its
**right endpoint** `sideMax := (sideSet φ f u ℓ).max'`, its **length**
`sideLen := sideMax − sideMin`, and its **residual degree** `sideDeg := sideLen / ℓ`. By B.17,
`ℓ ∣ sideLen`, so `sideLen = ℓ * sideDeg` exactly; and the on-side abscissae are contained in
`{sideMin + ℓ*k | k ≤ sideDeg}`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

noncomputable def sideMin (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideSet φ f u ℓ).min' h

noncomputable def sideMax (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideSet φ f u ℓ).max' h

noncomputable def sideDeg (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideMax φ f u ℓ h - sideMin φ f u ℓ h) / ℓ

theorem sideMax_eq (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) :
    sideMax φ f u ℓ h = sideMin φ f u ℓ h + ℓ * sideDeg φ f u ℓ h

theorem onSide_eq_add_mul (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {j : ℕ}
    (hj : j ∈ sideSet φ f u ℓ) :
    ∃ k ≤ sideDeg φ f u ℓ h, j = sideMin φ f u ℓ h + ℓ * k
```

**DEPENDS.** B.16 · B.17 · B.18 · mathlib `Finset.min'_le`, `Finset.le_max'`,
`Nat.ModEq`, `Nat.div_mul_cancel`.

**PROOF.**
1. `sideMax_eq`: `sideMin ≤ sideMax` (`Finset.min'_le_max'`), and `ℓ ∣ (sideMax − sideMin)` by B.17
   applied to the two members `sideMin`, `sideMax` (both are in `sideSet`, hence `OnSide`), so
   `Nat.div_mul_cancel` gives the identity.
2. `onSide_eq_add_mul`: for `j ∈ sideSet`, `sideMin ≤ j ≤ sideMax`, and `ℓ ∣ (j − sideMin)` by B.17;
   set `k := (j − sideMin)/ℓ`; then `j = sideMin + ℓ*k` by `Nat.div_mul_cancel` and `k ≤ sideDeg`
   from `j ≤ sideMax` and step 1 by `omega` after clearing `ℓ`.

**SIZE.** 26 lines. **Five public declarations, three of them definitions** — this is one *object*
(the side's numerical data) and splitting it across files would force every consumer to import three
modules for one triple. If the merge queue objects, the split boundary is `{sideMin, sideMax,
sideDeg}` in `B20a.lean` and `{sideMax_eq, onSide_eq_add_mul}` in `B20b.lean`. **SPLIT CANDIDATE.**

**FAITHFULNESS.** `EFF.HE3.13` verbatim: "each side has a `dv`-slope `λ = u/ℓ` in lowest terms
(`u, ℓ > 0`), horizontal length `L_λ = ℓ·d_λ`, and a residual polynomial `R_λ ∈ K[Z]` of degree
`d_λ`". `sideLen` is `L_λ` and `sideDeg` is `d_λ`. `EFF.HE3.14` verbatim: "the side of `P(F)` with
slope `λ = u/ℓ` in lowest terms, left endpoint `(j₀, κ₀)`, lattice abscissas `j₀ + ℓk`
(`k = 0, …, d_λ`)" — `sideMin` is `j₀` and `suppVal` is `ℓκ₀ + u j₀`. `L_v` of `EFF.W12.83`
("`L_v = #{j < m_v : P_v(j) ∈ ℤ}`", the "priced digits") is the **count** `(sideSet).card`, which is
`≤ sideDeg + 1` and equals it exactly when every on-side lattice abscissa carries a point; the
count is chapter C/H's object and the inequality is all this chapter needs. **Flagged for human
review.**

**SOURCE.** `EFF.HE3.13`; `EFF.HE3.14`; `EFF.W12.83`; `EFF.HE6.10`.

**TEETH.** `W12-SHAPE` (`EFF.W12.54`, 23 rows, both directions — every row is a
`(polygon, residual, count, σ)` tuple keyed by exactly this data) → **executable regression**
retained.

**ENVIRONMENT.** ENV-A.

---

## 4. §4 — THE ORDER-1 RESIDUAL FIELD AND THE RESIDUAL POLYNOMIAL

### NODE B.21 [def] [fresh]

**STATEMENT.** *The digit at a height.* For `π : O`, `k : ℕ` and `x : O`, define
`digAt π k x : ResidueField O` to be the residue class of the unique `y` with `x = π^k * y` when
`π^k ∣ x`, and `0` otherwise. (Uniqueness of `y` holds because `O` is a domain and `π^k ≠ 0`; the
`otherwise` branch is junk and no lemma reads it.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `digAt π k x` : the residue of `x / π ^ k` when `π ^ k ∣ x` (junk `0` otherwise) — the "digit of
`x` at height `k`" of the corpus's digit calculus. -/
noncomputable def digAt (π : O) (k : ℕ) (x : O) : ResidueField O :=
  open Classical in if h : π ^ k ∣ x then IsLocalRing.residue O h.choose else 0
```

**DEPENDS.** none (mathlib `IsLocalRing.residue`, `Dvd.dvd.choose`).

**PROOF.** definitional.

**FAITHFULNESS.** `EFF.W12.23` verbatim: "Each `a_j` is a free module of `N` digit-slots over the
residue `F_q`-space `F_q^d ≅ F_{q^d}` … write `digit_h(a_j) ∈ F_{q^d}` for the slot at height `h`
(**the GMN order-1 residual-coefficient convention**)". This node is the scalar half of `digit_h`
(the `F_q`-level digit); B.23 assembles the polynomial and B.28 pushes it into `F_{q^d}`. The corpus's
`digit_h` is the *slot*, i.e. it is read at a height that need not be the element's own valuation —
which is exactly why `digAt` takes `k` as an argument rather than computing it: `EFF.HE3.14`'s
residual coefficient is `0` "whenever the pin at `j₁+tℓ` lies strictly above the `λ`-line", and that
is `digAt π k x = 0` with `k` the LINE height and `v(x) > k`. **Flagged for human review.**

**SIZE.** 6 lines.

**SOURCE.** `EFF.W12.23`; `EFF.HE3.14`; `EFF.HE6.13` (`LEMMA HE6-1L`'s reachable-residue set is a
statement about exactly this map's image).

**TEETH.** `HE6R1-LIFT2` (`EFF.HE6R1.27`, 5 exhaustive frames; the reachable-set question is about
`digAt`'s image) → **executable regression** retained: `(LIFT₂)`'s threshold is disclosed
**sufficient, not sharp** (`EFF.HE6R1.46`, "non-sharp by exactly 1 in every tested frame"), so no
Lean theorem is claimed for the sharp form.

**ENVIRONMENT.** ENV-A.

---

### NODE B.22 [lemma] [fresh]

**STATEMENT.** *The digit's specification.* For `hπ : Irreducible π`:

* if `x = π^k * y` then `digAt π k x = residue O y` (well-definedness);
* if `π^k ∣ x` then `digAt π k x = 0 ↔ π^(k+1) ∣ x` (the digit detects exactness);
* `digAt π k (x + x') = digAt π k x + digAt π k x'` when `π^k ∣ x` and `π^k ∣ x'`;
* `digAt π 0 x = residue O x`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem digAt_eq (hπ : Irreducible π) {k : ℕ} {x y : O} (h : x = π ^ k * y) :
    digAt π k x = IsLocalRing.residue O y

theorem digAt_eq_zero_iff (hπ : Irreducible π) {k : ℕ} {x : O} (h : π ^ k ∣ x) :
    digAt π k x = 0 ↔ π ^ (k + 1) ∣ x

theorem digAt_add (hπ : Irreducible π) {k : ℕ} {x x' : O} (h : π ^ k ∣ x) (h' : π ^ k ∣ x') :
    digAt π k (x + x') = digAt π k x + digAt π k x'

theorem digAt_zero (x : O) : digAt π 0 x = IsLocalRing.residue O x
```

**DEPENDS.** B.21 · mathlib `mul_left_cancel₀`, `IsLocalRing.residue`,
`Ideal.Quotient.eq_zero_iff_mem`, `Irreducible.maximalIdeal_eq`, `pow_ne_zero`.

**PROOF.**
1. `digAt_eq`: `π^k ∣ x` from `h`, so the `dif_pos` branch fires with some `y'` and
   `π^k * y' = x = π^k * y`; `mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero)` gives `y' = y`.
2. `digAt_eq_zero_iff`: write `x = π^k * y` (from `h`); by step 1 the digit is `residue O y`, which is
   `0` iff `y ∈ maximalIdeal O` iff `π ∣ y` (`hπ.maximalIdeal_eq`, `Ideal.mem_span_singleton`) iff
   `π^(k+1) ∣ π^k*y = x` (again by `mul_left_cancel₀` for the ← direction).
3. `digAt_add`: write `x = π^k*y`, `x' = π^k*y'`; then `x + x' = π^k*(y+y')`; apply step 1 three times
   and `map_add`.
4. `digAt_zero`: `π^0 = 1 ∣ x` and `x = 1 * x`, so step 1 with `y = x`.

**SIZE.** 24 lines. **Four public declarations** — the digit API is one object and every consumer
needs at least two of the four; `digAt_zero` is the one a merge queue may reasonably ask to inline.

**SOURCE.** `EFF.W12.23`; `EFF.HE3.14`.

**TEETH.** `HE-NORM`, `HE-PSI` → **Lean theorem** (the digit read becomes a theorem rather than a
convention).

**ENVIRONMENT.** ENV-A'.

---

### NODE B.23 [def] [fresh]

**STATEMENT.** *The digit polynomial.* For `π : O`, `k : ℕ` and `a ∈ O[X]`, define
`digPoly π k a : (ResidueField O)[X] = Σ_{i ≤ a.natDegree} C (digAt π k (a.coeff i)) * X^i`.
When `(k : ℕ∞) ≤ gaussVal a` this is the reduction of `a / π^k`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `digPoly π k a` : the coefficientwise digit of `a` at height `k`, as a polynomial over the
residue field. When `π ^ k` divides every coefficient of `a`, this is `(a / π ^ k) mod π`. -/
noncomputable def digPoly (π : O) (k : ℕ) (a : Polynomial O) : Polynomial (ResidueField O) :=
  ∑ i ∈ Finset.range (a.natDegree + 1), Polynomial.C (digAt π k (a.coeff i)) * Polynomial.X ^ i
```

**DEPENDS.** B.21.

**PROOF.** definitional.

**SIZE.** 6 lines.

**SOURCE.** `EFF.W12.23`; `EFF.HE3.14`.

**TEETH.** signed non-applicable (a definition).

**ENVIRONMENT.** ENV-A.

---

### NODE B.24 [lemma] [fresh]

**STATEMENT.** *The digit polynomial's specification.* For `hπ : Irreducible π` and `a ∈ O[X]`:

* `(digPoly π k a).coeff i = digAt π k (a.coeff i)` for every `i`;
* `(digPoly π k a).degree ≤ a.degree`;
* if `(k : ℕ∞) ≤ gaussVal a` and `a = C (π^k) * b` then `digPoly π k a = b.map (residue O)`;
* if `(k : ℕ∞) ≤ gaussVal a` then `digPoly π k a = 0 ↔ (k+1 : ℕ∞) ≤ gaussVal a`. In particular for
  `a ≠ 0` and `k` with `gaussVal a = (k : ℕ∞)`, `digPoly π k a ≠ 0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem digPoly_coeff (hπ : Irreducible π) (k i : ℕ) (a : Polynomial O) :
    (digPoly π k a).coeff i = digAt π k (a.coeff i)

theorem degree_digPoly_le (k : ℕ) (a : Polynomial O) : (digPoly π k a).degree ≤ a.degree

theorem digPoly_eq_map (hπ : Irreducible π) {k : ℕ} {a b : Polynomial O}
    (h : a = Polynomial.C (π ^ k) * b) : digPoly π k a = b.map (IsLocalRing.residue O)

theorem digPoly_eq_zero_iff (hπ : Irreducible π) {k : ℕ} {a : Polynomial O}
    (h : (k : ℕ∞) ≤ gaussVal a) : digPoly π k a = 0 ↔ ((k + 1 : ℕ) : ℕ∞) ≤ gaussVal a
```

**DEPENDS.** B.08 · B.21 · B.22 · B.23 · landed `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow`
(`HenselFactorization.lean:175`) · mathlib `Polynomial.ext_iff`,
`Polynomial.coeff_eq_zero_of_natDegree_lt`.

**PROOF.**
1. `digPoly_coeff`: landed `coeff_sum_range_C_mul_X_pow` gives the value
   `if i < a.natDegree + 1 then digAt π k (a.coeff i) else 0`; for `i > a.natDegree`,
   `a.coeff i = 0` and `digAt π k 0 = 0` (from B.22's `digAt_eq` with `y = 0`).
2. `degree_digPoly_le`: `Polynomial.degree_le_iff_coeff_zero` plus step 1 and
   `coeff_eq_zero_of_natDegree_lt`.
3. `digPoly_eq_map`: coefficientwise by step 1 — `a.coeff i = π^k * b.coeff i` (from `h` and
   `coeff_C_mul`), so B.22's `digAt_eq` gives `residue O (b.coeff i) = (b.map (residue O)).coeff i`
   (`coeff_map`).
4. `digPoly_eq_zero_iff`: by step 1 and `Polynomial.ext_iff`, `digPoly π k a = 0` iff
   `digAt π k (a.coeff i) = 0` for all `i`, iff `π^(k+1) ∣ a.coeff i` for all `i` (B.22's
   `digAt_eq_zero_iff`, whose hypothesis `π^k ∣ a.coeff i` comes from `h` via B.08's
   `le_gaussVal_iff`), iff `(k+1 : ℕ∞) ≤ gaussVal a` (B.08 again).

**SIZE.** 28 lines. **Four public declarations**, same justification as B.22.

**SOURCE.** `EFF.W12.23` (the three-way slot-membership law); `EFF.HE3.14`.

**TEETH.** `W12-SHAPE` → **Lean theorem** (the "digit at the polygon height is nonzero at a vertex"
half of `EFF.W12.23`'s membership law).

**ENVIRONMENT.** ENV-A'.

---

### NODE B.25 [def] [fresh]

**STATEMENT.** *The order-1 residual field.* For an order-1 key `φ` define
`resField φ := AdjoinRoot (φ.map (residue O))`, the quotient `F[y]/(φ̄)`. Since `φ̄` is irreducible,
`resField φ` is a field, and it is an `F`-algebra of degree `m = φ.natDegree`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `resField φ = F[y]/(φ̄)` : the order-1 residual field of the key `φ`. -/
abbrev resField (φ : Polynomial O) : Type _ := AdjoinRoot (φ.map (IsLocalRing.residue O))

noncomputable instance instFieldResField {φ : Polynomial O} (hφ : IsKey φ) :
    Field (resField φ) := AdjoinRoot.instField (hf := hφ.irred.ne_zero) -- see PROOF note

/-- The residual reduction `O[X] → resField φ` at height `k`. -/
noncomputable def resMk (π : O) (φ : Polynomial O) (k : ℕ) (a : Polynomial O) : resField φ :=
  AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) (digPoly π k a)
```

**DEPENDS.** B.01 · B.23 · mathlib `AdjoinRoot`, `AdjoinRoot.instField` / `AdjoinRoot.span_maximal_of_irreducible`
(**confirm the pinned route to the `Field` instance**: mathlib provides `Fact (Irreducible p) →
Field (AdjoinRoot p)` as `AdjoinRoot.instField`; the idiomatic use is
`haveI : Fact (Irreducible (φ.map (residue O))) := ⟨hφ.irred⟩` inside each consuming proof, and the
instance is then found by TC. **If so, the `instFieldResField` declaration above is replaced by a
`Fact`-producing `instance` or by a local `haveI` in each consumer, and this node's SIGNATURE drops
to the `abbrev` plus `resMk`.**)

**PROOF.** definitional, modulo the instance route named in DEPENDS. Note that `resField` must be an
`abbrev` (not a `def`) so that the `Field`/`Algebra F` instances found for
`AdjoinRoot (φ.map (residue O))` apply to it without re-declaration.

**FAITHFULNESS.** `docs/GMN_citations.md` Def 1.21 verbatim: "the order-1 residue field
`F_φ := F[y]/(ψ₀(y))`". `EFF.HE6.08` gives it as `K := F_Q(η_θ) ≅ F_{Q^{f₁}}`, i.e. as a subfield of
`k̄` generated by a residue — at `e₁ = 1` the two presentations agree because `η_θ = res(θ)` is a root
of `φ̄` (`EFF.HE6.08`'s `η_θ := res(θ^{e₁}π^{−h})` degenerates to `res(θ)` at `e₁ = 1, h = 0`).
**This chapter uses the quotient presentation and never the subfield presentation** — the subfield
presentation needs an ambient `k̄` and the embeddings `ι_ξ`, which H-1 puts out of scope.
**Flagged for human review.**

**SIZE.** 10 lines.

**SOURCE.** `docs/GMN_citations.md` Def 1.21, fact (I); `EFF.HE6.08`; `EFF.HE3.13`
(`R_λ ∈ K[Z]` with `K` the order-1 residue field).

**TEETH.** `HE6R1-T-BASIS` (`EFF.HE6R1.29`, "`{1, β}` is a K-basis of `K₂` — load-bearing", fired) →
**executable regression** retained at the level-2 analogue; this node is its level-1 base.

**ENVIRONMENT.** ENV-A.

---

### NODE B.26 [lemma] [fresh]

**STATEMENT.** *The residual field is finite of the right size.* For an order-1 key `φ` with
`m := φ.natDegree`, over the standing bundle with finite residue field:
`Module.finrank F (resField φ) = m` and `Nat.card (resField φ) = residueCard O ^ m`; and
`Finite (resField φ)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem finrank_resField {φ : Polynomial O} (hφ : IsKey φ) :
    Module.finrank (ResidueField O) (resField φ) = φ.natDegree

noncomputable instance instFiniteResField {φ : Polynomial O} (hφ : IsKey φ) :
    Finite (resField φ)

theorem card_resField {φ : Polynomial O} (hφ : IsKey φ) :
    Nat.card (resField φ) = residueCard O ^ φ.natDegree
```

**DEPENDS.** B.01 · B.25 · landed `Uniformity.Density.residueCard` (`LocalData.lean:72`) ·
mathlib `AdjoinRoot.powerBasis`, `PowerBasis.finrank`, `Polynomial.natDegree_map_eq_of_monic`
(or `Monic.natDegree_map`), `Module.card_eq_pow_finrank` (**confirm the pinned name**; the fact is
`#V = #F ^ finrank F V` for a finite-dimensional space over a finite field — in the pin it is
`Module.card_eq_pow_finrank` or `Module.card_fintype`; if neither, the fallback is
`Nat.card_congr (AdjoinRoot.powerBasis _).basis.equivFun.toEquiv` followed by
`Nat.card_fun`/`card_pi`).

**PROOF.**
1. `(φ.map (residue O)).natDegree = φ.natDegree` by `Monic.natDegree_map hφ.monic`.
2. `AdjoinRoot.powerBasis` (needs `φ̄ ≠ 0`, from `hφ.irred.ne_zero`) has dimension
   `(φ.map (residue O)).natDegree`; `PowerBasis.finrank` gives `finrank_resField`.
3. `Finite`: the power basis gives a linear equivalence with `Fin m → F`, and `F` is finite by the
   bundle's `[Finite (ResidueField O)]`; `Finite.of_equiv`.
4. `card_resField`: `Module.card_eq_pow_finrank` with steps 2 and 3, and
   `residueCard O = Nat.card (ResidueField O)` by definition.

**SIZE.** 22 lines.

**⚠ THIS NODE IS NS-4 (`docs/GMN_citations.md` fact (I)) AT ORDER 1.** The resolution doc's verdict
is `COVERS-ALL-O` with the note "**Finiteness** is then immediate and characteristic-free — it
follows from `F` finite, which is our hypothesis, not theirs." That is exactly steps 3–4.

**SOURCE.** `docs/GMN_citations.md` fact (I), NS-4; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-4;
`EFF.W12.25` (the residual censuses are stated over `Q = q^d`, i.e. over this field).

**TEETH.** `W12-CENSUS4` (`EFF.W12.57`, fires 8×; the censuses `S_λ(Q)` are polynomial in
`Q = q^d = card (resField φ)`) → **Lean theorem** (the identification `Q = q^m` becomes a theorem).

**ENVIRONMENT.** ENV-C.

---

### NODE B.27 [lemma] [fresh]

**STATEMENT.** *Separability over the residual field.* Let `K` be a finite field. Then every
irreducible `p ∈ K[y]` is separable, and for any `p ≠ 0`: `p.Separable ↔ Squarefree p`. Consequently
for a monic `R ∈ K[y]` of positive degree, `R.Separable` iff every monic irreducible factor of `R`
occurs with multiplicity `1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem irreducible_separable {K : Type*} [Field K] [Finite K] {p : Polynomial K}
    (hp : Irreducible p) : p.Separable

theorem separable_iff_squarefree {K : Type*} [Field K] [Finite K] {p : Polynomial K}
    (hp : p ≠ 0) : p.Separable ↔ Squarefree p
```

**DEPENDS.** mathlib `Irreducible.separable` (needs `PerfectField K`; a finite field is perfect —
**confirm the pinned instance name**, `PerfectField.ofFinite` or via `ExpChar`/`PerfectRing`),
`Polynomial.separable_iff_squarefree` (**confirm**: in the pin the equivalence
`Separable ↔ Squarefree` holds over a perfect field; if the pin only has
`Polynomial.Squarefree.separable`-style one-directional lemmas, the missing direction for a finite
field is `Polynomial.separable_of_squarefree` over a perfect field — record whichever the pin has and
prove the other from `EuclideanDomain.gcd`-based `Separable` unfolding).

**PROOF.**
1. `Finite K → PerfectField K` (mathlib instance; a finite field is perfect since Frobenius is
   surjective by injectivity plus finiteness).
2. `irreducible_separable`: `Irreducible.separable` over a perfect field.
3. `separable_iff_squarefree`: the pinned equivalence over a perfect field.

**SIZE.** 10 lines. If the pin's names differ this node grows to ~30 lines and becomes the place the
Frobenius-surjectivity argument lands; it is still a single unit.

**⚠ WHY THIS IS A NODE AND NOT A `simp` STEP.** `docs/GMN_citations.md` fact (I)'s parenthetical is
the whole reason: "**finite fields are perfect at every `r`, so 'needs descent = non-squarefree =
discriminant locus' with no inseparable-irreducible exceptions in any characteristic**". The
`Separable ↔ Squarefree` bridge is what makes NS-6 (B.63/B.64) a statement about **multiplicities**
rather than about derivatives, and it is the single place the chapter uses finiteness of the residue
field for anything other than counting.

**SOURCE.** `docs/GMN_citations.md` fact (I); `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6;
`EFF.W12.27` ("If every residual is separable"); `EFF.HE3.15` ("every TERMINAL residual polynomial
separable").

**TEETH.** `HEX3`-side separability rows are chapter G's; here **signed non-applicability** as a
battery item (a residue-field algebra fact, characteristic-uniform as a theorem).

**ENVIRONMENT.** ENV-D + `[Finite K]`.

---

### NODE B.28 [def] [fresh]

**STATEMENT.** *The residual coefficients of a side.* Fix an order-1 key `φ`, a polynomial `f`,
`u ℓ : ℕ` with `0 < ℓ` and `Nat.Coprime u ℓ`, and a nonemptiness witness `h` for
`sideSet φ f u ℓ`. Write `j₀ := sideMin φ f u ℓ h`, `d := sideDeg φ f u ℓ h`, and let `H₀ : ℕ` be the
natural number with `npHgt φ f j₀ = (H₀ : ℕ∞)` (it exists: `j₀` is on the side and the support value
is finite). The **`k`-th residual coefficient** (`k ≤ d`) is

```
resCoeff k := resMk π φ (H₀ - u * k) (dev φ f (j₀ + ℓ * k))  ∈  resField φ,
```

i.e. the digit of the `(j₀ + ℓk)`-th development coefficient read at the **line** height `H₀ − u·k`,
pushed into the residual field. It is `0` exactly when the point at abscissa `j₀ + ℓk` lies strictly
above the `(u,ℓ)`-line.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `resCoeff` : the `k`-th residual coefficient of the `(u,ℓ)`-side of `f`'s `φ`-adic polygon. -/
noncomputable def resCoeff (π : O) (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) (H₀ k : ℕ) : resField φ :=
  resMk π φ (H₀ - u * k) (dev φ f (sideMin φ f u ℓ h + ℓ * k))
```

**DEPENDS.** B.02 · B.11 · B.16 · B.20 · B.23 · B.25.

**PROOF.** definitional. **The height is `H₀ − u·k`, not `npHgt φ f (j₀ + ℓk)`** — this is the whole
content of the definition and it is the difference between the *line* and the *point*. `H₀` is passed
as an explicit argument rather than extracted from `npHgt` inside the definition, because extracting
it needs the finiteness proof and a definition must not carry a proof obligation; B.29's consumer
supplies it and B.30 pins it.

**FAITHFULNESS.** `EFF.HE3.14` verbatim (the coherent-construction pin): "For the side of `P(F)` with
slope `λ = u/ℓ` in lowest terms, left endpoint `(j₀, κ₀)`, lattice abscissas `j₀ + ℓk`
(`k = 0, …, d_λ`; the line heights `κ₀ − ku ∈ ℤ`): `R_λ(Z) := Σ_{k=0}^{d_λ} res(A_{j₀+ℓk}(θ) ·
n(u)(θ)^k / n(κ₀)(θ)) · Z^k`." At `e₁ = 1` the normalizer system `n(·)` is the pure power
`n(k) = π^k` (`EFF.HE6.13`'s `n(k) := x^{i₀(k)}π^{(k−i₀(k)h)/e₁}` with `i₀ = 0, h = 0`), so the
argument of `res` is `A_{j₀+ℓk} · π^{uk} / π^{κ₀} = A_{j₀+ℓk} / π^{κ₀−uk}` — verbatim this node with
`κ₀ = H₀`. **The `ϖ`-vs-`n(k)` discrepancy and its coset factor `η_θ^{−q(k)}` (`EFF.HE6.13` RIDER,
`EFF.HE6.15` as corrected by `EFF.HE6.58`) are invisible at `e₁ = 1`, where `q(k) = 0` and
`ϖ = π = n(1)`.** That is H-1's scope claim made concrete, and it is §14 item 4.
**Flagged for human review.**

**SIZE.** 8 lines.

**SOURCE.** `EFF.HE3.14` (the coherent construction — and note `EFF.HE3.24` records THE WITNESS: a
PARI-adjudicated flip between the *naive* and the *coherent* `R_λ` at `(e₁,f₁) = (2,2)`, i.e. the
naive normalization is **wrong** at `e₁ ≥ 2`; this chapter is at `e₁ = 1` where the two agree, and
that is exactly why the chapter may use the simple form); `EFF.HE6.11`; `EFF.W12.23`.

**TEETH.** THE WITNESS (`EFF.HE3.24`) → **signed non-applicability at `e₁ = 1`**, with the reason
recorded above: the witness distinguishes naive from coherent normalization only when `e₁ ≥ 2`, and
`e₁ = 1` is out of its scope by construction. **This is the chapter's most delicate teeth
disposition and it is §14 item 4.**

**ENVIRONMENT.** ENV-A.

---

### NODE B.29 [def] [fresh]

**STATEMENT.** *The residual polynomial.* With the data of B.28,
`resPoly := Σ_{k ≤ d} C (resCoeff k) * Y^k ∈ (resField φ)[Y]`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `resPoly π φ f u ℓ h H₀` : the residual polynomial `R_{u/ℓ}(f) ∈ (resField φ)[Y]`. -/
noncomputable def resPoly (π : O) (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ) : Polynomial (resField φ) :=
  ∑ k ∈ Finset.range (sideDeg φ f u ℓ h + 1),
    Polynomial.C (resCoeff π φ f u ℓ h H₀ k) * Polynomial.X ^ k
```

**DEPENDS.** B.20 · B.28.

**PROOF.** definitional.

**FAITHFULNESS.** `EFF.HE3.13`: "a residual polynomial `R_λ ∈ K[Z]` of degree `d_λ` with
`R_λ(0) ≠ 0`". `docs/GMN_citations.md` Def 2.21 (at order 1): "`R_{λ}(f)(y) := c_s + c_{s+e} y + … +
c_{s+de} y^d ∈ F_r[y]`, a monic (after normalization) degree-`d` polynomial … `c_s` and `c_{s+de}`
are always nonzero, so `R_λ(f)` has degree `d` and is never divisible by `y`". **This node does NOT
normalize to monic**: the corpus's "monic after normalization" is a choice of representative in the
`K^×`-scaling orbit, and the two facts every consumer needs — `degree = d` and `coeff 0 ≠ 0` — are
scaling-invariant and are B.30. Monicity would force a division and buys nothing; the *factorization*
statements (B.48, B.63) are stated up to units, exactly as `EFF.HE3.32`'s `R_λ = Π_r r^{m_r}` is.
**Flagged for human review.**

**SIZE.** 8 lines.

**SOURCE.** `EFF.HE3.13`; `EFF.HE3.14`; `docs/GMN_citations.md` Def 2.21; `EFF.HE6.11`.

**TEETH.** `W12-SHAPE`, `HE-SIG` → **executable regression** retained (the batteries read `R_λ`'s
factorization type per row).

**ENVIRONMENT.** ENV-A.

---

### NODE B.30 [lemma] [fresh]

**STATEMENT.** *The residual polynomial has degree `d` and nonzero constant term.* With the data of
B.28, assume additionally `hφ : IsKey φ`, `hπ : Irreducible π`, `suppVal φ f u ℓ ≠ ⊤`, and that `H₀`
is correct (`npHgt φ f (sideMin …) = (H₀ : ℕ∞)`). Then

* `resCoeff k = 0 ↔ ¬ OnSide φ f u ℓ (j₀ + ℓ*k)` for every `k ≤ d`;
* `resCoeff 0 ≠ 0` and `resCoeff d ≠ 0`;
* `(resPoly …).natDegree = d` and `(resPoly …).coeff 0 ≠ 0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem resCoeff_eq_zero_iff (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) {k : ℕ} (hk : k ≤ sideDeg φ f u ℓ h) :
    resCoeff π φ f u ℓ h H₀ k = 0 ↔ ¬ OnSide φ f u ℓ (sideMin φ f u ℓ h + ℓ * k)

theorem natDegree_resPoly (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) :
    (resPoly π φ f u ℓ h H₀).natDegree = sideDeg φ f u ℓ h ∧
      (resPoly π φ f u ℓ h H₀).coeff 0 ≠ 0
```

**DEPENDS.** B.03 · B.08 · B.11 · B.16 · B.20 · B.24 · B.25 · B.28 · B.29 · B.36 (the slot lemma —
**this is a forward dependency inside §5 and it is deliberate**: B.36 needs only B.03/B.08/B.24/B.25,
not this node, so the DAG stays acyclic; the topological order is B.36 before B.30) ·
landed `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow`.

**PROOF.**
1. The line height at `j_k := j₀ + ℓk` is `H₀ − u·k`, and `H₀ − u·k ≤ npHgt φ f j_k` always: from
   `OnSide … j₀` and `Finset.inf_le` at `j_k`,
   `ℓ*H₀ + u*j₀ = suppVal ≤ ℓ • npHgt φ f j_k + u*j_k`, and `u*j_k = u*j₀ + u*ℓ*k`, so
   `ℓ*(H₀ − u*k) ≤ ℓ • npHgt φ f j_k`, hence the claim after cancelling `ℓ > 0`.
   (Do the `ℕ∞` arithmetic by cases on `npHgt φ f j_k = ⊤`.)
2. Equality in step 1 holds iff `OnSide φ f u ℓ j_k`, by the same computation read backwards.
3. `resCoeff_eq_zero_iff`: `resCoeff k = AdjoinRoot.mk φ̄ (digPoly π (H₀−u*k) (dev φ f j_k))`. By
   B.36 (the slot lemma) applied to `a := dev φ f j_k` — whose degree is `< φ.degree` by B.03 — the
   class `AdjoinRoot.mk φ̄ (digPoly π c a)` is `0` iff `digPoly π c a = 0`. By B.24's
   `digPoly_eq_zero_iff` (whose hypothesis `(c : ℕ∞) ≤ gaussVal a` is step 1) that is
   `(c+1 : ℕ∞) ≤ gaussVal a = npHgt φ f j_k`, i.e. strict inequality in step 1, i.e. `¬ OnSide` by
   step 2.
4. `resCoeff 0 ≠ 0`: `k = 0` gives `j_0 = j₀`, which IS on side (`Finset.min'_mem`); apply step 3.
5. `resCoeff d ≠ 0`: `j_d = sideMax` by B.20's `sideMax_eq`, which is on side
   (`Finset.max'_mem`); apply step 3.
6. `natDegree_resPoly`: `(resPoly).coeff k = resCoeff k` for `k ≤ d` and `0` above
   (`coeff_sum_range_C_mul_X_pow`); with step 5 the leading coefficient is nonzero, so the
   `natDegree` is `d`; with step 4 the constant coefficient is nonzero.

**SIZE.** 34 lines. **SPLIT CANDIDATE** at step 3/step 6 (`resCoeff_eq_zero_iff` in `B30a.lean`,
`natDegree_resPoly` in `B30b.lean`); steps 1–2's `ℕ∞` arithmetic is the largest piece and belongs
with step 3.

**⚠ THIS NODE IS `docs/GMN_citations.md` Def 2.21's LOAD-BEARING CLAUSE, AT ORDER 1 AND AT GENERAL
`O`.** The corpus states "`c_s` and `c_{s+de}` are always nonzero" as part of a *definition*; here it
is a theorem, and its proof is where the slot lemma (B.36) is actually consumed.

**SOURCE.** `docs/GMN_citations.md` Def 2.21; `EFF.HE3.13` ("`R_λ` … of degree `d_λ` with
`R_λ(0) ≠ 0`"); `EFF.HE3.14`; `EFF.W12.23` (the vertex clause's `digit ≠ 0`).

**TEETH.** `W12-SHAPE` (0/164, both directions) → **Lean theorem** (the degree-and-endpoints half of
every row's polygon key).

**ENVIRONMENT.** ENV-A'.

---

## 5. §5 — THE SLOT LEMMA AND THE PRODUCT LAW

### NODE B.31 [lemma] [fresh]

**STATEMENT.** *Monic division does not lower the Gauss valuation.* For `φ` monic and any `a ∈ O[X]`:
`gaussVal a ≤ gaussVal (a %ₘ φ)` and `gaussVal a ≤ gaussVal (a /ₘ φ)`. Consequently
`gaussVal f ≤ npHgt φ f j` for every `j`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem gaussVal_le_modByMonic (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (a : Polynomial O) : gaussVal a ≤ gaussVal (a %ₘ φ)

theorem gaussVal_le_divByMonic (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (a : Polynomial O) : gaussVal a ≤ gaussVal (a /ₘ φ)

theorem gaussVal_le_npHgt (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (f : Polynomial O) (j : ℕ) : gaussVal f ≤ npHgt φ f j
```

**DEPENDS.** B.02 · B.08 · B.10 (its step-2 map-commutation, which is the whole content) · B.11.

**PROOF.**
1. Reduce to the case `gaussVal a ≠ ⊤` (else `a = 0` and both sides are `⊤`), and write
   `gaussVal a = (k : ℕ∞)`.
2. By B.08, `π^k` divides every coefficient of `a`, i.e. `a.map ρ = 0` for
   `ρ := Ideal.Quotient.mk ((maximalIdeal O)^k)`.
3. By B.10's step 2 (`map` commutes with monic division), `(a %ₘ φ).map ρ = (a.map ρ) %ₘ (φ.map ρ) = 0`
   and likewise for `/ₘ`.
4. B.08 in the other direction turns each `map … = 0` back into `(k : ℕ∞) ≤ gaussVal (…)`.
5. `gaussVal_le_npHgt`: induction on `j`, using both halves at each step
   (`npHgt φ f j = gaussVal (dev φ f j)` and `dev φ f (j+1) = dev φ (f /ₘ φ) j`).

**SIZE.** 18 lines.

**SOURCE.** `EFF.W12.23` (the development lives at level `N` — i.e. the digits of `a_j` are digits of
`f`); `EFF.HE3.27`(c).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.32 [lemma] [fresh]

**STATEMENT.** *The representation bound (the carry lemma).* Let `φ` be monic with `0 < deg φ`,
`0 < ℓ`, and suppose `f = Σ_{t ∈ range K} c t * φ^t` for some family `c : ℕ → O[X]` with **no degree
restriction**. Then

```
(Finset.range K).inf (fun t => ℓ • gaussVal (c t) + (u * t : ℕ))  ≤  suppVal φ f u ℓ.
```

In words: the canonical development minimises the weighted `inf` among all `φ`-representations —
carrying can only raise the weight, because moving mass from index `t` to index `t+1` adds `u` to the
weight and cannot lower the Gauss valuation (B.31).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem inf_weight_le_suppVal (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) {f : Polynomial O}
    {c : ℕ → Polynomial O} {K : ℕ} (hc : ∑ t ∈ Finset.range K, c t * φ ^ t = f) :
    (Finset.range K).inf (fun t => ℓ • gaussVal (c t) + (u * t : ℕ)) ≤ suppVal φ f u ℓ
```

**DEPENDS.** B.02 · B.05 · B.07 · B.09 · B.11 · B.14 · B.31 · mathlib `Finset.inf_le`,
`Finset.le_inf`, `Nat.rec` (strong induction on `Σ_t (c t).natDegree`).

**PROOF.**
1. **The one-step carry.** Define `c' t := (c t %ₘ φ) + (c (t-1) /ₘ φ)` (with the `t = 0` term reading
   `c 0 %ₘ φ`), extended by `0` past `K`. Then `Σ_t c' t * φ^t = f` — a computation:
   `c t = c t %ₘ φ + φ * (c t /ₘ φ)` (`modByMonic_add_div`), and reindexing the `φ * (c t /ₘ φ) * φ^t`
   terms to index `t+1` is `Finset.sum_range_succ'` plus `pow_succ`.
2. **The carry raises the weight.** `gaussVal (c' t) ≥ min (gaussVal (c t %ₘ φ)) (gaussVal (c (t-1) /ₘ φ))`
   (the `inf` of a sum bound: `gaussVal (x + y) ≥ min (gaussVal x) (gaussVal y)`, a private helper of
   two lines from B.08), and each of those is `≥ gaussVal (c t)` resp. `≥ gaussVal (c (t-1))` by
   B.31. Hence
   `ℓ • gaussVal (c' t) + u*t ≥ min (ℓ • gaussVal (c t) + u*t) (ℓ • gaussVal (c (t-1)) + u*(t-1))`,
   using `u*(t-1) ≤ u*t`. Taking `inf` over `t`, the new `inf` is `≥` the old one.
3. **Termination.** `Σ_t (c' t).natDegree < Σ_t (c t).natDegree` unless every `c t` already has
   degree `< φ.natDegree`, because `%ₘ` strictly drops the degree of any `c t` of degree
   `≥ φ.natDegree` and `/ₘ` drops it by `φ.natDegree ≥ 1`. Strong induction on that sum.
4. **The base case.** When every `c t` has degree `< φ.natDegree`, B.06's uniqueness gives
   `c t = dev φ f t` for `t < K`, and the `inf` is `suppVal φ f u ℓ` up to the range: B.08's
   `gaussVal_range` and B.12's tail clause make the two ranges interchangeable.

**SIZE.** 60 lines. **SPLIT MANDATED → 3**: `B32a.lean` = the two private helpers
(`gaussVal_add_ge` and the one-step carry identity of step 1); `B32b.lean` = the weight-monotonicity
of step 2; `B32c.lean` = the induction (steps 3–4) and the contract declaration. The fleet must not
attempt this as one unit — it is the chapter's largest single combinatorial argument after B.42.

**SOURCE.** `EFF.W12.23` ("Monic division gives the UNIQUE `Φ`-adic development"); the carry
bookkeeping is `EFF.W12.24`'s "right-to-left sweep" read as an inequality rather than a count.

**TEETH.** `W12-BLOCK` (`EFF.W12.55`, 0/1,594,670) → **executable regression** retained.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.33 [lemma] [fresh]

**STATEMENT.** *The easy half of the product law.* For `φ` monic with `0 < deg φ`, `0 < ℓ`, and any
`f g ∈ O[X]`:
`suppVal φ f u ℓ + suppVal φ g u ℓ ≤ suppVal φ (f * g) u ℓ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem suppVal_add_le_suppVal_mul (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (f g : Polynomial O) :
    suppVal φ f u ℓ + suppVal φ g u ℓ ≤ suppVal φ (f * g) u ℓ
```

**DEPENDS.** B.05 · B.09 · B.14 · B.32 · mathlib `Finset.sum_mul_sum`, `Finset.inf_le`.

**PROOF.**
1. Let `K` be large enough that B.05 applies to both `f` and `g` (e.g.
   `K := f.natDegree + g.natDegree + 2`), so `f = Σ_{j<K} dev φ f j * φ^j` and likewise for `g`.
2. Multiply: `f * g = Σ_{t < 2K} c t * φ^t` with `c t := Σ_{j+i=t} dev φ f j * dev φ g i`
   (`Finset.sum_mul_sum` plus the `Finset.Nat.antidiagonal` reindexing; the reindexing identity is a
   private helper).
3. `gaussVal (c t) ≥ inf over the pairs (j,i) with j+i=t of (gaussVal (dev φ f j) + gaussVal (dev φ g i))`
   by B.09 (`gaussVal_mul`) and the sum bound `gaussVal (x+y) ≥ min …` (B.32's private helper,
   extended to a `Finset.sum` by induction).
4. Hence `ℓ • gaussVal (c t) + u*t ≥ inf_{j+i=t} ((ℓ • gaussVal (dev φ f j) + u*j) + (ℓ • gaussVal (dev φ g i) + u*i))`
   `≥ suppVal φ f u ℓ + suppVal φ g u ℓ` (`Finset.inf_le` at each of `j` and `i`).
5. Apply B.32 to the representation of step 2: the left-hand `inf` of B.32 is `≥` the constant of
   step 4, so `suppVal φ (f*g) u ℓ ≥ suppVal φ f u ℓ + suppVal φ g u ℓ`.

**SIZE.** 34 lines, plus the antidiagonal private helper (~10 lines) and the `Finset.sum` extension of
the sum bound (~8 lines).

**SOURCE.** `EFF.HE6.06` (the ultrametric inequality, imported classically there — here proved);
`EFF.HE3.22` (`LEMMA HE3-1′`, whose "generically" is exactly the failure of the reverse inequality
that B.35 must rule out).

**TEETH.** `HE-PSI` (`EFF.HE3.51`, guarding `.22`) → **Lean theorem** (the inequality half of
`LEMMA HE3-1′`).

**ENVIRONMENT.** ENV-A'.

---

### NODE B.34 [def] [fresh]

**STATEMENT.** *The initial form of a one-sided polynomial.* Say `f` is **`(u,ℓ)`-pure** when
`sideSet φ f u ℓ` contains both `0` and `f.natDegree / φ.natDegree` — i.e. the polygon is one-sided of
slope `−u/ℓ` spanning the whole abscissa range. For such `f`, with `H₀` the height at `0`, the
**initial form** is `resPoly π φ f u ℓ h H₀ ∈ (resField φ)[Y]`, of degree `sideDeg φ f u ℓ h` and with
nonzero constant term (B.30). Declare the predicate.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `IsPure φ f u ℓ` : the `φ`-adic polygon of `f` is a single side of slope `−u/ℓ` spanning the whole
abscissa range `0 … f.natDegree / φ.natDegree`. -/
def IsPure (φ f : Polynomial O) (u ℓ : ℕ) : Prop :=
  OnSide φ f u ℓ 0 ∧ OnSide φ f u ℓ (f.natDegree / φ.natDegree)
```

**DEPENDS.** B.16 · B.20 · B.29 · B.30.

**PROOF.** definitional. The right endpoint is `f.natDegree / φ.natDegree` and not `f.natDegree`,
because the development index runs to `μ = deg f / deg φ` (B.13). For a `(u,ℓ)`-pure monic `f` of
degree `μ*m`, B.13 gives `npHgt φ f μ = 0`, so `OnSide … μ` forces `suppVal φ f u ℓ = u*μ` — the
polygon's right endpoint is at height `0`, as `EFF.HE3.13`'s `A_μ = 1` requires.

**FAITHFULNESS.** `EFF.HE6.32` step 1 and `EFF.HE3.32` both work "at a slope `λ`" with the block
factor already separated, i.e. on a pure polynomial; `docs/GMN_citations.md` Thm 1.15 phrases the
conclusion as "`N_φ(F_i)` one-sided of slope `λ_i`". `IsPure` is that conclusion as a predicate.
**Flagged for human review.**

**SIZE.** 8 lines.

**SOURCE.** `docs/GMN_citations.md` Thm 1.15; `EFF.HE3.32`; `EFF.HE6.32`.

**TEETH.** signed non-applicable (a definition).

**ENVIRONMENT.** ENV-A.

---

### NODE B.35 [theorem] [fresh]

**STATEMENT.** *The theorem of the product at order 1 (NS-9's order-1 case).* Let `φ` be an order-1
key, `0 < ℓ`, `Nat.Coprime u ℓ`, and let `f, g` be monic with `f`, `g` both `(u,ℓ)`-pure. Then

* `suppVal φ (f * g) u ℓ = suppVal φ f u ℓ + suppVal φ g u ℓ`;
* `f * g` is `(u,ℓ)`-pure;
* `resPoly` of `f * g` equals the product of the `resPoly`s of `f` and `g` (with the heights added):
  `resPoly π φ (f*g) u ℓ h_{fg} (H₀f + H₀g) = resPoly π φ f u ℓ h_f H₀f * resPoly π φ g u ℓ h_g H₀g`;
* `sideDeg (f*g) = sideDeg f + sideDeg g`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem suppVal_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O}
    (hf : f.Monic) (hg : g.Monic) (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ) :
    suppVal φ (f * g) u ℓ = suppVal φ f u ℓ + suppVal φ g u ℓ ∧ IsPure φ (f * g) u ℓ

theorem resPoly_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O}
    (hf : f.Monic) (hg : g.Monic) (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ)
    {H₀f H₀g : ℕ} (hHf : npHgt φ f 0 = (H₀f : ℕ∞)) (hHg : npHgt φ g 0 = (H₀g : ℕ∞))
    (hf' hg' hfg') :
    resPoly π φ (f * g) u ℓ hfg' (H₀f + H₀g)
      = resPoly π φ f u ℓ hf' H₀f * resPoly π φ g u ℓ hg' H₀g
```
(the three `Nonempty` witnesses are named `hf' hg' hfg'` and are supplied by B.18.)

**DEPENDS.** B.09 · B.13 · B.14 · B.18 · B.20 · B.22 · B.24 · B.25 · B.26 · B.28 · B.29 · B.30 ·
B.33 · B.34 · B.36 · mathlib `Polynomial.coeff_mul`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`,
and the domain property of `(resField φ)[Y]`.

**PROOF.**
1. Write `n_f := f.natDegree / m`, `n_g := g.natDegree / m`, so `n_{fg} = n_f + n_g`
   (`natDegree_mul` for monics plus `Nat.add_div_right`-style arithmetic; a private helper).
2. `≥` in the first claim is B.33.
3. For `≤`, compute the digit of the product at the *predicted* height and index and show it is
   nonzero. By B.05 and the convolution of step 2 of B.33, the development coefficient of `f*g` at
   index `t` is `c t = Σ_{j+i=t} dev φ f j * dev φ g i` **after carrying**; by B.32's step-1 carry
   identity the carry contributes only terms of strictly larger weight, so at the minimal weight the
   digit of `dev φ (f*g) t` equals the digit of the uncarried `c t`.
4. The digit of `c t` at the line height is `Σ_{j+i=t} (digit of dev φ f j) * (digit of dev φ g i)`
   by B.22's `digAt_add` and the multiplicativity of `digAt` on products at added heights (a private
   helper: `digAt π (k+k') (x*y) = digAt π k x * digAt π k' y` when `π^k ∣ x`, `π^k' ∣ y`, immediate
   from `digAt_eq`).
5. Pushing into `resField φ` (a ring hom, B.25), the residual coefficient of `f*g` at position `k` is
   `Σ_{k₁+k₂=k} resCoeff_f k₁ * resCoeff_g k₂`, i.e. `resPoly (f*g) = resPoly f * resPoly g`
   coefficientwise (`Polynomial.coeff_mul`).
6. `(resField φ)[Y]` is a domain (`resField φ` is a field, B.25), and both factors are nonzero (B.30:
   nonzero constant term), so the product is nonzero; in particular its degree-`0` and
   degree-`(d_f+d_g)` coefficients are nonzero (leading coefficients multiply, constant terms
   multiply).
7. A nonzero residual coefficient at position `0` says (B.30's `resCoeff_eq_zero_iff`, contrapositive)
   that the abscissa `0` is on the `(u,ℓ)`-side of `f*g` at the predicted support value, which forces
   `suppVal φ (f*g) u ℓ ≤ suppVal φ f u ℓ + suppVal φ g u ℓ`; with step 2 this is the equality, and
   with the position-`(d_f+d_g)` coefficient it is `IsPure`.

**SIZE.** 90 lines across the split. **SPLIT MANDATED → 4**: `B35a.lean` = the two private helpers
(index arithmetic of step 1, `digAt` multiplicativity of step 4); `B35b.lean` = the carry-does-not-see
-the-minimal-weight lemma (step 3, the delicate one); `B35c.lean` = `resPoly_mul_of_pure`
(steps 4–6); `B35d.lean` = `suppVal_mul_of_pure` (step 7) and the contract.

**⚠ THIS IS THE CHAPTER'S SECOND HARD CORE, AND ITS FALLBACK IS `B-BOX-2`.** Step 3 is the only place
the carry bookkeeping and the digit read interact, and it is where a wrong estimate would silently
make B.42 and B.48 false. **`B-BOX-2` (the fallback, to be invoked only on a `BLOCKED` return with a
minimised reproducer):** restrict the whole chapter to `m = 1` (`φ` linear, `φ̄` of degree 1), where
`dev φ f j = C (f.coeff j)` after a shift (B.15 at `φ = X`, composed with landed `typeOf_shift`) and
the carry disappears entirely because every development coefficient is already a constant. At `m = 1`
steps 3–4 are one line. The cost of the fallback is stated and it is **not** small: `m ≥ 2` would then
be reachable from `m = 1` only by the unramified base change `O → AdjoinRoot φ` **plus Galois descent
of the factorization**, neither of which exists in `leanfinal` or in any quarry (H-6). A fleet agent
returning `BLOCKED` on B.35 must say which of steps 3–7 failed and why.

**⚠ WHY THE RAMIFIED BASE CHANGE IS *NOT* USED HERE, AND WHY THAT MATTERS.** A tempting shortcut for
the `ℓ ≥ 2` case is `O ↝ O' := O[T]/(T^ℓ − π)`, over which the slope becomes integral and the whole
argument collapses to the `ℓ = 1` case. `EFF.HE3.44`'s HE3-BOX-6 is precisely the record of that
shortcut failing: "the substitute ramified base change `O ↝ O[Π]/(Π^ℓ−π)` is **stated too cheaply:
`Φ′` need not remain irreducible over `O₂`**". **The obstruction is specifically to keeping the key
irreducible, i.e. to transporting the *residual field*, and it does NOT obstruct transporting a
*valuation identity*.** So a base change would be admissible for the first clause alone
(`suppVal` additivity, a statement in `ℕ∞` about `O`-polynomials) and is inadmissible for the third
(`resPoly` multiplicativity, a statement in `(resField φ)[Y]`). Since the chapter needs all four
clauses from one argument, the base change is not used at all — but the distinction is recorded
because it is the exact content of HE3-BOX-6 and a cross-reader should check that no node below
smuggles the shortcut in. **§14 item 1.**

**SOURCE.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-9 (theorem of the product);
`EFF.HE3.14`, `.22`; `EFF.HE6.11`; `EFF.HE3.44` (the base-change objection quoted above).

**TEETH.** `HE6-GEN` (`EFF.HE6.49`, the flat resultant identity
`2v(Res(f,Ψ)) = ℓ·deg r·D′·h_F(κ)` at rational heights) → **executable regression** retained: the
identity is the corpus's *multiplicative* form of this node's additivity, read through resultants,
and the chapter does not formalise resultants (H-2). `HE6R1-GEN2` (`EFF.HE6R1.28`, 252 flat
identities, 0 violations) → **executable regression** retained at the level-2 analogue.

**ENVIRONMENT.** ENV-A' + `[Finite (ResidueField O)]` (via B.26, which B.30 consumes).

---

### NODE B.36 [lemma] [fresh]

**STATEMENT.** *The slot lemma at order 1 over the base.* Let `φ` be an order-1 key with
`m = φ.natDegree`, and let `p ∈ (ResidueField O)[y]` with `p.degree < (m : WithBot ℕ)`. Then
`AdjoinRoot.mk (φ.map (residue O)) p = 0 ↔ p = 0`. Consequently, for `a ∈ O[X]` with
`a.degree < φ.degree` and any `k`, `resMk π φ k a = 0 ↔ digPoly π k a = 0`; and if `a ≠ 0` with
`gaussVal a = (k : ℕ∞)` then `resMk π φ k a ≠ 0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem mk_eq_zero_iff_of_degree_lt {φ : Polynomial O} (hφ : IsKey φ)
    {p : Polynomial (ResidueField O)} (hp : p.degree < (φ.natDegree : WithBot ℕ)) :
    AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) p = 0 ↔ p = 0

theorem resMk_eq_zero_iff (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {k : ℕ}
    {a : Polynomial O} (ha : a.degree < φ.degree) :
    resMk π φ k a = 0 ↔ digPoly π k a = 0

theorem resMk_ne_zero (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {k : ℕ}
    {a : Polynomial O} (ha : a.degree < φ.degree) (ha0 : a ≠ 0)
    (hk : gaussVal a = (k : ℕ∞)) : resMk π φ k a ≠ 0
```

**DEPENDS.** B.01 · B.23 · B.24 · B.25 · mathlib `AdjoinRoot.mk_eq_zero`, `Polynomial.degree_map`
(for a monic and a field target: `Monic.degree_map`), `Polynomial.eq_zero_of_dvd_of_degree_lt_degree`
(or `Polynomial.eq_zero_of_dvd_of_natDegree_lt`).

**PROOF.**
1. `mk_eq_zero_iff_of_degree_lt`, (→): `AdjoinRoot.mk_eq_zero` gives `φ̄ ∣ p`; `φ̄` has degree `m`
   (`Monic.degree_map hφ.monic`) and `p.degree < m`, so `p = 0`
   (`eq_zero_of_dvd_of_degree_lt_degree`).
2. (←): `map_zero`.
3. `resMk_eq_zero_iff`: `resMk π φ k a = AdjoinRoot.mk φ̄ (digPoly π k a)` by definition, and
   `(digPoly π k a).degree ≤ a.degree < φ.degree = m` by B.24's `degree_digPoly_le`; apply step 1.
4. `resMk_ne_zero`: by step 3 it suffices that `digPoly π k a ≠ 0`, which is B.24's
   `digPoly_eq_zero_iff` — its hypothesis `(k : ℕ∞) ≤ gaussVal a` is `hk` with `le_refl`, and its
   conclusion `(k+1 : ℕ∞) ≤ gaussVal a = (k : ℕ∞)` is false.

**SIZE.** 20 lines.

**⚠ THIS NODE IS `EFF.HE6.15` (T2 PIN `HE6-SLOT-SEAM`, 48 T2 citations) AT `e₁ = 1`.** The pin's
statement is *"`dv(A(ξ)) = min_i(e₁v(a_i) + ih)` **EXACTLY**, and the residue of the attaining class,
read after division by `ϖ(ξ)^{dv(A)}`, is `ι_ξ(γ)·η_ξ^{−q}`"*, as corrected by `EFF.HE6.58` (A3 F-1,
which replaced a **vacuous bare `γ`** by `γ_k(A) := Σ_{t≥0, i+e₁t<D′} res(a_{i+e₁t}π^{−(k−(i+e₁t)h)/e₁}) η_θ^t`).
At `e₁ = 1, h = 0`: the exactness clause `dv(A(ξ)) = min_i v(a_i)` **is** `gaussVal a`, the twist
`η_ξ^{−q(k)}` is trivial (`q(k) = 0`), and `γ_k(A)` collapses to the single term
`res(a_0 π^{−k}) η_θ^0`… no: it collapses to `Σ_{t<m} res(a_t π^{−k}) η_θ^t`, which is precisely the
class of `digPoly π k a` in `F[y]/(φ̄)` under `y ↦ η_θ`. So **`resMk π φ k a` is `γ_k(A)`** and
`resMk_ne_zero` is the exactness clause. **The `ξ` is gone**: the corpus states the lemma at a point
`ξ` of `K̄₀` satisfying `(T1)/(T2)`, this chapter states it as the injectivity of
`F[y]_{<m} → F[y]/(φ̄)`, which is the same fact with the ambient closure removed. **That removal is
§14 item 4 and it is the chapter's most consequential transcription choice.** Note also that
`EFF.HE6.30`'s OPEN-CALL 2 flags exactly this pin as one whose A3 correction "sits **outside** every
T2 pin span" and calls it "the most consequential item in this compilation" — so the corrected form
`EFF.HE6.58`, not the pin span `EFF.HE6.15` alone, is what is transcribed here.

**SOURCE.** `EFF.HE6.15` (`[PIN HE6-SLOT-SEAM]`, LEMMA HE6-0″) **as corrected by** `EFF.HE6.58`
(A3 F-1); `EFF.HE3.03` (`LEMMA GENHN-2`, the SLOT LEMMA, whose over-consumption at non-root points
`EFF.HE6.15` exists to cure); `EFF.HE3.71` (R8-5: the provenance fix — cite HE6-0″, not GENHN-2).

**TEETH.** `HE6R1-SLOT2` (`EFF.HE6R1.26`, 0 violations / 1,512, "(SLOT₂) exactness
`v(Res(f,C)) = 4·dv₂(C)`") → **executable regression** retained at the level-2 analogue;
`HE-NORM` (`EFF.HE3.50`, 72,134 identities) → **Lean theorem** (the level-1 exactness clause is this
node).

**ENVIRONMENT.** ENV-A'.

---

## 6. §6 — THE TWO DISSECTIONS

### DECISION D-2 — HOW THE DISSECTIONS ARE PROVED

> Recorded here because it is the chapter's second interface decision and it fixes ≈ 40% of the
> chapter's Lean mass.

**THE DECISION.** Both dissections are proved **over `O`, by one graded successive-approximation
engine (B.37–B.41), modelled declaration-for-declaration on the landed Hensel engine of
`leanfinal/Uniformity/HenselFactorization.lean`.** No base change of any kind is used.

**The three alternatives, and why each is rejected.**

1. **Unramified base change `O → AdjoinRoot φ` to make the key linear (`m = 1`).** Rejected: the
   dissection would then be a factorization over `AdjoinRoot φ`, and descending it to `O` needs
   **Galois descent for an unramified extension**, which exists in neither `leanfinal` nor any quarry
   (H-6) and is a strictly larger obligation than the graded engine.
2. **Totally ramified base change `O → O_ℓ := O[T]/(T^ℓ − π)` to make the slope integral (`ℓ = 1`),
   then landed `exists_monic_factorization` after `scaleRoots`.** Rejected, and the reason is
   **NOT** HE3-BOX-6's: over `O_ℓ` the residue field is unchanged, so `φ̄` stays irreducible and `φ`
   stays an order-1 key — HE3-BOX-6's objection ("`Φ′` need not remain irreducible over `O₂`",
   `EFF.HE3.44`) bites at `e₁ ≥ 2`, where a key's irreducibility is **not** determined by its
   reduction, and does not bite here. **The real obstruction is on the residual side:** the on-side
   abscissae stay `ℓ`-spaced over `O_ℓ` (B.17's argument is unchanged), so the residual polynomial
   over `O_ℓ` at slope `(u,1)` is `R_O(Y^ℓ)` rather than `R_O(Y)`; factoring `R_O(Y^ℓ)` over
   `resField φ` is a **strictly finer** dissection whose pieces are permuted by the (possibly
   non-Galois) extension `O_ℓ/O`, so descent fails for the same reason as in alternative 1 and for a
   worse reason besides (`O_ℓ/O` need not be Galois when the `ℓ`-th roots of unity are absent).
   **This is a finding, not a transcription:** the corpus's own objection to the ramified base change
   is about key irreducibility, and at `e₁ = 1` that objection is void — the obstruction that
   remains is the residual-index one recorded here. **§14 item 1.**
3. **Rational sampling with an intermediate slope, then a single coprime-Hensel step.** Rejected as
   incomplete rather than wrong: at a vertex the support value at an intermediate slope `κ` is
   attained at exactly one abscissa (B.19 is the reason), so the "residual polynomial at `κ`" is a
   monomial and carries no coprime factorization to feed landed Hensel. Rational sampling is what
   *detects* the vertex (`EFF.HE6.30`(c): "integer sampling cannot separate three slopes inside one
   open interval, but rational sampling … can"), and B.42 uses it for exactly that; it does not by
   itself produce the factorization.

**The template, named precisely.** B.38 ↔ landed `exists_solve_field` (`HenselFactorization.lean:133`);
B.39 ↔ `exists_solve_mod` (`:230`); B.40 ↔ `exists_solve_step` (`:248`); B.41 ↔
`exists_adicLimit_of_degree_lt` (`:306`) + `exists_monic_factorization` (`:393`); B.43 ↔
`monic_factorization_unique` (`:694`). **The landed file is 790 lines for the ungraded case; the
graded case is the chapter's largest cluster and the fleet should be sized for ≈ 900 lines across
B.37–B.43.** Every one of those landed lemmas is `sorry`-free with a Lean-core footprint, so the
template is known to close; what is new is the graded weight bookkeeping.

---

### NODE B.37 [def] [fresh]

**STATEMENT.** *Graded coprimality at a slope.* Fix an order-1 key `φ`, `0 < ℓ`, `Nat.Coprime u ℓ`,
and monic `g, h` that are `(u,ℓ)`-pure with heights `H_g, H_h` at abscissa `0`. Say the pair is
**`(u,ℓ)`-coprime** when their residual polynomials are coprime in `(resField φ)[Y]`:
`IsCoprime (resPoly π φ g u ℓ _ H_g) (resPoly π φ h u ℓ _ H_h)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `GradedCoprime π φ u ℓ g h` : `g` and `h` are `(u,ℓ)`-pure with coprime residual polynomials. -/
def GradedCoprime (π : O) (φ : Polynomial O) (u ℓ : ℕ) (g h : Polynomial O) : Prop :=
  ∃ (Hg Hh : ℕ) (hg' : (sideSet φ g u ℓ).Nonempty) (hh' : (sideSet φ h u ℓ).Nonempty),
    npHgt φ g 0 = (Hg : ℕ∞) ∧ npHgt φ h 0 = (Hh : ℕ∞) ∧
    IsPure φ g u ℓ ∧ IsPure φ h u ℓ ∧
    IsCoprime (resPoly π φ g u ℓ hg' Hg) (resPoly π φ h u ℓ hh' Hh)
```

**DEPENDS.** B.16 · B.18 · B.20 · B.29 · B.34.

**PROOF.** definitional.

**FAITHFULNESS.** This is the graded analogue of the landed engine's hypothesis
`IsCoprime g₀ h₀` on residue-field reductions (`HenselFactorization.lean:393`). The corpus's
corresponding hypotheses are `EFF.HE3.32`'s "`R_λ = Π_r r^{m_r}` (`r` irreducible over `K`)" — the
factors of a squarefree-at-`r` residual are pairwise coprime — and `docs/GMN_citations.md` Thm 1.19's
"pairwise-distinct monic irreducibles in `F_φ[y]`". **Flagged for human review.**

**SIZE.** 12 lines.

**SOURCE.** `docs/GMN_citations.md` Thm 1.15, Thm 1.19; `EFF.HE3.32`.

**TEETH.** signed non-applicable (a definition).

**ENVIRONMENT.** ENV-C.

---

### NODE B.38 [lemma] [fresh]

**STATEMENT.** *The graded Bézout solve over the residual field.* Let `K` be a field and
`G, H ∈ K[Y]` coprime with `G.natDegree = a`, `H.natDegree = b`. For every `W ∈ K[Y]` with
`W.degree < ((a + b : ℕ) : WithBot ℕ)` there are `U, V ∈ K[Y]` with `U.degree < (a : WithBot ℕ)`,
`V.degree < (b : WithBot ℕ)` and `W = H * U + G * V`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_solve_resField {K : Type*} [Field K] {G H : Polynomial K}
    (hG : G.Monic) (hH : H.Monic) (hcop : IsCoprime G H) {W : Polynomial K}
    (hW : W.degree < ((G.natDegree + H.natDegree : ℕ) : WithBot ℕ)) :
    ∃ U V : Polynomial K, U.degree < (G.natDegree : WithBot ℕ) ∧
      V.degree < (H.natDegree : WithBot ℕ) ∧ W = H * U + G * V
```

**DEPENDS.** landed `Uniformity.Hensel.exists_solve_field` (`HenselFactorization.lean:133`).

**PROOF.**
1. This is **literally** the landed `exists_solve_field` with `k := K`, `g₀ := G`, `h₀ := H`,
   `w := W`. `exact Uniformity.Hensel.exists_solve_field hG hH hcop hW`.

**SIZE.** 4 lines. **This node exists only to record that the landed lemma is stated at the right
generality** (`{k : Type*} [Field k]`, not over `ResidueField O`), so no re-proof is needed and the
graded engine inherits it. If `exists_solve_field`'s section variables turn out to bind
`ResidueField O`, this node becomes a 40-line re-proof and the orchestrator must be told —
**check first: `HenselFactorization.lean:131` reads `variable {k : Type*} [Field k]`, so the node is a
one-liner.**

**SOURCE.** landed API; `docs/GMN_citations.md` Thm 1.19's proof needs exactly this Bézout step.

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-D.

---

### NODE B.39 [lemma] [fresh]

**STATEMENT.** *The graded solve at one weight.* Let `φ` be an order-1 key, `0 < ℓ`,
`Nat.Coprime u ℓ`, and `g, h` monic `(u,ℓ)`-pure and `(u,ℓ)`-coprime with residual polynomials
`G, H` of degrees `a, b`. Let `e ∈ O[X]` with `e.natDegree < (a + b) * ℓ * m` (the degree of `g*h`)
and `suppVal φ e u ℓ ≥ c` for a given `c`. Then there exist `U, V ∈ O[X]` with
`U.natDegree < g.natDegree`, `V.natDegree < h.natDegree`,
`suppVal φ U u ℓ ≥ c - suppVal φ h u ℓ`, `suppVal φ V u ℓ ≥ c - suppVal φ g u ℓ`, and

```
suppVal φ (e - (h * U + g * V)) u ℓ ≥ c + 1.
```

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_graded_solve (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g h : Polynomial O}
    (hg : g.Monic) (hh : h.Monic) (hgh : GradedCoprime π φ u ℓ g h)
    {c : ℕ} {e : Polynomial O} (hdeg : e.natDegree < (g * h).natDegree)
    (he : ((c : ℕ) : ℕ∞) ≤ suppVal φ e u ℓ) :
    ∃ U V : Polynomial O, U.natDegree < g.natDegree ∧ V.natDegree < h.natDegree ∧
      ((c + 1 : ℕ) : ℕ∞) ≤ suppVal φ (e - (h * U + g * V)) u ℓ
```

**DEPENDS.** B.20 · B.28 · B.29 · B.30 · B.33 · B.35 · B.36 · B.37 · B.38 · landed
`Uniformity.Hensel.exists_monic_lift`, `Uniformity.Hensel.eq_sum_range_of_degree_lt`.

**PROOF.**
1. Form the residual polynomial of `e` **at the weight `c`** rather than at its own support value: by
   B.28's definition with `H₀` replaced by the line height determined by `c`, this is a well-defined
   element `E ∈ (resField φ)[Y]` (zero if `suppVal φ e u ℓ > c`), of degree `< a + b` because
   `e.natDegree < (g*h).natDegree` bounds the abscissa range.
2. Apply B.38 with `G, H, W := E`: obtain `U₀, V₀ ∈ (resField φ)[Y]` with the degree bounds and
   `E = H * U₀ + G * V₀`.
3. Lift `U₀, V₀` back to `O[X]`: each residual coefficient of `U₀` is an element of
   `resField φ = F[y]/(φ̄)`, hence the class of some `p ∈ F[y]` of degree `< m` (choose the canonical
   representative via `AdjoinRoot.mk`'s surjectivity plus `modByMonic`), which lifts to `O[X]` of
   degree `< m` by `Ideal.Quotient.mk_surjective` coefficientwise; assemble
   `U := Σ_k (lift of U₀'s k-th coefficient) * π^{(line height)} * φ^{j₀ + ℓk}`. The weight
   bookkeeping is the only content: `suppVal φ U u ℓ ≥ c - suppVal φ h u ℓ` by B.33 and the
   construction.
4. `e - (h*U + g*V)` has residual polynomial `E - (H*U₀ + G*V₀) = 0` at weight `c`, hence by B.30's
   `resCoeff_eq_zero_iff` (contrapositive) its support value at `(u,ℓ)` is `> c`, i.e. `≥ c + 1`.
5. The degree bounds on `U, V` follow from step 3's construction: `U` has abscissa range `< a`, so
   degree `< a * ℓ * m = g.natDegree`.

**SIZE.** 70 lines. **SPLIT MANDATED → 2**: `B39a.lean` = step 3 (the residual-to-`O[X]` lift with its
weight bookkeeping — reusable, so its extraction is a **RE-PLAN request**, orchestrator books it as
**B.39a `resLift`**); `B39b.lean` = steps 1–2, 4–5 and the contract.

**⚠ THE `resLift` OF STEP 3 IS THE `(LIFT)` OF `EFF.HE6.13`, AT `e₁ = 1`.** The pin
`[PIN HE6-LIFT-1L]` (T2 count 34) gives the **exact reachable-residue set** at height `k`:
`η_θ^{−q(k)} · { Σ_{t ∈ T(k)} c_t η_θ^t : c_t ∈ F_Q, not all 0 }` with
`T(k) := { t < f₁ : k ≥ (i₀ + e₁t)h }`, and "The set is ALL of `K^×` iff `T(k) = {0,…,f₁−1}`". At
`e₁ = 1, h = 0` we have `i₀ = 0`, `T(k) = {0,…,m−1}` for **every** `k ≥ 0`, and `q(k) = 0` — so the
reachable set is all of `resField φ` at every height, unconditionally, and the lift of step 3 is
total. **`EFF.HE6.12` records that the original `(LIFT)` was FALSE as stated, refuted by two
independent counterexamples**, and `EFF.HE6.13` is the corrected form; the reason the correction is
invisible here is that `T(k) = ∅` (the "height not attained" clause) cannot happen at `h = 0`. This
is the third place H-1's scope claim does real work and it is **§14 item 4**.

**SOURCE.** `EFF.HE6.13` (`[PIN HE6-LIFT-1L]`, `(LIFT)` corrected) and `EFF.HE6.12` (the refutation
of the original); `EFF.HE3.21` (`LEMMA HE3-1L`, the letter lift: "fullness at `κ ≥ (D′−1)h`", which at
`h = 0` is every `κ`); landed `HenselFactorization.lean:230,248` as the ungraded template.

**TEETH.** `HE6R1-LIFT2` (`EFF.HE6R1.27`, 5 exhaustive frames, threshold **sufficient not sharp**) →
**executable regression** retained; `HE6-RANK` (`EFF.HE6.51`, "old family 3 spurious vectors vs
enlarged family's exactly 1") → **signed non-applicability**: the rank question is about the *enlarged
test family* at fractional height, which H-1 puts out of scope.

**ENVIRONMENT.** ENV-C.

---

### NODE B.40 [lemma] [fresh]

**STATEMENT.** *The graded adic limit.* Let `d : ℕ` and let `p : ℕ → O[X]` satisfy
`(p k).natDegree < d` for every `k` and
`((k : ℕ) : ℕ∞) ≤ suppVal φ (p (k+1) - p k) u ℓ` for every `k`. Then (over the complete bundle) there
is `P ∈ O[X]` with `P.natDegree < d` and `((k : ℕ) : ℕ∞) ≤ suppVal φ (P - p k) u ℓ` for every `k`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_graded_limit (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd0 : 0 < φ.natDegree) {u ℓ : ℕ} (hℓ : 0 < ℓ) (d : ℕ) (p : ℕ → Polynomial O)
    (hdeg : ∀ k, (p k).natDegree < d)
    (hstep : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (p (k + 1) - p k) u ℓ) :
    ∃ P : Polynomial O, P.natDegree < d ∧ ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (P - p k) u ℓ
```

**DEPENDS.** B.14 · B.31 · landed `Uniformity.Hensel.exists_adicLimit_of_degree_lt`
(`HenselFactorization.lean:306`) · B.08.

**PROOF.**
1. `suppVal φ a u ℓ ≥ (k : ℕ∞)` implies `gaussVal a ≥ (⌈k/ℓ⌉ : ℕ∞)` — a weight-to-coefficient
   conversion: from `Finset.le_inf_iff`, `ℓ • gaussVal (dev φ a j) + u*j ≥ k` at `j = 0` gives
   `ℓ • gaussVal (dev φ a 0) ≥ k`; and `gaussVal a ≤ npHgt φ a j` is **the wrong direction** — so use
   instead B.31's `gaussVal_le_npHgt` in the form: `gaussVal a = inf_j` over a representation, hence
   `gaussVal a ≥ (S - u * μ)/ℓ` where `S = suppVal`. Precisely: for every `j ≤ μ`,
   `ℓ • npHgt φ a j ≥ S - u*j ≥ S - u*μ`, and `gaussVal a ≥ min_j npHgt φ a j` … **this step is the
   node's only content and it must be got right**: the clean statement is
   `((k - u * μ) / ℓ : ℕ) ≤ gaussVal a` where `μ := d / φ.natDegree`, proved from
   `Finset.le_inf_iff` plus `gaussVal a = gaussVal (Σ_j dev φ a j * φ^j) ≥ min_j gaussVal (dev φ a j)`
   (B.09's sum bound and B.05).
2. With step 1, `hstep` gives `p (k+1) - p k ∈ coeffIdeal (maximalIdeal O ^ ⌈(k - uμ)/ℓ⌉)`, so after
   reindexing `k ↦ ℓ*k + u*μ` the hypothesis of landed `exists_adicLimit_of_degree_lt` holds for the
   subsequence `q j := p (ℓ*j + u*μ)`.
3. Landed `exists_adicLimit_of_degree_lt` gives `P` with `P - q j ∈ coeffIdeal (maximalIdeal O ^ j)`.
4. Convert back: `P - p k = (P - q j) + (q j - p k)` for a suitable `j` and use B.33's easy
   inequality plus B.08 to recover the `suppVal` bound; the telescoping `q j - p k` is a finite sum of
   `hstep` increments and its `suppVal` is bounded below by the smallest index.

**SIZE.** 50 lines. Step 1 is the whole risk and the fleet must state it as a standalone private
helper `gaussVal_ge_of_suppVal_ge` before anything else.

**SOURCE.** landed `HenselFactorization.lean:306` as template; `EFF.HE3.27`(c) (the in-window,
upward clause — the corpus's form of "the approximation converges inside the window").

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-B.

---

### NODE B.41 [theorem] [fresh]

**STATEMENT.** *The graded factorization (the engine).* Over the complete bundle, let `φ` be an
order-1 key, `0 < ℓ`, `Nat.Coprime u ℓ`, and let `f` be monic with a factorisation of its residual
data: suppose `G, H ∈ (resField φ)[Y]` are monic coprime with `G.natDegree + H.natDegree = μ_f`, that
`f` is `(u,ℓ)`-pure of residual polynomial `G * H` (up to a unit), and that `deg f = μ_f * ℓ * m`
— wait, `deg f = μ_f * m` with `μ_f = ℓ * (G.natDegree + H.natDegree)`; the exact index arithmetic is
fixed in the PROOF. Then `f = g * h` with `g, h` monic, `g` `(u,ℓ)`-pure of residual polynomial `G`,
`h` `(u,ℓ)`-pure of residual polynomial `H`, and
`g.natDegree = ℓ * m * G.natDegree`, `h.natDegree = ℓ * m * H.natDegree`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_graded_factorization (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O} (hf : f.Monic)
    (hpure : IsPure φ f u ℓ) {H₀ : ℕ} (hH₀ : npHgt φ f 0 = (H₀ : ℕ∞))
    (hne : (sideSet φ f u ℓ).Nonempty)
    {G H : Polynomial (resField φ)} (hG : G.Monic) (hH : H.Monic) (hGH : IsCoprime G H)
    (hprod : ∃ c : (resField φ)ˣ,
      resPoly π φ f u ℓ hne H₀ = Polynomial.C (c : resField φ) * (G * H)) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.natDegree = ℓ * φ.natDegree * G.natDegree ∧
      h.natDegree = ℓ * φ.natDegree * H.natDegree ∧
      IsPure φ g u ℓ ∧ IsPure φ h u ℓ ∧ GradedCoprime π φ u ℓ g h
```

**DEPENDS.** B.13 · B.18 · B.20 · B.29 · B.30 · B.33 · B.34 · B.35 · B.37 · B.39 · B.40 · landed
`Uniformity.Hensel.exists_monic_lift`, `Uniformity.Hensel.natDegree_eq_of_map_eq`,
`Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq`, `Uniformity.Hensel.isCoprime_of_map_eq`.

**PROOF.** The landed `exists_monic_factorization` (`HenselFactorization.lean:393`) is the template;
each step below names the landed step it mirrors.
1. **Initial approximation.** Lift `G` and `H` to monic `g₀, h₀ ∈ O[X]` of degrees
   `ℓ*m*G.natDegree`, `ℓ*m*H.natDegree` whose residual polynomials are `G`, `H`: use B.39a's
   `resLift` on the coefficients, then multiply by the appropriate `φ`-powers. (Landed step: the
   `exists_monic_lift` call.) The construction must make `g₀` **monic**, which fixes its top
   development coefficient to `1`; B.13 then forces its polygon's right endpoint.
2. **The error.** `e₀ := f - g₀ * h₀` has `suppVal φ e₀ u ℓ ≥ suppVal φ f u ℓ + 1`, because the
   residual polynomials agree at the top weight (B.35's `resPoly_mul_of_pure` applied to `g₀ * h₀`,
   plus `hprod`) and B.30 converts "residual polynomial vanishes" into "support value is strictly
   larger". `e₀.natDegree < f.natDegree` since both `f` and `g₀h₀` are monic of the same degree
   (landed `degree_sub_lt_of_monic_of_natDegree_eq`).
3. **The iteration.** Define `g_{k+1} := g_k + V_k`, `h_{k+1} := h_k + U_k` from B.39 applied to
   `e_k := f - g_k h_k` at weight `c_k := suppVal φ f u ℓ + k + 1`; the degree bounds keep
   `g_k` monic of fixed degree. Then `e_{k+1} = e_k - (h_k U_k + g_k V_k) - U_k V_k` and both
   correction terms have support value `≥ c_k + 1` (the cross term by B.33). (Landed step:
   `exists_solve_step`'s loop.)
4. **The limit.** B.40 applied to `(g_k)` and to `(h_k)` gives monic `g, h` of the right degrees with
   `suppVal φ (f - g*h) u ℓ = ⊤`, i.e. `f = g*h` (B.08's `gaussVal_eq_top_iff` after B.40's step-1
   conversion). (Landed step: `exists_adicLimit_of_degree_lt`.)
5. **The residual data of the limit.** `resPoly π φ g u ℓ = G` because `g - g₀` has support value
   `> suppVal φ g u ℓ`, so B.30's `resCoeff_eq_zero_iff` makes the residual polynomials equal; same
   for `h`. `IsPure` for `g` and `h`, and `GradedCoprime`, follow from `hGH` and B.35.

**SIZE.** 220 lines. **SPLIT MANDATED → 4**: `B41a.lean` = step 1 (the initial approximation, the
place `resLift` is consumed); `B41b.lean` = step 2 (the error bound); `B41c.lean` = step 3 (the
iteration, with the two correction sequences defined by `Nat.rec` and their invariants);
`B41d.lean` = steps 4–5 and the contract. **This is the chapter's largest node and the fleet must
receive it pre-split.**

**⚠ SIGNATURE HAZARD, DECLARED.** The index arithmetic between `μ_f`, `G.natDegree + H.natDegree` and
`ℓ` is stated loosely in the STATEMENT above and is **pinned in the SIGNATURE**: the conclusion's
degrees are `ℓ * m * G.natDegree` and `ℓ * m * H.natDegree`, and their sum must equal `f.natDegree`.
The stub-landing agent must check `f.natDegree = ℓ * m * (G.natDegree + H.natDegree)` is derivable from
`hpure` + `hprod` + B.30 (it is: B.30 gives `(resPoly).natDegree = sideDeg`, `hprod` gives
`sideDeg = G.natDegree + H.natDegree`, and `IsPure` + B.13 give
`f.natDegree = m * μ_f` with `μ_f = ℓ * sideDeg`) — and if it is not, **this is a blueprint defect and
goes back to this file**, not patched in `leanspec` (0e rule 3).

**SOURCE.** `docs/GMN_citations.md` Thm 1.15 and Thm 1.19 (both are applications of this one engine);
`EFF.HE3.32` (`LEMMA HE3-4`, the residue peel, which is this engine's conclusion read as a class
count); landed `HenselFactorization.lean:393` as template.

**TEETH.** `W12-BLOCK` (`EFF.W12.55`, 0/1,594,670: "Hensel product identity `g·l == f` + fiber
bijection") → **Lean theorem** (the product identity is step 4).

**ENVIRONMENT.** ENV-C.

---

### NODE B.42 [theorem] [fresh]

**STATEMENT.** *THE THEOREM OF THE POLYGON at order 1 (NS-1).* Over the complete bundle, let `φ` be
an order-1 key and `f` monic with `f.map (residue O) = (φ.map (residue O)) ^ μ` and `0 < μ`. Then
there is a finite family of coprime slope pairs `(u_i, ℓ_i)` with **pairwise distinct** slopes
(`u_i * ℓ_j ≠ u_j * ℓ_i` for `i ≠ j`) and monic `f_i` with

* `f = ∏ f_i`;
* each `f_i` is `(u_i, ℓ_i)`-pure;
* `Σ (f_i).natDegree = f.natDegree`;
* the slopes `(u_i, ℓ_i)` are exactly the slopes of `f`'s `φ`-adic polygon, i.e. exactly the coprime
  pairs whose `sideSet φ f u ℓ` has at least two elements.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_slope_factorization (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ) :
    ∃ (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → Polynomial O),
      (∀ p ∈ s, 0 < p.2 ∧ Nat.Coprime p.1 p.2) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 * q.2 ≠ q.1 * p.2) ∧
      (∀ p ∈ s, (F p).Monic ∧ IsPure φ (F p) p.1 p.2) ∧
      f = ∏ p ∈ s, F p ∧
      (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
        (1 < (sideSet φ f u ℓ).card ↔ (u, ℓ) ∈ s))
```

**DEPENDS.** B.13 · B.16 · B.17 · B.18 · B.19 · B.20 · B.30 · B.34 · B.35 · B.41 ·
landed `Uniformity.Hensel.exists_monic_factorization_finset` (as the shape to mirror for the
`Finset` induction).

**PROOF.**
1. **The slope set is finite and bounded.** Every slope `(u,ℓ)` of `f` has `ℓ ≤ μ` (B.20:
   `ℓ ∣ sideLen ≤ μ`) and `u ≤ ℓ * npHgt φ f 0` (the leftmost height, finite by B.18 and `hres`,
   which forces `npHgt φ f j ≥ 1` for `j < μ`). So the slopes live in a fixed
   `Finset.range × Finset.range`, and `s` is a `Finset.filter` of it.
2. **`hres` forces every slope positive.** `f̄ = φ̄^μ` says `dev φ f j ≡ 0 mod π` for `j < μ`
   (a private helper: reduce the development mod `π` and use B.06's uniqueness in
   `(ResidueField O)[X]`), so `npHgt φ f j ≥ 1` for `j < μ`, so `suppVal φ f u ℓ` is attained at
   `j = μ` only when `u = 0`; hence every side with two elements has `u ≥ 1`.
3. **Strong induction on `μ`.** If `s` has at most one element, `f` is already pure (B.34) and the
   family is `{f}`; done.
4. Otherwise pick two distinct slopes and, by B.19, the abscissa `i` they share (the vertex). Choose a
   coprime pair `(w, t)` with slope strictly between them (rational sampling: the interval is
   nonempty in `ℚ`, and `Nat.Coprime`-normalising a mediant gives the pair — a private helper
   `exists_coprime_between`). At `(w,t)` the support value is attained **only at `i`** (B.19 plus
   convexity of the `inf` in the slope — the private helper `onSide_unique_of_between`).
5. **Apply B.41 at the slope `(w,t)`** with `G := Y^{i'}` and `H :=` the remaining factor of
   `resPoly π φ f w t`, where `i'` is `i`'s position on the `(w,t)`-side. Because the support value is
   attained only at `i`, the residual polynomial at `(w,t)` is `C c * Y^{i'}` for a unit `c`, so the
   coprime split to feed B.41 is **not** available in that form — instead apply B.41 at a slope
   `(w,t)` chosen so that the residual polynomial has **two** coprime factors, namely
   `Y^{i'}` and `(the part of degree ≥ 1 with nonzero constant term)`. **This is the step that needs
   the mediant chosen ON a vertex rather than strictly between:** take `(w,t)` to be one of the two
   slopes met at `i` — say the steeper one `(u₁,ℓ₁)` — whose residual polynomial `R₁` has degree
   `d₁ ≥ 1` and nonzero constant term (B.30), and split `R₁ = Y^0 * R₁`… **RESOLVED as follows**: the
   correct split is at the *steepest* slope. Let `(u₁,ℓ₁)` be the slope with the largest value of
   `u/ℓ` in `s` (`Finset.max'` on the mediant order — private helper). Its side spans
   `[j₁, j₁ + ℓ₁ d₁]` with `j₁ = 0` (the steepest side starts at abscissa `0`, since heights left of
   it would violate the `inf`). The residual polynomial at `(u₁,ℓ₁)` for the **whole** `f` has degree
   `d₁` and nonzero constant term; the rest of the polygon contributes the monomial factor. So take
   `G := resPoly π φ f u₁ ℓ₁` (degree `d₁`, nonzero constant term, hence coprime to `Y`) and
   `H := Y^{μ/ℓ₁ - d₁}`, which are coprime because `G.coeff 0 ≠ 0`
   (`IsCoprime` with a power of `Y` ⟺ nonzero constant term — private helper
   `isCoprime_X_pow_iff`). B.41 then peels off the steepest side.
6. The peeled factor `g` has degree `ℓ₁ m d₁ < f.natDegree` (strictly, since `s` has ≥ 2 elements), and
   the cofactor `h` has `h̄ = φ̄^{μ - ℓ₁ d₁}` (B.35 and step 2), with polygon the remaining sides
   (B.35's `suppVal` additivity, which pins the cofactor's support values). Apply the induction
   hypothesis to `h`.
7. The last conclusion (the slope set is exactly the set of `(u,ℓ)` with a two-element side) is B.35
   run in the other direction: the product's support value at any `(u,ℓ)` is the sum of the factors',
   and a two-element side of the product forces one of a factor.

**SIZE.** 180 lines. **SPLIT MANDATED → 4**: `B42a.lean` = the three private helpers
(`exists_coprime_between`, `isCoprime_X_pow_iff`, and the steepest-slope selection);
`B42b.lean` = steps 1–2 (the slope set is a finite `Finset` and every slope is positive);
`B42c.lean` = step 5 (the peel at the steepest slope, the only place B.41 is called);
`B42d.lean` = steps 3, 6–7 (the induction and the contract).

**⚠ THIS NODE IS THE CHAPTER'S CRITICAL-PATH RISK AND ITS STEP 5 IS DECLARED UNSETTLED.** The
STATEMENT is certain — it is `docs/GMN_citations.md` Thm 1.15 verbatim at order 1, `COVERS-ALL-O` by
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-1 — but the *route* went through two candidate splits
above before settling on "peel the steepest side", and the settled version rests on the unproved
geometric claim **"the steepest side starts at abscissa 0"**. That claim is true (a side steeper than
all others must contain the leftmost support point, or the `inf` at its slope would be attained
further right) but it is not among the nodes below, and it must be added as a private helper of
`B42b.lean`. **A cross-reader should not accept step 5 without checking it**, and a fleet agent that
cannot prove it must return `BLOCKED` with the counterexample attempt rather than re-cut the route.
**§14 item 2.**

**SOURCE.** `docs/GMN_citations.md` Thm 1.15 (order-1 theorem of the polygon);
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-1 ([AGNPRW] Thm 4.4 / [GN15] Thm 2.3, `COVERS-ALL-O`);
`EFF.W12.09`, `.27`, `.46` (the corpus's three citation sites); `EFF.HE3.13`.

**TEETH.** `W12-SHAPE` (`EFF.W12.54`, 0/164 over 23 rows, **both directions** — the completeness
half is exactly this node's last conclusion) → **Lean theorem**; `HE6-SEP`
(`EFF.HE6.49`, 4,232 strict-excess certificates) → **executable regression** retained.

**ENVIRONMENT.** ENV-C.

---

### NODE B.43 [lemma] [fresh]

**STATEMENT.** *Uniqueness of the graded factorization.* Under B.41's hypotheses, if `f = g*h` and
`f = g'*h'` with `g, g', h, h'` monic, `g, g'` `(u,ℓ)`-pure with residual polynomial `G` and
`h, h'` `(u,ℓ)`-pure with residual polynomial `H`, and `IsCoprime G H`, then `g = g'` and `h = h'`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem graded_factorization_unique (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g h g' h' : Polynomial O}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hcopGH : GradedCoprime π φ u ℓ g h)
    (hgg' : ∀ hne hne' H₀, resPoly π φ g u ℓ hne H₀ = resPoly π φ g' u ℓ hne' H₀)
    (hhh' : ∀ hne hne' H₀, resPoly π φ h u ℓ hne H₀ = resPoly π φ h' u ℓ hne' H₀)
    (heq : g * h = g' * h') : g = g' ∧ h = h'
```

**DEPENDS.** B.30 · B.33 · B.35 · B.37 · B.39 · landed
`Uniformity.Hensel.monic_factorization_unique` (`HenselFactorization.lean:694`) as template.

**PROOF.** Mirror the landed proof.
1. `g' - g` has degree `< g.natDegree` (both monic of equal degree, landed
   `degree_sub_lt_of_monic_of_natDegree_eq`) and `g*h = g'*h'` gives
   `g*(h - h') = (g' - g)*h'`.
2. Suppose `g ≠ g'`. Let `c := suppVal φ (g' - g) u ℓ`, finite by B.08. From step 1 and B.35's
   additivity, `suppVal φ (h - h') u ℓ = c + suppVal φ h' u ℓ - suppVal φ g u ℓ`.
3. Read residual polynomials at weight `c`: the residual of `g' - g` is a nonzero
   `D ∈ (resField φ)[Y]` of degree `< G.natDegree`, and step 1 gives `G * D' = D * H` in
   `(resField φ)[Y]` for the corresponding residual `D'` of `h - h'`. Coprimality of `G` and `H`
   forces `G ∣ D`, contradicting `D ≠ 0` and `D.degree < G.degree`.
4. Hence `g = g'`, and then `h = h'` by cancelling `g` in `g*h = g*h'` (`O[X]` is a domain).

**SIZE.** 60 lines.

**SOURCE.** landed `HenselFactorization.lean:694`; `docs/GMN_citations.md` Thm 1.15 (the
factorization's uniqueness is implicit in "`f_φ = F_1 … F_g`" being well defined).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-C.

---

### NODE B.44 [lemma] [fresh]

**STATEMENT.** *The integral-slope shortcut, as an independent check.* Let `φ = X` (so `m = 1`) and
let `f` be monic of degree `n > 0` with `IsPure X f u 1` and `suppVal X f u 1 = u * n`. Then
`f = G.scaleRoots (π^u)` for a monic `G` of degree `n` with
`G.map (residue O) = resPoly π X f u 1 _ H₀` (up to the identification `resField X ≅ ResidueField O`),
and `typeOf f = typeOf G`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_scaleRoots_of_pure_integral (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (hn : 0 < f.natDegree) {u : ℕ} (hpure : IsPure X f u 1)
    (hsupp : suppVal X f u 1 = ((u * f.natDegree : ℕ) : ℕ∞)) :
    ∃ G : Polynomial O, G.Monic ∧ G.natDegree = f.natDegree ∧
      f = G.scaleRoots (π ^ u) ∧ typeOf f = typeOf G ∧
      (∀ i, IsLocalRing.residue O (G.coeff i) = digAt π (u * (f.natDegree - i)) (f.coeff i))
```

**DEPENDS.** B.15 · B.21 · B.24 · B.28 · landed `Uniformity.Density.exists_monic_scaleRoots`,
`exists_monic_scaleRoots_typeOf` (`ScaleExtraction.lean:92,136`), `typeOf_scaleRoots`
(`TypeOfInvariance.lean:486`).

**PROOF.**
1. B.15's `suppVal_X_iff` converts `hsupp`'s `≥` half into `∀ i < n, π^(u*(n-i)) ∣ f.coeff i`.
2. Landed `exists_monic_scaleRoots_typeOf hπ hf u` (step 1 is exactly its hypothesis) gives monic `G`
   with `G.natDegree = f.natDegree`, `f = G.scaleRoots (π^u)` and `typeOf f = typeOf G`.
3. The residue identity: `f.coeff i = π^{u(n-i)} * G.coeff i` (`Polynomial.coeff_scaleRoots`), so
   B.22's `digAt_eq` gives the claim.

**SIZE.** 26 lines. **SPLIT MANDATED → 3 only if the `resField X ≅ ResidueField O` identification is
not `rfl`**: `resField X = AdjoinRoot (X.map (residue O)) = AdjoinRoot X`, and
`AdjoinRoot X ≃ₐ ResidueField O` needs mathlib's `AdjoinRoot.adjoinRootXEquivField` or an explicit
`AdjoinRoot.equiv`; **the stub-landing agent must resolve this before B.44 fires**, and if the
identification is not available the SIGNATURE drops the `resPoly` clause and keeps only the `digAt`
clause (which is representation-free). Booked as a declared signature risk.

**⚠ WHY THIS NODE EXISTS.** It is the chapter's **independent cross-check on the graded engine**: for
`m = 1` and `ℓ = 1` the entire dissection is landed API, so B.41/B.42 restricted to that case must
agree with B.44. The corpus does the analogous internal decorrelation at `EFF.HE3.34`
("at `μ ≤ 3`, HE6.A agrees with HE3-4 — internal decorrelation"). **If B.44 and B.42 disagree at
`m = ℓ = 1`, the graded engine is wrong.** The disagreement test is B.83's gate.

**SOURCE.** `spec/CERTAIN_NODES_2026-08-14.md` CN-12/CN-13; `EFF.HE3.34` (the decorrelation pattern);
landed `ScaleExtraction.lean`.

**TEETH.** `W12-L1X` (`EFF.W12.55`, 0/1,594,090, "FRESH direct cubic read vs SEALED W-11 classifier,
pointwise" — a cross-implementation check) → **executable regression** retained; this node is the
Lean analogue of that cross-implementation discipline.

**ENVIRONMENT.** ENV-C.

---

### NODE B.45 [lemma] [fresh]

**STATEMENT.** *The residual factorization exists and its factors are pairwise coprime.* Let `K` be a
finite field and `R ∈ K[Y]` monic of positive degree. Then there is a `Finset` of monic irreducible
`ψ` and multiplicities `a : K[Y] → ℕ` with `R = ∏ ψ^{a ψ}`, the `ψ` pairwise non-associated, hence
pairwise coprime; and `R` is separable iff every `a ψ = 1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_residual_factorization {K : Type*} [Field K] [Finite K]
    {R : Polynomial K} (hR : R.Monic) (hd : 0 < R.natDegree) :
    ∃ (s : Finset (Polynomial K)) (a : Polynomial K → ℕ),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ) ∧ (∀ ψ ∈ s, 0 < a ψ) ∧
      (∀ ψ ∈ s, ∀ χ ∈ s, ψ ≠ χ → IsCoprime ψ χ) ∧
      R = ∏ ψ ∈ s, ψ ^ a ψ ∧
      (R.Separable ↔ ∀ ψ ∈ s, a ψ = 1)
```

**DEPENDS.** B.27 · mathlib `UniqueFactorizationMonoid.factors`, `Polynomial.Monic.factors`-style
API, `Polynomial.Separable`, `EuclideanDomain.isCoprime_of_...`
(**the concrete route**: use `UniqueFactorizationMonoid.normalizedFactors R` — over `K[Y]` the
normalisation is "monic", so the normalised factors are monic irreducible — and take
`s := (normalizedFactors R).toFinset`, `a ψ := (normalizedFactors R).count ψ`; coprimality of distinct
monic irreducibles is `(Irreducible.coprime_iff_not_dvd).2` plus
`Irreducible.dvd_irreducible_iff_associated`).

**PROOF.**
1. `R ≠ 0` from `hR`; `normalizedFactors R` is a multiset of monic irreducibles with product
   associated to `R`, and both are monic, so the product **equals** `R`
   (`Polynomial.eq_of_monic_of_associated`).
2. `s`, `a` as in DEPENDS; `Finset.prod_pow_eq_prod` of the multiset (`Multiset.toFinset_prod_pow`,
   or `Finset.prod_multiset_count`).
3. Coprimality: distinct monic irreducibles are non-associated, so neither divides the other, and in
   a PID that is coprimality.
4. Separability: `R.Separable ↔ Squarefree R` by B.27, and `Squarefree (∏ ψ^{a ψ}) ↔ ∀ ψ, a ψ ≤ 1` in
   a UFD (`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`), which with `0 < a ψ`
   is `a ψ = 1`.

**SIZE.** 44 lines.

**SOURCE.** `docs/GMN_citations.md` Thm 1.19 ("`R_λ(f) ∼ ψ_1^{a_1} … ψ_t^{a_t}` into
pairwise-distinct monic irreducibles in `F_φ[y]`"); `EFF.HE3.32` ("`R_λ = Π_r r^{m_r}`");
`EFF.W12.25` (the censuses are indexed by exactly this factorization type).

**TEETH.** `W12-CENSUS4` (`EFF.W12.57`, fires 8×) → **executable regression** retained.

**ENVIRONMENT.** ENV-D + `[Finite K]`.

---

### NODE B.46 [lemma] [fresh]

**STATEMENT.** *A residual factor splits off, one at a time.* Let `K` be a field and
`R = ψ^a * S` with `ψ` monic irreducible, `0 < a`, and `¬ ψ ∣ S`. Then `IsCoprime (ψ^a) S`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem isCoprime_pow_of_not_dvd {K : Type*} [Field K] {ψ S : Polynomial K}
    (hψ : Irreducible ψ) {a : ℕ} (h : ¬ ψ ∣ S) : IsCoprime (ψ ^ a) S
```

**DEPENDS.** mathlib `Irreducible.coprime_iff_not_dvd`, `IsCoprime.pow_left`.

**PROOF.**
1. `IsCoprime ψ S` by `(hψ.coprime_iff_not_dvd).2 h` (in `K[Y]`, a PID; the mathlib name may be
   `EuclideanDomain.isCoprime_of_...` — **confirm**).
2. `IsCoprime.pow_left`.

**SIZE.** 6 lines.

**SOURCE.** `docs/GMN_citations.md` Thm 1.19; `EFF.HE3.32`.

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-D.

---

### NODE B.47 [lemma] [fresh]

**STATEMENT.** *The degree of a residual piece.* In the situation of B.41, if `G = ψ^a` with `ψ`
monic irreducible of degree `d_ψ`, then the corresponding factor `g` has
`g.natDegree = ℓ * m * a * d_ψ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem natDegree_of_residual_piece {φ : Polynomial O} {u ℓ : ℕ} {g : Polynomial O}
    {ψ : Polynomial (resField φ)} {a : ℕ}
    (hg : g.natDegree = ℓ * φ.natDegree * (ψ ^ a).natDegree) :
    g.natDegree = ℓ * φ.natDegree * a * ψ.natDegree
```

**DEPENDS.** mathlib `Polynomial.natDegree_pow`.

**PROOF.**
1. `(ψ^a).natDegree = a * ψ.natDegree` (`natDegree_pow`); rewrite and `ring`.

**SIZE.** 4 lines. **This node is deliberately trivial**: it is the place the corpus's degree formula
is *stated* in the shape every consumer quotes, so that no consumer has to unfold `natDegree_pow`
inline. `docs/GMN_citations.md` Thm 1.19/Cor 1.20 and [GN15] Thm 2.3's
`deg g_{λ,ψ} = e_λ · ord_ψ(R) · deg ψ · deg φ` is exactly `ℓ * a * d_ψ * m`.

**SOURCE.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-2, quoting [GN15] Thm 2.3:
"`deg g_{λ,ψ} = e_λ ord_ψ(R_{r+1,λ}(g)) deg ψ deg φ`"; `EFF.HE3.32` (`|S_r| = D′ℓ deg r`, the same
number read as a class size).

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, all 5 `μ=3` stage types) → **executable regression**
retained.

**ENVIRONMENT.** ENV-A.

---

### NODE B.48 [theorem] [fresh]

**STATEMENT.** *THE THEOREM OF THE RESIDUAL POLYNOMIAL at order 1 (NS-2, first half).* Over the
complete bundle, let `φ` be an order-1 key, `0 < ℓ`, `Nat.Coprime u ℓ`, and let `f` be monic and
`(u,ℓ)`-pure with residual polynomial `R` of degree `d > 0`. Write `R = c * ∏_{ψ ∈ s} ψ^{a ψ}` by
B.45 (`c` a unit). Then there are monic `f_ψ` with

* `f = ∏_{ψ ∈ s} f_ψ`;
* each `f_ψ` is `(u,ℓ)`-pure with residual polynomial a unit times `ψ^{a ψ}`;
* `(f_ψ).natDegree = ℓ * m * a ψ * ψ.natDegree`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_residual_dissection (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O} (hf : f.Monic)
    (hpure : IsPure φ f u ℓ) (hne : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f 0 = (H₀ : ℕ∞)) (hd : 0 < sideDeg φ f u ℓ hne) :
    ∃ (s : Finset (Polynomial (resField φ))) (a : Polynomial (resField φ) → ℕ)
      (F : Polynomial (resField φ) → Polynomial O),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ ∧ 0 < a ψ) ∧
      f = ∏ ψ ∈ s, F ψ ∧
      (∀ ψ ∈ s, (F ψ).Monic ∧ IsPure φ (F ψ) u ℓ ∧
        (F ψ).natDegree = ℓ * φ.natDegree * a ψ * ψ.natDegree) ∧
      (∀ ψ ∈ s, ∃ (hne' : (sideSet φ (F ψ) u ℓ).Nonempty) (H : ℕ) (c : (resField φ)ˣ),
        resPoly π φ (F ψ) u ℓ hne' H = Polynomial.C (c : resField φ) * ψ ^ a ψ)
```

**DEPENDS.** B.26 · B.27 · B.29 · B.30 · B.35 · B.41 · B.45 · B.46 · B.47.

**PROOF.**
1. Normalise `R` to monic: `R`'s leading coefficient is a unit (B.30 gives `natDegree = d`, and the
   leading coefficient of a nonzero polynomial over a field is a unit), so `R = C c * R'` with `R'`
   monic; B.45 factors `R'`.
2. `Finset.induction_on` over `s`, mirroring landed `exists_monic_factorization_finset`
   (`MultiHensel.lean:111`): peel `ψ₀`, set `G := ψ₀^{a ψ₀}` and `H := ∏_{ψ ∈ s'} ψ^{a ψ}`, coprime by
   B.46 (`¬ ψ₀ ∣ H` because the `ψ` are pairwise non-associated and `ψ₀` is prime).
3. B.41 at `(u,ℓ)` with this `G, H` gives `f = g * h` with `g` pure of residual `ψ₀^{a ψ₀}` and `h`
   pure of residual `H`, degrees as predicted.
4. `natDegree` of `g` is `ℓ * m * (ψ₀^{a ψ₀}).natDegree = ℓ * m * a ψ₀ * ψ₀.natDegree` by B.47.
5. Recurse on `h` (its residual polynomial is `H`, of strictly smaller degree since `0 < a ψ₀` and
   `0 < ψ₀.natDegree`).

**SIZE.** 110 lines. **SPLIT MANDATED → 3**: `B48a.lean` = step 1 (the monic normalisation of `R`);
`B48b.lean` = the `Finset` induction skeleton (steps 2, 5) with `sorry`-free peeling but the B.41 call
abstracted as a hypothesis — **NO: `leanfinal` holds no `sorry`; the abstraction is a
`private theorem` taking the peel as an explicit hypothesis**; `B48c.lean` = the contract, discharging
that hypothesis by B.41.

**SOURCE.** `docs/GMN_citations.md` Thm 1.19 verbatim; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-2
([GN15] Thm 2.3, `COVERS-ALL-O`); `EFF.HE3.32` (`LEMMA HE3-4`); `EFF.W12.27`.

**TEETH.** `W12-ORACLE` (`EFF.W12.56`, 0 bad / 41,923 checks, PARI `factorpadic` per decided member,
class `[IND]`) → **executable regression** retained: PARI is the independent engine and the chapter
does not replace it. `HE-SIG` (`EFF.HE3.52`) → **executable regression** retained.

**ENVIRONMENT.** ENV-C.

---

## 7. §7 — THE `(e,f)` ASSIGNMENT AND THE LEAF THEOREM

### DECISION D-3 — HOW `(e,f)` IS READ, AND THE CHAPTER'S UNCONDITIONAL PERIMETER

**THE DECISION.** `(e,f)` is read **through `leanfinal`'s own `typeOf`**, i.e. through
`inertiaDegOf g = sSup (normDivisors g)` = the gcd of the valuations of the norms from
`AdjoinRoot g` (`TypeOf.lean:193`), and **not** through the corpus's class-size count
`|S_{λ,r}| = D′ℓ·deg r` (H-2). Two consequences, both load-bearing:

* the chapter needs **no algebraic closure, no Galois action and no resultants**;
* the chapter's conclusions are statements about the **order** `AdjoinRoot g`, and it never assumes
  that this order is maximal — `HYP.01` (`typeOf` faithfulness, disposition **NODE [CORE-SET]**) stays
  exactly as open as it was.

**THE PERIMETER.** Write a leaf as `(m, ℓ, u, ψ)`: key degree `m`, coprime slope `−u/ℓ`, residual
factor `ψ` of degree `d` and multiplicity `1`. The chapter proves
`typeOf g = ⟨{(ℓ, m·d)}⟩`:

| region | status | route | nodes |
|---|---|---|---|
| `ℓ = 1`, any `m`, any `d` | **UNCONDITIONAL** | `scaleRoots` + landed `typeOf_inert_of_irreducible_map`; the residual-to-reduction bridge is B.59 | B.44, B.59, B.60 |
| any `ℓ`, any `m`, `d = 1` | **UNCONDITIONAL** | the norm bracket `m ∣ inertiaDegOf g ∣ m·d` (B.55) collapses at `d = 1` | B.49–B.58 |
| `ℓ ≥ 2`, `d ≥ 2` | **CONDITIONAL on `B-BOX-1`** | the bracket leaves `inertiaDegOf g` a multiple of `m` dividing `m·d`; pinning it to `m·d` is the residue-degree lower bound | B.61, B.62 |

**This perimeter strictly contains the corpus's own unconditional perimeter.** `EFF.HE3.33` verbatim:
"*`ℓ ≥ 2` sides.* `ℓd ≤ μ ≤ 3` with `ℓ ≥ 2` forces `d = 1`, so the side carries a SINGLE label …
*non-`K`-rational residual factors on an integer-slope side.* After peeling every `K`-rational root,
the leftover part of `R_λ` has degree `≤ d ≤ 3` and NO `K`-rational root, hence is a SINGLE
irreducible factor `r` … **with no nonemptiness assumption and no base change**" — i.e. HE3's
unconditional region is `{ℓ ≥ 2, d = 1} ∪ {ℓ = 1}`, which is exactly the two rows above. `EFF.HE3.69`
(R8-3, `LEMMA HE3-4D1`) adds `D′ = 1` (`m = 1`) "unconditional at every `μ`", which is the `ℓ = 1`
row plus the `d = 1` row at `m = 1`. **Nothing in this chapter's conditional region was
unconditional in the corpus**, so the chapter loses nothing and states its boundary in Lean rather
than in prose.

**THE TECHNICAL SPINE of the `ℓ ≥ 2` route, in one display.** For `A := AdjoinRoot g` with
`ḡ = φ̄^{ℓd}`:

```
   addVal (Algebra.norm O z)  =  length_O (A ⧸ zA)          (B.50, determinant–length)
   length_O M                 =  m · length_A M             (B.51, A local, residue field resField φ)
   ⟹  m ∣ addVal (norm z)  for every z                     (B.52)

   A ⧸ φ(α)A ≅ (AdjoinRoot φ) ⧸ (dev φ g 0)                (B.53, step 1)
   ⟹  addVal (norm (φ α)) = m · gaussVal (dev φ g 0) = m·u·d (B.53)
   addVal (norm π) = ℓ·m·d                                   (landed norm_algebraMap_rootBasis)
   gcd (m·u·d, ℓ·m·d) = m·d·gcd(u,ℓ) = m·d
   ⟹  inertiaDegOf g ∣ m·d                                  (B.54)
```

The bracket `m ∣ inertiaDegOf g ∣ m·d` is B.55; at `d = 1` it is an equality, and B.56–B.58 turn it
into `typeOf g = ⟨{(ℓ, m)}⟩`. **`gcd(u,ℓ) = 1` is where the coprimality hypothesis finally pays**, and
it pays in the same place the corpus's tooth `HE6-T-BADKEY` (`EFF.HE6.52`) says it must.

---

### NODE B.49 [lemma] [fresh]

**STATEMENT.** *The leaf's order is local with residual residue field.* Let `φ` be an order-1 key and
`g` monic with `g.map (residue O) = (φ.map (residue O)) ^ k` for some `k ≥ 1`. Then
`A := AdjoinRoot g` is a local ring whose maximal ideal is the preimage of `(φ̄)` under
`A → A ⧸ πA ≅ (ResidueField O)[X] ⧸ (φ̄^k)`, and there is a ring isomorphism
`IsLocalRing.ResidueField A ≃+* resField φ`. In particular
`Module.finrank (ResidueField O) (ResidueField A) = φ.natDegree`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

noncomputable instance instLocalRingAdjoinRoot {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    IsLocalRing (AdjoinRoot g)

noncomputable def residueFieldEquiv {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    IsLocalRing.ResidueField (AdjoinRoot g) ≃+* resField φ
```

**DEPENDS.** B.01 · B.25 · landed `Uniformity.Density.isMaximal_map_maximalIdeal_adjoinRoot`
(`InertLeaf.lean:71`, the `k = 1` case, whose proof is the template) ·
`Uniformity.Density.isUnit_of_notMem_map_maximalIdeal` (`InertLeaf.lean:92`) ·
mathlib `AdjoinRoot.quotMapOfEquivQuotMapCMapSpanNewtonMap`-style quotient identifications
(**the concrete route**: `AdjoinRoot g ⧸ π = O[X] ⧸ (g, π) ≅ (ResidueField O)[X] ⧸ (ḡ)` by
`Ideal.quotientEquivAlgOfEq` and `Polynomial.quotientSpanXSubCAlgEquiv`-style transport; the honest
statement of the route is "reduce mod `π` first, then mod `ḡ`", i.e.
`AdjoinRoot.quotEquivQuotMap`).

**PROOF.**
1. `A ⧸ πA ≅ (ResidueField O)[X] ⧸ (ḡ)` (reduce the two quotients in the other order).
2. `ḡ = φ̄^k` with `φ̄` irreducible, so `(ResidueField O)[X] ⧸ (φ̄^k)` is a **local** ring: its unique
   maximal ideal is `(φ̄)/(φ̄^k)`, because `(φ̄^k)` has a unique minimal prime over it in a PID.
   (`Ideal.isPrimary`/`IsLocalRing.of_unique_max_ideal`; the concrete route is
   `Polynomial.isLocalRing_quotient_pow_irreducible`, a private helper if the pin lacks it: every
   element is either a unit or in `(φ̄)`, since `(φ̄)` is maximal and the quotient's nonunits are
   exactly the elements of `(φ̄)/(φ̄^k)`.)
3. A commutative ring `A` with `A ⧸ πA` local and `π` in every maximal ideal (`π ∈ maximalIdeal O`,
   pushed forward) is itself local. (Landed `isMaximal_map_maximalIdeal_adjoinRoot` does the `k = 1`
   case by showing the pushed-forward ideal is maximal; here it is only local, so the argument is
   `IsLocalRing.of_isUnit_or_isUnit_of_add_one` applied through the surjection `A → A ⧸ πA`, using
   that `πA ⊆ Jacobson`.)
4. `ResidueField A = A ⧸ 𝔪_A = ((ResidueField O)[X] ⧸ (φ̄^k)) ⧸ ((φ̄)/(φ̄^k)) ≅
   (ResidueField O)[X] ⧸ (φ̄) = resField φ`.
5. The `finrank` claim is B.26's `finrank_resField` transported along step 4.

**SIZE.** 90 lines. **SPLIT MANDATED → 3**: `B49a.lean` = step 1 (the quotient identification);
`B49b.lean` = step 2 (the local structure of `K[X] ⧸ (φ̄^k)`, a pure residue-field statement, ENV-D);
`B49c.lean` = steps 3–5 and the two contracts.

**⚠ THIS NODE GENERALISES A LANDED NODE AND MUST NOT REDEFINE IT.** `InertLeaf.lean:71` proves the
`k = 1` case in the stronger form "`𝔪·A` is maximal"; at `k ≥ 2` that is **false** (`A ⧸ πA` has
nilpotents), so the generalisation is to "`A` is local with residue field `resField φ`". The landed
declaration is consumed unchanged for `k = 1` and is not touched.

**SOURCE.** `EFF.HE3.10` verbatim: "Stage ring `R = O[x]/(Φ′)` is an order in field `L = K₀(θ)`,
**NOT a complete DVR in general**; carried through `O_L`" — the corpus's own record that the order is
not the maximal order, which is exactly why D-3 works with `AdjoinRoot g` and states its perimeter.
Also `EFF.HE3.10`'s `[r1,F7]` correction (the carrier is `O_L`, not `R`).

**TEETH.** signed non-applicable (a structural lemma).

**ENVIRONMENT.** ENV-C (finiteness enters through B.26 at step 5 only; steps 1–4 are ENV-A).

---

### NODE B.50 [lemma] [fresh]

**STATEMENT.** *The determinant–length identity.* Let `A` be an `O`-algebra that is free of finite rank
`r > 0` as an `O`-module, and let `z ∈ A` with `Algebra.norm O z ≠ 0`. Then

```
addVal O (Algebra.norm O z)  =  (the O-length of A ⧸ zA).
```

Concretely (avoiding any dependence on a `Module.length` API): there are `e : Fin r → ℕ` and an
`O`-module isomorphism `A ⧸ zA ≃ₗ ⨁ i, O ⧸ (π ^ e i)` with
`addVal O (Algebra.norm O z) = (Σ i, e i : ℕ)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_smith_of_norm (hπ : Irreducible π) {A : Type*} [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] (hr : 0 < Module.finrank O A)
    {z : A} (hz : Algebra.norm O z ≠ 0) :
    ∃ e : Fin (Module.finrank O A) → ℕ,
      Nonempty ((A ⧸ (Ideal.span {z}).restrictScalars O) ≃ₗ[O]
        (⨁ i, O ⧸ (Ideal.span {π ^ e i}))) ∧
      IsDiscreteValuationRing.addVal O (Algebra.norm O z) = ((∑ i, e i : ℕ) : ℕ∞)
```

**DEPENDS.** mathlib `Basis.smithNormalForm` / `Submodule.smithNormalForm`
(**confirm the pinned name and shape**; the fact needed is: a submodule of a free module of finite rank
over a PID admits a basis adapted to a basis of the ambient module, with the elementary divisors
dividing one another), `Algebra.norm_eq_matrix_det`, `Matrix.det_diagonal`,
`IsDiscreteValuationRing.addVal`, `LinearMap.det`.

**PROOF.**
1. `Algebra.norm O z = LinearMap.det (LinearMap.mulLeft O z)`
   (`Algebra.norm_apply`/`Algebra.norm_eq_matrix_det` with the free basis).
2. `zA` as an `O`-submodule of `A` is the image of `LinearMap.mulLeft O z`, which is injective because
   its determinant is nonzero (`LinearMap.injective_iff_det_ne_zero` over a domain — **confirm**;
   over an integral domain a linear endomorphism of a finite free module is injective iff its
   determinant is nonzero).
3. `Submodule.smithNormalForm` applied to `zA ⊆ A` gives a basis `b` of `A` and naturals/elements
   `d i` with `zA = span {d i • b i}`, hence
   `A ⧸ zA ≃ₗ ⨁ i, O ⧸ (d i)`. Each `d i ≠ 0` (step 2), so `d i = π^{e i} * unit`
   (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`), giving the direct-sum shape.
4. In the adapted bases the matrix of `mulLeft z` is diagonal with entries `d i` up to a change of
   basis of determinant a unit, so `addVal (det) = Σ addVal (d i) = Σ e i`
   (`AddValuation.map_prod`/`map_mul` and `hπ.addVal_pow`).

**SIZE.** 140 lines. **SPLIT MANDATED → 3**: `B50a.lean` = steps 1–2 (norm = det, injectivity);
`B50b.lean` = step 3 (the Smith normal form transport to the direct sum); `B50c.lean` = step 4 and the
contract.

**⚠ THIS IS THE CHAPTER'S THIRD HARD CORE AND ITS ONLY MATHLIB-API RISK OF THE FIRST KIND.** Everything
else in the chapter is elementary over `leanfinal`'s API; this node needs the PID structure theory
(`Submodule.smithNormalForm`) at exactly the shape mathlib provides it, and **the shape must be checked
before the node is assigned**. If `Submodule.smithNormalForm` in the pin is stated only for
`Basis ι R M` with `ι` a `Fintype` and gives an `∃ (n : ℕ) (bM : Basis (Fin n) …)` package rather than
a decomposition, step 3 becomes a 60-line repackaging and the node grows to ~200 lines. The
**fallback**, if the PID theory proves unusable: state B.50 only for `A` a **DVR** (where
`length_O(A/zA) = f·v_A(z)` is a one-line induction on `v_A(z)`), which suffices for B.53 (where the
ring is `AdjoinRoot φ`, a DVR by B.59's step 1) but **not** for B.52 (where `A` is not a DVR at
`d ≥ 2`). Under that fallback B.52 is lost, the bracket loses its lower half, and the chapter's
`ℓ ≥ 2, d = 1` row becomes conditional too — so the fallback is a real degradation and the
orchestrator must be told, not silently applied. **§14 item 6.**

**SOURCE.** classical (the corpus imports it as part of `EFF.HE6.06`'s "resultant symmetry … Galois
invariance of `v`" package and never isolates it); `EFF.HE3.20` (`LEMMA HE3-1`, the resultant identity
`Σ_ρ dv(Φ″(ρ)) = D′·dv(B₀)`, is the corpus's form of exactly this identity read through roots — this
node is its root-free form).

**TEETH.** `HE-NORM` (`EFF.HE3.50`, 72,134 exact Bareiss/Sylvester integer-resultant identities, 0
violations) → **executable regression** retained: the battery checks the resultant form of this
identity, and the chapter proves the norm form.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.51 [lemma] [fresh]

**STATEMENT.** *Length multiplies by the residue degree.* Let `A` be a local `O`-algebra, module-finite
over `O`, whose residue field has `ResidueField O`-dimension `s`. Then for every `A`-module `M` of
finite length, `length_O M = s * length_A M`. In the elementary-divisor form of B.50: if
`A ⧸ zA ≃ₗ[O] ⨁ i, O ⧸ (π^{e i})` then `s ∣ Σ i, e i`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem residueDeg_dvd_sum_of_local (hπ : Irreducible π) {A : Type*} [CommRing A] [IsLocalRing A]
    [Algebra O A] [Module.Free O A] [Module.Finite O A] {s : ℕ}
    (hs : Module.finrank (ResidueField O) (IsLocalRing.ResidueField A) = s)
    (hmap : (algebraMap O A) '' (maximalIdeal O) ⊆ IsLocalRing.maximalIdeal A)
    {z : A} (hz : Algebra.norm O z ≠ 0) :
    s ∣ (Nat.find (…) : ℕ) -- see PROOF: the contract is stated on `addVal (norm z)` directly
```
**Contract declaration (the one the fleet must land):**
```lean
theorem residueDeg_dvd_addVal_norm (hπ : Irreducible π) {A : Type*} [CommRing A] [IsLocalRing A]
    [Algebra O A] [Module.Free O A] [Module.Finite O A] {s : ℕ}
    (hs : Module.finrank (ResidueField O) (IsLocalRing.ResidueField A) = s)
    {z : A} {k : ℕ} (hk : IsDiscreteValuationRing.addVal O (Algebra.norm O z) = (k : ℕ∞)) :
    s ∣ k
```

**DEPENDS.** B.50 · mathlib `Module.length`-free route below; `IsLocalRing.ResidueField`,
`Module.finrank`, `IsNoetherian`, `Submodule.exists_maximal_chain`-style composition-series API
(**this is the second API risk; the fallback route is stated in the PROOF**).

**PROOF (primary route).**
1. `A ⧸ zA` is an `A`-module of finite length (it is a finitely generated module over a Noetherian
   local ring, `O`-finite, hence of finite `O`-length by B.50, hence of finite `A`-length).
2. Every simple `A`-module is `A ⧸ 𝔪_A = ResidueField A`, whose `O`-length is
   `finrank (ResidueField O) (ResidueField A) = s` (a one-dimensional `ResidueField A`-space is an
   `s`-dimensional `ResidueField O`-space, and each `ResidueField O`-line has `O`-length `1`).
3. `O`-length is additive on short exact sequences, so a composition series of `A ⧸ zA` of `A`-length
   `t` has `O`-length `s * t`.
4. B.50 identifies the `O`-length with `addVal (norm z)`, giving `s ∣ addVal (norm z)`.

**PROOF (fallback route, if a composition-series API is missing from the pin).** Replace steps 1–3 by
a **strong induction on `k`** in the style of landed `natDegree_dvd_addVal_norm`
(`InertLeaf.lean:128`), with the induction step "pick `w ∈ 𝔪_A` with `zA ⊆ wA`" replaced by "pick a
maximal `A`-submodule `N` of `A ⧸ zA`; then `(A ⧸ zA) ⧸ N ≅ ResidueField A` has `O`-length `s`, and
`N` has `O`-length `k − s`, so `s ∣ k − s` by induction". This needs only the existence of a maximal
submodule of a nonzero finitely generated module over a local ring
(`Submodule.exists_le_maximal`/Nakayama), which is certainly in the pin.

**SIZE.** 80 lines (primary) or 110 (fallback).

**⚠ THE `k = 1`, `s = natDegree` CASE IS LANDED.** `InertLeaf.lean:128`
(`natDegree_dvd_addVal_norm`) is exactly this node when `A ⧸ 𝔪A` is a field of degree
`g.natDegree`, and its proof is the fallback route's shape with the maximal-submodule step replaced by
`z = π z'`. **The landed proof is the template and it is known to close** — that is why the fallback is
credible.

**SOURCE.** classical; landed `InertLeaf.lean:128` as the `k = 1` instance; `EFF.HE3.10` (the order
vs maximal-order distinction that makes this the right general form).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.52 [lemma] [fresh]

**STATEMENT.** *The residue-degree lower bound at the key level.* Let `φ` be an order-1 key with
`m = φ.natDegree`, and `g` monic of positive degree with
`g.map (residue O) = (φ.map (residue O))^k`, `k ≥ 1`. Then `m ∣ inertiaDegOf g`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem key_natDegree_dvd_inertiaDegOf (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    φ.natDegree ∣ inertiaDegOf g
```

**DEPENDS.** B.26 · B.49 · B.50 · B.51 · landed `Uniformity.Density.inertiaDegOf_mem_normDivisors`,
`normValues_nonempty`, `normValues` (`TypeOf.lean:182,193,262`).

**PROOF.**
1. `AdjoinRoot g` is local with residue field `resField φ` (B.49), of
   `ResidueField O`-dimension `m` (B.26 transported along B.49's `residueFieldEquiv`).
2. `AdjoinRoot g` is free of finite rank `g.natDegree` over `O` (`AdjoinRoot.powerBasis' hg`).
3. B.51 with `s := m` gives `m ∣ k` for every `k ∈ normValues g`.
4. `inertiaDegOf g` is the greatest common divisor of `normValues g`
   (landed `inertiaDegOf_mem_normDivisors` with `normValues_nonempty hg hd`); `m` is a common divisor
   by step 3 and is positive (`hφ.pos`), so `m ∈ normDivisors g`, hence
   `m ≤ inertiaDegOf g` by landed `le_inertiaDegOf`. **For the divisibility rather than the
   inequality**, use landed `inertiaDegOf_mem_normDivisors`: `inertiaDegOf g ∈ normValues g` is NOT
   claimed by the landed API, so the divisibility must come from `inertiaDegOf g = sSup (normDivisors g)`
   and the fact that `normDivisors g` is closed under lcm — **the honest route**: `m ∈ normDivisors g`
   and `inertiaDegOf g ∈ normDivisors g`, and `Nat.lcm m (inertiaDegOf g) ∈ normDivisors g` (an lcm of
   two common divisors of a set of naturals is a common divisor), so
   `Nat.lcm m (inertiaDegOf g) ≤ inertiaDegOf g` by `le_inertiaDegOf`, forcing
   `m ∣ inertiaDegOf g`. The lcm-closure of `normDivisors` is a **private helper** of this node
   (~10 lines: `Nat.Coprime`-free, from `Nat.lcm_dvd`).

**SIZE.** 40 lines including the lcm-closure helper.

**⚠ THE lcm STEP IS THE NODE'S ONLY SUBTLETY AND IT IS FLAGGED.** `inertiaDegOf` is defined as
`sSup (normDivisors g)`, a supremum in `ℕ`, and "the greatest common divisor" is a *name* for it, not
its definition. Landed `inertiaDegOf_eq_of` (`TypeOf.lean:229`) is the recognition principle
(`k ∈ normValues` and `k` divides all of them ⟹ `inertiaDegOf = k`), and it is the clean route
whenever a witness in `normValues` is available. **B.55 uses `inertiaDegOf_eq_of` and therefore needs
a witness; this node does not have one, which is why it goes through the lcm.**

**SOURCE.** landed `TypeOf.lean`; `docs/GMN_citations.md` Cor 1.20 ("`f(L/K)` is divisible by
`m·deg ψ_i`") — this node is the `m` half of that divisibility; the `deg ψ_i` half is `B-BOX-1`.

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, 0 bad) → **executable regression** retained.

**ENVIRONMENT.** ENV-C.

---

### NODE B.53 [lemma] [fresh]

**STATEMENT.** *The norm of the key's value.* Let `φ` be an order-1 key, `g` monic of positive degree
with `φ ∤ g` (equivalently `dev φ g 0 ≠ 0`), and let `α := AdjoinRoot.root g`. Then

```
addVal O (Algebra.norm O (Polynomial.aeval α φ))  =  φ.natDegree * gaussVal (dev φ g 0),
```

read in `ℕ∞` (both sides are `⊤` iff `dev φ g 0 = 0`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem addVal_norm_key_eval (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree) (h0 : dev φ g 0 ≠ 0) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O (Polynomial.aeval (AdjoinRoot.root g) φ))
      = (φ.natDegree : ℕ∞) * gaussVal (dev φ g 0)
```

**DEPENDS.** B.02 · B.05 · B.07 · B.24 · B.25 · B.36 · B.50 · B.51 · mathlib `AdjoinRoot`,
`Ideal.quotientEquivAlgOfEq`, `AdjoinRoot.quotEquivQuotMap`.

**PROOF.**
1. **The quotient identification.** `AdjoinRoot g ⧸ (φ(α))` `≅` `O[X] ⧸ (g, φ)` `≅`
   `(O[X] ⧸ (φ)) ⧸ (g mod φ)` `=` `AdjoinRoot φ ⧸ (dev φ g 0)`, because `g mod φ = g %ₘ φ = dev φ g 0`
   (B.02 at `j = 0`). Both isomorphisms are `Ideal.quotientEquivAlgOfEq`/the double-quotient
   isomorphism, and the middle one uses that `(g, φ) = (φ, g %ₘ φ)` as ideals of `O[X]`
   (from `modByMonic_add_div`).
2. **`AdjoinRoot φ` is a DVR with uniformizer `π` and residue field `resField φ`.** Local with
   residue field `resField φ` by B.49 at `k = 1` (or landed
   `isMaximal_map_maximalIdeal_adjoinRoot`, which gives the stronger "`πA` is maximal"); its maximal
   ideal is `π·AdjoinRoot φ`, principal; it is a Noetherian domain (`φ` irreducible over `O` by
   `Monic.irreducible_of_irreducible_map hφ.irred`); hence a DVR.
3. **The valuation of `dev φ g 0` in `AdjoinRoot φ` is `gaussVal (dev φ g 0)`.** Its class is
   `π^c * unit` with `c = gaussVal (dev φ g 0)`: divide out `π^c` (B.24's `digPoly_eq_map` route) and
   apply B.36's `resMk_ne_zero` — the residue of the quotient is nonzero in `resField φ`, i.e. the
   quotient is a unit of `AdjoinRoot φ`. **This is the slot lemma doing its real work.**
4. **The length.** `AdjoinRoot φ ⧸ (dev φ g 0) ≅ AdjoinRoot φ ⧸ (π^c)`, whose `O`-length is `m*c`
   (B.51 with `s = m` and `A`-length `c`, or directly: it is free of rank `m` over `O ⧸ π^c`, so its
   `O`-length is `m*c`).
5. **Conclude by B.50** applied to `A := AdjoinRoot g` and `z := φ(α)`: the `O`-length of `A ⧸ zA` is
   `m*c` by steps 1 and 4, hence `addVal (norm z) = m*c`.

**SIZE.** 90 lines. **SPLIT MANDATED → 3**: `B53a.lean` = step 1 (the quotient identification, pure
commutative algebra); `B53b.lean` = steps 2–3 (`AdjoinRoot φ` is a DVR and the slot-lemma valuation
computation); `B53c.lean` = steps 4–5 and the contract.

**⚠ THIS NODE IS THE CHAPTER'S REPLACEMENT FOR `LEMMA HE3-1`.** `EFF.HE3.20` states the corpus's
version as a **resultant identity** `Σ_ρ dv(Φ″(ρ)) = D′·dv(B₀)` — a sum over roots in `K̄₀`. This node
is the same identity with the roots replaced by a length and the resultant by a norm: at `e₁ = 1`,
`dv = addVal`, `D′ = m`, `B₀ = dev φ g 0`, and `Σ_ρ dv(φ(ρ)) = addVal (norm (φ(α)))`. **The
correspondence is exact and it is §14 item 7.**

**SOURCE.** `EFF.HE3.20` (`LEMMA HE3-1`); `EFF.HE3.22` (`LEMMA HE3-1′`, the support-function form of
the same quantity, `dv(B₀) = min_j(dv(A_j)+jκ)` — which is B.14's `suppVal` and connects this node to
B.54).

**TEETH.** `HE-NORM` (`EFF.HE3.50`, 72,134 identities, 0 violations, guarding `.20`) → **Lean
theorem** (the identity `LEMMA HE3-1` becomes this node); `HE-PSI` (`EFF.HE3.51`, 43,528, guarding
`.22`) → **Lean theorem** at B.54.

**ENVIRONMENT.** ENV-C.

---

### NODE B.54 [lemma] [fresh]

**STATEMENT.** *The residue-degree upper bound.* Let `φ` be an order-1 key, `0 < ℓ`,
`Nat.Coprime u ℓ`, `0 < u`, and let `g` be monic of positive degree, `(u,ℓ)`-pure with
`sideDeg = d > 0` and `g.map (residue O) = (φ.map (residue O))^{ℓ*d}`. Then

* `gaussVal (dev φ g 0) = (u * d : ℕ)`;
* `addVal O (Algebra.norm O (φ(α))) = (m * u * d : ℕ)`;
* `addVal O (Algebra.norm O (algebraMap O (AdjoinRoot g) π)) = (ℓ * m * d : ℕ)`;
* `inertiaDegOf g ∣ m * d`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem inertiaDegOf_dvd_key_mul_resDeg (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne) :
    inertiaDegOf g ∣ φ.natDegree * sideDeg φ g u ℓ hne
```

**DEPENDS.** B.13 · B.14 · B.16 · B.18 · B.20 · B.34 · B.53 · landed
`Uniformity.Density.norm_algebraMap_rootBasis` (`TypeOfInvariance.lean:353`),
`inertiaDegOf_dvd` (`TypeOf.lean:218`), `normValues` (`TypeOf.lean:182`).

**PROOF.**
1. **The left height.** `IsPure` at abscissa `μ = ℓ*d` with `npHgt φ g μ = 0` (B.13) gives
   `suppVal φ g u ℓ = (u*ℓ*d : ℕ)`; `IsPure` at abscissa `0` then gives
   `ℓ • npHgt φ g 0 = (u*ℓ*d : ℕ)`, i.e. `gaussVal (dev φ g 0) = npHgt φ g 0 = (u*d : ℕ)` after
   cancelling `ℓ > 0`.
2. **The two norm valuations.** B.53 with step 1 gives `addVal (norm (φ α)) = m*(u*d)`. Landed
   `norm_algebraMap_rootBasis hg π` gives `norm (algebraMap O _ π) = π ^ g.natDegree`, and
   `g.natDegree = m * μ = m*ℓ*d`, so its `addVal` is `ℓ*m*d`.
3. **Both are in `normValues g`.** Each is positive (`0 < u, d, ℓ, m`) and each is the `addVal` of the
   norm of a nonzero element (`φ(α) ≠ 0` because `norm (φ α) ≠ 0` by step 2's finiteness;
   `algebraMap O _ π ≠ 0` because `AdjoinRoot g` is a domain and `π ≠ 0`).
4. **The gcd.** Landed `inertiaDegOf_dvd` gives `inertiaDegOf g ∣ m*u*d` and
   `inertiaDegOf g ∣ ℓ*m*d`, hence `inertiaDegOf g ∣ Nat.gcd (m*u*d) (ℓ*m*d) = m*d*Nat.gcd u ℓ = m*d`
   (`Nat.gcd_mul_left` twice and `hcop`).

**SIZE.** 44 lines.

**⚠ `Nat.Coprime u ℓ` IS CONSUMED HERE AND NOWHERE ELSE IN §7.** Step 4 is the payoff, and it is the
same hypothesis whose necessity `EFF.HE6.52`'s tooth `HE6-T-BADKEY` established by counterexample
(`κ = 6/2` gives two factors with different residues). **Minimum-hypothesis check:** `0 < u` is needed
(at `u = 0` the polygon is horizontal, `g` is not in the `f̄ = φ̄^μ` regime, and step 1's height is
`0`); `hres` is needed only to make `AdjoinRoot g` local for B.53's step 2 — actually B.53 does not
need `hres` at all, so **`hres` is over-strong in this node's signature and should be dropped**; it is
retained only because B.55 consumes both nodes together and the shared hypothesis avoids a
re-derivation. **Flagged as a minimum-hypothesis item for the cross-read (§14 item 8).**

**SOURCE.** `docs/GMN_citations.md` Cor 1.20; `EFF.HE3.22` (`LEMMA HE3-1′`, whose
`dv(B₀) = min_j(dv(A_j)+jκ)` is step 1); `EFF.HE3.26` (`COROLLARY HE3-0′`).

**TEETH.** `HE-PSI` (`EFF.HE3.51`, guarding `.22`) → **Lean theorem** (step 1 is `LEMMA HE3-1′`'s
identity in the pure case).

**ENVIRONMENT.** ENV-C.

---

### NODE B.55 [lemma] [fresh]

**STATEMENT.** *The residue-degree bracket, and its collapse at `d = 1`.* Under the joint hypotheses of
B.52 and B.54:
`φ.natDegree ∣ inertiaDegOf g` and `inertiaDegOf g ∣ φ.natDegree * d`. In particular if `d = 1` then
`inertiaDegOf g = φ.natDegree` and `ramIndexOf g = ℓ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem inertiaDegOf_bracket (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne)) :
    φ.natDegree ∣ inertiaDegOf g ∧ inertiaDegOf g ∣ φ.natDegree * sideDeg φ g u ℓ hne

theorem inertiaDegOf_eq_of_resDeg_one (… same hypotheses …)
    (h1 : sideDeg φ g u ℓ hne = 1) :
    inertiaDegOf g = φ.natDegree ∧ ramIndexOf g = ℓ
```

**DEPENDS.** B.13 · B.20 · B.52 · B.54 · landed `Uniformity.Density.ramIndexOf_mul_inertiaDegOf`
(`TypeOf.lean:275`).

**PROOF.**
1. The bracket is B.52 and B.54 conjoined.
2. At `d = 1` the bracket reads `m ∣ inertiaDegOf g ∣ m`, so `inertiaDegOf g = m`
   (`Nat.dvd_antisymm`).
3. `ramIndexOf g * inertiaDegOf g = g.natDegree = m * ℓ * 1` (landed
   `ramIndexOf_mul_inertiaDegOf`, plus `g.natDegree = m * μ` and `μ = ℓ*d = ℓ`), so
   `ramIndexOf g = ℓ` by cancelling `m > 0`.

**SIZE.** 18 lines.

**SOURCE.** `docs/GMN_citations.md` Cor 1.20; `EFF.HE3.26`; `EFF.HE3.33` (the corpus's own `d = 1`
perimeter).

**TEETH.** `HE-SIG` (`EFF.HE3.52`) → **Lean theorem** at `d = 1`; **executable regression** retained
at `d ≥ 2` (where the bracket is not an equality).

**ENVIRONMENT.** ENV-C.

---

### NODE B.56 [lemma] [fresh]

**STATEMENT.** *The singleton lemma.* Let `σ : FactorizationType` with `σ.degree = n`, `0 < n`, and
suppose every `(e', f') ∈ σ.data` satisfies `n ≤ e' * f'`. Then `σ.data` is a singleton `{(e₀, f₀)}`
with `e₀ * f₀ = n`. If moreover `a ∣ e'` and `b ∣ f'` for every member and `a * b = n`, then
`σ = ⟨{(a, b)}⟩`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem factorizationType_singleton {σ : FactorizationType} {n : ℕ} (hn : 0 < n)
    (hdeg : σ.degree = n) (hge : ∀ p ∈ σ.data, n ≤ p.1 * p.2) :
    ∃ p, σ.data = {p} ∧ p.1 * p.2 = n

theorem factorizationType_eq_of_dvd {σ : FactorizationType} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hdeg : σ.degree = a * b) (hpos : ∀ p ∈ σ.data, 0 < p.1 ∧ 0 < p.2)
    (hA : ∀ p ∈ σ.data, a ∣ p.1) (hB : ∀ p ∈ σ.data, b ∣ p.2) :
    σ = ⟨{(a, b)}⟩
```

**DEPENDS.** landed `Uniformity.Density.FactorizationType.degree` (`LocalData.lean:49`),
`FactorizationType.ext` (`:52`), `efPair_pos_of_mem` (`TypePositivity.lean:55`) ·
mathlib `Multiset.sum_map_le`-style bounds, `Multiset.card_eq_one`.

**PROOF.**
1. `σ.degree = (σ.data.map (fun p => p.1*p.2)).sum = n`. Each summand is `≥ n` by `hge` and `> 0`.
2. If `σ.data.card ≥ 2` the sum is `≥ 2n > n`; if `σ.data.card = 0` the sum is `0 < n`. So
   `card = 1` (`Multiset.card_eq_one`), giving the singleton and `e₀*f₀ = n`.
3. For the second statement: `hA`/`hB` give `a ∣ e₀`, `b ∣ f₀`, so `a*b ∣ e₀*f₀ = a*b`, and with
   positivity `e₀ = a`, `f₀ = b` (`Nat.eq_of_dvd_of_le` twice, or
   `Nat.eq_of_mul_eq_mul_left`). The hypothesis `n ≤ e'*f'` of the first statement is supplied by
   `a ∣ e'`, `b ∣ f'`, positivity, and `a*b = n`.
4. `FactorizationType.ext` closes.

**SIZE.** 30 lines.

**⚠ THIS IS THE NODE THAT REPLACES THE CORPUS'S GALOIS-ORBIT ARGUMENT.** `EFF.HE3.34`'s base step
concludes irreducibility from "A Galois-stable set of size `N` all of whose elements have orbit size
`≥ N` is a single orbit of size exactly `N`", and `EFF.HE6.32` step 3 from the sandwich
`Σ_r|S_{λ,r}| = Σ_rN_r` with `|S_{λ,r}| ≥ N_r`. **Both are counting arguments over `K̄₀`.** This node is
the same pigeonhole run on `FactorizationType.data` instead, which is why the chapter needs no
closure and no Galois action (H-2). It is elementary and it is the chapter's cheapest important node.

**SOURCE.** `EFF.HE3.34` (the orbit argument); `EFF.HE6.32` (the sandwich); landed
`TypePositivity.lean`.

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-A (no `O` beyond the `FactorizationType` namespace; the node is arithmetic).

---

### NODE B.57 [lemma] [fresh]

**STATEMENT.** *Every monic factor of a pure polynomial is pure of the same slope, with additive
residual degree.* Let `φ` be an order-1 key, `0 < ℓ`, `Nat.Coprime u ℓ`, `0 < u`, and `g` monic
`(u,ℓ)`-pure with `sideDeg = d`. If `g = g₁ * g₂` with `g₁, g₂` monic then both `g₁, g₂` are
`(u,ℓ)`-pure and `sideDeg g₁ + sideDeg g₂ = d`; moreover
`g_i.map (residue O) = (φ.map (residue O)) ^ (ℓ * sideDeg g_i)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem isPure_of_monic_factor (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g g₁ g₂ : Polynomial O}
    (hg : g.Monic) (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (heq : g = g₁ * g₂)
    (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty) :
    ∃ (hne₁ : (sideSet φ g₁ u ℓ).Nonempty) (hne₂ : (sideSet φ g₂ u ℓ).Nonempty),
      IsPure φ g₁ u ℓ ∧ IsPure φ g₂ u ℓ ∧
      sideDeg φ g₁ u ℓ hne₁ + sideDeg φ g₂ u ℓ hne₂ = sideDeg φ g u ℓ hne ∧
      g₁.map (IsLocalRing.residue O)
        = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g₁ u ℓ hne₁)
```

**DEPENDS.** B.13 · B.16 · B.18 · B.20 · B.30 · B.33 · B.35.

**PROOF.**
1. `suppVal φ g u ℓ = suppVal φ g₁ u ℓ + suppVal φ g₂ u ℓ` — the ≥ is B.33; the ≤ needs B.35, which
   assumes both factors pure. **Break the circularity** by first proving purity from the extreme
   abscissae: `dev φ g_i 0` and the top development coefficient are pinned by
   `dev φ g 0 = (dev φ g₁ 0) * (dev φ g₂ 0) mod φ` and B.13's `dev_top`, giving
   `npHgt φ g 0 = npHgt φ g₁ 0 + npHgt φ g₂ 0` (B.09's `gaussVal_mul` plus B.31 for the carry) and
   `μ = μ₁ + μ₂`. Both abscissa-`0` and abscissa-`μ_i` points then lie on the respective
   `(u,ℓ)`-lines, because their sum lies on `g`'s line and B.33 gives the one-sided inequality at each
   — a two-line squeeze.
2. With both factors pure, B.35 applies and gives the `suppVal` additivity and the residual
   multiplicativity; `sideDeg` additivity is the degree additivity of `resPoly` (B.30 plus
   `natDegree_mul` over the field `resField φ`).
3. The residual-reduction claim: reduce `g_i` mod `π`; its reduction is a monic divisor of
   `φ̄^{ℓd}`, hence `φ̄^{k_i}` with `k_1 + k_2 = ℓd` (unique factorization in
   `(ResidueField O)[X]`), and `k_i = ℓ * sideDeg g_i` because `g_i.natDegree = m*ℓ*sideDeg g_i`
   (step 2 and B.13).

**SIZE.** 60 lines. **Step 1's squeeze is the node's whole risk** and must be written first.

**SOURCE.** `docs/GMN_citations.md` Thm 1.15 ("`N_φ(F_i)` one-sided of slope `λ_i`" — the factors of a
one-sided polynomial are one-sided); `EFF.HE3.32`.

**TEETH.** `W12-SHAPE` → **Lean theorem**.

**ENVIRONMENT.** ENV-C.

---

### NODE B.58 [theorem] [fresh]

**STATEMENT.** *THE LEAF THEOREM at residual degree 1 (unconditional).* Over the complete bundle, let
`φ` be an order-1 key with `m = φ.natDegree`, `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, and let `g` be
monic, `(u,ℓ)`-pure with `sideDeg φ g u ℓ = 1` and
`g.map (residue O) = (φ.map (residue O))^ℓ`. Then

```
typeOf g = ⟨{(ℓ, m)}⟩,
```

and in particular `g` is irreducible over `O`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem typeOf_leaf_resDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (h1 : sideDeg φ g u ℓ hne = 1)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ ℓ) :
    typeOf g = ⟨{(ℓ, φ.natDegree)}⟩
```

**DEPENDS.** B.13 · B.52 · B.55 · B.56 · B.57 · landed `Uniformity.Density.typeOf_degree`
(`TypeOf.lean:372`), `efPair_pos_of_mem` (`TypePositivity.lean:55`), `monicFactors_spec`,
`typeOf_data`.

**PROOF.**
1. `g.natDegree = m * ℓ` (B.13 with `μ = ℓ * 1`), so `(typeOf g).degree = m*ℓ` (landed
   `typeOf_degree hg`).
2. Let `(e', f') ∈ (typeOf g).data`; by `typeOf_data` it is `efPair g'` for some
   `g' ∈ monicFactors g`, which is monic irreducible with `0 < g'.natDegree`.
3. `g'` is `(u,ℓ)`-pure with `sideDeg g' ≤ 1` (B.57 applied to the factorization
   `g = g' * (g / g')`, plus `sideDeg` additivity and `h1`); since `g'` has positive degree its
   `sideDeg` is `≥ 1` (B.20 and `hres`), hence `= 1`, and `sideDeg (g/g') = 0`, forcing
   `g/g' = 1`, i.e. `monicFactors g = {g'}` **already at this step** — so step 4 is not strictly
   needed. **Both routes are recorded; the fleet should take whichever closes, and the second is
   preferred because it avoids B.56.**
4. (Route via B.56.) `m ∣ f'` by B.52 and `ℓ ∣ e'` by B.55 (`inertiaDegOf g' = m`,
   `ramIndexOf g' = ℓ`, applied to `g'` whose data is that of a `d = 1` leaf). B.56's
   `factorizationType_eq_of_dvd` with `a := ℓ`, `b := m`, `a*b = m*ℓ = (typeOf g).degree` gives
   `typeOf g = ⟨{(ℓ, m)}⟩`.
5. Irreducibility is then `monicFactors g = {g}` read off the singleton.

**SIZE.** 50 lines.

**⚠ THE TWO ROUTES OF STEP 3/4 ARE BOTH RECORDED DELIBERATELY.** The short route (step 3) proves
irreducibility from the `sideDeg` bookkeeping alone and then reads `(e,f)` off B.55; the long route
(step 4) never proves irreducibility separately. `EFF.HE3.34` uses the long route (orbit counting) and
`EFF.HE6.32` step 4 uses the short one ("Each class is one irreducible factor … forcing
`e(g_r) = e₁ℓ`, `f(g_r) = f₁d_r` **exactly**"). Recording both is the chapter's hedge on its
critical-path node, and a fleet agent may pick either — but it must say which, because the DEPENDS
differ.

**SOURCE.** `docs/GMN_citations.md` Cor 1.20 ("in particular, if `a_i = 1` then `G_i` is irreducible,
`f(L/K) = m·deg ψ_i`, `e(L/K) = e`"); `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-2 ([GN15] Thm 2.3's
last clause, `COVERS-ALL-O`); `EFF.HE6.32` step 4; `EFF.HE3.34`; `EFF.W12.27`.

**TEETH.** `W12-ORACLE` (`EFF.W12.56`, `[IND]`, 0 bad / 41,923 PARI checks) → **executable
regression** retained (PARI remains the independent engine); `HE-SIG` (`EFF.HE3.52`, all 5 `μ=3`
stage types) → **Lean theorem** at `d = 1`.

**ENVIRONMENT.** ENV-C.

---

### NODE B.59 [lemma] [fresh]

**STATEMENT.** *The residual-to-reduction bridge at integral slope.* Let `φ` be an order-1 key,
`0 < u`, and let `g` be monic `(u,1)`-pure with `sideDeg = d`, so `g.natDegree = m*d`. Let `G` be the
extracted polynomial of B.44 (`g = G.scaleRoots (π^u)`, `G` monic of degree `m*d`). Then

```
G.map (residue O)  is irreducible over ResidueField O   ↔   resPoly π φ g u 1 _ H₀  is irreducible
                                                             over resField φ,
```

and in that case `(ResidueField O)[X] ⧸ (Ḡ) ≃+* resField φ [Y] ⧸ (resPoly …)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem irreducible_map_iff_irreducible_resPoly (hπ : Irreducible π) {φ : Polynomial O}
    (hφ : IsKey φ) {u : ℕ} (hu : 0 < u) {g G : Polynomial O} (hg : g.Monic) (hG : G.Monic)
    (hGdeg : G.natDegree = g.natDegree) (hscale : g = G.scaleRoots (π ^ u))
    (hpure : IsPure φ g u 1) (hne : (sideSet φ g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ g 0 = (H₀ : ℕ∞)) :
    Irreducible (G.map (IsLocalRing.residue O)) ↔ Irreducible (resPoly π φ g u 1 hne H₀)
```

**DEPENDS.** B.15 · B.24 · B.25 · B.26 · B.28 · B.29 · B.30 · B.44 · mathlib
`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`-style transfer is **not** what is
needed; the needed tool is the identification of the two residue algebras
(`(ResidueField O)[X] ⧸ (Ḡ)` and `resField φ [Y] ⧸ (R)`) as `ResidueField O`-algebras, plus
`Irreducible` ⟺ the quotient is a field (`Ideal.Quotient.isField_iff_isMaximal`,
`PrincipalIdealRing.isMaximal_of_irreducible`).

**PROOF.**
1. Both quotients are `ResidueField O`-algebras of dimension `m*d`: the left by
   `hGdeg` and `Monic.natDegree_map`, the right by B.26 (`[resField φ : F] = m`) and B.30
   (`(resPoly).natDegree = d`).
2. Construct the isomorphism: the `φ`-development of `g` at the on-side abscissae `0, 1, …, d`
   (spacing `ℓ = 1`) has digits `resCoeff k`; the reduction `Ḡ` has coefficients
   `digAt π (u*(m*d - i)) (g.coeff i)` (B.44's third clause). Assembling, `Ḡ` is the image of
   `resPoly` under the `ResidueField O`-algebra map `resField φ [Y] → (ResidueField O)[X]`
   induced by `y ↦ X^?`… **this is the node's real content and it is where the index bookkeeping
   between the `φ`-development and the plain coefficient expansion is discharged.** The honest
   construction: both algebras are `(ResidueField O)[X, y] ⧸ (φ̄(y), R(X-ish))`-shaped, and the
   isomorphism is `Ideal.quotientEquivAlgOfEq` after showing the two ideals coincide.
3. `Irreducible p` over a field ⟺ `K[X]⧸(p)` is a field (for `p` monic of positive degree). Transport
   along step 2.

**SIZE.** 100 lines. **SPLIT MANDATED → 3**: `B59a.lean` = step 1 (the two dimensions);
`B59b.lean` = step 2 (the algebra isomorphism, the hard part); `B59c.lean` = step 3 and the contract.

**⚠ DECLARED WEAKNESS.** Step 2 is the least-specified step in this chapter. The statement is certain
(it is the standard identification `F[X]/(Ḡ) ≅ F_φ[Y]/(ψ)` for an unramified leaf) but the *route* is
described rather than pinned, and the index bookkeeping between a `φ`-development and a plain
coefficient expansion at `ℓ = 1` has not been checked line by line here. **A fleet agent that cannot
close step 2 must return `BLOCKED` with the two candidate ideals written out**, and the fallback is to
drop B.60's `ℓ = 1` row to the `d = 1` case (already covered by B.58), i.e. to lose the
`ℓ = 1, d ≥ 2` region — **which would leave the whole `d ≥ 2` region conditional and would make
`B-BOX-1` the chapter's only open item rather than one of two.** §14 item 9.

**SOURCE.** `docs/GMN_citations.md` fact (I) and Cor 1.20; `EFF.HE3.69` (R8-3, `LEMMA HE3-4D1`: "the
classical Newton-polygon and Hensel read produces the corresponding factor of degree `ℓd`" — this node
is the `ℓ = 1` half of that read); `EFF.HE3.68` (R8-2, `LEMMA HE3-4U`, the unramified branch).

**TEETH.** `HE-SIG` → **executable regression** retained.

**ENVIRONMENT.** ENV-C.

---

### NODE B.60 [theorem] [fresh]

**STATEMENT.** *THE LEAF THEOREM at integral slope (unconditional, any `d`).* Over the complete
bundle, let `φ` be an order-1 key with `m = φ.natDegree`, `0 < u`, and let `g` be monic `(u,1)`-pure
with `sideDeg = d > 0`, `g.map (residue O) = (φ.map (residue O))^d`, and residual polynomial
irreducible over `resField φ`. Then

```
typeOf g = ⟨{(1, m * d)}⟩.
```

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem typeOf_leaf_integral_slope (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u : ℕ} (hu : 0 < u) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure φ g u 1) (hne : (sideSet φ g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ g 0 = (H₀ : ℕ∞)) (hd : 0 < sideDeg φ g u 1 hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (sideDeg φ g u 1 hne))
    (hirr : Irreducible (resPoly π φ g u 1 hne H₀)) :
    typeOf g = ⟨{(1, φ.natDegree * sideDeg φ g u 1 hne)}⟩
```

**DEPENDS.** B.13 · B.44 · B.59 · landed `Uniformity.Density.typeOf_inert_of_irreducible_map`
(`InertLeaf.lean:179`), `typeOf_scaleRoots` (`TypeOfInvariance.lean:486`).

**PROOF.**
1. B.44 gives monic `G` of degree `g.natDegree = m*d` with `g = G.scaleRoots (π^u)` and
   `typeOf g = typeOf G`. (B.44's hypothesis `suppVal X f u 1 = u*n` is here
   `suppVal φ g u 1 = u * d` from `IsPure` and B.13 — **note the different normalisation: B.44 is
   stated at `φ = X`, and this node needs its general-`φ` analogue.** The general-`φ` analogue is
   B.44's proof with `dev φ` in place of `C ∘ coeff`; **the orchestrator must book B.44 in the
   general-`φ` form, or book a second node B.44′. Recorded as a re-plan item.**)
2. B.59 with `hirr` gives `Irreducible (G.map (residue O))`.
3. Landed `typeOf_inert_of_irreducible_map hG (0 < m*d) step 2` gives
   `typeOf G = ⟨{(1, G.natDegree)}⟩ = ⟨{(1, m*d)}⟩`.
4. Conclude by step 1.

**SIZE.** 30 lines.

**⚠ RE-PLAN ITEM DECLARED IN STEP 1.** B.44 as written is `φ = X`-only; this node needs the
general-`φ` extraction. The orchestrator should either widen B.44's SIGNATURE to a general order-1 key
(preferred: the landed `exists_monic_scaleRoots` is stated for a general monic `f` and does not know
about `φ`, so the widening is in the *hypothesis translation* B.15 → general `φ`, i.e. a new node) or
book **B.44′**. This is a blueprint defect of the "missing supplier" class — exactly chapter G's
**A-7** (`G.31`'s missing supplier, cured by adding a micro-node `G.30a`) — and it is booked here
rather than discovered at fleet time. **§14 item 10.**

**SOURCE.** `EFF.HE3.68`, `.69` (R8-2/R8-3, the unramified and `D′=1` branches, both "PROOF-ONLY" in
the corpus and both proved here); `docs/GMN_citations.md` Cor 1.20; landed `InertLeaf.lean`.

**TEETH.** `HE-SIG`, `W12-ORACLE` → **executable regression** retained.

**ENVIRONMENT.** ENV-C.

---

### NODE B.61 [theorem] [fresh]

**STATEMENT.** *THE LEAF THEOREM in general, conditional on `B-BOX-1`.* Over the complete bundle, let
`φ` be an order-1 key with `m = φ.natDegree`, `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, and let `g` be
monic `(u,ℓ)`-pure with `sideDeg = d > 0`, `g.map (residue O) = (φ.map (residue O))^{ℓd}`, and
residual polynomial `resPoly` a unit times an **irreducible** `ψ` of degree `d`. Assume

```
(B-BOX-1)   ∀ g' ∈ monicFactors g,  m * d ∣ inertiaDegOf g'.
```

Then `typeOf g = ⟨{(ℓ, m*d)}⟩`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem typeOf_leaf_of_resDeg_lower_bound (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (hd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne))
    (hBOX : ∀ g' ∈ monicFactors g,
      φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g') :
    typeOf g = ⟨{(ℓ, φ.natDegree * sideDeg φ g u ℓ hne)}⟩
```

**DEPENDS.** B.13 · B.54 · B.56 · B.57 · landed `typeOf_degree`, `typeOf_data`, `efPair_pos_of_mem`,
`ramIndexOf_mul_inertiaDegOf`, `monicFactors_spec`.

**PROOF.**
1. `g.natDegree = m*ℓ*d` (B.13), so `(typeOf g).degree = m*ℓ*d`.
2. For `g' ∈ monicFactors g`: `m*d ∣ inertiaDegOf g' = f'` by `hBOX`. Also `f' ∣ m*d'` with
   `d' := sideDeg g' ≤ d` by B.57 and B.54 applied to `g'`, so `m*d ∣ m*d'` forces `d' = d`, hence
   `g'.natDegree = m*ℓ*d = g.natDegree`, hence `monicFactors g = {g}` and `f' = m*d`.
3. `ramIndexOf g = g.natDegree / f' = ℓ` (landed `ramIndexOf_mul_inertiaDegOf`).
4. Conclude, or alternatively apply B.56 with `a := ℓ`, `b := m*d`.

**SIZE.** 34 lines.

**⚠ `B-BOX-1` IS AN EXPLICIT HYPOTHESIS, NOT AN AXIOM AND NOT A `sorry`.** It appears in exactly one
place — this node's `hBOX` — and in the corollaries that consume this node (B.71, B.79). H-7 records
its precise content (the order-1 root label: the residue field of the leaf realises a root of `ψ` over
`resField φ`), its ledger neighbours (`HYP.01`, `HYP.12`, both **[CORE-SET]**), and the fact that the
chapter's two unconditional rows (B.58, B.60) do not touch it. **No node outside `hBOX`'s consumers
may assume it**; an agent that finds itself wanting it has left the perimeter and must return
`BLOCKED: B-BOX-1`.

**SOURCE.** `docs/GMN_citations.md` Cor 1.20 (the full statement, of which this is the conditional
Lean form); `EFF.HE6.29` (`[PIN HE6-ROOT-LABEL]`, Cor HE6-2″ — the corpus's proof of exactly `hBOX`,
through the resultant account that H-2 puts out of scope); `EFF.HE3.26` (`COROLLARY HE3-0′`:
"`f₁f_s ∣ f(L_ρ)`").

**TEETH.** `HE6-T-CASEB` (`EFF.HE6.37`, `.52`: "3 distinct PARI σ on identical outer data — box is
real") → **executable regression** retained, and note carefully: that tooth certifies
**HE6-BOX-1** (the *repeated* residual factor, `a ≥ 2`), which is a **different** open item from
`B-BOX-1` (a *multiplicity-1* factor of *degree* `d ≥ 2`). The two must not be conflated; see B.66.

**ENVIRONMENT.** ENV-C.

---

### NODE B.62 [lemma] [fresh] [OPTIONAL — the `B-BOX-1` repair route]

**STATEMENT.** *`B-BOX-1` from the spectral norm.* Let `g` be a leaf as in B.61 and let
`L := FractionRing (AdjoinRoot g)`. Then the unique extension of the valuation of `K = FractionRing O`
to `L` has value group `(1/ℓ)·addVal(K^*)`, its valuation ring has residue field containing a root of
`ψ` over `resField φ`, and consequently `m*d ∣ inertiaDegOf g'` for every monic irreducible factor
`g'` of `g` — i.e. `hBOX` of B.61 holds.

**SIGNATURE.** *(not frozen — this node is OPTIONAL and its interface depends on which mathlib route
survives contact; the orchestrator must re-sign it before it fires.)*

**DEPENDS.** B.30 · B.36 · B.49 · B.53 · mathlib, at our pin `v4.31.0` (rev `fabf563a`), per
`docs/VENDOR_QUARRY_MAP_2026-08-15.md` §2.1:
`Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:695` `spectralNorm_unique`,
`:766` `spectralNorm_unique_field_norm_ext`,
`:987` `spectralNorm_eq_norm_coeff_zero_rpow` (`|x|_L = |N_{L/K}(x)|_K^{1/[L:K]}`),
`:115` `spectralValue`, `:237` `norm_root_le_spectralValue`;
`Mathlib/Analysis/Normed/Field/Krasner.lean:56` `IsKrasner`, `:63` `IsKrasner.krasner`,
`:117` `IsKrasner.of_completeSpace`.

**PROOF SKETCH** (a sketch, not a contract — this node is not fireable as written).
1. `spectralNorm_unique` gives the unique multiplicative extension of the norm to `L`.
2. `spectralNorm_eq_norm_coeff_zero_rpow` converts it to `|N_{L/K}(x)|^{1/[L:K]}`, i.e. gives
   `addVal (norm x) = [L:K] · v_L(x)` after the multiplicative-to-additive translation.
3. `v_L(φ(α)) = u/ℓ` from B.53 and step 2; `Nat.Coprime u ℓ` then forces the value group to contain
   `(1/ℓ)ℤ`.
4. `β := φ(α)^ℓ / π^u` is a unit of the valuation ring, and B.30's `resCoeff` computation gives
   `ψ(β̄) = 0` in the residue field — the **root label**.
5. The residue field therefore contains `resField φ [Y] ⧸ (ψ)`, of `ResidueField O`-degree `m*d`, and
   step 2 gives `m*d ∣ addVal (norm x)` for every `x`.

**SIZE.** unknown; estimated **250–400 lines**, opus-tier, and dominated by a cost the sketch above
hides: **mathlib's spectral norm is `ℝ`-valued and multiplicative while all of `leanfinal` is
`ℕ∞`-valued and additive.** Step 2's "translation" is a real bridge — `addVal` ↔ `‖·‖` with
`‖x‖ = c^{-addVal x}` for a chosen `c > 1` — and it has no precedent anywhere in `leanfinal`
(`StrongHensel.lean:206`'s `section Dictionary` is the only `addVal` plumbing in the repo and it is
divisibility-to-`addVal`, not norm-to-`addVal`).

**⚠ RECOMMENDATION TO THE ORCHESTRATOR: DO NOT FIRE THIS NODE WITH THE CHAPTER.** Land B.58 and B.60
first, ship the chapter with `B-BOX-1` carried as B.61's hypothesis, and book B.62 as a separate unit
with its own design pass. The reason is scheduling, not doubt: B.62 is the only node in the chapter
whose size is not bounded by a landed template, and the two unconditional rows of D-3's perimeter are
worth more than the third row is.

**SOURCE.** `docs/VENDOR_QUARRY_MAP_2026-08-15.md` §2.1; `EFF.HE6.29`; `EFF.HE3.26`;
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-2.

**TEETH.** `HE6-XI` (`EFF.HE6.46`, ξ-side height reads + orthogonality, 24 + 6) → **executable
regression** retained.

**ENVIRONMENT.** ENV-C (plus whatever normed-field instances the mathlib route needs — undetermined).

---

## 8. §8 — NS-6, THE ORDER-0 PEEL, AND `typeOf` TRANSPORT

### NODE B.63 [theorem] [fresh]

**STATEMENT.** *NS-6, the `⇐` direction: separable residuals give a complete leaf factorization.* Over
the complete bundle, let `φ` be an order-1 key and `f` monic with
`f.map (residue O) = (φ.map (residue O))^μ`, `0 < μ`. Suppose that for every slope `(u,ℓ)` of `f`'s
`φ`-adic polygon the residual polynomial is **separable**. Then `f` factors as a product indexed by
pairs `(slope, monic irreducible residual factor)`, each factor being a leaf in the sense of B.58 /
B.60 / B.61, with `(f_{S,ψ}).natDegree = ℓ_S * m * ψ.natDegree`; and

```
(typeOf f).data  =  Σ_{(S,ψ)}  {(ℓ_S, m * ψ.natDegree)}
```
whenever every `(S,ψ)` lies in D-3's unconditional perimeter (`ℓ_S = 1` or `ψ.natDegree = 1`), and in
general under `B-BOX-1` for the pairs outside it.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem typeOf_of_separable_residuals (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hsep : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ f u ℓ).Nonempty,
      1 < (sideSet φ f u ℓ).card → ∀ H₀ : ℕ, npHgt φ f 0 = (H₀ : ℕ∞) →
        (resPoly π φ f u ℓ h H₀).Separable)
    (hperim : ∀ u ℓ : ℕ, ∀ ψ : Polynomial (resField φ), … ) :
    ∃ (T : Finset ((ℕ × ℕ) × Polynomial (resField φ))) (F : _ → Polynomial O),
      f = ∏ t ∈ T, F t ∧
      (typeOf f).data = (T.val.map (fun t => (t.1.2, φ.natDegree * t.2.natDegree)))
```
*(the `hperim` clause is the perimeter/`B-BOX-1` disjunction; its exact form is fixed by B.58/B.60/B.61
and is written out in full in the leanspec stub — see §12 item 4.)*

**DEPENDS.** B.27 · B.42 · B.45 · B.48 · B.58 · B.60 · B.61 · landed
`Uniformity.Density.typeOf_mul` (`TypeOfAlgebra.lean:58`), `monicFactors_mul` (`:46`),
`FactorizationType.degree_mk_add` (`:72`).

**PROOF.**
1. B.42 splits `f` into `(u_i,ℓ_i)`-pure pieces `f_i`, one per slope.
2. B.48 splits each `f_i` according to its residual factorization; `hsep` and B.45 make every
   multiplicity `1`, so each piece has residual a unit times a single irreducible `ψ`.
3. Each piece is a leaf: B.58 if `ψ.natDegree = 1`, B.60 if `ℓ_i = 1`, B.61 under `B-BOX-1`
   otherwise. Its `typeOf` is `⟨{(ℓ_i, m·ψ.natDegree)}⟩`.
4. Landed `typeOf_mul` (iterated over the `Finset` product by `Finset.prod_induction`, with
   monicity preserved) turns the product into the multiset sum.

**SIZE.** 70 lines. **SPLIT CANDIDATE** at step 4 (the `Finset`-indexed `typeOf_mul` iteration is
reusable and the orchestrator should expect a RE-PLAN request for `typeOf_prod`).

**⚠ `typeOf_prod` IS A MISSING SUPPLIER AND IS BOOKED HERE.** Landed `typeOf_mul` is binary; step 4
needs the `Finset`-indexed version. `spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10 already flagged the
gap ("it needs CN-17 (`n`-fold Hensel) AND CN-03 (`typeOf_mul`) AND CN-21 … **Recommendation to the
orchestrator: book it as the FIRST second-layer node**"). It is B.67's DEPENDS too. **Booked as
`B.63a typeOf_prod`** — a 20-line `Finset.prod_induction` — so that two nodes do not each grow a
private copy. §14 item 10.

**SOURCE.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 §3 F-1 verbatim: "(⇐) is [GN15] Thm 2.3's
last clause (`ord_ψ = 1 ⟹ g_{λ,ψ}` irreducible), applied to every `(λ,ψ)`"; `EFF.W12.27`;
`EFF.HE3.15` (DEFINITION 2's clause (a): "the read TERMINATES with every TERMINAL residual polynomial
separable"); `EFF.W12.86` steps 5–6.

**TEETH.** `W12-SHAPE` (0/164, both directions), `W12-ORACLE` (`[IND]`, 0 bad / 41,923) →
**executable regression** retained; `HE-SIG` (`EFF.HE3.52`, all 5 `μ=3` stage types) → **Lean
theorem** inside the perimeter.

**ENVIRONMENT.** ENV-C.

---

### NODE B.64 [lemma] [fresh]

**STATEMENT.** *NS-6, the `⇒` direction: a repeated residual factor forces a further level.* Let `φ`
be an order-1 key, `(u,ℓ)` a slope of `f`, and `ψ` a monic irreducible factor of the residual
polynomial with multiplicity `a ≥ 2`. Then the corresponding factor `g` of `f` (B.48) has

```
g.natDegree = ℓ * m * a * ψ.natDegree  >  ℓ * m * ψ.natDegree,
```

i.e. `g`'s degree strictly exceeds the degree that a single order-1 leaf with the data `(ℓ, ψ)` would
have; consequently `g` is **not** an order-1 leaf for the pair `(u/ℓ, ψ)`, and the order-1 datum does
not determine `typeOf g`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem lt_natDegree_of_multiplicity_two {φ : Polynomial O} {u ℓ a : ℕ} (hℓ : 0 < ℓ)
    (hm : 0 < φ.natDegree) {ψ : Polynomial (resField φ)} (hψ : 0 < ψ.natDegree) (ha : 2 ≤ a)
    {g : Polynomial O} (hg : g.natDegree = ℓ * φ.natDegree * a * ψ.natDegree) :
    ℓ * φ.natDegree * ψ.natDegree < g.natDegree
```

**DEPENDS.** B.47 · mathlib `Nat` arithmetic only.

**PROOF.**
1. `hg` rewrites the goal to `ℓ*m*ψ.natDegree < ℓ*m*a*ψ.natDegree`.
2. `Nat.mul_lt_mul_of_lt_of_le` with `1 < a` and the positivity of `ℓ*m*ψ.natDegree`; close by
   `omega` after `ring_nf`.

**SIZE.** 8 lines.

**⚠ WHY THIS IS THE HONEST FORM OF NS-6's `⇒`.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §3 F-1
gives the route verbatim: "(⇒) is [AGNPRW] Thm 2.10's degree law `deg Q = m·e·deg R(Q)`: a residual
factor `ψ` with `ord_ψ(R) = a ≥ 2` gives `deg g_{λ,ψ} = e_λ·a·deg ψ·deg φ > e_λ·deg ψ·deg φ = deg(lift of ψ)`,
so the type is not `f`-complete and a level must be added." **That is a degree inequality and nothing
more**, which is why this node is eight lines. What it does **not** prove — and what this chapter does
not claim — is that `typeOf g` is genuinely *undetermined* by the order-1 data. That stronger claim is
`HE6-BOX-1`, and it has a machine certificate but no proof: `EFF.HE6.36` widens the box to
`{ℓ≥2, d_r≥1} ∪ {ℓ=1, d_r≥2}` and `EFF.HE6.37`'s tooth `HE6-T-CASEB` exhibits "3 distinct PARI σ on
identical outer data — box is real". **`HE6-BOX-1` IS AN EXPLICIT NON-NODE OF THIS CHAPTER AND MUST NOT
BE GIVEN ONE.** Its ℓ=1 branch lives entirely in `EFF-HE6R1.md` (H-3), its disposition is
disclosure-without-promotion, and a fleet agent who needs it must return `BLOCKED: HE6-BOX-1`.

**SOURCE.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 §3 F-1; `EFF.HE6.36`; `EFF.HE6.37`;
`EFF.HE6R1.09` (`LEMMA HE6R1-1`'s jump condition `ℓ_i·deg r_i ≥ 2`, which is the *level-2* trigger and
a different statement).

**TEETH.** `HE6-T-CASEB` (`EFF.HE6.37`) → **executable regression** retained (the box is certified
real by machine and is not proved here); `HE6R1-T-CRACK` (`EFF.HE6R1.29`, "3 distinct σ at identical
outer data", fired at both `p=3,5`) → **executable regression** retained.

**ENVIRONMENT.** ENV-A.

---

### NODE B.65 [theorem] [fresh]

**STATEMENT.** *NS-6, the biconditional (ledger `HYP.14`).* Over the complete bundle, with `φ` an
order-1 key and `f` monic with `f̄ = φ̄^μ`, `0 < μ`, the following are equivalent:

1. every residual polynomial of every slope of `f` is separable;
2. every `(slope, monic irreducible residual factor)` pair has multiplicity `1`;
3. `f` factors as a product of order-1 leaves, one per such pair, with degrees
   `ℓ_S * m * ψ.natDegree`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem ns6_biconditional (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ) :
    (∀ u ℓ, … (resPoly …).Separable) ↔ (∀ u ℓ ψ, … multiplicity = 1)
```
*(clause 3 is B.63's conclusion and is stated as a separate `iff` in the same file; the SIGNATURE above
freezes the `1 ↔ 2` half, whose statement needs no perimeter hypothesis.)*

**DEPENDS.** B.27 · B.45 · B.63 · B.64.

**PROOF.**
1. `1 ↔ 2` is B.45's last clause (`Separable ↔ ∀ ψ ∈ s, a ψ = 1`), which rests on B.27
   (`Separable ↔ Squarefree` over a finite field).
2. `2 → 3` is B.63.
3. `3 → 2` by degree count: if some `a ψ ≥ 2` then B.64 gives a factor of degree strictly larger than
   any leaf's, contradicting clause 3's degree list.

**SIZE.** 20 lines.

**⚠ THIS NODE DISCHARGES LEDGER ROW `HYP.14`.** `spec/HYPOTHESIS_LEDGER.md` `HYP.14` reads: "`NS-6`
stopping criterion. STATEMENT: The tower stops at order `r` iff every order-`r` residual is separable;
descent continues iff some is inseparable. CLASS: cite-scope-residue. PROPOSED DISPOSITION: NODE —
short GN15/AGNPRW corollary." **The discharge is at order 1 only** (`r = 1`); the order-`r` statement
is chapter C's and this node is its base case. The DAG edge `BP.B.65 → HYP.14` in §11 is therefore a
*partial* discharge and is labelled as such in the `evidence` column.

**SOURCE.** `spec/HYPOTHESIS_LEDGER.md` `HYP.14`; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 and
§3 F-1 ("~½ page, LOW risk"); `docs/GMN_citations.md` Lemma 3.11(3);
`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md` §4 ("NS-6 corollary (B)").

**TEETH.** `W12-SHAPE` (both directions) → **Lean theorem**.

**ENVIRONMENT.** ENV-C.

---

### NODE B.66 [def] [fresh]

**STATEMENT.** *The order-1 type datum.* For `φ` an order-1 key and `f` monic with `f̄ = φ̄^μ` whose
residuals are all separable, the **order-1 datum** of `f` is the multiset of pairs
`(ℓ_S, m · ψ.natDegree)` over all `(slope S, monic irreducible residual factor ψ)`, as a
`FactorizationType`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `order1Type π φ f` : the `FactorizationType` predicted by `f`'s order-1 polygon-and-residual data.
`0` (the empty type) when the data are not separable — the junk branch is never read. -/
noncomputable def order1Type (π : O) (φ f : Polynomial O) : FactorizationType :=
  open Classical in
  ⟨(slopeFinset π φ f).val.bind (fun p =>
      (resFactorFinset π φ f p).val.map (fun ψ => (p.2, φ.natDegree * ψ.natDegree)))⟩
```
*(`slopeFinset` and `resFactorFinset` are the two `Finset`s produced by B.42 and B.45; their
definitions are private helpers of this node, and if either turns out to be reusable the orchestrator
books it separately.)*

**DEPENDS.** B.20 · B.42 · B.45 · landed `FactorizationType`.

**PROOF.** definitional.

**FAITHFULNESS.** `EFF.W12.62` item 2 verbatim: "THEOREM W-12.A is the transcription spec for order-1
menu entries AT EVERY DEGREE (**`typeOf`-keyed by `(C, P_i, λ_{i,S})`**)" — level-0 configuration `C`,
per-branch polygon `P_i`, per-side residual type `λ_{i,S}`. This node is the last two components at a
single branch; the level-0 component is B.67. `EFF.HE3.15` calls the analogous object the **stage type**
`τ_stage(ℓ) := {(e_s^{(i)}, f_s^{(i)})}` with `Σ e_s f_s = μ`, and `EFF.HE3.16` (THEOREM HE3.A) states
the transport `(e,f) ↦ (e₁e, f₁f)` — at `e₁ = 1, f₁ = m` that is `(e,f) ↦ (e, m·f)`, which is exactly
this definition's second component. **Flagged for human review.**

**SIZE.** 16 lines.

**SOURCE.** `EFF.W12.62`; `EFF.HE3.15`; `EFF.HE3.16`.

**TEETH.** `HM3`-side menu rows are chapter G's; here **signed non-applicability** (a definition).

**ENVIRONMENT.** ENV-C.

---

### NODE B.67 [theorem] [fresh]

**STATEMENT.** *The order-0 peel at every degree.* Over the complete bundle, let `f` be monic of
positive degree and let `f.map (residue O) = ∏_{i ∈ s} φ̄_i ^ {a_i}` with the `φ̄_i` monic irreducible
and pairwise distinct. Then `f = ∏_{i ∈ s} f_i` with each `f_i` monic,
`f_i.map (residue O) = φ̄_i^{a_i}`, `f_i.natDegree = a_i * φ̄_i.natDegree`, and

```
(typeOf f).data  =  Σ_{i ∈ s} (typeOf f_i).data.
```

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_order0_peel {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {φ₀ : ι → Polynomial (ResidueField O)}
    {a : ι → ℕ} (hmon : ∀ i ∈ s, (φ₀ i).Monic) (hirr : ∀ i ∈ s, Irreducible (φ₀ i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → φ₀ i ≠ φ₀ j)
    (hres : f.map (IsLocalRing.residue O) = ∏ i ∈ s, (φ₀ i) ^ (a i)) :
    ∃ g : ι → Polynomial O, (∀ i ∈ s, (g i).Monic) ∧ f = ∏ i ∈ s, g i ∧
      (∀ i ∈ s, (g i).map (IsLocalRing.residue O) = (φ₀ i) ^ (a i)) ∧
      (typeOf f).data = ∑ i ∈ s, (typeOf (g i)).data
```

**DEPENDS.** B.46 · B.63a (`typeOf_prod`) · landed
`Uniformity.Hensel.exists_monic_factorization_finset` (`MultiHensel.lean:111`),
`Uniformity.Density.typeOf_mul` (`TypeOfAlgebra.lean:58`), `monicFactors_mul`,
`Uniformity.Density.typeOf_of_residual_coprime` (`TypeOfAlgebra.lean:131`).

**PROOF.**
1. The powers `(φ₀ i)^{a i}` are pairwise coprime: distinct monic irreducibles are non-associated,
   so B.46's `isCoprime_pow_of_not_dvd` applies to each pair (with a `Finset.prod` extension by
   `IsCoprime.prod_right`).
2. Landed `exists_monic_factorization_finset` with `g₀ i := (φ₀ i)^{a i}` gives the monic lifts, the
   product identity, the reductions and the degrees.
3. B.63a's `typeOf_prod` (landed `typeOf_mul` iterated) gives the multiset identity.

**SIZE.** 40 lines.

**SOURCE.** `EFF.W12.21` (`LEMMA W12-S2.1`, "Level-0 product structure (window-exact Hensel
bijection)"); `EFF.W12.22` (simple branches and the level-0 census); `spec/HYPOTHESIS_LEDGER.md`
`HYP.03` (**DISCHARGED**, whose residual scope note reads: "composing this with `typeOf_mul` … into the
full order-0 leaf law at every degree is flagged but not yet assembled
(`spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10) — the row's own '`n≥4` splitting-type assembly'
consumer still awaits that weld"). **This node is that weld.**

**TEETH.** `W12-LVL0` (`EFF.W12.54`, 0/138 violations: 5 cubic level-0 pattern censuses plus their sum
`q³`) → **executable regression** retained; `W12-BLOCK` (0/1,594,670) → **Lean theorem** (the product
identity).

**ENVIRONMENT.** ENV-C.

---

### NODE B.68 [theorem] [fresh]

**STATEMENT.** *THE ORDER-0 LEAF LAW at every degree (`CERTAIN_NODES` REJECTED **R10**).* Over the
complete bundle, let `f` be monic of positive degree with `f.map (residue O)` **separable**, and let
`f.map (residue O) = ∏_{i ∈ s} r̄_i` be its factorization into distinct monic irreducibles. Then

```
typeOf f = ⟨ Σ_{i ∈ s} {(1, (r̄_i).natDegree)} ⟩.
```

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem typeOf_of_separable_reduction {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {r : ι → Polynomial (ResidueField O)}
    (hmon : ∀ i ∈ s, (r i).Monic) (hirr : ∀ i ∈ s, Irreducible (r i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r i ≠ r j)
    (hres : f.map (IsLocalRing.residue O) = ∏ i ∈ s, r i) :
    typeOf f = ⟨∑ i ∈ s, {((1 : ℕ), (r i).natDegree)}⟩
```

**DEPENDS.** B.67 (at `a i = 1`) · landed `Uniformity.Density.typeOf_inert_of_irreducible_map`
(`InertLeaf.lean:179`), `FactorizationType.ext`.

**PROOF.**
1. B.67 at `a i = 1` gives `f = ∏ g i` with `(g i).map (residue O) = r i` irreducible and
   `(typeOf f).data = Σ (typeOf (g i)).data`.
2. Landed `typeOf_inert_of_irreducible_map` gives `typeOf (g i) = ⟨{(1, (g i).natDegree)}⟩`, and
   `(g i).natDegree = (r i).natDegree` (landed `Uniformity.Hensel.natDegree_eq_of_map_eq`).
3. `FactorizationType.ext` closes.

**SIZE.** 22 lines.

**⚠ THIS IS THE NODE `CERTAIN_NODES` CALLED "the single highest-value node not on this list".**
REJECTED **R10** verbatim: "The full order-0 leaf law (`f̄` separable with monic irreducible
factorization `∏ r̄ᵢ` ⟹ `typeOf f = ⟨Σ (1, deg r̄ᵢ)⟩`). Passes F1 and F2 — but FAILS F3: it needs
CN-17 (`n`-fold Hensel) AND CN-03 (`typeOf_mul`) AND CN-21 (the unramified leaf), three internal
edges. **Recommendation to the orchestrator: book it as the FIRST second-layer node once CN-03, CN-17
and CN-21 land.**" All three landed on 2026-08-14, so the node is fireable **immediately** and it
depends only on B.67 inside this chapter. **The orchestrator should fire B.67 + B.68 in wave 1
regardless of the rest of the chapter's schedule**: they are independent of §§3–7 entirely and they
close a named standing gap.

**SOURCE.** `spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10; `spec/HYPOTHESIS_LEDGER.md` `HYP.03`'s
residual-scope note; `EFF.W12.22`.

**TEETH.** `W12-LVL0` (0/138) → **Lean theorem**.

**ENVIRONMENT.** ENV-C.

---

### NODE B.69 [lemma] [fresh]

**STATEMENT.** *The development is shift-covariant.* For `c : O`, `φ` monic and any `f`:
`dev (φ.comp (X + C c)) (f.comp (X + C c)) j = (dev φ f j).comp (X + C c)`; hence
`npHgt`, `suppVal`, `sideSet`, `sideDeg` and (up to the induced isomorphism of residual fields)
`resPoly` are invariant under the shift `X ↦ X + c`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem dev_comp_shift (φ : Polynomial O) (c : O) (f : Polynomial O) (j : ℕ) :
    dev (φ.comp (X + Polynomial.C c)) (f.comp (X + Polynomial.C c)) j
      = (dev φ f j).comp (X + Polynomial.C c)

theorem npHgt_comp_shift (hπ : Irreducible π) (φ : Polynomial O) (c : O) (f : Polynomial O)
    (j : ℕ) : npHgt (φ.comp (X + Polynomial.C c)) (f.comp (X + Polynomial.C c)) j = npHgt φ f j
```

**DEPENDS.** B.02 · B.07 · B.11 · landed `Uniformity.Density.shift` (`TypeOfInvariance.lean:89`),
`shift_apply`, `shift_monic`, `shift_natDegree` · mathlib `Polynomial.comp` as a ring hom
(`algEquivAevalXAddC`).

**PROOF.**
1. The shift is a ring automorphism of `O[X]` preserving degrees (landed `shift`, an `AlgEquiv`), so it
   commutes with monic division: `(f %ₘ φ).comp (X+C c) = (f.comp (X+C c)) %ₘ (φ.comp (X+C c))` by
   the uniqueness clause of monic division (B.06's step-3 helper).
2. Induction on `j` as in B.10.
3. `npHgt` invariance: the shift acts on coefficients by an `O`-linear map with unit determinant, so
   `gaussVal (a.comp (X + C c)) = gaussVal a` — proved by `≤` in both directions using
   `c ↦ -c` for the inverse.

**SIZE.** 26 lines.

**SOURCE.** `EFF.HE3.27` (`LEMMA HE3-2`, the recentering: "Keep `κ > D′h`, `s ∈ K^×`, `w := −C` …
`Φ″ = Φ′ + w`") — the corpus's recentering is a shift of the *key*, and this node is the shift of the
*variable*; the two are the two halves of the recentering calculus, and **only the variable shift is a
chapter-B node**: the key shift `φ ↦ φ − C` changes the order-1 datum and is the descent step, i.e.
chapter C's.

**TEETH.** `HE-T-CAP` (`EFF.HE3.54`) → **executable regression** retained.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.70 [lemma] [fresh]

**STATEMENT.** *The development is scale-covariant at `φ = X`.* For `hπ : Irreducible π`, `w : ℕ` and
`f` monic of degree `n`: `npHgt X (f.scaleRoots (π^w)) j = npHgt X f j + (w * (n - j) : ℕ)` for
`j ≤ n`, hence `suppVal X (f.scaleRoots (π^w)) u 1 = suppVal X f (u + w) 1 + (w * ... )` — precisely,
the polygon is sheared by `w` and the slopes shift by `w`:
`sideSet X (f.scaleRoots (π^w)) (u + w) 1 = sideSet X f u 1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem npHgt_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (w j : ℕ)
    (hj : j ≤ f.natDegree) :
    npHgt X (f.scaleRoots (π ^ w)) j = npHgt X f j + ((w * (f.natDegree - j) : ℕ) : ℕ∞)

theorem sideSet_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (u w : ℕ) :
    sideSet X (f.scaleRoots (π ^ w)) (u + w) 1 = sideSet X f u 1
```

**DEPENDS.** B.15 · B.16 · B.20 · landed `Uniformity.Density.dvd_sub_coeff_of_scaleRoots`
(`ScaleExtraction.lean:61`) · mathlib `Polynomial.coeff_scaleRoots`.

**PROOF.**
1. `npHgt X g j = addVal O (g.coeff j)` (B.15) and
   `(f.scaleRoots (π^w)).coeff j = π^{w*(n-j)} * f.coeff j` (`coeff_scaleRoots` for a monic `f`);
   `AddValuation.map_mul` and `hπ.addVal_pow` give the first claim.
2. Second claim: substitute the first into `OnSide` at `(u+w, 1)` and cancel the common
   `w*n` from both sides of the equality (`Nat` arithmetic, valid because `suppVal` shifts by the same
   constant).

**SIZE.** 24 lines.

**⚠ WHY ONLY `φ = X`.** For a general key `φ`, `scaleRoots` does not act on the `φ`-development in a
closed form (it does not preserve `φ`), so no general statement is available or needed: the only
consumer is B.44/B.60's integral-slope extraction, which is at `φ = X` after B.69's shift. Recorded so
that nobody looks for the general statement.

**SOURCE.** `spec/CERTAIN_NODES_2026-08-14.md` CN-13; landed `ScaleExtraction.lean`;
`EFF.W12.79` (the `κ(T)` correction's level-0 decoration-orbit factor is the counting shadow of this
shear).

**TEETH.** `W12-L1X` (`EFF.W12.55`, 0/1,594,090, cross-implementation) → **executable regression**
retained.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.71 [theorem] [fresh]

**STATEMENT.** *The full order-1 `typeOf` read.* Over the complete bundle, let `f` be monic of positive
degree, let `f.map (residue O) = ∏_{i ∈ s} φ̄_i^{a_i}` with the `φ̄_i` distinct monic irreducible, and
choose monic lifts `φ_i` (order-1 keys). Suppose every block's residual polynomials are separable and
every `(block, slope, residual factor)` triple lies in D-3's unconditional perimeter (or `B-BOX-1`
holds for the triples outside it). Then

```
(typeOf f).data  =  Σ_{i ∈ s}  Σ_{(S,ψ) for block i}  {(ℓ_S, (φ̄_i).natDegree * ψ.natDegree)}.
```

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem typeOf_order1 (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {φ : ι → Polynomial O} {a : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    (hres : f.map (IsLocalRing.residue O)
      = ∏ i ∈ s, ((φ i).map (IsLocalRing.residue O)) ^ (a i))
    (hsep : ∀ i ∈ s, …) (hperim : ∀ i ∈ s, …) :
    (typeOf f).data = ∑ i ∈ s, (order1Type π (φ i) (…the block factor…)).data
```
*(the block factor is the `g i` produced by B.67; the SIGNATURE therefore quantifies over the
existential B.67 supplies, which the leanspec stub spells out — §12 item 4.)*

**DEPENDS.** B.63 · B.66 · B.67 · B.68.

**PROOF.**
1. B.67 peels the blocks and gives the multiset additivity.
2. B.63 computes each block's `typeOf` as its `order1Type` (B.66).
3. Sum.

**SIZE.** 26 lines.

**SOURCE.** `EFF.W12.09` (THEOREM W-12.A: "`σ(T)` is read off by Ore's theorem: one étale piece
`(e_S, d_i·deg ψ)` per side `S` and irreducible residual factor `ψ` of `R_S`"); `EFF.W12.29` (the
`σ(λ)` readout dictionary); `EFF.HE3.16` (THEOREM HE3.A's transport `(e,f) ↦ (e₁e, f₁f)`).

**TEETH.** `W12-SHAPE`, `W12-ORACLE`, `HE-SIG` → **executable regression** retained; the
`σ(λ)` dictionary of `EFF.W12.29` (`(1,1) ↦ {(1,1),(1,1)}`, `(2) ↦ {(1,2)}`, `(1,1,1) ↦ {(1,1)³}`,
`(1,2) ↦ {(1,1),(1,2)}`, `(3) ↦ {(1,3)}`, `e=2` side with degree-1 residual `↦ {(2,1)}`, `e=3` side
`↦ {(3,1)}`) is **this node's instance table** and B.83/B.84's gates check two of its rows.

**ENVIRONMENT.** ENV-C.

---

### NODE B.72 [lemma] [fresh]

**STATEMENT.** *Degree conservation.* `(order1Type π φ g).degree = g.natDegree` for a block `g` whose
residuals are separable; and `(typeOf f).degree = f.natDegree` (landed) is consistent with B.71's sum.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem degree_order1Type (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hsep : …) : (order1Type π φ g).degree = g.natDegree
```

**DEPENDS.** B.13 · B.20 · B.30 · B.42 · B.45 · B.66 · landed `FactorizationType.degree`,
`FactorizationType.degree_mk_add`.

**PROOF.**
1. `(order1Type).degree = Σ_{(S,ψ)} ℓ_S * m * ψ.natDegree`.
2. For each slope `S`, `Σ_ψ ψ.natDegree = sideDeg S` (B.45's factorization has
   `Σ ψ.natDegree * a ψ = (resPoly).natDegree = sideDeg` by B.30, and separability makes `a ψ = 1`).
3. `Σ_S ℓ_S * sideDeg S = μ` — **the polygon's length identity**, which is B.42's degree bookkeeping
   (`Σ (f_S).natDegree = f.natDegree` divided by `m`).
4. `m * μ = g.natDegree` (B.13).

**SIZE.** 26 lines.

**⚠ STEP 3 IS `EFF.HE6.30`(a) AND ITS PROOF WAS INCOMPLETE IN THE SOURCE.** `EFF.HE6.59` (A3 F-2)
records: "completes `HE6-3(a)`'s proof via length argument `Σ L_λ = μ`", and `EFF.HE6.30`'s OPEN-CALL
2 records that this correction "sits **outside** every T2 pin span" and is one of the compilation's most
consequential items. **This chapter obtains `Σ_S ℓ_S d_S = μ` as a corollary of B.42's factorization
rather than as an independent length argument**, which is a different (and, being a degree count over
`O`, more elementary) route. Recorded as §14 item 11.

**SOURCE.** `EFF.HE6.30`(a) as completed by `EFF.HE6.59`; `EFF.HE3.13` ("`Σ_{labels} e_s f_s = μ`
whenever every `R_λ` is separable"); landed `typeOf_degree`.

**TEETH.** `HE6-SEP` (`EFF.HE6.49`, 4,232) → **executable regression** retained.

**ENVIRONMENT.** ENV-C.

---

### NODE B.73 [def] [fresh]

**STATEMENT.** *The descent-trigger predicate.* `NeedsDescent π φ f` holds when some slope of `f`'s
`φ`-adic polygon has a non-separable residual polynomial. By B.65, `¬ NeedsDescent` is exactly the
hypothesis of B.63.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `NeedsDescent π φ f` : some side's residual polynomial is not separable — the order-1 read does
not terminate. -/
def NeedsDescent (π : O) (φ f : Polynomial O) : Prop :=
  ∃ (u ℓ : ℕ) (h : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ), 0 < ℓ ∧ Nat.Coprime u ℓ ∧
    1 < (sideSet φ f u ℓ).card ∧ npHgt φ f 0 = (H₀ : ℕ∞) ∧
    ¬ (resPoly π φ f u ℓ h H₀).Separable
```

**DEPENDS.** B.16 · B.20 · B.29.

**PROOF.** definitional.

**FAITHFULNESS.** `docs/GMN_citations.md` Lemma 3.11(3) at order 1; `EFF.HE6R1.09`'s jump condition is
the **level-2** analogue and must not be conflated (H-3). The quarry has a declaration of the same name
(`lean/LeanUrat/OM/ResidualPolynomial.lean`'s `needsDescent`) but it is `PadicValuation`-wired and
therefore not a quarry copy (H-6); the name coincidence is deliberate and harmless, since the two live
in different projects that are never in the same environment. **Flagged for human review.**

**SIZE.** 12 lines.

**SOURCE.** `docs/GMN_citations.md` Lemma 3.11(3); `EFF.HE3.15`; `EFF.W12.86` step 5.

**TEETH.** signed non-applicable (a definition).

**ENVIRONMENT.** ENV-C.

---

### NODE B.74 [lemma] [fresh]

**STATEMENT.** *The descent trigger is decidable from the window.* `NeedsDescent π φ f` depends only on
the development coefficients at the on-side abscissae and on their digits at the line heights;
consequently (with B.77) it is determined by `f mod π^N` for `N` exceeding every on-side line height.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem needsDescent_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i)
    (hvis : Visible π φ f N) : NeedsDescent π φ f ↔ NeedsDescent π φ f'
```
*(`Visible` is B.75.)*

**DEPENDS.** B.10 · B.73 · B.75 · B.77.

**PROOF.**
1. B.77's level-stability transports `npHgt`, `suppVal`, `sideSet` and `resPoly` from `f` to `f'`
   under `hvis`.
2. `Separable` is a property of `resPoly`, so it transports.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE3.67` (R8-1's recursive certificate, whose clause 2 is exactly "every recentred
value consulted there is either read exactly below `c_ν`, or is known only to be `≥ c_ν` but satisfies
`c_ν > b_{ν,j}`"); `EFF.W12.27` ("All data the read consumes sit at heights `≤ N−1`, so every lift of
the window class shares them").

**TEETH.** `HE-BND` (`EFF.HE3.55`, 3,744 boundary reads, **RE-SCOPED by R8-1**) → **executable
regression** retained, with the re-scoping carried: the battery's decided/undecided profile is scored
only on rows aligned with R8-1's corrected criterion.

**ENVIRONMENT.** ENV-C.

---

## 9. §9 — LEVEL-`N` DECIDEDNESS CERTIFICATES IN FULL GENERALITY

This section turns §§3–8's polynomial-level leaf theory into statements about `leanfinal`'s
level-`N` coefficient classes: **window visibility** (B.75–B.76), **level stability** (B.77–B.78),
and the **decidedness certificates** themselves (B.79–B.82) — at general `O`, every degree `n`,
every window `N`, both characteristics. "Full generality" is measured against two baselines: the
landed `leancheck` suite (`UniformityCheck/N3Cert*.lean`), which is `n = 3` by hand-cased polygon
readings, and the corpus's own certification (`EFF.W12.27`), which quantifies over `disc ≠ 0` lifts
only — H-11 records why this section's conclusions hold for **every** lift of the class. Per H-4 and
the chapter's line-221 commitment: **B.75 and B.79 transcribe `R8-1`'s rewritten recursive
certificate (`EFF.HE3.67`), never the superseded `LEMMA HE3-5` display of `EFF.HE3.37`.**

### DECISION D-4 — WHAT A LEVEL-`N` CERTIFICATE IS, AND WHAT IS *NOT* CLAIMED

**THE DECISION, in three clauses.**

**(a) The decided predicate is `leanfinal`'s landed `DecidedAt`, unweakened.**
`Uniformity.Density.DecidedAt O n σ N c` (`GenuineDensity.lean:66`) quantifies over **every**
lift `a : Fin n → O` with `proj O n N a = c` — no `disc ≠ 0` restriction, no separability
restriction on the lift. The corpus's pinned notion is weaker: `EFF.W12.51` (`W12-BOX-7`)
verbatim, "Decided = certified on window digits for all `disc ≠ 0` lifts", and `EFF.W12.27`
records (with the `[r4, PE4 m2]` strike and its explicit equal-characteristic counter-instance)
that the unrestricted "every lift" was **FALSE for the corpus's σ**, which is read through roots.
This chapter's σ is read through `monicFactors` and `typeOf` is total on monic polynomials
(H-11), so the every-lift statements below are provable — they are **strictly stronger** than
their sources, and every SOURCE field in this section says so where it applies. That divergence
is §14 item 5 (already flagged at H-11).

**(b) Certificate hypotheses are stated on ONE representative's data and the theorem transports
them.** A node below takes a concrete `a : Fin n → O` (or a concrete block `g`), states its
polygon/residual hypotheses on that representative, and concludes `DecidedAt … (proj O n N a)` —
i.e. the same conclusion for every other lift, obtained through the transport layer B.76–B.78,
entered via landed `decidedAt_of_congr` (`DensityAPI.lean:140`, which already performs the
`proj`-to-coefficientwise reduction through `proj_eq_iff_dvd`). The alternative — defining a
window-level "shape datum" type on `Coeff O n N` and stating the certificate on it — is
**rejected** for chapter B: it is the count layer's object (`EFF.W12.08`'s SHAPE `T`, consumed by
the `HT` law), it belongs to chapter C together with `LEMMA W12-HT` (H-10), and nothing in this
chapter's conclusions needs it. The representative-based form is also exactly the landed
`leancheck` idiom (`UniformityCheck/N3CertRam.lean` and its siblings certify concrete coefficient
hypotheses `π² ∣ B₀ ∧ …`), so the §10 gates can fire B.82 with zero adaptation.

**(c) `R8-1`'s certificate is carried at the single order-1 node, and NO uniform-level law is
stated.** `EFF.HE3.67` (R8-1) replaced `LEMMA HE3-5`'s "one more window unit" bound by a
**recursive** criterion — clause 1: "every terminal residual polynomial is separable"; clause 2:
"at every nonterminal node ν, every recentered value consulted there is either read exactly below
`c_ν`, or is known only to be `≥ c_ν` but satisfies `c_ν > b_{ν,j}`" — and refuted the uniform
bound by an explicit counterexample (`f = (Φ′ − C)³ + 5^M`, unbounded `M`). Chapter B's read has
**one** node (H-1: order 1, no recentering chain — the key shift is chapter C's descent step, per
B.69's SOURCE), so the criterion instantiates as: clause 1 = `¬ NeedsDescent` (B.73), clause 2 =
`Visible` (B.75) with the one cap `c = N`. Consequently: (i) B.79/B.80/B.82 state **per-member**
certificates at an explicitly hypothesized `N`; (ii) B.81 states **existence** of a certifying
`N` read off the member's own polygon — R8-1's stratification bullet ("stratifying by complete
read histories and their deepest consulted heights") in its order-1 form; (iii) **no node of this
chapter asserts any `N`-law of the form "decided as soon as `N > (fixed function of the shape)`
uniformly over a family"** — that was the refuted bullet, and its battery table `HE-BND`
(`EFF.HE3.55`) survives only as re-scoped instance evidence, which is how every TEETH field below
scores it.

**THE PERIMETER, restated for this section.** Every certificate below concludes a `typeOf` value
through §7/§8, so D-3's perimeter is inherited verbatim: unconditional at `ℓ = 1` (any `d`) and at
`d = 1` (any `ℓ`); conditional on `B-BOX-1` at `ℓ ≥ 2 ∧ d ≥ 2`, carried as the explicit `hperim`
hypothesis exactly as in B.63 — never assumed silently (H-7). A fleet agent needing `B-BOX-1`
outside an `hperim` clause returns `BLOCKED: B-BOX-1`; one needing `HE6-BOX-1` returns
`BLOCKED: HE6-BOX-1` (it is a NON-NODE, B.64).

---

### NODE B.75 [def] [fresh]

**STATEMENT.** *Window visibility.* For `π : O`, polynomials `φ, f` and a level `N : ℕ`, say the
order-1 read of `f` at the key `φ` is **visible at level `N`** when some coefficient of the
constant development coefficient `dev φ f 0` is not divisible by `π^N` — equivalently (B.76, given
`hπ`), when `npHgt φ f 0 < N`. Since the `φ`-adic polygon of `f` runs from `(0, npHgt φ f 0)` down
to `(μ, 0)` and is convex, `npHgt φ f 0` bounds **every** height the order-1 read consults: every
vertex height, every on-side line height `H₀ − u·k`, and every "strictly above the line" ceiling.
`Visible π φ f N` therefore says: *all data the read consumes sit at heights `≤ N − 1`.*

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

/-- `Visible π φ f N` : the order-1 read of `f` at the key `φ` is contained in the height-`N`
window — some digit of `dev φ f 0` sits strictly below height `N`. Equivalently (given
`Irreducible π`): `npHgt φ f 0 < N`. -/
def Visible (π : O) (φ f : Polynomial O) (N : ℕ) : Prop :=
  ∃ i, ¬ π ^ N ∣ (dev φ f 0).coeff i
```

**DEPENDS.** B.02 (`dev`).

**PROOF.** definitional. Two choices are deliberate. (i) The **digit form** (`∃ i, ¬ π^N ∣ …`)
rather than the valuation form (`npHgt φ f 0 < N`) is primary, because it is literally a statement
about the window — it mentions no `ℕ∞`, and it is the form a certificate checker evaluates on a
level-`N` class; the two are equated in B.76 (`visible_iff_npHgt_lt`, needing `hπ`), which is why
`π` is an argument of the definition. (ii) Visibility is pinned at **abscissa 0**, not per side:
B.76's calculus derives every per-side bound from it (for `0 < ℓ`,
`suppVal φ f u ℓ ≤ ℓ • npHgt φ f 0`, so every on-side height is `≤ npHgt φ f 0`), and a per-side
definition would multiply the transport lemmas by the number of sides for no gain.

**FAITHFULNESS.** Three sources, and the definition must be read against all three.
(1) `EFF.HE3.67` (R8-1, the rewritten certificate — H-4's line-221 commitment) clause 2 verbatim:
"at every nonterminal node ν, every recentered value consulted there is either read exactly below
`c_ν`, or is known only to be `≥ c_ν` but satisfies `c_ν > b_{ν,j}`, so that the required strict
inequality above the supporting line is nevertheless certified." At chapter B's single order-1
node with cap `c = N` (DECISION D-4(c)): values on the hull are read exactly below `N` (their
heights are `≤ npHgt φ f 0 < N`), and values off the hull need only "`≥ hull ceiling`", certified
since `N > npHgt φ f 0 ≥ b_j` for every supporting-line height `b_j`. **The superseded
`LEMMA HE3-5` display (`EFF.HE3.37`) is not transcribed, and no "one more window unit" clause
exists here.**
(2) `EFF.W12.23` verbatim: "Every pinned or priced slot sits at height `≤ P(0) ≤ N−1`: in-window,
no truncation error" — `P(0)` is `npHgt φ f 0` and "`≤ N−1`" is `< N`. Also `EFF.W12.28`'s
per-family visibility clause "`u₀ ≤ N−1`" (there `u₀ = v(b₀) = P(0)` at the TRP center).
(3) The **junk direction is meaningful**: `Visible` is *false* exactly when every digit of
`dev φ f 0` vanishes in-window — `EFF.HE3.55`'s never-decided residue, "the 25 / 49 with vanishing
residual constant (no full side: outside the genre)", is precisely the `¬ Visible` locus, and it
is correct that no certificate below fires there. **Flagged for human review.**

**SIZE.** 8 lines.

**SOURCE.** `EFF.HE3.67` (R8-1 clause 2, the rewritten certificate — transcribed per H-4);
`EFF.W12.23` (the in-window slot-height law); `EFF.W12.28` (the `u₀ ≤ N−1` instances);
`EFF.HE3.55` (the `¬ Visible` residue, read through its R8-1 re-scoping).

**TEETH.** `HE-BND` (`EFF.HE3.55`, 3,744 boundary reads, **RE-SCOPED by R8-1**) → **executable
regression** retained with the re-scoping carried (D-4(c)): the battery's zero-decided row at
`cap < μλ` is instance evidence that invisibility blocks certification; no general `N`-law is
scored.

**ENVIRONMENT.** ENV-A (no `hπ` in the definition; `π` is data. The equivalence lemma is B.76's
and lives in ENV-A').

---

### NODE B.76 [lemma] [fresh]

**STATEMENT.** *The visibility calculus.* Fix `hπ : Irreducible π` and `φ` monic of positive
degree. (i) **The truncation congruence** (`GENHN-3(a)`'s "lift-stability iff `dv < e₁N`" at
`e₁ = 1`): if `π^N ∣ (f − f').coeff i` for every `i`, then for every abscissa `j`

```
min (npHgt φ f j) N  =  min (npHgt φ f' j) N        (in ℕ∞),
```

so heights `< N` transport **exactly** and heights `≥ N` transport **as the bound** `≥ N`.
(ii) `Visible π φ f N ↔ npHgt φ f 0 < (N : ℕ∞)`. (iii) `Visible` is monotone in `N`.
(iv) `Visible` is invariant under `π^N`-congruence of `f`. (v) `Visible π φ f N` holds for some
`N` iff `dev φ f 0 ≠ 0` (and then for every `N > npHgt φ f 0`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem npHgt_min_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (j : ℕ) :
    min (npHgt φ f j) (N : ℕ∞) = min (npHgt φ f' j) (N : ℕ∞)

theorem visible_iff_npHgt_lt (hπ : Irreducible π) {φ f : Polynomial O} {N : ℕ} :
    Visible π φ f N ↔ npHgt φ f 0 < (N : ℕ∞)

theorem visible_mono {φ f : Polynomial O} {N M : ℕ} (hNM : N ≤ M) :
    Visible π φ f N → Visible π φ f M

theorem visible_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) :
    Visible π φ f N ↔ Visible π φ f' N

theorem exists_visible (hπ : Irreducible π) {φ f : Polynomial O} (h0 : dev φ f 0 ≠ 0) :
    ∃ N : ℕ, Visible π φ f N
```

**DEPENDS.** B.02 · B.07 · B.08 (`le_gaussVal_iff`, `gaussVal_eq_top_iff`) · B.10 (`dev_congr`) ·
B.11 · B.75 · mathlib `min_eq_left/right`, `ENat` order lemmas, landed
`Uniformity.Hensel.pow_dvd_iff_le_addVal` (`StrongHensel.lean`, the `addVal`/divisibility
dictionary).

**PROOF.**
1. (i): B.10's `dev_congr` gives `π^N ∣ (dev φ f j − dev φ f' j).coeff i` for every `i`, i.e.
   `(N : ℕ∞) ≤ gaussVal (dev φ f j − dev φ f' j)` by B.08's `le_gaussVal_iff`. For `x, y` with
   `gaussVal (x − y) ≥ N`: if `gaussVal x < N` then `gaussVal y = gaussVal x` (the minimum
   coefficient valuation is untouched by a perturbation of valuation `≥ N` — `AddValuation`
   ultrametric on each coefficient, via `min`-of-`addVal` case analysis); if `gaussVal x ≥ N` then
   `gaussVal y ≥ N` (`y = x − (x − y)`, both arguments `≥ N`). Both branches together are exactly
   the `min`-truncation identity.
2. (ii): `Visible` unfolds to `¬ ∀ i, π^N ∣ (dev φ f 0).coeff i` (pushing `∃¬` through `¬∀`),
   which by B.08's `le_gaussVal_iff` is `¬ ((N : ℕ∞) ≤ gaussVal (dev φ f 0))`, i.e.
   `npHgt φ f 0 < N` by `not_le`.
3. (iii): `π^M ∣ x → π^N ∣ x` for `N ≤ M` (`pow_dvd_pow` + `dvd_trans`), contrapose the witness.
4. (iv): (i) at `j = 0` truncated below `N`: `npHgt φ f 0 < N ↔ npHgt φ f' 0 < N` reads off the
   `min` identity (`min a N < N ↔ a < N`); then (ii) twice. *(This is where `hφ`/`hd` enter, via
   B.10; (ii) and (iii) are hypothesis-free beyond `hπ`.)*
5. (v): `h0` gives `gaussVal (dev φ f 0) ≠ ⊤` (B.08's `gaussVal_eq_top_iff`), so it is some
   `(H₀ : ℕ∞)`; take `N := H₀ + 1` and apply (ii).

**SIZE.** 44 lines. **Five public declarations — one object** (the visibility calculus), on the
B.20 precedent; if the merge queue objects, the split boundary is `{npHgt_min_congr}` in
`B76a.lean` (it is the transport engine, consumed by B.77) and the four `Visible` lemmas in
`B76b.lean`.

**⚠ CLAUSE (i) IS THE WHOLE TRANSPORT ENGINE AND IT IS DELIBERATELY `min`-TRUNCATED.** The naive
statement "`npHgt φ f' j = npHgt φ f j`" is **false** at heights `≥ N` (the class contains lifts
of every deeper height — R8-1's counterexample lives exactly there, `A₀ = 5^M` with `M`
unbounded), and the pair of one-sided statements ("exact below `N`", "`≥ N` preserved") is
awkward to chain. The `min`-truncation is both, in one rewritable equality. This is the form in
which `GENHN-3(a)` is consumed by R8-1 — `spec/EFF-HE3.md` XREF ledger verbatim:
"`GENHN_PROOF_2026-08-08.md:GENHN-3(a)` … Lift-stability iff `dv < e₁N` / consumed by HE3-5
(`.37`) and R8-1 (`.67`)" — transcribed here at `e₁ = 1` (`dv = addVal`, cap `= N`). The citation
is **through HE3's ledger, not through an EFF-GENHN unit**: chapter B's cut does not include
GENHN (H-3-adjacent scope note), and the half-page proof above is self-contained, so nothing is
consumed from GENHN beyond the name.

**SOURCE.** `EFF.HE3.67` (R8-1's proof cites "LEMMA HE3-2(b) plus GENHN-3(a)" at one node — this
node is the `GENHN-3(a)` half at `e₁ = 1`); `spec/EFF-HE3.md` XREF ledger (`GENHN-3(a)`, count
11); `EFF.W12.23` ("in-window, no truncation error").

**TEETH.** `HE-T-CAP` (`EFF.HE3.54`, Q5: the reader variant that dropped out-of-window digits
disagrees with the sound reader on 17 (`p = 5`) + 43 (`p = 7`) members) → **executable
regression** retained: the tooth is a live check that exactly the `min`-truncation, and nothing
finer, survives the window.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.77 [lemma] [fresh]

**STATEMENT.** *Level stability (the transport pinned by B.74).* Fix `hπ : Irreducible π`, `φ`
monic of positive degree, a level `N`, and `f, f'` with `π^N ∣ (f − f').coeff i` for every `i` and
`f'.natDegree = f.natDegree`. Assume `hvis : Visible π φ f N`. Then the four objects the order-1
read consists of transport from `f` to `f'`:

* **`npHgt`** — truncated at `N`: this is B.76(i), restated here as clause (0) because B.74's
  consumers read it off this node;
* **`suppVal`**: `suppVal φ f' u ℓ = suppVal φ f u ℓ` for **all** `u ℓ : ℕ` (no positivity, no
  coprimality);
* **`sideSet`**: `sideSet φ f' u ℓ = sideSet φ f u ℓ` for all `u ℓ` — hence, definitionally,
  `sideMin`, `sideMax`, `sideDeg` and `IsPure` transport too;
* **`resPoly`**: for every `H₀ : ℕ` with `H₀ < N`,
  `resPoly π φ f' u ℓ h' H₀ = resPoly π φ f u ℓ h H₀` (with `h'` the nonemptiness witness obtained
  from `h` by rewriting along the `sideSet` clause) — hence `Separable`, degree, constant term,
  and the residual factorization all transport.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem suppVal_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) (u ℓ : ℕ) :
    suppVal φ f' u ℓ = suppVal φ f u ℓ

theorem sideSet_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) (u ℓ : ℕ) :
    sideSet φ f' u ℓ = sideSet φ f u ℓ

theorem resPoly_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) {u ℓ : ℕ} (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : H₀ < N) :
    resPoly π φ f' u ℓ (by rw [sideSet_congr hπ hφ hd hff' hdeg hvis]; exact h) H₀
      = resPoly π φ f u ℓ h H₀
```

**DEPENDS.** B.02 · B.07 · B.08 · B.10 (`dev_congr`) · B.11 · B.14 · B.16 · B.20 · B.21/B.22
(`digAt`, `digAt_eq`, `digAt_eq_zero_iff`, `digAt_add`) · B.23/B.24 (`digPoly`) · B.25 (`resMk`) ·
B.28 · B.29 · B.75 · B.76 (`npHgt_min_congr`, `visible_iff_npHgt_lt`).

**PROOF.**
1. **Setup.** Write `H j := npHgt φ f j`, `H' j := npHgt φ f' j`; B.76(i) gives
   `min (H j) N = min (H' j) N` for every `j`; `hvis` gives `H 0 < N` (B.76(ii)). The two `inf`
   ranges agree by `hdeg`.
2. **`suppVal`.** Case `ℓ = 0`: both sides are `inf_j (u*j : ℕ∞) `, attained at `j = 0`, value
   `0` — equal with no hypotheses. Case `0 < ℓ`: put `S := suppVal φ f u ℓ`. Then
   `S ≤ ℓ • H 0 + 0 < ℓ • N` (the `inf` against `j = 0`, `H 0 < N`, and `ℓ`-scaling is strictly
   monotone below `⊤`). For each `j`: if `H j < N` then `H' j = H j` (step 1's `min` identity read
   below `N`) and the `j`-terms agree; if `H j ≥ N` then `H' j ≥ N` and **both** `j`-terms are
   `≥ ℓ • N > S`, so neither participates in either `inf`. The two `inf`s therefore run over
   pointwise-equal relevant terms: `suppVal φ f' u ℓ = S`. *(The minimum of the `f`-side is
   attained at a `j` with `H j < N` — from `S < ℓ • N`.)*
3. **`sideSet`.** `OnSide φ f' u ℓ j ↔ OnSide φ f u ℓ j` for every `j` in the common range: on the
   `H j < N` branch both defining equalities have identical left- and right-hand sides (step 2);
   on the `H j ≥ N` branch both fail (`ℓ • H j + u*j ≥ ℓ • N > S`, same for `f'` — for `ℓ = 0`
   the branch is empty since `0 • ⊤ = 0` makes every term finite and equal anyway). `Finset.ext` +
   `Finset.mem_filter` close.
4. **`sideMin`/`sideMax`/`sideDeg`/`IsPure` transport** is definitional rewriting along step 3
   (they are built from `sideSet` and, for `IsPure`, from `OnSide` at the two endpoints — B.20,
   B.34) plus `hdeg`; recorded in the statement, not as separate contract declarations.
5. **`resPoly`.** By B.29 it suffices that `resCoeff π φ f' u ℓ h' H₀ k = resCoeff π φ f u ℓ h H₀ k`
   for `k ≤ sideDeg` (equal ranges by step 4). `resCoeff` (B.28) is
   `resMk π φ (H₀ − u*k) (dev φ f (sideMin + ℓ*k))`; `sideMin` agrees by step 4; the read height
   satisfies `H₀ − u*k ≤ H₀ < N`; and B.10 gives `π^N ∣` every coefficient of the `dev`
   difference. The digit lemma: for `x, y ∈ O` with `π^N ∣ x − y` and `k < N`,
   `digAt π k x = digAt π k y` — from B.22's `digAt_eq`/`digAt_eq_zero_iff` by the case split
   `π^k ∣ x` or not (if yes, `π^k ∣ y` and the two quotients differ by `π^{N−k}·(unit stuff)` with
   `N − k ≥ 1`, so their residues agree; if no, both are junk `0`). Lift coefficientwise through
   `digPoly` (B.24's `digPoly_coeff`) and push through `resMk` (B.25). **This digit lemma is a
   private helper of this node** (~12 lines); it is the only place §9 touches digits directly.

**SIZE.** 110 lines. **SPLIT MANDATED → 2** (recorded in the AMENDMENT block — §2's split table
predates this section): `B77a.lean` = steps 1–4 (`suppVal_congr`, `sideSet_congr` — the polygon
half); `B77b.lean` = step 5 (`resPoly_congr` — the residual half, consuming B77a).

**⚠ THE `H₀ < N` CLAUSE IS CONVENTION-FREE, DELIBERATELY.** Two `H₀`-pinning conventions coexist
upstream: B.28/B.30 pin `H₀` at the side's **left endpoint** `sideMin` (the convention under which
`resPoly` is the side's residual polynomial), while committed B.63/B.65/B.73/B.74 pin `H₀` at
**abscissa 0** (`npHgt φ f 0 = H₀`), which agrees with the former exactly on sides containing `0`
— on a one-sided (pure) polygon, always; on an interior side of a multi-slope polygon, **not**.
This node's transport holds for **every** `H₀ < N` — it transports whatever polynomial the
consumer's convention names, junk or not — so both conventions' consumers (B.74 among them, whose
statement is committed) compose with it unchanged. The convention seam itself is a §8-owned repair
and is booked in the AMENDMENT block below (defect notice D-§9.1); it is **§14 item 13**.

**SOURCE.** `EFF.W12.27` verbatim: "All data the read consumes sit at heights `≤ N−1`, so every
lift of the window class shares them" — this node is that sentence as four equalities;
`EFF.HE3.67` (R8-1 clause 2: the two transport branches — "read exactly below `c_ν`" is step 2's
low branch, "known only to be `≥ c_ν` but `c_ν > b_{ν,j}`" is the high branch, where both terms
leave the `inf`); `EFF.W12.84` step 2 ("bijective in every characteristic and at every finite
window, including when some conservative lower bounds lie beyond the window" — the high branch
again, in the count layer's language); `spec/EFF-HE3.md` XREF `GENHN-3(a)` (via B.76).

**TEETH.** `HE-T-CAP` (`EFF.HE3.54`, 17 + 43 members: the unsound reader's dropped digits are
exactly a violation of clause 5's `k < N` guard) → **Lean theorem** (this node); `HE-BND`
(`EFF.HE3.55`, 3,744 boundary reads, **RE-SCOPED by R8-1**) → **executable regression** retained,
scored per D-4(c) on the aligned rows only.

**ENVIRONMENT.** ENV-A'.

---

### NODE B.78 [lemma] [fresh]

**STATEMENT.** *The window dictionary: `monicPoly` congruence, and window-exactness of the Hensel
peel.* Three clauses, in increasing strength.

* **(i) `monicPoly` congruence.** For `a b : Fin n → O` with `π^N ∣ (a i − b i)` for every `i`:
  `π^N ∣ (monicPoly a − monicPoly b).coeff j` for every `j` (the top coefficients cancel; the rest
  are the vector differences).
* **(ii) Binary block stability.** Let `f = g·h` and `f' = g'·h'` with `g, h, g', h'` monic,
  `ḡ = ḡ' = g₀` and `h̄ = h̄' = h₀` in `(ResidueField O)[X]` with `IsCoprime g₀ h₀`. If
  `π^N ∣ (f − f').coeff i` for every `i`, then `π^N ∣ (g − g').coeff i` and
  `π^N ∣ (h − h').coeff i` for every `i`.
* **(iii) Finset block stability.** The same with `f = ∏_{i ∈ s} g i`, `f' = ∏_{i ∈ s} g' i`, the
  reductions `(g i).map (residue O) = (g' i).map (residue O) = g₀ i` monic and **pairwise
  coprime**: then `π^N ∣ ((g i) − (g' i)).coeff j` for every `i ∈ s` and every `j`.

No completeness is assumed anywhere: the factorizations are **given**, and the content is that the
level-`N` window of the product pins the level-`N` window of each factor. (Producing the
factorizations is landed Hensel — `exists_monic_factorization_finset` — and needs ENV-B; that
happens in B.80's proof, not here.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem monicPoly_congr {n N : ℕ} {a b : Fin n → O}
    (hab : ∀ i, π ^ N ∣ (a i - b i)) (j : ℕ) :
    π ^ N ∣ (Uniformity.Density.monicPoly a - Uniformity.Density.monicPoly b).coeff j

theorem factor_congr_of_coprime (hπ : Irreducible π) {N : ℕ} {g h g' h' : Polynomial O}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    {g₀ h₀ : Polynomial (ResidueField O)} (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (IsLocalRing.residue O) = g₀) (hhr : h.map (IsLocalRing.residue O) = h₀)
    (hgr' : g'.map (IsLocalRing.residue O) = g₀) (hhr' : h'.map (IsLocalRing.residue O) = h₀)
    (hff' : ∀ i, π ^ N ∣ (g * h - g' * h').coeff i) :
    (∀ i, π ^ N ∣ (g - g').coeff i) ∧ (∀ i, π ^ N ∣ (h - h').coeff i)

theorem peel_congr (hπ : Irreducible π) {N : ℕ} {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {g g' : ι → Polynomial O} {g₀ : ι → Polynomial (ResidueField O)}
    (hgmon : ∀ i ∈ s, (g i).Monic) (hgmon' : ∀ i ∈ s, (g' i).Monic)
    (h₀mon : ∀ i ∈ s, (g₀ i).Monic)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g₀ i) (g₀ j))
    (hgr : ∀ i ∈ s, (g i).map (IsLocalRing.residue O) = g₀ i)
    (hgr' : ∀ i ∈ s, (g' i).map (IsLocalRing.residue O) = g₀ i)
    (hff' : ∀ k, π ^ N ∣ ((∏ i ∈ s, g i) - (∏ i ∈ s, g' i)).coeff k) :
    ∀ i ∈ s, ∀ k, π ^ N ∣ ((g i) - (g' i)).coeff k
```

**DEPENDS.** landed `Uniformity.Hensel.natDegree_eq_of_map_eq` (`HenselFactorization.lean`),
`degree_sub_lt_of_monic_of_natDegree_eq` (ibid.), `Uniformity.Hensel.monic_factorization_unique`
(`HenselFactorization.lean:694` — the `N = ∞` limit of clause (ii), whose proof shape
(coprimality + degree bound) is the induction step's template) · landed
`Uniformity.Density.monicPoly` (`LocalData.lean:151`) · mathlib `Polynomial.coeff_sub`,
`Polynomial.coeff_mul`, `Finset.prod` API, `IsCoprime.prod_right`.

**PROOF.**
1. **(i).** `monicPoly a − monicPoly b = ∑ i, C (a i − b i) * X^i` (the `X^n` cancels); its `j`-th
   coefficient is `a j − b j` for `j < n` and `0` otherwise; both are divisible by hypothesis.
2. **(ii), by induction on `k ≤ N`**: claim `π^k ∣ (g − g').coeff i` and `π^k ∣ (h − h').coeff i`
   for all `i`. Base `k = 1`: `ḡ = ḡ'` and `h̄ = h̄'` are the hypotheses (`hgr/hgr'` etc.), and
   `map (residue O) (g − g') = 0` is coefficientwise `π ∣ ·`.
3. Step `k → k+1` (`k ≥ 1`, `k < N`): write `A := g' − g`, `B := h' − h`; by the induction
   hypothesis every coefficient of `A, B` is in `(π^k)`, and `deg A < deg g`, `deg B < deg h`
   (monic, equal degrees via `natDegree_eq_of_map_eq` twice and
   `degree_sub_lt_of_monic_of_natDegree_eq`). Expand:
   `g'h' − gh = A·h + g·B + A·B`, so `A·h + g·B ≡ (g'h' − gh) ≡ 0 mod π^{k+1}` — the `A·B` term
   has coefficients in `(π^{2k}) ⊆ (π^{k+1})` since `k ≥ 1`, and `g'h' − gh = f' − f` has
   coefficients in `(π^N) ⊆ (π^{k+1})`.
4. Divide by `π^k` coefficientwise (each coefficient of `A, B` is `π^k·(something)`, `O` a domain)
   and reduce mod `π`: with `Ā₁, B̄₁` the reductions of the quotients,
   `Ā₁·h₀ + g₀·B̄₁ = 0` in `(ResidueField O)[X]`. Hence `g₀ ∣ Ā₁·h₀`; coprimality
   (`hcop.dvd_of_dvd_mul_right` shape) gives `g₀ ∣ Ā₁`; and `deg Ā₁ ≤ deg A < deg g = deg g₀`
   forces `Ā₁ = 0`, i.e. `π^{k+1} ∣ A.coeff i` for every `i`. Symmetrically `B̄₁ = 0`. **This is
   `EFF.W12.21`'s displayed injectivity proof, verbatim in structure** ("Write
   `f_i′ = f_i + π^{k−1}A_i`, `deg A_i < m_i d_i` … coprimality gives `P̄_i^{m_i} | Ā_i`, forcing
   `Ā_i = 0` by degree").
5. **(iii), by `Finset.induction` on `s`** : split `∏_{s} = g i₀ * ∏_{s \ i₀}`; the complement
   product is monic with reduction `∏_{j ≠ i₀} g₀ j`, coprime to `g₀ i₀` by
   `IsCoprime.prod_right` over `hcop`; clause (ii) peels `i₀` and hands the complement product
   congruence to the induction hypothesis.

**SIZE.** 116 lines. **SPLIT MANDATED → 2** (recorded in the AMENDMENT block): `B78a.lean` =
clauses (i)–(ii) (steps 1–4); `B78b.lean` = clause (iii) (step 5, consuming B78a).

**⚠ CLAUSE (ii) AT `N = "∞"` IS LANDED; THIS NODE IS ITS FINITE-PRECISION FORM.** Landed
`monic_factorization_unique` proves `g = g'` from `g·h = g'·h'` exactly; this node proves
`g ≡ g' mod π^N` from `g·h ≡ g'·h' mod π^N`. The landed proof cancels in one step (divisibility
plus a degree bound); the finite-precision form needs the height-by-height induction because
division by `h'` is not available mod `π^N`. The landed lemma is still consumed — B.80 uses it to
show that its conclusion does not depend on WHICH peel of the representative was supplied.

**SOURCE.** `EFF.W12.21` (`LEMMA W12-S2.1`, "the level-0 product structure (window-exact
Hensel)"), statement AND quoted proof — clauses (ii)/(iii) are its injectivity leg over `O`
instead of `O/π^N` (the corpus works in `O/π^N` where the statement is a bijection; this chapter
needs only the congruence direction, which is the same induction); `EFF.W12.85` step 3 (the same
mechanism "now on the weighted side modules" — NOT transcribed, that is chapter C's); the
surjectivity leg of `EFF.W12.21` is landed `exists_monic_factorization_finset`
(`MultiHensel.lean:111`) and is consumed by B.67, not re-proved here.

**TEETH.** `W12-BLOCK` (0/1,594,670 — the Hensel product identity and fiber bijection, pointwise
on every DBL member; guards `EFF.W12.21`) → **Lean theorem** (this node is the injectivity half;
the surjectivity half is landed and its tooth is discharged at B.67).

**ENVIRONMENT.** ENV-A' (clause (i) is even `π`-hypothesis-free but is stated in ENV-A' for
uniformity; **no completeness** — see the STATEMENT's last paragraph).

---

### NODE B.79 [theorem] [fresh]

**STATEMENT.** *The block certificate — R8-1's order-1 certificate, in two halves.* Over the
complete bundle, let `φ` be an order-1 key with `m = φ.natDegree`, and `g` monic with
`g.map (residue O) = (φ.map (residue O))^μ`, `0 < μ`. Assume

* **(clause 1 of `EFF.HE3.67`)** `hterm : ¬ NeedsDescent π φ g` — every (terminal) residual
  polynomial of every slope of `g` is separable (B.73; at order 1 every residual is terminal);
* `hperim` — every `(slope, irreducible residual factor)` pair lies in D-3's unconditional
  perimeter (`ℓ = 1` or `deg ψ = 1`), or `B-BOX-1` holds for the pairs outside it *(the same
  clause as B.63's `hperim`; exact form in the leanspec stub, §12 item 4)*.

Then:

* **(a — the value.)** `typeOf g = order1Type π φ g` (B.66's order-1 datum is the actual type).
* **(b — the certificate.)** If moreover **(clause 2 of `EFF.HE3.67`)** `hvis : Visible π φ g N`,
  then for **every** monic `g'` of the same degree with `π^N ∣ (g − g').coeff i` for all `i`:

```
typeOf g' = order1Type π φ g   (=  typeOf g).
```

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem typeOf_eq_order1Type (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hterm : ¬ NeedsDescent π φ g)
    (hperim : ∀ u ℓ : ℕ, ∀ ψ : Polynomial (resField φ), …) :
    typeOf g = order1Type π φ g

theorem typeOf_congr_of_certificate (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hterm : ¬ NeedsDescent π φ g)
    (hperim : ∀ u ℓ : ℕ, ∀ ψ : Polynomial (resField φ), …)
    {N : ℕ} (hvis : Visible π φ g N)
    {g' : Polynomial O} (hg' : g'.Monic) (hdeg : g'.natDegree = g.natDegree)
    (hgg' : ∀ i, π ^ N ∣ (g - g').coeff i) :
    typeOf g' = order1Type π φ g
```
*(the `hperim` clause is byte-identical to B.63's; both are spelled out once, in the leanspec stub
of §12 item 4, and the stub is the single source for both — a divergence there is a stub-stage
blueprint defect.)*

**DEPENDS.** (a): B.13 · B.42 · B.45 · B.58 · B.60 · B.61 · B.63 · B.63a (`typeOf_prod`) · B.66.
(b): (a) · B.73 · B.74 · B.75 · B.76 (`visible_congr`) · B.77 (all three transport clauses) ·
landed `Uniformity.Hensel.natDegree_eq_of_map_eq`.

**PROOF.**
1. **(a).** B.63 (whose `hsep` is `hterm` unfolded — B.73's `NeedsDescent` is the `∃`-negation of
   exactly B.63's `∀`-clause, a `push_neg` away) factors `g` over the pairs
   `(slope, irreducible residual factor)` and gives
   `(typeOf g).data = Σ_{(S,ψ)} {(ℓ_S, m·deg ψ)}`.
2. B.66's `order1Type π φ g` is by definition the same multiset, indexed by B.66's canonical
   finsets `slopeFinset`/`resFactorFinset`. **Tying step 1's existentially produced index family
   to the canonical finsets is this half's real work** (B.63's `T` is existential): the proof
   re-reads B.63's own steps 1–2 — the slope split is B.42's, whose slopes are by construction
   the elements of `slopeFinset`; the residual split is B.45's, whose factors are
   `resFactorFinset`'s — so the two multisets are equal term by term. `FactorizationType.ext`
   closes. *(See the ⚠ RE-PLAN item.)*
3. **(b).** Transport every hypothesis of (a) from `g` to `g'`:
   `g'.map (residue O) = (φ.map (residue O))^μ` — from `hgg'` at any `i` with the reduction map
   (the `N ≥ 1` needed is automatic: `hvis` forces `0 < N`, since `Visible` at `N = 0` is
   `∃ i, ¬ 1 ∣ …`, false); `¬ NeedsDescent π φ g'` — by B.74's `needsDescent_congr` (which
   consumes B.75 and B.77, and whose hypotheses are exactly `hgg'`, `hvis`); `hperim` for `g'` —
   its data (slopes, residual factors) are **equal**, not just corresponding, by B.77's
   `sideSet_congr`/`resPoly_congr`, so the clause transports by rewriting.
4. Apply (a) to `g'`: `typeOf g' = order1Type π φ g'`.
5. `order1Type π φ g' = order1Type π φ g`: B.66's definition reads only `slopeFinset` and
   `resFactorFinset`, both of which are built from `sideSet`/`resPoly` data that B.77 transports
   (a ~10-line congruence unfold, private to this node — `order1Type_congr`).

**SIZE.** (a) 60 lines + (b) 40 lines. **SPLIT MANDATED → 2** (§2's table, honored):
`B79a.lean` = `typeOf_eq_order1Type`; `B79b.lean` = `typeOf_congr_of_certificate`.

**⚠ RE-PLAN ITEM: B.66's PRIVATE HELPERS BECOME SHARED SUPPLIERS.** B.66 defined
`slopeFinset`/`resFactorFinset` as private helpers "and if either turns out to be reusable the
orchestrator books it separately" — step 2 and step 5 make both reusable (B.79a needs them to
*state* nothing but to *prove* everything; the private-copy ban of §0.2 applies). **The
orchestrator must book B.66a (`slopeFinset`/`resFactorFinset` + their membership lemmas
`mem_slopeFinset ↔ (sideSet …).Nonempty ∧ 1 ≤ card ∧ …`, `mem_resFactorFinset ↔ ψ ∈ (B.45
factorization)`) before B.79a fires** — the same missing-supplier class as chapter G's A-7 and
this chapter's B.44′/B.63a. Booked here rather than discovered at fleet time. **§14 item 12**: the
cross-read must check that B.79a step 2's "term by term" tie is actually available from B.42/B.45's
statements as committed (if B.63's existential cannot be re-opened, B.63's SIGNATURE needs its `T`
strengthened to the canonical finsets — a §8-owned statement refinement, same class as defect
D-§9.1).

**⚠ WHAT THIS NODE DOES *NOT* SAY.** No bound on `N` in terms of `μ`, `λ`, or anything else: the
refuted `LEMMA HE3-5` bullet ("one more window unit", `EFF.HE3.37`) is **not** transcribed, per
H-4 and D-4(c). The hypothesis is `Visible` — the member's own polygon in the window — and R8-1's
counterexample (`f = Φ″³ + 5^M`, height `M` unbounded) is precisely a family where `Visible`
demands `N > M` with `M` arbitrary. At order 1 there is additionally no recursion: R8-1's
"apply the same criterion to that child's recentered development" has no children here (the
recentering chain is chapter C's, H-1/B.69), so clauses 1 + 2 are the whole criterion.

**SOURCE.** `EFF.HE3.67` (R8-1, the rewritten recursive certificate — clauses 1 and 2 verbatim,
transcribed at the single order-1 node per H-4's line-221 commitment; its induction proof
degenerates to the one-node case, which is B.63 + B.77); `EFF.HE3.15` (DEFINITION 2's decided
leaves: "(a) the read TERMINATES with every TERMINAL residual polynomial separable … (b) every
event along the history is lift-stable at the stage window" — clauses (a)/(b) are `hterm`/`hvis`;
`EFF.HE3.67`'s CONDITIONALITY (i) records that R8-1 *agrees* with DEFINITION 2, correcting only
HE3-5's bound, and this node transcribes that agreement); `EFF.W12.86` step 5 ("By the definition
of a decided order-1 key, every terminal residual is separable. S2.3's order-1 Ore theorem then
certifies, for every disc-nonzero lift, one étale piece for each terminal side factor with its
displayed `(e, f)`" — strengthened here to every lift per D-4(a)/H-11); `EFF.W12.27`.

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, 0 bad, all 5 `μ = 3` stage types) → **Lean
theorem** inside D-3's perimeter, **executable regression** retained outside it (`hperim`
carried); `HE-BND` (`EFF.HE3.55`, RE-SCOPED) → **executable regression** retained per D-4(c);
`HE-T-CAP` (`EFF.HE3.54`) → **Lean theorem** (via B.77's clause 5 guard, consumed at step 3).

**ENVIRONMENT.** ENV-C (through B.63; the transport steps alone are ENV-A', but the node's
conclusions name `typeOf` on a factored residual read, which is §0.1's ENV-C trigger).

---

### NODE B.80 [theorem] [fresh]

**STATEMENT.** *THE FULL LEVEL-`N` DECIDEDNESS CERTIFICATE (every degree, every block count).*
Over the complete bundle, let `a : Fin n → O` with `0 < n` and write `f := monicPoly a`. Suppose
given order-0 data — order-1 keys `φ i` (`i ∈ s`) with pairwise distinct reductions, exponents
`e i ≥ 1`, `f.map (residue O) = ∏_{i ∈ s} (φ̄ i)^{e i}` — and a peel of the representative: monic
`g i` with `f = ∏_{i ∈ s} g i` and `(g i).map (residue O) = (φ̄ i)^{e i}` (B.67 supplies one;
by landed `monic_factorization_unique` iterated, the choice is unique, so the hypotheses are data
of `a` alone). Assume, **per block**, R8-1's two clauses and the perimeter:
`Visible π (φ i) (g i) N`, `¬ NeedsDescent π (φ i) (g i)`, and `hperim i`. Then the class of `a`
is decided — for **every** lift, per D-4(a):

```
DecidedAt O n ⟨Σ_{i ∈ s} (order1Type π (φ i) (g i)).data⟩ N (proj O n N a).
```

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem decidedAt_of_order1_certificate (hπ : Irreducible π) {n N : ℕ} (hn : 0 < n)
    (a : Fin n → O) {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {φ : ι → Polynomial O} {e : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i)) (he : ∀ i ∈ s, 0 < e i)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic)
    (hgprod : Uniformity.Density.monicPoly a = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (e i))
    (hvis : ∀ i ∈ s, Visible π (φ i) (g i) N)
    (hterm : ∀ i ∈ s, ¬ NeedsDescent π (φ i) (g i))
    (hperim : ∀ i ∈ s, ∀ u ℓ : ℕ, ∀ ψ : Polynomial (resField (φ i)), …) :
    Uniformity.Density.DecidedAt O n ⟨∑ i ∈ s, (order1Type π (φ i) (g i)).data⟩ N
      (Uniformity.Density.proj O n N a)
```

**DEPENDS.** B.46 · B.63a (`typeOf_prod`) · B.66 · B.75 · B.78 (all three clauses) · B.79(b) ·
landed `Uniformity.Density.decidedAt_of_congr` (`DensityAPI.lean:140`),
`Uniformity.Density.proj_eq_iff_dvd` (`DensityAPI.lean:124`, consumed inside the former),
`Uniformity.Hensel.exists_monic_factorization_finset` (`MultiHensel.lean:111`),
`Uniformity.Hensel.natDegree_eq_of_map_eq`, `Uniformity.Density.FactorizationType.ext`.

**PROOF.**
1. Enter through landed `decidedAt_of_congr`: it remains to show, for every `b : Fin n → O` with
   `π^N ∣ (b i − a i)` for all `i`, that `typeOf (monicPoly b) = ⟨Σ (order1Type …).data⟩`.
2. `f' := monicPoly b` satisfies `π^N ∣ (f − f').coeff j` for all `j` (B.78(i)), and `0 < N`
   (from any `hvis i` with `s.Nonempty`; `s = ∅` is impossible: `hgprod` + `hgres` would force
   `f̄ = 1` against `0 < n` and monicity). Hence `f'.map (residue O) = f.map (residue O)`.
3. Peel `f'`: the reductions `(φ̄ i)^{e i}` are pairwise coprime — distinct monic irreducibles are
   non-associated, B.46's `isCoprime_pow_of_not_dvd` pairwise, exactly as in B.67 step 1 — so
   landed `exists_monic_factorization_finset` gives monic `g' i` with `f' = ∏ g' i` and
   `(g' i).map (residue O) = (φ̄ i)^{e i}`.
4. B.78(iii) applied to the two peels of the `π^N`-congruent products:
   `π^N ∣ ((g i) − (g' i)).coeff k` for every `i ∈ s`, `k`. Degrees match by
   `natDegree_eq_of_map_eq` on both sides of `hgres`.
5. Per block, B.79(b) with `hvis i`, `hterm i`, `hperim i`:
   `typeOf (g' i) = order1Type π (φ i) (g i)`.
6. `(typeOf f').data = Σ_{i ∈ s} (typeOf (g' i)).data` by B.63a's `typeOf_prod` (the same step as
   B.67's step 3, applied to the step-3 peel); substitute step 5 and close with
   `FactorizationType.ext`.

**SIZE.** 55 lines.

**⚠ THE σ IS WELL-DEFINED DATA OF `a` ALONE.** The signature takes the peel `g` as a hypothesis
tuple rather than unpacking B.67's existential (D-4(b); B.71 chose the existential route — both
are recorded deliberately, and the leanspec stub fixes each). Landed
`monic_factorization_unique`, iterated over `s` exactly as in B.78 step 5's induction pattern,
shows any two peels of the same `f` along the same reduction data are **equal**, so
`⟨Σ (order1Type π (φ i) (g i)).data⟩` does not depend on the supplied peel. This uniqueness
corollary is a private helper of this node; if chapter C wants it by name (its `HT` transcription
will), the orchestrator books it — RE-PLAN candidate, flagged.

**⚠ H-11 CASHED.** The conclusion quantifies over **every** lift of the class — including the
equal-characteristic `disc = 0` lifts that `EFF.W12.27`'s `[r4]` strike shows have *no σ in the
corpus's sense* (its counter-instance `F = y³ + b₀`, char 3, `F′ ≡ 0`). `typeOf F` is still
defined and still computed by this certificate (for that instance: the `(u,ℓ) = (h,3)` leaf,
`d = 1`, B.58's norm bracket — no separability used anywhere in §7's route). The corpus's
`disc ≠ 0` quantifier is thus not weakness repaired but strength gained; §14 item 5.

**SOURCE.** `EFF.W12.27` verbatim ("the shape is σ-DECIDED with σ read off the shape alone, and
(A0)-strongly (every `disc ≠ 0` lift has this σ …)" — the certification sentence this node makes
a theorem, at the stronger every-lift quantifier per D-4(a)); `EFF.W12.51` (`W12-BOX-7`, the
pinned definiendum this node's `DecidedAt` strictly implies); `EFF.W12.21` ("σ(f) = ⊔_i σ(f_i)
branchwise, and f is σ-decided iff every f_i is" — steps 3–6 are the "if" direction);
`EFF.W12.08` (the σ-pin and its `[r4]` totality remark); `EFF.HE3.16` (THEOREM HE3.A's
"factors over `O` into exactly `k` monic irreducible factors, in bijection with the members of
`τ_stage(ℓ)`" — at `e₁ = 1, f₁ = m`, the stage type is `order1Type`, per B.66's FAITHFULNESS).

**TEETH.** `W12-ORACLE` (`EFF.W12.56`, `[IND]`, 0 bad / 41,923 PARI σ-multiset checks per decided
member) → **executable regression** retained, with the scope note of D-4(a): the battery's
"`disc = 0 ⟹ never decided`" clause tests the corpus's weaker predicate, not this node's (the
PARI oracle cannot score a `disc = 0` lift; the Lean theorem covers it); tooth `W12-T-SIGMA`
(`EFF.W12.27`) → **Lean theorem** (this node); `W12-BLOCK` → **Lean theorem** at B.78 (consumed
at step 4).

**ENVIRONMENT.** ENV-C **plus completeness** (= ENV-B ∩ ENV-C as in §7's leaf theorems: step 3 is
Hensel). Binding note for the stub agent: `DecidedAt`, `proj`, `Coeff` need
`[Finite (ResidueField O)]` (§0.1's ⚠); `exists_monic_factorization_finset` needs
`[IsAdicComplete (maximalIdeal O) O]`; both are bound.

---

### NODE B.81 [lemma] [fresh]

**STATEMENT.** *Eventual certification — the per-member level exists.* Over the complete bundle,
with the data of B.80 minus the level: `a : Fin n → O`, order-0 data `(φ i, e i)`, the peel `g i`,
and per block `dev (φ i) (g i) 0 ≠ 0`, `¬ NeedsDescent π (φ i) (g i)`, `hperim i`. Then there is a
level `N` — explicitly, any `N > max_{i ∈ s} npHgt (φ i) (g i) 0` — at which B.80 fires, and its
σ is the member's own type:

```
∃ N : ℕ, 0 < N ∧ DecidedAt O n (typeOf (monicPoly a)) N (proj O n N a).
```

The level is **per-member** (read off the member's own polygon heights) and this chapter states no
uniform law over any family — D-4(c); R8-1's counterexample shows none exists even for the family
of a single shape.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Leaf

theorem exists_decidedAt_of_terminating (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (a : Fin n → O) {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {φ : ι → Polynomial O} {e : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i)) (he : ∀ i ∈ s, 0 < e i)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic)
    (hgprod : Uniformity.Density.monicPoly a = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (e i))
    (hnz : ∀ i ∈ s, dev (φ i) (g i) 0 ≠ 0)
    (hterm : ∀ i ∈ s, ¬ NeedsDescent π (φ i) (g i))
    (hperim : ∀ i ∈ s, ∀ u ℓ : ℕ, ∀ ψ : Polynomial (resField (φ i)), …) :
    ∃ N : ℕ, 0 < N ∧ Uniformity.Density.DecidedAt O n
      (typeOf (Uniformity.Density.monicPoly a)) N (Uniformity.Density.proj O n N a)
```

**DEPENDS.** B.63a · B.66 · B.76 (`exists_visible`, `visible_mono`, `visible_iff_npHgt_lt`) ·
B.79(a) · B.80 · landed `FactorizationType.ext`.

**PROOF.**
1. Per block, B.76(v) with `hnz i` gives `N i` with `Visible π (φ i) (g i) (N i)`; take
   `N := max (1, max_{i ∈ s} N i)` (`Finset.max'` over the image, or `Finset.sup` + 1); B.76(iii)
   makes every block visible at `N`, and `0 < N`.
2. B.80 at this `N` gives `DecidedAt O n ⟨Σ (order1Type π (φ i) (g i)).data⟩ N (proj O n N a)`.
3. The σ is the member's own type: per block B.79(a) gives
   `typeOf (g i) = order1Type π (φ i) (g i)`; B.63a's `typeOf_prod` over `hgprod` gives
   `(typeOf (monicPoly a)).data = Σ (typeOf (g i)).data`; `FactorizationType.ext` closes
   `typeOf (monicPoly a) = ⟨Σ (order1Type …).data⟩`, and rewriting in step 2 concludes.

**SIZE.** 40 lines. **SPLIT CANDIDATE** (§2's table, honored): the natural boundary is step 3 as
`B81a` (`typeOf_eq_sum_order1Type`, the member's-own-type identity — reusable by chapter C's
menu-to-density weld) and steps 1–2 as `B81b`; the orchestrator decides at fleet time.

**⚠ WHAT "EVENTUAL" DOES AND DOES NOT BUY.** This node certifies **one member at a time**. It does
NOT say that the decided proportion tends to anything (that is drainage, chapter I — forward
reference, marked per the chapter charge), and it does NOT bound `N` by the shape (refuted,
D-4(c)). It is the order-1 kernel of the drainage argument: every terminating order-1 member
eventually enters `decidedSet`, with `hnz`/`hterm`/`hperim` delimiting exactly which members
"terminating" means — `¬ hnz` is `EFF.HE3.55`'s out-of-genre residue, `¬ hterm` is the descent
locus (chapter C), and the perimeter's conditional region carries `B-BOX-1` (H-7).

**SOURCE.** `EFF.HE3.67` (R8-1's replacement bullet 3, transcribed at order 1: "the σ-undecided
mass is therefore obtained by stratifying by complete read histories and their deepest consulted
heights. No single 'one more window unit' law, nor one unstratified exact q-power, follows" — the
per-member `N` of step 1 IS the deepest-consulted-height stratification, and the refusal to state
more is the correction carried); `EFF.HE3.55` (HE-BND: the measured two-step decided profile is
the instance evidence for exactly this per-member eventuality, valid post-R8-1 only row-by-row);
`EFF.W12.86` step 5 (the corpus's termination argument — its depth-increase recursion `s_u ≥
s_v + 1` is chapter C's; at order 1 only its terminal clause is needed, which is `hterm`).

**TEETH.** `HE-BND` (`EFF.HE3.55`, 3,744 boundary reads, RE-SCOPED by R8-1) → **executable
regression** retained: the battery's saturation columns (`N = 6, 7`) are per-member eventuality
observed; the never-decided residue (28/51) decomposes as the battery says into out-of-genre
(`¬ hnz`, 25/49) + deeper (`¬ hterm`-or-deeper, 3/2), which is this node's hypothesis frontier
measured.

**ENVIRONMENT.** ENV-C plus completeness (inherits B.80's binding).

---

### NODE B.82 [theorem] [fresh]

**STATEMENT.** *The single-key certificate (the §10 gates' engine).* The one-block form of B.80:
`DecidedAt O n (order1Type π φ (monicPoly a)) N (proj O n N a)`. *(stub)*

---

### AMENDMENT BLOCK (2026-08-15, §9 composer)

*(to be filled — census/split-table refinements and the H₀-convention defect notice.)*

---

<!-- CHAP-B APPEND POINT — do not remove; sections are appended here in order -->
