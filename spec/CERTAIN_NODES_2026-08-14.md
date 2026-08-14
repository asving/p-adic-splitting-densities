# CERTAIN-NODES LIST — 2026-08-14

**Charge (Asvin):** *"formalize now the pieces that we know we will need for sure, scoped so
that opus or sonnet can deliver it exactly."*

**Role of this file.** Extraction and specification only. Nothing here is formalized; every
entry is a frozen Lean signature plus its provenance and its certainty argument. The
orchestrator books nodes; the fleet formalizes to the SIGNATURE as a contract.

**The three filters** (a node is listed only if it passes ALL three):

1. **CERTAIN** — on the capstone path REGARDLESS of the open design decisions (the 0c chapter
   cut, unlanded spec shards, the WELDZERO arc outcome). Each entry names the consuming
   conjunct and argues survival under every open branch.
2. **EXACTLY SCOPED** — the Lean statement is written here, now, typed against the real
   `leanfinal`/`leancheck` names. A node whose signature cannot be written is in REJECTED.
3. **INDEPENDENTLY FORMALIZABLE** — dependencies are landed API plus **at most one** other node
   on this list (such edges are marked `CN-nn` in DEPENDS).

**Standing conventions for every node below.** `O` is the standing bundle
`{O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]`, with
`[Finite (IsLocalRing.ResidueField O)]` and/or `[IsAdicComplete (IsLocalRing.maximalIdeal O) O]`
added where the signature says so. Files `open IsLocalRing Polynomial`, so `residue`,
`maximalIdeal`, `ResidueField`, `X`, `C` are unqualified in the signatures. Namespaces:
`Uniformity.Density` (types/densities), `Uniformity.Hensel` (Hensel), `UniformityCheck`
(census). Every node: zero `sorry`, Lean-core axioms, signature is a contract — a node that
cannot be proved AS STATED returns BLOCKED with the obstruction, never a weakened statement.

---

## SUMMARY TABLE (orchestrator review pass)

Ordered by (certainty × unblocking-value). Sizes are target Lean lines for the whole node file
(contract declaration + private/public helpers), excluding the header docstring.

| id | name | tier | size |
|---|---|---|---|
| CN-01 | `exists_monicPoly_eq` — every monic degree-`n` polynomial is a `monicPoly` | sonnet | 35 |
| CN-02 | `monicFactors_mul` — monic factorizations add over products | sonnet | 30 |
| CN-03 | `typeOf_mul` — the peel/product law for `typeOf` | sonnet | 12 |
| CN-04 | `efPair_pos_of_mem` — every `(e,f)` in a type is positive | sonnet | 25 |
| CN-05 | `genuineDensity_eq_zero_of_forall_ne` — non-occurring types have density 0 | sonnet | 35 |
| CN-06 | `genuineDensity_eq_zero_of_degree_ne` — off-degree types have density 0 | sonnet | 12 |
| CN-07 | `proj_eq_iff_dvd` — class equality ⟺ coefficientwise congruence, general `n` | sonnet | 20 |
| CN-08 | `decidedAt_of_congr` — certificate ⟹ decided class, general `n` | sonnet | 15 |
| CN-09 | `decidedDensity_ge_of_subset` — the census inner bound | sonnet | 25 |
| CN-10 | `genuineDensity_le_of_superset` — the census outer bound | sonnet | 25 |
| CN-11 | `drainage_of_undecided_comp` — drainage from a subsequence bound, general `n` | sonnet | 40 |
| CN-12 | `exists_monic_scaleRoots` — polygon-above-slope-`m` ⟹ integral extraction | opus | 70 |
| CN-13 | `dvd_sub_coeff_of_scaleRoots` — level bookkeeping across the extraction | sonnet | 30 |
| CN-14 | `typeOf_prod_X_sub_C` — the totally split type at every `n` | sonnet | 35 |
| CN-15 | `exists_anisotropic` — general-`O` anisotropic quadratic (HYP.147) | sonnet | 45 |
| CN-16 | `card_certSet_gen` — the census lemma at general `n` and general read | opus | 60 |
| CN-17 | `exists_monic_factorization_finset` — `n`-fold Hensel (HYP.03) | opus | 90 |
| CN-18 | `typeOf_of_residual_coprime` — the order-0 two-block peel | sonnet | 30 |
| CN-19 | `norm_adjoinRoot_root` — `N(α) = (−1)ⁿ·a₀` | opus | 130 |
| CN-20 | `typeOf_eisenstein` — the totally ramified leaf at every `n` | opus | 60 |
| CN-21 | `typeOf_inert_of_irreducible_map` — the unramified leaf at every `n` | opus | 150 |
| CN-22 | `exists_coveringMenu` — finitely many types occur in degree `n` | opus | 90 |
| CN-23 | `FactorizationType.degree_mk_add` — degree adds under multiset union | sonnet | 10 |

**Counts:** 23 listed (16 sonnet / 7 opus; ~1000 Lean lines total) · 16 rejected.

**Internal edges (the only CN→CN dependencies):** CN-02→CN-03; CN-03→{CN-14, CN-18};
CN-05→CN-06; CN-07→CN-08; CN-04→CN-22; CN-19→CN-20. Everything else depends on landed API only.
Layer 0 (fireable immediately, 15 nodes): CN-01, CN-02, CN-04, CN-05, CN-07, CN-09, CN-10,
CN-11, CN-12, CN-13, CN-15, CN-16, CN-17, CN-19, CN-21, CN-23.

---

## NODES

### CN-01 | `exists_monicPoly_eq` | tier: sonnet | est. 35 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O]

/-- helper, public in the same file -/
theorem monicPoly_coeff_lt {n : ℕ} (a : Fin n → O) {i : ℕ} (h : i < n) :
    (monicPoly a).coeff i = a ⟨i, h⟩

/-- CONTRACT -/
theorem exists_monicPoly_eq {n : ℕ} {f : Polynomial O} (hf : f.Monic) (hd : f.natDegree = n) :
    ∃ a : Fin n → O, monicPoly a = f
```

**SOURCE** Landed API's obvious next lemma: `Density/LocalData.lean:151` defines `monicPoly`
and proves `monicPoly_monic`, `monicPoly_degree`, `monicPoly_natDegree` — but never that the
map is onto the monic degree-`n` polynomials. Witness: `a i := f.coeff i`.

**CONSUMED-BY** Every transport from a polynomial-level theorem to the coefficient box. The
landed polynomial-level results (`typeOf_shift`, `typeOf_scaleRoots`, `typeOf_scale`,
`Hensel.exists_monic_factorization`, `typeOf_degree`) are all stated for `Polynomial O`, while
`DecidedAt`/`PossibleAt`/`decidedSet`/`possibleSet` (`GenuineDensity.lean:66-79`) quantify over
`a : Fin n → O` through `monicPoly a`. Without surjectivity no polynomial-level theorem can be
consumed by a census. Decision-proof: `monicPoly` and `Coeff` are Phase-0d-signed capstone
interfaces (`Statement.lean:55-58`), unchanged by any chapter cut.

**DEPENDS** `monicPoly`, `monicPoly_monic`, `monicPoly_natDegree`; mathlib `Polynomial.ext`,
`coeff_X_pow`, `finsetSum_coeff`.

**RISK** Almost none. Only fiddle: the `i = n` and `i > n` coefficient cases of the tail sum.

---

### CN-02 | `monicFactors_mul` | tier: sonnet | est. 30 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- CONTRACT -/
theorem monicFactors_mul {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) :
    monicFactors (f * g) = monicFactors f + monicFactors g
```

**SOURCE** Landed API's obvious next lemma: `Density/TypeOf.lean:154` (`monicFactors`),
`:158` (`monicFactors_spec`), `:165` (`monicFactors_eq`). Proof is `monicFactors_eq` applied to
`IsMonicFactorization (f * g) (monicFactors f + monicFactors g)`, whose product clause is
`Multiset.prod_add`.

**CONSUMED-BY** CN-03, and through it every peel law. See CN-03 for the decision-proofness
argument.

**DEPENDS** `IsMonicFactorization`, `monicFactors_spec`, `monicFactors_eq`; mathlib
`Multiset.prod_add`, `Multiset.mem_add`.

**RISK** None identified. Note the hypotheses are `Monic` only — no coprimality, no
separability; do not add any.

---

### CN-03 | `typeOf_mul` | tier: sonnet | est. 12 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- CONTRACT -/
theorem typeOf_mul {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) :
    (typeOf (f * g)).data = (typeOf f).data + (typeOf g).data
```

**SOURCE** `Density/TypeOf.lean:300` (`typeOf`), `:303` (`typeOf_data`) + CN-02 +
`Multiset.map_add`. Mathematical content: HE7.A clause 6 — *"their product is `F` … their
ramification and residue degrees are obtained by multiplying the successive displayed `e`- and
`f`-increments"* (`spec/EFF-T2-s1of6.md` EFF.T2.s1of6.31, clause 6); and `(SIDE-PROD)` /
`(LABEL-PROD)` (EFF.T2.s1of6.17), which are exactly "typeOf is additive along a monic
factorization".

**CONSUMED-BY** (i) drainage at every `n` — every peel of a decided stratum reads the type of a
product; (ii) the covering menus at every `n`; (iii) chapter B's leaf layer (CN-18, CN-14);
(iv) HE7.A clause 6's Lean discharge. Decision-proof: it is a theorem about `typeOf`, which is
a Q4 CORE-SET definition (`spec/HYPOTHESIS_LEDGER.md` HYP.01/HYP.98) and cannot move with the
chapter cut. Stated on `.data` (not on a `FactorizationType` addition) precisely so that it
does not presuppose any algebraic structure on `FactorizationType` — see REJECTED R14.

**DEPENDS** CN-02 (the only internal edge); `typeOf`, `typeOf_data`; mathlib `Multiset.map_add`.

**RISK** None. If the orchestrator later adds `FactorizationType` addition, this statement
survives verbatim as its unfolding.

---

### CN-04 | `efPair_pos_of_mem` | tier: sonnet | est. 25 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- CONTRACT -/
theorem efPair_pos_of_mem {f : Polynomial O} (hf : f.Monic) {p : ℕ × ℕ}
    (hp : p ∈ (typeOf f).data) : 0 < p.1 ∧ 0 < p.2
```

**SOURCE** Landed API's obvious next lemma, forced by the definitions: members of
`monicFactors f` are monic irreducible (`monicFactors_spec`, `TypeOf.lean:158`) hence of
positive degree (the argument at `TypeOf.lean:374-379`), so `inertiaDegOf g > 0`
(`inertiaDegOf_pos` + `normValues_nonempty`, `:213`/`:262`) and
`ramIndexOf g = natDegree / inertiaDegOf > 0` by `inertiaDegOf_dvd_natDegree` (`:269`).

**CONSUMED-BY** Every menu-exhaustiveness / shape-enumeration argument at every degree. It is
the lemma that makes `(typeOf f).degree = f.natDegree` (landed `typeOf_degree`) into a FINITE
constraint: without positivity, degree-`n` `FactorizationType`s include junk like
`⟨{(1,1),(1,1),(0,7)}⟩`, so no enumeration is possible. Directly required by CN-22 and by
HYP.10 (five cubic types). Decision-proof: a fact about `typeOf`, in the CORE-SET.

**DEPENDS** `monicFactors_spec`, `inertiaDegOf_pos`, `normValues_nonempty`,
`inertiaDegOf_dvd_natDegree`, `ramIndexOf`, `efPair`, `typeOf_data`; mathlib `Nat.div_pos`.

**RISK** None. (Optional companion in the same file, free from `typeOf_degree`:
`p.1 * p.2 ≤ f.natDegree` — book it as a helper, not a second contract.)

---

### CN-05 | `genuineDensity_eq_zero_of_forall_ne` | tier: sonnet | est. 35 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- CONTRACT -/
theorem genuineDensity_eq_zero_of_forall_ne {n : ℕ} {σ : FactorizationType}
    (h : ∀ a : Fin n → O, typeOf (monicPoly a) ≠ σ) : genuineDensity O n σ = 0

/-- helper, public in the same file (immediate from `decidedDensity_le_genuineDensity`) -/
theorem decidedDensity_eq_zero_of_forall_ne {n : ℕ} {σ : FactorizationType}
    (h : ∀ a : Fin n → O, typeOf (monicPoly a) ≠ σ) : decidedDensity O n σ = 0
```

**SOURCE** Generalization to all `n` of the landed degree-2 instances
`Drainage.lean:1037` (`genuineDensity_two_eq_zero`), `:1032`
(`genuineDensity_two_linType_eq_zero`), `Gates.lean:87` (`decidedDensity_one_of_ne`). Proof:
`possibleSet O n σ N = ∅` at every `N` by the definition at `GenuineDensity.lean:70`, so
`possibleSeq = 0` and `⨅ N, 0 = 0`.

**CONSUMED-BY** `UniformityStatement` (`Statement.lean:71`) itself. The capstone demands a
rational function for EVERY `σ` with `σ.degree = n`, including the types that never occur; this
node is the `num = 0` branch and it is needed at every `n`. It survives every chapter cut
because it is a property of the frozen, Asvin-signed capstone statement, not of any chapter.

**DEPENDS** `possibleSet`, `possibleCount`, `possibleSeq`, `genuineDensity`,
`decidedDensity_le_genuineDensity`, `genuineDensity_nonneg`; mathlib `Nat.card_eq_zero_of_...`,
`ciInf_const`.

**RISK** Low. Watch the `N = 0` degenerate box (`Res O 0` is trivial): the emptiness argument
still runs because `proj_surjective` supplies a lift of every class at every level.

---

### CN-06 | `genuineDensity_eq_zero_of_degree_ne` | tier: sonnet | est. 12 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- CONTRACT -/
theorem genuineDensity_eq_zero_of_degree_ne {n : ℕ} {σ : FactorizationType}
    (h : σ.degree ≠ n) : genuineDensity O n σ = 0
```

**SOURCE** Signed signature point (iv), `Statement.lean:59`: *"The hypothesis `σ.degree = n`
does real work (`typeOf_degree`): off-degree `σ` are forced to density `0`."* This node is that
sentence, as a theorem. Proof: `typeOf_degree` + `monicPoly_natDegree` give
`(typeOf (monicPoly a)).degree = n ≠ σ.degree`, so CN-05 applies.

**CONSUMED-BY** The same capstone conjunct as CN-05, and it is the clause that makes
`UniformityStatement`'s degree hypothesis non-decorative. Decision-proof for the same reason
(Asvin-signed statement, HYP.94 CLOSED-SIGNED).

**DEPENDS** CN-05 (the only internal edge); landed `typeOf_degree`, `monicPoly_natDegree`,
`monicPoly_monic`.

**RISK** None.

---

### CN-07 | `proj_eq_iff_dvd` | tier: sonnet | est. 20 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- CONTRACT -/
theorem proj_eq_iff_dvd (hπ : Irreducible π) {n N : ℕ} (a b : Fin n → O) :
    proj O n N a = proj O n N b ↔ ∀ i, π ^ N ∣ (b i - a i)
```

**SOURCE** Generalization of the landed one-directional degree-2 lemma
`Drainage.lean:639` (`congAt_of_proj_eq`, which produces `CongAt π N a b` from `proj` equality
at `n = 2`). The iff at general `n` is what every census actually needs. Proof:
`funext` + `Ideal.Quotient.eq` + landed `mem_maximalIdeal_pow_iff_dvd` (`Drainage.lean:635`,
already general).

**CONSUMED-BY** Every certificate→census step at every `n` and in every chapter: certificates
are stated as divisibility conditions on integral coefficient vectors (`CertSplit`/`CertRam`/
`CertInert`, `Drainage.lean:245-258`) while `decidedSet` is a set of classes. This is the
translation. Decision-proof: `proj`/`Coeff` are the frozen counting arena
(`LocalData.lean:131-136`), fixed independently of the chapter cut.

**DEPENDS** `proj`, `Res`, `mem_maximalIdeal_pow_iff_dvd`; mathlib `Ideal.Quotient.eq`,
`funext_iff`.

**RISK** Low. Direction convention (`b i - a i` vs `a i - b i`) must match
`mem_maximalIdeal_pow_iff_dvd`'s orientation; the landed `Drainage.lean:639` and
`Counting.lean:204` both need a `dvd_sub_comm` flip — expect the same here.

---

### CN-08 | `decidedAt_of_congr` | tier: sonnet | est. 15 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- CONTRACT -/
theorem decidedAt_of_congr (hπ : Irreducible π) {n N : ℕ} {σ : FactorizationType}
    {a : Fin n → O}
    (h : ∀ b : Fin n → O, (∀ i, π ^ N ∣ (b i - a i)) → typeOf (monicPoly b) = σ) :
    DecidedAt O n σ N (proj O n N a)
```

**SOURCE** Generalization of the landed degree-2 pattern `Drainage.lean:652`
(`decidedAt_of_not_tang`) and `Gates.lean:218` (`split_decided_class`), each of which
re-derives this plumbing inline at `n = 2`.

**CONSUMED-BY** Every decided-stratum certificate at every `n`. It is the single interface
between "certificate is congruence-invariant" (the `*_congr` lemmas, `Drainage.lean:455-484`)
and `decidedSet` membership, which every census and every drainage bound consumes. Survives
every branch for the same reason as CN-07.

**DEPENDS** CN-07 (the only internal edge); `DecidedAt`, `proj`.

**RISK** None.

---

### CN-09 | `decidedDensity_ge_of_subset` | tier: sonnet | est. 25 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- CONTRACT -/
theorem decidedDensity_ge_of_subset {n N : ℕ} {σ : FactorizationType}
    {T : Set (Coeff O n N)} (hT : T ⊆ decidedSet O n σ N) :
    (Nat.card T : ℝ) / (residueCard O : ℝ) ^ (n * N) ≤ decidedDensity O n σ
```

**SOURCE** Generalization of the landed single-class version `Gates.lean:325`
(`decidedDensity_ge_of_decided`, which handles `T = {c}`). Proof: `Nat.card` monotone on
subsets of the finite `Coeff O n N` (`instFiniteCoeff`, `LocalData.lean:133`), then
`decidedSeq_le_decidedDensity` (`GenuineDensity.lean:295`).

**CONSUMED-BY** The inner half of every stratum census at every `n` — the exact shape in which
`card_certSet` (`Counting.lean:228`) output is consumed. Every chapter that produces a decided
count needs it. Decision-proof: the decided/genuine bracket is frozen by the P4 rewire and
signed (HYP.94, HYP.111).

**DEPENDS** `decidedSet`, `decidedCount`, `decidedSeq`, `decidedSeq_le_decidedDensity`,
`card_coeff`, `instFiniteCoeff`; mathlib `Nat.card_le_card_of_injective`, `div_le_div_of_...`.

**RISK** Low. Cast discipline (`ℕ → ℝ`) is the only friction; mirror `Gates.lean:325`.

---

### CN-10 | `genuineDensity_le_of_superset` | tier: sonnet | est. 25 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- CONTRACT -/
theorem genuineDensity_le_of_superset {n N : ℕ} {σ : FactorizationType}
    {T : Set (Coeff O n N)} (hT : possibleSet O n σ N ⊆ T) :
    genuineDensity O n σ ≤ (Nat.card T : ℝ) / (residueCard O : ℝ) ^ (n * N)
```

**SOURCE** The outer twin of CN-09; the landed pieces are `genuineDensity_le_possibleSeq`
(`GenuineDensity.lean:299`) and `possibleCount` monotonicity. No landed general form exists —
`Drainage.lean`'s upper bounds all go through the `n = 2` `undecidedCount_le`.

**CONSUMED-BY** The outer half of every stratum census. Since the 2026-08-13 P4 rewire the
capstone's headline object is `genuineDensity = ⨅ N, possibleSeq` (`GenuineDensity.lean:266`),
so an upper bound on the density is now a *first-class* deliverable of every census, not just a
drainage by-product. Decision-proof: the P4 rewire is signed and frozen (append #48).

**DEPENDS** `possibleSet`, `possibleCount`, `possibleSeq`, `genuineDensity_le_possibleSeq`,
`card_coeff`; mathlib `Nat.card_le_card_of_injective`.

**RISK** Low. `T` must be a subset of the finite `Coeff O n N`, so `Nat.card T` is honest; no
finiteness hypothesis is needed.

---

### CN-11 | `drainage_of_undecided_comp` | tier: sonnet | est. 40 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
open Filter Topology
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- helper, public in the same file; general-`n` form of the landed `Drainage.lean:829` -/
theorem gapSeq_antitone_general (n : ℕ) (σ : FactorizationType) : Antitone (gapSeq O n σ)

/-- CONTRACT -/
theorem drainage_of_undecided_comp {n : ℕ} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop)
    (h : Tendsto (fun M => undecidedSeq O n (φ M)) atTop (𝓝 0))
    (σ : FactorizationType) : UndecidedVanishes O n σ
```

**SOURCE** The general-`n` extraction of the landed `n = 2` drainage proof
`Drainage.lean:838` (`drainage_two`, lines 839–856), whose only degree-2 inputs are
`gapSeq_antitone` (`:829`, stated at `n = 2` but with a degree-free proof) and
`undecidedSeq_tendsto_zero` (`:820`). `gapSeq_le_undecidedSeq` (`:716`) is ALREADY general in
`n`; so is `gapSeq_nonneg` (`:340`).

**CONSUMED-BY** `DrainageAt n` (`Statement.lean:118`), hence `UniformityStatement.ofDecided`
/`.toDecided` (`:124`/`:134`) and `TotalMassOne` (`:166`, via `totalMassOne_of_drainage`).
Every drainage proof at every degree ends by exhibiting a bound along a subsequence
(`2M` at `n = 2`; `N − 3m` steps at `n = 3` per `P5_INFRA_2026-08-14.md` §7 item 3); this node
is the fixed plumbing that converts such a bound into `UndecidedVanishes`. It survives the
WELDZERO arc, every chapter cut, and both the decided and genuine routes.

**DEPENDS** `gapSeq`, `gapSeq_nonneg`, `gapSeq_le_undecidedSeq`, `undecidedSeq`,
`UndecidedVanishes`, `possibleSeq_antitone`, `decidedSeq_mono`; mathlib
`tendsto_atTop_ciInf`, `squeeze_zero`, `Filter.Tendsto.comp`.

**RISK** Naming collision: the landed `gapSeq_antitone` is the `n = 2` instance. Do NOT edit it
in this node; land `gapSeq_antitone_general` beside it and leave the rename/merge to the
orchestrator (it is a strict generalization, so the merge is safe but is a landed-statement
change).

---

### CN-12 | `exists_monic_scaleRoots` | tier: opus | est. 70 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- CONTRACT -/
theorem exists_monic_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (m : ℕ) (h : ∀ i < f.natDegree, π ^ (m * (f.natDegree - i)) ∣ f.coeff i) :
    ∃ G : Polynomial O, G.Monic ∧ G.natDegree = f.natDegree ∧ f = G.scaleRoots (π ^ m)
```

**SOURCE** The integrality side condition that `TypeOfInvariance.lean`'s module docstring
(lines 19–22) explicitly declines to prove: *"This one carries a side condition, because
`F(π^m Y) / π^(m n)` is integral only when the Newton polygon of `F` lies above the line of
slope `m`. The clean statement runs the substitution BACKWARDS, where no side condition
exists."* This node supplies the forward direction's hypothesis-discharge, in the ONE polygon
formulation that is representation-free: "polygon above slope `m`" written as divisibility of
coefficients. Composed with the landed `typeOf_scaleRoots` (`:486`) / `typeOf_scale` (`:521`)
it gives depth reduction `typeOf f = typeOf G`.

**CONSUMED-BY** The depth-reduction step of the deep-tail recursion at EVERY degree and every
order — `P5_INFRA_2026-08-14.md` §7 item 1 names the missing hypothesis-manufacturing lemma,
and this is the half of it that does not need the polygon case analysis. Decision-proof: it is
stated purely in `Polynomial.scaleRoots` + divisibility, so it is invariant under whichever
Newton-polygon representation 0d picks (see REJECTED R1).

**DEPENDS** `Polynomial.scaleRoots`, `coeff_scaleRoots`, `natDegree_scaleRoots`,
`monic_scaleRoots_iff` (all mathlib, all already used in `TypeOfInvariance.lean:200-220`);
pattern-match the landed `eq_scaleRoots_of_comp` (`:502`), which is the same computation run in
the opposite direction.

**RISK** The witness `G` must be built coefficientwise from the quotients
`f.coeff i / π^(m(n−i))`, which requires `Classical.choice` on the divisibility witnesses and a
degree argument to see `G` is monic of degree `n`. Wasted-work risk is nil (the statement is
forced); proof risk is moderate — budget an opus.

---

### CN-13 | `dvd_sub_coeff_of_scaleRoots` | tier: sonnet | est. 30 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- CONTRACT -/
theorem dvd_sub_coeff_of_scaleRoots (hπ : Irreducible π) {G G' : Polynomial O}
    (hG : G.Monic) (hG' : G'.Monic) (hdeg : G'.natDegree = G.natDegree) {m N : ℕ}
    (h : ∀ i, π ^ N ∣ ((G'.scaleRoots (π ^ m)).coeff i - (G.scaleRoots (π ^ m)).coeff i)) :
    ∀ i, π ^ (N - m * G.natDegree) ∣ (G'.coeff i - G.coeff i)
```

**SOURCE** `P5_INFRA_2026-08-14.md` §7 item 3, verbatim: *"the extraction `X = π^m Y` changes
the level (roughly `N ↦ N − 3m`). The correspondence of classes … is not proved."* This node is
the coefficient-level kernel of that correspondence, and the ONLY part of it whose statement is
pinned today. Proof: `coeff_scaleRoots` turns the difference into
`(G'.coeff i − G.coeff i) · π^(m(n−i))`; cancel in the domain; weaken `m(n−i)` to `m·n`.

**CONSUMED-BY** Any formulation of the level-bookkeeping clause of HYP.08 at any degree — the
level drop is read off exactly this divisibility, whatever map on classes 0c eventually fixes.
Decision-proof because it is a statement about coefficients, not about `Coeff O n N` classes;
every candidate class-correspondence factors through it.

**DEPENDS** `coeff_scaleRoots`, `natDegree_scaleRoots` (mathlib); domain cancellation
`mul_right_cancel₀`, `pow_ne_zero`, `Irreducible.ne_zero`.

**RISK** Truncated subtraction: `N - m * G.natDegree` is `ℕ`-subtraction, so the statement is
vacuously easy when `m·n ≥ N`. That is intended (the level is exhausted), but the consumer must
not read it as a nontrivial claim there — say so in the docstring.

---

### CN-14 | `typeOf_prod_X_sub_C` | tier: sonnet | est. 35 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- CONTRACT -/
theorem typeOf_prod_X_sub_C {n : ℕ} (r : Fin n → O) :
    typeOf (∏ i : Fin n, (X - C (r i))) = ⟨Multiset.replicate n (1, 1)⟩
```

**SOURCE** Generalization to all `n` of the landed degree-2 instance `Gates.lean:171`
(`typeOf_mul_linear : typeOf ((X - C r) * (X - C s)) = splitType`). Proof: induction on `n`
using CN-03 and the landed `typeOf_of_natDegree_one` (`TypeOf.lean:350`).

**CONSUMED-BY** The totally split stratum, which is on the covering menu at every degree and in
every chapter cut, and is the base case of every peel. Decision-proof: `⟨{(1,1)}⟩` is the
type of a monic linear by a landed theorem, not by a convention that 0d could move.

**DEPENDS** CN-03 (the only internal edge); `typeOf_of_natDegree_one`, `monic_X_sub_C`,
`Polynomial.monic_prod_of_monic`; mathlib `Multiset.replicate_succ`, `Fin.prod_univ_succ`.

**RISK** Low. Watch `n = 0`: the empty product is `1`, `monicFactors 1 = 0`, so
`typeOf 1 = ⟨0⟩ = ⟨Multiset.replicate 0 (1,1)⟩` — check this base case explicitly rather than
assuming it.

---

### CN-15 | `exists_anisotropic` | tier: sonnet | est. 45 lines

**SIGNATURE**
```lean
-- lands in `leancheck` (see RISK) — namespace `Uniformity.Density` or `UniformityCheck`
open Uniformity Uniformity.Density

/-- CONTRACT -/
theorem exists_anisotropic (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] : ∃ a : Fin 2 → O, Anisotropic a
```

**SOURCE** `spec/HYPOTHESIS_LEDGER.md` HYP.147 (v3 delta item 15), which DISPLAYS this exact
missing declaration and quotes `GENUINE_DENSITY_2026-08-13.md:697,704`: *"What is fenced out:
the general-`O` inert lower bound … the `gate_bracket_*` payoff is therefore stated at
`q = 2, 3` rather than for all `O`."* The ledger also names the intended route: leancheck's
`two_mul_card_aniK` (`FiniteFieldQuad.lean:104`), giving `2·#Ani + q = q²`, so `#Ani ≥ 1`
whenever `q ≥ 2` (`two_le_residueCard`, `LocalData.lean:84`); then lift `(b₀,b₁)` through
`residue_surjective` and convert with `aniK_iff` (`FiniteFieldQuad.lean:25`).

**CONSUMED-BY** The `n = 2` leaf of `UniformityStatement`, which quantifies over EVERY complete
DVR (`Statement.lean:74`). The landed inert certificates are `ℤ_[p]`-only
(`Gates.lean:441` `anisotropic_padic`, `:454` `inert_decided_class_padic`), so without this node
the degree-2 leg of the capstone is not general-`O`. Decision-proof: `n = 2` is the induction's
base case under every chapter cut (ledger HYP.137's premise correction: *"the n≤3 menus and
drainage DO enter the final proof — they are the induction's base cases"*).

**DEPENDS** `Anisotropic`, `quadForm` (`QuadCert.lean:336-341`); `UniformityCheck.AniK`,
`aniK_iff`, `two_mul_card_aniK`; `two_le_residueCard`, `IsLocalRing.residue_surjective`.

**RISK** PLACEMENT, not mathematics: `Anisotropic` lives in `leanfinal`, `two_mul_card_aniK` in
`leancheck`, and `leanfinal` must not import `leancheck`. Two dispositions, orchestrator's
call: (a) land the node in `leancheck` and leave the general-`O` `gate_bracket_*` payoff there
too, or (b) first move `FiniteFieldQuad.lean` into `leanfinal` (self-contained, mathlib-only,
122 lines) and then land the node in `leanfinal`. Sign convention: `AniK (b₀, b₁)` matches
`quadForm a u v = u² − a₁uv + a₀v²`, i.e. `a 0 ↦ b₀`, `a 1 ↦ b₁` — verify before proving.

---

### CN-16 | `card_certSet_gen` | tier: opus | est. 60 lines

**SIGNATURE**
```lean
namespace UniformityCheck
open Uniformity Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- CONTRACT -/
theorem card_certSet_gen {n N m : ℕ} (hm : m ≤ N) {D : Type*}
    (read : Res O N → (Coeff O n N ≃ D)) (S : Set D)
    (cert : Res O N → Coeff O n N → Prop)
    (hcert : ∀ γ c, cert γ c ↔ read γ c ∈ S)
    (hshift : ∀ γ γ' c, cert γ c → resFactor (O := O) hm γ' = resFactor hm γ → cert γ' c)
    (huniq : ∀ γ γ' c, cert γ c → cert γ' c → resFactor (O := O) hm γ' = resFactor hm γ) :
    Nat.card {c : Coeff O n N | ∃ γ, cert γ c} = residueCard O ^ m * Nat.card S

/-- helper, public: the landed lemma becomes an instance -/
example : True := trivial   -- `card_certSet = card_certSet_gen (n := 2) readEquiv`
```

**SOURCE** `leancheck/UniformityCheck/Counting.lean:228` (`card_certSet`), THE census lemma.
Its proof (lines 234–261) uses `readEquiv` only as "an `Equiv` for each centre" — the
`n = 2`-specific `(F(γ), F'(γ))` reading is never unfolded. This node is therefore a verbatim
re-parametrization: replace `readEquiv γ : Coeff O 2 N ≃ Res O N × Res O N` by an abstract
`read γ : Coeff O n N ≃ D`.

**CONSUMED-BY** Every stratum count at every degree. Currently consumed at
`InertCensus.lean:117` and `RamCensus.lean:202`; every higher-degree census must consume the
same shape, and the count law `q^m · #S` (centre contributes `q^m`, admissible data `#S`) is
the census pattern the whole counting layer is built on. Decision-proof: it is strictly more
general than a landed, proved lemma, so it cannot be wrong; and the centre/`resFactor`
bookkeeping is fixed by the frozen truncation tower (`LocalData.lean:215-312`).

**DEPENDS** `Res`, `Coeff`, `resFactor`, `resFactor_surjective`, `resSection`,
`resFactor_resSection`, `card_res`; mathlib `Nat.card_eq_of_bijective`, `Nat.card_prod`.
Landed `card_certSet` should be re-derived from it in the same file as a regression check.

**RISK** Wasted-work risk (not correctness): at degree ≥ 3 the centre may need to be richer
than a single `Res O N` (a point AND a slope). If so this node is still correct and still
consumed by the single-centre strata; a two-centre variant would be a separate node. The
`n = 2` `readEquiv` itself is NOT generalized here — see REJECTED R16.

---

### CN-17 | `exists_monic_factorization_finset` | tier: opus | est. 90 lines

**SIGNATURE**
```lean
namespace Uniformity.Hensel
open Polynomial IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

/-- CONTRACT -/
theorem exists_monic_factorization_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : Polynomial R} (hf : f.Monic) (g₀ : ι → Polynomial (ResidueField R))
    (hmon : ∀ i ∈ s, (g₀ i).Monic)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g₀ i) (g₀ j))
    (hfgh : f.map (residue R) = ∏ i ∈ s, g₀ i) :
    ∃ g : ι → Polynomial R, (∀ i ∈ s, (g i).Monic) ∧ f = ∏ i ∈ s, g i ∧
      (∀ i ∈ s, (g i).map (residue R) = g₀ i) ∧
      (∀ i ∈ s, (g i).natDegree = (g₀ i).natDegree)
```

**SOURCE** `spec/HYPOTHESIS_LEDGER.md` HYP.03, verbatim STATEMENT: *"A finite pairwise-coprime
residual factorization lifts to the corresponding finite monic factorization"*, WHERE
`leanfinal/notes/HENSEL_FACT_2026-08-13.md` §§6.2–7, PROPOSED DISPOSITION: *"NODE — induction
from the landed two-block theorem using `IsCoprime.prod_right`."* The landed two-block theorem
is `HenselFactorization.lean:393` (`exists_monic_factorization`).

**CONSUMED-BY** HYP.03's own CONSUMED-BY: *"general-degree factorization and n≥4
splitting-type assembly."* Composed with CN-03 it gives the full order-0 leaf law at every
degree (see REJECTED R10). Decision-proof: it is a statement about lifting factorizations over
a complete local ring, with no reference to any classifier, chapter, or menu; the Q4 policy
even puts it outside the human-review surface (*"the Hensel statements take care of
themselves"*, append #47).

**DEPENDS** Landed `exists_monic_factorization`, `isCoprime_of_map_eq`,
`monic_factorization_unique`, `natDegree_eq_of_map_eq` (all `HenselFactorization.lean`);
mathlib `IsCoprime.prod_right`, `Finset.prod_insert`, `Finset.induction_on`,
`Polynomial.monic_prod_of_monic`.

**RISK** Two real ones. (a) The induction hypothesis needs `IsCoprime (g₀ i) (∏ j ∈ s', g₀ j)`
from pairwise coprimality — that is `IsCoprime.prod_right`, but check its exact mathlib form
before starting. (b) `g` is a total function while only `i ∈ s` is constrained; use
`Classical` junk off `s` and do NOT add a `g i = 1` clause to the statement (it would over-fix
the interface). Uniqueness is deliberately NOT part of this contract; if a consumer needs it,
book it as a separate node from `monic_factorization_unique`.

---

### CN-18 | `typeOf_of_residual_coprime` | tier: sonnet | est. 30 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
open Uniformity.Hensel
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- CONTRACT -/
theorem typeOf_of_residual_coprime {f : Polynomial O} (hf : f.Monic)
    {g₀ h₀ : Polynomial (ResidueField O)} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue O) = g₀ * h₀) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue O) = g₀ ∧ h.map (residue O) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
      (typeOf f).data = (typeOf g).data + (typeOf h).data
```

**SOURCE** The landed `Hensel.exists_monic_factorization_dvr`
(`HenselFactorization.lean:777`) with CN-03's conclusion appended. This is the ORDER-0 /
LEVEL-1 PEEL: it is the only place the classifier's leaf layer touches `typeOf`.

**CONSUMED-BY** Chapter B (leaf/order-1 layer) under every version of the chapter cut, and the
order-0 stratum of every menu at every degree. It is also the Lean form of T2's
`(LABEL-PROD)` / `(SIDE-PROD)` split at the residual level (`EFF-T2-s1of6.md`
EFF.T2.s1of6.17/.22). Decision-proof: both halves are already-landed frozen theorems; the node
only welds them.

**DEPENDS** CN-03 (the only internal edge); landed `exists_monic_factorization_dvr`.

**RISK** None mathematically. Bookkeeping only: `residue O` vs `Ideal.Quotient.mk (maximalIdeal O)`
must be the same map the landed theorem uses — copy the landed signature's spelling verbatim.

---

### CN-19 | `norm_adjoinRoot_root` | tier: opus | est. 130 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
open Polynomial
variable {O : Type*} [CommRing O] [IsDomain O]

/-- CONTRACT -/
theorem norm_adjoinRoot_root {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree) :
    Algebra.norm O (AdjoinRoot.root f) = (-1) ^ f.natDegree * f.coeff 0
```

**SOURCE** Generalization to all `n` of the landed degree-2 instance `QuadCert.lean:175`
(`norm_root_quad : Algebra.norm O (AdjoinRoot.root (monicPoly a)) = a 0`), which is this
statement at `n = 2` since `(−1)² · coeff 0 = a 0`. `typeOf` is DEFINED through
`Algebra.norm` on `AdjoinRoot g` (`TypeOf.lean:182-193`), so this is the universal read.

**CONSUMED-BY** Every ramified/Eisenstein certificate at every degree (CN-20 directly), and any
`inertiaDegOf` computation that needs a norm-valuation other than `deg` — the landed
recognition principles `inertiaDegOf_eq_of` (`TypeOf.lean:229`) and
`inertiaDegOf_eq_one_of_coprime` (`:237`) both need an explicitly computed norm, and `deg` is
the only one currently available (`natDegree_mem_normValues`, `:247`). Decision-proof: it is a
theorem about the frozen `typeOf` definition's own ingredient.

**DEPENDS** `AdjoinRoot.powerBasis'`, `PowerBasis.basis`, `Algebra.norm_eq_matrix_det`,
`Algebra.leftMulMatrix_eq_repr_mul` (the exact route used at `QuadCert.lean:166`); mathlib
`Matrix.det_succ_row_zero` or a triangularity lemma.

**RISK** THE HIGHEST-RISK NODE ON THIS LIST, and the risk is proof cost, not correctness.
Checked 2026-08-14: mathlib has NO companion-matrix determinant (`grep -i companion` over
`Mathlib/` returns only quadratic-form `exists_companion` and prose), and
`PowerBasis.norm_gen_eq_coeff_zero_minpoly` (`Mathlib/RingTheory/Norm/Basic.lean:65`) is stated
through `minpoly R pb.gen`, which is not available as `f` over a non-field base without
irreducibility. So the node must either (i) compute the `n × n` companion determinant by
expansion along the first row, or (ii) establish `minpoly O (AdjoinRoot.root f) = f` for monic
`f` and quote the mathlib lemma. Route (ii) is likely cheaper — try it FIRST and return BLOCKED
with the minpoly obstruction if it fails, rather than sinking the budget into (i).

---

### CN-20 | `typeOf_eisenstein` | tier: opus | est. 60 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- CONTRACT -/
theorem typeOf_eisenstein {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hlow : ∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O)
    (h0 : f.coeff 0 ∉ (maximalIdeal O) ^ 2) :
    typeOf f = ⟨{(f.natDegree, 1)}⟩
```

**SOURCE** Generalization to all `n` of the landed degree-2 instance `QuadCert.lean:283`
(`typeOf_ram_of_eisenstein : typeOf (monicPoly a) = ramType`, `ramType = ⟨{(2,1)}⟩`). At
degree 2 the landed proof re-proves irreducibility by hand (`:266`); at general `n` mathlib
supplies it.

**CONSUMED-BY** The totally ramified leaf, which is on the covering menu at every degree
(`(n,1)` is a type of degree `n` for every `n`) and is the standard non-trivial exact value the
census must produce. Under every chapter cut and every WELDZERO outcome the Eisenstein stratum
is present. Decision-proof: `⟨{(n,1)}⟩` is forced by the frozen `(e,f)` ordering convention
(`TypeOf.lean:292-297`, HYP.12 inside the CORE-SET audit) — it is not a namable menu constant.

**DEPENDS** CN-19 (the only internal edge); mathlib `Polynomial.IsEisensteinAt`,
`IsEisensteinAt.irreducible` (`Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:230`),
`Polynomial.Monic.isPrimitive`, `IsLocalRing.maximalIdeal.isMaximal`; landed
`inertiaDegOf_eq_of`, `IsDiscreteValuationRing.addVal_uniformizer`, `monicFactors_eq`.

**RISK** Two checks before starting. (a) `IsEisensteinAt.irreducible` takes
`(hprime : 𝓟.IsPrime) (hu : f.IsPrimitive) (hfd0 : 0 < f.natDegree)` — confirm the exact
argument order at HEAD mathlib rather than from memory. (b) `AdjoinRoot.root f ≠ 0` is needed
for the `1 ∈ normValues` step; derive it from `h0` (if the root were `0` then `f.coeff 0 = 0`,
which lies in `𝔪²`), NOT from irreducibility.

---

### CN-21 | `typeOf_inert_of_irreducible_map` | tier: opus | est. 150 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- CONTRACT -/
theorem typeOf_inert_of_irreducible_map {f : Polynomial O} (hf : f.Monic)
    (hd : 0 < f.natDegree) (h : Irreducible (f.map (residue O))) :
    typeOf f = ⟨{(1, f.natDegree)}⟩
```

**SOURCE** Generalization to all `n` of the landed degree-2 instance `QuadCert.lean:400`
(`typeOf_inert_of_anisotropic : typeOf (monicPoly a) = inertType`, `inertType = ⟨{(1,2)}⟩`);
at `n = 2`, `Anisotropic a` says exactly that the reduction has no residual root, i.e. is
irreducible.

**CONSUMED-BY** The unramified leaf `(1, n)`, on the covering menu at every degree and the
`e = 1` end of every order-0 stratification; T2's clause 2 reads `f = f_𝒞 · deg r'`
(`EFF-T2-s1of6.md` EFF.T2.s1of6.31 clause 2), whose `e_𝒞 = 1`, `deg r' = n` instance this is.
Survives every chapter cut for the same reason as CN-20.

**DEPENDS** `Polynomial.Monic.irreducible_of_irreducible_map`, `AdjoinRoot.powerBasis'`;
landed `inertiaDegOf_eq_of`, `natDegree_mem_normValues`, `normValues`, `monicFactors_eq`;
mathlib DVR characterizations (`IsDiscreteValuationRing.of_...` / `HenselianLocalRing`).

**RISK** The hard step is "`inertiaDegOf f = n`", i.e. `n ∣ v(N z)` for every nonzero
`z ∈ AdjoinRoot f`. The intended route: `A = AdjoinRoot f` is a local domain with
`A ⧸ πA` a field (that is `h`), so `πA` is maximal and principal, so `A` is a DVR with
uniformizer `π`; then `z = π^k · u`, `N z = π^(nk) · N u`, `N u` a unit. Each of those steps is
short mathematically and possibly long in Lean. If the DVR step stalls, return BLOCKED naming
it — do NOT weaken to a `Finite (ResidueField O)` or separability hypothesis, which would not
help and would narrow the contract.

---

### CN-22 | `exists_coveringMenu` | tier: opus | est. 90 lines

**SIGNATURE**
```lean
namespace Uniformity.Density
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- CONTRACT -/
theorem exists_coveringMenu (n : ℕ) : ∃ S : Finset FactorizationType, CoveringMenu O n S
```

**SOURCE** `GenuineDensity.lean:458` defines `CoveringMenu` and its docstring asserts the
mathematics without proving it: *"This is the finiteness input that makes `Σ_σ` meaningful —
`FactorizationType` itself is infinite, and only finitely many types occur in degree `n`."*
Landed only at `n = 2` (`coveringMenu_two`, `Drainage.lean:1087`) and `n = 1`. Proof: by CN-04
every occurring type is a multiset of pairs with `1 ≤ e, 1 ≤ f`, and by `typeOf_degree` their
`Σ ef = n`, so card `≤ n` and every coordinate `≤ n`; inject `σ.data` into
`(Fin (n+1) × Fin (n+1)) → Fin (n+1)` by `Multiset.count` and use `Multiset.ext`.

**CONSUMED-BY** `TotalMassOne` (`Statement.lean:166`) and `sum_genuineDensity_eq_one_of_drainage`
(`GenuineDensity.lean:513`) — both quantify over covering menus, and without existence at
general `n` the whole `Σ_σ R_σ = 1` layer is contentless above `n = 2`. Also the assembly
chapter's "finitely many σ carry mass, the rest are 0" split (with CN-06). Decision-proof: it
is a statement about the frozen `CoveringMenu` predicate; every chapter cut needs a finite
menu, and none of them can supply one from a chapter-local definition.

**DEPENDS** CN-04 (the only internal edge); `CoveringMenu`, `typeOf_degree`,
`monicPoly_natDegree`, `FactorizationType.degree`, `FactorizationType.ext`; mathlib
`Multiset.ext`, `Multiset.count`, `Set.Finite.toFinset`, `Finset.image`.

**RISK** Real but bounded: the finiteness argument on multisets is the whole node, and mathlib's
`Multiset` finiteness API is thin. Two routes — (a) the count-function injection above, or
(b) `Sym (Fin (n+1) × Fin (n+1)) k` for `k ≤ n`, which is a `Fintype`. Try (b) first; it is
closer to an off-the-shelf instance. Nothing about the CONCLUSION can be wrong; only the effort
is uncertain. This node deliberately does NOT name the menu — see REJECTED R8.

---

### CN-23 | `FactorizationType.degree_mk_add` | tier: sonnet | est. 10 lines

**SIGNATURE**
```lean
namespace Uniformity
open Uniformity

/-- CONTRACT -/
theorem FactorizationType.degree_mk_add (σ τ : FactorizationType) :
    (⟨σ.data + τ.data⟩ : FactorizationType).degree = σ.degree + τ.degree
```

**SOURCE** `LocalData.lean:49` (`FactorizationType.degree`) + mathlib `Multiset.map_add`,
`Multiset.sum_add`. The degree bookkeeping half of the peel law.

**CONSUMED-BY** Every use of CN-03 that then reasons about degrees — i.e. all of them: the peel
law gives `.data` additivity, and the consumer invariably needs `deg = deg + deg` to close the
degree accounting (T2's `(HULL-LENGTH)` / `(MID-MASS)`, `EFF-T2-s1of6.md` .11/.23; the
`σ.degree = n` conjunct of the capstone). Decision-proof: pure `Multiset` arithmetic over a
frozen definition, and it introduces no algebraic structure on `FactorizationType`
(see REJECTED R14).

**DEPENDS** `FactorizationType`, `FactorizationType.degree`; mathlib `Multiset.map_add`,
`Multiset.sum_add`.

**RISK** None. Smallest node on the list; bundle it with CN-03's file if the orchestrator
prefers, but keep the declaration name.

---

## REJECTED — examined and NOT listed, with the filter each fails

This section is a deliverable in its own right: it records what was deliberately considered and
why it is not yet a node, so no later sweep re-litigates it silently. "Fails F1" = not certain
under every open branch; "Fails F2" = the exact Lean statement cannot be written today;
"Fails F3" = needs more than one other CN.

**R1. Newton-polygon primitives over `O[X]` (hull, vertices, sides, slopes).** FAILS F1 AND F2.
`leanfinal` has none; the quarry has `lean/LeanUrat/OM/NewtonPolygon.lean` (828 lines, proved,
`sorry`-free) plus `Order0Hull.lean`, `HullStability.lean`, `ResidualPolynomial.lean`,
`MultiSlopeMenu.lean`. The blocker is that the quarry FIXES a representation the blueprint has
not chosen: the support is an input `Finset (ℕ × ℕ)` with ℕ-valued valuations, the height is a
`Finset.sup'` over valid supporting lines (`npHeight`), and the file's own header records that
an earlier `inf'` definition was refuted by counterexample. Whether the leanfinal polygon reads
a `Finset (ℕ × ℕ)`, a function `ℕ → ℕ∞` (matching `IsDiscreteValuationRing.addVal`), or ℚ-slope
data is exactly a Phase-0d interface decision (`BLUEPRINT_PHASE_DESIGN` REVISION 2, stage 0d:
"the open v1 §7 decisions … quarry-vs-fresh for the leaf layer … are RESOLVED at this stage as
interface decisions"), and v1 §7 item 3 names it explicitly. **Verdict: quarry-copy vs
fresh-prove must NOT be decided by this list.** What survives the decision, and is listed: the
two representation-free polygon reads, CN-12 (above-slope-`m` ⟹ integral extraction) and
CN-13 (the level drop across it).

**R2. The T2 σ-ladder CARRIER structure** (`h`, `dig`, normalizers `n(k)`, cocycle `τ`,
`ϑ_s`/`Θ_s`, `γ_k`, `Pt`, threshold `T`, integer-normalized value `d = c_𝒞 v`). FAILS F2, and
the source says so: `spec/EFF-T2-s1of6.md` EFF.T2.s1of6.01 quotes the note verbatim — *"It
contains no Lean signature, record declaration, or interface sketch. Formal encodings belong to
the S-5 probe output and to stage 2 of the arc."* Writing a `structure SigmaLadderCarrier`
today would be inventing the interface the spec refuses to fix.

**R3. `THEOREM HE7.A` and `THEOREM T2.KEY-BOUNDARY`** (EFF.T2.s1of6.31/.32). FAILS F2 via R2 —
they quantify over a carrier. Also FAILS F1 in part: both are conditional on `(LB1)` and
`(MP1)` (EFF.T2.s1of6.18/.23), whose placement (blueprint hypothesis vs discharge node) is an
open 0d decision (`BLUEPRINT_PHASE_DESIGN` v1 §7 item 2). The one piece of HE7.A that is
decision-proof — clause 6's "multiply the successive `e`- and `f`-increments" — IS listed, as
CN-03.

**R4. The T1/T3 cocycle-telescope layer** (`τ_N(a,b)`, `ϑ_N(s;q)`, `Θ_N(s;q)`, the B-law,
`(T1-C2)`/`(T1-TEL)`/`(T1-THETA)`/`(T1-DICT)`). FAILS F2, same reason as R2: `spec/EFF-T3.md`
EFF.T3.01–.05 are all stated over T1's carrier ("Fix a tower level `i`. Write
`N(k) := n̂_i(k)`"), imported and not re-derived, with the Lean encoding unlanded.

**R5. HYP.08 level bookkeeping as a whole** (classes mod `π^N` ↦ classes mod `π^(N−3m)`).
FAILS F1 AND F2. `leanfinal/notes/P5_INFRA_2026-08-14.md` §7 item 3 is explicit that the
statement does not exist yet: *"The correspondence of classes — the statement that would let
`undecidedSeq` at level `N` be bounded by `undecidedSeq` at the reduced level — is not
proved."* The `3m` is cubic-specific (it is `n·m` in general) and the map on `Coeff O n N` is
unpinned. Rescued in part by CN-13, which is the coefficient-level kernel every candidate
formulation must factor through.

**R6. The Newton-polygon case analysis of the recentred cubic** (P5 §7 item 1: the lemma taking
`(B₀,B₁,B₂)` to "one side of integral slope `m`" / "non-integral slope" / "two or three sides",
and the lemma PRODUCING the point `x₀` with `v(F(x₀)) > 2v(F'(x₀))`). FAILS F1 (degree-3
specific, and the case list depends on the 0c stratification) and F2 (needs R1's
representation). The tool it feeds — strong Hensel — is already landed
(`StrongHensel.lean:340`).

**R7. HYP.07, the non-integral-slope `CertRam3`.** FAILS F1 and F2. Ledger class:
`lean-open-statement`, disposition **MATH** — *"norm/valuation proof absent"*. It is missing
mathematics, not bookkeeping, and its statement needs R1.

**R8. A hard-coded `CoveringMenu O 3 S` with the five cubic types.** FAILS F2 in the sense that
matters: writing it requires NAMING five `FactorizationType` constants
(`⟨{(1,1),(1,1),(1,1)}⟩`, `⟨{(1,1),(2,1)}⟩`, `⟨{(1,1),(1,2)}⟩`, `⟨{(3,1)}⟩`, `⟨{(1,3)}⟩`), and
the naming/placement of menu constants is a 0d interface decision (the landed precedent
`linType/splitType/inertType/ramType`, `QuadCert.lean:43-52`, is degree-2-local). Also
`spec/HYPOTHESIS_LEDGER.md` HYP.10 marks the enumeration *"LOW-CONFIDENCE until checked in
Lean."* Superseded by CN-22 (existence, no naming) + CN-04 (the positivity constraint that
makes any later enumeration possible).

**R9. HYP.02 `eq_of_add_mul_eq`** (injectivity, hence bijectivity, of the degree-bounded map
`(u,v) ↦ hu + gv`). FAILS F1 on the ledger's own words: CONSUMED BY *"optional injectivity
refinements of two-block Hensel; **the n=3 consumer does not obviously need it**."* Nothing
names it as required.

**R10. The full order-0 leaf law** (`f̄` separable with monic irreducible factorization
`∏ r̄ᵢ` ⟹ `typeOf f = ⟨Σ (1, deg r̄ᵢ)⟩`). Passes F1 and F2 — but FAILS F3: it needs CN-17
(`n`-fold Hensel) AND CN-03 (`typeOf_mul`) AND CN-21 (the unramified leaf), three internal
edges. **Recommendation to the orchestrator: book it as the FIRST second-layer node once
CN-03, CN-17 and CN-21 land.** It is the single highest-value node not on this list.

**R11. `UniformityStatement` assembly lemmas** ("it suffices to give the law on a covering menu
and 0 off it"; the `num/den` bookkeeping). FAILS F1 — the shape depends on chapter J's assembly
design, which the 0c DAG has not cut. The two decision-proof fragments ARE listed: CN-05 and
CN-06 (the "0 off the menu" half) and CN-22 (the menu's existence).

**R12. The cubic drainage rate `u(N) ≤ q^(−N/2) + q^(−5)·u(N−3)` (HYP.08's inequality) and
HYP.09 (triple-root drainage).** FAILS F1/F2 — ledger class MATH, and P5 §7 items 3–4 record
both as underived. CN-11 supplies the plumbing that will consume such a bound once it exists.

**R13. Hypothesis-manufacturing lemmas for strong Hensel** (producing `x₀` from a polygon
hypothesis). FAILS F2 — same unpinned statement as R6. The theorem itself is landed
(`strongHensel`, `strongHensel_addVal`, HYP.04 DISCHARGED 2026-08-14).

**R14. Algebraic structure on `FactorizationType`** (`Add`/`AddCommMonoid` instance, a
`FactorizationType.add`, a `degree` monoid hom). FAILS F1 — adding structure to a CORE-SET
trust-boundary definition is a 0d decision requiring a faithfulness note and Asvin sign-off
(`BLUEPRINT_PHASE_DESIGN` stage 0d; ledger HYP.98). CN-03 and CN-23 deliver the entire content
WITHOUT any new instance, by stating everything on `.data` and on the explicit `⟨σ.data + τ.data⟩`.

**R15. `typeOf` faithfulness (HYP.01) and the `(e,f)` ordering convention (HYP.12).** Not Lean
nodes at all — ledger disposition NODE **[CORE-SET]**, and the Q4 review-boundary policy
(append #47) keeps them as human definitional-audit items under HYP.98. Listing them as fleet
work would misroute them.

**R16. `readEquiv` at general `n`** (the centred reading `c ↦ (F(γ), F'(γ))`). FAILS F2: at
degree `n` the analogue is not determined — the `n = 2` reading uses exactly the two Taylor
coefficients that exist, and whether degree 3 reads `(F, F', F'')`, a truncated Taylor jet, or a
polygon-indexed datum is undecided. CN-16 is the decision-proof residue: the census lemma
PARAMETRIZED over whatever read is eventually chosen.

---

## NOTES FOR THE ORCHESTRATOR

1. **Nothing here touches a landed statement.** The two places where a landed declaration is
   strictly generalized — `gapSeq_antitone` (CN-11) and `card_certSet` (CN-16) — are specified
   as NEW declarations beside the old ones, with the merge left as an orchestrator decision.
2. **One placement question needs answering before CN-15 fires:** whether
   `leancheck/UniformityCheck/FiniteFieldQuad.lean` (122 lines, mathlib-only, self-contained)
   moves into `leanfinal`. If yes, CN-15 lands in `leanfinal` and the general-`O`
   `gate_bracket_*` payoff follows there; if no, CN-15 lands in `leancheck` and HYP.147's
   consumer stays out of the final artifact.
3. **Two nodes are budget risks, both flagged in their RISK lines:** CN-19 (no companion-matrix
   determinant in mathlib — try the `minpoly` route first, return BLOCKED rather than grinding)
   and CN-21 (the "`AdjoinRoot f` is a DVR" step). Everything else is routine.
4. **Suggested first wave (3 concurrent, per the fleet throttle):** CN-01, CN-02, CN-05 — all
   sonnet, all layer 0, all unblocking several others. Second wave: CN-03 (needs CN-02), CN-07,
   CN-04.
