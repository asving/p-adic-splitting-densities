# MAIN-THEOREM SCOPING — CORE SECTION: the Stage-2 signed anchor, its definition closure, and the corrected shape

Sources: `/data/users/asvin/math-and-lean/p-adic-splitting-densities/lean/LeanUrat/Stage2/UniformityTarget.lean` (working tree = **revision 2**, commit `cb169b40`, 2026-08-12), `lean/LeanUrat/CountingModel.lean`, `lean/LeanUrat/Interface.lean`, `lean/LeanUrat/MontesV2.lean`, `lean/LeanUrat/RatFn.lean`, `lean/LeanUrat/L4.lean`, `runs/leansimp_output.log` (D1–D12 + module tree), and git history (`8c56f600` = the leansimp fold that defect-flagged rev 1 in-file; `cb169b40` = rev 2 landed).

## 0. Findings requiring sign-off attention (established during this scoping pass)

**F1 — MACHINE-CHECKED: the rev-2 signed statements are provable from the abstract interface alone.** I compiled a scratch snippet (in-memory, no repo file touched) containing a byte-identical copy of `RealCountingFamily` and full proofs of both `uniformity_target` and `uniformity_target_exhaustive` against it. Both compile; `#print axioms` shows exactly `[propext, Classical.choice, Quot.sound]`; the linter confirms `hn : 0 < n` and `hσ : σ.degree = n` are **unused**, and the exhaustive variant's per-prime drainage hypothesis is **discarded**. The ~20-line proof: pick the prime 2, transport `(F.dataAt 2 h2).C_isRational` across `coefficient_coherent` to get `IsRationalFn (F.coefficient T)` for each menu shape, close under the finite sum via `MontesV2.isRationalFn_finsetSum`, then at each prime `p` tie the density via `MontesDataV2.countingDensity_eq_sum_coeff` + `shapes_coherent` + `coefficient_coherent`. Three consequences for sign-off:

1. The anchor's fence conclusion (NO proof unit may target these until `faithfulAt` is real) is not merely prudent — it is the **only** thing standing between the repo and a contentless discharge of both sorries. Discharging them today would prove nothing about ℤ_p.
2. The fence's stated *mechanism* is wrong: the header claims "an abstract family whose `coefficient` is not rational-in-q still defeats the law". No such family exists — `coefficient_coherent` + the `C_isRational` field of any single prime's `dataAt` force `coefficient T` to be rational-in-q. The actual failure mode of rev 2 is the opposite: **trivial truth**, not falsity. (Rev 1's failure mode was genuine falsity, via free instances; rev 2 traded falsity for vacuity-until-gated.)
3. The whole mathematical content of stage two therefore lives in **constructing the real family** — a `RealCountingFamily n` whose `modelAt` genuinely counts monic degree-n ℤ_p-boxes (`faithfulAt` real), whose `coefficient` is the canonical OM count with rationality a *theorem* (D6), and whose coherence fields are proved from GMN p-independence. The sign-off should decide whether the capstone remains "the signed statements + fenced real instance" or is restated as an existence/instantiation theorem about the canonical real family (D8's `uniformity_core` shape), so that provability *is* content.

**F2 — broken theorem-name cite in the anchor.** The rev-2 header (lines 20–21) cites the decomposition theorem as `MontesV2.countingDensity_eq_sum_C`. No such declaration exists anywhere in `LeanUrat/`; the actual name is `MontesDataV2.countingDensity_eq_sum_coeff` (`lean/LeanUrat/MontesV2.lean:123`). Comment-only, trivial fix, but per the repo's trust-boundary rule (comments are unverified claims) it should be corrected at revision.

**F3 — date reconciliation.** The tasking described "a 2026-08-11 defect flag comment". The in-file defect flag is dated **2026-08-12** (the leansimp review, folded at commit `8c56f600`); **2026-08-11** is the *statement-grain sign-off* date (bare (e,f)-multiset grain), recorded in both revisions. Both are quoted below.

**F4 — import-graph note.** The anchor imports `LeanUrat.MontesV2`, which transitively imports `LeanUrat.Interface` → `LeanUrat.PadicMeasure`. The *statement closure* (§2) consumes no measure object, but the *module* closure still touches the measure route — the D2/D5 split ("no new Stage2 file should import `PadicMeasure`") is pending, not landed.

---

## 1. THE CURRENT SIGNED STATEMENTS

File: `/data/users/asvin/math-and-lean/p-adic-splitting-densities/lean/LeanUrat/Stage2/UniformityTarget.lean` — outside the trusted capstone graph, exactly two `sorry`s (the two target bodies), `sorryAx` expected in this file and nowhere else.

### 1.1 `uniformity_target` (verbatim, lines 81–92)

```lean
/-- **THE STAGE-2 TARGET (decided density), rev. 2.** One rational law per
(n, σ) and per real counting family, tying the decided density at EVERY prime
simultaneously — the general form of `montes_unconditional`'s conclusion, with
no tame hypothesis (review D8). FENCED until `faithfulAt` is real. -/
theorem uniformity_target
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (F : RealCountingFamily n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p),
        den.eval (p : ℚ) ≠ 0 ∧
        (F.modelAt p hp).countingDensity σ = num.eval (p : ℚ) / den.eval (p : ℚ) := by
  sorry
```

Mathematical reading: for each degree n, each factorization type σ of degree n (bare (e,f)-multiset grain), and each coherent prime-indexed counting family, there is **one** rational function num/den ∈ ℚ(t), denominator nonvanishing at every prime, whose value at p is the DECIDED (level-N certified, N→∞) density of type σ among monic degree-n polynomials at p. The ∃ stands **outside** the ∀ p — the uniformity claim. (Per F1: `hn`, `hσ` currently do no work.)

### 1.2 `uniformity_target_exhaustive` (verbatim, lines 94–107)

```lean
/-- **THE STAGE-2 TARGET, full density, rev. 2.** The same law ties the full
density at every prime whose model additionally drains (undecided mass → 0),
mirroring `montes_unconditional_exhaustive`. FENCED until `faithfulAt` is real. -/
theorem uniformity_target_exhaustive
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (F : RealCountingFamily n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p),
        Filter.Tendsto
          (fun N => (F.modelAt p hp).undecidedCount N / (p : ℚ) ^ (n * N))
          Filter.atTop (nhds 0) →
        den.eval (p : ℚ) ≠ 0 ∧
        (F.modelAt p hp).countingDensity σ = num.eval (p : ℚ) / den.eval (p : ℚ) := by
  sorry
```

Mathematical reading: same law, with a per-prime drainage hypothesis (the inline `Tendsto` is exactly `CountingModel.UndecidedVanishes (F.modelAt p hp)` unfolded through `CountingModel.undecided`). **D9's standing complaint applies verbatim to rev 2**: the conclusion is the *same* `countingDensity` equality — there is no distinct full-density symbol, so the drainage hypothesis connects to nothing (F1 makes this a machine-checked fact: the hypothesis is literally discardable).

### 1.3 The defect-flag comment (rev 1, verbatim; commit `8c56f600`, superseded in the working tree)

This is the in-file flag the tasking referred to. It sat in rev 1's header until rev 2 landed:

```
**⚠ DESIGN DEFECT FLAGGED (2026-08-12, leansimp review — DO NOT TARGET
THESE STATEMENTS UNTIL REVISED).** `uniformity_target` fixes (num, den)
BEFORE quantifying over q and R, but `RealInstanceAt q n` admits arbitrary
unrelated instances: nothing forces two instances at the same q to share a
density, so the statement is false as stated (an adversarial abstract
instance defeats any single law). The fix (review D1/D6/D8): a canonical
`RealCountingFamily` with cross-prime coherent menu/coefficients replaces
the free bundle; the target quantifies over faithful views of THAT.
Revision awaits Asvin's sign-off (he reviewed the current form).
```

### 1.4 The rev-2 header that superseded it (verbatim, current file)

```
**REVISION 2 (2026-08-12, per the leansimp review D1/D6/D8, Asvin signed off).**
Revision 1's statements were FALSE-AS-STATED: they fixed (num, den) before
quantifying over q and a FREE instance bundle `RealInstanceAt q n`, whose
instances at the same q need not share a density. The fix, landed here: the
quantification is now over a `RealCountingFamily n` — one prime-indexed family
carrying a SINGLE shared shape menu and a SINGLE shared coefficient function,
with per-prime Montes data COHERENT with both (`shapes_coherent`,
`coefficient_coherent`), and `p.Prime` required. Within one family, the
decomposition theorem (`MontesV2.countingDensity_eq_sum_C`) pins each prime's
density to the shared data, so one law per family is the honest content.
The old rev-1 statements are preserved below in a comment for the record.

**THE REMAINING PLACEHOLDER (named, fenced).** `faithfulAt : True` still awaits
the realness gates (Unit 1 of the stage-two spec: the general analogue of
`OM/RealInstanceV2Gates.lean` — genuine monic-ℤ_p-box counting semantics, with
the same-prime uniqueness theorem as its safety check). UNTIL THAT UNIT LANDS,
NO PROOF UNIT MAY TARGET THESE STATEMENTS: with `faithfulAt` trivial, an
abstract family whose `coefficient` is not rational-in-q still defeats the law,
so the statements below are honest TARGETS only on the real family the gates
will pin.
```

(Per F2, `MontesV2.countingDensity_eq_sum_C` is a broken cite — actual name `MontesDataV2.countingDensity_eq_sum_coeff`. Per F1, the sentence "an abstract family whose `coefficient` is not rational-in-q still defeats the law" describes an impossible family; the true hazard is trivial provability.)

The file also carries (line 135–136, both revisions): *"Statement-grain sign-off (2026-08-11, Asvin): the bare (e,f)-multiset `FactorizationType` IS the intended target grain; finer invariants deferred."*

---

## 2. THE DEFINITION CLOSURE

Everything the two statement texts consume, recursively down to mathlib/core. Dependency DAG:

```
uniformity_target(_exhaustive)
├── RealCountingFamily            [Stage2/UniformityTarget.lean]
│   ├── CountingModel             [CountingModel.lean]
│   │   ├── FactorizationType     [Interface.lean]  ── Multiset (ℕ × ℕ)   (mathlib)
│   │   └── Filter.Tendsto / atTop / nhds / Monotone / Finset / ℚ        (mathlib)
│   ├── MontesDataV2              [MontesV2.lean]
│   │   ├── ClusterShape ⟷ ShapeCell (mutual)  [Interface.lean]
│   │   │   └── L4.LatticePolygon [L4.lean]  ── Fin / Bool               (core)
│   │   └── LeanUrat.RatFn.IsRationalFn  [RatFn.lean]  ── Polynomial ℚ   (mathlib)
│   └── True                                                              (core)
├── CountingModel.countingDensity (:= densityVal)  [CountingModel.lean]
├── CountingModel.undecidedCount (field; exhaustive variant only)
└── Polynomial ℚ / Polynomial.eval / Nat.Prime / Filter.Tendsto / atTop / nhds  (mathlib)
```

### 2.1 `RealCountingFamily` — `lean/LeanUrat/Stage2/UniformityTarget.lean:58` (verbatim, full, docstrings included — every field docstring is load-bearing)

```lean
/-- **The canonical prime-indexed real counting family** (leansimp review D1).
One shared shape menu and one shared coefficient function across all primes;
per-prime counting models and Montes data coherent with both. This coherence is
what makes "one law for all primes" a well-posed claim: within a family, the
V2 decomposition theorem pins the density at p to `∑ T ∈ menu σ, coefficient T p`.
-/
structure RealCountingFamily (n : ℕ) where
  /-- The counting model at each prime (as `realM2` at the committed prime). -/
  modelAt : ∀ p : ℕ, Nat.Prime p → CountingModel p n
  /-- THE shared shape menu: the finite set of cluster shapes contributing to
  each type — one menu for all primes (p-independence is L5fix/GMN content). -/
  menu : FactorizationType → Finset ClusterShape
  /-- THE shared per-shape coefficient `C T (q)` as a function of the residue
  cardinality — one function for all primes. Its rationality-in-q is the
  cross-prime coefficient-uniformity theorem (review D6), NOT a field. -/
  coefficient : ClusterShape → ℕ → ℚ
  /-- The Montes data over each prime's model (as `realD2`). -/
  dataAt : ∀ p hp, MontesDataV2 p n (modelAt p hp)
  /-- Every prime's shape decomposition uses THE shared menu. -/
  shapes_coherent : ∀ p hp σ, (dataAt p hp).shapesOf σ = menu σ
  /-- Every prime's per-shape coefficients are THE shared coefficients. -/
  coefficient_coherent : ∀ p hp T, (dataAt p hp).C T = coefficient T
  /-- ⚠ PLACEHOLDER (Unit 1, the realness gates): the models count genuine
  monic degree-`n` ℤ_p-boxes. While this field is `True`, NO proof unit may
  target the theorems below (an abstract family with non-rational
  `coefficient` defeats them); the gates unit replaces this with the
  `GenuineZpCounting` predicate + the same-prime uniqueness theorem. -/
  faithfulAt : True
```

Meaning: one coherent p-indexed bundle — the object over which "one rational law" is well-posed. Status per review: **implements D1** (quantifier-order fix; `p.Prime` landed per D1's "Also put `p.Prime` in the realness data" — rev 1 assumed only `1 < q`). Field-level status:
- `modelAt`, `dataAt` — general-prime analogues of the capstone's `realM2`/`realD2` (`OM/RealInstanceV2.lean`). Adequate as data slots; realness unpinned until `faithfulAt` is real.
- `menu`, `shapes_coherent` — the shared-menu coherence; p-independence of the menu is L5fix/GMN termination content; the certified informal menu suppliers are the W-11/HEX3/HMENU3 notes (see §3).
- `coefficient`, `coefficient_coherent` — the shared coefficient; its rationality-in-q is deliberately NOT a field (docstring: "the cross-prime coefficient-uniformity theorem (review D6), NOT a field") — but note per F1 that the interface *already* forces it via any prime's `C_isRational`, so D6's genuine content is about the *canonical* coefficient of the real construction, not about this abstract family.
- `faithfulAt : True` — **THE placeholder** (Unit 1; leansimp migration step 5: replace with a concrete predicate covering actual monic ℤ_p boxes, certified type, partition, refinement; safety = non-vacuity witness, σ-separation witness, same-prime uniqueness theorem, rejection tests for degenerate empty-menu models). Its docstring's defeat-mechanism sentence is imprecise (F1).

### 2.2 `CountingModel` — `lean/LeanUrat/CountingModel.lean:95` (fields verbatim, docstrings elided)

```lean
structure CountingModel (q n : ℕ) where
  hq : 2 ≤ q
  decidedCount : FactorizationType → ℕ → ℚ
  undecidedCount : ℕ → ℚ
  decidedCount_nonneg : ∀ σ N, 0 ≤ decidedCount σ N
  undecidedCount_nonneg : ∀ N, 0 ≤ undecidedCount N
  typeMenu : Finset FactorizationType
  typeMenu_degree : ∀ σ ∈ typeMenu, σ.degree = n
  decidedCount_off_menu : ∀ σ N, σ ∉ typeMenu → decidedCount σ N = 0
  box_partition : ∀ N, (∑ σ ∈ typeMenu, decidedCount σ N) + undecidedCount N = (q : ℚ) ^ (n * N)
  decided_mono : ∀ σ, Monotone (fun N => decidedCount σ N / (q : ℚ) ^ (n * N))
  densityVal : FactorizationType → ℚ
  decided_tendsto : ∀ σ, Filter.Tendsto (fun N => decidedCount σ N / (q : ℚ) ^ (n * N))
    Filter.atTop (nhds (densityVal σ))
  upper_tail : ∀ (σ : FactorizationType) (N K : ℕ), N ≤ K →
    decidedCount σ K / (q : ℚ) ^ (n * K)
      ≤ decidedCount σ N / (q : ℚ) ^ (n * N) + undecidedCount N / (q : ℚ) ^ (n * N)
```

Meaning: the level-N DECIDED-count semantics — `decidedCount σ N` = #cosets mod p^N whose type σ is Hensel/Newton-certified; `undecidedCount N` = #cosets not yet decided; `box_partition` places the box count q^(nN) as the partition TOTAL (never a per-type density — the anti-box care point); `decided_mono` + `decided_tendsto` make the density the decided limit; `upper_tail` is the honest per-level content of `lem:countHaar`. Adequacy per review:
- **`densityVal : FactorizationType → ℚ` = D7's complaint.** Carrying the limit as ℚ-valued *data* assumes every individual limit already lands in ℚ, "although rationality is advertised as an eventual theorem". (The module's own docstring defends this — ℚ has no `SupSet`, and the field is *constrained* by `decided_tendsto` — but D7's point stands: for new Stage-2 code, split `FiniteCountingModel` / `HasDecidedLimit` / `UndecidedVanishes` / rationality-as-theorem, keeping `CountingModel` as a compatibility adapter. Note the D7 defect *compounds* F1: interface-carried rationality is part of why the anchor is abstractly provable.)
- **`decidedCount`, `undecidedCount : … → ℚ` = D10's complaint.** Counts should be ℕ with conversion at normalization boundaries; ℚ-valued counts permit nonintegral "counting models" and weaken faithfulness gates.
- Directory verdict: REDESIGN — "Keep a compatibility facade, but separate finite counts, convergence, drainage, and cross-prime family semantics."

### 2.3 `CountingModel.countingDensity` — `lean/LeanUrat/CountingModel.lean:235` (verbatim, docstring elided)

```lean
noncomputable def countingDensity (σ : FactorizationType) : ℚ := M.densityVal σ
```

Meaning: THE density = the decided limit (pinned as the genuine N→∞ limit by `decided_tendsto`, re-exposed as `density_isLimit`; never the box count — `box_is_total_not_density`). Status: definitionally just the carried `densityVal`, so it inherits D7's status. Supporting proved API consumed by the anchor's rationale (statements only): `decidedMeasure σ N := M.decidedCount σ N / (q : ℚ) ^ (n * N)`, `undecided N := M.undecidedCount N / (q : ℚ) ^ (n * N)`, the bracket theorems `decided_le_density` / `density_le_decided_add_undecided`, and

```lean
def UndecidedVanishes {q n : ℕ} (M : CountingModel q n) : Prop :=
  Filter.Tendsto M.undecided Filter.atTop (nhds 0)
```

— which is exactly the exhaustive target's inline drainage hypothesis, unfolded. (D9: this predicate never connects to a distinct full-density object; see §3.4.)

### 2.4 `MontesDataV2` — `lean/LeanUrat/MontesV2.lean:66` (fields verbatim, docstrings elided)

```lean
structure MontesDataV2 (q n : ℕ) (M : CountingModel q n) where
  shapesOf : FactorizationType → Finset ClusterShape
  stratumCount : ClusterShape → ℕ → ℚ
  partition : ∀ (σ : FactorizationType) (N : ℕ),
    M.decidedCount σ N = ∑ T ∈ shapesOf σ, stratumCount T N
  C : ClusterShape → ℕ → ℚ
  C_isRational : ∀ T : ClusterShape, IsRationalFn (fun q' => C T q')
  stratum_tendsto_C : ∀ (σ : FactorizationType), ∀ T ∈ shapesOf σ,
    Filter.Tendsto (fun N => stratumCount T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds (C T q))
```

Meaning: the abstract-coefficient Montes interface (blueprint W1/D2): per-type shape menu, level-N per-shape stratum counts, the partition of the decided count over the menu, an abstract per-shape coefficient `C T q'` with (i) uniform rationality and (ii) the per-shape counting limit at this model's q. Adequacy:
- Its own docstring flags the weakness: "DELIBERATELY WEAK … satisfiable by degenerate instances (e.g. an empty menu with `C ≡ 0`) … semantics are pinned at the INSTANCE … any consumer claiming non-vacuity must cite the instance gates, never this structure." This is exactly the pattern **D11** complains about (omnibus structures whose fields permit degenerate models; replace with raw data + named law predicates: partition / faithfulness / stage laws / cross-prime coherence / drainage).
- **`C_isRational` as a FIELD** means rationality is *assumed* at the interface and is a *theorem* only for the real instance (`OMCountV2.omCount_isRational` at the committed prime). This is the second half of why F1 holds. D6's cross-prime theorem is what would make it earned content at general primes.
- Module verdict: KEEP — "Trusted statements and core-only footprints are immutable" (TRUSTED-FROZEN in the target tree).

The two proved theorems on it that the anchor's coherence rationale invokes (statements verbatim, proofs elided):

```lean
theorem countingDensity_eq_sum_coeff (σ : FactorizationType) :
    M.countingDensity σ = ∑ T ∈ D.shapesOf σ, D.C T q := by ...

theorem countingDensity_isRational (σ : FactorizationType) :
    IsRationalFn (fun q' => ∑ T ∈ D.shapesOf σ, D.C T q') := ...
```

(with `variable {q n : ℕ} {M : CountingModel q n} (D : MontesDataV2 q n M)`; both Lean-core footprint, sorry-free). The first is the V2 decomposition theorem — the "pins each prime's density to the shared data" step of the rev-2 header (miscited there as `countingDensity_eq_sum_C`, F2).

### 2.5 `FactorizationType` — `lean/LeanUrat/Interface.lean:152` (verbatim, docstrings elided)

```lean
structure FactorizationType where
  data : Multiset (ℕ × ℕ)

def FactorizationType.degree (σ : FactorizationType) : ℕ :=
  (σ.data.map (fun p => p.1 * p.2)).sum
```

Meaning: a splitting/factorization type σ of degree n = Σ eᵢfᵢ — the multiset of (ramification, residue-degree) pairs of the irreducible p-adic factors. Status: **the statement grain, signed off 2026-08-11** (bare (e,f)-multiset; finer invariants deferred). Note the structure imposes no positivity on the pairs (e.g. (0,0) entries are legal) — degree-n-ness is imposed only by `hσ`, which per F1 the abstract statements do not currently use. Destination per D5 split: `Core/Factorization.lean`.

### 2.6 `ClusterShape` / `ShapeCell` — `lean/LeanUrat/Interface.lean:178` (mutual; verbatim, docstrings elided)

```lean
mutual
structure ClusterShape where
  tree : List (ℕ × ℕ × ℕ)
  cells : List ShapeCell
structure ShapeCell where
  dS : ℕ
  δ : ℕ
  polygon : L4.LatticePolygon
  children : List ClusterShape
end
```

Meaning: the cluster-tree / OM-type shape index T of the recursion — `tree` is the count-native slot encoding (root `(order, clusterSize, residualDegree)` + concatenated subtrees), `cells` the enriched faithful per-node cell payload (decision 2b, faithful-by-construction decoding to `MontesAxiom.CountCell`; empty for order-0 shells). One type σ is realized by many shapes T; per-type density = menu-sum of per-shape coefficients. `DecidableEq` for both is supplied classically (`Classical.decEq`, noncomputable — legitimate, not an escape hatch). Adequacy: no review defect; D5 destination `Core/ClusterShape.lean`.

### 2.7 `L4.LatticePolygon` — `lean/LeanUrat/L4.lean:59` (verbatim, docstrings elided)

```lean
structure LatticePolygon where
  width : ℕ
  ceilHeights : Fin width → ℕ
  isVertex : Fin width → Bool
```

Meaning: the pure integer-lattice Newton-polygon data (GMN structural fact (II)) — width e, ceiling heights ⌈hᵢ⌉, vertex predicate; p never appears. Leaf of the closure (Fin/Bool are core). No review defect.

### 2.8 `LeanUrat.RatFn.IsRationalFn` — `lean/LeanUrat/RatFn.lean:32` (verbatim)

```lean
def IsRationalFn (f : ℕ → ℚ) : Prop :=
  ∃ num den : Polynomial ℚ, den ≠ 0 ∧
    ∀ q : ℕ, 1 < q → den.eval (q : ℚ) ≠ 0 ∧ f q = num.eval (q : ℚ) / den.eval (q : ℚ)
```

Meaning: "one rational function represents f at every q > 1" — the uniform-rationality predicate. Note its quantifier order is already ∃-before-∀: **this is the interface-level engine that lets the anchor's ∃ (num, den) stand outside ∀ p within one family** (D6's "logical engine that permits `∃ num den` to move outside `∀ p`", here consumed via `C_isRational`). Module verdict: KEEP ("the small stable algebraic output API needed by both V2 and Stage2").

### 2.9 Mathlib/core leaves

`Polynomial ℚ`, `Polynomial.eval`, `Nat.Prime`, `Finset`, `Multiset`, `Monotone`, `Filter.Tendsto`, `Filter.atTop`, `nhds`, `ℚ`, `Fin`, `Bool`, `List`, `True`. All standard; closure stops here.

### 2.10 What is deliberately NOT in the rev-2 closure (scoping wins, each a review decision)

- **`RealInstanceAt`** — rev 1's free per-prime bundle, the carrier of the **quantifier-order defect** (the stop-the-line item: "nothing forces two instances—even at the same q—to have the same density", so ∃-before-∀ was **false as stated**). Deleted from live code; survives only inside the anchor's STATEMENT HISTORY comment, quoted verbatim there as:

  ```lean
  structure RealInstanceAt (q n : ℕ) where
    model : CountingModel q n
    data : MontesDataV2 q n model
    foundation : DensityFoundation
    hbridge : ∀ σ q', 1 < q' → foundation.density n σ q' = ∑ T ∈ data.shapesOf σ, data.C T q'
    faithful : True
  ```

  (rev 1's `faithful : True` is the same placeholder now named `faithfulAt`; rev 1 also assumed only `1 < q` where it "talks about primes" — both fixed per D1.)
- **`DensityFoundation`** and **`TameFunctionalEquation`** (`Interface.lean`) — gone per **D8**: the completed informal proof derives uniform rationality without tame palindromy; the tame FE "was only ever palindromy's carrier, and palindromy was dropped from the target 2026-08-10". Rev 2's statements carry **no** tame hypothesis (unlike the single-prime capstone `montes_unconditional`, whose `htameFE` conditionality remains for its palindromy clause).
- **`IsPalindromic`** — palindromy dropped from the stage-2 targets 2026-08-10 (Asvin directive), so the anchor asks strictly less than `MontesV2.goal_theorem_montes` per prime and strictly more across primes.
- **`OMBridge` / `PadicMeasure.*`** — the measure route; statement-closure-free (module-import caveat F4).

For the record, the single-prime trusted statement being generalized (statement verbatim, proof elided — `lean/LeanUrat/MontesV2.lean:179`, Lean-core footprint, fired by the capstone `OM.RealInstanceV2.montes_unconditional`):

```lean
theorem goal_theorem_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesDataV2 q n M)
    (σ : FactorizationType) (F : DensityFoundation) (hσ : σ.degree = n)
    (hbridge : ∀ q' : ℕ, 1 < q' →
      F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.C T q')
    (htameFE : TameFunctionalEquation F n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ D.shapesOf σ, D.C T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      IsPalindromic num den := by ...
```

---

## 3. THE PROPOSED CORRECTED SHAPE (leansimp D1 / D6 / D8 / D9)

Source: `runs/leansimp_output.log`, "## 2. Design decisions" and "## 3. Target Stage2 module tree". Status key: D1 = **landed** in rev 2 except its `faithfulAt` clause; D6, D8, D9 = **not landed** (proof-side, awaiting units).

### 3.1 D1 — the canonical family (leansimp sketch, verbatim)

```lean
structure RealCountingFamily (n : ℕ) where
  modelAt : ∀ p, p.Prime → CountingModel p n
  menu : FactorizationType → Finset ClusterShape
  coefficient : ClusterShape → ℕ → ℚ
  dataAt : ∀ p hp, MontesDataV2 p n (modelAt p hp)
  shapes_coherent : ...
  coefficient_coherent : ...
  faithfulAt : ∀ p hp, GenuineZpCounting (modelAt p hp)
```

plus the review's prose: "`RealInstanceAt p n` should be a faithful view of this canonical semantics, or should carry a proof that its density equals the canonical model's density. Arbitrary unrelated instances cannot support the anchor's quantifier order." and "Also put `p.Prime` in the realness data."

Annotation, field by field, with the certified informal supplier:
- `modelAt` + `faithfulAt : ∀ p hp, GenuineZpCounting (modelAt p hp)` — genuine monic-ℤ_p-box counting semantics at every prime, with the same-prime uniqueness theorem as safety check. **This is Unit 1** (target module `Stage2/Real/Faithfulness.lean`; migration step 5), the general analogue of `OM/RealInstanceV2Gates.lean`. Rev 2 landed everything except this clause: `faithfulAt : True` is the one placeholder standing between the signed statements and content (F1).
- `menu` + `shapes_coherent` — one shape menu for all primes. p-independence of the menu is L5fix/GMN-termination content; the certified informal suppliers are the **W-11 / HEX3 / HMENU3** menu notes (annex mapping: `HMENU3`, `HEX3`, `GENIND` → `Induction/*`; `W11` → gauge/tower transport support), with the finite-genre stage laws (`GENHN` → `StageLaws/*`) feeding the per-stage menus.
- `coefficient` + `coefficient_coherent` — one per-shape coefficient function C T(q) for all primes; its rationality is D6's theorem (below), **not** a field.
- `dataAt` — per-prime Montes data: stratum counts + `partition` (ax:partition) + the per-shape limits (`stratum_tendsto_C`, the general `hNodeLimit` legs), the general analogue of the capstone's `realD2`.

### 3.2 D6 — the cross-prime coefficient theorem (leansimp sketch, verbatim)

```lean
theorem coefficient_uniform
    (n) (T : ClusterShape) :
    IsRationalFn (fun p => canonicalCoefficient n T p)
```

with the review's prose: "`MontesDataV2.C_isRational` is local to one arbitrary `D`. It does not show that different primes or different instances use the same `C`, menu, or rational representative. … together with menu independence and a per-prime value tie. This is the logical engine that permits `∃ num den` to move outside `∀ p`."

Annotation: `canonicalCoefficient n T p` is the **canonical** (real, genuine-counting) per-shape coefficient — the general-prime analogue of the capstone's `omCount`, whose single-prime rationality is `OMCountV2.omCount_isRational`. The theorem says: one rational representative in ℚ(t) works at **all** primes, for the real coefficient. Certified informal supplier: **W-12.D corrected (A1)** — the corrected cross-prime coefficient-uniformity result of the 26-note corpus (target module `Stage2/Assembly/CoefficientUniformity.lean`; Unit 4 → `Stage2/Reduction/W12.lean`; migration step 13, whose safety line restates the quantifier discipline: "theorem must quantify `p` after choosing the rational representative; test two different faithful presentations at the same prime"). Scoping note per F1: rev 2's abstract interface already forces `IsRationalFn (F.coefficient T)` formally; D6's non-trivial content is entirely that the **canonical real** coefficient satisfies it — i.e. D6 is a theorem about the real construction, and it is what makes instantiating `RealCountingFamily` at the real semantics possible at all.

### 3.3 D8 — the core theorem without tame palindromy (leansimp sketch, verbatim)

```lean
uniformity_core : ∃ num den, ...
```

with the review's prose: "The completed target asks only uniform rationality. The tame functional equation was needed by `MontesV2.goal_theorem_montes` to transfer palindromy; Stage2 explicitly dropped palindromy. Therefore prove [`uniformity_core`] directly from the five-node counting proof, without `DensityFoundation` or `TameFunctionalEquation`. Then derive the signed `uniformity_target` by accepting and ignoring its legacy `TameFunctionalEquation` hypothesis. This preserves the signed statement while deleting a major proof dependency."

Annotation and status: the second half is now **moot in the best way** — rev 2's signed statements already carry no `TameFunctionalEquation` hypothesis (the review's D8 was folded into the statement itself, per the anchor header "Per review D8, no tame-functional-equation hypothesis appears"). What remains of D8 is its first half: `uniformity_core` = the decided-density law proved **directly from the five-node counting proof** (Reduction / Induction / StageLaws / Ladder / Towers, per D3) against the canonical real family — the informal complete proof (the certified 26-note corpus) derives uniform rationality without the tame FE, which "was only ever palindromy's carrier". Target module: `Stage2/Assembly/DecidedUniformity.lean`; migration step 14 ("Prove `uniformity_core`, then discharge the signed anchors … remove both Stage2 sorries; Stage2 trusted closure contains no `sorryAx`").

### 3.4 D9 — a formal full-density object (leansimp sketch, verbatim)

```lean
UndecidedVanishes M →
fullDensity M σ = M.countingDensity σ
```

with the review's prose: "`uniformity_target_exhaustive` currently concludes the same `countingDensity` equality as the decided theorem. Its drainage hypothesis does not connect to a distinct full-density symbol. Add a counting-native `fullDensity` or a `GenuineDensity` semantic relation … Keep the signed exhaustive theorem as a compatibility corollary, and add a genuinely full-density theorem whose conclusion mentions the full density."

Annotation: `fullDensity M σ` is the to-be-defined genuine (not merely decided-limit) density; the law says decided = full **under drainage**. The drainage hypothesis is exactly the anchor's inline `Tendsto` = `UndecidedVanishes` = the general `hExhaust` of `montes_unconditional_exhaustive`; its certified informal supplier is the **drainage/exhaustiveness** leg of the corpus — GENHN-HE exhaustiveness (Unit 13 → `Stage2/Ladder/Exhaustiveness.lean`; annex `HE3`/`HE6`/`HE7`/`HE6R1_RECON`/`HETOW_RECON` → `Ladder/*`), resting on M1 termination (`lem:countHaar`: every separable f resolves at finite OM order). Status: **not landed** — rev 2's exhaustive target still concludes `countingDensity`, and F1 upgraded D9's complaint to a machine-checked fact (the hypothesis is discardable as stated). Target modules: `Stage2/Assembly/FullUniformity.lean` + `Counting/Drainage.lean`; migration step 15's safety line is the acceptance test: "ensure the drainage hypothesis occurs in a necessary value-tie theorem, not merely as an unused argument."

### 3.5 Where the corrected shape lives (leansimp "## 3. Target Stage2 module tree", verbatim)

```text
LeanUrat/
├── Core/
│   ├── Factorization.lean
│   ├── ClusterShape.lean
│   └── RationalLaw.lean
├── Counting/
│   ├── FiniteModel.lean
│   ├── Normalized.lean
│   ├── Limit.lean
│   ├── Drainage.lean
│   └── PrimeFamily.lean
├── Gauge/
│   ├── Defs.lean
│   ├── Cocycle.lean
│   └── Transport.lean
├── Stage2/
│   ├── Real/
│   │   ├── Semantics.lean
│   │   ├── InstanceAt.lean
│   │   └── Faithfulness.lean
│   ├── Reduction/
│   │   ├── MenuBound.lean
│   │   └── W12.lean
│   ├── Induction/
│   │   ├── Species.lean
│   │   └── TwoSpecies.lean
│   ├── StageLaws/
│   │   ├── FiniteGenres.lean
│   │   └── OrderOne.lean
│   ├── Ladder/
│   │   ├── Base.lean
│   │   ├── FractionalKeys.lean
│   │   ├── StrictDescent.lean
│   │   └── Exhaustiveness.lean
│   ├── Towers/
│   │   ├── Budgets.lean
│   │   ├── Windows.lean
│   │   ├── TwistedTransport.lean
│   │   └── Cap.lean
│   ├── Assembly/
│   │   ├── CoefficientUniformity.lean
│   │   ├── DecidedUniformity.lean
│   │   └── FullUniformity.lean
│   └── UniformityTarget.lean
├── Interface.lean                 [TRUSTED-FROZEN facade]
├── CountingModel.lean             [TRUSTED-FROZEN facade]
├── MontesV2.lean                  [TRUSTED-FROZEN]
└── OM/
    ├── OMCountV2.lean             [TRUSTED-FROZEN]
    ├── RealInstanceV2Prep.lean    [TRUSTED-FROZEN]
    ├── RealInstanceV2Gates.lean   [TRUSTED-FROZEN]
    └── RealInstanceV2.lean        [TRUSTED CAPSTONE]
```

with the review's closing rule: "The new Stage2 graph becomes trusted only after it is sorry-free and its footprint is pinned." The D7/D10/D11 remediations (counting split; ℕ counts; data-plus-named-law-predicates) live in `Counting/*` and `Core/*` behind the frozen facades (D12: statement bytes and axiom output of kept declarations must not change; every kept declaration receives a ledger hash).

---

**Bottom line for sign-off.** The signed rev-2 statements are the right *shape* (one family → one law → all primes, tame-free, decided + drainage-gated variants) and fix rev 1's falsity. But as signed they are machine-checkably provable from the abstract interface alone (F1) — with `hn`/`hσ` idle and the drainage hypothesis idle — so the entire theorem-content burden sits on three not-yet-landed pieces: `faithfulAt` → `GenuineZpCounting` (Unit 1), `coefficient_uniform` for the canonical coefficient (D6 = W-12.D corrected (A1)), and the `fullDensity` object with a necessary drainage tie (D9). The sign-off decision is whether to (a) keep the current statements as fenced anchors and let Unit 1 + D6 + D9 make their eventual proofs contentful, or (b) restate now so that provability itself certifies content (e.g. the capstone becomes the construction/existence of the canonical real family plus `uniformity_core` over it). Small mandatory fixes at next revision regardless: the `countingDensity_eq_sum_C` miscite (F2) and the incorrect defeat-mechanism sentence in the `faithfulAt` fence (F1.2).
