# UNIT NOTE — the genuine density (Part 1 of `leanfinal/Uniformity`), 2026-08-13

**Charge.** Asvin, 2026-08-13: *"get the scaffolding right where we define the density
correctly in lean (taking as inputs the prime, the local ring (Z_p or an extension), the
splitting type) and outputting the density as a limit. This will be the input to the main
theorem, the thing we prove is evaluated by a rational function with the size of the local
field as an input"* — plus the verification target *"check if using the definitions to compute
the densities for n=2 or 3 works out as expected."*

**What landed.** Five Lean files under `Uniformity/Density/` (1 439 lines, **zero `sorry`s,
zero axioms beyond Lean core**), one Python cross-check, this note. The old `lean/` tree
(LeanUrat) was **not touched**: nothing was created or modified there. Two declarations
(`FactorizationType`, `FactorizationType.degree`) are verbatim quarry copies, marked as such
at the declaration site.

| file | lines | content |
|---|---|---|
| `Uniformity/Density/LocalData.lean` | 351 | the local base bundle, `residueCard`, level-`N` boxes, `#(O/𝔪^N) = q^N`, `ℤ_[p]` instance |
| `Uniformity/Density/TypeOf.lean` | 294 | monic factorization in `O[X]`; `(e,f)` by the norm form of the valuation; `typeOf` |
| `Uniformity/Density/GenuineDensity.lean` | 396 | `decidedSeq`/`possibleSeq`, monotone/antitone, **the density as a proved limit**, sandwich, drainage tie, total mass ≤ 1 |
| `Uniformity/Density/Statement.lean` | 73 | `UniformityStatement`, `UniformityStatementPadic` (capstone targets, ⚠ pending sign-off) |
| `Uniformity/Density/Gates.lean` | 325 | G1–G4 + the `#print axioms` block |
| `verification/genuine_density_check.py` | 163 | exact `n = 2` enumeration over `ℤ_p`, `p ∈ {2,3,5}`, vs the W-11 closed forms |

---

## 1. THE INFORMAL ARGUMENT (written before the Lean)

Fix a complete DVR `O` with maximal ideal 𝔪, finite residue field of size `q`, degree `n`, and
a splitting type σ (a multiset of `(e,f)` pairs). A monic degree-`n` polynomial over `O` is a
coefficient vector `a ∈ O^n`. Truncating the coefficients mod 𝔪^N cuts `O^n` into `q^(nN)`
equal-Haar-measure boxes ("classes"). Call a class **σ-decided** when *every* polynomial in it
has splitting type σ. Then

* refining a decided class keeps it decided (the ∀ over lifts only shrinks), so the decided
  proportion `D_σ(N)/q^(nN)` is **nondecreasing** in `N`; it is `≤ 1`; hence it converges, and
  its limit is the honest density of the type-σ locus **from inside**;
* dually, calling a class **σ-possible** when *some* member has type σ, the possible
  proportion is **nonincreasing** and bounds the locus **from outside**;
* the two brackets sandwich the true measure. If the gap drains to 0 the bracket closes and the
  decided limit *is* the density. Without drainage, `genuineDensity` is a certified lower
  bound and `upperDensity` a certified upper bound — that is the honest state of affairs and
  exactly what the Lean says.

`q` is the only numerical input; nothing else in the construction sees the prime. That is why
"one rational function of `q`, all local fields at once" is even a well-posed statement.

---

## 2. EVERY NEW DEFINITION, VERBATIM, WITH ITS FAITHFULNESS PARAGRAPH

Definitions are the trust boundary: Lean checks proofs, not statements. Each item below is
flagged for human review.

### 2.1 The local base

```lean
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

noncomputable def residueCard : ℕ := Nat.card (ResidueField O)

abbrev Res (N : ℕ) : Type _ := O ⧸ (maximalIdeal O) ^ N

abbrev Coeff (n N : ℕ) : Type _ := Fin n → Res O N

def proj (n N : ℕ) (a : Fin n → O) : Coeff O n N := fun i => Ideal.Quotient.mk _ (a i)

noncomputable def monicPoly {n : ℕ} (a : Fin n → O) : Polynomial O :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)
```

**Faithfulness.** The bundle is the standard axiomatisation of "the ring of integers of a
non-archimedean local field": a complete DVR with finite residue field. It is *not*
`ℤ_[p]`-specific — `ℤ_[p]` is proved to be an instance (`residueCard_padicInt : residueCard
ℤ_[p] = p`), and any unramified/ramified extension or `𝔽_q⟦t⟧` qualifies once its instances
are supplied. `residueCard O` is the `q` of the theorem. `monicPoly` is a bijection between
`O^n` and monic degree-`n` polynomials (`monicPoly_monic`, `monicPoly_natDegree` proved;
surjectivity onto monics is not needed and not claimed). *Design choices flagged:* (i)
completeness is spelled `IsAdicComplete (maximalIdeal O) O` rather than via a topology or the
`IsNonarchimedeanLocalField` class (which is field-side and needs `ValuativeRel` — heavier, and
`ℚ_[p]` has no `ValuativeRel` instance at this mathlib rev); (ii) `Res O 0` is the zero ring, so
level 0 is a single class — deliberate, and harmless because the sequence is monotone.

Proved here: `Finite (Res O N)`, `2 ≤ residueCard O`, and

```lean
theorem card_res (N : ℕ) : Nat.card (Res O N) = residueCard O ^ N
theorem card_coeff (n N : ℕ) : Nat.card (Coeff O n N) = residueCard O ^ (n * N)
```

so the denominator `q^(n·N)` in the density really is the box count, not a convention.
(`card_res` is proved by induction: the kernel of `O/𝔪^(N+1) → O/𝔪^N` is the image of `𝔪^N`,
and multiplication by `π^N` identifies it with the residue field.)

### 2.2 `typeOf` — the splitting type, engine-free

```lean
noncomputable def monicize (g : Polynomial O) : Polynomial O :=
  C (Ring.inverse g.leadingCoeff) * g

def IsMonicFactorization (f : Polynomial O) (F : Multiset (Polynomial O)) : Prop :=
  (∀ g ∈ F, g.Monic ∧ Irreducible g) ∧ F.prod = f

noncomputable def monicFactors (f : Polynomial O) : Multiset (Polynomial O) :=
  open Classical in
  if h : ∃ F, IsMonicFactorization f F then h.choose else 0

def normValues (g : Polynomial O) : Set ℕ :=
  {k : ℕ | 0 < k ∧ ∃ x : AdjoinRoot g, x ≠ 0 ∧
    IsDiscreteValuationRing.addVal O (Algebra.norm O x) = (k : ℕ∞)}

noncomputable def inertiaDegOf (g : Polynomial O) : ℕ := sInf (normValues g)
noncomputable def ramIndexOf  (g : Polynomial O) : ℕ := g.natDegree / inertiaDegOf g
noncomputable def efPair      (g : Polynomial O) : ℕ × ℕ := (ramIndexOf g, inertiaDegOf g)

noncomputable def typeOf (f : Polynomial O) : FactorizationType :=
  ⟨(monicFactors f).map efPair⟩
```

**Faithfulness — layer 1 (the factorization).** `O` is a PID, so `O[X]` is a UFD; a monic `f`
factors into monic irreducibles (`monicFactorization_exists`, proved) and the multiset of
factors is **unique** (`monicFactorization_unique`, proved: two monic associates are equal).
So `monicFactors f` is the classical multiset of monic irreducible factors *with
multiplicity*, and `Classical.choose` introduces no ambiguity. Junk convention: for non-monic
`f` the value is `0`; every use site supplies `monicPoly a`, which is monic.

**Faithfulness — layer 2 (the `(e,f)` pair). READ THIS ONE CAREFULLY.** Let `g` be monic
irreducible of degree `d`, `K = Frac O`, `L = K[x]/(g)`, `A = O[x]/(g) = AdjoinRoot g` (free of
rank `d` over `O`). Because `O` is **complete**, the valuation `v` of `O` extends *uniquely* to
`L`, by the norm form `w(x) = v(N_{L/K}(x))/d`. Writing `e`, `f` for the ramification index and
residue degree (`e·f = d`), the value group of `w` is `(1/e)·ℤ`, hence

  `{ v(N_{L/K}(x)) : x ∈ L^× } = d·w(L^×) = (d/e)·ℤ = f·ℤ`,

and the values realised by the *integral* `x ∈ A \ {0}` are exactly `f·ℕ`. So `f` is the least
strictly positive `v(N(x))` — which is `inertiaDegOf g` — and `e = d/f`. Three checks against
familiar cases: `g = X − a` gives `A ≅ O`, `N(π) = π`, least value `1`, so `(e,f) = (1,1)`
(this one is **proved in Lean**, `efPair_of_natDegree_one`); `g = X² − π` (Eisenstein) gives
`N(√π) = −π`, value `1`, so `(e,f) = (2,1)`; `g` with `ḡ` irreducible gives all norms of even
valuation, least value `2`, so `(e,f) = (1,2)`.

*Why not the `Ideal.ramificationIdx`/`inertiaDeg` route:* it needs the integral closure `S` of
`O` in `L` together with a proof that `S` is local, and the composite `Algebra O L` instance;
neither is available off the shelf at mathlib v4.31.0. *Why not `O[x]/(g)` itself:* its residue
field is **not** the residue field of `L` in general — counterexample checked by hand,
`L = ℚ_p(ζ, √p)` with generator `α = ζ√p` has minimal polynomial `X⁴ − t p X² + n p²`, whose
reduction is `X⁴`, giving residue degree 1 instead of the true `f = 2`.

*Design choices flagged:* (a) the pair is `(e, f)` in that order, matching
`FactorizationType.degree = ∑ eᵢ·fᵢ`; (b) multiplicity is kept (a repeated factor contributes
twice); (c) no separability hypothesis — inseparable/degenerate `f` still get a value, and they
are never σ-decided at any finite level, so they cannot pollute a density; (d) the definition is
*total* (`Algebra.norm` and `sInf` are total), so no instance obligation leaks into it.

*Known gap (see STATUS):* `(typeOf f).degree = f.natDegree` is **not proved in general** — it
needs `inertiaDegOf g ∣ g.natDegree`, i.e. the uniqueness-of-extension theorem. It is proved at
degree 1 (`typeOf_degree_one`), and at degree 2 the weaker fact actually used is proved
(`inertiaDegOf g ≤ 2`, hence `efPair g ∈ {(2,1),(1,2)}`, inside
`typeOf_monicPoly_two_ne_linType`).

### 2.3 The density

```lean
def DecidedAt (n : ℕ) (σ : FactorizationType) (N : ℕ) (c : Coeff O n N) : Prop :=
  ∀ a : Fin n → O, proj O n N a = c → typeOf (monicPoly a) = σ

def PossibleAt (n : ℕ) (σ : FactorizationType) (N : ℕ) (c : Coeff O n N) : Prop :=
  ∃ a : Fin n → O, proj O n N a = c ∧ typeOf (monicPoly a) = σ

noncomputable def decidedCount (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℕ :=
  Nat.card (decidedSet O n σ N)

noncomputable def decidedSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℝ :=
  (decidedCount O n σ N : ℝ) / (residueCard O : ℝ) ^ (n * N)

noncomputable def possibleSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℝ :=
  (possibleCount O n σ N : ℝ) / (residueCard O : ℝ) ^ (n * N)

noncomputable def genuineDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
  ⨆ N, decidedSeq O n σ N

noncomputable def upperDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
  ⨅ N, possibleSeq O n σ N

noncomputable def gapSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℝ :=
  possibleSeq O n σ N - decidedSeq O n σ N

def UndecidedVanishes (n : ℕ) (σ : FactorizationType) : Prop :=
  Tendsto (gapSeq O n σ) atTop (𝓝 0)
```

**Faithfulness.** The counts are honest `ℕ`s (defect D10 of the old design fixed); the
sequences are `ℝ`-valued; the density is a `⨆`, and the fact that it is the `N → ∞` limit is a
**theorem**, not a field:

```lean
theorem decidedSeq_tendsto  : Tendsto (decidedSeq  O n σ) atTop (𝓝 (genuineDensity O n σ))
theorem possibleSeq_tendsto : Tendsto (possibleSeq O n σ) atTop (𝓝 (upperDensity   O n σ))
```

(defect D7 — "ℚ-valued `densityVal` carried as data" — fixed). Decidedness is not vacuous:
`proj` is surjective, so every class has lifts, hence a decided class is possible
(`decided_imp_possible`) and no class is decided for two distinct types
(`decidedSet_disjoint`).

**Faithfulness of `UndecidedVanishes` (defect D9).** The drainage hypothesis is tied to a
genuinely different object and does real work:

```lean
theorem genuineDensity_le_upperDensity : genuineDensity O n σ ≤ upperDensity O n σ
theorem upperDensity_eq_of_drainage (h : UndecidedVanishes O n σ) :
    upperDensity O n σ = genuineDensity O n σ
theorem drainage_of_upperDensity_eq (h : upperDensity O n σ = genuineDensity O n σ) :
    UndecidedVanishes O n σ
```

The converse direction is the point: `UndecidedVanishes` is *exactly* the statement that the
bracket closes, so it can never be a decorative hypothesis here.

*Design choice flagged:* the gap is taken **per σ** (`possibleSeq σ − decidedSeq σ`) rather
than globally (`1 − ∑_σ decidedSeq σ`), because the global form needs a finite menu of types,
which is downstream content. The global inequality that gates need is proved separately:
`sum_genuineDensity_le_one : ∑ σ ∈ S, genuineDensity O n σ ≤ 1` for any finite `S`, and its
consequence `genuineDensity_le_of_others`.

### 2.4 The capstone targets (⚠ PENDING ASVIN'S SIGN-OFF)

```lean
def UniformityStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

def UniformityStatementPadic : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        den.eval (p : ℚ) ≠ 0 ∧
          genuineDensity ℤ_[p] n σ = ((num.eval (p : ℚ) / den.eval (p : ℚ) : ℚ) : ℝ)

theorem UniformityStatement.toPadic (h : UniformityStatement) : UniformityStatementPadic
```

These are `Prop` **definitions**, not sorried theorems (this repo carries zero `sorry`s). The
`∃ (num, den)` stands outside the `∀ O`: that ∃-before-∀ order *is* the uniformity claim. The
statement cannot be satisfied vacuously — `genuineDensity` is the Part-1 limit, not an
abstract model's carried value, so the F1 accident of the old `Stage2/UniformityTarget.lean`
(both anchors provable in ~20 lines with a Lean-core footprint) is structurally impossible
here.

**Four points for your sign-off.** (i) The `∀ O` is over `Type` (universe 0). `ℤ_[p]` and every
concrete local ring live there; a universe-polymorphic version would need the `Prop` to be
universe-polymorphic too. (ii) The rational function is evaluated at `(q : ℚ)` and the equality
is read in `ℝ` via the coercion. (iii) `den.eval q ≠ 0` is demanded per-`O`, not globally
(matching the signed rev-2 shape). (iv) `σ.degree = n` currently does no work, because
`typeOf_degree` is open (§ STATUS); once that lands, off-degree σ are automatically density-0
and the hypothesis becomes live.

---

## 3. GATE RESULTS

All gates hold for an **arbitrary** complete DVR with finite residue field, not just `ℤ_[2]`.

| gate | statement | status | expected (W-11) |
|---|---|---|---|
| **G1** `genuineDensity_linear_eq_one` | `genuineDensity O 1 ⟨{(1,1)}⟩ = 1` | **EXACT, proved** | 1 (every monic linear splits) ✓ |
| **G1′** `genuineDensity_one_of_ne` | `σ ≠ ⟨{(1,1)}⟩ → genuineDensity O 1 σ = 0` | **EXACT, proved** | 0 ✓ |
| **G1″** `gate_sigma_separation_one` | `genuineDensity O 1 linType ≠ genuineDensity O 1 splitType` | **EXACT, proved** | `1 ≠ 0` ✓ |
| **G2** `typeOf_mul_linear` | `typeOf ((X−C r)(X−C s)) = ⟨{(1,1),(1,1)}⟩` | proved | the split type ✓ |
| **G3** `gate_split_lower` | `1/q² ≤ genuineDensity O 2 splitType` | **BOUND (one-sided), proved** | `q/(2(q+1))`; at `q=2`: `1/4 ≤ 1/3` ✓; `q=3`: `1/9 ≤ 3/8` ✓; `q=5`: `1/25 ≤ 5/12` ✓ |
| **G3′** `gate_padic_two` | `1/4 ≤ genuineDensity ℤ_[2] 2 splitType` | **BOUND, proved** | `1/3` ✓ |
| **G4** `genuineDensity_two_linType_eq_zero` | `genuineDensity O 2 ⟨{(1,1)}⟩ = 0` | **EXACT, proved** | 0 (no quadratic has a degree-1 type) ✓ |
| **G4′** `gate_sigma_separation_two` | `genuineDensity O 2 linType < genuineDensity O 2 splitType` | **proved** | `0 < 1/3` ✓ |

**Exact-vs-bounded, stated plainly.** At `n = 1` the gates are **exact equalities**. At `n = 2`
the split gate is a **one-sided lower bound** (`1/q²`, from a single Hensel-certified level-1
class), and the σ-separation is between a positive density and an exact `0`. There is **no**
two-sided `n = 2` bracket in the landed state, and no exact `n = 2` value — those need the
order-0 census and the inert/ram certificates listed in STATUS. G3's mechanism: Hensel's lemma
applied once at the simple residue root `0` of `X² + a₁X + a₀` with `a₀ ∈ 𝔪`, `a₁` a unit; the
second root is then `−a₁ − r` by an algebraic identity, so the polynomial factors into two
monic linears and G2 applies.

---

## 4. PYTHON CROSS-CHECK (`verification/genuine_density_check.py`)

Exact enumeration of level-`N` decided classes of monic quadratics over `ℤ_p` (the type of a
monic quadratic over `ℤ_p` is a function of `disc = a₁² − 4a₀` alone; a class is decided iff
every refinement's disc forces one and the same type). Compared against the W-11 closed forms
(`lean/notes/openmath/W11_PROOF_2026-08-08.md` clauses (ii)–(iii)): `undecided = q^N` exactly,
`ram = (q^{2N} − q^{2N−2⌊N/2⌋})/(q+1)`, `split = inert = (q^{2N} − q^N − ram)/2`. `amb` counts
undecided classes visibly carrying ≥ 2 distinct types (W-11 clause F6). Run time 1.5 s.

```
--- p = q = 2   (W-11 limits: split = inert = 1/3, ram = 1/3; undecided mass = q^-N) ---
 N      box |    split    inert      ram    undec | W11 split  W11 ram  W11 und | amb | match | decidedSeq(split)
 1        4 |        1        1        0        2 |         1        0        2 |   2 |   YES | 1/4 = 0.250000
 2       16 |        4        4        4        4 |         4        4        4 |   4 |   YES | 1/4 = 0.250000
 3       64 |       20       20       16        8 |        20       16        8 |   8 |   YES | 5/16 = 0.312500
 4      256 |       80       80       80       16 |        80       80       16 |  16 |   YES | 5/16 = 0.312500
    Lean gate `gate_split_lower`: 1/q^2 = 1/4 <= density(split) = 1/3  ->  CONSISTENT

--- p = q = 3   (W-11 limits: split = inert = 3/8, ram = 1/4; undecided mass = q^-N) ---
 N      box |    split    inert      ram    undec | W11 split  W11 ram  W11 und | amb | match | decidedSeq(split)
 1        9 |        3        3        0        3 |         3        0        3 |   3 |   YES | 1/3 = 0.333333
 2       81 |       27       27       18        9 |        27       18        9 |   9 |   YES | 1/3 = 0.333333
 3      729 |      270      270      162       27 |       270      162       27 |  27 |   YES | 10/27 = 0.370370
    Lean gate `gate_split_lower`: 1/q^2 = 1/9 <= density(split) = 3/8  ->  CONSISTENT

--- p = q = 5   (W-11 limits: split = inert = 5/12, ram = 1/6; undecided mass = q^-N) ---
 N      box |    split    inert      ram    undec | W11 split  W11 ram  W11 und | amb | match | decidedSeq(split)
 1       25 |       10       10        0        5 |        10        0        5 |   5 |   YES | 2/5 = 0.400000
 2      625 |      250      250      100       25 |       250      100       25 |  25 |   YES | 2/5 = 0.400000
    Lean gate `gate_split_lower`: 1/q^2 = 1/25 <= density(split) = 5/12  ->  CONSISTENT

ALL CHECKS PASSED
```

**Reading.** Every cell matches W-11 exactly, at three primes including the wild one, at every
level computed — an independent confirmation that the *Lean definition* of `decidedSeq` (all
lifts of a class share a type) is the same object as the corpus's "σ-decided at window `N`".
Note `decidedSeq(split)` climbing `1/4, 1/4, 5/16, 5/16 → 1/3` at `p = 2`: monotone, as
`decidedSeq_mono` requires, and converging to the W-11 limit. `n = 3` was **not** run — there
is no discriminant-only criterion at degree 3, so an exact enumeration needs a genuine
`ℚ_p`-factorization oracle; left as an open verification item.

---

## 5. AXIOM FOOTPRINTS

`lake build` from `leanfinal/` is green (8 565 jobs). The `#print axioms` block at the end of
`Gates.lean` reports, for every one of the following:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

`genuineDensity_linear_eq_one`, `genuineDensity_one_of_ne`, `gate_sigma_separation_one`,
`typeOf_mul_linear`, `typeOf_split_of_unit`, `gate_split_lower`, `gate_padic_two`,
`genuineDensity_two_linType_eq_zero`, `gate_sigma_separation_two`, `decidedSeq_tendsto`,
`possibleSeq_tendsto`, `upperDensity_eq_of_drainage`, `genuineDensity_le_upperDensity`,
`sum_genuineDensity_le_one`, `card_res`, `UniformityStatement.toPadic`.

Lean core only; **no `sorryAx`, no declared axioms**. `grep -rn sorry Uniformity/` returns only
the word inside a docstring.

---

## 6. STATUS

### PROVED (landed, sorry-free)

* the bundle + `ℤ_[p]` instance + `residueCard ℤ_[p] = p`; `#(O/𝔪^N) = q^N`; `#(Coeff) = q^(nN)`;
* fibre-counting for the refinement tower (`card_preimage_coeffFactor`);
* monic factorization in `O[X]`: existence **and** uniqueness;
* `typeOf`; `efPair = (1,1)` and `typeOf = ⟨{(1,1)}⟩` in degree 1;
* `decidedSeq` monotone, `possibleSeq` antitone, both in `[0,1]`, `decidedSeq ≤ possibleSeq`;
* `genuineDensity`/`upperDensity` **are** the limits (`Tendsto`); the sandwich; the drainage
  tie **in both directions**;
* `∑_{σ ∈ S} genuineDensity ≤ 1` and the complement upper bound;
* gates G1–G4 (§3);
* `UniformityStatement → UniformityStatementPadic`.

### STATED IN THIS NOTE, NOT PROVED (open targets, statements preserved)

1. **`typeOf_degree`** — `theorem typeOf_degree {f : Polynomial O} (hf : f.Monic) :
   (typeOf f).degree = f.natDegree`. *Blocked because*: it reduces to `inertiaDegOf g ∣
   g.natDegree` for monic irreducible `g`, which is the statement that the set of norm
   valuations is `f·ℕ` — i.e. uniqueness of the extension of `v` to `L`. mathlib v4.31.0 has no
   usable form of that theorem (the `IsNonarchimedeanLocalField` file is field-side and needs
   `ValuativeRel`; `Valuation.Extension` only defines `HasExtension`). Two routes: (a) prove
   `A = AdjoinRoot g` is local with `𝔪A`-adic completeness and read `f` off `A/𝔪A` for the
   *maximal order* — needs the integral closure; (b) prove `w(x) = v(N x)/d` is a valuation
   directly (the classical Hensel/Newton-polygon argument). **Recommend (b)**, and it is worth a
   dedicated unit — it also unlocks `typeOf` of an irreducible = a singleton `{(e,f)}` with
   `e·f = deg`.
2. **`gate_split_exact`** — `theorem gate_split_level_one : decidedCount O 2 splitType 1 =
   residueCard O - 1`, i.e. *all* `q−1` level-1 classes `(0, unit)` are split-decided, giving
   `(q−1)/q² ≤ genuineDensity O 2 splitType` (W-11's SEP-SPLIT row is exactly `(q−1)/(2q)`,
   and `(q−1)/q²` is its per-centre form). *Blocked only by*: counting `{c : Coeff O 2 1 |
   c 0 = 0 ∧ c 1 ≠ 0}` — needs `Res O 1 ≃ ResidueField O` (from `pow_one`) plus a
   `Fintype`-level count. Purely mechanical; ~40 lines.
3. **`gate_inert_lower`** — `theorem typeOf_inert_of_irreducible_reduction {a : Fin 2 → O}
   (h : Irreducible ((monicPoly a).map (residue O))) : typeOf (monicPoly a) = inertType`.
   *Blocked because*: needs `inertiaDegOf = 2`, i.e. every nonzero `x ∈ A` has even
   `v(N x)` — provable from `A` local with residue field `k[X]/(ḡ)` and the `π`-adic
   decomposition `x = π^k·unit`, ~80 lines.
4. **`gate_ram_lower`** — `theorem typeOf_ram_of_eisenstein {a : Fin 2 → O}
   (h0 : addVal O (a 0) = 1) (h1 : a 1 ∈ maximalIdeal O) : typeOf (monicPoly a) = ramType`.
   *Blocked because*: needs Eisenstein ⇒ irreducible (mathlib has
   `Polynomial.IsEisensteinAt.irreducible`, needs plumbing) and `N(root) = ±a₀` (candidate:
   `PowerBasis.norm_gen_eq_coeff_zero_minpoly`). This is the **cheapest** of the three and the
   one that would give a genuine two-sided `n = 2` bracket when combined with 2 and 3 via
   `genuineDensity_le_of_others`.
5. **`drainage_two`** — `theorem drainage_at_two : UndecidedVanishes O 2 σ`, the Lean form of
   W-11 clause (iii) (`undecided = q^{−N}` exactly). Needs the full `n = 2` census.
6. **`n = 3` Python check** — needs a `ℚ_p`-factorization oracle (the quarry's
   `verification/quartic_oracle.py` uses PARI `factorpadic`; cypari2 was not available in this
   session's environment and was not installed).

### NOT BLOCKED, JUST NOT IN SCOPE

Design point **E** of the original charge (`GenuineZpCounting` over `CountingModel`) was
dropped by Asvin's 2026-08-13 redirect: there is no `CountingModel` in this repo, and its role
— "the model's counts are the genuine ones" — is now discharged by construction, because the
capstone statement quantifies over `genuineDensity` itself.

---

## 7. WHAT THE FOLLOW-UP UNITS NEED FROM THIS ONE

* **The menu unit** consumes `decidedSet`/`decidedCount` and must produce, for each `(n, σ)`, a
  finite family of *shapes* whose counts sum to `decidedCount`. The interface it should target
  is `decidedCount O n σ N = ∑ T ∈ menu σ, stratumCount T N`, with `menu` independent of `O`.
* **The rationality unit** consumes `genuineDensity` and `residueCard` and must produce
  `num, den : Polynomial ℚ` with the Statement's ∃-before-∀ shape. Note `card_res` is what
  licenses writing the denominator as `q^(nN)`.
* **The drainage unit** should target `UndecidedVanishes O n σ` as defined here; the tie
  theorem is already available in both directions, so drainage buys exactly
  `upperDensity = genuineDensity` and nothing has to be re-stated.
* **`typeOf_degree` (open item 1) is on the critical path** for making `σ.degree = n` do work in
  the capstone; recommend it as the next standalone unit, before any menu authoring.
