# UNIT NOTE — the genuine density (Part 1 of `leanfinal/Uniformity`), 2026-08-13

> 🔁 **READ §8 FIRST IF YOU KNEW THIS FILE BEFORE 2026-08-13 EVENING.** Unit **UNIFORMITY-P4**
> moved the name `genuineDensity` from the *decided* limit to the *consistent-class* limit, on
> Asvin's Q5 instruction. Everything in §§1–7 has been mechanically re-keyed to the new names
> and describes the current code; §8 is the rename map, the re-keyed theorem list, and the
> honest status of `Σ_σ R_σ = 1`. **In one line:** `genuineDensity = ⨅_N possibleSeq` (THE
> density), `decidedDensity = ⨆_N decidedSeq` (the certified inner one), equal by theorem at
> `n = 1` and `n = 2`, so no number changed.

**Charge.** Asvin, 2026-08-13: *"get the scaffolding right where we define the density
correctly in lean (taking as inputs the prime, the local ring (Z_p or an extension), the
splitting type) and outputting the density as a limit. This will be the input to the main
theorem, the thing we prove is evaluated by a rational function with the size of the local
field as an input"* — plus the verification target *"check if using the definitions to compute
the densities for n=2 or 3 works out as expected."*

**What landed.** Seven Lean files under `Uniformity/Density/` (3 184 lines, **zero `sorry`s,
zero axioms beyond Lean core**), two Python cross-checks, this note. *(Updated 2026-08-13,
follow-up unit: STATUS items 2–4 discharged — see §3 and §6. Updated again 2026-08-13, unit
**UNIFORMITY-P2**: the `n = 2` DRAINAGE THEOREM for arbitrary `O` — §3B, gates G9–G14 — plus a
**faithfulness defect found and fixed in `typeOf`**, see the correction box in §2.2, and STATUS
items 1 and 5 discharged. Updated a third time 2026-08-13, unit **UNIFORMITY-P4**: the
`genuineDensity` REWIRE — §8.)* The old `lean/` tree (LeanUrat) was **not touched**: nothing was
created or modified there. Two declarations (`FactorizationType`, `FactorizationType.degree`)
are verbatim quarry copies, marked as such at the declaration site.

| file | lines | content |
|---|---|---|
| `Uniformity/Density/LocalData.lean` | 351 | the local base bundle, `residueCard`, level-`N` boxes, `#(O/𝔪^N) = q^N`, `ℤ_[p]` instance |
| `Uniformity/Density/TypeOf.lean` | 390 | monic factorization in `O[X]`; `(e,f)` by the norm form of the valuation; `typeOf` |
| `Uniformity/Density/GenuineDensity.lean` | 532 | `decidedSeq`/`possibleSeq`, monotone/antitone, **both densities as proved limits**, sandwich, drainage tie, total mass ≤ 1, *(P4)* covering menus + `Σ_σ ≥ 1` + `Σ_σ = 1` under drainage |
| `Uniformity/Density/QuadCert.lean` | 421 | *(follow-up unit)* the binary norm form `N(u+vα)`; the RAM (Eisenstein) and INERT (anisotropic) `typeOf` certificates |
| `Uniformity/Density/Statement.lean` | 178 | `UniformityStatement` (over THE density), *(P4)* `UniformityStatementDecided`, `UniformityStatementPadic`, `DrainageAt`, the cross-implications, **`TotalMassOne`** (named target, not proved) |
| `Uniformity/Density/Gates.lean` | 638 | G1–G8 (incl. the `gate_bracket_*_decided` payoff) + *(P4)* **`drainage_one`** and the `n = 1` re-key + the `#print axioms` block |
| `Uniformity/Density/Drainage.lean` | 1195 | *(unit UNIFORMITY-P2)* the valuation API, the three certificates, the dichotomy, **`drainage_two`**, `sum_three_decidedDensities_eq_one` (G9–G14) + *(P4)* §9, the 16 `n = 2` headlines over THE density incl. **`sum_three_densities_eq_one`** and **`totalMass_two`** |
| `verification/genuine_density_check.py` | 163 | exact `n = 2` enumeration over `ℤ_p`, `p ∈ {2,3,5}`, vs the W-11 closed forms |
| `verification/drainage_check.py` | 161 | *(unit UNIFORMITY-P2)* the tangency criterion and the certificate trichotomy vs the exact type map |

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
  decided limit *is* the density. Without drainage, `decidedDensity` is a certified lower
  bound and `genuineDensity` a certified upper bound — that is the honest state of affairs and
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

> ⚠ **CORRECTION, 2026-08-13 (unit UNIFORMITY-P2) — the `inertiaDegOf` definition below was
> UNFAITHFUL and has been changed.** The original read `inertiaDegOf g := sInf (normValues g)`
> ("the least strictly positive valuation of a norm"), justified by "the values realised by the
> integral `x ∈ A \ {0}` are exactly `f·ℕ`". That last step is **false whenever `A = O[α]` is
> not the maximal order.** Counterexample (verified independently by Codex): `g = X² − 27` over
> `ℤ_[3]`. Here `L = ℚ_3(√3)` is RAMIFIED, `(e,f) = (2,1)`; the norm form is
> `N(s + tα) = s² − 27t²`, whose valuation is `min(2v(s), 3 + 2v(t))` — the value `1` is never
> attained and `2` is, so the old definition returned `(e,f) = (1,2)`, i.e. **INERT for a
> RAMIFIED polynomial**. In the `n = 2` census this misreads the entire deep-ram family
> `RAM(h)`, `h ≥ 3` odd — W-11 mass `1/(q+1) − (q−1)/q²`, which is `1/12` at `q = 2`, not a
> rounding error.
>
> **The repair** (in force below): `inertiaDegOf g := sSup {k > 0 | k ∣ every element of
> normValues g}` — the **gcd** of the norm-valuation semigroup, i.e. the positive generator of
> the subgroup it spans. Faithfulness of the gcd form: all values lie in `f·ℤ`; and `A` has
> finite index in the maximal order `O_L`, so `π^m O_L ⊆ A` for some `m ≥ 1`, whence for
> `y ∈ O_L` with `w(y) = 1` the two members `π^m, π^m y ∈ A \ {0}` have norm valuations
> differing by exactly `f`. So the gcd is `f` for **every** order, maximal or not, in every
> characteristic and without separability hypotheses. **Two consequences:** (i) the deep-ram
> family is now read correctly (`typeOf_of_certRam` covers all odd `v(F)`, not just Eisenstein);
> (ii) `inertiaDegOf g ∣ deg g` holds *by construction*, which is what unblocked
> `typeOf_degree` (STATUS item 1, now closed). ⚠ **This is a trust-boundary change: the new
> definition is flagged for human review, like the old one.**

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

def normDivisors (g : Polynomial O) : Set ℕ := {k : ℕ | 0 < k ∧ ∀ m ∈ normValues g, k ∣ m}
noncomputable def inertiaDegOf (g : Polynomial O) : ℕ := sSup (normDivisors g)   -- the gcd
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

and the values realised by the *integral* `x ∈ A \ {0}` lie in `f·ℕ` and **generate `f·ℤ` as a
group** (the `π^m O_L ⊆ A` argument in the correction box above). So `f` is the **gcd** of
`{ v(N(x)) : x ∈ A \ {0} }` — which is `inertiaDegOf g` — and `e = d/f`. Four checks against
familiar cases: `g = X − a` gives `A ≅ O`, `N(π) = π`, gcd `1`, so `(e,f) = (1,1)` (this one is
**proved in Lean**, `efPair_of_natDegree_one`); `g = X² − π` (Eisenstein) gives `N(√π) = −π`,
value `1`, gcd `1`, so `(e,f) = (2,1)`; `g` with `ḡ` irreducible gives all norms of even
valuation with `2` attained, gcd `2`, so `(e,f) = (1,2)`; **and the case that broke the old
definition** — `g = X² − π³`, values `{2, 3, 4, …}`, least positive value `2` (wrong) but gcd
`1` (right), so `(e,f) = (2,1)`, ramified.

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

*~~Known gap~~ CLOSED 2026-08-13 (UNIFORMITY-P2):* `theorem typeOf_degree (hf : f.Monic) :
(typeOf f).degree = f.natDegree` is now **proved in general**. It reduces to
`inertiaDegOf g ∣ g.natDegree` for each monic irreducible factor, and under the gcd definition
that is immediate — `deg g = v(N(π))` is itself a member of `normValues g`, so the gcd divides
it (`inertiaDegOf_dvd_natDegree`), and `ramIndexOf g * inertiaDegOf g = deg g` exactly
(`ramIndexOf_mul_inertiaDegOf`); summing over the factors and using
`natDegree_multiset_prod_of_monic` gives the identity. **Consequence for the capstone:** the
hypothesis `σ.degree = n` in `UniformityStatement` now does work (off-degree σ are forced to
density 0), which was design point (iv) of the sign-off list.

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

noncomputable def decidedDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
  ⨆ N, decidedSeq O n σ N

noncomputable def genuineDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
  ⨅ N, possibleSeq O n σ N

noncomputable def gapSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℝ :=
  possibleSeq O n σ N - decidedSeq O n σ N

def UndecidedVanishes (n : ℕ) (σ : FactorizationType) : Prop :=
  Tendsto (gapSeq O n σ) atTop (𝓝 0)

-- unit UNIFORMITY-P4, 2026-08-13: the finiteness input for `Σ_σ`
def CoveringMenu (n : ℕ) (S : Finset FactorizationType) : Prop :=
  ∀ a : Fin n → O, typeOf (monicPoly a) ∈ S
```

> ⚠ **REWIRE, 2026-08-13 (unit UNIFORMITY-P4) — `genuineDensity` NOW NAMES THE OTHER LIMIT.**
> Asvin, Q5 of the morning's list: *"Let us define `genuineDensity` using the limit of the
> proportion (proven to equal the decided proportion) and let us prove that `Σ_σ R_σ = 1` using
> this definition."* Accordingly `genuineDensity` is now `⨅ N, possibleSeq` (what used to be
> `upperDensity`), and the old `⨆ N, decidedSeq` is now `decidedDensity`. The two `.lean`
> definitions above are the post-rewire text; the full rename map is §8. Everything numeric is
> unchanged, because at `n = 1` and `n = 2` the two limits are equal by a theorem.

**FAITHFULNESS OF `genuineDensity` (post-rewire — Asvin-reviewed core set).** `genuineDensity
O n σ = ⨅_N possibleSeq O n σ N` is *the limit of the proportion of level-`N` coefficient
classes consistent with type `σ`* — "consistent with" meaning `PossibleAt`: the class has at
least one monic degree-`n` lift whose `typeOf` is `σ`. Three things make this the right
formalisation of "the density of type-σ polynomials", and one thing it deliberately is not.

1. *It is an outer approximation of the actual locus.* Cutting `O^n` at level `N` into `q^(nN)`
   equal boxes, the type-σ locus is contained in the union of the σ-possible boxes and meets
   every one of them. So `possibleSeq σ N` is the proportion of the space that could still be
   type σ after seeing `N` digits of the coefficients.
2. *It really is a limit, and the limit exists for a structural reason.* Refining a level can
   only delete possible boxes, never create them (`possibleSet_subset_preimage`), so
   `possibleSeq` is antitone (`possibleSeq_antitone`) and bounded below by `0`; the infimum is
   therefore the honest `N → ∞` limit, and that is a **theorem** (`possibleSeq_tendsto`), not a
   definitional convention. Nothing is carried as data.
3. *It is the tight outer reading.* `decidedDensity ≤ genuineDensity` always
   (`decidedDensity_le_genuineDensity`), and the two agree **iff** the ambiguity gap drains
   (`genuineDensity_eq_of_drainage` and its converse `drainage_of_genuineDensity_eq`). So the
   pair brackets the truth from both sides and drainage is exactly the statement that the
   bracket closes.
4. *What it is NOT.* It is not asserted to be the Haar measure of the type-σ locus. That bridge
   needs the locus to be measurable and the cylinder measures to be `q^(−nN)`; see §3B.4. Read
   formally, `genuineDensity` is the limit of the consistent-class proportions, full stop —
   and that is what the capstone quantifies over, so nothing downstream depends on the bridge.

*Degenerate cases, unchanged by the rewire:* `n = 0` gives `genuineDensity O 0 ⟨0⟩ = 1` and `0`
elsewhere; level `0` is one class, harmless because the sequences are monotone/antitone.

**FAITHFULNESS OF `decidedDensity` (post-rewire).** Same object as the pre-rewire
`genuineDensity`, renamed: `⨆_N decidedSeq`, the limit of the proportion of classes on which
the type is *forced* (`DecidedAt`: every lift has type σ). It is the **certified inner**
reading — the mass a finite computation can vouch for — and its distinctive property, which the
outer density does NOT have, is that distinct types have disjoint decided sets
(`decidedSet_disjoint`), hence `∑_σ decidedDensity ≤ 1` (`sum_decidedDensity_le_one`). That
inequality is what turns lower bounds on the other types into upper bounds on σ, so the
certified density stays load-bearing after the rewire; it is not a deprecated alias.

**FAITHFULNESS OF `CoveringMenu` (new).** `CoveringMenu O n S` says the finite set `S` contains
`typeOf (monicPoly a)` for **every** `a : Fin n → O`. It is the finiteness input that makes
`Σ_σ` well posed: `FactorizationType` is infinite, only finitely many types occur in degree
`n`, and rather than construct that finite set (a partition enumeration) the statements take
any covering `S` as a hypothesis. Two honest consequences: (i) `S` may contain extra types, but
they contribute `0`, so no statement is weakened; (ii) the hypothesis is *checked*, not
assumed, wherever it is used — `coveringMenu_two` derives it at `n = 2` from `typeOf_two_cases`.

**Faithfulness of the counts and sequences (unchanged from the original unit).** The counts are
honest `ℕ`s (defect D10 of the old design fixed); the sequences are `ℝ`-valued; and both
densities are theorem-backed limits:

```lean
theorem decidedSeq_tendsto  : Tendsto (decidedSeq  O n σ) atTop (𝓝 (decidedDensity O n σ))
theorem possibleSeq_tendsto : Tendsto (possibleSeq O n σ) atTop (𝓝 (genuineDensity O n σ))
```

(defect D7 — "ℚ-valued `densityVal` carried as data" — fixed). Decidedness is not vacuous:
`proj` is surjective, so every class has lifts, hence a decided class is possible
(`decided_imp_possible`) and no class is decided for two distinct types
(`decidedSet_disjoint`).

**Faithfulness of `UndecidedVanishes` (defect D9).** The drainage hypothesis is tied to a
genuinely different object and does real work:

```lean
theorem decidedDensity_le_genuineDensity : decidedDensity O n σ ≤ genuineDensity O n σ
theorem genuineDensity_eq_of_drainage (h : UndecidedVanishes O n σ) :
    genuineDensity O n σ = decidedDensity O n σ
theorem drainage_of_genuineDensity_eq (h : genuineDensity O n σ = decidedDensity O n σ) :
    UndecidedVanishes O n σ
```

The converse direction is the point: `UndecidedVanishes` is *exactly* the statement that the
bracket closes, so it can never be a decorative hypothesis here.

*Design choice flagged:* the gap is taken **per σ** (`possibleSeq σ − decidedSeq σ`) rather
than globally (`1 − ∑_σ decidedSeq σ`), because the global form needs a finite menu of types,
which is downstream content. The global inequality that gates need is proved separately:
`sum_decidedDensity_le_one : ∑ σ ∈ S, decidedDensity O n σ ≤ 1` for any finite `S`, and its
consequence `decidedDensity_le_of_others`.

### 2.4 The drainage-unit definitions (UNIFORMITY-P2, 2026-08-13)

All of these live in `Uniformity/Density/Drainage.lean`. They are *auxiliary* — none of them
appears in the statement of a headline theorem — but they are new definitions, so they are
flagged for review anyway.

```lean
def qval (a : Fin 2 → O) (γ : O) : O := γ ^ 2 + a 1 * γ + a 0        -- F(γ)
def qder (a : Fin 2 → O) (γ : O) : O := 2 * γ + a 1                  -- F'(γ)

def Tang (π : O) (a : Fin 2 → O) (t : ℕ) (γ : O) : Prop :=
  π ^ t ∣ qval a γ ∧ π ^ ((t + 1) / 2) ∣ qder a γ

def CertSplit (π : O) (a : Fin 2 → O) (N : ℕ) : Prop :=
  ∃ (γ : O) (w : ℕ), 2 * w + 1 ≤ N ∧ π ^ w ∣ qder a γ ∧ ¬ π ^ (w + 1) ∣ qder a γ ∧
    π ^ (2 * w + 1) ∣ qval a γ
def CertRam (π : O) (a : Fin 2 → O) (N : ℕ) : Prop :=
  ∃ (γ : O) (j : ℕ), 2 * j + 2 ≤ N ∧ π ^ (2 * j + 1) ∣ qval a γ ∧
    ¬ π ^ (2 * j + 2) ∣ qval a γ ∧ π ^ (j + 1) ∣ qder a γ
def CertInert (π : O) (a : Fin 2 → O) (N : ℕ) : Prop :=
  ∃ (γ : O) (k : ℕ) (b₀ b₁ : O), 2 * k + 1 ≤ N ∧ qval a γ = π ^ (2 * k) * b₀ ∧
    qder a γ = π ^ k * b₁ ∧ Anisotropic ![b₀, b₁]

def CongAt (π : O) (N : ℕ) (a b : Fin 2 → O) : Prop := ∀ i, π ^ N ∣ (b i - a i)

def UndecidedAt (n N : ℕ) (c : Coeff O n N) : Prop := ∀ σ, ¬ DecidedAt O n σ N c
def undecidedSet   (n N : ℕ) : Set (Coeff O n N) := {c | UndecidedAt O n N c}
noncomputable def undecidedCount (n N : ℕ) : ℕ := Nat.card (undecidedSet O n N)
noncomputable def undecidedSeq   (n N : ℕ) : ℝ :=
  (undecidedCount O n N : ℝ) / (residueCard O : ℝ) ^ (n * N)
```

**Faithfulness — `qval`/`qder`.** `qval a γ = (monicPoly a).eval γ` is proved
(`qval_eq_eval`); `qder a γ` is the linear coefficient of the recentred polynomial
(`qval_shift : qval a (γ + δ) = qval a γ + qder a γ * δ + δ ^ 2` is the recentring identity, and
it is *the* computation the whole file runs on). Note `qder` is the formal derivative, so in
residue characteristic 2 it is just `a 1` up to `2γ ∈ 𝔪` — nothing in the file assumes `2` is a
unit, and the wild case is not special-cased anywhere.

**Faithfulness — `Tang`.** `Tang π a t γ` says `min(v(F(γ)), 2·v(F'(γ))) ≥ t`, written with
divisibility instead of valuations (`π ^ ⌈t/2⌉ ∣ F'(γ)` is `2 v(F') ≥ t`; `(t+1)/2` is ℕ
division, i.e. `⌈t/2⌉`). The **tangency depth** `T(a) = max_γ min(v(F(γ)), 2 v(F'(γ)))` is the
single invariant governing decidedness. It is *not* defined as a function in Lean (a max over
`O` would need a compactness argument); instead the file works with "no centre reaches depth
`N`", and manufactures the maximiser by descent (`exists_max_step`). `Tang` depends on the
choice of uniformizer `π` only through `π ^ k ∣ ·`, which is `π`-independent.

**Faithfulness — the three `Cert*`.** These are the three readable Newton-polygon shapes of the
recentred quadratic, written so that *every numeric datum they mention sits strictly inside the
window* `N` — that is exactly what makes them class properties (`CertSplit_congr` &c.) and hence
what "decided" can be read off. `CertSplit` is Newton's condition `v(F) > 2v(F')` at a centre
with `2v(F') < N`; `CertRam` is "the value has exact ODD valuation `< N` and the derivative is
at least half of it"; `CertInert` is "the value has valuation `2k < N`, the derivative at least
`k`, and the residual data `(b₀, b₁)` is anisotropic mod `𝔪`". Here `Anisotropic ![b₀,b₁]` is
the QuadCert predicate on the *binary form* `Q(u,v) = u² − b₁uv + b₀v²` ("its only zero mod `𝔪`
is `(0,0)`"), which is equivalent to the *residual quadratic* `y² + b₁y + b₀` having no root mod
`𝔪` — the two are related by `z = −u/v` (`exists_residual_root` proves the direction used).
`y² + b₁y + b₀` is the shape that appears in the recentring identity
`F(γ + π^k z) = π^{2k}(z² + b₁z + b₀)`; the sign flip between it and `Q` is not a typo. Anisotropy forces `b₀` to be a unit, so the valuation `2k` in `CertInert`
is automatically exact. **What is NOT claimed:** the certificates are not asserted to be
exhaustive of decidedness — only that *if no centre is deeply tangent* one of them fires
(`cert_of_not_tang`). The numeric check `verification/drainage_check.py` shows the criterion is
in fact sharp (`T < N ⟺ decided`) at `p = 2, 3, 5` up to level 4, but sharpness is not proved
and is not needed.

**Faithfulness — `UndecidedAt`.** "No type is decided on `c`". It is the honest complement:
`decidedSet σ` for the finitely many `σ`, together with `undecidedSet`, cover everything
(`coeff_subset_union` at `n = 2`), and the general bound `gapSeq σ N ≤ undecidedSeq N`
(`gapSeq_le_undecidedSeq`, any `n`) holds because a `σ`-possible class that is not
`σ`-decided has a lift of type `σ` and therefore cannot be decided for any type at all.
`undecidedSeq` is normalised by the same `q^(n·N)` box count as `decidedSeq`.

### 2.5 The capstone targets (signature points SIGNED OFF 2026-08-13; rewired same day)

```lean
def UniformityStatement : Prop :=                       -- over THE density
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

def UniformityStatementDecided : Prop :=                -- identical, over decidedDensity
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          decidedDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

def UniformityStatementPadic : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        den.eval (p : ℚ) ≠ 0 ∧
          genuineDensity ℤ_[p] n σ = ((num.eval (p : ℚ) / den.eval (p : ℚ) : ℚ) : ℝ)

def DrainageAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    ∀ σ : FactorizationType, UndecidedVanishes O n σ

theorem UniformityStatement.toPadic   (h : UniformityStatement) : UniformityStatementPadic
theorem UniformityStatement.ofDecided (hd : ∀ n, DrainageAt n)
    (h : UniformityStatementDecided) : UniformityStatement
theorem UniformityStatement.toDecided (hd : ∀ n, DrainageAt n)
    (h : UniformityStatement) : UniformityStatementDecided
```

These are `Prop` **definitions**, not sorried theorems (this repo carries zero `sorry`s). The
`∃ (num, den)` stands outside the `∀ O`: that ∃-before-∀ order *is* the uniformity claim.
Neither can be satisfied vacuously — both densities are Part-1 limits, proved to be limits of
explicitly counted proportions, not an abstract model's carried value, so the F1 accident of
the old `Stage2/UniformityTarget.lean` (both anchors provable in ~20 lines with a Lean-core
footprint) is structurally impossible here.

**Why no drainage conjunct inside either Prop** (the design question this unit had to answer).
The old `lean/` corpus carries drainage as conjunct A2 of its conditionality display, because
there the density existed *only* as a decided limit — without drainage that theorem was about
the wrong object, so the hypothesis had to travel with the statement. Here the outer limit is a
first-class object with its own existence theorem, so `UniformityStatement` is honest standing
alone: it says the consistent-class proportion converges to `num(q)/den(q)`. Drainage is what
makes the two Props *equivalent*, and it therefore appears as the hypothesis of the two
cross-implications, never as a conjunct. Keeping `UniformityStatementDecided` alongside
preserves the unconditional-shape option: a census of decided strata proves it with no drainage
input at all.

**The four signature points, PRESERVED VERBATIM by the rewire.** (i) The `∀ O` is over `Type`
(universe 0). `ℤ_[p]` and every concrete local ring live there; a universe-polymorphic version
would need the `Prop` to be universe-polymorphic too. (ii) The rational function is evaluated at
`(q : ℚ)` and the equality is read in `ℝ` via the coercion. (iii) `den.eval q ≠ 0` is demanded
per-`O`, not globally. (iv) `σ.degree = n` does real work now that `typeOf_degree` has landed:
off-degree σ are forced to density 0.

---

## 3. GATE RESULTS

All gates hold for an **arbitrary** complete DVR with finite residue field, not just `ℤ_[2]`.

> **Post-rewire reading of this table (2026-08-13, UNIFORMITY-P4).** The `n = 2` rows below are
> the CERTIFIED-density versions, which is why their names carry `_decided` — they are proved in
> `Gates.lean`, which sits below `Drainage.lean` and so cannot see `drainage_two`. Every one of
> them has an unsuffixed twin at the end of `Drainage.lean` stating the **same numbers** about
> THE density `genuineDensity`; the twins are listed in §8.3. The `n = 1` rows are stated
> directly over `genuineDensity` (drainage at `n = 1` is proved in `Gates.lean` itself).

| gate | statement | status | expected (W-11) |
|---|---|---|---|
| **G1** `decidedDensity_linear_eq_one` | `decidedDensity O 1 ⟨{(1,1)}⟩ = 1` | **EXACT, proved** | 1 (every monic linear splits) ✓ |
| **G1′** `decidedDensity_one_of_ne` | `σ ≠ ⟨{(1,1)}⟩ → decidedDensity O 1 σ = 0` | **EXACT, proved** | 0 ✓ |
| **G1″** `gate_sigma_separation_one` | `decidedDensity O 1 linType ≠ decidedDensity O 1 splitType` | **EXACT, proved** | `1 ≠ 0` ✓ |
| **G2** `typeOf_mul_linear` | `typeOf ((X−C r)(X−C s)) = ⟨{(1,1),(1,1)}⟩` | proved | the split type ✓ |
| **G3** `gate_split_lower_decided` | `1/q² ≤ decidedDensity O 2 splitType` | **BOUND, proved** | `q/(2(q+1))` ✓ |
| **G3-sharp** `gate_split_lower_sharp_decided` | `(q−1)/q² ≤ decidedDensity O 2 splitType` | **BOUND, proved** (all `q−1` level-1 classes `(0, unit)`) | W-11's SEP-SPLIT row `(q−1)/(2q)` in per-centre form ✓ |
| **G3′** `gate_padic_two_decided` | `1/4 ≤ decidedDensity ℤ_[2] 2 splitType` | **BOUND, proved** | `1/3` ✓ |
| **G4** `decidedDensity_two_linType_eq_zero` | `decidedDensity O 2 ⟨{(1,1)}⟩ = 0` | **EXACT, proved** | 0 ✓ |
| **G4′** `gate_sigma_separation_two_decided` | `decidedDensity O 2 linType < decidedDensity O 2 splitType` | **proved** | `0 < 1/3` ✓ |
| **G5** `typeOf_ram_of_eisenstein` | `a₀ ∈ 𝔪∖𝔪², a₁ ∈ 𝔪 → typeOf = ⟨{(2,1)}⟩` | **proved** | the RAM(1) family ✓ |
| **G5′** `gate_ram_lower_decided` | `1/q⁴ ≤ decidedDensity O 2 ramType` | **BOUND, proved** (one level-2 Eisenstein class) | `1/(q+1)` ✓ |
| **G6** `typeOf_inert_of_anisotropic` | reduced norm form anisotropic → `typeOf = ⟨{(1,2)}⟩` | **proved** | the SEP-INERT family ✓ |
| **G6′** `lowers_padic_two_decided/three` (inert leg) | `1/q² ≤ decidedDensity ℤ_[q] 2 inertType`, `q = 2, 3` | **BOUND, proved** (`decide` on `ZMod q`) | `q/(2(q+1))` ✓ |
| **G7** `bracket_two_decided` | three lower bounds ⟹ three two-sided brackets | **proved** (via `sum_decidedDensity_le_one`) | — |
| **G8** `gate_bracket_padic_two_decided` / `_three` | **THE PAYOFF** — see the numeric table below | **proved** | all three W-11 values inside ✓ |
| **G8′** `gate_bracket_w11_two` / `_three` | the W-11 values lie in the brackets | **proved** (`norm_num`) | — |
| **G9** `drainage_two` | `UndecidedVanishes O 2 σ` — the `n = 2` gap drains, every `O`, every `σ` | **PROVED** (UNIFORMITY-P2) | W-11 (iii): undecided mass `= q^(−N)`; we prove `≤ q^(−M)` at level `2M` ✓ |
| **G10** `genuineDensity_eq_decidedDensity_two` | `genuineDensity O 2 σ = decidedDensity O 2 σ` — **the bracket closes** | **PROVED** | — |
| **G11** `sum_three_decidedDensities_eq_one` | `decidedDensity O 2 split + inert + ram = 1` | **EXACT EQUALITY, proved, every `O`** | W-11 (iii) `Σ = 1`: `q/(2(q+1)) + q/(2(q+1)) + 1/(q+1) = 1` ✓ |
| **G12** `typeOf_two_cases` | every monic quadratic has type `split`, `inert` or `ram` | **proved** | the three-row `n = 2` menu ✓ |
| **G13** `typeOf_degree` | `f.Monic → (typeOf f).degree = f.natDegree`, all degrees | **proved** (was STATUS item 1) | — |
| **G14** `undecidedCount_le` | `undecidedCount O 2 (2M) ≤ q^(3M)` | **proved** | W-11's exact law is `q^(2M)`; ours is lossy but sufficient ✓ |

### The certified two-sided brackets (`gate_bracket_*`)

The lower bounds come from decided classes; each upper bound is `1 − (the other two lowers)`,
via the proved `sum_decidedDensity_le_one` (densities of distinct types sum to `≤ 1`).

**q = 2 (`O = ℤ_[2]`, the wild prime) — `gate_bracket_padic_two_decided`**

| type | lower (proved) | upper (proved) | W-11 exact | inside? |
|---|---|---|---|---|
| split `{(1,1),(1,1)}` | `1/4 = 0.2500` | `11/16 = 0.6875` | `q/(2(q+1)) = 1/3 ≈ 0.3333` | **YES** |
| inert `{(1,2)}` | `1/4 = 0.2500` | `11/16 = 0.6875` | `q/(2(q+1)) = 1/3 ≈ 0.3333` | **YES** |
| ram `{(2,1)}` | `1/16 = 0.0625` | `1/2 = 0.5000` | `1/(q+1) = 1/3 ≈ 0.3333` | **YES** |

**q = 3 (`O = ℤ_[3]`, tame) — `gate_bracket_padic_three_decided`**

| type | lower (proved) | upper (proved) | W-11 exact | inside? |
|---|---|---|---|---|
| split | `2/9 ≈ 0.2222` | `71/81 ≈ 0.8765` | `3/8 = 0.375` | **YES** |
| inert | `1/9 ≈ 0.1111` | `62/81 ≈ 0.7654` | `3/8 = 0.375` | **YES** |
| ram | `1/81 ≈ 0.0123` | `2/3 ≈ 0.6667` | `1/4 = 0.25` | **YES** |

**Reading.** These are the first *two-sided* certified brackets on a genuine `p`-adic splitting
density in this repo. They are loose (the ram lower bound uses a single level-2 class and the
inert lower bound a single level-1 class), but they are honest: every bound is a theorem about
`decidedDensity`, and each of the six intervals contains the corresponding W-11 value. The
Python trajectories in §4 show where the true values sit — e.g. at `q = 2` the split decided
proportion climbs `1/4, 1/4, 5/16, 5/16 → 1/3`, so the certified lower bound `1/4` is exactly
the level-1 (and level-2) truth, while the upper bound is what the *other two* types'
certificates can currently force.

**Exact-vs-bounded, stated plainly** *(revised 2026-08-13, UNIFORMITY-P2)*. At `n = 1` the gates
are **exact equalities**. At `n = 2`: the **aggregate** is now an exact equality
(`sum_three_decidedDensities_eq_one`, G11) and the bracket **closes**
(`genuineDensity_eq_decidedDensity_two`, G10 — the decided limit is genuinely *the* density, not merely a lower
bound for it); but **no individual `n = 2` value is proved exact** — split, inert and ram are
still only two-sided bounds. The mechanism of each lower bound: split — one Hensel lift at a
simple residue root (`typeOf_split_of_unit`), counted over all `q−1` level-1 classes
`(0, unit)`; ram — Eisenstein irreducibility plus `N(α) = a₀` of valuation 1; inert —
anisotropy of the reduced binary norm form, which forces every norm valuation to be even.

---

## 3B. THE `n = 2` DRAINAGE THEOREM (unit UNIFORMITY-P2, 2026-08-13)

**Rung landed: (a), general `O`** — every complete DVR with finite residue field, no
restriction on the residue characteristic (the wild prime `2` is not special-cased anywhere),
no `ℤ_[p]`-specific step. The fallback rungs (b) `ℤ_[p]` and (c) concrete `p` were not needed.

### 3B.1 The invariant

For `f = X² + a₁X + a₀` write `F(γ) = γ² + a₁γ + a₀` and `F'(γ) = 2γ + a₁`, and define the
**tangency depth**

    T(a) = max_γ min ( v(F(γ)), 2·v(F'(γ)) )   ∈ ℕ ∪ {∞}.

Two facts, each proved in Lean, sandwich the drainage:

**(D1) `T(a) < N` ⟹ the level-`N` class of `a` is decided** (`decidedAt_of_not_tang`). Take a
centre `γ` attaining the max and read the Newton polygon of the recentred `X² + F'(γ)X + F(γ)`.
Exactly four shapes are possible, and the fourth is self-defeating:

| shape at the maximising centre | certificate | type |
|---|---|---|
| `v(F) > 2v(F')` | `CertSplit` — Newton root, Hensel lifts it | split |
| `v(F)` odd, `≤ 2v(F')` | `CertRam` — norms of valuation `2` and of odd valuation, `gcd = 1` | ram |
| `v(F) = 2k ≤ 2v(F')`, residual irreducible | `CertInert` — all norm valuations even | inert |
| `v(F) = 2k`, residual with a SIMPLE root | recentre at `γ + π^k z` ⟹ `CertSplit` | split |
| `v(F) = 2k`, residual with a DOUBLE root | **impossible**: recentring reaches depth `2k+1` | — |

The last line is the whole trick — the classical Montes/Okutsu refinement loop is replaced by
the observation that a refinement step *increases* `min(v(F), 2v(F'))`, so at the maximiser
there is nothing left to refine. *(Two bookkeeping points a verifier will ask about, both
handled in the Lean and worth stating explicitly. **The endpoint.** "Contradicts maximality of
`t`" is the right reason only when `t + 1 < N`; at `t + 1 = N` what it contradicts is the
hypothesis that no centre reaches depth `N`. The Lean does not case-split: `exists_max_step`
returns `t` **together with** `¬ ∃γ, Tang π a (t+1) γ`, which at the endpoint *is* the
hypothesis. **The choice.** In §3B's counting step, "the map class ↦ (γ mod π^M, a₁ mod π^{2M})"
is not literally a map until one witness pair `(a, γ)` is selected per undecided class; the Lean
selects with `choose`, and the pinning lemma then shows any such selection is injective.)* Each certificate mentions only data with exponent `< N`
(`2w+1 ≤ N`, `2j+2 ≤ N`, `2k+1 ≤ N`), so it survives verbatim on every other lift of the class
(`CertSplit_congr`, `CertRam_congr`, `CertInert_congr`) — and a certificate determines the
type, which is what "decided" means.

**(D2) `T(a) ≥ N` is rare** (`undecidedCount_le`). At level `N = 2M`, deep tangency means
`π^{2M} ∣ F(γ)` and `π^M ∣ F'(γ)` for some `γ`. Then the centre only matters mod `π^M`
(shifting `γ` by `π^M s` moves `F(γ)` by `π^M s F'(γ) + π^{2M}s²`, both in `π^{2M}`), and
`a₀ ≡ −γ² − a₁γ (mod π^{2M})` is then forced (`class_pinned`). So the undecided classes inject
into `(γ mod π^M, a₁ mod π^{2M})` — at most `q^M · q^{2M} = q^{3M}` of the `q^{4M}` classes.

Hence `undecidedSeq(2M) ≤ q^{−M} → 0`, and since `gapSeq σ` is antitone and `≥ 0` and
`gapSeq σ N ≤ undecidedSeq N` for every `σ`, its infimum is `0`: **`drainage_two`**.

### 3B.2 Honest slack

The bound `q^{3M}` is **lossy by a factor `q^M`**: W-11's exact law is `q^N` undecided classes
at level `N`, i.e. `q^{2M}` here (confirmed numerically, §4B). Drainage needs only *some* bound
beating `q^{2N}`, so the exact per-centre census was not attempted. Also note that (D1) is a
*sufficient* condition for decidedness in the Lean proof; the numeric check shows it is
actually an equivalence (`T < N ⟺ decided`) on every row computed, but that is not proved and
nothing depends on it.

### 3B.3 The payoff, and what it is not

`sum_three_decidedDensities_eq_one` (G11) is the first EXACT `n = 2` statement about the genuine
density in this repo: split + inert + ram `= 1`, for arbitrary `O`. Its `≤` half is the old
total-mass bound; its `≥` half is drainage — without drainage the decided proportions could in
principle leave mass permanently unaccounted for, and the identity would fail.

**It is not the individual values.** W-11's `split = inert = q/(2(q+1))`, `ram = 1/(q+1)` need
two further ingredients, neither of which this unit attempted (both are recorded as open in
§6):

* the **split = inert symmetry** at every window — over `2`-invertible `O` this is the twist
  `disc ↦ ε·disc` for a non-square unit `ε`, i.e. `(a₀,a₁) ↦ (εa₀ + a₁²(1−ε)/4, a₁)`, a
  measure-preserving involution of every level-`N` box; in residue characteristic 2 the twist is
  Artin–Schreier (`a₀ ↦ a₀ + a₁²u`) and there is no uniform coefficient formula, which is why
  W-11 proves the symmetry by a finite telescoping identity instead;
* the **exact ram count** `Σ_{u odd < N} (q−1)q^{2N−u−1}`, which needs the per-centre census
  (uniqueness of the centre mod `π^{(u+1)/2}` plus disjointness across `u`).

Given drainage, either one of these plus the other's value pins all three: `2·split + ram = 1`.

### 3B.4 What "the bracket closes" does and does not say

*(Adversarial-verifier finding, Codex, 2026-08-13 — logged because it is exactly the kind of
over-reading this repo's honesty invariant exists to prevent.)*
`genuineDensity O 2 σ = decidedDensity O 2 σ` says that the **inner** approximation of the type-σ
locus (unions of decided cylinders) and the **outer** one (intersections of possible cylinders)
have the same limit. It does **not**, as a Lean theorem, say that this common value is the
**Haar measure** of the type-σ locus. That bridge would additionally need: level-`N` cylinders
have measure `q^(−nN)`; the inner union and outer intersection are measurable; the locus itself
is measurable (or the measure is completed so that subsets of the null boundary are); and the
locus is sandwiched between the two. Mathematically the vanishing bracket is precisely the
null-boundary input such a bridge needs and every remaining step is standard — but none of it is
formalized here. Formally, `decidedDensity` is the limit of decided proportions and
`genuineDensity` the limit of consistent-class proportions, full stop; and since the latter is
what the capstone `UniformityStatement` quantifies over, **nothing downstream depends on the
bridge**. It is recorded as an optional, not a blocking, item. Where this note (§1) speaks of
"Haar-measure boxes" and "the true measure", read those as motivation, not as formalized
content.

> **Post-rewire amendment (UNIFORMITY-P4).** The rewire does not weaken this caveat and does not
> smuggle the bridge in. It changes *which* of the two limits wears the name "the density", on
> the grounds that the outer limit is the one that deserves it (it bounds the locus from
> outside at every finite level, so it is an upper bound for any reasonable measure of the
> locus, whereas the inner one is only a lower bound). Calling it `genuineDensity` is a naming
> decision about the better formal proxy, not a claim that a measure has been constructed.

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
    Lean gate `gate_split_lower_decided`: 1/q^2 = 1/4 <= density(split) = 1/3  ->  CONSISTENT

--- p = q = 3   (W-11 limits: split = inert = 3/8, ram = 1/4; undecided mass = q^-N) ---
 N      box |    split    inert      ram    undec | W11 split  W11 ram  W11 und | amb | match | decidedSeq(split)
 1        9 |        3        3        0        3 |         3        0        3 |   3 |   YES | 1/3 = 0.333333
 2       81 |       27       27       18        9 |        27       18        9 |   9 |   YES | 1/3 = 0.333333
 3      729 |      270      270      162       27 |       270      162       27 |  27 |   YES | 10/27 = 0.370370
    Lean gate `gate_split_lower_decided`: 1/q^2 = 1/9 <= density(split) = 3/8  ->  CONSISTENT

--- p = q = 5   (W-11 limits: split = inert = 5/12, ram = 1/6; undecided mass = q^-N) ---
 N      box |    split    inert      ram    undec | W11 split  W11 ram  W11 und | amb | match | decidedSeq(split)
 1       25 |       10       10        0        5 |        10        0        5 |   5 |   YES | 2/5 = 0.400000
 2      625 |      250      250      100       25 |       250      100       25 |  25 |   YES | 2/5 = 0.400000
    Lean gate `gate_split_lower_decided`: 1/q^2 = 1/25 <= density(split) = 5/12  ->  CONSISTENT

ALL CHECKS PASSED
```

### 4B. The drainage cross-check (`verification/drainage_check.py`, unit UNIFORMITY-P2)

Same exact enumeration, now used to test the three claims of `Drainage.lean` against an
*independent* decision procedure (the discriminant-based `classify`, which knows nothing about
tangency depths or Newton polygons). For each class it computes
`T = max_γ min(v(F(γ)), 2v(F'(γ)))` by brute force over centres and asks: (C1) does `T < N`
imply decided? (C2) does the certificate trichotomy predict the right type? (C3) is
`#{T ≥ 2M} ≤ q^{3M}`?

```
--- p = q = 2 ---                          --- p = q = 3 ---            --- p = q = 5 ---
 N     box |  T<N decided  C1  C2 | T>=N undec  bound  C3
 1       4 |    2       2 YES YES |    2     2      -   -      1    9 |   6   6 YES YES | 3  3
 2      16 |   12      12 YES YES |    4     4      8 YES      2   81 |  72  72 YES YES | 9  9 (bound 27) YES
 3      64 |   56      56 YES YES |    8     8      -   -      3  729 | 702 702 YES YES | 27 27
 4     256 |  240     240 YES YES |   16    16     64 YES      p=5: N=1 20/20 YES; N=2 600/600 YES (25 <= 125)
```

**Reading.** (C1) and (C2) hold on every row at all three primes — and note the first two
numeric columns are *equal* on every row: `T < N ⟺ decided`, so the Lean criterion is not just
sound but sharp (sharpness is not proved and nothing depends on it). (C3) holds with the
expected slack: the true deeply-tangent count is `q^N` (= W-11's exact drainage law), against
the proved bound `q^{3M} = q^{1.5N}`. Two things this rules out: a certificate that fires on
the wrong type (it would break C2 immediately at `p = 2`, where ram and inert both occur at
even disc valuation), and a decidedness criterion that is too generous.

**Reading (the older check).** Every cell matches W-11 exactly, at three primes including the
wild one, at every level computed — an independent confirmation that the *Lean definition* of
`decidedSeq` (all lifts of a class share a type) is the same object as the corpus's "σ-decided
at window `N`".
Note `decidedSeq(split)` climbing `1/4, 1/4, 5/16, 5/16 → 1/3` at `p = 2`: monotone, as
`decidedSeq_mono` requires, and converging to the W-11 limit. `n = 3` was **not** run — there
is no discriminant-only criterion at degree 3, so an exact enumeration needs a genuine
`ℚ_p`-factorization oracle; left as an open verification item.

---

## 5. AXIOM FOOTPRINTS

`lake build` from `leanfinal/` is green (8 566 jobs). The `#print axioms` block at the end of
`Gates.lean` reports, for every one of the following:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

`decidedDensity_linear_eq_one`, `decidedDensity_one_of_ne`, `gate_sigma_separation_one`,
`typeOf_mul_linear`, `typeOf_split_of_unit`, `gate_split_lower_decided`, `gate_padic_two_decided`,
`decidedDensity_two_linType_eq_zero`, `gate_sigma_separation_two_decided`, `decidedSeq_tendsto`,
`possibleSeq_tendsto`, `genuineDensity_eq_of_drainage`, `decidedDensity_le_genuineDensity`,
`sum_decidedDensity_le_one`, `card_res`, `UniformityStatement.toPadic`
— and, from the follow-up unit — `norm_quad`, `typeOf_ram_of_eisenstein`,
`typeOf_inert_of_anisotropic`, `gate_split_lower_sharp_decided`, `gate_ram_lower_decided`, `lowers_padic_two_decided`,
`lowers_padic_three_decided`, `bracket_two_decided`, `gate_bracket_padic_two_decided`, `gate_bracket_padic_three_decided`,
`gate_bracket_w11_two`, `gate_bracket_w11_three` (28 declarations in all).

**Unit UNIFORMITY-P2 (2026-08-13)** adds a second `#print axioms` block, at the end of
`Drainage.lean`; every line reports `[propext, Classical.choice, Quot.sound]`:

```
typeOf_of_certSplit   typeOf_of_certRam    typeOf_of_certInert   cert_of_not_tang
decidedAt_of_not_tang gapSeq_le_undecidedSeq  class_pinned       undecidedCount_le
drainage_two          genuineDensity_eq_decidedDensity_two  typeOf_two_cases      sum_three_decidedDensities_eq_one
```

`lake build` green (8 567 jobs) after the change; `grep -rn sorry Uniformity/` still returns
only the word inside docstrings. The `typeOf` definition change (§2.2) left every previously
reported footprint unchanged.

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
* `decidedDensity`/`genuineDensity` **are** the limits (`Tendsto`); the sandwich; the drainage
  tie **in both directions**;
* `∑_{σ ∈ S} decidedDensity ≤ 1` and the complement upper bound;
* gates G1–G4 (§3);
* `UniformityStatement → UniformityStatementPadic`;
* **(follow-up unit, 2026-08-13)** the binary norm form `N(u+vα) = u² − a₁uv + a₀v²`
  (`norm_quad`, via the power basis `(1,α)` and `Matrix.det_fin_two`); "a reducible monic
  quadratic is `(X−r)(X−s)`" (`exists_roots_of_not_irreducible`); the RAM certificate
  (`irreducible_of_eisenstein`, `typeOf_ram_of_eisenstein`); the INERT certificate
  (`irreducible_of_anisotropic`, `typeOf_inert_of_anisotropic`); the sharpened split count
  (`decidedCount_split_ge : q − 1 ≤ decidedCount O 2 splitType 1`); the bracket engine
  (`bracket_two_decided`) and the numeric brackets at `q = 2, 3` (G5–G8 in §3);
* **(unit UNIFORMITY-P2, 2026-08-13)** the `typeOf` repair (§2.2) and with it `typeOf_degree`
  in full generality; the ℕ-valued valuation API (`pow_dvd_iff_le`, `pow_dvd_right_of_mul`,
  `no_odd_exact_of_split`, `pow_dvd_both_of_even`); the three window certificates and their
  types (`typeOf_of_certSplit/Ram/Inert`) — the RAM one now covers **all** odd `v(F(γ))`, not
  just Eisenstein, and the INERT one covers all even `v(F(γ))`, not just `v = 0`; their
  class-invariance (`Cert*_congr`); **the dichotomy** (`cert_of_not_tang`); **the decidedness
  theorem** (`decidedAt_of_not_tang`); the undecided objects and the universal gap bound
  (`gapSeq_le_undecidedSeq`, any `n`); the pinning and counting lemmas (`class_pinned`,
  `undecidedCount_le`); **`drainage_two`**, **`genuineDensity_eq_decidedDensity_two`**, `typeOf_two_cases` and
  **`sum_three_decidedDensities_eq_one`** (G9–G14 in §3 and §3B).

### STATED IN THIS NOTE, NOT PROVED (open targets, statements preserved)

1. ~~**`typeOf_degree`**~~ — **DONE** (UNIFORMITY-P2): proved in full generality, as a free
   consequence of the gcd repair of `inertiaDegOf` (§2.2). The route the old note recommended
   (prove `w(x) = v(N x)/d` is a valuation) turned out to be unnecessary: only the *divisibility*
   `f ∣ d` was needed, and the gcd definition delivers it because `d = v(N(π)) ∈ normValues`.
2. ~~**`gate_split_exact`** (all `q−1` level-1 split classes)~~ — **DONE** (follow-up unit):
   `decidedCount_split_ge` + `gate_split_lower_sharp_decided`, giving `(q−1)/q²`.
3. ~~**`gate_inert_lower`**~~ — **DONE in the form that was needed** (follow-up unit):
   `typeOf_inert_of_anisotropic` proves the certificate for *any* complete DVR from anisotropy
   of the reduced binary norm form. What is **fenced out**: the *general-`O`* inert lower bound,
   because exhibiting an anisotropic quadratic over an abstract finite residue field needs
   "every finite field has an irreducible monic quadratic", which mathlib v4.31.0 does not
   expose in a directly usable form. Consequence: the inert lower bound is instantiated only at
   `ℤ_[2]` and `ℤ_[3]`, where anisotropy is a `decide` on `ZMod p`
   (`inert_decided_class_padic`), and the `gate_bracket_*` payoff is therefore stated at
   `q = 2, 3` rather than for all `O`. Statement of the missing piece:
   `theorem exists_anisotropic (O) [bundle] : ∃ a : Fin 2 → O, Anisotropic a`.
4. ~~**`gate_ram_lower_decided`**~~ — **DONE** (follow-up unit): `typeOf_ram_of_eisenstein` +
   `gate_ram_lower_decided : 1/q⁴ ≤ decidedDensity O 2 ramType`, for **every** complete DVR. Not
   sharpened: the bound uses one level-2 class, where the full centre-0 Eisenstein stratum has
   `(q−1)q` classes (density `(q−1)/q³`) and W-11's whole RAM(1) row, over all `q` centres, is
   `(q−1)/q²`. Sharpening needs counting the image of `𝔪` inside `O/𝔪²`;
   statement: `theorem decidedCount_ram_ge : (residueCard O − 1) * residueCard O ≤
   decidedCount O 2 ramType 2`.
5. ~~**`drainage_two`**~~ — **DONE** (UNIFORMITY-P2), for arbitrary `O`: see §3B. The
   `possibleSeq` side needed no separate certificate — `gapSeq σ N ≤ undecidedSeq N` routes
   every type through one bound. The *exact rate* `q^{−N}` of W-11 clause (iii) is **not**
   proved; the proved rate is `q^{−M}` at level `2M`, which is all drainage needs.

5a. **The individual exact `n = 2` values** (the remaining half of the payoff). With drainage
   in hand these reduce to two independent statements, either of which suffices given the other:

   ```lean
   theorem split_eq_inert_decidedDensity_two : decidedDensity O 2 splitType = decidedDensity O 2 inertType
   theorem ram_decidedDensity_two :
       decidedDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
   ```
   and then `sum_three_decidedDensities_eq_one` gives
   `split = inert = q / (2(q+1))` (W-11's values). *Why they were not attempted here*: the
   symmetry has no uniform coefficient formula across residue characteristics (the char-`≠2`
   twist `disc ↦ ε·disc` becomes Artin–Schreier at `q` even — see §3B.3), and the ram value
   needs the exact per-centre census (`(q−1)q^{2N−u−1}` classes per odd `u`, plus uniqueness of
   the centre mod `π^{(u+1)/2}` and disjointness across `u`). Both are genuine units of work,
   not one-liners. **A cheaper intermediate**, if a concrete number is wanted first: the
   `2`-invertible case of the symmetry (`ℤ_[p]`, `p` odd) via the involution
   `(a₀,a₁) ↦ (εa₀ + a₁²(1−ε)/4, a₁)`, which is measure preserving on every level-`N` box and
   swaps split-decided with inert-decided once the disc classification is available in Lean.
6. **`n = 3` Python check** — needs a `ℚ_p`-factorization oracle (the quarry's
   `verification/quartic_oracle.py` uses PARI `factorpadic`; cypari2 was not available in this
   session's environment and was not installed).

### NOT BLOCKED, JUST NOT IN SCOPE

Design point **E** of the original charge (`GenuineZpCounting` over `CountingModel`) was
dropped by Asvin's 2026-08-13 redirect: there is no `CountingModel` in this repo, and its role
— "the model's counts are the genuine ones" — is now discharged by construction, because the
capstone statement quantifies over `genuineDensity` itself (post-P4; pre-P4 it quantified over
what is now `decidedDensity`, and the argument was the same).

---

## 7. WHAT THE FOLLOW-UP UNITS NEED FROM THIS ONE

* **The menu unit** consumes `decidedSet`/`decidedCount` and must produce, for each `(n, σ)`, a
  finite family of *shapes* whose counts sum to `decidedCount`. The interface it should target
  is `decidedCount O n σ N = ∑ T ∈ menu σ, stratumCount T N`, with `menu` independent of `O`.
* **The rationality unit** consumes `genuineDensity` (or `decidedDensity`, then transfers via
  drainage) and `residueCard`, and must produce `num, den : Polynomial ℚ` with the Statement's
  ∃-before-∀ shape. Note `card_res` is what licenses writing the denominator as `q^(nN)`.
  Post-P4 it has a choice of target: proving `UniformityStatementDecided` needs no drainage but
  is not the headline claim; proving `UniformityStatement` is the headline claim and, at every
  `n` where drainage is open, must be reached directly over the outer limit rather than by
  transfer.
* ~~**The drainage unit**~~ — **DONE at `n = 2`** (UNIFORMITY-P2). What a *general-`n`* drainage
  unit should copy: the shape `T(a) < N ⟹ decided` + `#{T ≥ N}` small is not specific to
  degree 2. The general invariant is the Okutsu–Montes depth (how far the recursive read gets
  before the window runs out); the two things that made `n = 2` cheap are (i) the polygon has at
  most two sides, so the trichotomy is finite and explicit, and (ii) a refinement step provably
  *increases* `min(v(F), 2v(F'))`, which is what kills the fourth case without a termination
  argument. At `n ≥ 3` the analogue of (ii) is the statement that a refinement raises the
  Okutsu depth — that is the thing to isolate first.
* ~~**`typeOf_degree` (open item 1)**~~ — **DONE** (UNIFORMITY-P2). `σ.degree = n` is now a live
  hypothesis in the capstone statement.
* **The remaining `n = 2` work is the two statements in STATUS item 5a** (split = inert; the
  exact ram value). Everything else at `n = 2` is closed.


**STATUS 5a doc update (2026-08-13, orchestrator, doc-only):** both named statements (`split_eq_inert_decidedDensity_two`, `ram_decidedDensity_two`) are now PROVED at general O — in `leancheck/UniformityCheck/` (N2Exact + Counting), kept out of this repo per the check/final separation directive; exact values ram = 1/(q+1), split = inert = q/(2(q+1)), cross-checked inside this repo's G8 brackets. The two n=2 rows of STATUS above are therefore CLOSED (externally).

---

## 8. THE `genuineDensity` REWIRE — unit UNIFORMITY-P4, 2026-08-13

**Charge.** Asvin, 2026-08-13, question 5 of the morning list: *"Let us define `genuineDensity`
using the limit of the proportion (proven to equal the decided proportion) and let us prove
that `Σ_σ R_σ = 1` using this definition."* This is an **Asvin-signed statement change**: the
name `genuineDensity` moves from one proved limit to the other, and every downstream statement
is re-keyed.

**One-paragraph summary.** `genuineDensity O n σ` is now `⨅_N possibleSeq O n σ N` — the limit
of the proportion of level-`N` coefficient classes *consistent with* type σ. The old
`genuineDensity` (`⨆_N decidedSeq`, the certified inner limit) is now `decidedDensity`; the old
`upperDensity` name is retired. Nothing numeric changed anywhere: at `n = 1` and `n = 2` the two
limits are **equal by a theorem**, so every landed value and bracket transfers verbatim. Both
repos build green, zero `sorry`s, Lean-core footprints throughout.

### 8.1 The rename map

| pre-rewire | post-rewire | what it is |
|---|---|---|
| `genuineDensity` | **`decidedDensity`** | `⨆ N, decidedSeq O n σ N` — certified inner limit |
| `upperDensity` | **`genuineDensity`** | `⨅ N, possibleSeq O n σ N` — **THE density** (outer) |
| `decidedSeq_le_genuineDensity` | `decidedSeq_le_decidedDensity` | |
| `upperDensity_le_possibleSeq` | `genuineDensity_le_possibleSeq` | |
| `genuineDensity_nonneg` / `_le_one` | `decidedDensity_nonneg` / `_le_one` | |
| `upperDensity_nonneg` / `_le_one` | `genuineDensity_nonneg` / `_le_one` | |
| `genuineDensity_le_upperDensity` | `decidedDensity_le_genuineDensity` | the sandwich |
| `upperDensity_eq_of_drainage` | `genuineDensity_eq_of_drainage` | **the tie** |
| `drainage_of_upperDensity_eq` | `drainage_of_genuineDensity_eq` | its converse |
| `sum_genuineDensity_le_one` | `sum_decidedDensity_le_one` | `≤ 1`, inner only |
| `genuineDensity_le_of_others` | `decidedDensity_le_of_others` | |
| `upperDensity_eq_two` | `genuineDensity_eq_decidedDensity_two` | the `n = 2` tie |
| `sum_three_densities_eq_one` | `sum_three_decidedDensities_eq_one` | inner version |
| *(new)* | `sum_three_densities_eq_one` | **the same identity over THE density** |
| `upperDensity_three_le` (leancheck) | `genuineDensity_three_le` | the `n = 3` `1/q²` closure |
| `upperDensity_three_padic_two/_three` | `genuineDensity_three_padic_two/_three` | |
| `genuineDensity_ge_of_decided` | `decidedDensity_ge_of_decided` | |
| `genuineDensity_ge_of_inj` (leancheck) | `decidedDensity_ge_of_inj` | |
| `genuineDensity_of_census` (leancheck) | `decidedDensity_of_census` | |

**Naming convention now in force.** *The unsuffixed name always states the fact about THE
density `genuineDensity`. The `_decided` suffix marks the certified-density version that the
proof route actually goes through.* Where a gate could not be stated over `genuineDensity` in
the file that proves it (because `drainage_two` lives further down the import graph), the
`_decided` version stays where it is and the unsuffixed twin appears in `Drainage.lean` §9.
`Gates.lean` `n = 2` names renamed accordingly: `gate_split_lower_decided`,
`gate_split_lower_sharp_decided`, `gate_ram_lower_decided`, `gate_padic_two_decided`,
`gate_sigma_separation_two_decided`, `bracket_two_decided`, `lowers_padic_two_decided`,
`lowers_padic_three_decided`, `gate_bracket_padic_two_decided`,
`gate_bracket_padic_three_decided`. Likewise in `leancheck/N2Exact.lean`:
`ram_decidedDensity_two`, `inert_decidedDensity_two`, `split_decidedDensity_two`,
`split_eq_inert_decidedDensity_two`, `decidedDensity_two_exact`,
`decidedDensity_two_padic_two/_three`.

### 8.2 New declarations (all in `GenuineDensity.lean` §7 and `Statement.lean`)

```lean
def CoveringMenu (n : ℕ) (S : Finset FactorizationType) : Prop :=
  ∀ a : Fin n → O, typeOf (monicPoly a) ∈ S

theorem card_le_sum_possibleCount (h : CoveringMenu O n S) (N : ℕ) :
    residueCard O ^ (n * N) ≤ ∑ σ ∈ S, possibleCount O n σ N
theorem one_le_sum_possibleSeq (h : CoveringMenu O n S) (N : ℕ) :
    1 ≤ ∑ σ ∈ S, possibleSeq O n σ N
theorem one_le_sum_genuineDensity (h : CoveringMenu O n S) :
    1 ≤ ∑ σ ∈ S, genuineDensity O n σ                              -- UNCONDITIONAL
theorem sum_genuineDensity_eq_one_of_drainage (h : CoveringMenu O n S)
    (hd : ∀ σ ∈ S, UndecidedVanishes O n σ) : ∑ σ ∈ S, genuineDensity O n σ = 1
theorem sum_decidedDensity_eq_one_of_drainage (...) : ∑ σ ∈ S, decidedDensity O n σ = 1

def DrainageAt (n : ℕ) : Prop                                       -- Statement.lean
def UniformityStatementDecided : Prop                               -- Statement.lean
def TotalMassOne : Prop                                             -- Statement.lean, NOT proved
theorem totalMassOne_of_drainage (hd : ∀ n, DrainageAt n) : TotalMassOne
theorem UniformityStatement.ofDecided / .toDecided                  -- cross-implications
```

Plus, at `n = 1` (`Gates.lean`): `possibleSet_one`, `possibleSeq_eq_decidedSeq_one`,
**`drainage_one`**, `genuineDensity_eq_decidedDensity_one`, `totalMass_one`. At `n = 2`
(`Drainage.lean` §9): `coveringMenu_two`, **`totalMass_two`**.

Faithfulness paragraphs for `genuineDensity`, `decidedDensity` and `CoveringMenu` are in §2.3
above (they are the Asvin-reviewed core set for this unit); the two new capstone `Prop`s and
`TotalMassOne` are in §2.5 and §8.4.

### 8.3 Re-keyed theorems (counts per file)

| file | re-keyed to `genuineDensity` | left on `decidedDensity` (with reason) |
|---|---|---|
| `leanfinal/Gates.lean` | 3 re-keyed at `n = 1` (`genuineDensity_linear_eq_one`, `genuineDensity_one_of_ne`, `gate_sigma_separation_one`) + 5 new (`possibleSet_one`, `possibleSeq_eq_decidedSeq_one`, `drainage_one`, `genuineDensity_eq_decidedDensity_one`, `totalMass_one`) | all 10 `n = 2` gates — the file cannot see `drainage_two` |
| `leanfinal/Drainage.lean` §9 | 16 (`genuineDensity_two_linType_eq_zero`, `genuineDensity_two_eq_zero`, `gate_split_lower`, `gate_split_lower_sharp`, `gate_ram_lower`, `gate_sigma_separation_two`, `bracket_two`, `sum_three_densities_eq_one`, `coveringMenu_two`, `totalMass_two`, `density_two_summary`, `gate_padic_two`, `lowers_padic_two`, `lowers_padic_three`, `gate_bracket_padic_two`, `gate_bracket_padic_three`) | the `_decidedDensities` route lemmas |
| `leanfinal/Statement.lean` | `UniformityStatement`, `UniformityStatementPadic` | `UniformityStatementDecided` (deliberately) |
| `leancheck/N2Exact.lean` | 7 (`ram_density_two`, `inert_density_two`, `split_density_two`, `split_eq_inert_two`, `density_two_exact`, `density_two_padic_two`, `density_two_padic_three`) | the census route (`*_decidedDensity_two`) |
| `leancheck/N3Exact.lean` | 6 NEW honest `n = 3` statements (see §8.5) | all five `n = 3` gates and both brackets |

**Nothing was left on `decidedDensity` for want of new mathematics at `n = 2`** — the tie is
unconditional there, so the transfer is a rewrite in every case. At `n = 3` the situation is
genuinely different and is recorded honestly in §8.5.

### 8.4 `Σ_σ R_σ = 1` — the honest status, in four lines

1. **`≥ 1` is UNCONDITIONAL** at every `n`, for any covering menu: `one_le_sum_genuineDensity`.
   Reason: every class has a lift, the lift has a type, so the σ-possible sets cover every box
   at every level. This is a direction the *inner* density can never have.
2. **`= 1` is proved at every `n` GIVEN drainage** at each type of the menu:
   `sum_genuineDensity_eq_one_of_drainage`. Drainage is spent turning each outer density into
   the inner one, whose distinct types are disjoint.
3. **`= 1` is UNCONDITIONAL at `n = 1` and `n = 2`**, because drainage is a theorem there:
   `totalMass_one`, `totalMass_two`, and concretely
   `sum_three_densities_eq_one : genuineDensity O 2 split + inert + ram = 1` for every complete
   DVR with finite residue field.
4. **General `n` is NOT proved and is NOT sorried.** It is the named `Prop` `TotalMassOne` in
   `Statement.lean`, with `totalMassOne_of_drainage` recording that general-`n` drainage buys it
   outright. So `Σ_σ R_σ = 1` at general `n` *is* the general-`n` drainage leg, i.e. the open
   order-≥2 Okutsu–Montes frontier. Do not record it as done.

### 8.5 `n = 3`: what transferred and what did not

Lower bounds transfer **for free** (`decidedDensity ≤ genuineDensity` at every `n`):
`lowers_three_genuine` gives all five certified `n = 3` lower bounds over THE density, general
`O`, unconditionally. Upper bounds do **not** transfer: they come from
`sum_decidedDensity_le_one`, an inner-density statement. What is available is the `n = 3`
partial-drainage theorem `genuineDensity_three_le : genuineDensity O 3 σ ≤ decidedDensity O 3 σ
+ 1/q²`, so a certified upper bound `u` becomes `u + 1/q²` over THE density
(`genuine3_bracket_of_decided`). The concrete brackets widen accordingly and the HMENU3
predicted values still sit inside all ten:

| type | `q = 2` genuine bracket | HMENU3 | `q = 3` genuine bracket | HMENU3 |
|---|---|---|---|---|
| `c3split` | `[1/512, 5/8]` | `4/93 ≈ 0.043` ✓ | `[1/27, 11/27]` | `63/968 ≈ 0.065` ✓ |
| `c3linInert` | `[1/4, 447/512]` | `28/93 ≈ 0.301` ✓ | `[1/3, 19/27]` | `351/968 ≈ 0.363` ✓ |
| `c3inert` | `[1/4, 447/512]` | `8/31 ≈ 0.258` ✓ | `[8/27, 2/3]` | `36/121 ≈ 0.298` ✓ |
| `c3linRam` | `[1/16, 351/512]` | `22/93 ≈ 0.237` ✓ | `[4/81, 34/81]` | `93/484 ≈ 0.192` ✓ |
| `c3ram` | `[1/16, 351/512]` | `5/31 ≈ 0.161` ✓ | `[2/81, 32/81]` | `10/121 ≈ 0.083` ✓ |

(`gate_bracket3_padic_two_genuine`, `_three_genuine`, `gate_bracket3_hmenu3_two_genuine`,
`_three_genuine`.) **Closing the `+ 1/q²` is exactly the open `n = 3` drainage problem — do not
quietly drop it.**

### 8.6 Build, axioms, `sorry`s

* `leanfinal`: `lake build` **green**, 8 568 jobs. 70 `#print axioms` lines, **every one**
  `[propext, Classical.choice, Quot.sound]`.
* `leancheck`: `lake build` **green**, 8 590 jobs. 140 `#print axioms` lines, **every one**
  `[propext, Classical.choice, Quot.sound]`.
* `grep -rn sorry` over both `Uniformity/` and `UniformityCheck/` returns only the word inside
  docstrings (two hits, both prose). **Zero landed `sorry`s, zero declared axioms.**

New footprints checked this unit (all Lean core): `drainage_of_genuineDensity_eq`,
`one_le_sum_possibleSeq`, `one_le_sum_genuineDensity`, `sum_genuineDensity_eq_one_of_drainage`,
`sum_decidedDensity_eq_one_of_drainage`, `totalMassOne_of_drainage`,
`UniformityStatement.ofDecided`, `UniformityStatement.toDecided`, `drainage_one`,
`genuineDensity_eq_decidedDensity_one`, `genuineDensity_linear_eq_one`,
`genuineDensity_one_of_ne`, `totalMass_one`, `genuineDensity_two_linType_eq_zero`,
`genuineDensity_two_eq_zero`, `gate_split_lower`, `gate_split_lower_sharp`, `gate_ram_lower`,
`gate_sigma_separation_two`, `bracket_two`, `sum_three_densities_eq_one`, `coveringMenu_two`,
`totalMass_two`, `density_two_summary`, `gate_padic_two`, `lowers_padic_two`,
`lowers_padic_three`, `gate_bracket_padic_two`, `gate_bracket_padic_three`; and in `leancheck`:
`ram_density_two`, `inert_density_two`, `split_density_two`, `split_eq_inert_two`,
`density_two_exact`, `density_two_padic_two`, `density_two_padic_three`,
`genuine3_bracket_of_decided`, `lowers_three_genuine`, `gate_bracket3_padic_two_genuine`,
`gate_bracket3_padic_three_genuine`, `gate_bracket3_hmenu3_two_genuine`,
`gate_bracket3_hmenu3_three_genuine`.

### 8.7 What a reader of the earlier sections must know

Sections 1–7 above were written pre-rewire and have been mechanically re-keyed to the new
names, so they describe the current code. Two places where the *prose* deserves care: §1's
"Without drainage, `decidedDensity` is a certified lower bound and `genuineDensity` a certified
upper bound" is still exactly right (it was always about the two limits, not the names); and
§3B.4's caveat about the Haar-measure bridge is unchanged in force — see the amendment box
appended there.
