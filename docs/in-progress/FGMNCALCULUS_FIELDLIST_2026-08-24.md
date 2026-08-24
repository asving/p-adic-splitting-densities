# U7 — `FGMNCalculus` field-list audit

Date: 2026-08-24  
Status: unsigned research draft  
Scope: chapter C, especially C.83, C.88–C.92 and C.99–C.104

## 1. Verdict

There are two different questions hidden in “the `FGMNCalculus` field list.” They have different
answers.

1. A **consumer-typing field list** exists and is small. Seven projected accessors type every
   current occurrence of `FGMNCalculus`; two unprojected key-chain laws complete the structural
   dictionary. The provisional class at lines 1321–1375 already has those nine fields, and
   `lake build Leanspec.ChapC` succeeds. Three further scope predicates are needed before the
   source laws can be stated faithfully.
2. A **cited-clause-complete field list**, in the sense promised by the blueprint's §10 design
   note (“one field per consumed cited clause”), does **not** yet exist in the corpus vocabulary.
   The missing pieces are not cosmetic. Published Corollary 6.3 needs Newton polygons, side
   lengths, root evaluations and the actual MacLane valuation; published Proposition 1.12 and
   Theorem 4.3 need the graded algebra and its evaluation map. None of these is a field of
   `DeepTower`. Adding opaque predicates for them would manufacture a vacuous interface, not
   port the cited results.

Accordingly, the exact recommendation is:

- retain `FGMNCalculus` only as an explicit **hypothesis carrier**;
- land the consumer-typing kernel below;
- add only the source laws whose types are stated below and whose dictionary obligations are
  discharged;
- do **not** declare the old unconditional `fgmn_calculus_exists` axiom;
- keep the four source/dictionary gaps in §8 as `OPEN` obligations.

This agrees with the repository's later A-C.6 disposition, even though the older C.92 prose and
the statement of this unit still describe `fgmn_calculus_exists` as a gate-(b) target. The live
blueprint and leanspec now retire that axiom after
`leanfinal/Uniformity/ChapC/C92_VACUITY.lean.txt` constructs a junk instance in Lean core.

## 2. Sources and numbering

Primary source checked:

- J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane valuations*,
  J. Algebra 427 (2015), 30–75, DOI 10.1016/j.jalgebra.2014.12.022.
- Repository author PDF:
  `docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`, SHA-256
  `33b849ce6784f4bad8368d83b5b725b4545eebdd79918e3ee5dfafd1791daeda`.
- ArXiv v3 comparison copy:
  `docs/references/fgmn_residual_ideals_1305.0775v3.pdf`, SHA-256
  `651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35`.

Secondary source pool inspected:

- `docs/references/montes-blueprint.pdf`, SHA-256
  `b104b2714da51421373db10c37e71ebe57b65b22d1d7ea93d4cb0d95c2a9c3d1`;
- `docs/references/HigherNewton.tex`, SHA-256
  `8253d4d62cf3d180567d5e41429fdb0e4875abdc5d58db595dc66a24fb16bd18`.

Neither secondary source contains literal labels `[Q1]`–`[Q10]`. Those labels are local labels in
`lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md`; all ten quoted loci there are in the FGMN
paper. The Montes/HigherNewton sources support the tower/type dictionary, but they do not turn
`keyAt_one` or the `DeepTower`–MacLane identification into a cited FGMN theorem.

The later author PDF has the numbering used by the published article. The repository's `[Q]`
labels were assigned to arXiv-v3 numbers. The relevant map is:

| label | arXiv-v3 locus | published locus | content actually available |
|---|---|---|---|
| Q1 | Lemma 1.11 | Lemma 1.8 | every key polynomial is irreducible in `K_v[x]` |
| Q2 | Corollary 1.13 | Corollary 1.10 | `KP(μ) ⊂ O[x]` |
| Q3 | Definition 5.2 | Definition 5.4 | definition of a one-sided Newton polygon |
| Q4 | Lemma 5.3 | Lemma 5.2 | two-branch key-polynomial criterion; branch (2) gives the degree and residual conditions |
| Q5 | Corollary 4.12 | construction in the proof of Theorem 5.7, using Corollary 4.6 | prescribed monic residual polynomial can be realized |
| Q6 | proof of Theorem 5.8 | proof of Theorem 5.7 | the degree-forcing inequality used to enter Lemma 5.2(2) |
| Q7 | Proposition 5.7 and equation (14) | Proposition 5.6 and equation (11) | five equivalences for key polynomials; residual of powers of the last key |
| Q8 | Corollary 4.7 | Corollary 4.12 | graded additivity, restricted graded multiplicativity, and multiplicativity of normalized residuals |
| Q9 | Theorem 6.3 | Theorem 6.2 | prime-polynomial/key certificate and the top one-sided polygon |
| Q10 | Corollary 6.4 | Corollary 6.3 | level-general one-sidedness, exact intermediate root values, residual powers, and length recurrence |

The additional design-note citations also drift:

| design-note citation | published locus |
|---|---|
| Proposition 1.15 | Proposition 1.12 |
| Definition 1.8 | Definition 1.6 |
| Corollary 4.4 | Corollary 4.9 |
| Theorem 4.8 | Theorem 4.3 |
| Lemma 3.17 | Lemma 3.14 |
| Proposition 1.9 | Proposition 1.7 |
| Definition 3.12's `γ_i` recursion | the displayed recursion in published §3.3 immediately before Lemma 3.11; it is no longer a numbered definition |

Two naming cautions matter for the Lean interface.

- FGMN's `γ_i` is a value-zero rational function. The residue-field letter is `z_i`, the image
  of `y_i = H_{μ_i}(γ_i)`. Thus `letterZ` is a `z_i` carrier, not a `γ_i` carrier.
- FGMN's `R_{r,α}` is polynomial-valued in `F_r[y]`. The provisional `Rgr` is scalar-valued in
  `W.fld r`. It can port a coefficient/degree-zero specialization of `R_{r,α}`, but it is not
  literally that operator. Every source law for `Rgr` therefore needs the scalar-specialization
  lemma stated explicitly.

## 3. The consumer-typing kernel

The following is the complete field list required merely to elaborate every current consumer.
No cited theorem is smuggled into this block; it contains carriers and chain dictionary data.

```lean
namespace Uniformity.Density.Tower

class FGMNCalculus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i

  ExactGrade : ℕ → Polynomial O → Prop
  AboveGrade : ℕ → Polynomial O → Prop
  PrevGrade : ℕ → Prop
  ScalarAt : ℕ → Polynomial O → Prop

  Rgr : ℕ → Polynomial O → W.fld r
  Rres : Polynomial O → Polynomial (W.fld r)
  KP : Polynomial O → Prop
  nuEquiv : Polynomial O → Polynomial O → Prop
  letterZ : ℕ → W.fld r

end Uniformity.Density.Tower
```

`AboveGrade`, `PrevGrade`, and `ScalarAt` are not used by extant signatures. They are the least
scope carriers needed to state, respectively, published Lemma 3.14, the `β ∈ Γ_{r-1}` hypothesis
of Corollary 4.12(2), and nonvanishing of the scalar coordinate without claiming that every
exact-grade residual polynomial is constant.

### 3.1 Field provenance and faithfulness

| field | Lean type | cited source | faithfulness |
|---|---|---|---|
| `keyAt` | `ℕ → Polynomial O` | FGMN Definition 3.1 and published §3.2 | Carries the MacLane keys `φ_i`. Totality outside `1 ≤ i ≤ r` is the corpus junk-total convention, not a source assertion. |
| `keyAt_one` | `keyAt 1 = F.key` | Montes/HigherNewton tower dictionary; FGMN Definition 3.1 only supplies the first MacLane key abstractly | This is a repo-to-source dictionary equality. It is not proved by FGMN alone. Its existence obligation is `OPEN-DICT-1`. |
| `keyAt_deg` | `∀ i, 1 ≤ i → i ≤ r → ... = W.Dcum i` | FGMN published §3.2, equation (7), `m_i = e_{i-1}f_{i-1}m_{i-1}` | The source degree recurrence is exact. Identifying its product with `W.Dcum` uses the chapter-C index dictionary and is `OPEN-DICT-1`. |
| `ExactGrade` | `ℕ → Polynomial O → Prop` | FGMN §1.1, `P_α \ P_α⁺`, and Definitions 3.13/3.15 | Intended meaning is “the cleared value is exactly `β`.” The conversion from rational `μ`-values to `ℕ` is not represented in `DeepTower`; `OPEN-DICT-2`. |
| `AboveGrade` | `ℕ → Polynomial O → Prop` | FGMN §1.1, `P_α⁺` | Intended meaning is strict inequality after the same clearing. It must not be defined independently of `ExactGrade`; `OPEN-DICT-2`. |
| `PrevGrade` | `ℕ → Prop` | FGMN published §3.2, the groups `Γ_i`, and Corollary 4.12(2) | Means that the cleared grade comes from the preceding value group. Omitting it turns Corollary 4.12(2) into a stronger statement than the source; `OPEN-DICT-2`. |
| `ScalarAt` | `ℕ → Polynomial O → Prop` | FGMN Definition 3.13 and Corollary 4.9(2) | Means that the relevant `R_{r,β}(g)` has only its degree-zero coordinate. Exact grade alone does not imply this. Its intended low-degree/single-point instances are `OPEN-DICT-3`. |
| `Rgr` | `ℕ → Polynomial O → W.fld r` | FGMN Definition 3.13 and Theorem 4.1, after taking the degree-zero/scalar coordinate | The codomain is scalar, while the source operator is in `F_r[y]`. A scalar-specialization theorem and the equivalence `W.fld r ≃ F_r` are required; `OPEN-DICT-3`. |
| `Rres` | `Polynomial O → Polynomial (W.fld r)` | FGMN Definition 3.15 | This is the normalized residual polynomial `R_r`, after transporting coefficients along `W.fld r ≃ F_r`; that equivalence is part of `OPEN-DICT-3`. |
| `KP` | `Polynomial O → Prop` | FGMN §1.2, definition of key polynomial | Restricting the domain to `O[x]` builds Q2/published Corollary 1.10 into the carrier. It does not encode monicity or irreducibility by itself; those remain law fields. |
| `nuEquiv` | `Polynomial O → Polynomial O → Prop` | FGMN Definition 1.2 | Intended to be equality of initial forms. Without an actual graded-algebra carrier this is abstract and must be tied to the realization; `OPEN-DICT-3`. |
| `letterZ` | `ℕ → W.fld r` | FGMN published §3.3, paragraph defining `z_i` from `y_i = H_{μ_i}(γ_i)` | This transports the source letters to the terminal residue field. The embeddings of lower `F_i` into the terminal field are not carried by `DeepTower`; `OPEN-DICT-4`. |

## 4. Source-law fields that can be stated in the present vocabulary

Subject to the four dictionary obligations in §8, the following fields are the conservative law
layer. Append exactly these signatures to the carrier block of §3; the union is the recommended
class field list. They replace the seven provisional law fields. The comments give the exact
source and the specialization being taken.

```lean
class FGMNCalculus -- same parameters and carrier fields as in §3
    where
  -- ... carrier fields from §3 ...

  /-- Published Lemma 3.14: the graded residual vanishes above the grade. -/
  Rgr_zero_of_above : ∀ β (g : Polynomial O),
    AboveGrade β g → Rgr β g = 0

  /-- Published Corollary 4.12(1), followed by scalar-coordinate projection. -/
  Rgr_add : ∀ β (g h : Polynomial O),
    ExactGrade β g → ExactGrade β h → ExactGrade β (g + h) →
      Rgr β (g + h) = Rgr β g + Rgr β h

  /-- Published Corollary 4.12(2), not item (3), after cleared-grade and
  scalar-coordinate specialization. -/
  Rgr_mul : ∀ β β' (g h : Polynomial O),
    ExactGrade β g → ExactGrade β' h → PrevGrade β' →
      ExactGrade (β + β') (g * h) ∧
      Rgr (β + β') (g * h) = Rgr β g * Rgr β' h

  /-- Theorem 4.1 plus published Corollary 4.9(1), in the scalar/single-point scope. -/
  Rgr_ne_zero : ∀ β (g : Polynomial O),
    ExactGrade β g → ScalarAt β g → g ≠ 0 → Rgr β g ≠ 0

  /-- Published Corollary 4.12(3): multiplicativity of normalized residuals. -/
  Rres_mul : ∀ g h : Polynomial O,
    Rres (g * h) = Rres g * Rres h

  /-- Published Definition 1.6 (expansion minimum), Definition 3.13,
  equation (11), and Corollary 4.12(1),(2): the recipe expansion. -/
  Rres_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
    Rres ((keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' -
        ∑ t ∈ Finset.range f',
          Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t

  /-- Q5: published Theorem 5.7 proof, using Corollary 4.6. -/
  Rres_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O,
        g.Monic ∧
        g.natDegree = e' * f' * (keyAt r).natDegree ∧
        Rres g = ψ

  /-- Q4+Q6: published Lemma 5.2(2), Corollary 4.9, and the
  degree-forcing display in the proof of Theorem 5.7. -/
  KP_criterion : ∀ g : Polynomial O,
    g.Monic →
    g.natDegree = e' * f' * (keyAt r).natDegree →
    Irreducible (Rres g) →
    (Rres g).natDegree = f' →
    (Rres g).coeff 0 ≠ 0 →
      KP g

  /-- Q1+Q2: published Lemma 1.8 and Corollary 1.10, followed by
  the monic Gauss transport from `K_v[x]` to `O[x]`. -/
  KP_irred : ∀ g : Polynomial O, KP g → g.Monic → Irreducible g

  /-- Published Proposition 1.7(4), equivalently Lemma 5.2(1), for
  the last live MacLane key. -/
  KP_keyAt : 0 < r → KP (keyAt r)

  /-- Q7, published equation (11); the `0 < r` fence is essential. -/
  Rres_keyAt : 0 < r → Rres (keyAt r) = 1

  /-- Q7, published Proposition 5.6(2)↔(3). -/
  nuEquiv_iff_Rres : ∀ g h : Polynomial O,
    KP g → KP h → (nuEquiv g h ↔ Rres g = Rres h)

  /-- Published §3.3: `z_i ≠ 0` for positive live indices. -/
  letterZ_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0
```

### 4.1 Law-field provenance and faithfulness

| field | source | faithfulness/status |
|---|---|---|
| `Rgr_zero_of_above` | published Lemma 3.14 | Exact after transporting `P_α⁺` to `AboveGrade` and projecting the zero residual polynomial to its scalar coordinate. |
| `Rgr_add` | published Corollary 4.12(1) | A restriction of the polynomial identity to exact-grade inputs and then to the scalar coordinate; no stronger claim is made when the sum moves above grade. |
| `Rgr_mul` | published Corollary 4.12(2) | `PrevGrade β'` preserves the source's `β ∈ Γ_{r-1}` hypothesis. The provisional citation to item (3) is incorrect. |
| `Rgr_ne_zero` | published Theorem 4.1 and Corollary 4.9(1) | `ScalarAt` is essential: a nonzero residual polynomial may have zero constant coefficient. Exact only in the scalar/single-point scope. |
| `Rres_mul` | published Corollary 4.12(3) | Direct transport of normalized residual-polynomial multiplicativity. |
| `Rres_recipe` | published Definition 1.6, Definition 3.13, equation (11), Corollary 4.12(1),(2) | This is the exact consumed finite-sum specialization, assuming the grade and index dictionaries. It is not Proposition 5.6. |
| `Rres_exists` | Q5; published proof of Theorem 5.7 using Corollary 4.6 | Exact at positive depth after resolving whether `(e',f',u')` is the source's last or next augmentation data. Until then: `OPEN-INDEX`. |
| `KP_criterion` | Q4+Q6; published Lemma 5.2(2), Corollary 4.9, proof of Theorem 5.7 | The extra nonzero-constant hypothesis exposes a source invariant that the provisional type hid. Exact after `Rres_recipe` supplies it for recipe keys. |
| `KP_irred` | Q1+Q2; published Lemma 1.8 and Corollary 1.10 | Source conclusion is over `K_v[x]`; the displayed conclusion over `O[x]` additionally needs Gauss. `OPEN-GAUSS`. |
| `KP_keyAt` | published Proposition 1.7(4), or Lemma 5.2(1) | Exact for the last live key, subject to the class's unresolved index convention. |
| `Rres_keyAt` | Q7, published equation (11) | Exact for positive depth. The `0 < r` fence prevents the different `r = 0` behavior. |
| `nuEquiv_iff_Rres` | Q7, published Proposition 5.6(2)↔(3) | Exact only under both `KP` hypotheses, which the field retains. |
| `letterZ_ne_zero` | published §3.3 following Lemma 3.11 | Exact for positive letters that are defined by a following augmentation. Whether `i = r` is live is part of `OPEN-INDEX`. |

### 4.2 Corrections to the provisional law fields

`Rgr_mul` must cite published Corollary 4.12(2). Item (3) is the law for the normalized,
polynomial-valued `Rres`; it does not directly type the scalar `Rgr` multiplication. The
provisional class cites item (3), so its docstring is wrong even if its intended specialization is
mathematically valid.

`Rgr_ne_zero` is not published Corollary 4.9(3) by itself. Item (3) says that the normalized
residual has the stated degree and nonzero constant coefficient. Nonvanishing of an exact-grade
graded residual comes from Theorem 4.1 and Corollary 4.9(1), with the scalar/single-point scope
made explicit.

`Rres_recipe` is not a consequence of published Proposition 5.6. Proposition 5.6 concerns
equivalence classes of key polynomials. The recipe equality is assembled from the augmented
valuation minimum, the definition of `R_{r,α}`, equation (11), and additivity/multiplicativity.

`Rres_keyAt` comes from equation (11), not Theorem 6.2. Theorem 6.2 is a root-evaluation and
Newton-polygon theorem for a prime polynomial `F`; invoking it for this elementary residual
identity is both unnecessary and index-obscuring.

`KP_irred` is the only field above whose displayed Lean conclusion is not verbatim from one
source clause. FGMN proves irreducibility in `K_v[x]` and integrality of coefficients. The
displayed `Irreducible g` is over `O[x]`; the monic Gauss transport must be a Lean theorem in the
ambient library. Until that theorem and all coercions are checked at the actual coefficient field,
this field is `OPEN-GAUSS`, not signed.

### 4.3 Assembled class signature

For avoidance of doubt, this is the complete union of §§3–4 in one copyable declaration. It is a
type-checked candidate, not a signed claim that the `OPEN` dictionaries exist.

```lean
namespace Uniformity.Density.Tower

class FGMNCalculus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i

  ExactGrade : ℕ → Polynomial O → Prop
  AboveGrade : ℕ → Polynomial O → Prop
  PrevGrade : ℕ → Prop
  ScalarAt : ℕ → Polynomial O → Prop

  Rgr : ℕ → Polynomial O → W.fld r
  Rres : Polynomial O → Polynomial (W.fld r)
  KP : Polynomial O → Prop
  nuEquiv : Polynomial O → Polynomial O → Prop
  letterZ : ℕ → W.fld r

  Rgr_zero_of_above : ∀ β (g : Polynomial O),
    AboveGrade β g → Rgr β g = 0
  Rgr_add : ∀ β (g h : Polynomial O),
    ExactGrade β g → ExactGrade β h → ExactGrade β (g + h) →
      Rgr β (g + h) = Rgr β g + Rgr β h
  Rgr_mul : ∀ β β' (g h : Polynomial O),
    ExactGrade β g → ExactGrade β' h → PrevGrade β' →
      ExactGrade (β + β') (g * h) ∧
      Rgr (β + β') (g * h) = Rgr β g * Rgr β' h
  Rgr_ne_zero : ∀ β (g : Polynomial O),
    ExactGrade β g → ScalarAt β g → g ≠ 0 → Rgr β g ≠ 0
  Rres_mul : ∀ g h : Polynomial O,
    Rres (g * h) = Rres g * Rres h
  Rres_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
    Rres ((keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' -
        ∑ t ∈ Finset.range f',
          Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
  Rres_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O,
        g.Monic ∧
        g.natDegree = e' * f' * (keyAt r).natDegree ∧
        Rres g = ψ
  KP_criterion : ∀ g : Polynomial O,
    g.Monic →
    g.natDegree = e' * f' * (keyAt r).natDegree →
    Irreducible (Rres g) →
    (Rres g).natDegree = f' →
    (Rres g).coeff 0 ≠ 0 →
      KP g
  KP_irred : ∀ g : Polynomial O, KP g → g.Monic → Irreducible g
  KP_keyAt : 0 < r → KP (keyAt r)
  Rres_keyAt : 0 < r → Rres (keyAt r) = 1
  nuEquiv_iff_Rres : ∀ g h : Polynomial O,
    KP g → KP h → (nuEquiv g h ↔ Rres g = Rres h)
  letterZ_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0

end Uniformity.Density.Tower
```

### 4.4 Design-note clause coverage

The blueprint's slogan “one field per clause” cannot be followed literally: Q2 is enforced by a
carrier type, Q4 and Q6 combine into one criterion, Q8 has three distinct laws, and several
clauses are not typeable. The exact coverage is:

| cited clause | class representation |
|---|---|
| Q1 / published Lemma 1.8 | `KP_irred` (`OPEN-GAUSS` for its `O[x]` conclusion) |
| Q2 / published Corollary 1.10 | `KP : Polynomial O → Prop` restricts the carrier to `O[x]`; also used in `KP_irred` |
| Q3 / published Definition 5.4 | `OPEN-POLYGON`; no field |
| Q4 / published Lemma 5.2 | `KP_criterion`, `KP_keyAt` |
| Q5 / published Theorem 5.7 construction | `Rres_exists` (`OPEN-INDEX`) |
| Q6 / published Theorem 5.7 degree-forcing display | `KP_criterion` |
| Q7 / published Proposition 5.6 and equation (11) | `nuEquiv_iff_Rres`, `Rres_keyAt` |
| Q8 / published Corollary 4.12 | `Rgr_add`, `Rgr_mul`, `Rres_mul` |
| Q9 / published Theorem 6.2 | `OPEN-ROOT-EVAL`; no field |
| Q10 / published Corollary 6.3 | `OPEN-LEVEL-GENERAL`; no field |
| published Proposition 1.12 | `OPEN-EVAL-ISO`; no field |
| published Definition 1.6 | `Rres_recipe` |
| published Corollary 4.9 | `ScalarAt`, `Rgr_ne_zero`, and the degree leg of `KP_criterion` |
| published Theorem 4.3 | `OPEN-EVAL-ISO`; no field |
| published Lemma 3.14 | `AboveGrade`, `Rgr_zero_of_above` |
| published Proposition 1.7 | `KP_keyAt`; item (2)'s dictionary use remains `OPEN-GRADE-STABILITY` |
| published §3.3 `γ_i,z_i` recursion | `letterZ`, `letterZ_ne_zero`, plus `OPEN-LETTERS` for the repo identification |

## 5. Clauses that must not be faked as fields

The following advertised design-note fields cannot yet be given faithful Lean types in the
current corpus vocabulary.

| clause | missing mathematical carrier | disposition |
|---|---|---|
| Q3 / published Definition 5.4 | `N_{μ,φ}(g)`, its distinguished side, endpoints `s,s'`, and slope | `OPEN-POLYGON`; do not replace it by an unconstrained `OneSided : Polynomial O → Prop`. |
| Q9 / published Theorem 6.2 | the inductive valuation `μ`, `μ`-divisibility, a root `θ` in an algebraic closure of the completion, evaluation valuation, Newton polygon and side length | `OPEN-ROOT-EVAL`. The special case `F = φ` does not supply the level-general data used later. |
| Q10 / published Corollary 6.3 | every truncated MacLane valuation, every intermediate key, polygons `N_i`, root values, `ℓ_i`, and residual fields at each level | `OPEN-LEVEL-GENERAL`. This is exactly C.90(b)'s booked field; `DeepTower` has no place to state it. |
| published Proposition 1.12 and Theorem 4.3 | `Gr(μ)`, `Δ(μ)`, the maps `Δ_i → Δ_{i+1}`, and the evaluation isomorphism to the residue field of a key root | `OPEN-EVAL-ISO`. This is the bridge used in the proof of C.100 and the letter formula, but it cannot be expressed by `ρ : W.fld 2 ≃+* AdjoinRoot T.ψ₂` alone. |
| published Proposition 1.7(2) | the actual pair of valuations before and after augmentation and `μ`-divisibility | `OPEN-GRADE-STABILITY`; ordinary polynomial divisibility by `keyAt r` is not a faithful substitute. |
| published §3.3 `γ_i,z_i` recursion | fraction-field rational functions, homogeneous initial forms, and embeddings of all `F_i` into the terminal field | `OPEN-LETTERS`; `letterZ` only supplies the final values after the missing transport. |

The two “booked residual fields” mentioned in the provisional class are therefore real missing
interface, not deferred proof details. Likewise C.91(c)'s level-entry characterization needs the
level-`i` valuation/polygon carrier and cannot be recovered from the scalar fields above.

## 6. Consumer-typing matrix

The matrix lists all sixteen consumer declarations in leanspec, not only C.99–C.101. “DT” means
a `DeepTower` field or definition, not an `FGMNCalculus` field.

| consumer | member occurrences | fields that type them | non-class typing facts |
|---|---|---|---|
| `FGMNCalculus.chainNorm` | `I.keyAt (j+1)` | `keyAt` | `W.towerNorm i k : ℕ × ℕ × (Fin i → ℕ)`; the product is in `Polynomial O`. |
| `FGMNCalculus.thetaRatio` | `I.Rgr ...`, `I.chainNorm ...` | `Rgr`, `keyAt` through `chainNorm` | `W.fld r` is a field via `DeepTower.fldField`, so multiplication, powers and inverse elaborate. |
| `gentow2_Bpp` | `Rgr`, `chainNorm`, `thetaRatio` | `Rgr`, `keyAt` | `W.Econst r : ℕ` is DT. Both sides lie in `W.fld r`. |
| `theta_letter_valued` | `thetaRatio`, `letterZ 1`, `letterZ 2` | `Rgr`, `keyAt`, `letterZ` | All terms lie in `W.fld r`; no embedding is needed merely to type the equality. |
| `gentow2_Bp` | `ExactGrade`, `Rgr`, `chainNorm` | `ExactGrade`, `Rgr`, `keyAt` | `ρ.symm : AdjoinRoot T.ψ₂ → (T.deepTower hπ).fld 2`; hence the product has the `Rgr` codomain. |
| `gentow2_Bp_unit_iff` | same as `gentow2_Bp` | `ExactGrade`, `Rgr`, `keyAt` | Same `ρ.symm` check; equality to `1` uses the field instance. |
| `gentow2_B` | `keyAt 2`, `Rres`, `Rgr`, `chainNorm` | `keyAt`, `Rres`, `Rgr` | `hkey` identifies `keyAt 2` with `composedKey T`; each coefficient is in `(T.deepTower hπ).fld 2`, so the sum is a polynomial over that field. |
| `letter_formula` | `letterZ 1`, `letterZ 2` | `letterZ` | `ρ.symm (AdjoinRoot.root T.ψ₂)` has type `(T.deepTower hπ).fld 2`. |
| `gentow2_A` | `keyAt 2`, `Rres`, `KP`, `nuEquiv` | `keyAt`, `Rres`, `KP`, `nuEquiv` | All polynomial arguments are in `Polynomial O`; `Rres` supplies the coefficient field for `Irreducible`. |
| `tower_slot_exact` | `ExactGrade`, `KP` | `ExactGrade`, `KP` | `W.Dcum r`, `W.ehat r : ℕ` are DT; `AdjoinRoot.mk g C` is well typed because `g,C : Polynomial O`. |
| `tower_lift` | `ExactGrade`, `Rgr` | `ExactGrade`, `Rgr` | `s : W.fld r`; `W.Dcum r` is DT. The equality `Rgr k C = s` is exact. |
| `GENTOW5W` | `Rgr`, `chainNorm`, `thetaRatio` | `Rgr`, `keyAt` | The witness `w` and both sides are in `W.fld r`. |
| `Wle` | the class at `W.trunc i hi` | the class itself | `DeepTower.trunc` sets `fld := W.fld` definitionally; the live call has terminal field `(W.trunc i hi).fld i = W.fld i`. |
| `gentow5w_two` | class argument passed to `GENTOW5W` | no additional accessor | `W.Econst 2` is DT. |
| `gentow5w_one_shape` | `Rgr`, `chainNorm`, `thetaRatio`, `letterZ 1` | `Rgr`, `keyAt`, `letterZ` | Both sides lie in `W.fld 1`. |
| `gentow5_key_certificate` | `(I r le_rfl).Rres`, `.KP` | `Rres`, `KP` | `W.Dcum r`, `W.Econst r` are DT. Since `trunc` preserves `fld`, `Rres Φnext` and `wconj w ψ'` are both in `Polynomial ((W.trunc r le_rfl).fld r)`. |

### 6.1 Accessor census

The actual accessor dependency set of the sixteen signatures is exactly:

```text
keyAt, ExactGrade, Rgr, Rres, KP, nuEquiv, letterZ
```

`keyAt_one` and `keyAt_deg` are structural chain laws but no present consumer signature projects
them. `AboveGrade` and every law field in §4 are proof-facing rather than signature-facing.

The `W.Dcum`, `W.Econst`, `W.ehat`, `W.towerNorm`, `W.fld` and `W.trunc` names are all provided by
C.83's `DeepTower`; they must not be duplicated in `FGMNCalculus`.

### 6.2 Hand-elaboration checks

The following potentially fragile unifications were checked.

1. `thetaRatio` elaborates because `DeepTower.fldField` is registered as an instance.
2. At depth two, `Rgr` and `letterZ` have codomain `(T.deepTower hπ).fld 2`, exactly the domain
   of `ρ`; `ρ.symm` is oriented correctly.
3. `Rres (recipe3 ...)` and the displayed right-hand side of `gentow2_B` are both
   `Polynomial ((T.deepTower hπ).fld 2)`.
4. In `gentow5_key_certificate`, truncation does not change the `fld` function; the apparent
   `W`/`W.trunc` coefficient-field mismatch is definitional.
5. `keyAt 2 = composedKey T` is type-correct but is an explicit hypothesis, not a consequence of
   any existing class field.
6. The full current file was rebuilt with `lake build Leanspec.ChapC` on 2026-08-24; it completed
   successfully. This verifies the provisional accessor types, not the mathematical fidelity of
   the law fields.

## 7. `fgmn_calculus_exists`: statement draft and disposition

### 7.1 The old draft is rejected

```lean
-- REJECTED: Lean-core inhabitable and not a faithful literature import.
axiom fgmn_calculus_exists
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ)
    (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u') :
    Nonempty (FGMNCalculus W e' f' u')
```

This is not merely under-specified. The existing class admits
`ExactGrade := False`, `KP := False`, constant residual operators and junk keys; the repository
contains a proof of this exact conclusion without a literature axiom. Moreover, an arbitrary
`DeepTower` carries abstract fields and arithmetic invariants but not an inductive valuation or
MacLane keys. FGMN never proves that every such abstract tower realizes its calculus.

### 7.2 Only defensible draft shape

An existence theorem can be stated only after a separate realization record is defined. Its
shape is:

```lean
-- OPEN: `FGMNChainRealization` has no definition in the corpus yet.
-- It must contain an actual inductive valuation/MacLane chain and the four
-- dictionary identifications of §8; it must not contain `FGMNCalculus` itself.
theorem fgmn_calculus_exists
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ)
    (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u')
    (A : FGMNChainRealization W e' f' u') :
    Nonempty (FGMNCalculus W e' f' u') := by
  -- construct the fields from A; invoke the published clauses listed in §2
  -- for the law fields; discharge all transports as ordinary Lean theorems.
  exact ⟨A.toCalculus⟩
```

This should be an ordinary theorem, not a gate-(b) axiom: once `A` contains the source-side
objects and dictionary equivalences, building the interface is packaging. The genuinely cited
existence claim would have to produce `A`. No cited clause in the audited source pool produces
such a realization from the present `DeepTower` hypotheses.

Therefore the C.92 cite statement is:

> **OPEN / not signable.** There is no faithful unconditional `fgmn_calculus_exists` statement
> over `DeepTower W` at the current parameter list. Retain hypothesis form, or first author and
> prove a non-vacuous `FGMNChainRealization` bridge.

## 8. Required realization data

These are the minimum obligations for `FGMNChainRealization`; they are deliberately not proposed
as opaque fields of `FGMNCalculus`.

1. `OPEN-DICT-1` — an actual MacLane chain whose keys transport to `keyAt`, with the index shift,
   `keyAt_one`, and the equation-(7) degree recurrence identified with `W.Dcum`.
2. `OPEN-DICT-2` — the cleared-value convention identifying the source's rational grades with
   the corpus's natural grades, and proving `ExactGrade`/`AboveGrade` are respectively
   `P_α \ P_α⁺`/`P_α⁺`.
3. `OPEN-DICT-3` — coefficient-field equivalences `W.fld i ≃ F_i`, compatibility with
   truncation, and proofs that `Rgr`, `Rres`, `KP`, and `nuEquiv` are the transported FGMN
   objects. This includes the scalar-coordinate specialization of `R_{r,α}`.
4. `OPEN-DICT-4` — compatibility of the FGMN `γ_i → y_i → z_i` construction with the
   repo normalizers and residue letters. C.102's formula is a theorem of this dictionary, not a
   bare consequence of a freely chosen `letterZ` function.

Only after these are present can Q9/Q10 be typed honestly and C.90(b), C.91(c), and the letter
read cease to be booked residuals.

## 9. Open questions for the owner

1. Is `FGMNCalculus` intended to describe the valuation at depth `r`, or the next augmentation
   determined by `(e',f',u')`? The provisional prose calls `Rgr` `R_{r+1,β}` while `Rres_recipe`
   behaves like the residual operator attached to the last key `keyAt r`. The index convention
   must be fixed before source laws are signed.
2. What exactly is scalar `Rgr β g`: the constant coefficient of `R_{r,β}(g)`, evaluation at a
   letter, or the degree-zero residual in the next augmentation? These agree only under scope
   hypotheses that are not encoded by `ExactGrade` alone.
3. Is the grade domain all cleared nonnegative elements of `Γ_{r-1}`? If yes, prove
   `PrevGrade β` automatically for every class grade and later remove that predicate. If not,
   every use of `Rgr_mul` must discharge it explicitly.
4. Should `r = 0` be supported? Published equation (11) and Lemma 5.2(1) have different base
   behavior. The recommended law fields use `0 < r`; an alternative is to require `0 < r` at the
   class level.
5. Which landed Lean theorem supplies the monic Gauss transport from irreducibility in the
   completion/fraction field to `Irreducible` in `Polynomial O`? Until identified,
   `KP_irred` is `OPEN-GAUSS`.
6. Is `hfree : ¬ composedKey T ∣ g` in C.100 meant as ordinary polynomial divisibility or FGMN
   `μ`-divisibility? Published Proposition 1.7(2) uses the latter. They cannot be silently
   identified.
7. Does the desired C.90 theorem need the full published Corollary 6.3 conclusion, or only the
   `R_{i-1}(F) = ψ_{i-1}^{ℓ_i}` component? Even the smaller statement requires per-level
   residual fields and an index dictionary, but the carrier design differs materially.
8. Should the source law fields live inside `FGMNCalculus`, or should the class contain only the
   realization and expose the laws as theorems? The latter avoids duplicating consequences and
   makes the trust boundary easier to audit.

## 10. Final field-list recommendation

For the next Lean-facing revision:

- land the carrier block of §3;
- add the law block of §4 only after `OPEN-DICT-1` through `OPEN-DICT-4` are represented and
  checked;
- correct the provisional citations and scopes exactly as in §4.1;
- do not create opaque fields for Q3, Q9, Q10, Proposition 1.12 or Theorem 4.3;
- keep every current consumer conditional on `[FGMNCalculus ...]`;
- leave `fgmn_calculus_exists` undeclared.

This is complete for the current consumer signatures, faithful to every source clause that can be
typed in the present vocabulary, and explicit about the clauses that cannot yet be ported without
inventing mathematics.
