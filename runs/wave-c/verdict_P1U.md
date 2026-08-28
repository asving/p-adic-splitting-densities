# UNIT P1U verdict — P1 cite draft; P2 LANDED; P3 needs A-C.22 (2026-08-28)

## Outcome

* **P1 — CITE-GRADE, declaration withheld.**  The exact published result is Guàrdia--Nart,
  *Genetics of polynomials over local fields*, Lemma 3.1(3): a polynomial is a
  representative of a type iff it is a key polynomial for the type's inductive valuation
  and has the prescribed residual ideal.  The source definition of a representative is the
  monic/right-degree/prescribed-residual recipe (pp. 12--13).  This is exactly the intended
  mathematics behind `IsTestKey L Ψ → IsMuKey L Ψ`, but the corpus has not formalized the
  dictionary saying that C.13's five coefficient clauses constitute a representative of the
  corresponding type.  No cite was declared; the draft and faithfulness entry are below.
* **P2 — LANDED.**  New file
  `leanfinal/Uniformity/ChapC/C134p1.lean` proves the generic forward
  initial-form/residual bridge, residual-nondivisibility `→ ¬ MuDvd`, and the F1.2
  complement specialization.  No new axiom and no `sorry`.
* **P3 — AMENDMENT FORCED for the generic signed family.**  The only concrete intended
  S2/μ₃ site has the stronger margin `20 < 21`, but the signed hypothesis exposes only
  `10 < 21`; no direct consumer supplies a generic implication.  Draft A-C.22 below replaces
  the floor in F1.3--F1.6 with the engine-honest floor.
* **F1.4--F1.6 were not re-attempted/landed.**  Charge 5 is conditional on **both** P1 and
  P2 landing.  P1 is held at the citation gate, so that condition is false.  Even after the
  floor amendment, F1.4/F1.5 still need the per-slot `dv2Res` cocycle telescope and F1.6
  still needs the level-2 side-min/side-degree equality mechanism recorded by DV2G.

## P1 — cite-vs-prove adjudication

### Exact source statement

Guàrdia--Nart, *Genetics of polynomials over local fields*, Contemporary Mathematics 637
(2015), arXiv:1309.4340v2:

* §3.1 defines a representative at the next level as a monic polynomial of degree
  `m_r = e_{r-1} f_{r-1} m_{r-1}` with prescribed residual polynomial
  `R_{r-1}(φ_r) = ψ_{r-1}`.
* **Lemma 3.1(3)** states that `φ` is a representative of a type `t` iff `φ` is a key
  polynomial for `μ_t` and its residual ideal is the one prescribed by the type.

FGMN, *Residual ideals of MacLane valuations*, supplies the structural apparatus behind
that equivalence: Definition 1.2's initial-form equivalence/divisibility/minimality,
key-polynomialhood as monic + μ-minimal + μ-irreducible, Lemma 5.2's residual criterion,
and Theorem 5.7's residual-ideal classification of key-polynomial classes.  It does not use
the corpus term “test polynomial”; the direct representative-to-key statement is GN Lemma
3.1(3).

### Why this is not an honest short Lean proof from the landed banks

The useful landed facts stop one layer short:

1. `C131aa.isTestKey_isDvPure` proves the one-sided Newton shape.
2. `C131aa.dvResPoly_testKey` proves the normalized level residual is exactly `L.r`.
3. The `C132kp*` key criteria are specialized to the concrete S2/μ₃ normalized-residual
   operators.  Their proofs use the corresponding specialized initial-form/residual and
   residual-divisibility banks.
4. `C134dv2g.IsMuKey` is frame-generic, but there is no frame-generic theorem converting
   “monic + representative degree + irreducible residual” into `MuMinimal ∧ MuPrime`, nor a
   total generic normalized-residual calculus from which to replay `C132kp3`.

Thus generalizing `s2Mu3_key_criterion` is not a binder-only port.  It requires formalizing
the type-representative dictionary and the generic μ-divisibility/residual correspondence;
that is substantially the unformalized proof of GN Lemma 3.1(3).  Treating it as a few lines
of assembly would hide the new mechanism.  The repository preference for proofs was applied:
P2's forward half was extracted and proved, but P1's minimality and primality halves remain
the real literature wall.

### Draft declaration — NOT DECLARED

```lean
/-- [cite:GN] A test key is a MacLane key polynomial for the level valuation.
Guàrdia--Nart, *Genetics of polynomials over local fields*, Lemma 3.1(3), after the
`IsTestKey`/type-representative dictionary. -/
axiom isMuKey_of_isTestKey
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) (hh : 0 < F.h)
    {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    C134dv2g.IsMuKey L Ψ
```

The explicit `hπ` and `hh` are the Lean-side realization of the paper's standing genuine
discrete/augmented valuation hypotheses and are already present at every DV2G consumer.
They avoid widening the cite to degenerate frame data the paper does not discuss.

### Draft faithfulness entry — pending orchestrator/owner review

#### AX-GN-REPKEY = `C134p1.isMuKey_of_isTestKey` — **STATEMENT DRAFT ONLY (NO Lean axiom exists; NOT-YET-DECLARED)** *(DRAFT 2026-08-28 — PENDING guardian audit + Asvin sign-off; NO consumer may cite it)*

* **Statement (drafted, not declared):** under a genuine DVR uniformizer `hπ` and positive
  frame augmentation `hh`, every `Ψ` satisfying C.13's `IsTestKey L Ψ` recipe is
  `C134dv2g.IsMuKey L Ψ`, i.e. monic, μ-minimal, and prime for initial-form divisibility at
  the level valuation `dvSupp F · L.u L.ℓ`.
* **Verified core:** Guàrdia--Nart, *Genetics of polynomials over local fields*,
  Contemporary Math. 637 (2015), **Lemma 3.1(3)**: representatives of a type are exactly
  key polynomials for the attached inductive valuation having the type's prescribed
  residual ideal.  The representative recipe immediately before the lemma is monic,
  prescribed degree, prescribed residual.  FGMN, *Residual ideals of MacLane valuations*,
  Definition 1.2/Lemma 5.2/Theorem 5.7 supplies the matching μ-predicate and residual-ideal
  classification.
* **Corpus/source dictionary:** `dvSupp F · L.u L.ℓ` is the cleared level valuation;
  `C134dv2g.MuEquiv/MuDvd/MuMinimal/MuPrime` are the FGMN initial-form predicates;
  `IsTestKey`'s top/off-slot/read clauses are the explicit representative lift;
  `C131aa.isTestKey_isDvPure` and `C131aa.dvResPoly_testKey` machine-check the one-sidedness
  and prescribed residual `L.r`.  The missing formal step is precisely packaging these
  facts as GN's type representative and importing Lemma 3.1(3)'s keyhood conclusion.
* **Scope caveats:** (a) only key-polynomialhood is imported—no factorization,
  irreducibility in `O[X]`, termination, or uniformity conclusion; (b) `hπ` and `hh` pin the
  paper's genuine valuation scope; (c) `IsMuKey` carries only the prime clause of
  μ-irreducibility because its nonzero/proper clauses follow downstream from monicity and
  μ-minimality; (d) the owner paper is not a source and is not cited.
* **Gate:** orchestrator guardian audit, citation-number/page check against the published
  version, then explicit owner sign-off before any `axiom` keyword or consumer.

## P2 — landed proof

Namespace: `Uniformity.Density.Tower.C134p1`.

| Declaration | Result/mechanism | Footprint |
|---|---|---|
| `dvResPoly_eq_of_muEquiv` | Generic forward initial→residual direction.  From `g ∼μ z`, write `g = z + (g-z)` with the difference strictly deeper; `C131y.dvResPoly_add_deep` preserves the normalized residual. | `[propext, Classical.choice, Quot.sound]` |
| `not_muDvd_of_residual_notdvd` | If `L.r ∤ R(g)` and `Ψ` is a test key, then `¬ MuDvd L Ψ g`.  A μ-divisibility witness gives `R(g)=R(Ψq)` by the preceding theorem; `C133mh3.dvResPoly_mul_gen` gives `R(Ψq)=R(Ψ)R(q)`; `C131aa.dvResPoly_testKey` gives `R(Ψ)=L.r`, contradiction. | `[propext, Classical.choice, Quot.sound]` |
| `block_complement_not_muDvd` | Applies the generic bridge to F1.2's `quotient_residual_notdvd`, producing the exact complement premise DV2G requested. | `[propext, Classical.choice, Quot.sound, Uniformity.Density.Tower.exists_dvDissection]` |

The last declaration inherits the single allowlisted dissection cite through signed F1.2;
the two mechanism declarations are Lean core.  There is no new citation.

## P3 — consumer and margin analysis

### Consumers actually present

A repository-wide exact-name search found no call to `dv2Supp_translation`,
`dv2ResPoly_scalar`, `dv2ResPoly_radical_eq`, or `mult₂_readable`: outside their leanspec
declarations, the names occur only in blueprint/status prose.  Therefore no landed caller
threads an additional inequality capable of strengthening the signed premise generically.

The concrete intended level-2 consumer family is the S2/μ₃ bank:

* `C130np4.seam_s2Tower`: `L.seam = 5`;
* `C130np4.ell_mul_seam_s2Tower`: `L.ℓ * L.seam = 10`, with `L.ℓ = 2`;
* `C132nv4` and the `C132rp*` μ₃ chain fix the outer pair `(u₂,ℓ₂) = (21,2)`.

Hence:

* signed floor: `ℓ₂ * L.seam = 2*5 = 10 < 21`;
* engine floor: `ℓ₂ * (L.ℓ * L.seam) = 2*(2*5) = 20 < 21`.

The honest S2 instance therefore works, with only a one-unit engine margin.  But this does
not repair the generic theorem: with the same `L` and `(ℓ₂,u₂)=(2,11)`, the signed premise
is true (`10<11`) while the engine premise is false (`20≮11`).  Thus the implication needed
by DV2G cannot be proved from the signed binder.  A specialized theorem at `21,2` would be
valid, but it would not discharge the universally quantified signed names.

### Recommendation: enact A-C.22

**A-C.22 — level-2 block-translation engine floor.**  In the signatures of C.37
`dv2Supp_translation`, C.38 `dv2ResPoly_radical_eq`, C.39 `dv2ResPoly_scalar`, and C.64
`mult₂_readable`, replace the binder

```lean
(hseam : ℓ₂ * L.seam < u₂)
```

verbatim by

```lean
(hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)
```

and update their statement annotations from “above the seam” to “above the test-key grade
`L.ℓ * L.seam`”.  No conclusions change.  The factor is forced by
`C131aa.dvSupp_testKey`, which identifies the test-key grade with `L.ℓ * L.seam`, and by
DV2G's sharp slot-1 carry inequality.  The amendment is true at the intended S2/μ₃
instantiation (`20<21`) and excludes generic pairs for which the current proof engine is
not valid.  This unit does **not** edit leanspec or any signed/landed file.

## Verification

Required command:

```text
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134p1.lean
```

Result: exit 0, zero errors, zero warnings, zero `sorry`.  AxCheck output is exactly the
three footprints listed above.  No landed `.lean`/leanspec file was edited and no git
commit was made.
