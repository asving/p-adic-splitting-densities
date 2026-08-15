# QUARRY BACKPORT + HYP.01 — unit note, 2026-08-15 (Opus arm)

**What this unit did.** Executed the top of the ranked shortlist in
`docs/VENDOR_QUARRY_MAP_2026-08-15.md` §5 — the read-only reconnaissance of the four libraries
cloned into `vendor/` — and used the survey's §2.5 finding to attack the classical half of
**HYP.01 (`typeOf` faithfulness)**, a `[CORE-SET]` ledger row. Three targets, in the survey's
value order. Lean work in `leanfinal/`, new files only, no existing statement touched.

**Quarry discipline (append #56, restated).** A backported declaration is a NEW declaration in
our tree. Every backport file carries a provenance block (source repo, commit, file, line,
licence, verification date) and an explicit dedup-audit statement listing every adaptation.
`vendor/FLT` is Apache-2.0, same as mathlib and as this repo — clean for adoption. The three
mariainesdff clones have **no LICENSE file**; nothing was copied from them.

---

## Target 1 — LANDED. The local fundamental identity, in rank form

`leanfinal/Uniformity/Quarry/RamificationInertiaLocal.lean` (new; wired into the root via the new
`Uniformity/Quarry.lean` roll-up).

```lean
theorem Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [IsLocalRing S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (IsLocalRing.maximalIdeal S).ramificationIdx' R *
      (IsLocalRing.maximalIdeal S).inertiaDeg' R = Module.finrank R S
```

Source: `vendor/FLT` @ `58f25c6f305e1cf794c7666f89adcd0375bcc047`,
`FLT/Mathlib/RingTheory/RamificationInertia/Basic.lean:28`, verified 2026-08-15. Shortlist #1.
Dedup-audit: **near-verbatim move**, three adaptations, all forced by the two-month mathlib drift
(FLT pins `v4.34.0-rc1`; we pin `v4.31.0` / mathlib `fabf563a`, 2026-06-15):

1. **Module-system header surgery** — `module` / `public import` / `@[expose] public section` →
   plain `import`s. Our rev predates mathlib's module system.
2. **`ramificationIdx'` / `inertiaDeg'` instead of the unprimed names.** This is the one thing a
   reader should not skip. At our rev the *rank-form* identity
   `Ideal.sum_ramification_inertia_eq_finrank` is stated in the **primed** generation; upstream
   renamed primed → unprimed when it deprecated the old `(p, q)`-keyed pair in Aug 2026, and FLT's
   source text is written against the post-rename tree. Same definitions, older names.
3. **Two instances supplied by hand** — `Module.Flat R S` (from `IsDedekindDomain R` plus
   torsion-freeness) and `Fintype (p.primesOver S)` (from `IsLocalRing.primesOver_eq`). Our
   `sum_ramification_inertia_eq_finrank` carries both as hypotheses; FLT's newer copy does not.
   This is why our proof is ~10 lines longer than FLT's.

Why it was worth taking (survey §5 row 1): `e · f = [S : R]` in **rank form**
`Module.finrank R S` — the form the tower chapters actually want — and the future-proof
replacement for mathlib's `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
(`Mathlib/NumberTheory/RamificationInertia/Basic.lean:650`), which is live for us *only* because
our rev predates its Aug-2026 deprecation, and which is stated in fraction-field form
`Module.finrank K L`. Any future mathlib bump must re-check that line.

Footprint: `[propext, Classical.choice, Quot.sound]`.

---

## Target 2 — the FLT henselian/étale cluster: BLOCKED BY COST. Substitute landed instead

### The cost audit (this is the reportable finding)

Shortlist #2 is `HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing`
(`vendor/FLT/FLT/HenselianLocalRing/Finite.lean:96`), which the survey called the highest-value
item because it closes §2.3's bottleneck `IsLocalRing (integralClosure O L)`. The survey flagged
**one** dependency newer than our pin and judged the bridge available inside the clone
(`EtaleDecomposition.lean`). Checked declaration by declaration against our mathlib, the blocker
is **worse than one lemma**:

| what `Finite.lean:96` needs | at our pin? | in FLT itself? |
|---|---|---|
| `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq` (the call at `:102`) | **NO** | **NO** — FLT has only the `private` universe-restricted `..._eq'` in `EtaleDecomposition.lean:109`; the public wrapper lives in FLT's newer mathlib |
| `Algebra.tensorQuotientTensorEquiv` (`EtaleDecomposition.lean:154`) | **NO** (mathlib has only the *module*-level `TensorProduct.quotientTensorEquiv` / `tensorQuotientEquiv`) | **NO** |
| `CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span` (`:155`) | **NO** (our `Idempotents.lean` lifts only along **nil** kernels) | **NO** |
| `Ideal.mem_map_span_singleton_iff_of_isIdempotentElem` (`:182`) | **NO** | **NO** |
| everything else: `IsIdempotentElem.Corner`, `CompleteOrthogonalIdempotents`, `Algebra.Etale`, `Etale/QuasiFinite`, `Unramified/LocalStructure`, `primesOverOrderIsoFiber`, `fiberIsoOfBijectiveResidueField`, `ResidueField.mapₐ`, `bijective_algebraMap_quotient_residueField`, `Localization.AtPrime.algebraOfLiesOver`, `exists_isStandardEtale`, `FormallyUnramified.finite_of_free`, `CompleteOrthogonalIdempotents.equiv` | **yes** | — |

So the backport is **not** "one bridgeable dep". It is: 191 lines of `EtaleDecomposition.lean`
(two `private` inductions over the fibre cardinality) + ~140 lines of `Finite.lean`
(`isMaximal_of_isMaximal_under_of_formallyUnramified` 19, the `IsEtaleAt` instance 5,
`exists_lift_of_to_ResidueField` 32, the target itself ~84) + a universe-polymorphic public
wrapper that exists in **no** tree we hold + **three mathlib lemmas that must be written from
scratch**, one of which (idempotent-family lifting through a quotient by an idempotent-generated
principal ideal) is itself a real lemma. ≈ **330 lines of adaptation plus four from-scratch
declarations**, against the charter's ~200-line budget. Not forced. Statement recorded here as the
standing target:

```lean
-- TARGET, not landed. vendor/FLT/FLT/HenselianLocalRing/Finite.lean:96, 0 sorries.
lemma HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing
    {R A : Type*} [CommRing R] [HenselianLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] :
    ∃ (n : ℕ) (e : Fin n → A) (he : CompleteOrthogonalIdempotents e),
      ∀ i, IsLocalRing (he.idem i).Corner
```

Re-attempt this only after a mathlib bump past FLT's pin, at which point the four missing
declarations arrive for free and the backport collapses to header surgery. **That, not the
étale induction, is the cheap path.** Recorded so the next agent does not re-audit.

### CROSS-REPO FINDING — the §2.3 bottleneck is currently a signed-off AXIOM in `lean/`

Not in the survey, found while confirming the other repo's baseline. `lean/LeanUrat/SerreLocalFields.lean`
declares

```lean
axiom AX_integralClosure_dvr (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] :
    IsDiscreteValuationRing (integralClosure ℤ_[p] L)
```

— Serre, *Local Fields* Ch. II §2 Prop. 3, DVR clause, at the concrete instance `(ℤ_[p], ℚ_[p])`.
Declared 2026-07-31, Codex statement audit PASSED, entry `AX-SERRE-DVR` in
`docs/AXIOM_FAITHFULNESS.md:299`, consumers landed (`MovesU/BridgeE567_zfLaws`, `BridgeE9_zpBridge`).
Its downstream in that repo: `integralClosure_isLocalRing`, `isLocalRing_integralClosure_adjoinRoot`
(and `maximalIdeal_liesOver`, which is derived axiom-free).

**So §2.3 is not merely a chapter obligation — it is a live axiom, and shortlist #2 is its retirement
route.** That reframes the value of the item: it is not only "unlocks `(FUND)`, GENHN E3, GENH4,
NS-14, HYP.01's classical half", it is "removes a declared axiom from the trusted base". Worth
saying in any progress report. (The axiom is correctly quarantined off the density capstones —
`OM.RealInstanceV2.montes_unconditional` still prints Lean core only, re-confirmed today.)

### The substitute: the AdjoinRoot-DVR cluster (shortlist #3, #5, #7) — the inert leaf, classically

`leanfinal/Uniformity/Quarry/AdjoinRootDVR.lean` (new; commit `9a3ab0c0`). Four declarations from
the same FLT commit, `FLT/Mathlib/RingTheory/DiscreteValuationRing/AdjoinRoot.lean` (Apache-2.0,
verified 2026-08-15):

| declaration | FLT line | shortlist |
|---|---|---|
| `IsLocalRing.of_isMaximal_map_maximalIdeal` | `:69` | #5 |
| `AdjoinRoot.residueFieldEquiv` | `:81` | #7 |
| `AdjoinRoot.isMaximal_map_maximalIdeal` | `:105` | #7 |
| `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue` | `:121` | #3 |

Dedup-audit: all four STATEMENTS are byte-identical to FLT's (diffed, not eyeballed); the first
three are verbatim moves, proof terms included. The fourth has exactly one proof-term adaptation,
applied twice — FLT's `List.TFAE.out 5 1` / `.out 3 1` become `.out 4 0` / `.out 2 0`, because
upstream made `TFAE.out` 1-indexed after our June-2026 rev; both readings were checked against
both clause lists (`IsDiscreteValuationRing.TFAE`, `local_hom_TFAE`) and select the same clauses.

Item #3 is the classical inert leaf: over ANY DVR `R` (no completeness), `P` monic with `P̄`
irreducible makes `R[X]/(P)` an unramified DVR — the sorry-free proof of exactly what
`vendor/LocalClassFieldTheory` only `sorry`s. Recorded, not resolved: #5 subsumes our
`Density/InertLeaf.lean:71` `isMaximal_map_maximalIdeal_adjoinRoot` (ours is the DVR-only special
case; dedup is a later housekeeping unit, not this one).

---

## Target 3 — HYP.01, the `[CORE-SET]` row

### >>> FLAGGED FOR THE OWNER'S FRESH-EYES AUDIT <<<

**This subsection is the reason the unit exists. HYP.01 is stamped `[CORE-SET]` in
`spec/HYPOTHESIS_LEDGER.md:63` — "`typeOf` is the engine of the type definition, so its faithfulness
to the classical `(e,f)`-multiset is inside the human-reviewed core set." What follows is the landed
statement plus an explicit account of what it does and does not certify. Read the caveat list; two
of the three caveats are about the *statement*, not the proof, and Lean cannot catch those.**

Two new files, 13 declarations, commit `f5a76a40`, both wired into the root.

`leanfinal/Uniformity/Density/TypeOfFaithful.lean` — the bridge, conditional on the order being
maximal. For `A = AdjoinRoot g`, `g` monic of positive degree over the DVR `O`, under
`[IsDomain A] [IsDiscreteValuationRing A]`:

```lean
inertiaDegOf_eq_inertiaDeg'    : inertiaDegOf g = (IsLocalRing.maximalIdeal A).inertiaDeg' O
ramIndexOf_eq_ramificationIdx' : ramIndexOf g = (IsLocalRing.maximalIdeal A).ramificationIdx' O
typeOf_eq_classical_of_isDiscreteValuationRing :
    typeOf g = {((IsLocalRing.maximalIdeal A).ramificationIdx' O,
                 (IsLocalRing.maximalIdeal A).inertiaDeg' O)}
```

(plus seven supporting lemmas: `injective_algebraMap_adjoinRoot`, `faithfulSMul_adjoinRoot`,
`finrank_adjoinRoot`, `addVal_norm_ne_top`, `exists_addVal_norm_eq_nsmul`,
`exists_ramification_data`, `ramificationIdx'_eq_of_map_maximalIdeal_eq_pow`).

`leanfinal/Uniformity/Density/TypeOfFaithfulInert.lean` — the unconditional inert instance. For
`g` monic with irreducible residue, NO DVR hypothesis and no completeness (the DVR structure is
supplied by the substitute's item #3): `typeOf_inert_faithful` gives `ramificationIdx' O = 1`,
`inertiaDeg' O = g.natDegree`, and `typeOf g = {(1, g.natDegree)}`; plus
`isDomain_adjoinRoot_of_irreducible_map` and `isIntegrallyClosed_adjoinRoot_of_irreducible_map` —
the in-Lean certificate that the inert order IS the maximal order, which is what licenses reading
its maximal ideal's `(e, f)` as the classical pair. `typeOf_inert_faithful`'s third clause
independently re-proves `Density/InertLeaf.lean:179`'s conclusion by a decorrelated route
(classical fundamental identity vs. the gcd/norm-divisibility induction) — deliberate; recorded,
not removed.

### The rung reached, in words

**Rung: the monogenic-maximal locus.** HYP.01 asks that the gcd-defined `(ramIndexOf, inertiaDegOf)`
of `Uniformity/Density/TypeOf.lean` agrees with the classical (ramification index, inertia degree).
What is now proved is: **whenever the order `O[x]/(g)` is already the maximal order, it does.** The
hypothesis that carries "already maximal" is `[IsDiscreteValuationRing (AdjoinRoot g)]` — a DVR is
integrally closed, so `AdjoinRoot g` then *is* the integral closure of `O` in its own fraction field.

Why that is the right rung and not a dodge: our `inertiaDegOf g` is defined as
`gcd { v_O(N_{A/O} x) : x ∈ A = AdjoinRoot g, x ≠ 0 }`, and the classical theorem behind the
definition is `v_O(N(x)) = f · w(x)` for `w` the normalized valuation of the *maximal* order. On a
non-maximal order that identity is exactly what fails — which is the content of
`spec/EFF-GENHN-s1of2.md:1105`, ERRATUM E3, "the false part is exactly '`R` a complete DVR'". So the
maximal-order hypothesis is not a convenience: it is the true boundary of the argument, and the
residual gap is a named, already-documented erratum rather than an unexplored region.

**What the proof runs on** (worth knowing, because it is cheaper than the survey's §2.5 route): NOT
the `‖·‖ ↔ addVal` translation the survey identified as HYP.01's remaining work (§2.5(ii)). The
spectral-norm bridge is avoided entirely. Instead the argument is
`v_O(N(π)) = n` (norm of a scalar) `= e · v_O(N(ϖ))` (factor `π` as unit × ϖ^e in the DVR `A`),
combined with `e · f = n` (Target 1) and `e > 0`, giving `v_O(N(ϖ)) = f` — after which `f` divides
every norm-valuation and is itself one, so the gcd *is* `f`. The whole classical half is Target 1
plus DVR bookkeeping. **The survey's §2.5 estimate should be revised: item (ii), the norm/valuation
translation, is not needed at this rung.**

**No completeness is used.** Neither theorem carries `[IsAdicComplete (maximalIdeal O) O]`. The
identity holds over any DVR. Completeness is what makes the DVR hypothesis on `AdjoinRoot g`
*checkable* in our applications, not what makes the identity true.

### The caveats (audit list)

1. **STATEMENT caveat — "classical" means the order's own `(e, f)`, not the field extension's.**
   The landed statement's classical side is
   `(IsLocalRing.maximalIdeal (AdjoinRoot g)).ramificationIdx' O` / `.inertiaDeg' O`, i.e. the
   ramification and inertia data of the maximal ideal of the ring `A = AdjoinRoot g` over `O`. To
   read that as "the `(e, f)` of the field extension `L/K`, `L = K[x]/(g)`" one needs `Frac A ≅ L`.
   That identification is standard and true, but it is **not formalized here**. The available fix is
   `AdjoinRoot.isFractionRing_map` (`vendor/FLT/FLT/Mathlib/RingTheory/DiscreteValuationRing/AdjoinRoot.lean:177`,
   0 sorries) — but its cost is MEDIUM, not LOW: FLT leaves the
   `Algebra (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))` instance and its compatibility
   `hmap` as *hypotheses*, so the caller must construct them.
2. **STATEMENT caveat — primed vs unprimed API generation.** `ramificationIdx'` / `inertiaDeg'` are
   the rank-form generation, keyed on the prime of the big ring with the base ring as an argument
   (`inertiaDeg' q R = finrank (q.under R).ResidueField q.ResidueField`). This is the generation
   upstream is migrating *to*; the older `(p, q)`-keyed `Ideal.ramificationIdx p q` / `p.inertiaDeg q`
   used elsewhere in mathlib's `NumberTheory/` is reconciled by
   `Ideal.ramificationIdx_eq_ramificationIdx'` / `Ideal.inertiaDeg_eq_inertiaDeg'`. If a chapter
   quotes HYP.01 against the old generation, it must go through those two lemmas.
3. **SCOPE caveat — one rung, not the row.** This does not close HYP.01. It closes it on the
   monogenic-maximal locus. The unconditional inert instance below is a genuine, hypothesis-free
   corollary; everything else (in particular every non-maximal order, i.e. every `g` whose index
   `[O_L : O[x]/(g)]` is nontrivial) is open and is GENHN ERRATUM E3's territory.

---

## Builds and footprints

- Target 1 + substitute: `lake build Uniformity.Quarry` green (2,569 jobs). Footprints Lean-core
  (`[propext, Classical.choice, Quot.sound]`) for all five backported declarations.
- Target 3: full `lake build` green (8,563 jobs), zero warnings from the new files. Footprints
  Lean-core for all 13 new declarations.
- Cross-check re-run 2026-08-15 (recorded in the Target-2 finding above):
  `OM.RealInstanceV2.montes_unconditional` in `lean/` still prints Lean core only — the
  `AX_integralClosure_dvr` axiom stays quarantined off the density capstones.
