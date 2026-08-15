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

### The substitute: RESULTS_TARGET2_PLACEHOLDER

---

## Target 3 — HYP.01, the `[CORE-SET]` row: RESULTS_TARGET3_PLACEHOLDER

---

## Builds and footprints

BUILD_PLACEHOLDER
