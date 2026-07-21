# WILD_WAVE2_BLUEPRINT — the Montes-paper axiom + semantic faithfulness of the σ-keying

**Date: 2026-07-21. Under the standing directive (wild uniformity conditional on the Montes paper).
Successor to `WILD_WAVE1_BLUEPRINT_2026-07-21.md` (complete, audited PASS 8/8). Grounded in the
2026-07-21 vocabulary survey (mathlib v4.31.0 pin, rev fabf563).**

## §0. The gap being closed

Wave 1's σ-keying is DEFINITIONAL: `typeOfW` reads (e,f) off shape literals; the capstone certifies
"the density of the σ-NAMED menu strata." The semantic claim — fiber members' true ℚ_p factorization
type IS σ — is not yet formal (W1 audit's single follow-up). Closing it requires (i) a formal
vocabulary for "(e,f) of an irreducible g over ℚ_p" and (ii) the Montes-paper import tying classifier
fibers to genuine factorizations.

## §1. Vocabulary verdict (from the survey; full report in the session log)

- The repo has ZERO ℚ_p-factorization vocabulary today; the only genuine ℤ_p bridges are
  `PadicValuation.coeffVal` and `PadicLift.toBox`/`toZModPow` (the sole formal ℤ_p ↔ finite-box link).
- Mathlib pin: `Ideal.ramificationIdx p P` / `Ideal.inertiaDeg p P` (2-ARG — the project blueprint's
  3-arg form is pre-refactor and will not compile); `Valuation.HasExtension` gives the needed
  `Ideal.LiesOver (maximalIdeal L₀) (maximalIdeal K₀)` instance; ℤ_[p] fully equipped (DVR,
  IsAdicComplete). MISSING: any `IsNonarchimedeanLocalField` instance, finite-extension
  `Valued`/`HasExtension`, DVR-ness of `integralClosure ℤ_[p] L`. So genuine per-factor (e,f) is
  statable ONLY with the local-field data carried as hypothesis data (survey Rank 1).
- Rank-2 (Eisenstein-only anchoring) is insufficient: Wave 1's menu already certifies a MIXED factor
  (σ = {(2,2)}: e=2, f=2). Rank 1 it is.
- No p-adic Newton polygon, no `IsTotallyRamified`, no p-adic Haar measure in mathlib at the pin.

## §2. Design

### W2a — the bundle + what is provable WITHOUT any axiom (leaf module `OM/QpType.lean`)
1. `structure LocalFactorData (p) (g : ℤ_[p][X])`: carrier `L` (Field, `Algebra ℚ_[p] L`,
   `Module.finrank ℚ_[p] L = g.natDegree`, g has a root generating L — via `AdjoinRoot`/`IsAdjoinRoot`
   or a `PowerBasis` clause), integers `𝒪` (CommRing, `IsDiscreteValuationRing`, `Algebra ℤ_[p] 𝒪`,
   `Algebra 𝒪 L`, `IsIntegralClosure 𝒪 ℤ_[p] L` — pinning 𝒪 as THE integers without the missing
   instances), `[Ideal.LiesOver (maximalIdeal 𝒪) (maximalIdeal ℤ_[p])]`, scalar-tower coherence.
   Then `def eOf (D) := Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.𝒪)` and
   `def fOf (D) := Ideal.inertiaDeg …` (2-arg forms).
2. **Non-vacuity witness (mandatory gate, the U1 lesson):** a machine-checked instance of the bundle
   at degree 1 — `g = X`, `L = ℚ_[p]`, `𝒪 = ℤ_[p]` — with `eOf = fOf = 1` PROVED. The bundle must
   not be a compiled `False`.
3. **Axiom-free semantic theorems (prove, don't import):**
   (a) the minimal-H wild fiber at fSum σ = 1 (n=2 gate stratum: v(a₀)=1, v(a₁)≥1) consists of
   IRREDUCIBLE polynomials over ℚ_p — via mathlib `Polynomial.IsEisensteinAt` +
   `IsEisensteinAt.irreducible` against `maximalIdeal ℤ_[p] = span {p}` (fiber ⟹ Eisenstein is a
   coefficient-valuation computation through `toBox`); (b) if cheap, the order-0 Hensel split
   (separable reduction ⟹ factorization lifting the residue factorization — check what
   mathlib/`GradedHensel.lean` already gives). These make part of the faithfulness content
   UNCONDITIONAL and give the axiom its mutation-consistency cross-checks.
4. `def qpTypeData (f : ℤ_[p][X])` : the record (factors multiset, per-factor bundle) and
   `def qpType (…) : FactorizationType := ⟨factors.map (fun g => (eOf, fOf))⟩`.

### W2b — the axiom (after W2a's plumbing exists; never against guessed objects)
`axiom om_leaf_faithful` — the NARROWLY-SCOPED, menu-fiber-restricted, order-≤1 instance of the GMN
dissection (house style = `omReadValuation_lt_of_certLevel_fkeyed`): for `f : ℤ_[p][X]` monic of
degree n with `PadicLift.toBox … f ∈` the level-N classifier fiber of `T ∈ WildMenu.omMenuW n σ`
(N ≥ the shape's decision threshold; add the `hbulk`-style disc guard iff the statement-map demands
it), THERE EXIST `factors : Multiset ℤ_[p][X]` and per-factor `LocalFactorData` with
`f = factors.prod`, each monic irreducible, and `(factors.map (fun g => (eOf, fOf))) = σ.data`.
- **Citation:** GMN (arXiv:0807.2620v2) Thm 1.15/1.19 + Cor 1.20 (order-1 leaf dichotomy with
  explicit (e,f)) — the order-≤1 instances of Thm 3.1/3.7/Cor 3.8 — + Def 3.10/eq.(37); the project
  blueprint's Lemma 7.9 scoped to the current decided menus.
- **Faithfulness constraints:** quantified over genuine `f : ℤ_[p][X]` and the REAL classifier fiber
  (never a free shape); NO uniformity/rationality/measure/density term anywhere in the statement;
  existence only (no uniqueness clause needed for Wave 2 — uniqueness is extra strength, add only if
  a consumer needs it); the (e,f) tie is to σ.data as a MULTISET equality.
- **Deliberate non-imports** (unchanged): drainage (false of the truncated classifier), residual
  equidistribution (not GMN-stated).
- Process per the axiom policy: faithfulness entry (PROJECT_STATE trusted-base table +
  `AXIOM_FAITHFULNESS`-style write-up), guardian audit BEFORE merge, mutation checks = the W2a
  Eisenstein/degree-1 theorems must remain consistent with the axiom's concrete instances
  (e.g. at the n=2 wild fiber the axiom's asserted type {(2,1)} must cohere with the PROVED
  irreducibility: a mutated axiom asserting a split type there contradicts irreducibility —
  machine-checkable as a `example : False`-shaped probe against the MUTATED form in a scratch file,
  NOT committed).

### W2c — the faithfulness theorem + wiring
`theorem menuFiber_qpType (…) : ∀ f …, toBox f ∈ fiber T → T ∈ omMenuW n σ → ∃ data, qpType data = σ`
(direct from the axiom); capstone docstrings updated to state the semantic layer and its
conditionality; census entries (the capstones STAY core-only — the axiom is consumed only by the
faithfulness theorem, NOT by the density capstones; the theorem's footprint = core + om_leaf_faithful,
printed and documented); PROJECT_STATE/audit-log updates; fresh guardian audit.

## §3. Risks
- Bundle over/under-constraint (vacuous-or-false — the central risk): the non-vacuity witness (W2a-2)
  and the degree-1/Eisenstein coherence probes are the mandatory guards; audit statement-maps the
  bundle against "𝒪_L = integers of L" both directions.
- `IsIntegralClosure` + DVR joint satisfiability for genuine wild L: mathematically true, not
  provable at the pin for deg ≥ 2 — that is exactly what the axiom's existence clause carries; the
  witness only certifies the bundle TYPE is inhabited (degree 1), not every instance the axiom
  asserts. Document this honestly in the faithfulness entry.
- Eisenstein-fiber theorem needs the fiber ⟹ coefficient-valuation translation through `toBox`
  (v_p reads through `toZModPow` below level N — the small-N vanishing lemmas are the template).
