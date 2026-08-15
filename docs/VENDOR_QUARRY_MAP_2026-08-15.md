# VENDOR QUARRY MAP — 2026-08-15 (Opus arm, read-only reconnaissance)

**What this is.** Append #56 cloned four external Lean libraries into `vendor/` (git-ignored) and
queued a unit to map them against the ledger's remaining MATH rows and the upcoming chapter
blueprints. This is that map. It is **reconnaissance only**: nothing was copied, nothing was
built, no statement in this repo changed.

**The four quarries and their pins.**

| quarry | Lean | mathlib pin | files | drift vs OUR pin |
|---|---|---|---:|---|
| `vendor/FLT` (ImperialCollegeLondon) | `v4.34.0-rc1` | `9058eaf3…` | 271 | **~2 months AHEAD** — adaptation = backport |
| `vendor/LocalClassFieldTheory` (mariainesdff) | `v4.22.0-rc2` | `81a4b04c…` | 66 | **~9 months BEHIND** — adaptation = forward-port, pre-module-system |
| `vendor/local_fields_journal` (CPP'24 artifact) | **Lean 3.51.1** | mathlib3 `32a7e535` (2023-08-05) | 49 | unusable as code; statements only |
| `vendor/norm_extensions` (ITP'23 artifact) | **Lean 3.49.1** | mathlib3 `4e42a9d0` (2022-11-28) | 18 | unusable as code; statements only |

**Our pin, for the record:** Lean `v4.31.0`, mathlib rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`,
tag `v4.31.0`, dated **2026-06-15**. Every "already have it" claim below was checked against
that tree at `leanfinal/.lake/packages/mathlib`, by path and declaration name.

**THE HEADLINE, stated before any table.** The single most consequential finding is not in
`vendor/` at all: **a large fraction of what these quarries were cloned for has already been
upstreamed into the mathlib we are pinned to.** Both mariainesdff Lean-3 artifacts are, to a
first approximation, *already ours* — `Mathlib/Analysis/Normed/Unbundled/` is the ITP'23
norm-extensions paper, and `Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean`
carries her copyright line verbatim. Read §2 before §4; several items the chapter blueprints
were about to carry as informal cites are citable Lean theorems at our own pin today.

---

## 1. What we actually need (the demand side)

Sources: `spec/HYPOTHESIS_LEDGER.md` (MATH rows), `spec/DAG_README.md` "THE CHAPTER CUT",
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` (the `[GN15]` NS rows), and the chapter specs
`spec/EFF-T2-*.md` (E), `spec/EFF-GENTOW*.md` + `spec/EFF-HETOW.md` (C),
`spec/EFF-GENIND*.md`/`EFF-GENHN*.md`/`EFF-GENH4*.md`/`EFF-W12*.md` (H).

### 1.1 The chapter letters, since they were relabelled

The `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md` §4 letters (B = leaf layer, E = induction,
F = σ-ladder, H = towers) are **superseded** by the computed cut in `spec/DAG_README.md`.
The live mapping is:

| ch | name | notes | |
|---|---|---|---|
| I | capstone and conditionality | `HYP.*`, `CAP:*`, `COND:*` | |
| **E** | **σ-LADDER MASTER** | `T2` (= HE7.A) | **HARD** |
| D | gauge + certificate T-chain | `T1, T3, T4, T5` | |
| **C** | **TOWER GRAMMAR** | `GENTOW1/3/4/5/6, HETOW` | **HARD** |
| B | HENSEL-SLOT CORE | `HE3, HE6, HE6R1, HE7` | |
| **H** | **GENERAL INDUCTION** | `GENIND, GENHN, GENH4, W12` | blueprint in flight |
| F | GRT weld layer | `GRTJA/B/C, GRTW2, WELDMASTER, LIFTCORNER, SIGMALAW` | |
| G | base cases and menus | `HMENU3, HEX3, W11, JD0` | fleet firing |
| A | landed Lean kernel | 34 `lean:` declarations | DONE |

### 1.2 The demand, by chapter, with the spec line that proves the need

**Chapter E (σ-ladder master, `T2`/HE7.A) — abstract-local-field-shaped, but axiomatized.**
The master is stated over a fixed complete DVR `O` with algebraic closure of `K₀`
(`spec/EFF-T2-s1of6.md:75`, `:93`), and quantifies over a **σ-ladder carrier** whose laws
`(NO-IRR)`, `(DEG-EF)`, `(FINITE-RES)`, `(RES-COMP)` are *interface axioms*
(`spec/EFF-T2-s1of6.md:1029`). Consequence for quarry-matching: a library plugs in at the
**instance** level, never at the master level. The concrete slots are:

- `(FUND)` — `|Ω| = [K₀(ρ):K₀] = e(ρ/K₀)·f(ρ/K₀)` (`spec/EFF-T2-s1of6.md:1002`), conditional on
  "`K₀` complete discretely valued; the orbit extension finite separable" (`:1015`).
- `(DEG-EF)` — `D = e_C·f_C`, "**explicitly not inferred from monicity**" (`:167`, `:184`).
- unique extension of `v` to `K₀-bar` (`:175`).
- `(FINITE-RES)`/`(RES-COMP)` — finite residue extension `k₀ ↪ K` with compatible embeddings
  (`:162`, `:181`).
- e/f multiplicativity along the tower (`:1077`, `:1007`).
- the resultant identity `(RES)`: `Σ_{ρ: f(ρ)=0} d·v(g(ρ)) = e₁·v(±Res(f,g))`
  (`spec/EFF-T2-s4of6.md:481`).

E needs **nothing** from higher ramification groups, the different, Krasner, Eisenstein, or
named MacLane/Okutsu machinery.

**Chapter C (tower grammar) — hybrid, and the field content is real.** The datum is integer +
residual stage data `(eᵢ,fᵢ,ψᵢ)` with the floor chain `u_{i+1} > e_{i+1}Eᵢ`
(`spec/EFF-GENTOW5-s1of2.md:735`), but the conclusions are about actual key polynomials over `O`
and an actual leaf field:

- key polynomials for `νᵢ` that are PRIME (monic, `O`-coefficients, irreducible over `K_v`)
  (`spec/EFF-GENTOW5-s1of2.md:761`).
- the MacLane chain `μ₀ -(x,λ₁)→ μ₁ -(Φ₁,λ₂)→ ⋯ → μ_r = ν_r`, stated in FGMN coordinates
  (`spec/EFF-GENTOW5-s1of2.md:735`).
- `L₂ :=` the completion of the leaf at a root, `k(L₂)` its residue field — a genuine finite
  extension of a complete DVF (`spec/EFF-GENTOW5-s1of2.md:175`).
- **LEMMA GENTOW5-A0: `gr` of a valued field is a graded division ring**
  (`spec/EFF-GENTOW5-s1of2.md:195`, `:202`) — the `gr(O_L)` frame.
- residual multiplicativity `R(gh) = R(g)R(h)`, `[CITED]` from FGMN Cor 4.7(3)
  (`spec/EFF-GENTOW5-s1of2.md:238`, `:921`; `spec/EFF-GENTOW6.md:318` disposition
  `cite-conditional supply`).
- residue-field tower rows over finite fields (`spec/EFF-HETOW.md:307`).

**Chapter H (general induction) — split.** `GENIND` is essentially combinatorial (window/digit/
drain bookkeeping over `O/π^N`; its classical list is "Hensel (coprime + monic-factor lifting),
Ore/GMN order-1, lower-hull geometry, generating functions", `spec/EFF-GENIND-s2of3.md:721`).
`GENHN`/`GENH4`/`W12` are field-shaped:

- `GENHN` **proves local-field structure theory**: value group of `R` contains `(1/e₁)ℤ`, so
  `e(R/O) ≥ e₁`; `η := res(θ^{e₁}π^{-h})` is a root of `ψ`, so `f ≥ f₁`; then
  "`e·f ≤ [R:Ô] = D' = e₁f₁` forces `e = e₁`, `f = f₁`"
  (`spec/EFF-GENHN-s1of2.md:1094`–`:1099`). **ERRATUM E3** corrects the carrier: `R = Ô[θ]` is a
  non-maximal order, so the statement must be run with `L := Frac(Ô)(θ)` and `O_L` **its
  valuation ring — a complete DVR** (`:1154`), `e·f = [L:base] ≤ deg Φ' = D'` (`:1160`).
  "**the false part is exactly 'R a complete DVR'**" (`:1105`). An integral-closure API is the
  named fix.
- `GENH4`: `Σ eᵢfᵢ = 4`; "Genre F always has even f (`F_{q²} ⊆ k_L`)"
  (`spec/EFF-GENH4-s1of2.md:461`); "`φ` is irreducible, **R is a complete DVR**, totally
  ramified" (`:563`).
- `W12`: "the τ-loci are **open by Krasner** on the étale locus and partition it; disc = 0 is a
  null set" (`spec/EFF-W12-s1of2.md:1024`, `:1026`, `:500`).

**The `[GN15]` cite scope (the leaf layer's imported theorems).** `[GN15]` = Guàrdia–Nart,
*Genetics of polynomials over local fields*, Contemp. Math. 637 (2015) 207–241, standing setting
"an arbitrary discrete valued field `(K,v)`" — the replacement for `[GMN12]`, whose scope is only
`K/ℚ_p` (`docs/GMN_citations.md` §6.0(2)). The imported statements, by NS row of
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`: NS-1 theorem of the polygon (all orders); NS-2
residual-polynomial theorem + leaf dichotomy (`ord_ψ(R)=1 ⟹ g_{λ,ψ}` irreducible, with
`e = e₀⋯e_r`, `f = f₀⋯f_r`); NS-3 the same at order `r` + Cor 3.3/3.8; NS-4 residue tower is
finite, `[F_r:F] = f₀⋯f_{r-1}`; NS-5 `N_r` is a lattice polygon; **NS-6 descent trigger**
(PARTIAL — no single published lemma states the biconditional, ~½ page to reprove); **NS-7
termination of the OM algorithm** (PARTIAL — its index step is discharged by ℚ_p-scope sources);
NS-8 existence of the key polynomial, `deg φ_r = m_r e_r f_r`; NS-9 theorem of the product
(`N⁻(fg) = N⁻(f)+N⁻(g)`, `R(gh)=R(g)R(h)`); NS-10 graded/residual ideal free of rank one;
NS-11 the GMN engine lemmas (with a normalization-shear obligation); NS-12 the FGMN `[Q1]`–`[Q10]`
inventory; **NS-14 defectlessness** ([Kuhl] Thm 3.3: every finite separable extension of a
discretely valued field is defectless, hence `Σ eᵢfᵢ = [L:K]`); NS-15 NOT-FOUND (Serre's
different bound is genuinely mixed-characteristic; the fix is a statement weakening, not a cite).

### 1.3 The valuation-theoretic MATH rows (7 of 21)

| row | statement | status |
|---|---|---|
| HYP.04 | strong Hensel: `v(F(x₀)) > 2v(F'(x₀)) = 2w`, `w ≥ 1` ⟹ some root has `v(r−x₀) > w` | **DISCHARGED** 2026-08-14, general complete DVR, stronger than stated |
| HYP.05 | `typeOf` shift invariance | **DISCHARGED**, general DVR |
| HYP.06 | `typeOf` scale invariance | **DISCHARGED**; level bookkeeping `π^N ↦ π^{N−3m}` still open inside HYP.08 |
| **HYP.07** | nonintegral-slope `CertRam3` — the nonintegral Newton-slope branch has the asserted cubic ramification type; "**norm/valuation proof absent**" | **OPEN** |
| **HYP.139** | `W-1` transport: the harness `w`/`R` to the FGMN MacLane-valuation/graded objects | **OPEN**, ATTEMPT grade |
| **HYP.143** | `HE3-BOX-6` (ii): the ramified base change `O ⇝ O[Π]/(Π^ℓ−π)` is stated too cheaply — `Φ'` need not remain irreducible over `O₂`; repair = higher-order Montes construction | **OPEN** |
| **HYP.144** | `GENTOW4-BOX-1`: the mixed-side multiplicity tie `μ₂*(r) = m_r`, "Ore-II/FGMN Lemma 2.17 content" | **OPEN** |

The other fourteen MATH rows (HYP.08/09/11, 67–71, 78–80, 88, 137, 146) are combinatorial,
counting, or measure-theoretic; **no external local-field library can touch them.** That is
itself the first half of the verdict.

---

## 2. THE MATHLIB BASELINE AT OUR OWN PIN (read this before any quarry table)

A quarry hit is worth something only if our own mathlib lacks it. Checked at
`leanfinal/.lake/packages/mathlib`, rev `fabf563a`, 2026-06-15.

### 2.1 PRESENT — things we can cite today, no adaptation, no quarry

| what | where | why it matters to us |
|---|---|---|
| **The unique-norm-extension theorem.** `spectralNorm_unique` (any power-multiplicative `K`-algebra norm on an algebraic `L/K` with `K` complete equals the spectral norm); `spectralNorm_unique_field_norm_ext` (any `AbsoluteValue L ℝ` extending `‖·‖_K` equals `spectralNorm`); `NormedAlgebra.norm_eq_spectralNorm` | `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:695`, `:766`, `:786` | **This is exactly "THE norm-extension uniqueness we cite informally" of append #56.** It is not a quarry item; it is a mathlib theorem at our pin. E's `:175` "the unique extension of `v`" slot is suppliable from here (via the norm↔valuation translation). |
| **`spectralValue`** — `spectralValue p = ⨆_{n < deg p} ‖p.coeff n‖^{1/(deg p − n)}`, with `norm_root_le_spectralValue`, `spectralValue_X_sub_C`, `spectralValue_eq_zero_iff`, `spectralValue_le_one_iff` | `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:115`, `:237`, `:142`, `:182`, `:202` | The **Newton-polygon top-slope bound in disguise**: an upper bound on root norms read off the coefficients, plus `spectralNorm K L y = spectralValue (minpoly K y)`. This is the closest thing in existence to a mathlib Newton polygon, and it is the natural first tool for **HYP.07**. |
| **The norm–valuation bridge, in normed language.** `spectralNorm_eq_norm_coeff_zero_rpow`: `spectralNorm K L x = ‖(minpoly K x).coeff 0‖ ^ (1/(minpoly K x).natDegree)`. Companion `spectralNorm_pow_natDegree_eq_prod_roots` | `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:987`, `:958` | Since `(minpoly K x).coeff 0 = ±N_{K(x)/K}(x)`, this **is** `\|x\|_L = \|N_{L/K}(x)\|_K^{1/[L:K]}`. **This is HYP.01's classical bridge** — see §2.5. |
| **Krasner's lemma.** `IsKrasner` class, `IsKrasner.krasner`, `IsKrasner.of_completeSpace` (instance for algebraic `L/K` with `K` complete), `of_completeSpace_of_normal` | `Mathlib/Analysis/Normed/Field/Krasner.lean:56`, `:63`, `:117`, `:73` | `W12`'s `:1024`/`:1026` Krasner-openness cite, and the three informal Krasner cites in `docs/HUMAN_PROOF.md:211`, `:418`, `:427`. |
| **The fundamental identity in general (flat) form.** `Ideal.sum_ramification_inertia_eq_finrank`: for a finite flat `S/R` over a domain and a prime `p`, `Σ_{q over p} e'(q)·f'(q) = finrank R S`. Also `sum_ramification_inertia_eq_finrank_fiber`, `sum_ramification_inertia_eq_card`, and the Dedekind version `Ideal.sum_ramification_inertia` | `Mathlib/RingTheory/RamificationInertia/Basic.lean:72`, `:44`, `:81`; `Mathlib/NumberTheory/RamificationInertia/Basic.lean:596` | E's `(FUND)`, `GENHN`'s `e·f ≤ [L:base]` step, `GENH4`'s `Σ eᵢfᵢ = 4`, and **NS-14 defectlessness restricted to the complete-DVR case**. |
| **`e·f = n` ALREADY SPECIALIZED TO THE LOCAL CASE.** `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` — docstring "`Ideal.sum_ramification_inertia`, in the local (DVR) case": for `R`/`S` Dedekind domains with **`[IsLocalRing S]`**, `[Module.Finite R S]`, `p` maximal in `R`, `p ≠ ⊥`, `K`/`L` their fraction fields — `ramificationIdx p (maximalIdeal S) * inertiaDeg p (maximalIdeal S) = finrank K L`. Rests on `IsLocalRing.primesOverFinset_eq` / `IsLocalRing.primesOver_eq` | `Mathlib/NumberTheory/RamificationInertia/Basic.lean:650`; `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean:1191`; `Mathlib/RingTheory/DedekindDomain/Basic.lean:178` | **This is `(FUND)` verbatim, at our pin.** (Upstream deprecated it 2026-07-01, i.e. *after* our 2026-06-15 rev — it is live and undeprecated for us, but any future mathlib bump must re-check.) See §2.3 for the one instance that still gates it. |
| `IsDiscreteValuationRing ⟹ IsDedekindDomain` for free (`IsPrincipalIdealRing.isDedekindDomain`, priority-100 instance); and **the integral closure of a Dedekind domain in a finite separable extension is a Dedekind domain**, as an instance | `Mathlib/RingTheory/DedekindDomain/Basic.lean:171`; `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:245` (`integralClosure.isDedekindDomain_fractionRing`), `:219`, `:233` | Two of the three hypotheses of the local `e·f = n` above are automatic for us. |
| **e and f are multiplicative in a tower.** `Ideal.ramificationIdx'_tower`, `ramificationIdx'_tower'`; `Ideal.inertiaDeg'_tower`; plus `ramificationIdx_eq_ramificationIdx'`, `inertiaDeg_eq_inertiaDeg'` reconciling the two API generations | `Mathlib/RingTheory/RamificationInertia/Ramification.lean:161`, `:146`, `:125`; `.../Inertia.lean:96`, `:79` | E `:1077`/`:1007` and C's stage composition. **Already ours.** |
| **A modern local-field class.** `IsNonarchimedeanLocalField` (ValuativeRel-based, Andrew Yang 2025), carrying `IsDiscreteValuationRing 𝒪[K]`, `Finite 𝓀[K]`, `CompleteSpace K`, `CompleteSpace 𝒪[K]`, `IsAdicComplete 𝓂[K] 𝒪[K]`, `ValuativeRel.IsDiscrete`, `valueGroupWithZeroIsoInt` | `Mathlib/NumberTheory/LocalField/Basic.lean:45`, `:108`, `:140`, `:157`, `:167`, `:176`, `:116` | Strictly newer and cleaner than mariainesdff's `MixedCharLocalField`/`EqCharLocalField` pair. If we ever want an abstract local-field carrier, **this** is the one to use, not the quarry's. |
| **DVR ⇄ discrete valuation round-trip** (the CPP'24 paper's headline). `IsDiscreteValuationRing.maximalIdeal` (as a `HeightOneSpectrum`), `isRankOneDiscrete`, `equivValuationSubring`, `exists_lift_of_le_one`, `associated_of_valuation_eq`, `intValuation_maximalIdeal` | `Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean:41`, `:46`, `:67`, `:120`, `:153` — **file copyright: María Inés de Frutos-Fernández, 2022** | Upstreamed. `vendor/local_fields_journal`'s central result is already in our tree. |
| Arithmetic Frobenius: `AlgHom.IsArithFrobAt`, `arithFrobAt` | `Mathlib/RingTheory/Frobenius.lean:54`, `:258` | Residue-field Frobenius if C/E ever needs it named. |
| Decomposition and inertia subgroups of a `ValuationSubring` | `Mathlib/RingTheory/Valuation/RamificationGroup.lean:30`, `:50` | Thin (no higher numbering) but present. |
| `HenselianRing` / `HenselianLocalRing` + `IsAdicComplete.henselianRing` | `Mathlib/RingTheory/Henselian.lean:94`, `:108`, `:170` | **Root**-lifting only. See §3. |
| `hensels_lemma` over `ℤ_[p]` with hypothesis `‖F.aeval a‖ < ‖F.derivative.aeval a‖^2` | `Mathlib/NumberTheory/Padics/Hensel.lean:458`, hypothesis at `:448` | This is **HYP.04's hypothesis verbatim, but only over `ℤ_[p]`.** See §3 — our `strongHensel` generalizes it. |
| Eisenstein polynomials: `IsEisensteinAt`, distinguished polynomials, integrality consequences | `Mathlib/RingTheory/Polynomial/Eisenstein/{Basic,Criterion,Distinguished,IsIntegral}.lean` | `GENHN`'s genre-E `h = 1` Eisenstein case (`spec/EFF-GENHN-s1of2.md:1149`). |
| `Valuation.HasExtension` + integer-ring/residue plumbing for an extension of valued fields (`maximalIdeal_comap_algebraMap_eq_maximalIdeal`, `Ideal.LiesOver` instance, `algebraMap_residue_eq_residue_algebraMap`) | `Mathlib/RingTheory/Valuation/Extension.lean:66`, `:202`, `:206`, `:209` | The scaffolding for an extension of complete DVRs — but **not** the existence theorem. |
| `C_p` and its spectral norm | `Mathlib/NumberTheory/Padics/Complex.lean:78` | The whole ITP'23 payload. |

### 2.2 CONFIRMED ABSENT from our mathlib (the real gap list)

Each of these was searched by declaration-name pattern and by directory. Absence is as
load-bearing as presence, so the searches are named.

1. **No Newton-polygon API of any kind.** `grep -rln "NewtonPolygon\|Newton polygon" Mathlib/` →
   zero hits. `spectralValue` (§2.1) is the only coefficient→root-norm tool.
2. **No MacLane / Vaquié / key-polynomial / Okutsu / Montes material.** Zero hits for `MacLane`,
   `key polynomial`, `Okutsu`, `Montes` (the `Montes`-pattern hits are all
   `CategoryTheory` false positives on "monomorphisms"). **This is chapter C's entire
   FGMN-coordinate layer, and it has no mathlib support whatsoever.**
3. **No `IsTotallyRamified` / `TotallyRamified` predicate.**
4. **No integral-closure-of-a-complete-DVR theorem.** No instance of the shape
   `IsDiscreteValuationRing (integralClosure O L)`, no `IsLocalRing (integralClosure O L)`, and no
   `IsAdicComplete` instance for such a ring. **This is precisely `GENHN` ERRATUM E3's named fix**
   (`spec/EFF-GENHN-s1of2.md:1154`) and the base of `typeOf` faithfulness (HYP.01). See §2.3.
5. **No structure theory for henselian local rings.** `HenselianLocalRing` is referenced in
   exactly one file — its own (`Mathlib/RingTheory/Henselian.lean`). Nothing downstream: no "a
   finite algebra over a henselian local ring splits into local factors", no "the prime above is
   unique". This is the *only* missing input to §2.3.
6. **No valuation-level uniqueness of the extension of `v` to a finite extension.** The *normed*
   version is present (`spectralNorm_unique`); the `Valuation`-language version is not, and
   `Mathlib/RingTheory/Valuation/ValuativeRel/` has only `Basic` and `Trivial`.
7. **No norm–valuation relation in `Valuation` language** — no `v_K(N_{L/K} x) = f_{L/K}·v_L(x)`.
   `Mathlib/RingTheory/Valuation/Minpoly.lean` is two trivial lemmas;
   `Mathlib/RingTheory/Valuation/FiniteField.lean` has no top-level declarations at all.
   **BUT the normed-language form IS present** — see §2.1's `spectralNorm_eq_norm_coeff_zero_rpow`
   row and §2.5. The missing piece is only the `‖·‖ ↔ addVal` translation, not the mathematics.
8. **No higher ramification groups in lower/upper numbering, no Herbrand functions, no
   conductor**; the different exists only in the Dedekind setting
   (`Mathlib/RingTheory/DedekindDomain/Different.lean`).
9. **No coprime-factorization Hensel.** See §3.

### 2.3 THE BOTTLENECK, isolated to one instance

This is the sharpest result of the whole survey, so it gets its own display. Chain the mathlib
facts of §2.1 for `O` a complete DVR with fraction field `K` and `L/K` finite separable, `S :=
integralClosure O L`:

```
O complete DVR
  ⟹ IsPrincipalIdealRing O ⟹ IsDedekindDomain O          [Basic.lean:171, instance]
  ⟹ IsDedekindDomain S                                    [IntegralClosure.lean:245, instance]
  ??? IsLocalRing S                                        ← THE ONLY MISSING LINK
  ⟹ e(m_O, m_S) · f(m_O, m_S) = finrank K L                [RamificationInertia/Basic.lean:650]
  ⟹ e and f multiplicative in a tower                      [Ramification.lean:161, Inertia.lean:96]
```

**One instance — `IsLocalRing (integralClosure O L)` for `O` a COMPLETE DVR — is the entire gap
between us and the classical `(e,f)` package.** Discharging it unlocks, in one stroke: E's
`(FUND)` (`spec/EFF-T2-s1of6.md:1002`) and `(DEG-EF)` (`:167`); `GENHN` ERRATUM E3's forcing step
`e·f = [L:base] ≤ D'` (`spec/EFF-GENHN-s1of2.md:1160`); `GENH4`'s `Σ eᵢfᵢ = 4`
(`spec/EFF-GENH4-s1of2.md:461`); `[GN15]` **NS-14** defectlessness restricted to the
complete-DVR scope; and the classical half of **HYP.01** `typeOf` faithfulness — the `[CORE-SET]`
row. It is also the mathematical content of the quarry's single best declaration (§4.2 item Q1).

The honest cost estimate for proving it ourselves: it is the statement "a finite algebra over a
henselian local ring with connected spectrum is local", or equivalently "a complete DVR has a
unique extension of its valuation" — a real theorem, not a one-liner, but a *bounded* one, and
one we now know has a sorry-free Lean-3 blueprint (§4.3).

### 2.4 Two mathlib-native routes to the bottleneck (SKETCHES — unverified, flagged as such)

Neither of these has been attempted; they are recorded so the chapter blueprints do not treat
§2.3 as a black box. **Both are conjectural proof plans, not results.**

**Route A — idempotent lifting up the adic tower.** `IsAdicComplete.le_jacobson_bot`
(`Mathlib/RingTheory/Henselian.lean` / `AdicCompletion`) forces every maximal ideal of `S` to
contain `m_O·S`, so `Spec S`'s closed points all lie over `m_O` and `S/m_O S` is a
finite-dimensional `k`-algebra, hence artinian with finitely many maximal ideals. Two or more of
them would give a nontrivial idempotent in `S/m_O S`; lifting it to `S` contradicts `IsDomain S`.
**The gap:** mathlib's idempotent lifting is only along **nil** ideals
(`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`,
`Mathlib/RingTheory/Idempotents.lean:324`; `OrthogonalIdempotents.lift_of_isNilpotent_ker`, `:273`)
— there is no lifting along an adically-complete ideal. It would have to be assembled by iterating
the nil case up `S/m^{n+1} → S/m^n` and taking an adic limit. We own that shape of argument
already (`HenselFactorization.exists_adicLimit_of_degree_lt`, the `NState` iteration in
`StrongHensel.lean`), so this is familiar territory rather than new machinery. Also note
`isLocalRing_of_isAdicComplete_maximal` (`Mathlib/RingTheory/AdicCompletion/LocalRing.lean:49`) is
a **near miss**: it needs the complete ideal to be *maximal*, which `m_O·S` is not unless
`e = f = 1`.

**Route B — read locality off our own Hensel factorization.** For `S = AdjoinRoot g` with `g`
monic and `ḡ` a power of a single irreducible, a splitting of `S` into two factors would produce a
coprime residual factorization of `ḡ`, which our landed
`HenselFactorization.exists_monic_factorization_dvr` lifts to a genuine factorization of `g`,
contradicting irreducibility. **This uses only landed assets** and would settle locality for the
carrier our `typeOf` actually uses (`normValues` is defined over `AdjoinRoot g`,
`leanfinal/Uniformity/Density/TypeOf.lean:180`–`:187`). **The honest caveat that keeps it from
closing §2.3:** `AdjoinRoot g` is in general a non-maximal *order*, not the integral closure — this
is exactly the error `GENHN` ERRATUM E3 corrects (`spec/EFF-GENHN-s1of2.md:1105`: "the false part
is exactly '`R` a complete DVR'"). Route B therefore serves HYP.01's `AdjoinRoot`-side needs but
does **not** by itself supply `IsLocalRing (integralClosure O L)`.

### 2.5 HYP.01 (`typeOf` faithfulness, `[CORE-SET]`) is closer than the ledger thinks

Our `inertiaDegOf g` is `sSup` of the positive common divisors of
`{ addVal O (Algebra.norm O x) : x ∈ AdjoinRoot g, x ≠ 0 }`, and `ramIndexOf g := deg g / f(g)`
(`leanfinal/Uniformity/Density/TypeOf.lean:180`–`:199`). HYP.01 asks that this agrees with the
classical `(e,f)`. The classical proof is `v_K(N_{L/K} x) = f·v_L(x)`, which follows from
`|x|_L = |N(x)|_K^{1/n}` together with `n = ef` (the extension's value group being `(1/e)ℤ`).
**Both inputs are at our pin:** the norm formula is `spectralNorm_eq_norm_coeff_zero_rpow` plus
`NormedAlgebra.norm_eq_spectralNorm` (§2.1), and `n = ef` is
`ramificationIdx_mul_inertiaDeg_of_isLocalRing` (§2.1) gated on §2.3's one instance.

So HYP.01's remaining work is: (i) §2.3's instance, and (ii) a `‖·‖ ↔ addVal` translation
(the real-valued spectral norm against our `ℕ∞`-valued `IsDiscreteValuationRing.addVal`).
**Neither is a quarry item.** This should be re-read before any chapter treats HYP.01 as
open-ended — and it is a `[CORE-SET]` row, so it deserves the owner's attention.

---

## 3. DUPLICATION: our Hensel layer vs. the outside world

Our layer, for reference: `leanfinal/Uniformity/StrongHensel.lean`
(`newton_step`, `NState` iteration, `strongHensel`, `strongHensel_addVal`,
`root_unique_of_strongHensel`, `exists_root_of_strongHensel`, gate `gate_fires`),
`leanfinal/Uniformity/HenselFactorization.lean` (`coeffIdeal` API, `exists_solve_field/mod/step`,
`exists_adicLimit_of_degree_lt`, `exists_monic_factorization`, `exists_monic_factorization_dvr`,
`monic_factorization_unique`, `exists_linear_factorization`, `exists_eq_add_mul_of_degree_lt`),
`leanfinal/Uniformity/MultiHensel.lean` (`exists_monic_factorization_finset`).

**Against mathlib at our pin (checked):**

| ours | mathlib | verdict |
|---|---|---|
| `strongHensel` / `strongHensel_addVal` — general complete DVR, no monicity, no `w ≥ 1`, **sharp** distance `k − w`, plus uniqueness in the disc `v(·−x₀) > w` | `hensels_lemma` (`Mathlib/NumberTheory/Padics/Hensel.lean:458`) — same hypothesis `‖F(a)‖ < ‖F'(a)‖²` but **only over `ℤ_[p]`**, distance only `< ‖F'(a)‖` | **ours is strictly stronger and strictly more general.** Genuine upstreaming candidate: it would subsume the `ℤ_[p]` file's main theorem. |
| `HenselianLocalRing`-style root lifting | present (`Mathlib/RingTheory/Henselian.lean`) | mathlib's is the *simple-root* case; ours is the *quantitative-slack* case. Complementary, not duplicate. |
| `exists_monic_factorization_dvr`, `monic_factorization_unique`, `exists_monic_factorization_finset` (coprime residual factorization lifts to a monic factorization over a complete DVR; two-block, `n`-block, and uniqueness) | **nothing.** mathlib's Henselian layer has no factorization statement; `UniversalFactorizationRing.lean` is a different (universal-algebra) object | **NOVEL relative to mathlib.** The strongest upstreaming candidate in the repo. |
| `coeffIdeal` API, `exists_adicLimit_of_degree_lt` | nothing comparable | novel plumbing; probably too repo-specific to upstream as-is. |

**Against FLT (checked directly, §4.5).** FLT contains **no** polynomial-factorization Hensel and
**no** quantitative/strong Hensel — the string `Hensel` appears in its local-algebra layer only as
the idempotent-decomposition material of `FLT/HenselianLocalRing/`. Therefore:

| ours | FLT | verdict |
|---|---|---|
| `strongHensel`, `strongHensel_addVal`, `newton_step`, `NState` iteration | nothing | **NOVEL relative to FLT.** |
| `exists_monic_factorization_dvr`, `monic_factorization_unique`, `exists_monic_factorization_finset`, `exists_linear_factorization` | nothing | **NOVEL relative to FLT.** |
| `HenselFactorization.exists_monic_lift` (`:369`) — monic lift of a monic residue polynomial | `IsLocalRing.exists_monic_map_residue_eq` (`FLT/Mathlib/RingTheory/DiscreteValuationRing/AdjoinRoot.lean:58`), which **additionally** returns `P.natDegree = pbar.natDegree` | **DUPLICATE, FLT's slightly stronger.** The only genuine overlap found in either direction. Ours has `natDegree_eq_of_map_eq` (`:376`) as a separate lemma; FLT bundles it. |

**Against LocalClassFieldTheory:** no overlap at all — its Hensel content is a single `sorry`
(`LocalField/GaloisConnection.lean:143`).

**Mutual-awareness note for future upstreaming, both directions.** *We → mathlib:* `strongHensel`
(generalizes and sharpens `Mathlib/NumberTheory/Padics/Hensel.lean:458` off `ℤ_[p]`) and the
coprime-factorization layer (no counterpart anywhere) are the two clean candidates. *FLT → us:* the
whole of §4.5. There is no collision: FLT went after the *idempotent/étale* side of henselian
local algebra, we went after the *polynomial-factorization and quantitative* side. Worth saying to
the FLT project if we ever open that channel — the two layers compose, and neither duplicates the
other.

---

## 4. THE QUARRIES

**Reading order:** if you want only the payload, go straight to **§4.5 (FLT)** — it is the only
quarry with sorry-free material on our critical path. §4.2–§4.4 are the three mariainesdff repos,
kept in clone order, and their upshot is mostly negative.

### 4.1 How the mariainesdff repos were dated

Two hard signals were used rather than guesswork. (i) `LocalClassFieldTheory.lean`, the root file,
annotates nearly every import with its mathlib PR number and comments out the ones that landed;
(ii) files that landed were physically moved to a `PR'ed files/` directory excluded from the
`lean_lib` target. **"Still imported in the root file" = not in mathlib at their pin.** Each
"UPSTREAMED" verdict below was additionally confirmed by locating the declaration in a mathlib
checkout.

### 4.2 `vendor/LocalClassFieldTheory` (Lean 4) — one real item, sorry-tainted; the rest upstreamed or scaffolding

**Repo health, stated up front: 114 `sorry`s across 15 files**, concentrated in
`LocalField/Basic.lean` (40), `LocalField/GaloisConnection.lean` (27), `Extensions.lean` (12). The
repo is mid-refactor — a `ℤₘ₀ → Γ` generalization in `Basic.lean` broke downstream proofs and they
were stubbed rather than fixed. Its pin (Lean 4.22.0-rc2) is nine releases behind ours.

**Q1 — THE ONE ITEM WORTH THE CLONE.**
`vendor/LocalClassFieldTheory/LocalClassFieldTheory/DiscreteValuationRing/Extensions.lean:621`

```lean
instance discreteValuationRing_of_finite_extension [FiniteDimensional K L] :
    IsDiscreteValuationRing (integralClosure hv.v.valuationSubring L)
```
(setting: `K` a field, `[Valued K ℤₘ₀] [IsDiscrete' hv.v] [CompleteSpace K]`, `L/K` finite;
in-source attribution "Chapter 2, Section 2, Proposition 3 in Serre's *Local Fields*")

- **Faithfulness to what we need:** this is §2.3's missing link **and strictly more** — DVR, not
  just local. Confirmed **not in mathlib** at any pin checked (`extendedValuation`,
  `discreteValuationRing_of_finite_extension`, `integralClosure_eq_integer`: zero hits).
- **Adaptation cost: HIGH, and not because of API drift.** The declaration's own body is clean,
  but it is **transitively `sorry`-tainted**: it rests on
  `instance isDiscrete_of_finite : IsDiscrete' (extendedValuation K L)` (`Extensions.lean:446`)
  whose proof is a **live `sorry` at `:464`**, which in turn rests on
  `def extendedValuation` (`:387`) whose `map_add_le_max'` field comes from `extensionDef_add`
  (`:289`) with a **live `sorry` at `:324`**. So this is a detailed ~900-line proof *sketch we
  would have to repair*, not a citable result. Add ~9 months of forward-porting on top.
- **Supporting declarations in the same file** (same taint): `extendedValuation` (`:387`),
  `integralClosure_eq_integer` (`:591`, body clean), `completeSpace` instance for `L` (`:567`,
  clean, rests on the now-upstreamed `spectralNorm.completeSpace`), `IsValExtension` instance
  (`:651`), and `expExtensionOnUnits_dvd : expExtensionOnUnits K L ∣ finrank K L` (`:211`, **live
  `sorry` at `:226`** — the closest thing in any quarry to `e ∣ n`).

**Q2 — `AdjoinRoot`-shaped DVR criterion.** `.../DiscreteValuationRing/AdjoinRoot.lean:141`

```lean
lemma IsDiscreteValuationRing_of_irreducible {f : A[X]} (hf1 : f.Monic)
    (hf : Irreducible (map (residue A) f)) :
    @IsDiscreteValuationRing (AdjoinRoot f) _ (isDomain_of_irreducible hf1 hf)
```
(Serre Ch. I §6 Prop. 15) — **directly relevant**: our `typeOf` is defined on `AdjoinRoot g`
(`leanfinal/Uniformity/Density/TypeOf.lean:180`), so this is the exact carrier we use, and the
"`f` irreducible mod `m`" hypothesis is our inert leaf. Body clean but **6 sorries in the file's
support lemmas** (`:62`, `:97`, `:118`). Companion `integralClosure_equiv_adjoinRoot` (`:180`,
Serre Ch. I §6 Cor. 1) is itself a **`sorry`** (`:187`).

**Q3 — the local-field class hierarchy.** `NALocalField` (`LocalField/Basic.lean:107`, clean,
marked in-source as mathlib PR 26449 *in flight*), `LocalField`/`NonarchLocalField`/
`ArchLocalField` (`LocalField/Defs.lean:6`, `Basic.lean:~68` — 2 + 40 sorries),
`EqCharLocalField` (`EqCharacteristic/Basic.lean:387`), `MixedCharLocalField`
(`MixedCharacteristic/Basic.lean:43`), and the only `e` for local fields anywhere in the repo:
`ramificationIndex : ℤ` (`EqCharacteristic/Valuation.lean:77`,
`MixedCharacteristic/Valuation.lean:87`) with `is_unramified_fpXCompletion`/`is_unramified_qP`.
**Verdict: DO NOT USE.** Our mathlib's `IsNonarchimedeanLocalField` (§2.1) is newer, cleaner,
sorry-free, and instance-rich; and the quarry's `ramificationIndex` is an **absolute `ℤ` for a
single field, not a relative index** — the wrong object for every one of our needs.

**Q4 — global-to-local, all three sorried.** `DiscreteValuationRing/Localization.lean:28`, `:54`,
`:59` (`adicValuedIsDiscrete`; `IsDiscrete'` on `K_v`; `IsDiscreteValuationRing R_v` for `R`
Dedekind, `v : HeightOneSpectrum R`) — **all three are `sorry` at `:31`/`:55`/`:60`, each with the
real one-line proof commented out.** The Lean-3 originals are complete (§4.3).

**Already upstreamed, so not quarry items** (each verified in mathlib): `Valuation.IsUniformizer`
and `pow_Uniformizer` (`DiscreteValuationRing/Basic.lean:134`, `:277`
→ `Mathlib/RingTheory/Valuation/Discrete/Basic.lean:200`ff);
`valuationSubring_isDiscreteValuationRing` (`:442` → `Discrete/Basic.lean:456`);
`IsDiscreteValuationRing.maximalIdeal`, `isRankOneDiscrete`, `equivValuationSubring` (`:461`,
`:467`, `:540` → `Discrete/IsDiscreteValuationRing.lean`);
**all of `FromMathlib/SpectralNormUnique.lean`** (`spectralNorm_unique`,
`spectralNorm_unique_field_norm_ext`, `spectralAlgNorm_mul`, `spectralMulAlgNorm`);
`spectralNorm_eq_root_zero_coeff` (`SpectralNorm.lean:165` → mathlib
`spectralNorm_eq_norm_coeff_zero_rpow`, **renamed**); `FromMathlib/CpDef.lean:113` (`ℂ_[p]`);
and lines 675–710 of `Extensions.lean` (→ `Mathlib/RingTheory/Valuation/Extension.lean`, renamed
to `Valuation.HasExtension`).

### 4.3 `vendor/local_fields_journal` (Lean 3, CPP'24) — the sorry-free blueprint for the bottleneck

`grep -rn sorry src/` → **nothing. The whole repo is sorry-free.** The proofs are unusable (Lean 3
/ mathlib3), but the *statements plus proof strategies* are the reference implementation for
exactly the material the Lean 4 port dropped or broke.

**Q5 — the ramification machinery that was DELETED in the Lean 4 port.**
`vendor/local_fields_journal/src/discrete_valuation_ring/residue_field.lean`

```lean
-- :155
lemma extended_eq_pow_ramification_index :
  (extended_max_ideal K L) =
    local_ring.maximal_ideal (integral_closure K₀ L) ^
      (ramification_idx (algebra_map K₀ (integral_closure K₀ L))
        (local_ring.maximal_ideal K₀) (local_ring.maximal_ideal (integral_closure K₀ L)))
-- :281
def quotient_linear_iso :
  ((integral_closure K₀ L) ⧸ (extended_max_ideal K L)) ≃ₗ[residue_field K₀]
    ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ ramification_idx …))
```
plus `ramification_idx_maximal_ne_zero` (`:114`), `ramification_idx_extended_ne_zero` (`:126`),
and `finite_dimensional_residue_field_of_integral_closure` (`:379`, `f < ∞` via
`quotient_range_pow_quot_succ_inclusion_equiv`).

**Why this is the item to keep:** `m_K·O_L = m_L^e` plus the residue-field-linear iso between the
two quotients is *the* local route to `e·f = n` — the ideal-theoretic content of §2.3 — and it is
**the only place in all four quarries where `e` is connected to ideal structure**. The Lean 4 port
deleted it and replaced `:379` with a call to mathlib's `ResidueField.finite_of_module_finite`,
recovering only the weaker finiteness conclusion. ~200 lines, sorry-free.

**Q6 — the complete local-field class and its two instances.** `src/local_field.lean:35`
(`local_field` class = complete + discrete + finite residue field) with
`eq_char_local_field.local_field` (`:52`) and `mixed_char_local_field.local_field` (`:74`)
**both complete** — where the Lean 4 versions sit on the sorried `isDiscrete_of_finite`.

### 4.4 `vendor/norm_extensions` (Lean 3, ITP'23) — DEAD WEIGHT, one casualty to note

Every mathematical result has been ported and upstreamed into the mathlib **we are pinned to**:
`spectralNorm`, `spectralValue`, `spectralAlgNorm`, `spectralMulAlgNorm`, `spectralNorm_unique`,
`spectralNorm_unique_field_norm_ext`, `smoothingSeminorm`, `seminormFromConst`,
`seminormFromBounded`, `IsPowMulFaithful`, `AlgebraNorm`, `algNormOfGalois`/`invariantExtension`,
`Basis.norm` + `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional`, and `ℂ_[p]`. Even
its two-`sorry` Fontaine-period-ring sketch (`src/Fontaine_period_rings.lean:50`ff — `B_HT`,
`A_inf`, `B_inf_plus`, `theta`, `B_dR`) is superseded by `Mathlib/RingTheory/Perfectoid/`
(`FontaineTheta.lean`, `Untilt.lean`, `BDeRham.lean`).

**The one casualty — record before deleting.** `src/spectral_norm.lean:646`, `:722`

```lean
max_root_norm_eq_spectral_value {f : algebra_norm K L} (hf_pm : is_pow_mul f) … :
  -- the max of the norms of the roots of a monic polynomial equals its spectral value
```
Not present in Lean 4 mathlib under any name found (mathlib has `spectralValue_X_sub_C`,
`spectralNorm_pow_natDegree_eq_prod_roots`, and the coeff-0 formula — but not the
max-over-roots identity). **This is the single most Newton-polygon-shaped statement in all four
quarries**, it is the `=` upgrade of mathlib's one-sided `norm_root_le_spectralValue`, and it is
the natural tool for **HYP.07** (nonintegral-slope `CertRam3`, "norm/valuation proof absent").

### 4.5 `vendor/FLT` — THE REAL QUARRY. Two zero-sorry clusters, both directly on our critical path

**Repo health:** 271 `.lean` files, **24 of them contain a `sorry`**, zero `proof_wanted`. Crucially,
**every file named below has ZERO sorries** (verified by `grep -c sorry` per file). FLT's pin is
Lean `v4.34.0-rc1`, ~2 months ahead of ours, so adaptation means *backporting*; every named
dependency below was checked for presence at our own pin and the result is recorded.

#### CLUSTER 1 — `FLT/HenselianLocalRing/` (712 lines, 0 sorries, Andrew Yang 2026)

File docstring, verbatim: *"Finite extensions of henselian local rings are products of henselian
local rings."* **This is §2.3's bottleneck, solved.**

**F1 — `FLT/HenselianLocalRing/Finite.lean:96`** (the item)

```lean
lemma HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing
    {R A : Type*} [CommRing R] [HenselianLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] :
    ∃ (n : ℕ) (e : Fin n → A) (he : CompleteOrthogonalIdempotents e),
      ∀ i, IsLocalRing (he.idem i).Corner
```

- **Faithfulness:** exactly the decomposition §2.4 Route A needed and mathlib lacks. Applied with
  `A := integralClosure O L`, which is a **domain**, the idempotent family must be trivial
  (`n = 1`, `e = 1`), so `A` itself is local — closing §2.3 and, with it, `(FUND)`, `GENHN` E3,
  `GENH4`'s `Σ eᵢfᵢ = 4`, NS-14 at complete-DVR scope, and HYP.01's classical half.
- **Companion in the same file:** `HenselianLocalRing.of_finite` (`:245`) — a finite *local*
  algebra over a henselian local ring is itself henselian. Also `exists_lift_of_to_ResidueField`
  (`:61`), `Ideal.isMaximal_of_isMaximal_under_of_formallyUnramified` (`:34`), and an
  étale-rigidity suite (`:314`, `:357`, `:371`, `:395`, `:410`).
- **Backport cost: MODERATE, and precisely one blocker identified.** All of `IsIdempotentElem.Corner`,
  `CompleteOrthogonalIdempotents`, `Algebra.Etale`, `Mathlib/RingTheory/Unramified/LocalStructure.lean`,
  `Mathlib/RingTheory/Etale/QuasiFinite.lean`, `Ideal.bijective_algebraMap_quotient_residueField`,
  `Localization.AtPrime.algebraOfLiesOver`, `Mathlib/RingTheory/LocalRing/Etale.lean` **are present
  at our pin.** The one blocker: `Finite.lean:102` calls
  `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`, which is defined
  **nowhere in FLT** — it lives in FLT's newer mathlib and is **absent from ours**. What we DO have
  is the single-idempotent predecessor `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`
  (`Mathlib/RingTheory/Etale/QuasiFinite.lean:378`), and FLT's `EtaleDecomposition.lean` (191 lines,
  0 sorries) contains the private induction from it to the family version
  (`..._forall_liesOver_eq_aux` `:25`, `..._forall_liesOver_eq'` `:109`). So the blocker is
  *bridgeable with material in the clone itself* — but that induction is the substantive step and
  must be re-elaborated against our pin.

#### CLUSTER 2 — the DVR/`AdjoinRoot`/unramified cluster (~540 lines, 0 sorries, Buzzard/Stoll/Claude 2026)

Six small files, all zero-sorry, all with **every mathlib dependency present at our pin**:
`FLT/Mathlib/RingTheory/DiscreteValuationRing/AdjoinRoot.lean` (210),
`.../DiscreteValuationRing/Separable.lean` (60),
`FLT/Mathlib/RingTheory/Unramified/LocalRing.lean` (120),
`FLT/Mathlib/RingTheory/RamificationInertia/Basic.lean` (46),
`FLT/Mathlib/FieldTheory/SeparableDegree.lean` (27),
`FLT/Mathlib/RingTheory/AdjoinRoot.lean` (77).

**F2 — `FLT/Mathlib/RingTheory/RamificationInertia/Basic.lean:28`** (the cheapest high-value item)

```lean
theorem Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [IsLocalRing S] [Algebra R S]
    [FaithfulSMul R S] [Module.Finite R S] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (IsLocalRing.maximalIdeal S).ramificationIdx R *
      (IsLocalRing.maximalIdeal S).inertiaDeg R = Module.finrank R S
```

- **Why it matters even though we already have `ramificationIdx_mul_inertiaDeg_of_isLocalRing`
  (§2.1):** FLT's in-source comment says it verbatim — *"`ramificationIdx_mul_inertiaDeg_of_isLocalRing`
  is deprecated in Aug 2026 so we use a longer name"*. Our copy is live only because our rev
  predates the deprecation. **This is the future-proof replacement**, in rank form
  (`Module.finrank R S`, which is what `GENHN`/`GENH4` actually want) rather than fraction-field
  form.
- **Backport cost: NEAR ZERO.** A 20-line proof over `Ideal.sum_ramification_inertia_eq_finrank`
  (ours at `Mathlib/RingTheory/RamificationInertia/Basic.lean:72`) and `IsLocalRing.primesOver_eq`
  (ours at `Mathlib/RingTheory/DedekindDomain/Basic.lean:178`). Both present. **Take this one.**

**F3 — `FLT/Mathlib/RingTheory/Unramified/LocalRing.lean:56`**

```lean
theorem exists_unramified_extension_of_residueField (k' : Type u) [Field k']
    [Algebra (ResidueField R) k'] [FiniteDimensional (ResidueField R) k']
    [Algebra.IsSeparable (ResidueField R) k'] :
    ∃ (L …) (S …), Module.finrank K L = Module.finrank (ResidueField R) k'
      ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] k')
```
(over `R` an arbitrary DVR with fraction field `K` — **no completeness hypothesis**; the bundle
also delivers `IsDiscreteValuationRing S`, `Module.Finite R S`, `IsFractionRing S L`,
`IsLocalHom (algebraMap R S)`, `Algebra.IsSeparable K L`)

**Unramified lifting at arbitrary degree.** Every finite separable residue-field extension lifts to
an unramified extension of the same degree. This is chapter E's `(FINITE-RES)`/`(RES-COMP)` supply
(`spec/EFF-T2-s1of6.md:162`, `:181`) and the constructor for `HETOW`'s residue-field tower rows
(`spec/EFF-HETOW.md:307`). **Backport cost: LOW** — it is assembled from F4 and F5 below, and
nothing else.

**F4 — `FLT/Mathlib/RingTheory/DiscreteValuationRing/AdjoinRoot.lean:121`**

```lean
theorem AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue
    {P : R[X]} [IsDomain (AdjoinRoot P)] (hPm : P.Monic) (hP0 : P.degree ≠ 0)
    (hirr : Irreducible (P.map (residue R))) :
    ((maximalIdeal R).map (algebraMap R (AdjoinRoot P))).IsMaximal ∧
      IsDiscreteValuationRing (AdjoinRoot P) ∧ IsLocalHom (algebraMap R (AdjoinRoot P))
```
(`R` an arbitrary DVR — again **no completeness**)

**This is THE INERT LEAF, classically.** Our landed `typeOf_inert_of_irreducible_map` (chapter A)
asserts the `typeOf` side; this asserts the classical side — `AdjoinRoot P` is a DVR, unramified
over `R`, `e = 1`, residue field `(ResidueField R)[X]/(P̄)`. Together they are HYP.01's inert-leaf
faithfulness. **Note it is the sorry-free proof of exactly the statement LocalClassFieldTheory
sorries (§4.2 Q2, Serre Ch. I §6 Prop. 15) — FLT wins that head-to-head outright.**

Same file, all zero-sorry and all useful in their own right:
- `IsLocalRing.of_isMaximal_map_maximalIdeal` (`:69`) — an integral algebra `S` over a local ring
  with `𝔪_R·S` maximal is local. **A general, four-line-to-apply locality tool** and a second,
  cheaper attack on §2.3 whenever we can show `𝔪_O·S` maximal.
- `AdjoinRoot.isMaximal_map_maximalIdeal` (`:105`) — `P̄` irreducible ⟹ `𝔪_A·A[X]/(P)` maximal.
- `AdjoinRoot.residueFieldEquiv` (`:81`) — `ResidueField (AdjoinRoot P) ≃ₐ AdjoinRoot (P.map (residue A))`.
- `IsLocalRing.exists_monic_map_residue_eq` (`:58`) — monic lift of a monic residue polynomial.
  **This DUPLICATES our `HenselFactorization.exists_monic_lift` (`:369`)** (see §3 addendum).
- `AdjoinRoot.isSeparable_root` (`:89`), `isSeparable_of_separable` (`:98`),
  `injective_of_not_maximalIdeal_le_ker` (`:37`), `isFractionRing_map` (`:177`),
  `exists_nonZeroDivisor_mul_eq_algebraMap` (`:148`),
  `Field.exists_monic_irreducible_adjoinRoot_algEquiv` (`:46`).

**F5 — `FLT/Mathlib/RingTheory/DiscreteValuationRing/Separable.lean:43`**
`Polynomial.Monic.separable_map_algebraMap_of_separable_map_residue` — separability transfers from
the residue reduction to the generic fibre. Small, needed by F3.

**F6 — `FLT/Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean:30`**
`exists_algebraMap_unit_eq_of_valuation_eq_one` — valuation-1 elements come from units of the
integer ring. Minor plumbing; listed for completeness.

#### CONFIRMED ABSENCES IN FLT

Searched by pattern across the whole tree:
- **No Newton polygon, no MacLane/Vaquié, no key polynomials, no Okutsu–Montes** —
  `grep -rniE "newtonpolygon|newton polygon|maclane|okutsu|key polynomial" FLT/` returns **nothing**.
  Chapter C's entire FGMN-coordinate layer has no support in FLT either. Combined with §2.2 and
  §4.5, this is now a **four-way confirmed absence**: it exists in no quarry and in no mathlib.
- **No higher ramification groups, no lower/upper numbering, no different, no conductor, no
  Herbrand functions.** (The `different`/`conductor` filename hits are prose false positives.)
- **No polynomial-factorization Hensel and no quantitative/strong Hensel.** `Hensel` occurs only in
  `FLT/HenselianLocalRing/{Finite,Stuff}.lean` (the idempotent-decomposition material above) and in
  unrelated files. See §3 addendum.

### 4.6 CONFIRMED ABSENCES ACROSS ALL THREE mariainesdff REPOS

Absence is load-bearing, so these are stated with the searches that found nothing.

- **No `e·f = n`, in any of the three repos** — not stated, not sorried, not commented out.
  (Ours has it; §2.1.)
- **No residue degree `f` at all.** `inertiaDeg`/`inertiaDeg'` appears in **zero** files across all
  three repos. Only `e` exists, in three forms: raw `Ideal.ramificationIdx`, and the absolute
  `ℤ`-valued `ramificationIndex` of Q3.
- **No tower multiplicativity of `e`** (no `e(C,A) = e(C,B)·e(B,A)`).
- **No uniqueness theorem for the extended valuation** — `extendedValuation` is *constructed*, but
  there is no "any valuation on `L` extending `v` equals it".
- **No Eisenstein polynomials** (zero hits for `eisenstein`); **no "totally ramified"**;
  "unramified" only as `e = 1` for the base field, one sorried lemma
  (`DiscreteValuationRing/Ramification.lean:25`, whose entire 30-line file *is* that one sorry),
  and sorried Galois-connection scaffolding.
- **Topic 6 is a total absence.** Grepping `newton|hensel|maclane|okutsu|montes|key_polynomial`
  across all 133 `.lean` files in the three repos yields **five** lines, all in
  `LocalField/GaloisConnection.lean`: an `import Mathlib.RingTheory.Henselian`, a section header,
  `instance henselianRing : HenselianRing [E]₀ (maximalIdeal [E]₀) := sorry` (`:143`), and two uses
  of it. **No Newton polygon, no key polynomials, no MacLane valuations, no Okutsu–Montes, no
  factorization over a complete DVR, anywhere.**

---

## 5. THE RANKED SHORTLIST (15 items)

Ranked by (value to a named chapter/ledger row) × (probability it survives adaptation). Every
"cost" is a backport estimate against Lean `v4.31.0` / mathlib `fabf563a`. Every row names what it
buys, so no row needs the reader to remember §1.

| # | item | where | cost | what it buys |
|---:|---|---|---|---|
| **1** | `Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing` | FLT `FLT/Mathlib/RingTheory/RamificationInertia/Basic.lean:28` (0 sorry) | **NEAR ZERO** — 20-line proof, both dependencies at our pin | `e·f = [S:R]` in **rank form**, the form `GENHN`/`GENH4` want; and the future-proof replacement for the mathlib lemma upstream deprecated in Aug 2026. Take verbatim. |
| **2** | `HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing` | FLT `FLT/HenselianLocalRing/Finite.lean:96` (0 sorry; cluster 712 lines) | **MODERATE** — one blocker: `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq` is absent at our pin; the induction to it from our `Etale/QuasiFinite.lean:378` is in `EtaleDecomposition.lean` and must be re-elaborated | **Closes §2.3's bottleneck**, hence in one stroke: E's `(FUND)`/`(DEG-EF)`, `GENHN` ERRATUM E3's forcing step, `GENH4`'s `Σ eᵢfᵢ = 4`, `[GN15]` NS-14 at complete-DVR scope, and the classical half of HYP.01 `[CORE-SET]`. **The highest-value item in the survey.** |
| **3** | `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue` | FLT `FLT/Mathlib/RingTheory/DiscreteValuationRing/AdjoinRoot.lean:121` (0 sorry) | **LOW** — all mathlib deps at our pin; two tiny FLT-local patch files (27 + 77 lines, 0 sorry) come along | **The inert leaf, classically**: over any DVR, `P̄` irreducible ⟹ `AdjoinRoot P` is an unramified DVR with `e = 1` and residue field `(ResidueField R)[X]/(P̄)`. Pairs with our landed `typeOf_inert_of_irreducible_map` to give HYP.01's inert-leaf faithfulness. Also the sorry-free proof of what LCFT only sorries. |
| **4** | `exists_unramified_extension_of_residueField` | FLT `FLT/Mathlib/RingTheory/Unramified/LocalRing.lean:56` (0 sorry) | **LOW** — assembled from #3 and #6 only | **Unramified lifting at arbitrary degree over an arbitrary DVR**, no completeness needed. Chapter E's `(FINITE-RES)`/`(RES-COMP)` supply (`spec/EFF-T2-s1of6.md:162`, `:181`) and the constructor for `HETOW`'s residue-tower rows (`spec/EFF-HETOW.md:307`). |
| **5** | `IsLocalRing.of_isMaximal_map_maximalIdeal` | FLT `.../DiscreteValuationRing/AdjoinRoot.lean:69` (0 sorry) | **NEAR ZERO** — six lines | A general locality tool: integral `S` over local `R` with `𝔪_R·S` maximal ⟹ `S` local. A **second, cheaper attack on §2.3** wherever we can show `𝔪_O·S` maximal, and it needs no henselian machinery at all. |
| **6** | `Polynomial.Monic.separable_map_algebraMap_of_separable_map_residue` | FLT `.../DiscreteValuationRing/Separable.lean:43` (0 sorry) | **NEAR ZERO** | Separability transfer residue → generic fibre. Needed by #4; independently useful wherever a spec says "the orbit extension finite **separable**" (`spec/EFF-T2-s1of6.md:1015`). |
| **7** | `AdjoinRoot.residueFieldEquiv` + `AdjoinRoot.isMaximal_map_maximalIdeal` | FLT `.../AdjoinRoot.lean:81`, `:105` (0 sorry) | **NEAR ZERO** | Identifies the residue field of our actual `typeOf` carrier. Directly feeds `inertiaDegOf`'s faithfulness. |
| **8** | `HenselianLocalRing.of_finite` | FLT `FLT/HenselianLocalRing/Finite.lean:245` (0 sorry) | **MODERATE** — same cluster as #2 | Finite + local over henselian ⟹ henselian. Lets a leaf order inherit henselianness, which is what `GENHN`'s stage tower needs when it descends into `O_L`. |
| **9** | `extended_eq_pow_ramification_index` + `quotient_linear_iso` | `vendor/local_fields_journal/src/discrete_valuation_ring/residue_field.lean:155`, `:281` (**Lean 3**, sorry-free) | **HIGH** — statements + strategy only; the proofs must be rewritten | `𝔪_K·O_L = 𝔪_L^e` and the residue-field-linear iso between the two quotients: the **ideal-theoretic** route to `e·f = n`. The only place in any quarry where `e` is tied to ideal structure. Keep as the fallback blueprint if #2 fails to backport. |
| **10** | `max_root_norm_eq_spectral_value` | `vendor/norm_extensions/src/spectral_norm.lean:646` (**Lean 3**, sorry-free) | **MEDIUM** — reprove in Lean 4 on top of mathlib's `spectralValue` API, which we already have | max of the root norms of a monic polynomial **equals** its spectral value — the `=` upgrade of mathlib's one-sided `norm_root_le_spectralValue`. **The most Newton-polygon-shaped statement in all four quarries**, and the natural instrument for **HYP.07** (nonintegral-slope `CertRam3`, "norm/valuation proof absent"). Not in Lean-4 mathlib under any name found. |
| **11** | `discreteValuationRing_of_finite_extension` | LCFT `.../DiscreteValuationRing/Extensions.lean:621` | **HIGH and tainted** — transitively `sorry`-dependent via `isDiscrete_of_finite:464` → `extensionDef_add:324`; plus 9 months of forward-porting | `IsDiscreteValuationRing (integralClosure O L)` — §2.3's link and more. **Superseded as a route by #2 + #5**, which are sorry-free. Keep as a *proof sketch* only. |
| **12** | `expExtensionOnUnits_dvd : expExtensionOnUnits K L ∣ finrank K L` | LCFT `Extensions.lean:211` | **HIGH** — **live sorry at `:226`** | The closest thing in any quarry to `e ∣ n`. Listed because the *statement shape* is what `GENHN`'s `e ≥ e₁` / `f ≥ f₁` sandwich argues around; the proof is absent. |
| **13** | `Localization.lean` global-to-local triple | LCFT `.../DiscreteValuationRing/Localization.lean:28`, `:54`, `:59` — **all three sorried**, real proofs commented out; **Lean-3 originals complete** at `local_fields_journal/src/.../global_to_local.lean:28`, `:62`, `:67` | **MEDIUM** | `IsDiscreteValuationRing R_v` for the adic completion of a Dedekind domain. Only relevant if a chapter ever instantiates our abstract `O` at a completion of a global ring; currently nothing on the critical path needs it. |
| **14** | `NALocalField` class | LCFT `LocalField/Basic.lean:107` | — | **DO NOT USE.** Listed to close the question: our mathlib's `IsNonarchimedeanLocalField` (`Mathlib/NumberTheory/LocalField/Basic.lean:45`) is newer, sorry-free, and instance-rich. LCFT's `LocalField` hierarchy carries 40 sorries in that one file. |
| **15** | `EqChar/MixedCharLocalField.ramificationIndex` | LCFT `EqCharacteristic/Valuation.lean:77`, `MixedCharacteristic/Valuation.lean:87` | — | **DO NOT USE.** Listed as a trap: it is an **absolute `ℤ` attached to one field**, not a relative index, so it is the wrong object for every `e` we need. |

## 6. VERDICT

**How much do these quarries change the chapter plans? Materially for one thing, not at all for the rest.**

1. **They do not touch the combinatorial mass.** Fourteen of the twenty-one MATH ledger rows are
   counting, drainage, or measure statements (HYP.08/09/11, 67–71, 78–80, 88, 137, 146). No
   local-field library can help, and none of these quarries pretends to.

2. **They collapse one bottleneck that four separate chapter obligations were each about to pay
   for separately.** `IsLocalRing (integralClosure O L)` for a complete DVR (§2.3) is the single
   missing link between mathlib's `e·f = n` and E's `(FUND)`, `GENHN`'s ERRATUM-E3 forcing step,
   `GENH4`'s `Σ eᵢfᵢ = 4`, `[GN15]` NS-14, and HYP.01's classical half. FLT solves it, sorry-free
   (shortlist #2), with a cheaper partial route also available (#5). **This is the one place the
   clone pays for itself.**

3. **Chapter C is unaffected, and now provably so.** C's need is MacLane/Vaquié key polynomials,
   `gr(O_L)` as a graded division ring, FGMN residual multiplicativity, and Ore/Montes ascent
   (`spec/EFF-GENTOW5-s1of2.md:735`, `:195`, `:238`, `:921`). **All of it is absent from all four
   quarries AND from mathlib** — a four-way confirmed absence. C must build its FGMN layer from
   scratch exactly as planned; the quarries change nothing about it. HYP.139 (`W-1` transport),
   HYP.143, HYP.144 are unaffected.

4. **Chapter E's master is unaffected; only its instances gain.** T2/HE7.A is axiomatized over a
   σ-ladder *carrier interface* (`spec/EFF-T2-s1of6.md:1029`), so a library plugs in at instance
   level only. What it gains: `(FUND)` via #1/#2, `(FINITE-RES)`/`(RES-COMP)` via #4, and — from
   mathlib, not the quarries — the unique extension of `v` via `spectralNorm_unique`.

5. **The biggest single win was not in `vendor/` at all.** Our own mathlib pin already contains the
   unique-norm-extension theorem (`spectralNorm_unique`), Krasner (`IsKrasner`), `spectralValue`,
   the norm–coefficient formula, the local `e·f = n`, e/f tower multiplicativity, and a modern
   local-field class. Append #56 listed "THE norm-extension uniqueness we cite informally" as a
   reason to clone `norm_extensions`; **it has been a citable mathlib theorem all along**
   (§2.1). Three informal Krasner cites in `docs/HUMAN_PROOF.md` and `W12`'s Krasner-openness cite
   are in the same position.

6. **HYP.01 `typeOf` faithfulness — the `[CORE-SET]` row — should be re-scoped.** Its classical
   bridge decomposes into (i) §2.3's instance and (ii) a `‖·‖ ↔ addVal` translation, with the
   mathematics supplied by mathlib (§2.5). It is not the open-ended obligation the ledger's
   `lean-open-statement` class suggests.

### Keep / drop

- **`vendor/FLT` — KEEP.** The only quarry with sorry-free material on our critical path. Two
  clusters (§4.5), ~1,250 zero-sorry lines, all mathlib dependencies at our pin bar one.
- **`vendor/local_fields_journal` — KEEP.** Counterintuitive (Lean 3, unusable proofs) but it is
  the *only sorry-free* mariainesdff artifact and the reference implementation for exactly what
  the Lean-4 port dropped: `𝔪_K·O_L = 𝔪_L^e` and the residue-quotient iso (shortlist #9). It is
  the fallback blueprint if #2 fails to backport. 49 small files.
- **`vendor/LocalClassFieldTheory` — KEEP, NARROWLY.** Value is now confined to
  `DiscreteValuationRing/Extensions.lean` as a *sketch*. 114 sorries across 15 files
  (`LocalField/Basic.lean` 40, `GaloisConnection.lean` 27, `Extensions.lean` 12); mid-refactor,
  nine mathlib releases behind us. Everything else is upstreamed or scaffolding. Do not cite it.
- **`vendor/norm_extensions` — DROP.** Fully upstreamed into the mathlib we are pinned to,
  including the Fontaine period rings (`Mathlib/RingTheory/Perfectoid/`). One casualty to record
  before deleting: `max_root_norm_eq_spectral_value` (shortlist #10).

### Quarry discipline reminder (append #56)

Nothing above has been copied. Any adoption is verbatim-copy-after-verification with provenance,
plus a kernel re-check against OUR pinned mathlib and an `AxChk` footprint run. A backported
declaration is a **new declaration in our tree**, so the dedup-audit rule applies: state
explicitly whether it is a verbatim move, and name the source file, line, commit, and licence.
**Licence status, checked:** `vendor/FLT` carries an Apache-2.0 `LICENSE` (same as mathlib) and its
per-file headers say "Released under Apache 2.0 license as described in the file LICENSE" — clean
for adoption. **The three mariainesdff clones have NO `LICENSE` file at all** (`ls vendor/*/LICENSE*`
finds nothing for them), so their terms are unresolved. Since every shortlist item we would
actually adopt is from FLT, this does not block anything — but do not copy from the mariainesdff
trees without settling it first. (This is a licence-provenance flag, not a legal opinion.)
