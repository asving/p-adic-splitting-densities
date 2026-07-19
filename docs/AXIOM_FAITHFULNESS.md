# Axiom faithfulness audit — the gate before turning BLUEPRINT §B into Lean axioms

**Date:** 2026-06-17. **Role:** Task #10 deliverable. Synthesis of four independent lens reports
(GMN-residual/polygon; GMN-descent/termination; non-GMN measure/defect/different; meta/cross-check)
plus an independent re-verification of every contested point against the **actual** GMN source
(arXiv:0807.2620v2, text extracted to `/tmp/gmn_full.txt` and `/workspace-vast/asving/tmp/gmn_check/`).

**Standard applied.** An axiom FAILS if it (a) claims more than the cited theorem (too-strong);
(b) is our conclusion in disguise (any uniformity/rationality/volume/p-independence claim is DERIVED,
never imported); (c) mis-states the math (wrong objects/hypotheses/formulas); (d) is a caricature the
real theorem doesn't support; (e) cites the wrong theorem/definition number.

---

## OVERALL GATE: **fix-first**

No axiom commits the cardinal sin (none imports uniformity/rationality/volume/p-independence as a
conclusion), and no axiom is mathematically false. But four items must be corrected in the axiom
*statements / citations* before they are written as Lean axioms, and three propagated downstream.
After these fixes the axiom set is a faithful literature transcription, safe to build on.

---

## Per-axiom verdict

### AX-GMN-I (finite-field residuals at every order) — **needs-fix (too-strong: "monic")**
- **Verified core (FAITHFUL):** GMN §2.1 builds a tower `F=F₀⊆…⊆F_r` of *finite* fields,
  `F_{i+1}=F_i[y]/(ψ_i)`, `[F_r:F]=f₀…f_{r-1}` (line 1520ff; "should not be confused with the finite
  field with i elements"). Def 2.21 (line 2397): `R_{λr}(f) := c_s + … + c_{s+de_r}y^d ∈ F_r[y]`, with
  "c_s and c_{s+de} are always nonzero, so that R has degree d and is never divisible by y." Degree
  `d=d(S)=ℓ(S)/e_r`. `f₀…f_{r-1} ∣ n` via Cor 3.8.
- **DEFECT:** Def 2.21 does **not** say `R` is monic. It says: degree exactly `d`, leading coeff
  `c_{s+de_r}` nonzero, `y ∤ R`. GMN factors `R` only up to associates (`∼`, Thm 3.7). The blueprint
  §A/§B drops the qualifier and writes "monic of degree d." (GMN_citations.md is honest:
  "monic (after normalization).")
- **FIX:** state as "`R_{λr}(f) ∈ F_r[y]` of degree exactly `d=ℓ/e_r`, leading coefficient a unit,
  `y ∤ R` (monic only after normalizing by the leading unit; GMN works up to `∼`)." Keep `F_r` finite,
  `[F_r:𝔽]=f₀…f_{r-1}`; note `∣n` is a derived consequence (separable degree-n ⇒ ∏fᵢ∣n), fine to keep.
- Benign for the program (BB3 counts factorization *shapes*, scale-invariant), but literal over-state.

### AX-GMN-II (lattice Newton polygon at every order) — **needs-fix (wrong-citation + normalization mis-statement)**
- **Verified core (FAITHFUL):** `N_r` is a principal/lattice polygon with p-independent combinatorics,
  index `e₁…e_{r-1}=D_r ≤ e`.
- **DEFECT 1 — wrong citation for the polygon object.** Blueprint §B cites "Def 2.3 / Lemma 2.4" for
  `N_r`. Verified: **Def 2.3** (line 1500) defines `P_t(x)`, the largest-degree type-`t` factor;
  **Lemma 2.4** (line 1509) is the type-membership criterion. Neither is the polygon. The order-`r`
  Newton polygon `N_r(f)` is defined in **§2.5, line 2174** ("We define the Newton polygon `N_r(f)`…",
  the principal polygon of negative-slope sides, line 2184). The correct "principal/lattice polygon"
  citation is **Def 1.1** (line 315, semigroup `PP`).
- **DEFECT 2 — normalization.** GMN's `v_r` is **ℤ-valued** ("`v_r : K(x)* → ℤ`", §2.2 line 1522;
  Def 2.5 line 1533: `v_r(P):=e_{r-1}H_{r-1}(S_{r-1}(P))`), so `N_r` lives in `ℤ×ℤ` in GMN's own
  coordinates. The `ℤ×(1/D_r)ℤ` lattice is the *project's* renormalization (rescaling `v_r` back to
  `v(p)=1`); `e₁…e_{r-1}` is the **index** with which `v_r` extends `v` (**Prop 2.6**, line 1572),
  not a coordinate denominator in GMN.
- **FIX:** cite **Def 1.1** (principal polygon) + **§2.5 (line 2174)** (definition of `N_r`) + **Def 2.5
  / Prop 2.6** (`v_r` integer-valued, index `e₁…e_{r-1}`). Word it: "`N_r` is a principal (integer-
  lattice) polygon for the order-`r` valuation `v_r` (Def 2.5); under the project's `v(p)=1`
  renormalization its slopes have denominators dividing `D_r=e₁…e_{r-1}≤e`, a p-independent integer
  (Prop 2.6, Cor 3.8)." Remove "Def 2.3 / Lemma 2.4." Strip editorial "p-independent combinatorics /
  wild slope = same lattice as tame" from the axiom STATEMENT (that is derived T-BB1, keep in prose).

### AX-GMN-III (leaf/descend dichotomy + descent trigger) — **FAITHFUL**
- **Verified verbatim:** **Cor 1.20** (order 1): `a_i=1 ⇒ G_i` irreducible, `f(L/K)=m·degψ_i`,
  `e(L/K)=e`. **Cor 3.8** (order `r`): `a_i=1 ⇒ G_i` irreducible, `f(L/K)=f₀…f_r`,
  `e(L/K)=e₁…e_r` — exactly `(e*,f*)=(e₁…e_r, f₀…f_r)`. Mult-≥2 = descend via Def 3.9 (`f`-complete ⇔
  `ω_r=1`) + Def 3.10 (sprouting). **Lemma 3.11** (line 3705): conditions equivalent — (1) `t_{r+1}=∅`;
  (3) "for all `t∈t_{r-1}(f)` and all `λ_r∈Q⁻`, `R_{λr}(f)` is separable." This is the descent trigger
  verbatim. Confirmed NOT conflated with the look-alike Lemma 4.8 (a two-poly resultant equivalence).
- **Precision note (not a defect):** mult-≥2 means "not yet resolved / descend," NOT "`G_i` reducible"
  (GMN gives `#factors ≤ a_i`). Blueprint correctly says "descends/refines." Separable⇔squarefree over
  `F_r` is a DERIVED finite-field (perfectness) fact, correctly not imported. Citation numbers correct.

### AX-GMN-IV (termination at finite order) — **needs-fix (too-strong: bundles "≤ e leaves" + p-indep depth + arbitrary-DVF scope)**
- **Verified core (FAITHFUL):** **Thm 4.18** (line 4364, monic separable `f`): `ind(f) ≥
  ind₁+…+ind_r`, equality iff `ind_{r+1}=0`. **Cor 4.19** (line 4374): "there exists `r≥0` such that all
  types in `t_r(f)` are `f`-complete, or equivalently `t_{r+1}(f)=∅`." This existence/finite-termination
  is exactly what the induction consumes.
- **DEFECT 1:** the axiom bundles "OM tree has ≤ e leaves." Cor 4.19 says nothing about a leaf count.
  (It is a trivially-true *separate* fact — a degree-`e` separable poly has ≤ e irreducible factors —
  but not what 4.18/4.19 assert.)
- **DEFECT 2:** the axiom's "p-independent depth bound." GMN bounds the step count by `ind(f)` ("finishes
  at most in ind(f) steps," intro line 88) — which is **p-DEPENDENT** (it is `v_p` of an index). The
  p-independent depth bound is DERIVED (T-Termination, from AX-DEFECT/AX-DIFFERENT), not imported.
- **DEFECT 3 (scope):** blueprint Faithfulness-Q says "over an arbitrary complete DVF." GMN fixes the
  base field to be a finite extension of `Q_p` (line 482: "We fix a finite extension `K` of `Q_p`…";
  abstract line 9: "over a p-adic field"). See the META framing finding below.
- **FIX:** state exactly Thm 4.18 (index inequality) + Cor 4.19 (existence of finite `r` with
  `t_{r+1}(g)=∅`), **for monic separable `g` over a p-adic field `K`**. Move "≤ e leaves" and the
  p-independent depth to the DERIVED column. Present "at most ind(g) steps" as cited prose, not formal
  statement.

### AX-GMN-KEY (existence of order-`r` key polynomial) — **FAITHFUL**
- **Verified verbatim:** **Thm 2.11**: "We can effectively construct a monic `φ_r(x)` of type `t` such
  that `R_{r-1}(φ_r) ∼ ψ_{r-1}`. This polynomial is irreducible over `O[x]` and satisfies `deg φ_r=m_r`,
  `ω_r(φ_r)=1`, `v_r(φ_r)=e_{r-1}f_{r-1}v_r(φ_{r-1})`." Degree `m_r=m_{r-1}e_{r-1}f_{r-1}` defined in the
  Def-2.1 type block. **Def 2.12** names it a *representative*. Existence over `O[x]`, the lift condition
  `∼ψ_{r-1}`, and the degree formula are exactly as stated. Citation numbers correct. (Pure-existence
  import; nothing derived smuggled in.)

### AX-MEASURE (Igusa box/shell Haar + unit-Jacobian CoV) — **FAITHFUL (minimal; advisory only)**
- **Verified:** Igusa §7.4 / Prop 7.4.1 is the p-adic change-of-variables formula (pullback measure
  transforms by `|Jac|_p`; unit-Jacobian ⇒ measure-preserving), corroborated via Potemans–Veys and
  Denef-type surveys citing [Ig4, Prop 7.4.1]. Box/shell: `μ{v(c)≥h}=Q^{-h}`, `μ{v(c)=h}=(1-Q⁻¹)Q^{-h}`
  from `[O_δ:p^mO_δ]=Q^m`. Product independence = product Haar.
- **KEY POSITIVE (minimality gate passes):** the assembled cell volume `(1-Q⁻¹)^V Q^{-A}` is NOT
  axiomatized. In `LeanUrat/L4.lean` it is PROVED (`cellVolume_eq`, sorry-free) from the per-column
  `columnMeasure` and the product-structure **hypothesis** `hfactor`. So AX-MEASURE does not smuggle in
  T-BB1/BB1. The Vandermonde self-loop exponent `e(e+1)/2-1` is a DERIVED theorem (L5fix), not an axiom.
- **ADVISORY (not a defect):** when written as a named Lean axiom, keep it as (a) box/shell measures,
  (b) product independence, (c) generic `|Jac|_p` CoV — leave the self-loop exponent downstream. Consider
  citing the box/shell normalization as "standard local-field Haar" rather than specifically Igusa §7.4
  (Igusa §7.4 is precisely the CoV/Jacobian piece).

### AX-DEFECT (complete DVF defectless: ∑eᵢfᵢ=[L:K]) — **FAITHFUL**
- **Verified (content):** Ostrowski: `[L:K]=∑ p^{n_i}e_if_i`, defect `p^{n_i}`. Residue char 0 ⇒ all
  defects 1 ⇒ every complete discretely valued field of char 0 (in particular `K/Q_p`, mixed char 0) is
  defectless; complete ⇒ unique extension (`g=1`) ⇒ `ef=[L:K]`. Equal-char-`p` Artin–Schreier defect
  towers correctly excluded by the mixed-char-0 hypothesis. Standard (Serre LF II.3 Cor to Prop 10;
  Neukirch ANT II.8.5; Kuhlmann "The Defect").
- **CAVEAT (numbering):** exact printed proposition numbers (Serre II.3 "Cor to Prop 10"; Neukirch
  II.8.5) verified on CONTENT, not at symbol level (book PDFs not machine-read). Confirm against the
  physical books before submission. Medium confidence on the number, high on the math.

### AX-DIFFERENT (Serre different bound) — **FAITHFUL**
- **Verified (content):** totally ramified separable degree-`e`: `d=e-1` iff tame (`p∤e`); wild
  `e ≤ d ≤ e-1+v_L(e)`, with `v_L(e)=e·v_p(e)`, so `e-1+v_L(e)=e+e·ν_P(e)-1` (matches Wikipedia/Weiss
  wild range). Tower multiplicativity `D_{L/F}=D_{L/K}·D_{K/F}` (Serre III §4 Prop 8). Confirmed via
  Cambridge Part III LF notes Thm 5.19 (= Serre III §6 Prop 13) and Wikipedia "Different ideal."
  The blueprint's annotation `v_L(e)=e·v_p(e)` is correct; the universal lower bound `e-1 ≤ d` is loose
  in the wild case (`d ≥ e` there) but valid and sufficient. Used only for the finite depth bound.
- **CAVEAT (numbering):** "III.6 Prop 13" and "III §4 Prop 8" verified on CONTENT via the Cambridge
  notes, not at symbol level. Medium confidence on the number, high on the math.

---

## Decisive answers to the gate questions

**Does any axiom secretly assert our conclusion (uniformity / rationality / volume / p-independence)?**
**NO.** All eight axioms are structural OM facts (finite-field tower, principal polygon, leaf/descend
dichotomy + separability trigger, finite termination, key-polynomial existence) or standard local-field
measure/ramification facts. The DERIVED targets (cell volume `(1-Q⁻¹)^V Q^{-A}`, count `Q_r^{d_r-1}`,
the rational function `R∈Q(t)`, p-independence) all live in the novel T-* theorems, never in an axiom.
The only residual risk is EDITORIAL: the prose around AX-GMN-II and the GMN_citations.md/BB3_infinity.md
narrative *phrase* p-independence as if imported. Strip every "p-independent / wild=tame / uniform"
adjective from the axiom STATEMENTS (keep them only in derived-theorem prose) so a referee cannot mistake
editorializing for an imported conclusion.

**Is the abstract interface a caricature?** **NO on the points checked — PROVIDED two design
constraints are enforced in Lean** (faithfulness flag A0):
1. `ResidueTower` `F_r` must carry `[Finite F_r]` AND `[F_r:F₀]=f₀…f_{r-1}` as a real field-extension
   degree tied to `deg ψ_i`, and `residual`'s codomain must be `Polynomial F_r` with `d=d(S)=ℓ/e_r` tied
   to the polygon side. If `F_r` is left an abstract "finite field" with `f_i` never tied to `deg ψ_i`,
   the "residual over a finite field" content (BB3's perfectness argument) is vacuous.
2. `childTypes` must fire ONLY at multiplicity ≥ 2 (`ω_r>1`), strictly drop `clusterSize` off the
   self-loop, and record the residue degree `f` peeled into the base extension (matching Def 3.10
   "non-f-complete" + Cor 3.8 `a_i=1⇒leaf`). The `selfLoopExponent e(e+1)/2-1` is a DERIVED project
   object, NOT a GMN field — keep it out of the GMN-faithful structure.

**Single highest-risk faithfulness gap:** the **pervasive base-field SCOPE over-claim** that "GMN holds
over an arbitrary complete discretely valued field" and "the wild/inseparable case is GMN's generic
case." Verified FALSE as a citation: GMN line 482 fixes `K` = a finite extension of `Q_p` (mixed char 0,
FINITE residue field); the paper treats only the mixed-char-0 / finite-residue-field / separable case.
This appears in GMN_citations.md §0/§3/§5 and BB3_infinity.md §1 (lines 41-42, 101-102, 144-147), §6,
§8 (line 645). The arbitrary-DVF / Henselian generality is a CORRECT folklore EXTENSION of the
Montes/MacLane framework but is NOT what arXiv:0807.2620 proves. It is the highest-risk gap because it
is (a) pervasive, (b) the *stated justification* for p-independence, and (c) exactly the kind of
over-claim the audit targets. **Substantively harmless**: the project's `K/Q_p` is finite (unramified)
over `Q_p`, so GMN applies per-`p` with identical combinatorial form, and the wild case the project needs
is wild RAMIFICATION in mixed char 0 (`p∣e_i`) — INSIDE GMN's `Q_p` scope; it is NOT residue-char-`p` /
inseparable-residue-field, which GMN never treats. **Fix:** re-derive p-independence as "the cited GMN
theorem has identical combinatorial form for every p-adic `K`," NOT as "GMN proved it over an arbitrary
complete DVF." If true arbitrary-DVF generality is ever wanted, cite the Montes/Nart Okutsu-frame /
MacLane-valuation literature instead of arXiv:0807.2620.

---

## Citation-number corrections

1. **AX-GMN-II:** remove "Def 2.3 / Lemma 2.4" as the citation for `N_r`. Def 2.3 = `P_t` (largest
   type-`t` factor); Lemma 2.4 = type-membership criterion. Correct: **Def 1.1** (principal polygon)
   + **§2.5, "We define the Newton polygon `N_r(f)`…"** (the polygon itself) + **Def 2.5 / Prop 2.6**
   (`v_r` integer-valued, index `e₁…e_{r-1}`).
2. **BB3_infinity.md §1 (lines 105, 114-115) and §8 (lines 643-644): WRONG-CITATION still live.**
   They print "(GMN-Polygon) [Def. 2.5, Thm. 2.11]" and "(GMN-Residual) [Def. 2.20–2.23, Thm. 2.26]."
   Verified: **Theorem 2.26 is the "Theorem of the product in order r"** (GMN line 2709), NOT the
   Theorem of the Residual Polynomial (that is **Thm 3.7**). Correct to: order 1 Thm 1.15 / 1.19, Cor
   1.20; order `r` Thm 3.1 / 3.7, Cor 3.8; residual poly Def 2.21; key poly Thm 2.11 / Def 2.12; trigger
   Lemma 3.11; termination Thm 4.18 / Cor 4.19. (The BLUEPRINT §B itself already uses the corrected
   numbers; only the consuming note BB3_infinity.md and the GMN_citations.md §4 propagation list it as a
   TODO were not yet applied to BB3_infinity.md.)
3. **AX-DEFECT / AX-DIFFERENT:** Serre/Neukirch printed proposition numbers (Serre LF III.6 Prop 13,
   III §4 Prop 8, II.3 Cor to Prop 10; Neukirch ANT II.8.5) verified on CONTENT only (edition-dependent
   numbering); confirm against the physical books before submission.
4. **GMN pagination:** all GMN theorem/definition NUMBERS in BLUEPRINT §B and GMN_citations.md match
   arXiv:0807.2620v2 verbatim (re-verified against the downloaded text). The arXiv-vs-TAMS-pagination
   caveat in GMN_citations.md header stands as the only residual numbering risk for GMN.

---

## Corrected faithful axiom list (what to write as Lean axioms)

- **AX-GMN-I.** For an OMType of order `r` and finite-slope side `S`: `R_{λr}(f) ∈ F_r[y]` of degree
  exactly `d=ℓ(S)/e_r`, leading coefficient a unit, `y ∤ R` (monic only after normalization; GMN uses
  `∼`). `F_r` finite, `[F_r:𝔽]=f₀…f_{r-1}`. [GMN §2.1 tower; Def 2.21.]
- **AX-GMN-II.** `N_r` is a principal (integer-lattice) polygon for the order-`r` valuation `v_r`; its
  faces/lengths/heights are lattice data; the index of `v_r` over `v` is `e₁…e_{r-1}=D_r`, dividing
  `e₁…e_r=e(L/K) ∣ e`. [Def 1.1; §2.5 (def of `N_r`); Def 2.5 / Prop 2.6.] (Renormalization to `v(p)=1`,
  giving the `1/D_r` denominators, is a project convention, not part of the axiom.)
- **AX-GMN-III.** (Unchanged.) Mult-1 residual factor ⇒ irreducible `p`-adic leaf with `(e*,f*)=
  (e₁…e_r, f₀…f_r)`; mult-≥2 ⇒ descend to order `r+1`; descent stops at order `r` iff every order-`r`
  residual is separable. [Cor 1.20 / Cor 3.8; Lemma 3.11(3).]
- **AX-GMN-IV.** For monic separable `g` over a p-adic field `K`: `ind(g) ≥ ∑_{i≤r} ind_i(g)` with
  equality iff `ind_{r+1}(g)=0` (Thm 4.18); hence there exists finite `r≥0` with `t_{r+1}(g)=∅` (every
  type in `t_r(g)` `g`-complete), i.e. the OM descent terminates at finite order (Cor 4.19). ("≤ e
  leaves" and any p-independent depth bound are DERIVED, not in this axiom.)
- **AX-GMN-KEY.** (Unchanged.) A repeated order-`(r-1)` residual factor `ψ_{r-1}` is lifted by a monic
  `φ_r ∈ O[x]`, irreducible over `O[x]`, of degree `m_r=m_{r-1}e_{r-1}f_{r-1}`, with `R_{r-1}(φ_r) ∼
  ψ_{r-1}`. [Thm 2.11 / Def 2.12.]
- **AX-MEASURE.** (a) `μ{v(c)=h}=(1-Q⁻¹)Q^{-h}`, `μ{v(c)≥h}=Q^{-h}` (standard local-field Haar);
  (b) product independence on `O_δ^e`; (c) a p-adic-analytic bijection multiplies Haar measure by
  `|Jac|_p`, so unit-Jacobian ⇒ measure-preserving [Igusa §7.4 / Prop 7.4.1]. (Cell volume and the
  Vandermonde self-loop exponent are DERIVED — T-BB1, L5fix — not axiomatized.)
- **AX-DEFECT.** (Unchanged content.) `K/Q_p` complete discretely valued of mixed char 0 ⇒ defectless;
  every finite separable `L/K` has `∑ eᵢfᵢ=[L:K]`, all defects 1. [Ostrowski; Serre LF II.3; Neukirch
  ANT II.8.5 — confirm printed numbers.]
- **AX-DIFFERENT.** (Unchanged content.) Totally ramified separable degree-`e` `L/K`: `e-1 ≤ d(𝔇) ≤
  e-1+v_L(e)`, `d=e-1` iff tame, `v_L(e)=e·v_p(e)`; tower multiplicativity of the different. [Serre LF
  III.6 Prop 13, III §4 Prop 8 — confirm printed numbers.]

---

## Net

`fix-first`. The eight axioms are within GMN's true scope (a finite extension of `Q_p`) and are faithful
in their load-bearing content; the abstract interface is not a caricature on the checked points (subject
to A0). Required corrections before building: (1) AX-GMN-I drop unqualified "monic"; (2) AX-GMN-II
re-cite (Def 1.1 + §2.5 + Def 2.5/Prop 2.6) and present the `1/D_r` lattice as the project's
renormalization; (3) AX-GMN-IV trim to the Thm 4.18 / Cor 4.19 existence statement and restrict to
p-adic `K`; (4) strip all "p-independent / arbitrary-DVF / wild=tame" framing from axiom statements and
from GMN_citations.md / BB3_infinity.md narrative — p-independence is DERIVED. Plus propagate the
BB3_infinity.md Thm-2.26 / Def-2.5-2.11 wrong-citation fix (already prescribed in GMN_citations.md §4)
and confirm Serre/Neukirch printed proposition numbers. No fatal failure; no conclusion-in-disguise.
