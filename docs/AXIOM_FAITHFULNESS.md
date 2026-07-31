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

---

# ADDENDUM (2026-07-30, verify-2 fold-in): entries for the AS-DECLARED Lean axiom set

**Status of the body above:** the 2026-06-17 sections are the FROZEN pre-Lean blueprint gate (Task #10
deliverable) auditing the PLANNED eight-axiom list. Several of those planned axioms were never declared
as Lean `axiom`s: AX-GMN-KEY, AX-DEFECT, AX-DIFFERENT, AX-GMN-I/II/IV have no Lean declaration (their
content became hypotheses, proved lemmas, or interface data); AX-MEASURE survives only as the `hfactor`
HYPOTHESIS of `L4.cellVolume_eq` (its axiom form `AX_columnMeasure` was declared, found FALSE-AS-STATED,
and DELETED — U3, `notes/MONTES_AUDIT.md`, 2026-07-02); AX-GMN-III's content survives as the
`omCells`/`descend`/`descend_size_lt` interface axioms. The verify-2 pass (2026-07-30) found the tree
declares exactly SEVEN axioms (comment-aware scan): five in `PadicMeasure.lean` (`omCells:268`,
`descend:272`, `descend_size_lt:278`, `clusterMeasure:405`, `AX_cellRecursion:438` — the first four
covered above under AX-GMN-III / the C' interface, the fifth being the Denef–Igusa wall) and two with
NO entry in this doc: `omReadValuation_lt_of_certLevel_fkeyed` (`OM/Classifier.lean:1114`) and
`om_leaf_faithful` (`OM/OmLeafFaithful.lean:489`). The three entries below close that gap. Primary
audits (semantic-guardian passes) live in `lean/notes/SEMANTIC_AUDIT_LOG.md`; these entries are the
faithfulness-doc mirror. **Each entry: DRAFT 2026-07-30 — PENDING ASVIN REVIEW.**

### AX-CELLREC = `PadicMeasure.AX_cellRecursion` (+ interface `clusterMeasure`) — **FAITHFUL** *(DRAFT 2026-07-30 — PENDING ASVIN REVIEW)*
- **Statement (as declared, PadicMeasure.lean:438):**
  `axiom AX_cellRecursion (T : OMShape) (q : ℕ) (hq : 1 < q) : clusterMeasure T q = ((omCells T).map
  (fun c => residualCountFn T c.residualDeg q * L4.bb1Value c.polygon q * (c.children.map (fun ch =>
  clusterMeasure ch.node q)).prod)).sum / omPivot T q` — the Igusa/Denef per-cell decomposition of the
  ONE fixed opaque cluster measure `clusterMeasure : OMShape → ℕ → ℚ` (itself an axiom asserting only
  that the symbol denotes a fixed function; no value/rationality content).
- **Verified core:** Igusa, *Local Zeta Functions* §7.4 / Prop 7.4.1 (p-adic change of variables) +
  Denef, Invent. Math. 77 (1984) 1–23 (cell decomposition); the eq-(4.1)/(4.2) form of
  `notes/BB3_infinity.md` §4.2 with multi-child product and per-cell count from the ACTUAL residual.
  Asserts ONLY the scalar measure-factorization identity — **no rationality/uniformity/p-independence**
  (those emerge via `OMInduction.clusterVol_isRational`, the cardinal-sin gate above passes).
- **Scope caveats:** (a) stated about FIXED objects (`clusterMeasure`, concrete `omPivot`) — the
  2026-06-19 soundness fix; the earlier free-binder form was INCONSISTENT and is gone; (b) consistency
  is witnessed by the compiled model `clusterMeasureModel` + `clusterMeasureModel_rec`; (c) measure
  route ONLY — the count-native capstone (`OM.RealInstanceV2.montes_unconditional`) does NOT consume it
  (its footprint is Lean-core; ground truth `AxChk_baseline.lean`).
- **Guardian audit:** `notes/SEMANTIC_AUDIT_LOG.md` AXIOMS section, `AX_cellRecursion` entry
  (2026-07-16 baseline) — CLEAN.

### AX-INDEX = `OM.Classifier.omReadValuation_lt_of_certLevel_fkeyed` — **FAITHFUL (narrowly scoped)** *(DRAFT 2026-07-30 — PENDING ASVIN REVIEW)*
- **Statement (as declared, OM/Classifier.lean:1114→1126):** for a box `g : monicBox p (N+1) n` with
  the bulk guard `hbulk : zmodValuation p (N+1) g.discr < N`, the two READ-SET-RESTRICTED guards hold:
  `GuardSuppR p N hN g ∧ GuardSideR p N hN g` (valuation `< N` at the hull-vertex abscissae and at the
  side columns up to `residualDeg S` — only what the OM reader touches).
- **Verified core:** GMN (arXiv:0807.2620v2 §4) Thm 4.18 / Cor 4.19 — the **theorem of the index**,
  `ind(f) ≤ v_p(disc f)`, specialized to the read-set. The single imported scalar fact, user-authorized
  as an axiom.
- **Scope caveats:** (a) f-keyed on the box's OWN discriminant valuation — the `hbulk` hypothesis is
  load-bearing (drop it and `g = xⁿ + pᴺ` refutes the statement; that counterexample killed the earlier
  UNIFORM `omReadValuation_lt_of_certLevel`, one of the two false axioms caught and removed);
  (b) quantified only over the read-set (`hullDots` / side columns), NOT all of `support`; (c) threshold
  is the box-native `zmodValuation p (N+1) g.discr`, not the retired PadicInt `certLevel`.
- **Guardian audit:** `notes/SEMANTIC_AUDIT_LOG.md` AXIOMS section, `omReadValuation_lt_of_certLevel_fkeyed`
  entry (2026-07-16 baseline) — CLEAN.

### AX-SERRE-DVR = `SerreLocalFields.AX_integralClosure_dvr` — **FAITHFUL (single clause of a named textbook theorem, instance-restricted)** *(Codex guardian STATEMENT AUDIT PASSED 2026-07-31 — verdict FAITHFUL-WITH-CAVEATS, axiom EXACT, caveats = entry phrasing only (fixed); `lean/notes/openmath/V3_serre_audit.jsonl` + BRIDGE_ADJUDICATIONS "VERIFICATION ROUND 1"; Group E consumers CLEARED and landed 2026-07-31 (BridgeE567_zfLaws/BridgeE9_zpBridge); declaration signed off with the 21-item queue, Asvin 2026-07-31)*
- **Statement (as declared, LeanUrat/SerreLocalFields.lean; declared 2026-07-31 under sign-off queue
  item 2, `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` C3/N1 + Asvin sign-off):**
  `axiom AX_integralClosure_dvr (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] :
  IsDiscreteValuationRing (integralClosure ℤ_[p] L)` — the integral closure of ℤ_p in a finite
  field extension of ℚ_p is a discrete valuation ring.
- **Verified core:** Serre, *Corps Locaux* (Hermann 1962; 2ᵉ éd. 1968) = *Local Fields* (GTM 67,
  Springer 1979, transl. Greenberg), **Chapter II ("Completion"), §2 ("Extension of a Complete
  Field"), Proposition 3**: for a complete discrete valuation ring `A` with fraction field `K` and
  a finite extension `L/K` of degree `n`, the integral closure `B` of `A` in `L` is a discrete
  valuation ring, a free `A`-module of rank `n`, complete, and carries the unique extension of the
  valuation. Numbering cross-checked against the de Frutos-Fernández–Nuccio formalization
  (`LocalClassFieldTheory/DiscreteValuationRing/Extensions.lean`,
  `integralClosure.discreteValuationRing_of_finite_extension`, docstring "Chapter 2, Section 2,
  Proposition 3 in Serre's Local Fields"; paper arXiv:2310.01998), which formalizes exactly this
  clause for abstract complete DVRs — independent confirmation the wall is real AND
  literature-grade. The axiom asserts **ONLY the DVR clause, only at (A, K) = (ℤ_[p], ℚ_[p])** —
  no freeness/rank, no completeness, no uniqueness-of-extension, no e·f = n, no lying-over (that
  last is DERIVED axiom-free: `SerreLocalFields.maximalIdeal_liesOver`, core-only footprint).
- **Scope caveats:** (a) the ℤ_p-algebra structure on `L` is PINNED to the composite through ℚ_p
  by the `IsScalarTower` hypothesis, and the quantification over arbitrary `Algebra ℚ_[p] L`
  structure maps φ is harmless: `integralClosure ℤ_[p] L` depends only on the image subring
  φ(ℤ_[p]), a complete DVR with fraction field φ(ℚ_[p]) by transport along the ring isomorphism —
  every instance is canonically equivalent (by transport) Prop. 3 at (A, K, L) = (φ(ℤ_[p]), φ(ℚ_[p]), L); (b) hypothesis-class
  non-vacuity is machine-checked (`axiom_nonvacuous` at L = ℚ_[p]; the degree-1 content is
  independently witnessed axiom-free at the `IsIntegralClosure` carrier by
  `OM/QpType.trivialFactorData`); (c) mathlib wall documented at `OM/QpType.lean` (no DVR-ness of
  `integralClosure ℤ_[p] L` at the v4.31.0 pin) and re-confirmed by the C3/N1 synthesis finding;
  (d) consumers: the item-2 re-pointed `MovesT.ramIdx`/`resDeg` dispatch (fired on the monic
  ℚ_p-irreducible locus by `isLocalRing_integralClosure_adjoinRoot`) and, post-audit, BP1 Group E
  (IB-E5–E7) + `OM/QpType.LocalFactorData` construction; the density capstones do NOT consume it
  (re-printed Lean-core in `AxChk_baseline.lean`, ground truth).
- **Guardian audit:** PASSED 2026-07-31 (the declared item-2 duty-(d) gate) — orchestrator-run
  Codex audit, artifact `lean/notes/openmath/V3_serre_audit.jsonl`, adjudicated in
  `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "VERIFICATION ROUND 1": axiom statement EXACT
  (precisely the DVR clause, no missing hypotheses, scalar-tower correct); the caveats were entry
  phrasing only and were fixed in the same round.  Group E dispatched on the pass; the consuming
  laws are `MovesU/BridgeE567_zfLaws.lean` (IB-E5/E6/E7) + `MovesU/BridgeE9_zpBridge.lean` (IB-E9),
  each printing exactly this axiom + core.

### AX-LEAF = `OM.OmLeafFaithful.om_leaf_faithful` — **FAITHFUL (menu-fiber-scoped; joint cite)** *(DRAFT 2026-07-30 — PENDING ASVIN REVIEW)*
- **Statement (as declared, OM/OmLeafFaithful.lean:489; current scope = W6q re-scope 2026-07-22):** for
  monic `f : ℤ_[p][X]` of degree `n` in a genuine classifier fiber (`fiberOf7`) of a shape
  `T ∈ ChainMenu7.omMenu7 n D K σ`, there EXISTS a `QpType.QpFactorization p f` with
  `QpType.qpType p F = σ` — existence of a genuine ℚ_p-factorization realizing the menu type.
- **Verified core:** GMN Thm 1.15/1.19 + Cor 1.20 (order-1 leaf dichotomy with explicit (e,f); the
  order-≤1 instances of Thm 3.1/3.7/Cor 3.8) + Def 3.10/eq.(37), **jointly with** the standard
  local-field structure theory the paper presupposes (integer rings of finite extensions of ℚ_p are
  DVRs; Serre, *Local Fields* I–II — unprovable at the mathlib pin, so the `LocalFactorData` existence
  is carried here).
- **Scope caveats:** (a) menu-fiber-scoped (arising-shape house form) — asserts nothing off the menu
  fibers; (b) EXISTENCE-ONLY: no uniqueness, and deliberate NON-imports = drainage (false of the
  truncated classifier), residual equidistribution, any translation-form GMN statement; (c) the menu has
  been widened by audited re-scopes (W3c/W4c/W5c/W6c/W6q), each with the prior form re-DERIVED as a
  theorem (`om_leaf_faithful_w6/_w5/_w4/...`) so consumers never widened silently; (d) safety evidence
  at declaration and at each re-scope: non-vacuity witnesses, mutation probes (`*_MUTATED` variants
  derive machine-checked `False` against axiom-free anchors), positive coherence gates.
- **Guardian audit:** `notes/SEMANTIC_AUDIT_LOG.md` 2026-07-21 Wild Wave 2 entry + re-scope audits
  #4–#7 — ACCEPT (with recorded flags). Consumed only by the faithfulness theorems; the density
  capstones remain Lean-core-only.

### AX-GMN-INDEX = `AX_GMN_index_finsum` — **STATEMENT DRAFT ONLY (NO Lean axiom exists; NOT-YET-DECLARED)** *(DRAFT 2026-07-31 — PENDING guardian audit + the two engine-side definitions + Asvin sign-off; NO consumer may cite it; declaration itself is gated)*
- **Statement (drafted, NOT declared; shape on record as `LeanUrat.GMNIndexAxiom.GmnIndexFinsumFace`,
  `lean/LeanUrat/GMNIndex.lean`, M15 dual-LITERATURE unit):**
  `axiom AX_GMN_index_finsum (n p : ℕ) [Fact p.Prime] (f : MonicBox n p) (hdz : f ∉ discZero n p)
  (R : Finset ℕ) : ∑ r ∈ R, gmnOrderInd p f r ≤ gmnInd p f` — every FINITE set of per-order GMN
  index contributions is dominated by the polynomial's index. The two constants are the deferral:
  `gmnInd p f : ℕ` (GMN Def 4.11 at O = ℤ_p) and `gmnOrderInd p f r : ℕ` (Def 4.15's ind_r(f),
  KEYED to the engine's pinned representative family, value 0 at r = 0) are NOT YET BUILT, and an
  axiom over `opaque` stand-ins is not a faithful transcription — it is satisfied by the all-zero
  functions (machine-checked vacuity witness `face_zero_witness` in the leaf). Hence the `axiom`
  keyword is withheld; the leaf ships the shape as a `def` + the declaration text + gates.
- **Verified core:** Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
  theory*, Trans. Amer. Math. Soc. 364 (2012), no. 1, 361–416 (arXiv:0807.2620v2), **Theorem
  4.18(1)** ("theorem of the index": ind(f) ≥ ind₁(f) + ⋯ + ind_r(f), f monic separable over O)
  with **Definitions 4.11** (ind(f) via irreducible factors + pairwise resultants), **4.12** (ind
  of a side/principal polygon), **4.15** (higher-order ind_t/ind_r; explicit representative-choice
  warning) and **Remark 4.14** (ind as a lattice-point count, whence ind_r(f) ≥ 0). The finite-sum
  face follows rigorously: nonnegativity + Thm 4.18(1) at r = max R dominate any finite subfamily
  (avoids all summability bookkeeping). Both twins verified the citation independently against the
  re-downloaded arXiv v2 text (Fable: `lean/notes/openmath/M15-x1a-align-gmn_fable.md` §1–§2, with
  executed numeric probes N1/N2/N4 — the 1548-case Def-4.12/`ind2` dictionary check, the §4.3
  worked family over ℤ₂, and a depth-2 two-increment family; Codex twin: results K1/K2, VERDICT
  LITERATURE). Theorem numbers are arXiv-v2; `docs/GMN_citations.md`'s standing caveat (confirm
  printed TAMS numbering before external use) applies.
- **Scope caveats:** (a) **representative-family keying is load-bearing**: per Def 4.15's own
  warning, ind_t(f) depends on the choice of representatives ("universally fixed family", §4.2
  opening convention), so `gmnOrderInd` is well-defined only relative to the engine's pinned
  family — the axiom must be declared against THAT definition, never a "canonical" value (residual
  OL-3 below); (b) **finite-sum face ONLY** — the axiom asserts nothing about histories, nodes,
  placement, or the engine; (c) **over-scoping trap (both twins, independently)**: declaring
  `∀ p, Nonempty (GmnOrderAccounting n p (X.gmn p))` (the KE8 carrier) as the axiom would import
  the `place`/`place_inj`/`place_charged` fields, which the paper does NOT assert — the same
  failure mode as the retired uniform read-guard axiom; the leaf's seam theorems
  (`orderAccounting_of_face`, `x1aAlignInc_of_face`, both Lean-core) machine-check that the face
  discharges `finsum_le` alone and every other field stays an explicit hypothesis; (d) the
  interface law `GMNIndex.p2` (2·ind f ≤ vdisc f) is NOT covered by this entry — both twins agree
  it needs separate disposition (classical, Ore-era: Def 4.11 + the per-factor
  v(disc F) = 2 ind(F) + v(disc L/K) which GMN itself only "recalls"; cite e.g. Serre, *Corps
  Locaux* III §6, or Neukirch III.2 — its own narrow cite or a proof, never folded in here);
  (e) hypothesis match is exact: monic ✓, separable ⇔ `f ∉ discZero` (monic, char 0) ✓, base field
  ℚ_p a special case of the paper's finite K/ℚ_p ✓, ℕ-valued ✓.
- **Residual (what `KT.cl15_align` = `MovesX.X1aAlignP n KC.XF ⟨true, false⟩` needs BEYOND the
  citation — the reconciled twin analyses):** Given the face, the row follows through the PROVED
  KE8 reduction `x1aAlignInc_of_orderAccounting` ONLY IF the engine discharges four open lemmas
  (Fable's OL-1–OL-4; the Codex twin packages the same content as one "Open Lemma L — ledger/GMN
  faithfulness" with four clauses + two remarks). The reconciliation map, explicit:
  * **OL-1 (injective order placement)** ↔ Codex L.1 + L.4: each certified-increment node of a
    stratum history is a genuine, DISTINCT accounting event of f's Montes flow — Fable: an
    injective map to GMN orders r with a type t_ν ∈ t_{r−1}(f) (mechanism: T1/T2 increments
    strictly grow the key degree m_r = m_{r−1}e_{r−1}f_{r−1}); Codex: an injection into
    "index-accounting events of the complete refined flow". **Route divergence, resolved:** the
    pinned axiom follows Fable's TAMS-only per-ORDER charging (single citation); Codex's charging
    to REFINED/cut indices ind^{H_r}_t(f) needs the companion paper (GMN, *Higher Newton polygons
    in the computation of discriminants…*, J. Théor. Nombres Bordeaux 23 (2011); Codex cites
    Def 3.3, Prop 3.4(b), 3.5(c), §3.3, Thm 2.5, Rmk 2.6) and is recorded as the FALLBACK
    mechanism for discharging OL-1/OL-2 if per-order placement fails on interleaved refinements —
    NOT as part of the axiom. Flag: the Bordeaux paper's numbering was NOT verified by the Fable
    twin this session (journal ref itself unverified — Fable §1); any discharge leaning on it must
    verify numbering first. Note the ⟨true, false⟩ state is design-load-bearing here: T1
    re-centerings are EXCLUDED from `dCert`, and Fable's N4/§7 worked example (GMN §4.3 family)
    exhibits a re-centering that GMN's own bookkeeping charges at a new order — the exclusion is
    what lets certified increments claim distinct orders without the refined-index apparatus.
  * **OL-2 (normalization crossing / per-order positivity)** ↔ Codex L.2 + L.3: the node's raw-
    frame side data (e, h, ℓ) must transport to a side of N_r^−(f) in the order-r valuation v_r's
    normalized coordinates (GMN Def 2.5) with the same (e, h) and the same ℓ ≥ 2 / ℓ = 1 class
    (Codex phrases the transport as region containment "after the integral shear"), giving
    ind_{t_ν}(f) ≥ 1, hence ind_r(f) ≥ 1 by nonnegativity of the other types' terms. The RAW-frame
    half is already machine-checked corpus-side and is NOT residual: `ind2Region`/XA9 prove
    ind2 = 2·|Remark-4.14 region| and 1 ≤ ind2 at T1/T2 (Codex's L.3 dictionary E = eℓ, H = hℓ,
    d = ℓ = Fable §3, brute-forced over 1548 configurations, 0 violations); what remains open is
    exactly the crossing.
  * **OL-3 (representative admissibility)**: the engine's canonical key lifts are GMN Def 2.12
    representatives forming ONE universally fixed family, so Def 4.15/Thm 4.18 apply as stated to
    the engine's data. Codex subsumes this under L.1's "valid refined Montes computation" and
    remarks representative choice is "not an obstruction"; kept EXPLICIT here because it fixes the
    MEANING of `gmnOrderInd` itself (scope caveat (a)) — it gates the axiom's declaration, not
    merely the placement proof.
  * **OL-4 (stratum scope)** ↔ Codex's `inStratum` remark: the real instance's `inStratum f H`
    must hold ONLY for ledgers of actual paths of f's canonical tree (the converse of the carried
    `gmnLink`); the row carries no `HistWF` hypothesis, so — as Codex puts it — its absence "is
    harmless only if `inStratum` itself enforces genuine-ledger semantics". Otherwise the
    placement legs are unprovable against junk histories.
  Consensus summary: both twins independently reached VERDICT LITERATURE (scoped), the SAME
  citation, the SAME face, and the SAME conclusion that the residual is engine-side
  implementation faithfulness, not literature; the only substantive divergence is the OL-1
  charging route (per-order vs refined-event), resolved above in favor of the single-citation
  per-order form with the refined route on record as fallback.
- **Guardian audit:** **PENDING — this is the declared gate.** Order of gates before ANY
  declaration: (1) `gmnInd`/`gmnOrderInd` built as real definitions with the representative family
  pinned (OL-3); (2) orchestrator-run Codex guardian audit of this entry + the drafted statement
  (quote-and-classify, per the axiom policy — the process that caught two false axioms);
  (3) Asvin sign-off. Until all three: no `axiom` keyword, no consumer, no footprint change
  (`AxChk_baseline` untouched — nothing to print).
