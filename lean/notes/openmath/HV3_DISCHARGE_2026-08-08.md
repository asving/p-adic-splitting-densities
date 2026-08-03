# (H-v3) DISCHARGE — the H_{r−1} generic display extracted from the sha256-pinned GMN TeX; v₃ = w₂ derived at e₀ = e₁ = 1

Unit chartered by synthesis pass 7 (`docs/SYNTHESIS_PASS7_2026-08-08.md` §F3,
queue #3): re-fetch `HigherNewton.tex` by the recorded hash, pin it into
`docs/references/`, extract the H_{r−1} display at generic r, check it against
the pinned evaluated r = 2 instance, and run the TR3-S3 §S1 sketch to a full
derivation of v₃ = w₂ at e₁ = 1. Genre: source-extraction + derivation note.
Parent displays: `TR3S3_2026-08-08.md` §S1 ((H-v3) + its derivation sketch),
`ADMREAL_2026-08-08.md` §REVISION-1 source-verification block (the original
sha256 pin + environment-count map). Numerics here are FALSIFIERS only; the
cover is already on file (§D6) and no new run is owed (the F3 charter:
"a further numerics pin adds nothing").

## D0. Verdict, as a defined term

**Definition (HV3-THM).** *(HV3-THM)* denotes the following scoped statement.
Setting: the standing TR3-S3 S0 tower setting restricted to states with
**e₀ = e₁ = 1** (e₂ unrestricted; the TR3-S3 stratum e₀ = e₁ = e₂ = 1 is
contained), under the normalized Bézout convention (H-ℓ), with w₁, w₂ the
project state valuations and v₃ the GMN order-3 valuation of the order-2 type
assembled from the tower's reads/keys under the standing GD23-row + TR-5
dictionary (the SAME §2-scope type-hood consumption TR3-S3 §S1 already makes
for GMN Defs 2.19–2.21 at r = 3 — no new obligation). Claim: for every nonzero
P ∈ O[x],

    v₃(P) = w₂(P),

and consequently, for f = Σ_i A_iΦ₂^i the Φ₂-development, the GMN order-3
ordinates satisfy u_i := v₃(A_iφ₃^i) = w₂(A_i) + i·w₂(Φ₂) — exactly the form
(H-v3) is consumed in at TR3-S3 §S1. Conditionality of (HV3-THM): it is a
theorem given ONLY [REV1, pass-1 gap 1: "(iv)" added — the D0 dictionary
consumptions were disclosed in D0 but omitted from this list]
(i) the **standing print-attribution baseline** for the sha256-pinned
    `HigherNewton.tex` (arXiv:0807.2620v2) generic displays extracted in §D2
    — Def 2.5, the H_{r−1} mapping display, Prop 2.6, Prop 2.7(3)(4) — read at
    r = 3 (generic-index instantiation, the same attribution status as every
    standing GMN pin; the source is the arXiv TeX itself, hash-pinned and
    re-fetched byte-identical this unit, so NO corrupted-extraction caveat of
    the fgmn.txt species applies on this leg);
(ii) accepted TR3-S1 (the r = 2 tie: v₂ = w₁ verbatim and v₂(φ₂) = w₁(Φ₁), at
    e₀ = 1);
(iii) the standing (H-CHAIN)-at-depth-3 + Lemma RESCALE consumptions
    (GRB S2.1: the project w_{j+1} is the MacLane-augmentation min over the
    Φ_j-development; trivial dilation at E₁ = E₂ = 1, which e₀ = e₁ = 1
    forces regardless of e₂).

(iv) the standing GD23-row/TR-5 projective dictionary and the r = 3 type-hood
    identifications it supplies (φ₂^GMN ↔ Φ₁, φ₃^GMN ↔ Φ₂,
    (e₂,h₂)^GMN = (e₁,h₁)^proj) — consumed at D0/D4 [REV1: made explicit in
    this list per pass-1 gap 1].


**VERDICT: (HV3-THM) HOLDS — the derivation is §D4, no gap was hit.** The
hypothesis (H-v3) of TR3-S3 is thereby DISCHARGED to the standing
print-attribution baseline: what TR3-S3 §S1 kept hypothesis-shaped was
exactly the H_{r−1} display at generic r ("the r = 2 instance was consumed
evaluated, never as a generic formula"); that display is now extracted
verbatim from the pinned source (§D2) and it evaluates to the sketch's
prediction (§D3, §D4). All consequence statements below reference (HV3-THM)
and add no further restrictions.

## D1. The source pin (re-fetch record)

* Recorded pin (ADM-REAL′ REVISION 1): `HigherNewton.tex`, sha256
  `8253d4d62cf3d180567d5e41429fdb0e4875abdc5d58db595dc66a24fb16bd18`,
  source arXiv:0807.2620v2 (GMN, *Newton polygons of higher order in
  algebraic number theory*).
* THIS UNIT re-fetched the e-print fresh from arXiv
  (`https://arxiv.org/e-print/0807.2620v2`, gzip of `HigherNewton.tex`):
  decompressed file sha256 IDENTICAL to the recorded pin, byte-for-byte equal
  to the prior fetch. The TeX is now PINNED IN-REPO at
  **`docs/references/HigherNewton.tex`** (2,897 lines) — the F3 charter's
  "pin the TeX into docs/references this time" duty, executed.
* Environment-count map RE-VERIFIED this unit: counting theorem-environments
  from `\section{Newton polygons of higher order}` (TeX 869): Def(type) 926
  = 2.1, Lemma(typedegree) 935 = 2.2, Def(ppt) 955 = 2.3, Lemma(factortype)
  962 = 2.4, **Def @ 985 = Def 2.5 (the v_r definition)**, Prop @ 1012 =
  Prop 2.6, **Prop(propertiesv) @ 1028 = Prop 2.7** — matching the ADM-REAL′
  count map (which cross-anchored seven labels) at every shared label.
* Standing caveat INHERITED UNCHANGED: the attribution is pinned to arXiv-v2;
  the published-TAMS numbering has never been checked against the printed
  PDF (`GMN_citations.md` header).
* **Symbol-overload caution (display duty).** The paper ALSO uses H for the
  *height* of a side: TeX 220–222 defines H(S) = the vertical-projection
  length, with d(S) = ℓ(S)/e = H(S)/h. The mapping H_{r−1} of §D2 (the
  λ_{r−1}-intercept datum) is a DIFFERENT object, defined at TeX 979–983 and
  consumed by Def 2.5. Nothing below touches the height-H.

## D2. The extracted displays (verbatim, TeX line cites)

All quotes from `docs/references/HigherNewton.tex` (arXiv-v2 numbering per
the §D1 count map). Standing §2 scope line, TeX 975: *"We fix a type $\ty$ of
order $r-1$ for the rest of section \ref{secNPr}."*

**(E1) The H_{r−1} generic display — TeX 979–983** (§2.2 [REV2: was §2.3, pass-2 gap 1 — subsection cite corrected; formulas and TeX-line cites unchanged], "The p-adic
valuation of r-th order", TeX 977; the object (H-v3) was waiting on):

    Consider the mapping
    $$
    H_{r-1}\colon \ss(\la_{r-1})\lra \Z_{\ge0},
    $$
    that assigns to each side $S\in \ss(\la_{r-1})$ the ordinate of the
    point of intersection of the vertical axis with the line $L_{\la_{r-1}}$
    of slope $\la_{r-1}$ that contains $S$. If $(i,u)$ is any point of
    integer coordinates lying on $S$, then $H_{r-1}(S)=u+|\la_{r-1}|i$;
    thus, $H_{r-1}$ is a semigroup homomorphism.

  GENERIC in r, one display for all orders — the "same normalization as the
  pinned r = 2 instance" question the TR3-S3 sketch had to leave open is
  CLOSED by the print itself: there is no per-r normalization freedom.

**(E2) Def 2.5 — TeX 985–991:**

    \begin{definition}
    For any nonzero polynomial $P(x)\in\zpx$, we define
    $$
    v_r(P):=e_{r-1}H_{r-1}(S_{r-1}(P)).
    $$
    Note that $v_r$ depends only on the reduced type $\ty^0$.
    \end{definition}

  Supporting notation, TeX 906–907 (§2.1, immediately before the §2.2 heading at TeX 977 [REV3: the label said "§2.2 preamble", pass-3 gap 1 — lines/content exact]): S_i(P) is the
  λ_i-component of N_i^-(P); s_i(P) its initial abscissa. The λ-component
  operator S_λ is Def(sla), TeX 361–367: L_λ(N) = the first-contact line of
  slope λ shifted up from below, S_λ(N) := N ∩ L_λ(N).

**(E3) Prop 2.6 — TeX 1012–1014:** *"The natural extension of $v_r$ to
$K(x)^*$ is a discrete valuation, whose restriction to $K^*$ extends $v$
with index $e_1\cdots e_{r-1}$."* (Printed proof at TeX 1016–1022 uses
exactly the L_{λ_{r−1}} support-line geometry of (E1)/(E2).)

**(E4) Prop 2.7(3)(4) (label `propertiesv`) — TeX 1028–1038**, items 3–4
verbatim (item 3's display at TeX 1034):

    \item If $P(x)=\sum_{0\le i}a_i(x)\phi_{r-1}(x)^i$ is the
    $\phi_{r-1}$-adic development of $P(x)$, then
    $$
    v_r(P)=\min_{0\le i}\{v_r(a_i(x)\phi_{r-1}(x)^i)\}
          =e_{r-1}\min_{0\le i}\{v_{r-1}(a_i)+i(v_{r-1}(\phi_{r-1})+|\la_{r-1}|)\}.
    $$
    \item $v_r(\phi_{r-1})=e_{r-1}v_{r-1}(\phi_{r-1})+h_{r-1}$.

  (E4) is the print's OWN evaluation of (E1)+(E2) on the φ_{r−1}-adic
  development — the support-line step the sketch would otherwise have owed as
  a convexity argument comes from the print, generic in r.

## D3. The charter-required check: (E1)+(E4) at r = 2 reproduce the pinned evaluated instance

Instantiate (E4) at r = 2 (GMN indices; order-1 data v₁ = w₀ the Gauss
valuation, v₁(φ₁) = 0 for the monic key, both per the standing TR3-S1 §S1
GMN rows): on the stratum e₁^{GMN} = e₀^{proj} = 1, |λ₁| = h₀,

    v₂(P) = min_m { w₀(b_m) + m·h₀ }   (φ₁-development P = Σ b_mφ₁^m)

— the accepted TR3-S1 §S1 pin's FIRST equality ("v₂(P) = min_m(w₀(b_m) + m·h₀) =
w₁(P)"); the pin's SECOND equality v₂(φ₂) = w₁(Φ₁) follows by applying the
all-P identity at P = φ₂ with the dictionary φ₂^GMN ↔ Φ₁ [REV1, pass-1 gap 2:
the substitution made explicit — the prior "VERBATIM the ... pin" claimed
both equalities reproduced when only the first was displayed]
(TR3S1_2026-08-08.md, GMN Defs 2.19–2.21 bullet). The generic displays specialize to EXACTLY what the trilogy consumed
evaluated at r = 2. Check PASSED; extraction-corruption discipline satisfied
(the generic formula now has its own decorrelated source leg, independent of
how the r = 2 instance entered).

## D4. The derivation of (HV3-THM)

Setting and dictionary as in D0. GMN data at r = 3 under the standing rows:
φ₂^{GMN} ↔ Φ₁, φ₃^{GMN} ↔ Φ₂; (e₂, h₂)^{GMN} = (e₁, h₁)^{proj} = (1, h₁)
at e₁ = 1, so λ₂^{GMN} = −h₁ and |λ₂| = h₁. Let P ∈ O[x] be nonzero and
P = Σ_i a_iΦ₁^i its Φ₁-development (= the φ₂^{GMN}-adic development; both
sides read the SAME development).

1. **[Print, (E2)+(E1)]** v₃(P) = e₂^{GMN}·H₂(S₂(P)) with H₂ the generic
   intercept mapping — consumed only through its print-evaluated form (E4).
2. **[Print, (E4) at r = 3]**
   v₃(P) = e₂·min_i{ v₂(a_i) + i(v₂(φ₂) + |λ₂|) }
         = min_i{ v₂(a_i) + i(v₂(φ₂) + h₁) }        (e₂^{GMN} = e₁ = 1).
3. **[Accepted TR3-S1]** v₂ = w₁ verbatim and v₂(φ₂) = w₁(Φ₁) (at e₀ = 1),
   totally in nonzero O[x] — applies to every a_i and to Φ₁. Hence
   v₃(P) = min_i{ w₁(a_i) + i(w₁(Φ₁) + h₁) } = min_i{ w₁(a_i) + i·γ₂ },
   with γ₂ = e₁w₁(Φ₁) + h₁ = w₁(Φ₁) + h₁ the project level-2 key value.
4. **[Project side, standing]** Under (H-CHAIN) at depth 3 + Lemma RESCALE
   (GRB S2.1 Application: "both valuations are the min over the SAME
   Φ_i-development of the same rescaled quantities"; E₁ = E₂ = 1 here, so
   the dilation is the identity), the project state valuation w₂ is the
   MacLane augmentation of w₁ at Φ₁ with w₂(Φ₁) = γ₂:
   w₂(P) = min_i{ w₁(a_i) + i·γ₂ } over the Φ₁-development.
5. **[Conclude]** v₃(P) = w₂(P) for every nonzero P ∈ O[x]. For the consumed
   ordinate form: u_i := v₃(A_iφ₃^i) = v₃(A_i) + i·v₃(φ₃) (v₃ is a discrete
   valuation, (E3); GMN also print this expansion at their (18)-note, the
   TR3-S1 §S1 Defs 2.19–2.21 pin), and v₃(A_i) = w₂(A_i), v₃(φ₃) = w₂(Φ₂)
   by step 5 applied at φ₃ ↔ Φ₂. So u_i = w₂(A_i) + i·w₂(Φ₂). ∎

Scope remark (honesty, not consumed): the derivation used e₀ = 1 (step 3's
accepted input) and e₁ = 1 (steps 2 (twice), 3 (the γ₂ substitution), and 4 (the E₁=E₂=1 site) [REV3]: dropping e₂^{GMN} and |λ₂| = h₁),
but NOT e₂ = 1 — v₃ reads only level-≤ 2 data. (HV3-THM) is therefore stated
at e₀ = e₁ = 1 with e₂ free; TR3-S3 consumes it strictly inside that scope.
No claim is made at e₀ ≥ 2 or e₁ ≥ 2 (there even the r = 2 tie v₂ = w₁ is
unavailable as accepted input, and the e-factors do not cancel — the
(TWIST-3) regime stays sealed, fence honored).

## D5. What stays displayed (NOT touched by this discharge)

* **(PIN-GEN-i)** — the FGMN-side attribution pin (Defs 3.15/3.16/3.18 at
  instantiated indices; owed fresh-pdftotext leg). Different paper, different
  pin; unchanged. NOTE the asymmetry: the GMN-side leg used here is the
  hash-pinned arXiv TeX itself — no corrupted shared extraction sits on this
  path, so no (PIN-GEN-i)-species caveat attaches to §D2.
* **(H-ℓ)** the normalized Bézout convention; **(KP_i)** + **[T]-properness**
  at TR3-S3 S6.2; the (H-CHAIN)/GD23/TR-5 standing consumptions — all exactly
  as displayed in TR3-S3. This unit removes ONE bracket: (H-v3).
* The TAMS-numbering pending-lookup caveat (§D1).

## D6. Numerics cover (on file; falsifiers, never proofs)

Already-recorded runs that operated under exactly the (HV3-THM) reading and
would have broken under any other v₃ normalization: STRATA3 P0 (GMN-3
integrity: t₂ ∈ ℤ, component shape, c ≠ 0 on-line — 0/6,468, sealed) and
CERT3 (PARI-certified order-3 towers; the 1,641-row reading-P discrimination
battery), plus the TR3-S3 composed E2E harness (`tr3s3_check.py`, TOTAL
30,813 checks / 0 failures on record) and the acceptance arc's three
independent implementations (93 + 1,564 + 821 checks, 0 failures). Per the
F3 charter, no further numerics pin is owed.
**Verifier-implementation expectation (pass-7 F2c, standing):** a from-note
verifier check of THIS note = implement v₃ two ways on random e₀ = e₁ = 1
towers — (a) geometrically via (E1)+(E2) (build N₂⁻(P), take the
λ₂-component's intercept, multiply by e₂) and (b) as the MacLane min-formula
w₂(P) of step 4 — and assert equality plus the step-5 ordinate identity on
Φ₂-developments; off-roster primes preferred.

## D7. Consequence and the bracket sites (fold duty = r31, NOT this unit)

Consequence of (HV3-THM): **TR-3′-GEN's order-3 scope becomes UNCONDITIONAL
ON PRINT** — the trilogy's only non-print hypothesis is gone; TR3-S3's S6.1
row ("THEOREM, conditional on (H-v3)") reduces to the standing
print-attribution baseline that every other trilogy pin already carries
(nothing becomes machine-checked or attribution-free that wasn't; the
(H-v3)-specific brackets become dischargeable citations of this note).

Live bracket sites, for the r31 fold (listed, DELIBERATELY NOT EDITED here):

* `lean/notes/openmath/TR3S3_2026-08-08.md` — 30 mentions, lines 34, 37, 53,
  66–68, 84, 144, 158, 167, 288, 299, 360, 363, 368, 371–372, 380, 412, 421,
  441, 443, 558, 599, 608–617, 688 (S0 displayed hypothesis; S1 pins incl.
  the derivation-sketch bullet this note completes; S6.1/S6.2/S6.3
  conditional rows; S7 scope box; S8 record).
* `docs/ROOT_ASSEMBLY_2026-08-02.md` — 14 mentions, lines 904, 960, 963,
  2491, 2608, 3612, 6435, 6611, 6620–6621, 6667, 6679, 6697, 6731 (the (H1)
  row displays + the §34 census patterns).
* `lean/notes/openmath/GRB_ORDER2_2026-08-05.md` — 3 mentions, lines 492,
  494, 509 (the post-acceptance scope brackets).
* Ancillary (state/charter/report docs — the fold's census owns them, they
  are not proof-note brackets): `docs/PROJECT_STATE.md` (2),
  `docs/SYNTHESIS_PASS7_2026-08-08.md` (8), `STRATA3_2026-08-08.md` (2),
  pass/VC reports (historical, never edited).

Acceptance criterion met in the F3 charter's own terms: "TR-3′-GEN order-3
conditionality reduces to standing print attributions" — that reduction is
(HV3-THM)'s clause list (D0 (i)–(iv)) [REV2: was (i)–(iii), pass-2 gap 2 — the stale cross-reference updated to include condition (iv)], on record above with verbatim
displays and line cites.

## REVISION 1 (orchestrator-applied, per pass 1)

Pass 1 (Codex; HV3_pass1_report.md): GAPS-ONLY 0C/2G — priorities A/B/scope all PASS
(the generic display genuinely r-generic; all five steps valid; e₂ never used). Fixes:
(1) condition (iv) added — the D0 dictionary/type-hood consumptions made explicit in
the conditionality list; (2) the D3 "verbatim" claim rescoped — the pin's second
equality now derived explicitly (one-line substitution at P = φ₂). Counter 0/2;
passes 2+3 decide.

## REVISION 2 (orchestrator-applied, per pass 2)

Pass 2 (Codex; HV3_pass2_report.md): GAPS-ONLY 0C/2G — the five-step derivation, both
REVISION 1 fixes, and the scope discipline all CLEAN. Fixes: (1) the D2 subsection cite
§2.3 → §2.2 (the pinned paper's own numbering; TeX lines unchanged); (2) D7's stale
"(i)–(iii)" cross-reference → "(i)–(iv)". Counter 0/2; passes 3+4 decide (pass 3 routed
to Fable for the model-diverse leg).

## REVISION 3 (orchestrator-applied, per pass 3 — Fable)

Pass 3 (HV3_pass3_report.md, 94415bf): GAPS-ONLY 0C/2G — the pin, all TeX cites, the
derivation, the four-condition closure, and the D3 specialization all verified
independently, PLUS a fresh two-way v₃ falsifier (615/615 at off-roster primes 5/11/13,
incl. 90 step-5 ordinate checks) — recorded here as the note's third external leg.
Fixes: (1) the TeX 906–907 location label corrected (§2.1, not "§2.2 preamble"; lines
exact); (2) the D4 scope remark's e₁ = 1 tally completed — e₁ enters at step 2 (twice),
step 3 (γ₂ = e₁w₁(Φ₁)+h₁), AND step 4 (the E₁ = E₂ = 1 site); the stated scope itself
was and is correct. Counter stays 0/2; passes 4+5 decide.
