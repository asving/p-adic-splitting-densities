# HV3 pass 5 — hostile verification of HV3_DISCHARGE_2026-08-08.md (REVISION 3)

Verifier: Fable (model-diverse leg #2; a different model's pass 4 was CLEAN).
Fresh context; NO prior pass report read (`HV3_pass1..4_report.md` untouched —
the REVISION 1–3 blocks inside the target note itself were read as part of the
target). Repo epoch verified against: HEAD `af88f12`; the note's landing commit
`f90d68a` and its revision commits `bc34acf` (REV1), `e3425b1` (REV2),
`0170d68` (REV3) consulted for epoch-stamped claims only. Charge: verify the
sha256 pin myself; check every cited TeX line + the §2.1/§2.2 location labels;
the 5-step derivation; the four-condition closure (hunt for unlisted
consumptions); the D3 specialization; the e₂-never-used scope; the completed
e₁ tally; the consequence display (no bracket edits); own spot-check numerics.
Quote-and-classify; fix nothing. FULL pass.

## 1. The source pin (D1) — VERIFIED, plus an independent fourth leg

* `sha256sum docs/references/HigherNewton.tex` run by me:
  `8253d4d62cf3d180567d5e41429fdb0e4875abdc5d58db595dc66a24fb16bd18` — equal
  to the D1 recorded pin and to the ADM-REAL′ REVISION-1 record
  (`ADMREAL_2026-08-08.md:202`). File is 2,897 lines as D1 states.
* **Independent re-fetch executed by THIS pass**: `curl
  https://arxiv.org/e-print/0807.2620v2` → gzip stamped `HigherNewton.tex`,
  2008-10-31, decompressed sha256 IDENTICAL (`8253d4d6…bd18`). D1's
  "re-fetched … byte-identical" process claim is now reproduced by a fetch
  the note's author never saw. (That makes the pin's legs: ADM-REAL′ fetch,
  the HV3-unit fetch, pass-3's claimed leg, and this pass's fetch.)
* Landing commit `f90d68a` diff-stat = exactly {`docs/references/HigherNewton.tex`
  (+2,897), the note (+250)} — the pin genuinely entered the repo at this unit,
  and nothing else was touched (feeds §7 below).

## 2. Environment-count map and §2.1/§2.2 labels (D1/D2) — VERIFIED

* Preamble (TeX 3–11): ONE shared counter — `\newtheorem{theorem}{Theorem}[section]`
  with lemma/remark/definition/**notation**/corollary/proposition all
  `[theorem]`. My scan included `notation` (the omission that would silently
  shift the count); no align/eqnarray/gather in the file; `\def\be{\bigskip}`
  (TeX 31), so the `\be\be` after Def 2.5's picture numbers nothing.
* §2 = the SECOND numbered section (TeX 197 Introduction is starred; §1 at
  TeX 218; §2 `secNPr` at TeX 869). Complete list of shared-counter
  environments in TeX 869–1050, in order: Def@926 (`type`), Lemma@935
  (`typedegree`), Def@955 (`ppt`), Lemma@962 (`factortype`), Def@985,
  Prop@1012, Prop@1028 (`propertiesv`) — i.e. 2.1–2.7 exactly as D1 maps them,
  with NO intervening environment. Extending the count: 2.11 `phir`@1257,
  2.12@1284, 2.17 `shape`@1401, **2.19–2.21@1431/1447/1497**, 2.26
  (product)@1662 — every label ADM-REAL′ cross-anchored reproduces, and the
  "GMN Defs 2.19–2.21" cites in D0/D3/step 5 carry the right numbers.
* Subsections: §2.1 `Types of order r−1` @ TeX 872; §2.2 `The $p$-adic
  valuation of $r$-th order` @ TeX 977. Hence: (E1) at TeX 979–983 IS in §2.2
  (REV2 correction verified correct); TeX 906–907 IS in §2.1 (REV3 correction
  verified correct); the §2 scope line IS TeX 975; the §2.2 heading title
  matches verbatim.

## 3. The extracted displays (D2) — every quote checked against the TeX

* **(E1) TeX 979–983**: byte-faithful modulo re-wrapping. The display is
  genuinely GENERIC in r — one mapping definition for all orders, no per-r
  normalization freedom anywhere in §2.2. D2's headline reading is correct.
* **(E2) Def 2.5, TeX 985–991**: verbatim; the only elision is the trailing
  `\medskip` on line 991 after `\end{definition}` (inconsequential).
* **(E3) Prop 2.6, TeX 1012–1014**: verbatim. The proof block is TeX
  1016–1022 as cited, and it does run on the L_{λ_{r−1}} support-line
  geometry (`L_P=L_{\la_{r-1}}(N_P)`, "all points … lie above the line").
* **(E4) Prop 2.7(3)(4), TeX 1028–1038**: items 3–4 verbatim; item 3's
  one-line display is exactly TeX 1034; item 4 at TeX 1036;
  `\end{proposition}` at 1038.
* Supporting cites: TeX 906–907 (S_i(P) = the λ_i-component of N_i⁻(P);
  s_i(P) its initial abscissa) — exact. Def `sla` TeX 361–367 (L_λ(N)
  first-contact line, S_λ(N) := N ∩ L_λ(N)) — exact. Height-overload duty:
  TeX 220–222 does define H(S) = vertical-projection length with
  d(S) = ℓ(S)/e = H(S)/h — the D1 caution is accurate and the note touches
  height-H nowhere.
* **The "(18)-note" (step 5's cite)**: equations number globally; counting
  every `equation`/`multline` env, #18 = `\label{phiradic}` at TeX 1367, and
  the sentence after it (TeX 1370–1373) prints
  u_i := v_r(a_i(x)φ_r(x)^i) = v_r(a_i(x)) + i·v_r(φ_r(x)) — precisely the
  expansion step 5 attributes to it. TR3-S1 §S1 line 92 pins the same
  "(18) note". Verified.

## 4. The D3 specialization — VERIFIED

(E4) at r = 2 with the TR3-S1 GMN rows (v₁ = w₀, v₁(φ₁) = 0, e₁^GMN = e₀ = 1,
|λ₁| = h₀ — all four verbatim at `TR3S1_2026-08-08.md:104–105`) collapses to
v₂(P) = min_m{w₀(b_m) + m·h₀}, the pin's FIRST equality, exactly as displayed.
The SECOND equality now derived by the explicit P = φ₂ substitution (REV1
fix): v₂(φ₂) = w₁(φ₂) = w₁(Φ₁) under φ₂^GMN ↔ Φ₁ — logically sound; the REV1
rescoping of the old "VERBATIM … pin" claim was the right repair. TR3-S1's
totality ("the identity is total in nonzero f ∈ O[x]", TR3S1:36) covers the
step-3 use on every digit a_i.

## 5. The five-step derivation (D4) and the four-condition closure (D0) — VERIFIED

Step-by-step: (1) = (E2) at r = 3, e₂^GMN kept symbolic — correct. (2) = (E4)
at r = 3; e₁ = 1 used TWICE (dropping the outer e₂^GMN factor; |λ₂| = h₂/e₂ =
h₁ needs e₂^GMN = 1), with (e₂,h₂)^GMN = (e₁,h₁)^proj the dictionary row —
consistent with TR3-S3's "GMN level-2 = project read-ν₁ data" (TR3S3:147),
and gcd(h₁,1) = 1 keeps λ₂ = −h₁ in lowest terms. (3) = accepted TR3-S1
applied to each a_i and to φ₂; γ₂ = e₁w₁(Φ₁)+h₁ matches GRB S2.1's
γ_{i+1} = e_i·w_i(Φ_i) + h_i at i = 1 — third e₁ site. (4) = (H-CHAIN)@3 +
Lemma RESCALE; the quoted clause "both valuations are the min over the SAME
Φ_i-development of the same rescaled quantities" is verbatim at
`GRB_ORDER2_2026-08-05.md:226–227` (S2.1 Application); E_{i+1} = e_iE_i,
E₀ = 1 gives E₁ = E₂ = 1 from e₀ = e₁ = 1 alone — "regardless of e₂" is
exact — fourth e₁ site. (5) valuation multiplicativity = (E3); the ordinate
form matches the (18)-note; φ₃ ↔ Φ₂ is condition (iv)'s row.

**Unlisted-consumption hunt (the pass-charge item): NOTHING FOUND.** Every
load-bearing move maps onto (i)–(iv): the print displays read at r = 3 → (i);
the r = 2 tie → (ii); the augmentation/dilation package → (iii); the
dictionary + r = 3 type-hood → (iv). (H-ℓ) is consumed only as the setting's
normalization (disclosed in the D0 setting sentence and re-displayed in D5);
h₁ ≥ 1 / λ₂ ∈ ℚ⁻ and the Φ-development existence ride the type-hood
identification inside (iv) + the standing S0 setting. My numerics (§8)
adversarially confirmed the closure is REAL: deleting type-hood (a non-key
φ₂) breaks exactly and only step 5's multiplicativity leg — the consumption
the note routes through (E3)+(iv) — while the formula-level two-way identity
survives. The D7 acceptance-criterion quote is verbatim charter text
(`SYNTHESIS_PASS7_2026-08-08.md:229–230`: "Acceptance: TR-3′-GEN order-3
conditionality reduces to standing print attributions."), and the (i)–(iv)
list (REV2's xref fix) is the correct referent.

## 6. e₂-never-used scope + the completed e₁ tally (REV3 items) — VERIFIED

Project e₂ appears in NO step: v₃ per Def 2.5 at r = 3 consumes only
e₂^GMN(=e₁^proj), λ₂, and order-2 polygon data. The stated scope (e₀ = e₁ = 1,
e₂ free; TR3-S3's all-e_j = 1 stratum contained; nothing claimed at e₀ ≥ 2 or
e₁ ≥ 2; TWIST-3 fence honored) is exactly what the derivation supports. The
REV3 e₁ tally — steps 2 (twice), 3 (the γ₂ substitution), 4 (the E₁ = E₂ = 1
site) — is complete: I checked each named site in the text and found no
further e₁ consumption (steps 1 and 5 are e₁-free).

## 7. Consequence display + bracket census (D7) — VERIFIED at the note's epoch; no edits by this unit

* TR3-S3 §S1 consumes (H-v3) exactly as u_i := v₃(A_iφ₃^i) = v₃(A_i) + i·v₃(φ₃)
  "consumed under (H-v3) as u_i = w₂(A_i) + i·w₂(Φ₂)" (TR3S3:144–145) — the
  precise form (HV3-THM)'s consequence delivers. S6.1 row wording matches
  (TR3S3:66).
* Census re-grepped: TR3S3 = 30 mention-lines matching D7's list exactly
  (66–68, 371–372, 608–617 as block ranges; 5 matches inside 608–617). GRB = 3
  @ 492/494/509 exactly. SYNTHESIS_PASS7 = 8, STRATA3 = 2. ROOT_ASSEMBLY and
  PROJECT_STATE verified AT THE LANDING COMMIT `f90d68a`: ROOT = 14 lines,
  precisely D7's list (904, 960, 963, 2491, 2608, 3612, 6435, 6611, 6620–6621,
  6667, 6679, 6697, 6731); PROJECT_STATE = 2. At today's HEAD those two have
  drifted (ROOT 27 lines, PROJECT_STATE 4) — post-note r31-fold + r31-ERRATUM
  activity (`19ac9e3`, `e3425b1`), i.e. the fold-side census D7 explicitly
  assigns to the fold ("the fold's census owns them"). Not a defect of the
  note; the r31 fold must re-grep rather than consume D7's ROOT line numbers.
* No bracket edits by this unit: `f90d68a` touched only the TeX pin + the
  note (diff-stat quoted in §1) — "DELIBERATELY NOT EDITED here" is
  machine-confirmed.
* D6's on-file figures all located: STRATA3 P0 "0/6,468 … sealed … under
  (H-v3)" (STRATA3:23); the 1,641-row battery (STRATA3:33/85, TR3S3:97);
  TOTAL 30,813 (TR3S3:549); the 93 + 1,564 + 821 arc (TR3S3:675/687,
  ROOT:959). Charter fidelity: "pin the TeX into `docs/references/` this
  time" and "a further numerics pin adds nothing" verbatim in F3
  (SYNTHESIS_PASS7:114–118); queue #3 confirmed (line 128).

## 8. Independent numerics (this pass; falsifier, not proof)

Fresh implementation (`/tmp/hv3_p5_check2.py`, exact ℤ arithmetic, hand-rolled
hull; seed 97), per D6's verifier-implementation expectation, at OFF-ROSTER
primes p ∈ {7, 17} (disjoint from pass-3's claimed 5/11/13): (a) geometric v₃
via (E1)+(E2) — actual lower convex hull of the (i, u_i) order-2 points,
first-contact line of slope −h₁, H₂ read from an integer point ON the
λ₂-component, ×e₂^GMN — vs (b) the step-4 MacLane min-formula w₂; plus the
step-5 ordinate identity v₃(A·φ₃^i) = w₂(A) + i·w₂(φ₃) with v₃ computed
geometrically on the PRODUCT (exercising (E3), not the min formula); plus the
r = 2 leg hull-vs-formula incl. the P = φ₂ corner. Towers with genuine
type-hood: φ₁ monic irreducible mod p (m₁ ∈ {1,2}), φ₂ = the standard lift of
an irreducible residual polynomial ψ₁ (f₁ ∈ {1,2}, ψ₁(0) ≠ 0) along the
slope-(−h₀) line, h₀, h₁ ∈ {1..3}. **RESULT: 1,655/1,655 (719 main two-way,
469 r = 2, 227 ordinate legs), 0 failures.** Adversarial control (round 1,
seed 20260803): with type-hood DELETED (arbitrary random monic φ₂), the main
two-way identity still passes everywhere (it is formula-level convexity) but
the step-5 ordinate leg fails 26/308 — confirming the note's condition
closure is load-bearing exactly where it says it is ((E3) needs the valid
type; the note consumes that through (i)+(iv), correctly).

## 9. Findings

**CRITICAL: none.**

**GAPS: none.**

Sub-threshold observations (no action owed; recorded for the r31 fold):

* (obs-1) D0's parenthetical quote "the r = 2 instance was consumed
  evaluated, never as a generic formula" is verbatim CHARTER text
  (SYNTHESIS_PASS7:109–110); TR3-S3 §S1's own wording is "…consumed
  evaluated, **not** as a generic formula" (TR3S3:165–166). The sentence's
  apposition could be read as attributing the quoted words to TR3-S3 itself.
  Same content, exact source exists; quote-source ambiguity only.
* (obs-2) D2's (E2) block silently drops TeX 991's trailing `\medskip`; the
  TeX 975 scope-line quote normalizes a double space. Trivia.
* (obs-3) The TeX 906–907 gloss "immediately before the §2.2 heading" is
  ~70 lines loose unless read as "in §2.1, the subsection immediately before
  §2.2"; lines and content are exact (the REV3 correction itself is right).
* (obs-4) Step 5's "by step 5 applied at φ₃ ↔ Φ₂" self-cites the step it
  sits in; the referent (the just-concluded all-P identity) is unambiguous.
* (obs-5) D7's ROOT/PROJECT_STATE line lists are epoch-true (landing commit)
  but already stale at HEAD (14→27, 2→4 via r31 fold + erratum); the fold
  should re-grep, as D7's framing anticipates.

Independence discipline: no `*_pass*_report.md` read; TeX-line verification,
env-count, hash, arXiv re-fetch, census greps, and numerics all executed
fresh this pass. REV1–REV3's five prior fixes each verified as correctly
applied (condition (iv) present and consumed at D0/D4; the D3 P = φ₂
substitution explicit; §2.2 cite correct; D7 xref "(i)–(iv)"; §2.1 label
correct; e₁ tally complete).

HV3-P5 FINDINGS: 0 critical, 0 gaps
VERDICT: CLEAN
