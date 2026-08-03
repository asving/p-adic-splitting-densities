# HV3 pass 3 (Fable) — hostile verification of `HV3_DISCHARGE_2026-08-08.md` (REVISION 2)

Charge: fresh-context hostile verifier, model-diverse leg (pass 3 of the 0/2 counter;
prior passes NOT read, per instruction). FULL pass over the discharge note + the pinned
`docs/references/HigherNewton.tex`. Quote-and-classify (CRITICAL / GAP); fix nothing.
Numerics run as falsifiers only. The corrupted `/tmp/litunit/fgmn.txt` extraction was
NOT consulted (it is also not consumed by the note — verified, §V1 below).

## VERDICT SUMMARY

**0 CRITICAL, 2 GAPS (both minor, cite-label / honesty-tally class; neither touches
the derivation, the scope, or the conditionality list).** The source pin is genuine,
the four extracted displays are faithful to the pinned TeX at the cited lines, the
five-step derivation of (HV3-THM) is valid under exactly the listed conditions
(i)–(iv), the e₀ = e₁ = 1 scope is honest with e₂ genuinely unused, the D3 r = 2
check is correct as rescoped in REVISION 1, and the D7 consequence/census claims are
exact at the note's authoring commit. A fresh two-way implementation of v₃ per the
note's own D6 verifier-expectation ran 615/615 green on off-roster primes.

## V1. Source pin (D1) — VERIFIED

* `sha256sum docs/references/HigherNewton.tex` =
  `8253d4d62cf3d180567d5e41429fdb0e4875abdc5d58db595dc66a24fb16bd18` — IDENTICAL to
  the pin recorded in the note (D1) and independently to the ADM-REAL′ REVISION-1
  record (`ADMREAL_2026-08-08.md` line 202). File is 2,897 lines as claimed.
* Environment-count map re-verified independently: the preamble (TeX 3–11) declares
  ONE shared per-section counter (`\newtheorem{lemma}[theorem]`, likewise remark /
  definition / notation / corollary / proposition), and between `\section{Newton
  polygons of higher order}` (TeX 869) and Prop 2.7 there are EXACTLY seven
  counter-bearing environments, in order: Def @926 (`type`) = 2.1, Lemma @935
  (`typedegree`) = 2.2, Def @955 (`ppt`) = 2.3, Lemma @962 (`factortype`) = 2.4,
  **Def @985 = 2.5 (the v_r definition)**, Prop @1012 = 2.6, Prop @1028
  (`propertiesv`) = 2.7. No remark/notation/example intervenes. The D1 map is exact.
* Subsection numbering: section 2's subsections are @872 ("Types of order r−1" =
  §2.1) and @977 ("The $p$-adic valuation of $r$-th order" = **§2.2**). The REVISION-2
  correction (§2.3 → §2.2) is RIGHT; the title and TeX 977 cite are exact.
* §2 scope line verified at TeX 975: "We fix a type $\ty$ of order $r-1$ for  the
  rest of section \ref{secNPr}." (TeX has a double space; the note's italic quote
  normalizes it — nit only, not a verbatim-block claim.)
* Symbol-overload caution (D1) accurate: TeX 220–222 define the *height* H(S) =
  vertical-projection length with d(S) = ℓ(S)/e = H(S)/h — a different object from
  the H_{r−1} intercept mapping @979–983, exactly as the note warns.
* fgmn.txt independence: the note's derivation consumes NO FGMN extraction; D5
  explicitly fences (PIN-GEN-i) as a different paper's owed leg. The GMN leg here is
  the in-repo hash-pinned TeX — the note's "no corrupted-extraction caveat of the
  fgmn.txt species applies on this leg" is correct.

## V2. The extracted displays (D2) — FAITHFUL

Each block compared character-by-character against the pinned TeX:

* **(E1)** TeX 979–983: verbatim match, including
  `H_{r-1}(S)=u+|\la_{r-1}|i` and the semigroup-homomorphism clause (the note
  re-wraps TeX 983's long line; content identical). The display IS generic in r:
  TeX 870 fixes "r is an integer, r ≥ 2" for the whole section and TeX 975 fixes the
  order-(r−1) type — one display for all orders, no per-r normalization freedom, as
  the note's commentary claims. The intercept datum is pinned absolutely ("the
  ordinate of the point of intersection of the vertical axis with the line
  L_{λ_{r−1}}"), which closes the normalization question TR3-S3's sketch left open
  (TR3S3 §S1 even wrote the sketch's intercept with a sign-sloppy `+mλ₁`; the
  extraction resolves it to +|λ|·i).
* **(E2)** TeX 985–991: verbatim (the note drops the trailing `\medskip` on 991 —
  formatting macro only; nit).
* **(E3)** TeX 1012–1014: quote exact; the printed proof at TeX 1016–1022 is indeed
  the L_{λ_{r−1}} support-line geometry (semigroup composition + "all points of both
  polygons lie above the line L_P" + v_r(a) = e_{r−1}v_{r−1}(a)).
* **(E4)** TeX 1028–1038, items 3–4: verbatim; item 3's display is one TeX line
  @1034 (the note wraps it at the `=`; symbols identical), item 4 @1036.
* Supporting notation: TeX 906–907 does carry "S_i(P) is the λ_i-component of
  N_i^-(P)" and "s_i(P) the initial abscissa of S_i(P)"; Def `sla` @361–367 does
  define L_λ(N) (first-contact line shifted up from below) and S_λ(N) := N ∩ L_λ(N).
  Line cites and content exact — but the parenthetical subsection label is wrong;
  see FINDING G1.
* Step-5's corroborative "(18)-note" cite checks out: the 18th `\begin{equation}` of
  the paper is TeX 1367 (the φ_r-development), and the u_i := v_r(a_iφ_r^i) =
  v_r(a_i) + i·v_r(φ_r) expansion is the unnumbered display + note immediately
  following (TeX 1373–1375), which also confirms v₁(φ₁) = 0 in print. Matches
  TR3-S1's naming of the same display ("their (18) note", TR3S1 line 92).

## V3. D3 — the r = 2 check re-derived (charter item) — PASSES

Independent re-derivation: (E4) second equality at r = 2 reads
v₂(P) = e₁^{GMN}·min_m{v₁(b_m) + m(v₁(φ₁) + |λ₁|)}. The standing TR3-S1 §S1 GMN rows
(verified at TR3S1 lines 102–105) supply v₁ = w₀, v₁(φ₁) = 0, e₁^{GMN} = e₀ = 1,
|λ₁| = h₀, giving v₂(P) = min_m{w₀(b_m) + m·h₀} — EXACTLY the accepted pin's first
equality ("v₂(P) = min_m(w₀(b_m) + m·h₀) = w₁(P) verbatim", TR3S1 line 104). The
pin's second equality v₂(φ₂) = w₁(Φ₁): the REVISION-1 fix correctly derives it as the
one-line substitution P = φ₂ into the all-P identity plus the dictionary φ₂^GMN ↔ Φ₁
(v₂(φ₂) = w₁(φ₂) = w₁(Φ₁)). The pre-REV1 "VERBATIM" overclaim is gone; the rescoped
claim is accurate. TR3-S1 is genuinely ACCEPTED (its pass-3 record: two consecutive
model-diverse CLEANs), so condition (ii)'s status label is honest. Numerically the
specialization was re-run fresh: 240/240 (see V7).

## V4. D4 — the five-step derivation — VALID; consumption ledger closed

Per-step audit (each consumption traced to a D0 condition):

1. Step 1 = (E2) + (E1) at r = 3 → condition (i). Correct instantiation of Def 2.5.
2. Step 2 = (E4) item 3 at r = 3 → (i); the substitutions e₂^{GMN} = e₁^{proj} = 1
   and |λ₂| = h₂^{GMN}/e₂^{GMN} = h₁ use the dictionary row (e₂,h₂)^{GMN} =
   (e₁,h₁)^{proj} → (iv), + the scope hypothesis e₁ = 1. (GMN's λ_i = −h_i/e_i with
   e_i, h_i positive coprime — verified at TeX 910 — so |λ₂| = h₂ at e₂ = 1.) Exact.
3. Step 3 = the accepted TR3-S1 tie applied to every digit a_i and to Φ₁ → (ii)
   (the tie is total in nonzero O[x] — Def 2.5's "any nonzero polynomial" scope, so
   applying it to digits is legitimate); the rewrite w₁(Φ₁) + h₁ = γ₂ uses
   γ₂ = e₁w₁(Φ₁) + h₁ (the GRB/TR3-S3 convention, verified: GRB S2.1 Application
   "w_{i+1}(Φ_i) = γ_{i+1} = e_iw_i(Φ_i) + h_i"; TR3S3 S0 line 28) at e₁ = 1 —
   an e₁-use NOT tallied in the scope remark; see FINDING G2.
4. Step 4 = (H-CHAIN) depth 3 + Lemma RESCALE → (iii). Verified against GRB S2.1:
   the quoted sentence "both valuations are the min over the SAME Φ_i-development of
   the same rescaled quantities" is verbatim there (Application paragraph), and
   E_i := w_i(π) = e₀⋯e_{i−1} (GRB line 83), so e₀ = e₁ = 1 forces E₁ = E₂ = 1
   REGARDLESS of e₂ — condition (iii)'s dilation claim is exactly right. w₂ = the
   MacLane augmentation of w₁ at Φ₁ with w₂(Φ₁) = γ₂, min over the SAME Φ₁-development
   GMN reads (both developments are literally the φ₂ = Φ₁-adic digits).
5. Step 5: v₃ = w₂ concluded from 2–4 (the two min-formulas coincide termwise);
   ordinate form via valuation multiplicativity from (E3) → (i), instantiated at
   P = A_i and P = φ₃ with φ₃ ↔ Φ₂ → (iv). The "(18)-note" is corroboration only
   (load-bearing justification is (E3)); no unlisted consumption. The self-citation
   "by step 5 applied at φ₃" means the all-P identity concluded in step 5's first
   sentence — awkward wording, logically fine (nit, not counted).

**Four-condition closure hunt (the pass-charge item): CLOSED.** Every consumption in
D3/D4 maps into (i)–(iv): print displays (E1)–(E4) → (i); the r = 2 tie + order-1
rows → (ii); (H-CHAIN)/RESCALE incl. the γ-convention and E-dilation → (iii);
dictionary rows + r = 3 type-hood → (iv). The type-hood consumption is genuinely NOT
new: TR3-S3 §S1 (lines 141–157) already consumes GMN Defs 2.19–2.21 at r = 3 under
the same §2 scope, as D0 claims. (H-ℓ) sits in D0's SETTING sentence, not the list —
correct placement: ℓ never enters v_r or the w-formulas (it feeds the twist/residual
operators only, untouched here), so it is ambient-setting disclosure, not a proof
consumption. I found nothing consumed but unlisted.

## V5. Scope (e₀ = e₁ = 1, e₂ free) — HONEST, with one tally slip

e₀ = 1 enters only through (ii) (TR3-S1's acceptance stratum — verified from TR3-S1's
own S0). e₁ = 1 enters at: (α) step 2, dropping e₂^{GMN}; (β) step 2, |λ₂| = h₁;
(γ) step 3, γ₂ = e₁w₁(Φ₁) + h₁ = w₁(Φ₁) + h₁; (δ) jointly with e₀ = 1 at step 4's
E₁ = E₂ = 1. The scope remark tallies only (α)(β) ("step 2 twice") — FINDING G2. The
load-bearing claim — **e₂ never used** — is TRUE: no step reads project (e₂, h₂);
GMN's v₃ consumes only levels ≤ 2 of the dictionary (GMN e₂ = project e₁); confirmed
structurally by the falsifier (V7), whose two independent implementations of the
claim require no e₂ input at all. The (TWIST-3) fence statement is accurate (at
e₀ ≥ 2 the accepted r = 2 input is indeed unavailable — TR3-S1 is e₀ = 1 only).
D0's containment claim also verified: TR3-S3's stratum is e₀ = e₁ = e₂ = 1 (TR3S3
S0 line 24) ⊂ {e₀ = e₁ = 1}, and the consumed form u_i = w₂(A_i) + i·w₂(Φ₂) is
character-identical to TR3-S3's display (line 145).

## V6. D7 — consequence display + census — VERIFIED; no bracket edits

* The consequence claim is correctly bounded: nothing is claimed machine-checked or
  attribution-free; the reduction target ("standing print attributions") matches the
  F3 charter's acceptance criterion VERBATIM (`SYNTHESIS_PASS7_2026-08-08.md` queue
  #3: "TR-3′-GEN order-3 conditionality reduces to standing print attributions").
  The REVISION-2 fix "(i)–(iv)" in D7 is present and now consistent with D0.
* Charter quotes verified verbatim in §F3: "a further numerics pin adds nothing";
  "pin the TeX into `docs/references/` this time"; the charter's task list =
  exactly D1/D2/D3/D4's structure.
* Census at the note's authoring commit (f90d68a), re-grepped from git history:
  TR3S3 30 mention-lines at EXACTLY the listed lines (34…688); ROOT_ASSEMBLY
  EXACTLY 14 at 904, 960, 963, 2491, 2608, 3612, 6435, 6611, 6620, 6621, 6667,
  6679, 6697, 6731; GRB 3 (492, 494, 509); PROJECT_STATE 2; SYNTHESIS_PASS7 8;
  STRATA3 2. The 30 + 14 + 3 = 47 proof-note bracket sites ride acceptance as
  listed. (Present-day ROOT/PROJECT_STATE counts have since drifted upward — that
  is the r31 fold's own census, which D7 explicitly assigns to r31, not this unit.)
* No-edit claim verified in git: commit f90d68a ADDS only the note + the TeX pin;
  bc34acf (REV1) and e3425b1 (REV2) modify only the note. No bracket site was
  touched by this unit.

## V7. Numerics — the D6 verifier-expectation executed fresh (falsifiers, not proofs)

D6's recorded-cover numbers spot-checked against the named notes: STRATA3 P0
"0/6,468 ... under (H-v3)" (STRATA3 line 23), CERT3 1,641 rows (line 33/85),
tr3s3_check TOTAL 30,813 (TR3S3 line 549) — all as cited. Roster primes there are
p ∈ {2,3}; this pass used OFF-roster primes as the note prefers.

Fresh implementation (`/tmp/hv3p3_falsifier.py`, exact integer arithmetic, seed
20260803): leg (a) = geometric v₃ per (E1)+(E2) — Φ₁-development, ordinates
u_i = v₂(a_iΦ₁^i) computed by running geometric v₂ ON THE EXPANDED PRODUCT
(decorrelated from the min-formula path), monotone-chain lower hull, slope −h₁
first-contact intercept with a hull-vs-pointset internal coherence assert, ×e₂ = 1;
leg (b) = the step-4 MacLane min w₂ with γ₂ = w₁(Φ₁) + h₁. Three genuine
e₀ = e₁ = 1 towers: p = 5 (h₀ = 1, g₀ = 2, residual z²+z+2 irred), p = 11 (h₀ = 2,
g₀ = 2, residual z²+1 irred), p = 13 (h₀ = 1, g₀ = 1 refinement corner). Results:

    r=2 tie   (v2_geo == w1_mac):   240/240   (the D3 specialization, re-run)
    r=3       (v3_geo == w2_mac):   240/240   ((HV3-THM) two-way)
    v3 multiplicativity spot-checks:  45/45   (the (E3) leg)
    step-5 ordinate identity:         90/90   (u_i = w2(A_i) + i*w2(Phi2))
    TOTAL 615/615, zero failures.

A transcription error in |λ₂|, a misplaced e-factor, a wrong γ₂, or an index-shift
slip in the dictionary would generically break the product-expanded leg; none did.

## FINDINGS (quote-and-classify)

**G1 — GAP (minor; cite-label).** D2, (E2) supporting-notation bullet: "Supporting
notation, TeX 906–907 **(§2.2 preamble)**: S_i(P) is the λ_i-component of N_i^-(P);
s_i(P) its initial abscissa." The line numbers and content are exact, but TeX
906–907 lies inside **§2.1** ("Types of order r−1", TeX 872–976); §2.2 begins at
TeX 977. Same species as the pass-2-corrected §2.3 → §2.2 miscite, one bullet lower.
Non-load-bearing (nothing consumes the subsection label; the lines are what is
consumed), but in a source-extraction note the subsection tag should be right.

**G2 — GAP (minor; honesty-tally completeness).** D4 scope remark: "the derivation
used e₀ = 1 (step 3's accepted input) and e₁ = 1 (**step 2 twice**: dropping
e₂^{GMN} and |λ₂| = h₁), but NOT e₂ = 1". The tally is incomplete: step 3 uses
e₁ = 1 a third time, in its own displayed line "γ₂ = e₁w₁(Φ₁) + h₁ = w₁(Φ₁) + h₁",
and step 4's trivial dilation E₁ = E₂ = 1 consumes e₀ = e₁ = 1 once more (E₂ =
e₀e₁, per GRB S2.1). The remark's CONCLUSIONS are unaffected — every use lies inside
the stated e₀ = e₁ = 1 scope and e₂ is genuinely never used (verified per-step and
structurally, V5/V7) — but an honesty-audit display should enumerate all sites.

Nits (not counted): step 5's self-reference "by step 5 applied at φ₃ ↔ Φ₂" (means
the all-P identity concluded one sentence earlier); (E2) quote drops TeX 991's
trailing `\medskip`; the TeX-975 double space normalized in the italic quote.

## VERDICT REASONING

Both findings are presentation-layer: no step of the derivation, no condition of the
(i)–(iv) list, no scope boundary, and no census number is wrong. The extraction is
faithful, the conditionality list is closed under the proof's consumptions, and the
note's own strongest falsifier (the two-way implementation) passes fresh at
off-roster primes. This is the pass-3 leg of the 0/2 counter: GAPS-ONLY, counter
advances only on CLEAN, so the two gaps above go to the orchestrator for a
REVISION-3 wording fix before the next pass.

HV3-P3 FINDINGS: 0 critical, 2 gaps
VERDICT: GAPS-ONLY
