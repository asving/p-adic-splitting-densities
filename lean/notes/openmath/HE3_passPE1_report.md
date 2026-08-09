# HE3 passPE1 — FIRST FRESH-CONTEXT HOSTILE PASS (Fable, zero prior stake)

**VERDICT: NOT CLEAN — 2 CRITICAL + 4 GAP + 2 MINOR survive this pass's own
verification. Counter stays 0/2.** The two CRITICALs are confined to the
f₁ ≥ 2 geography of the μ ≤ 3 claim: the note's headline "[GENHN-HE(μ)]
UNCONDITIONAL for μ ≤ 3 (degrees n ≤ 7)" quantifies over stage genres with
f₁ ≥ 2 (live at n = 4, 6), where (i) the displayed test-key letters cannot
peel K∖F_Q-rational residual roots and (ii) the S = e₁h thresholds are wrong
(correct: D′h = f₁S), with exact counter-instances below. At f₁ = 1 — the
battery's entire geography, where S = D′h — the chain survives this pass
intact, and the DICTIONARY of THEOREM HE3.A is machine-confirmed by this
pass's fresh route at f₁ = 2 (13/13 PARI jobs) and at q = 9 equal-char
(15/15 constructed ties). So the defects found are in HE3's displayed
statements and proofs, not (on the evidence run) in the σ-law itself; the
repairs exist downstream (GENHN erratum [r1], HE6-0″/HE6-0′/HE6-1L/HE6-5,
all in accepted-or-pinned notes) and were never folded back into HE3 at HEAD.

**Pass metadata.** Target `HE3_PROOF_2026-08-08.md` at HEAD (file unchanged
since HE6's pin 7a95449 — no pin drift). Protocol: quote-and-classify, fix
nothing. FILE NOTE: this path previously held the composer's own record of a
Codex pass adjudicated in the composer's context (commit 2299cc4) — that is
why the orchestrator's counter reads 0/2. That record is preserved verbatim
at `CODEX_HE3PE1_2026-08-08.md` (the corpus convention, cf.
`CODEX_HE6PE1_2026-08-08.md`); in-note citations of "HE3_passPE1_report.md"
for the Codex adjudication should be read as pointing there.

---

## FINDINGS (ranked)

### F1 — CRITICAL. The μ ≤ 3 peel cannot reach K∖F_Q letters at f₁ ≥ 2; the
### "μ ≤ 3 IS BASE-CHANGE-FREE" repair block does not cover K-rational roots
### outside F_Q; the μ ≤ 3 UNCONDITIONAL headline is over-claimed.

QUOTE (LEMMA HE3-1′, §S3): "Let κ > S be an integer, **s ∈ K^×, ŝ ∈ O a
lift**, n(κ) = x^{i}π^{a} ...". QUOTE (§S6.2 REPAIR block): "After peeling
**every K-rational root** by the recentering paragraph above (which uses no
base change), the leftover part of R_λ has degree ≤ d ≤ 3 and NO K-rational
root, hence is a SINGLE irreducible factor".

An ŝ ∈ O has residue in F_Q; at f₁ ≥ 2, letters s ∈ K^× ∖ F_Q^× (6 of the 8
letters at K = F₉) have NO lift ŝ ∈ O, so the test key Φ′ + ŝ·n(κ) of the
displayed family cannot carry them. Consequently a K-rational residual root
s ∉ F_Q cannot be peeled by the displayed recentering, and the subtraction
bullet does not apply to it (it IS K-rational). Concrete failure scenario,
inside the μ ≤ 3 / n = 6 scope of COROLLARY HE3.B: genre (3; 1, 2, 3; h=1),
Φ′ = x² + 9 over ℤ₃, K = F₉, single side λ = 3 with residual
(Z−1)(Z−i)(Z+i). The displayed argument peels s = 1, then has no instrument
that pins |S_{Z−i}| vs |S_{Z+i}| (both non-F_Q letters; the two identities
of §S2 admit (4,0), (2,2), (0,4)). The dictionary is nevertheless TRUE there
(fresh-route leg B, member `T:{1,i,-i}`: PARI σ = {(1,2),(1,2),(1,2)}), and
HE6 proves it (HE6-1L letters of degree < D′ + HE6-5 equivariance) — but
HE3's own text does not. This is the same defect HE6's r1 round struck in
its (LIFT) display ("FALSE as stated ... at (e₁,f₁,h) = (1,2,1), k = 0 only
F_Q ⊊ K is reached"); the strike never propagated back to HE3.
CLASSIFICATION: CRITICAL against COROLLARY HE3.B/HE3.C's "UNCONDITIONAL for
μ ≤ 3" as quantified (GENHN's [GENHN-HE(μ)] ranges over stage leaves with
f₁ ≥ 2); the f₁ = 1 sub-claim is unaffected.

### F2 — CRITICAL. The S = e₁h thresholds are wrong at f₁ ≥ 2: LEMMA HE3-1's
### parenthetical is FALSE (exact counter-instances), LEMMA HE3-2(c)'s
### justification is FALSE, and the §S1 node display is superseded by the
### supplier's own erratum.

QUOTE (LEMMA HE3-1, §S3): "Let Φ″ ∈ O[x] be monic of degree D′ with Φ″ ≡ Φ′
modulo terms of dv-height > S (**so Φ″ is again irreducible with e = e₁,
f = f₁, roots satisfying (T1)/(T2)**, and R″ := O[x]/(Φ″) is again a
complete DVR ...)". COUNTER-INSTANCES (fresh-route leg A1, PARI, exact): at
(e₁,f₁,h) = (1,2,1), Φ′ = x²+9 (irreducible, e=1, f=2, ψ = y²+1), the
height-κ=2 > S=1 perturbations give Φ″ = x²+18 which SPLITS over ℚ₃ into two
linear factors with root residues η = ±1 ∉ roots(ψ), and Φ″ = x²+27 which is
RAMIFIED (e = 2, (T1) broken). Both letters of F₃^× fail; the parenthetical
is false throughout the band S < κ ≤ D′h.

QUOTE (LEMMA HE3-2(c), §S5): "the key invariants ... are untouched, since
dv(w) = κ > S = e₁h places w strictly above the key's own side." The key's
own side has height D′h = e₁f₁h = f₁S at abscissa 0; κ > S places w above it
only when f₁ = 1. Same counter-instances.

QUOTE (§S1, and §S0's GENHN-1 quote): "dv(A_j) ≥ (μ−j)S + 1". GENHN at HEAD
carries erratum [r1 2026-08-08]: "CORRECTED at f₁ ≥ 2 to
{dv(A_j) ≥ (μ−j)·D′h + 1}" — HE3's display was faithful at its pin f2a7164
(pre-erratum) and is stale-false at HEAD. The displayed node is not just
loose: it ADMITS dictionary-breaking members. Fresh-route leg A2:
f = (x²+9)³ + 9(x²+9)² + 81(x²+9) + 729 satisfies the displayed floors
(dv(A_j) = 6,4,2 ≥ 4,3,2) yet is OFF-LOCUS (ambient residual
η⁶+η⁴+1 ≠ ψ³ = η⁶+1); its face-value stage read is the 3-label type with
dictionary {(1,2),(1,2),(1,2)} while PARI σ = {(1,1),(1,1),(1,4)}. Any
consumer that enumerates "stage coordinates + displayed node" (the §S8
recipe, legitimate at f₁ = 1) would emit wrong σ at f₁ ≥ 2. Further sites
consulting the broken band: HE3-1′'s stated range "κ > S"; (SEP)'s index set
"(min(λ, κ))_{κ ∈ ℤ, κ > S}"; the §S6.1 Remark's sample recipe
"κ₀ := ⌊min slope⌋" (can land at κ = D′h where the residual ψ is perturbed).
MODERATION (verified by this pass): for ON-LOCUS f the corrected node forces
dv(A_j) + jκ − μκ ≥ (μ−j)(D′h − κ) + 1 > 0 for κ ≤ D′h, so in the band the
minimum sits uniquely at j = μ and the VALUES Ψ(κ,s) = D′·min_j(dv(A_j)+jκ)
stay true; the μ ≤ 3 conclusions survive the S → D′h repair (as HE6's frozen
Remark "why D′h and not S = e₁h" records). The displayed statements do not.
CLASSIFICATION: CRITICAL (a displayed lemma statement with exact
counter-instances; every §S6 proof cites it). At f₁ = 1, S = D′h and the
band is empty — the battery geography is sound.

### F3 — GAP. Internal inconsistency: the μ ≤ 3 UNCONDITIONAL headline vs the
### note's own in-line semilinearity gap, which it scopes to f₁ ≥ 2.

QUOTE (§S6.3): "[JUSTIFICATION GAP, PE1 finding 6 ...] ... **Assume it and
continue (this affects f₁ ≥ 2 genres**; at f₁ = 1, where the battery lives,
K = F_Q is fixed pointwise and the gap is vacuous)." QUOTE (COROLLARY HE3.B
title): "UNCONDITIONAL for μ ≤ 3 — the first-live case, degrees n ≤ 7".
f₁ ≥ 2 genres exist at μ ≤ 3 (n = 4: (1,2,2); n = 6: (1,2,3), (1,3,2), and
the μ = 2 re-derivation §S6.4 at f₁ ≥ 2). A claim carrying an assumed
justification gap on part of its quantified range is CONDITIONAL there by
the corpus's own vocabulary. Correct display: unconditional at f₁ = 1;
conditional on the equivariance compatibility (since proved as HE6-5) at
f₁ ≥ 2. Failure scenario: a consumer citing "HE3.B unconditional at n ≤ 7"
inherits an unpriced hypothesis at n ∈ {4, 6, 7} f₁ ≥ 2 genres.

### F4 — GAP. The SLOT LEMMA is over-consumed: GENHN-2 is stated at roots θ
### of Φ′ only; HE3 quotes and uses it at arbitrary (T1)/(T2) points.

QUOTE (HE3 §S0): "LEMMA GENHN-2 (THE SLOT LEMMA) ...: for A = Σ a_i x^i and
**ANY element ξ** with (T1) ... (T2) ..., dv(A(ξ)) = min ... EXACTLY".
QUOTE (HE3 §S4, HE3-0 proof): "the SLOT LEMMA (GENHN-2) **is stated for any
ξ with (T1)/(T2)**". GENHN's actual LEMMA GENHN-2 (its §S4): "dv(A(θ)) =
min_i(e₁·v(a_i) + i·h) EXACTLY, **for every root θ of Φ′** and every lift".
HE3 applies the ξ-form at roots ρ of f (HE3-0(i)) and at roots θ″ of test
keys (HE3-1′, HE3-2) — statements GENHN-2 does not make. The ξ-form is true
and is proved as LEMMA HE6-0″, whose bold rider says exactly this: "GENHN-2
as PASTED is stated at roots θ of Φ′ only ... an overconsumption cured by
this restatement." The cure lives in HE6; HE3's cite at HEAD is unfaithful
to its pinned supplier. (This is the pass's answer to attack item 1: the
statement HE6's frozen text consumes is HE6-0″ + κ > D′h test heights —
HE6's chain is safe; the daylight is HE3-internal.)

### F5 — GAP. Two mutually-canceling false displays in the peel (NEW — not
### in the Codex adjudication): S6.2's recentering equivalence and
### HE3-2(b)'s "all other sides are unchanged".

QUOTE (§S6.2): "dv(Φ″(ρ)) > λ ⟺ [dv(Φ′(ρ)) = λ and res(Φ′(ρ)/n(λ)(ρ)) = s]
**or dv(Φ′(ρ)) > λ**". The second disjunct is false: a root with
dv(Φ′(ρ)) > λ has res(Φ″(ρ)/n(λ)(ρ)) = s ≠ 0, hence dv(Φ″(ρ)) = λ EXACTLY.
QUOTE (HE3-2(b), §S5): "the portion of slope λ has length reduced by m ...
**all other sides are unchanged**". False for the sides of slope > λ: under
recentering their pins drop onto the λ-line (their roots' y″ = y + w has
dv = λ), so P(F″)'s above-λ length is m alone and its λ-side gains the old
above-λ length T. The two errors cancel in HE3-4's count: the displayed
subtraction D′(m + T) − D′T and the true direct count
#{dv(Φ″(ρ)) > λ} = D′·len(P(F″) > λ) = D′m agree at |S| = D′m, so the
conclusion stands; but on the CORRECTED (b) the displayed subtraction
formula would give D′(m − T). The §S6.3 stage-α sentence "The blocks at
slope λ with other residues, and at other slopes, are untouched (their
labels at Φ″ agree with those at Φ′ by LEMMA HE3-2(b))" leans on the false
clause; the recoverable form is that the sub-block's onward read consults
only heights > λ of P(F″), where the collapsed material does not appear.
Failure scenario: a Lean transcription of HE3-2(b) as displayed is
refutable at any two-side polygon (e.g. leg B member `2side:{i,-i}`).

### F6 — GAP. HE3-0(iii)/HE3-0′ read a residue off y_ρ/n(λ)(ρ) at ℓ ≥ 2
### slopes, where n(λ) does not exist.

QUOTE (HE3-0′ proof, §S4): "the normalizer n(λ)(ρ) = ρ^{i}π^{a} lies in
L_ρ, so β = res(y_ρ/n(λ)(ρ)) ∈ k_{L_ρ}". Normalizers exist at integer
dv-heights only (§S6.1 Remark says so); for a label with λ = u/ℓ, ℓ ≥ 2
there is no n(λ), and the displayed residue is undefined. HE6-0′ records
and repairs exactly this ("which does not exist for ℓ ≥ 2; the correct
reading is y_ρ^ℓ/ϖ(ρ)^u"). At μ ≤ 3 the f-part of ℓ ≥ 2 labels is vacuous
(ℓd ≤ 3, ℓ ≥ 2 forces d = 1, f_s = 1), so no μ ≤ 3 conclusion is touched;
at μ ≥ 4 it is load-bearing (HE3-BOX-6 territory, repaired in HE6).

### F7 — MINOR. "R := O[x]/(Φ′) = O[θ] the stage ring (complete DVR ...)"
(§S1) is false in general: R is a non-maximal order (e.g. ℤ₃[3i] ⊊ ℤ₃[i] at
(1,2,1)); GENHN carries erratum [e2-E3 2026-08-09] re-carrying e/f/v/res in
L = Frac(Ô)(θ). At μ ≤ 3 cosmetic (HE3-1's norm runs through the field L);
at μ ≥ 4 the stage-CS step instantiates HE3.A "with base ring R (a complete
DVR with finite residue field K)" — that hypothesis fails as displayed and
needs the O_L re-carrier (inside the already-boxed μ ≥ 4 region).

### F8 — MINOR. Sign-convention seam never reconciled: §S5 proves the
recentering by "R_λ(Z + s)" while §S6.2 names the absorbed class "S_{Z−s}"
and HE3-1′ tests "R_λ(s) = 0"; whether the class absorbed by Φ′ + ŝn(λ) has
residue s or −s (and how the twist ẑ^{fl} enters) is left to the reader. No
numeric consequence found (the battery's twist-free measurement is immune).

---

## CLEAN CHARGES (attacked, survived this pass)

* **LEMMA HE3-1a, the engine identity** Σ_ρ dv(Φ″(ρ)) = D′·dv(B₀): sound as
  an identity (resultant symmetry + field norm through L″); machine-real at
  72,134 + 43,528 committed checks and at this pass's fresh legs.
* **LEMMA HE3-3 steps (1)–(3) with (★)** at f₁ = 1 (band empty): the convex
  duality display and the (★★) root-side sum verified line-by-line; the
  (SEP)-holds-at-μ ≤ 3 argument (at most one non-integral slope) verified.
* **Strict descent**: GENIND.A(IV) cite checked at pin 4682bcf ("a CS event
  at a stage with m keys requires a side of abscissa length e·μ·deg ψ ≥ 4,
  hence m ≥ 4"; children multiplicity ≤ m/2) — faithful; μ′ ≤ μ/2 follows.
* **No circularity** in the §S6.4 μ = 2 cross-check (GENHN.C not consumed).
* **The re-basing map** (e,f) ↦ (e₁e_s, f₁f_s): well-defined and correct on
  the evidence run — the forcing HE3-0′ (e-part) + degree count verified;
  fresh legs B and C machine-confirm the composed dictionary at f₁ = 2 and
  at q = 9, including Frobenius-conjugate label pairs (no class-merging).
* **FGMN cites (charge item 4): VACUOUS.** HE3 contains zero references to
  FGMN or its local print at any numbering (grep-verified); §S0(b)'s claim
  that the Montes/GMN index theorem is NOT cited is accurate — §§S3–S6 use
  only resultants, the ultrametric read, and GENHN-2/-3. No unfaithful cite
  can exist where no cite exists.
* **Battery decorrelation (tautology audit)**: HE-NORM's two sides are
  computed independently (Bareiss/Sylvester integer resultant vs
  development slot-min); the σ-oracle is PARI factorpadic-200 +
  idealprimedec (the pinned w12 GP_FUN) against a Python polygon reader —
  no shared code path found on inspection; HE-T-SIG's flipped dictionaries
  are killed by the oracle, not by the reader.

## MACHINE LEG (isolated re-run + pins)

Isolated re-run of the sealed battery (`he3_checks.py` copied with its
import closure to /tmp/he3_iso, run from scratch): **VERDICT GREEN, 0
violations, 17.0 s; `he3_checks_results.json` bit-identical to the
committed artifact (md5 1b679cd23e337f3e45cfb72ade74fffe) and stdout
byte-identical to the committed `he3_checks_output.txt`.** Pins: HE3's file
is byte-unchanged since HE6's pin 7a95449; GENHN's pin f2a7164 predates
GENHN's [r1]/[r2]/[e2] errata (supplier drift AFTER pin — F2/F7 report the
HEAD-level consequences); GENIND pin 4682bcf checked at the cited clause.
Sealed-vs-delivered: HE3-BOX-4b's disclosure (ℤ_p rows only; HE-T-NODE
mis-specified; HE-T-PSI/-CERT owed) matches the runner and artifacts as
committed; the equal-char rows promised in the sealed docstring were not
delivered there — this pass's leg C covers an equal-char cell fresh.

## FRESH ROUTE (instruments committed: `verification/openmath/
he3_pe1fresh_ab.py`, `he3_pe1fresh_c.py`, with outputs)

* **Leg A (exact + PARI, f₁ = 2 genre (3;1,2,3;1))**: A1 — the κ = 2 > S
  test keys x²+18 (SPLITS, wrong residues) and x²+27 (RAMIFIED) refute
  HE3-1's parenthetical and HE3-2(c)'s justification (→ F2). A2 — a
  displayed-node member that is off-locus with face-value dictionary
  {(1,2)³} vs PARI {(1,1),(1,1),(1,4)} (→ F2).
* **Leg B (PARI oracle, 13 jobs, 0 mismatches)**: on-locus f₁ = 2, μ = 3
  members at K = F₉ across 8 configurations — 3-label residuals incl. the
  Frobenius pair {1,i,−i}, K-irreducible quadratic and cubic residuals
  ((1,4) and (1,6) blocks), two-side polygons, ℓ = 2 side ((2,2) block),
  ℓ = 3 side ((3,2) block) — the HE3.A dictionary confirmed on each; no
  conjugate-class merging observed (F1/F3's gap is a justification gap, not
  a truth failure, on this evidence).
* **Leg C (exact, mechanism-free, 15 jobs, 0 failures)**: equal-char cell
  at NON-PRIME base q = 9 (O = F₉[[t]], genre (9;2,1,3;1)) — f constructed
  as three slope-1/2 quadratics with distinct letters, σ = {(2,1)³} known
  by construction; the stage read's single λ = 3 side reproduces residual
  roots = the letters on each of 15 (z, letter-triple) choices, tying the
  dictionary with no oracle and no shared reader. Also fresh: the 3-label
  μ = 3 type at p = 3 (impossible at q = 3; the battery had it only at
  p ∈ {5,7}).

## GRADE LINE

**Pass verdict: NOT CLEAN (F1, F2 CRITICAL; F3–F6 GAP; F7, F8 MINOR).
Counter: 0/2 — unchanged; this pass does not award the grade.** The μ ≤ 3
claim survives at f₁ = 1 as displayed and at f₁ ≥ 2 in substance-by-HE6;
what fails is HE3-at-HEAD's own display of statements, thresholds, letters,
and its UNCONDITIONAL self-grade at f₁ ≥ 2. Suggested repair round (for the
composer, not executed here): fold GENHN [r1] (D′h node) + HE6-0″ (ξ-form
slot lemma) + HE6-0′ (ℓ ≥ 2 residue read) + HE6-1L (letters) + HE6-5
(equivariance) back into HE3's §S0–S6 with tagged errata; rescope HE3.B/C
to "unconditional at f₁ = 1; at f₁ ≥ 2 via HE6's accepted closures"; then a
PE2 charged at the repaired f₁ ≥ 2 displays and at HE3-5's window law
(not deep-audited by this pass — disclosed).
