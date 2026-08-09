# HE6R1 passPE2 — hostile pass 2 on the RECONCILIATION note's [r1′] text (fresh context)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 4 MINOR. The two PE1 GAP repairs
(F-1 hypothesis addition, F-2 rider) survive re-derivation from first
principles; the F-3 scalar clause is derived and correct at the battery's
ℓ = 1 (with a general-ℓ identification caveat recorded as MINOR here);
the machine leg re-ran bit-identical in isolation with its 21 disclosed
violation records; the mandated fresh route (non-prime-q base, f₁ = 2,
K₂ = F_{p⁴}) ran 487 members with 487 PARI agreements and 0 mismatches.
The 2-clean count STARTS: 0/2 → 1/2.**

Target: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md` at HEAD 9086844
(r1′ = 71c7457/8cbfaa2/57700f3 on the arc seal 4f5ebaa → verdict 850e77e →
[r2] rows → passPE1 598582b-era report, 0C+2G+5m). Protocol:
quote-and-classify, nothing fixed. Endpoints read at HEAD:
`HE6_PROOF_2026-08-08.md` (post-PE3-era), `HE7_PROOF_2026-08-08.md`
(ACCEPTED 2/2; dated appends through 07dfbb7, i.e. past db0001a).
Attack order followed: (1) the three [r1′] repairs re-derived (Ψ ∤ f_S
equivalence; RIDER HE6R1-2R + the §S5.8(c) item (6) keying; the γ_g
scalar clause), (2) tag-convention collision hunt over [r1]/[r2]/[r1′],
(3) the literal-instance table against the CURRENT frozen HE7 (annex-era
drift), (4) the P1 re-score and F-4 totals-split honesty, (5) free hunt;
plus machine-leg integrity (pins, isolated re-run, tautology audit) and
the mandated fresh route.

---

## FINDINGS (ranked; none GAP-or-worse)

### F-1 (MINOR) — the PE1 F-3 defect has an unflagged verbatim echo inside frozen, ACCEPTED HE7

Quote (HE7_PROOF §S5.5 [r1] addition (b), L730–731, the one place HE7
paraphrases LEMMA HE6R1-2(c)): "with R_{λ₂}^{f} and R_{λ₂}^{f_S} of equal
degree and equal radical **(equal outright when separable)**." That is the
pre-repair form of the clause PE1's F-3 falsified — equality holds only up
to the K₂^× scalar γ_g — and it now stands inside a note that is ACCEPTED
2/2 and FULLY FROZEN (HE7-BOX-1 final dated line). The [r1′] F-3 repair
corrected the recon's own clause and stated consumer scale-invariance, but
did not flag this propagated copy, although the note's own R3 row shows
the standard for exactly this situation ("an HE7-side residue, noted
here"). Grep: "equal outright" occurs once across the openmath notes —
this site. Failure scenario: a reader of frozen HE7 §S5.5(b) takes the
parenthesis as accepted ground truth and consumes coefficient-level
equality of the two residuals (e.g. reads a residue VALUE off f and
attributes it to f_S) — wrong by γ_g (times the ℓ ≥ 2 twist unit of F-2
below). No present consumer does: HE7.A(2) consumes the monic irreducible
factors, the α-refine consumes residual roots, separability checks are
scale-invariant — the same blast-radius analysis that made PE1's F-3 a
MINOR.

### F-2 (MINOR) — the [r1′] scalar identification "γ_g" is exact at ℓ = 1 but omits the fixed cocycle unit at ℓ ≥ 2

Quote (§S3.4(c) [r1′]): "they agree up to the K₂^× scalar carried by g's
level-2 residue (a fixed γ_g ∈ K₂^×, nonzero by (a))", and the proof's
closing line "res(g(ξ)/n₂(c_g)(ξ)) = ι_ξ(γ_g) … so the term-residue
assembly gives R^f_{λ₂} = γ_g·R^{f_S}_{λ₂}". LEMMA HE6R1-2 is stated at
general ℓ. Along f = f_S·g the residue assemblies at a side λ₂ compose
through n₂(h_{f_S}(λ₂))·n₂(c_g) = τ₂(h_{f_S}(λ₂), c_g)·n₂(h_f(λ₂)), and
by HE7's own ANNEX-LEMMA R1-a(ii)/(iv) the cocycle τ₂(a,b) = Λ₁^{c₁(a,b)}
with c₁ ∈ {0,1}: its residue is the FIXED unit β^{c₁} ∈ K₂^×, which is 1
at ℓ = 1 (s(·) ≡ 0, the note's own §S3.1 table row) but can be β at
ℓ ≥ 2. So at ℓ ≥ 2 the scalar is γ_g·β^{c₁(h_{f_S}(λ₂),c_g)}, not γ_g
alone, and it can differ side by side through c₁. Failure scenario: a
consumer at an ℓ ≥ 2 proper block equates γ_g with the observed residual
ratio and gets a β-power discrepancy. The clause's mathematical content —
a fixed element of K₂^× per side, nonzero, consumers scale-invariant —
survives untouched, and the note's proof-uses and battery are at ℓ = 1.

### F-3 (MINOR) — stale cross-note status lines inside the [r1′]-touched grade box

HE6R1-BOX-1 (§S5) still reads "HE7 is **0/2** and now carries FINDING
HE6R1-F1" and inherits the minimum over "{GENHN 0/2, HE6 0/2, HE7 0/2,
HE3 1/2 …}". The [r1′] round (commits 15:22–15:25 on 2026-08-09) inserted
its arc sentence INTO this box while, at those timestamps, HE7 was already
ACCEPTED 2/2 with FINDING HE6R1-F1 applied (annex-pass #2 a472155,
micro-annex ca3754d at 07:32), and HE6/GENHN had reached 1/2 (e1aef82 at
13:59). Same era-drift genus one row up: the R3 row's re-verified
parenthesis "(an HE7-side residue, noted here)" about the fold-box
"verbatim" sentence predates db0001a ("HE7 dated line (fold-box as-of
scoping)", 13:01), which addressed that residue. Direction is conservative
(grades understated, a residue over-reported), so no consequence is
over-claimed; but the sentences are false in present tense at HEAD in a
box this round edited. Failure scenario: a downstream note copies "HE7
0/2" from this box and mis-prices the chain's conditionality (downward).

### F-4 (MINOR) — the tag convention's collision-freedom claim is imprecise against its own text

The [r1′] header states: "plain [r1] inside this note names the HE6-side
repairs of §S1, and [r2] the HE6-PE2-era row updates". Counter-instances
inside the note: [r1] naming HE7's r1 tag at "§S1 CONVENTION [r1]"
(L432), [r1] naming GENHN's erratum annex in the R9 row, and — inside the
[r1′] round's own new F-5 paragraph — [r2] twice naming HE7's r2 round
("HE7's later [r2] round", "frozen HE7 §S5.8 [r2]", L237/241). Each
occurrence carries an explicit file qualifier, and the primed tag [r1′]
itself collides with nothing, so no ambiguous reading was found — the
defect is that the stated convention mis-describes the note's uses of the
unprimed tags. Failure scenario: a mechanical reader resolving bare [r1]
per the stated convention re-points HE7's §S1 CONVENTION cite at HE6's
repair table.

---

## CLEAN CHARGES (attacked, survived)

* **The Ψ ∤ f_S hypothesis and its equivalence (attack 1, PE1 F-1
  repair).** Re-derived both directions. (⟸ of "Ψ ∤ f_S ⟸ Ψ ∤ f" is
  f_S | f.) For the substantive direction: LEMMA HE6-1 at HEAD (HE6
  L250–253) gives that a root ξ of Ψ = Ψ_{λ,r} is a (T1)/(T2) point with
  dv(Φ′(ξ)) = λ and ι_ξ(r)(β_ξ) = 0 — i.e. carries level-1 label (λ, r) —
  so if Ψ | f its roots are roots of f with that label, hence lie in
  S = S_{λ,r} = roots(f_S); Ψ is squarefree as a divisor of f with
  disc f ≠ 0; a squarefree polynomial whose roots are roots of f_S divides
  f_S. The 57700f3 rewording of this sentence is the sound form. Placement
  checked: the hypothesis makes the (b)/(c) consumptions of frozen
  HE7-7′(b)-at-f_S and THEOREM HE7.A(1) in-scope (HE7 §S1 CONVENTION [r1]
  carries the same hypothesis), the two f-side consumption sites are
  tagged to the rider, and the "why added" paragraph's failure mechanism
  (A₀^{(2)} = 0, j = 0 pin at ∞, finite part sums to μ₂ − 1) matches the
  12 committed BADTOTAL records.
* **RIDER HE6R1-2R (attack 1, PE1 F-2 repair).** The proof re-derived
  from first principles: for monic F with Ψ ∤ F (⟺ C_0^{(F)} ≠ 0, so the
  j = 0 pin is finite), each nonzero development term has
  dv₂(C_j(ξ)Ψ(ξ)^j) = dv₂(C_j) + jκ₂ EXACTLY by (SLOT₂) at C_j
  (deg C_j < D″; zero terms skipped per the R8/F9 nonzero-terms
  convention); two attaining j, j′ force (j−j′)κ₂ ∈ ℤ, i.e. j ≡ j′
  (mod ℓ₂) by gcd(u₂, ℓ₂) = 1 with dv₂ ℤ-valued; multiple attainment ⟺
  κ₂ is a slope of P₂(F); the tie-residue sum assembles through the §S1
  twist to ι^{(2)}(R^F_{κ₂})(β₂), whose non-vanishing gives exactness —
  HE7-7′(b)'s proof with f_S replaced by F, no step reading the evaluand
  beyond {C_j}. The §S5.8(c) item (6) keying is FAITHFUL: item (6) (HE7
  L896–899) records, for HE7-7′/7″, "the developments … have coefficients
  of degree < D″, so (SLOT₂) applies to them; the congruence argument
  uses gcd(u₂, ℓ₂) = 1 only" — the mechanism the rider quotes; item (6)'s
  own axis is the KEY (Ψ → Ψ^{(w)}) where the rider's is the evaluand,
  and the rider correctly displays its own full proof rather than leaning
  on the cite as authority.
* **The F-3 scalar clause derived (attack 1).** Same radical + equal
  degree + separability gives R^f = γ̃·R^{f_S} with γ̃ ∈ K₂^×; pinning γ̃
  via residue multiplicativity along f = f_S·g at the (c)-proof's test
  points, with a generic letter of degree exceeding both residual degrees
  to convert pointwise equality into polynomial identity, yields
  γ̃ = γ_g·(τ₂ residue), = γ_g exactly at ℓ = 1 where n₂(k) = ϖ^k and the
  cocycle is trivial. "Equal exactly when γ_g = 1, which is not claimed"
  is the honest strengthening of the sealed clause. (The ℓ ≥ 2
  identification caveat is F-2 above.)
* **Literal-instance table vs the CURRENT frozen endpoints (attack 3).**
  ANNEX-DEF HE7-2′ (the CODEX-F1 re-based normalizer recursion) pins "At
  i = 1 the recursion reproduces §S1's n₂(k) = ϖ^{m(k)}Φ′^{s(k)} verbatim
  … levels 1 and 2 are byte-unchanged" — the recon's §S3.1 substitution
  table and the TWIST0 tooth's n₂(k) = ϖ^k row survive the annex era
  unmoved. DEFINITION HE7-1, HE7-7′(a)/(b), COROLLARY HE7-7″ [r1], LEMMA
  HE7-12(d) [r3] re-read at HEAD against the recon's citations —
  line-level agreement at the cited clauses. The [r1′] F-5 citation-era
  paragraph's two factual claims verified: HE7-12/13's displays carry ℓ
  as a parameter ((S5.8.1)'s ℓ(D′−1)ε₀ coefficient, HE7 L823), and HE7's
  PE2 fresh route was ℓ = 1, d_r = 2, K₂ = F_{p²}, 634 members, σ == PARI
  634/634 (`HE7_passPE2_report.md` L9–10). Post-PE1 annex-era additions
  (ANNEX-LEMMA HE7-13′, R1-b/R1-c) sit under the same explicit
  citation-era scoping sentence ("read at citation era 62d683f"), which
  is the honest device; no adapted-content drift found. HE7-12(c) item
  (7) at HEAD already lists "LEMMA HE6R1-2's read consumes only the
  HE7-7/7′ analogues, items (5)–(6)" — consistent with the rider's
  consumption inventory.
* **P1 re-score + Totals split (attack 4, PE1 F-7/F-4 repairs).** The
  restated scoreboard ("FAILED AS PREREGISTERED — DIAGNOSED AND CURED
  POST-SEAL") matches the artifacts: 944 members, 932 decided, 12
  BADTOTAL, 5 of the 12 in the 682 PARI jobs, 677/677 decided-and-checked
  agreement, 0 σ outside the three-element alphabet (0 alphabet-violation
  records in the json). The Totals split "42 strict-excess certificates +
  4 sealed SEP2 violations (recovered STRICT post-seal)" matches the
  runner's counter semantics read from the code: `note('HE6R1-SEP2')` at
  each TESTED instance (46) precedes the strict-excess check whose
  failure appends the violation (4), so sealed certificates = 42; the
  supp's recovery leg re-ran here 4/4 STRICT (68>64 ×2, 100>96 ×2). The
  retirement of "✓ with one honest qualification" is the honesty-correct
  direction.
* **[r1′] footprint discipline.** The three r1′ commits touch only the
  note file (git show --stat); sealed runners and artifacts byte-frozen
  as claimed (md5s below). F-6's corrected R8 row now matches the HE6
  bytes (L430–431: one standing sentence, tagged [r1, R8/F9], "below"
  scoping the §S4 displays).
* **Free hunt (attack 5), no finding.** Re-checked: (b)'s generic-letter
  degree bound (> max(deg f/D″, μ₂) dominates the residual degrees of
  both f and f_S); the concave-PL argument (constant difference on
  (T₂, ∞) forces shared breakpoints/slopes/lengths); FINDING HE6R1-F1's
  non-propagation arithmetic (ℓ₂d_{r₂} ≥ 2 ⟹ L_{λ₂} ≥ 4 ⟹ μ₂ ≥ 4 vs
  HE7's μ₂ ≤ 3 scope); LEMMA HE6R1-1's two displays and the J ≤ log₂n − 2
  iteration; the n ≤ 7 chain; LEMMA HE6R1-3's orbit/degree pinch. The
  (a)-proof's level-1 applications of HE6-1/2/2′/3/4 to g are frame
  instantiations, not evaluand widenings — g is monic with disc g ≠ 0,
  Φ′ ∤ g, roots on the same opening locus, so the frame's hypotheses hold
  at f := g (unlike the level-2 frame, which is keyed to f_S — which is
  why F-2's rider was needed there and nothing analogous is needed here).

---

## MACHINE LEG (isolated re-verification, this pass's own)

* **Pins.** At HEAD == 850e77e byte-identical (md5): runner
  7112f7c738ed13fb352f96849da1d309, supp 79da51dcd40535da82effb2e347b7f18,
  output f842065a…, results json cbd8fd25…, supp output 691f5bce…, supp
  json 6cd743ce…. Import pins inside the committed json (he6_checks
  321fa4d4…, he7_checks 688adbe8…, w12 7dc040d9…, w10 a9c34244…) match
  the HEAD file md5s.
* **Isolated re-run.** Battery re-run from 850e77e blobs in a clean
  directory (`git archive 850e77e`, full verification/openmath tree, so
  the deeper import chain is pinned too): stdout identical to the sealed
  output modulo per-row timing; results json identical modulo `secs`;
  the 21 violation records reproduced exactly — 12 READ2 (BADTOTAL
  non-decisions) + 5 SIG2 (read None vs PARI {(2,2),(2,2)}) + 4 SEP2;
  legs {LIFT2 59, READ2 932, SLOT2 1512, GEN2 252, SEP2 46, SEP2-inf 4,
  SIG2 682}; teeth 5/5 FIRED. Supp re-run in the same clean directory:
  identical modulo timing; 12/12 peels decided, 5/5 PARI, 4/4 post-refine
  STRICT.
* **Tautology audit.** `level2_read` (runner L347–610) makes no gp/PARI
  call — grep over the function body: zero hits; PARI enters only at
  `run_row`'s scoring (L640s). Independent cross-tab with this pass's own
  Fraction-arithmetic division code on the full Z₃ row (124 members
  regenerated through the sealed generator): BADTOTAL = 4 = {Ψ | f} = 4,
  coinciding member-by-member — the non-decision stratum is exactly the
  Ψ | f stratum on that row, agreeing with PE1's independent 944-member
  cross-tab.

## FRESH ROUTE (`verification/openmath/he6r1_pe2_fresh.py` + artifacts) — the non-prime-q leg

The PE1-disclosed never-run candidate: an ℓ = 1 repeated-irreducible-
residual family over a NON-PRIME residue field — K = F_{p²} (e₁ = 1,
f₁ = 2, h = 1, Φ′ = x² − c·p² with c a QNR), r irreducible quadratic over
K, K₂ = F_{p⁴} — the first machine contact of the widened box's ℓ = 1
branch at f₁ ≥ 2 (HE6R1-BOX-2 lists f₁ ≥ 2 as unexercised). Construction,
residual computation (exact F_{p⁴} tower arithmetic) and the σ dictionary
(e = e₁ℓℓ₂, f = f₁d_r·deg r₂) were derived by this verifier from first
principles — not read through the sealed reader — and scored against
PARI (factor + nfinit([g,[p]]) + idealprimedec; poldisc ≠ 0 asserted per
member; predictions preregistered in the runner docstring before the
first gp call). **3 frames (F₉ base with r₁ = 0 and r₁ ≠ 0 genres; F₂₅
base), 487 members, 487/487 PARI agreements, 0 mismatches, 0 zero-disc.**
Families per frame: A0/A1 (λ₂ = 7, ℓ₂ = 1: R = Z² + γ₁Z + γ₀ over
K₂ = F_{p⁴}; both genres live — the p = 3 A0 sweep split 40 irreducible
→ {(1,8)} / 40 split → {(1,4),(1,4)}), B (λ₂ = 13/2, ℓ₂ = 2 → {(2,4)}),
P (Ψ | f peel → {(1,4),(1,4)}), plus a DIRECT check of LEMMA HE6R1-3's
prediction at f₁ = 2: Ψ itself irreducible with (e, f) = (e₁ℓ, f₁d_r) =
(1, 4), 3/3 frames. Two double-root (α-refine-stratum) members set aside
with count, disclosed (the refined read is PE1 leg B's territory).
Self-tooth: deliberately wrong dictionaries on 2 members were caught
(mismatch detected both times); factorpadic spot-check on one {(1,8)}
member returned a single degree-8 ℚ₃-factor, consistent.

---

## GRADE LINE

passPE2 verdict **CLEAN**: 0 CRITICAL, 0 GAP, 4 MINOR (an unflagged
HE7-side echo of PE1's F-3; a general-ℓ scalar-identification caveat; two
era/convention wording drifts). The four MINORs touch no display the
σ-decision chain consumes, and each has a one-line rider-style cure. The
machine leg is GREEN in isolation with the disclosed 21-record violation
set reproduced; the fresh non-prime-q route is GREEN at 487/487. Per the
protocol ("a CLEAN pass starts the count"): **HE6R1 moves 0/2 → 1/2**;
the four MINOR one-liners are owed as dated riders before or at the next
pass, and pass 2-of-2 remains.
