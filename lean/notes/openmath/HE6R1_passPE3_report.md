# HE6R1 passPE3 — hostile pass 3 on the RECONCILIATION note + its post-PE2 dated micro-annex (fresh context; THE ACCEPTANCE ATTEMPT)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 3 MINOR. The owned surfaces (§S2's
four-case analysis + n ≤ 7 chain end-to-end; the [r2]-era rows' timeline;
LEMMA HE6R1-1 vs THEOREM HE7.C [r1] at character level; the 12+5+4
exception taxonomy re-derived from the sealed code; the dated micro-annex
rider-by-rider) all held. Machine leg: bit-identical isolated re-run, 21
disclosed records reproduced, tautology audit clean. Fresh route: the
ℓ₂ = 3 genre + two-sided level-2 polygons at μ₂ = 3 — 246/246 by BOTH
PARI oracles, 0 mismatches, including the program's first WILD-corner
member family (p = 3, e = 6). The 2-clean count completes:
1/2 → 2/2 — HE6R1 ACCEPTED.**

Target: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md` at HEAD (annex
a57c486 on the PE2-era body; arc seal 4f5ebaa → verdict 850e77e → [r2]
rows cec49ba/d1b0bc8 → PE1 report (0C/2G/5m) → [r1′]
71c7457/8cbfaa2/57700f3 → PE2 CLEAN 2118e59 (count 1/2) → dated
micro-annex a57c486). Append-only claim verified: the a57c486-parent blob
md5 is exactly the annex's stated prefix b43b798f229f5f68f35c41b37a072099,
and the file is byte-unchanged since a57c486. Protocol:
quote-and-classify, nothing fixed. Surfaces owned by this pass are
disjoint from PE1/PE2's routes (their reports read, their walks not
re-walked).

---

## FINDINGS (ranked; none GAP-or-worse)

### F-1 (MINOR) — the annex F-2 rider's cocycle-exponent argument is the side's LINE VALUE, which is a non-integer off the first side at ℓ₂ ≥ 2 (display ill-formed there; the composing argument is the PIN height)

Quote (micro-annex, PE2 F-2 rider):
"n₂(h_{F₂,f_S}(λ₂))·n₂(c_g) = τ₂(h_{F₂,f_S}(λ₂), c_g)·n₂(h_{F₂,f}(λ₂)),
with h_{F₂,f}(λ₂) = h_{F₂,f_S}(λ₂) + c_g by (b) and the heights in ℤ
(dv₂ ℤ-valued)", and the display
"R^f_{λ₂} = γ_g · β^{c₁(h_{F₂,f_S}(λ₂), c_g)} · R^{f_S}_{λ₂}".
The same formula sits in frozen HE7's same-wave dated line 263cef0.
Defect: n₂ and s(·) — hence c₁(a, b) = (s(a)+s(b)−s(a+b))/ℓ, per
ANNEX-LEMMA R1-a(ii)/(iv) — are defined on ℤ (R1-a: "for all
a, b, k ∈ ℤ"). The line value h_{F₂,f_S}(λ₂) = m₁ + j₁λ₂ (m₁ :=
dv₂(A^{(2)}_{j₁}) at the side's starting index j₁) is an integer only
when ℓ₂ | j₁. On a MULTI-side level-2 polygon a later side starts at
j₁ > 0 not divisible by ℓ₂: e.g. pins (3,0), (1,13), (0,21) — this
pass's own fresh-route TS geometry — give the 13/2-side
h(13/2) = 13 + 13/2 = 39/2 ∉ ℤ, and s(39/2) is undefined. The composing
argument, re-derived here: normalize each side by n₂(m₁)·Ψ(ξ)^{j₁} (the
normalization HE7-7′(b)'s own proof uses — "the line height
m₁ − λ₂(j−j₁) is an integer only then"); the Ψ(ξ)^{j₁} factor is COMMON
to f and f_S (same sides by (b)) and cancels in the ratio, so
f/N_f = (f_S/N_{f_S})·(g/n₂(c_g))·τ₂(m₁^{f_S}, c_g) with
m₁^f = m₁^{f_S} + c_g (vertex pins shift by c_g), all arguments in ℤ —
the correct exponent is **c₁(m₁^{f_S}, c_g)**, the pin height, which
equals the annex's line-value form exactly when j₁ = 0 (single-side
polygons, the first side — and every ℓ = 1 use, where c₁ ≡ 0 anyway).
Failure scenario: a consumer at an ℓ ≥ 2 proper block whose level-2
polygon has a second side evaluates the annex display's exponent there —
undefined at h ∉ ℤ, and off by a β-power where h ∈ ℤ but j₁ ≢ 0 (mod ℓ₂).
Blast radius: the same as PE2's F-2, whose classification this inherits —
the consumed content (a FIXED nonzero K₂^× scalar per side; consumers
scale-invariant; γ_g alone exact at ℓ = 1, the branch every proof-use and
battery member lives on) survives untouched; no consumer at HEAD reads
the exponent. The HE7-side copy (263cef0) carries the same wrinkle — an
HE7-side residue, noted here.

### F-2 (MINOR) — the §S6 completion statement's grade parenthesis "except HE3 at 1/2 for μ ≤ 3" is falsified DOWNWARD at HEAD, outside the annex F-3 re-date's scope

Quote (§S6, qualification (i)): "every step is proved in a note at
attempt grade 0/2 (HE6 post-r1, HE7 …, GENHN …, this note) **except HE3
at 1/2 for μ ≤ 3**". At HEAD, HE3 is 0/2 (its [r1] corrected the old 1/2
down; `HE3_passPE2_report.md` @ 6d0ff09 left 2 GAP, one PARI-confirmed
at the (2,2) geography; r2 owed). This is a third site of PE2 F-3's
stale-grade genus, and the one site where the direction is NOT
conservative — it OVERSTATES a dependency's grade. The annex F-3 re-dated
HE6R1-BOX-1 (including, correctly, "HE3 0/2 … minimum keeps value 0/2,
now keyed to HE3") and the R3 row, but not this §S6 sentence. Failure
scenario: a reader prices the composition off §S6's qualification alone
and takes HE3's μ ≤ 3 leg as pass-1-verified. Mitigation in-file: the
authoritative grade box (BOX-1 + annex F-3) carries the corrected
minimum, keyed to HE3's 0/2, so the chain's PRICED conditionality is
right; the stale sentence is prose in the frozen seal-era body.

### F-3 (MINOR) — unqualified "PE2 F-1"/"PE2 F-4" references inside the R3 row's [r2] block now collide with this note's own PE2 finding numbers

The R3 row ([r2] era, written before this note had a PE2) cites
"(PE2 F-4: …)" and "(PE2 F-1)" meaning HE6's passPE2 findings (verified:
`HE6_passPE2_report.md` F-4 = the five cosmetic byte-diffs, F-1 = the
η_θ^{−q(k)} coset omission — content matches the row exactly). At HEAD
this note's OWN PE2 report also has an F-1 (the HE7 §S5.5 echo) and an
F-4 (tag imprecision), so the bare references acquired a second candidate
referent after the fact. The annex F-4's precise convention resolves
[r1]/[r2] TAGS but is silent on pass-report references. Failure scenario:
a mechanical reader resolves "PE2 F-1" to this note's PE2 and re-points
the coset-correction cite at the S5.5 scalar finding. Context
disambiguates for a careful reader (the same sentence quotes commit
5da0552's subject, "…from HE6 PE2 F-1").

---

## CLEAN CHARGES (attacked, survived)

* **Owned surface 1 — §S2's four-case analysis + the n ≤ 7 chain,
  end-to-end.** Exhaustiveness/disjointness re-derived: every side either
  has separable R_λ (iii), or carries a repeated irreducible factor; a
  repeated factor is K-rational-linear-at-integer-slope exactly when
  ℓ = d_r = 1 (a monic linear r ∈ K[Z] is automatically K-rational;
  "integer slope" ⟺ ℓ = 1), so the excluded set
  {repeated} ∖ {ℓ = 1 ∧ d_r = 1} = {repeated with ℓd_r ≥ 2} = (ii) ∪ (iv)
  exactly. Corners checked: a repeated LINEAR factor at ℓ ≥ 2 falls in
  (iv), not (i) — HE6 §S6.3 confirms the recentering needs λ ∈ ℤ ("the
  recentered key Φ′ + ŝϖ^λ exists because λ ∈ ℤ there"); a side carrying
  BOTH a repeated linear and a repeated non-linear factor has a stage-CS
  event and is excluded, with HE7's read descending into each distinct
  factor's block (HE6R1-2 consequence (2)); the mechanisms cited per case
  verified at HEAD (HE6.B [r1] clause-for-clause; §S6.3; HE6-3(b)
  n_λ = D′L_λ). The n ≤ 7 chain: deg R_λ ≥ m·d_r (r^m | R_λ), L_λ =
  ℓ·deg R_λ ≥ m(ℓd_r) ≥ 4; μ = Σ_λ L_λ ≥ L_λ under Φ′ ∤ f — and ROBUST to
  the R2 peel: if Φ′ | f then f̃ has μ̃ = μ−1 ≥ 4 and n = D′ + deg(locus
  part of f̃) ≥ D′(μ̃+1) = D′μ, same bound; n ≥ D′μ via HE6-3(b) summed
  over slopes; D′ ≥ 2 at a composite stage (a D′ = 1 event is the
  stage-OPENING order-1 read, not a stage-CS event — the boxed
  configuration is the SECOND repeated-irreducible event, inside the
  stage); nested stages only increase the factor. Both first-bite
  witnesses check: (iv) at (2,2,1) L = 4 (ALPHA2), (ii) at (1,2,2) L = 4
  (this note's rows). n ≤ 7 → μ ≤ 3 → no boxed node. ✔
* **Owned surface 2 — the [r2]-era rows' timeline at HEAD (three tag
  eras + annex).** The [r2] era is cec49ba (08-09 12:51) + d1b0bc8
  (12:52): both AFTER 5da0552 (12:50) — the R3 row's "LANDED this wave"
  is accurate — and both BEFORE db0001a (13:01) — so "does not soften …
  (an HE7-side residue, noted here)" was true as written, and the annex
  F-3's "addressed at the owner" re-date is the correct cure, not a
  contradiction. The [r1′] commits (15:22–15:25) postdate HE7's
  acceptance stack (a472155 07:24, ca3754d 07:32) — PE2's F-3 timeline
  claim re-verified — and the annex (16:43) postdates PE2 (2118e59
  16:20), HE7's S5.5 dated line (263cef0 16:42), and HE3's PE2 (6d0ff09
  16:24), so every annex cross-cite is to an object that existed at its
  landing. The header's tag-convention sentence, §S1 rows R1–R9 (era
  tags [r1]/[r2]/[r1′] each dated), BOX-1 + annex re-date, and the §S6
  scoreboard [r1′] rewrites are mutually consistent at HEAD — the one
  residue found is F-3 above (report-reference collisions), plus F-2's
  un-re-dated §S6 sentence.
* **Owned surface 3 — LEMMA HE6R1-1 vs THEOREM HE7.C [r1] at the CURRENT
  frozen HE7, character level.** HE7.C [r1] (HE7 L253–277): jump
  condition "repeated irreducible residual factor r (multiplicity m ≥ 2)
  with ℓ·deg r ≥ 2"; first display via L_λ ≥ ℓ·m·d_r = m(ℓd_r) ≥ 4;
  second display μ₂ ≤ μ/(ℓ·d_r) ≤ μ/2; J ≤ log₂ μ − 1 ≤ log₂ n − 2; n = 8
  one jump, μ₂ = 2; first level-3 degree n = 16 — bound-for-bound and
  character-for-character the recon's LEMMA HE6R1-1 (whose fuller chain
  μ₂ ≤ deg R_λ/d_r ≤ μ/(ℓd_r) HE7.C's [r1] paragraph reproduces, crediting
  the lemma). The middle step re-derived: deg f_S ≤ n_λ = D′L_λ
  (HE6-3(b), (SEP)-free) and D″ = D′ℓd_r. HE7.A(3) [r1] re-read at HEAD:
  splits on ℓ₂·deg r₂ (not ℓ₂), with the α-refine branch licensed at
  ℓ₂ deg r₂ = 1 via s₂ ∈ K₂ and the non-propagation μ₂ ≥ 4 re-derived
  in-place — exactly FINDING HE6R1-F1's landing as the recon states it. ✔
* **Owned surface 5 — the dated micro-annex, rider by rider.**
  Append-only verified (prefix md5 exact; no post-annex commits touch the
  file). F-1 rider: HE7's dated line 263cef0 exists, same wave, states
  the per-side K₂^×-scalar correction with the scale-invariant-consumer
  check — the PE2 F-1 cure landed at the owner as claimed. F-2 rider:
  re-derivation checked against frozen HE7's ANNEX-LEMMA R1-a —
  R1-a(ii)/(iv) give τ₂(a,b) = Λ₁^{c₁(a,b)}, c₁ ∈ {0,1}, R1-a(iii) the
  fixed transported unit β^{c₁} ∈ K₂^×, exactly as cited; the
  γ_g-multiplicativity and generic-letter conversion are sound; s(·) ≡ 0
  at ℓ = 1 (§S3.1 table) makes the scalar γ_g alone there ✔ — the one
  defect is the exponent's argument (F-1 above). F-3 rider: every grade
  re-date verified against the commit record (HE7 2/2 FULLY FROZEN with
  HE6R1-F1 applied, micro-annex ca3754d; HE6 2/2 PE4 7ca97c9; GENHN 2/2
  PE4 6053c3d; GENIND 2/2 with ANNEX R at its own unpassed grade,
  cd5b0f4/98ac7bb; W-12 2/2 d76b785 + re-anchor 2fcbd0c; HE3 0/2 with r2
  owed, 6d0ff09; this note 1/2, 2118e59); minimum 0/2 keyed to HE3 ✔;
  the R3-row residue re-date matches db0001a ✔. F-4 rider: the four
  enumerated cross-note sites verified at the named lines (L78 GENHN
  [r1]; L237/L241 HE7 [r2]; L432 HE7 [r1]), each carrying its file
  qualifier; an independent grep over the note's [r1]/[r2] uses found no
  additional site (the residue found is pass-REPORT references, F-3
  above, which the convention does not claim to cover). Count-holds
  disposition (minors-only, HE7 ca3754d precedent) is the arc protocol's.
* **Owned surface 4 — exception taxonomy.** See MACHINE LEG below: each
  class's mechanism re-derived from the sealed code and each count
  reproduced in isolation.
* **Free hunt (no further finding).** LEMMA HE6R1-1's proof steps
  (complement enumeration = §S2's; both displays; the iteration
  4 ≤ μ_J ≤ μ/2^{J−1}); LEMMA HE6R1-3's "at most once" (simplicity from
  disc f_S ≠ 0); §S3.2 item 2's margin arithmetic ((D′−1)h < λ from
  λ > D′h and h ≥ 1; (d_r−1)λ + (D′−1)h < d_rλ ≤ u₂; λ₂ > T₂ = d_rλ ≥
  2λ > λ + (D′−1)h); item 5's ℓ = 1 chain (gain beats deficit by 1 per
  offset); P3's threshold arithmetic ((d_r−1)u + (D′−1)h = λ+1 at both
  frames, matching the re-run's tables); the §S6 census arithmetic
  re-added (12 BADTOTALs distribute 4+1+4+3 over the rows; decided
  per-row counts sum to members − BADTOTALs; 677 = 682 − 5).

---

## MACHINE LEG (this pass's own isolated re-verification)

* **Pins.** At HEAD, all six committed artifacts byte-identical (md5) to
  their 850e77e blobs: runner 7112f7c738ed13fb352f96849da1d309, supp
  79da51dcd40535da82effb2e347b7f18, output f842065a…, results json
  cbd8fd25…, supp output 691f5bce…, supp json 6cd743ce…. The four import
  pins recorded inside the committed json (he6_checks 321fa4d4…,
  he7_checks 688adbe8…, w12 7dc040d9…, w10 a9c34244…) equal the md5s of
  the 850e77e blobs and of the HEAD files.
* **Isolated re-run.** Full `verification/openmath` tree extracted from
  850e77e via `git archive` into a clean directory (transitive import
  chain pinned by construction); `he6r1_checks.py --full` re-run there:
  stdout IDENTICAL to the sealed `he6r1_checks_output.txt` modulo per-row
  timing strings; results json identical modulo `secs` fields
  (field-by-field compare after dropping `secs`: True); legs
  {LIFT2 59, READ2 932, SLOT2 1512, GEN2 252, SEP2 46, SEP2-inf 4,
  SIG2 682}; teeth 5/5 FIRED; 21 violation records; 87.2 s. Supp re-run
  in the same directory: 12/12 peels decided, 5/5 PARI agree, 4/4
  post-refine STRICT. Exit 0 on both. (One re-run wrinkle, disclosed:
  invoking the runner with no flags runs the SMOKE path only — exactly as
  the sealed docstring's smoke record states; `--full` is the battery.)
* **Tautology audit.** `level2_read` (runner L347–524) contains zero
  gp/pari/factorpadic references (grep over the exact line range); PARI
  enters only at `run_row`'s scoring and the teeth.
* **Exception taxonomy re-derived from the sealed code (owned surface
  4).** The 21 records classify as 12 READ2 + 5 SIG2 + 4 SEP2, and each
  class's mechanism was read off the code, not the note: (a) READ2 —
  `run_row` files a violation whenever `level2_read` returns status ≠ OK;
  all 12 records carry status BADTOTAL, produced at runner L413 when the
  reader's block sizes fail to sum to deg f (the Ψ | f stratum:
  A₀^{(2)} = 0 kills the j = 0 pin). (b) SIG2 — the PARI leg runs only on
  char-0 rows (`oracle and R.char0`); a BADTOTAL member there has
  σ = None ≠ PARI's {(2,2),(2,2)}. Verified: the 5 SIG2 f-strings are an
  exact subset of the 12 READ2 f-strings; the 12 distribute 4 (ℤ₃) +
  1 (ℤ₅, r = Z²+Z+1) + 4 (F₃[[t]]) + 3 (F₅[[t]]) — char-0 subset = 5,
  matching "5 of the 12 sit in the PARI count" and the per-row σ census.
  (c) SEP2 — `grid2_labels` harvests (λ₂, r₂) labels from the reader's
  FINAL trace (post-α-refine states) while `build_psi2` always builds the
  test key over `fr.Psi`, the frame's PRE-refine key; the 4 violations
  are all `got == flat` (56=56, 56=56 at κ₂ = 8; 88=88, 88=88 at
  κ₂ = 12) — flat equality where strict excess was predicted, exactly the
  misalignment mechanism (the mis-keyed Ψ₂ behaves generically). The
  supp's recovery over the refined key gives 4/4 STRICT (68>64 ×2,
  100>96 ×2), the note's numbers.

## FRESH ROUTE (`verification/openmath/he6r1_pe3_fresh.py` + artifacts) — the ℓ₂ = 3 genre + two-sided level-2 polygons, BOTH oracles, first WILD corner

Disjoint from the seal battery (μ₂ = 2, ℓ₂ ∈ {1,2}, p ∈ {3,5,7}), PE1's
legs (p = 11/13; peel∘refine), and PE2's leg (non-prime-q, ℓ₂ ∈ {1,2}).
Construction and predictions derived by this verifier from first
principles (the sealed reader NOT imported); predictions preregistered in
the runner docstring before the first gp call; scored against BOTH PARI
oracles per member — factor + nfinit + idealprimedec (global (e,f)
multiset) AND factorpadic (local degree multiset). **246 members, 246/246
agreements on both oracles, 0 mismatches, 0 zero-disc.**

* **Family C3 — the first ℓ₂ = 3 contact of the program**, and the first
  multiplicity-3 repeated residual (R_λ = r³, m = 3, μ = 6, n = 12,
  μ₂ = 3): f = Ψ³ − E + P with dv₂(E) = u₂ ∈ {19, 20}, λ₂ = u₂/3 > T₂ =
  6, perturbations strictly above the line. Predicted σ = {(6,2)}
  (e = e₁ℓℓ₂ = 6, f = f₁d_r = 2) with an INDEPENDENT non-HE7 leg
  (v(Ψ(θ)) = u₂/6 forces the e-denominator; β a root of r forces
  F_{p²} ⊆ residue field; ef ≤ 12 pins (6,2)). Frames (3,19), (5,19),
  (7,20), (5,20): 41+41+40+40 = 162/162, factorpadic returning ONE
  degree-12 local factor each. **p = 3 is wild (3 | e = 6) — the level-2
  dictionary's first machine test at wild ramification on this branch:
  41/41.**
* **Family TS — two-sided level-2 polygon at μ₂ = 3**:
  f = (Ψ − E₁)(Ψ² − E₂) + P with dv₂(E₁) = 8, dv₂(E₂) = 13; pins (3,0),
  (1,13), (0,21) give sides 13/2 (ℓ₂ = 2, L = 2) and 8 (ℓ₂ = 1, L = 1).
  Predicted σ = {(4,2),(2,2)}, factorpadic degrees {8,4}: p = 3 and
  p = 5, 42+42 = 84/84. (This geometry is also F-1's concrete
  non-integer-line-value instance — the machine result shows the SIGMA
  chain is untouched by that display wrinkle, as the scale-invariance
  analysis says.)
* **Self-tooth:** the planted "three separable blocks" dictionary
  ({(2,2)}×3) refuted by PARI on 8/8 tested members.

---

## GRADE LINE

passPE3 verdict **CLEAN**: 0 CRITICAL, 0 GAP, 3 MINOR (the annex F-2
rider's cocycle-exponent argument — line value vs pin height, ill-formed
off the first side at ℓ ≥ 2, ℓ = 1 exact, no consumer; the §S6
completion statement's stale "HE3 at 1/2" — the one non-conservative
stale-grade site, priced correctly in the corrected BOX-1 minimum; the
unqualified cross-report "PE2 F-n" references). None touches a display
the σ-decision chain consumes; each has a one-line dated-rider cure.
Machine leg GREEN in isolation (bit-identical; 21 records reproduced;
taxonomy mechanisms re-derived from code). Fresh route GREEN 246/246 on
both oracles (first ℓ₂ = 3, first m = 3, first wild corner, first
two-sided level-2 polygon). Rider verified as part of the charge. Per
the arc protocol (PE2 CLEAN started the count at 1/2; minors-only holds
the count; this pass is 2-of-2):

**HE6R1 moves 1/2 → 2/2 — ACCEPTED. The three MINOR one-liners are owed
as dated riders (F-1's cure lands at both copies: this note's annex and
HE7's dated line 263cef0).**
