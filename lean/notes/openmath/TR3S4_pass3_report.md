# TR3-S4 hostile pass 3 (Fable, fresh context) — target REVISION 2

**Target:** `lean/notes/openmath/TR3S4_2026-08-08.md` (through REVISION 2) +
`verification/openmath/tr3s4_check.py` + recorded outputs. Context consumed:
TR3-S1/S2/S3 notes (accepted family), TWIST3_PROBE, the pinned
`docs/references/HigherNewton.tex`, GRB_ORDER2, strata3_probe (imported
perimeter). No prior TR3S4 pass report read (fresh-context discipline).
Charge: quote-and-classify, fix nothing; two mandatory execution legs.

**VERDICT: CLEAN — 0 critical, 0 gaps** (4 non-classifiable observations,
§6). The S8.4 F2c verifier-owned-implementation obligation is DISCHARGED by
this pass's execution leg 2 (§2): 1,108 checks / 0 failures at off-roster
p ∈ {5, 7}, with the GMN ordinates computed by the decorrelated geometric
(E4)-Fraction leg rather than the harness's hard-coded w₂ reading.

## 1. Execution leg 1 — the sealed battery, re-run

* `python3 verification/openmath/tr3s4_check.py` (isolated copies of the
  recorded outputs taken first): **exit 0**. Output **byte-identical to
  `tr3s4_check_output.txt` INCLUDING the four ring-timing lines and the
  TOTAL elapsed** (stronger than S8.3's "identical mod the four timing
  lines"); regenerated `tr3s4_check_results.json` **byte-identical** to the
  recorded file. 13,679 samples / 0 violations reproduced; repo left
  unmutated (byte-identity ⇒ no git-visible change).
* Recorded JSON reconciled against the note's S8.3 block field-by-field:
  counts (E2A 900, E2B 400, RI 9,267, RII/RIII/RIV 536 each, Z2 384,
  HV 160, XV 400, W 80, K 64, O 400, CERT 16; Σ = 13,679), meters
  (m0pos 87, t2nz 481, epsnz 340, vis 130, identkill 130 = vis, j0pos 72,
  noff 269, noisy 48, holes 34, wfail 0, naive 27), ord histogram
  0:366 1:19 2:15, 12/16 visible — ALL EXACT. No cypari2 warning in either
  run ⇒ the PARI legs genuinely fired.
* Design table re-derived by hand from the roster triples alone:
  S4A ℓ₁=1, γ₂=2·2·1+1=5, θ₂=1·2·5=10, γ₃=21; S4B γ₂=2·1·2+1=5, θ₂=10,
  γ₃=21; S4C ℓ₁=1, γ₂=3·1·1+1=4, θ₂=1·2·4=8, γ₃=26; S4D ℓ₁=2⁻¹ mod 3=2,
  γ₂=5, θ₂=2·2·5=20, γ₃=31 — matches the sealed header and the JSON tower
  records; the blind/visible pattern (S4A blind everywhere: θ₂=10 ≡ 0 mod
  ord(z̄₂)=5) is internally consistent with the disclosed ord column.
* Provenance: seal commit **7fa8825** (note 707 lines + script, 06:57:41)
  precedes run commit **79eaee6** (S8.3 block + both outputs, 06:59:18);
  `git diff 7fa8825..HEAD -- tr3s4_check.py` is **EMPTY** — the sealed
  script is byte-untouched through both revisions, as REVISION 1 ("NO
  falsifier change") and REVISION 2 (seal discipline) claim. 303b11e (the
  PIN-GEN-i extraction discharge) exists as cited.

## 2. Execution leg 2 — the F2c verifier-owned from-note implementation

Fresh implementation (`/tmp/tr3s4_p3_f2c.py`, this pass, seed 20260803),
written from the note's displays alone: own base-ring models (ℤ with p-adic
reduction; F_p[t] tuples), own nested-tuple field towers K₀/K₁/K₂ with own
arithmetic, own Φ₁/Φ₂ lawful-lift constructions (checked at runtime:
w₁(Φ₁)=g₀h₀, w₂(Φ₂)=e₁g₁γ₂), own FGMN pipeline (corrected Def 3.15 ǫ₂ +
Def 3.16 at i=2 stride e₁ / i=3 + Def 3.18 j₀-law; all slots computed
honestly incl. off-line and γ_j<0), own GMN pipeline (Defs 2.19–2.21 at
r=2,3 as pinned in TR3-S1 S1 + this note's S1; normalized ℓ per (H-ℓ)).
**Deliberate decorrelation:** the order-3 ordinates use
u_i = v₃geo(A_i) + i·v₃geo(Φ₂) with v₃geo = the (E4) min over exact
Fractions — NOT the w₂-hardcoded reading shared by gmn3 — and the per-digit
tie v₃geo = w₂ is checked at every consumed digit (263 ties) plus 60
dedicated HV draws (random P two-way + ordinate expansion three-way).

* Roster: 6 towers, **p ∈ {5, 7} (off-roster; roster is p ∈ {2,3})**, both
  ring kinds; corners: g₀=1 (K₁=K₀), g₁=1 (z₂∈K₁), d₀=2, h₀=2, h₁>e₁
  (h₁=3, e₁=2 — tests eq12 with h>e), e₁=3 with ℓ₁=2, and a designed BLIND
  control (ψ₁=z−1 ⇒ z̄₂=1; the law degenerates to IDENT-3 and held).
  One further tower came out blind by accident of ord(z̄₂) | θ₂ — retained
  as a second degenerate control. 4/6 twist-visible.
* Families per tower: 10 random f (deg ≤ 3·degΦ₂+4), Φ₂^a·h, Φ₁^a·h
  (a=1..3), π^k (k=0..2), exact powers Φ₂^a (forced j₀=a>0), a two-draw
  HOLE family (A₀ + A₂Φ₂², single-digit realizers π^mΦ₁^{s(β)} with s(β)>0
  forced — the dedicated **s₂>0 face**), and an off-line-nonzero-digit
  corner π^N + Φ₂.
* Checks: (TR3-S4-coeff) per abscissa + support equality (329), the
  (TR3-S4-form) list law (j₀=s₀(f), twisted elementwise tie, ends nonzero,
  length d+1; 144), HV two-way (60+263), t₂-integrality (156), and the
  EXP-3 integer identity (ℓ₁′s−ℓ₁u′)+m₀ = t₂+θ₂j read off MY two pipelines
  at every on-line slot (156). **TOTAL 1,108 checks, 0 failures, first
  run** (family precedent: 93/1,564/821 on TR3-S1/S3; 615/1,655 on HV3).
  Meters all fired: vis 28, identkill 28 == vis, epsnz 44 (the revival
  live at p ∉ {2,3}), t2nz 103, m0pos 5, j0pos 36, noff 107 (98 at
  negative slot weight), s2pos 38, spos 35, holes 12.
* Teeth (mutation controls on my own harness): drop ǫ₂ → 40 violations
  RED; compare naively (twist ≡ 1) → **exactly 28 = vis** violations RED
  (the identkill face from the negative side); drop the i·v₃(φ₃) term from
  the ordinate → 209 violations RED. The green run is not vacuous.

## 3. Lemma HV3-E2 — the print instantiation re-derived (the charter leg)

sha256 of `docs/references/HigherNewton.tex` re-verified =
`8253d4d6…bd18` (full match). The four displays re-read at the pinned
lines and confirmed GENERIC in r: (E1) H_{r−1}: 𝕊(λ_{r−1}) → ℤ_{≥0},
H(S) = u + |λ_{r−1}|·i (TeX 981, block 979–983 ✓); (E2) v_r(P) :=
e_{r−1}·H_{r−1}(S_{r−1}(P)) (TeX 988 ✓); (E3) discrete-valuation
proposition (TeX 1013 ✓); (E4) Prop `propertiesv` items 3/4 (TeX
1028–1038 ✓: item 3 the e_{r−1}·min development formula, item 4
v_r(φ_{r−1}) = e_{r−1}v_{r−1}(φ_{r−1}) + h_{r−1}). All five steps of the
S3 derivation re-run at r = 3 with the dictionary φ₂↔Φ₁, φ₃↔Φ₂,
(e₂,h₂)^GMN = (e₁,h₁): **e₂^GMN = e₁ and |λ₂| = h₁/e₁ enter exactly at the
three tallied sites** (step 2 twice; step 3's e₁-distribution through the
min — exact, every term e₁w₁(a_i)+iγ₂ ∈ ℤ, no rounding; step 4's E₂ = e₁
dilation = the standing TR3-S2 pin). The (E1) ℤ_{≥0}-codomain typing is
NOT load-bearing: at e₁ ≥ 2 the intercept is fractional, but it is
consumed only through (E4) whose e₁-multiplied output is an integer, as
the S3 step-1 display and the S9.1 attack item state. v₂ = w₁ is genuinely
e₁-free (Def 2.5 at r = 2 reads ν₀-data only — TR3-S1 S1 pin verbatim).
Step 5's ordinate expansion rides (E3) + GMN (18) ✓. The consistency
display v₃(φ₂) = e₁w₁(Φ₁) + h₁ = γ₂ = w₂(Φ₁) checks ✓. e₂ is indeed never
used ✓. Falsifier cover: the HV row here + my leg-2 v₃geo (223+60 checks
on Fractions) — both green. **Lemma HV3-E2 stands at attempt grade with
honest conditionality (HV3-THM's four standing conditions verbatim; the
e₁ ≥ 2 instantiation is this note's own, correctly NOT borrowed).**

## 4. The algebraic chain — re-derived in full

* **KER-13**: (e,h) = (1,·) forces (s,u) = (0,β), (ℓ,ℓ′) = (0,1),
  ǫ = z^{1·0−0·β} = 1 at FGMN levels 1 and 3 ((e₁,h₁)^F = (1,h₀),
  (e₃,h₃)^F = (1,h₂) at e₂ = 1) ✓; only ǫ₂ lives ✓.
* **A-GEN-3 citation discipline** (the S9.2 attack): TR3-S1's statement
  re-read — stratum {order 2, e₀ = 1} with ν₁ = (e₁,h₁,ψ₁) genuinely FREE
  ✓; total in nonzero f ∈ O[x], no degree bound (its scope note even runs
  Lemma A at a = Φ₁) ✓; (TR3-S1) is R^F_{2,γ}(f) = y^{j₀}R_λ(f) with
  j₀ = ⌊s₀(f)/e₁⌋, so at f := A, β := w₂(A): j₀ = ⌊(s(β)+m₀e₁)/e₁⌋ = m₀
  with m₀ = (s₂−s(β))/e₁ ∈ ℤ_{≥0} (TR3-S1 S5(i): on-line abscissas
  ≡ s(β) mod e₁, s₂ the least; s₂ ≥ s(β) since s(β) is the least
  non-negative residue) ✓; inner operator match: (SLOT) = (SLOT-2′)
  verbatim and GMN's r=2 inner data t₁ = s₁(a) at normalized ℓ₀ = 0 ✓.
* **Z2-e2**: both corners re-checked (γ_j < 0 and zero digits; the chain
  w₀(b) ≥ w₁(a) − m″h₀ > β_{m′} − m″h₀ = δ gives strictly-positive
  valuation of every coefficient of b·π^{−δ} including δ < 0); domain
  direction INSIDE P_β(µ₂) ✓. Tested honestly in leg 2 (107 off-line
  nonzero-digit slots computed, all zero).
* **EXP-3**: multiplied by e₁, LHS = s(ℓ₁′e₁+ℓ₁h₁−1) + s₂ − ℓ₁β =
  s₂ − ℓ₁β; RHS = s₂ − ℓ₁β − ℓ₁Se₁g₁γ₂ + e₁ℓ₁g₁γ₂S = s₂ − ℓ₁β ✓; the
  common value is integral (s₂ ≡ s ≡ ℓ₁β mod e₁, via β ≡ sh₁ and
  ℓ₁h₁ ≡ 1) ✓; t₂-integrality free ✓; e₁ = 1 collapse to m₀ = s₂ =
  TR3-S3's form ✓. Independently instantiated 156× in leg 2.
* **t₂-absorption (S5(ii))**: the five-display chain re-derived; the
  on-line ordinate u_j = γ_j + j·e₁g₁γ₂ matches EXP-3's u_S at β = γ_j,
  S = j ✓; the nonvanishing degree bound deg R_λ₂(A) ≤ (e₁g₁−1)/e₁ < g₁
  (where deg A < deg Φ₂ is consumed) + the K₁-basis evaluation argument ✓;
  support equality incl. the γ_j < 0 face ✓; assembly/two-form re-indexing
  and the y^{j₀} division (k = 0 term nonzero ⇒ observed initial slot =
  j₀ = s) ✓.
* **σ₂ (S2)**: Cor 5.6(2) chain-internal at index 2 < r (no (KP_i)) ✓;
  TR3-S1 at f = Φ₂ with the substate's trivial twist ✓; the monicity
  upgrade re-computed (top digit on-line with c^G2_{e₁g₁} = 1 at ℓ₀ = 0;
  lawful degree forces s₂(Φ₂) = 0; monic associate of monic ψ₁ = ψ₁) ✓;
  (SQ₂) ✓. My leg-2 Φ₂ construction realizes exactly this datum and its
  runtime asserts double-check the two w-pins on 6 fresh towers.
* **S6.2**: KEY0-LIFT's four steps ✓ (degree window ⇒ s₀ = 0, s′ = g₂;
  the T_{c⁻¹} coefficientwise form (R_λ₃(Φ₃^h))_k = z̄₂^{−θ₂k}ψ₂_k ✓);
  the step-1 scalar pin t₂(g₂) = (0 − ℓ₁g₂e₁g₁γ₂)/e₁ = −θ₂g₂ ✓ and
  **R_λ₃(Φ₃) = z̄₂^{−θ₂g₂}·ψ₂ (UNTWISTED)** ✓ — the REVISION 1
  orientation is the correct one; σ₂(ψ₃^F) = z̄₂^{−θ₂g₂}·T_cψ₂ ✓; the
  ORD-INV-LIFT four-step ord chain ✓ (T_c automorphism / scalars / step 1
  + form / σ₂ iso); both divergence criteria re-derived (class: some
  k < g₂, ψ₂_k ≠ 0, z̄₂^{θ₂(g₂−k)} ≠ 1; literal: some k ≤ g₂, ψ₂_k ≠ 0,
  z̄₂^{θ₂k} ≠ 1) and they match rows k-iii/k-iv ✓. (KP_i) enters only at
  the state key, [T]-properness displayed not discharged ✓.
* **WIT-3 / Remark 2**: the W₀ threshold re-computed — the worst slot
  gives β_k ≥ (g₀−1)h₀ exactly, all π-exponents nonnegative, deg A <
  deg Φ₂ ✓; the two-slot ordinate tie u₀ = u₁ + h₂ ✓; the ratio-invariance
  refutation argument sound wherever z̄₂^{θ₂} ≠ 1 ✓.

## 5. Revisions, fences, record

* **REVISION 1**: `git diff 79eaee6..HEAD` on the note = exactly the five
  declared orientation sites + the S8.3 79eaee6-hash insertion + the two
  appended revision blocks — the "perimeter textually untouched" claim is
  diff-verified. Each of the five rewrites is the mathematically correct
  orientation (§4 above, re-derived independently).
* **REVISION 2 (the seal-supersession bracket)**: the stale sentence
  exists exactly once, in the sealed script header; the seal is
  byte-untouched (§1); the bracket names the sentence, states the
  corrected orientation, and claims row K's actual construction is
  correctly oriented — **independently confirmed**: `strata3_probe.
  Tower3.build_Phi3` realizes ǫ₂(gp)⁻¹-adjusted ψ₂ digits, i.e. the
  FGMN-NORMALIZED canonical lift, so k-i (fresh side read = ψ₂, j₀ = 0)
  and k-ii (gmn3 class = z₂^{−θ₂k}ψ₂_k) test KEY0-LIFT step 0 exactly;
  the defect was descriptive only. Correct disposition under the seal
  discipline.
* **Fences (S7)** honored: no e₀ ≥ 2 (A-GEN-3's citation genuinely needs
  the substate's e₀ = 1), no e₂ ≥ 2 (KER-13's level-3 clause and the S5
  assembly are e₂ = 1-throughout), no order ≥ 4, no D-ITER object consumed
  (the argument never touches composite-digit algebra). Conditionality
  displays present at every consumer site ((H-ℓ), (PIN-GEN-i) + 303b11e,
  Lemma HV3-E2's own status box, (KP_i)+[T] at S6.2 steps 1/3, GMN base
  scope). S6.1's coverage union is correctly assembled (order 2 =
  TR3-S1 ∪ TR3-S2; order-3 e₁ = 1 = TR3-S3; e₁ ≥ 2 = this unit at attempt
  grade, flagged). Acceptance counter honestly 0/2 after two GAPS-ONLY
  passes. S8.1's probe numbers reconciled against TWIST3_PROBE (C1
  0/1,656 over 2,274 comparisons, P4′ 0/24 + secondary RED 10/24, P5′
  0/1,656, M6 710/710, M1 1,277/1,277, M8 142, 23,733 samples, seals
  76513f8/48c07b4 — all exact).

## 6. Non-classifiable observations (no fix required)

1. **Upstream orientation echo, outside this unit's perimeter**:
   `TWIST3_PROBE_2026-08-08.md` line 80 ("the GMN-lawful level-3 key class
   is the θ₂-TWISTED ψ₂ class") carries the same pre-REVISION-1 mislabel
   as the sealed script header (the probe's Φ₃ is likewise the
   FGMN-normalized lift). TR3-S4 itself never repeats it — S6.2/S8.1 cite
   only the rows, which are correct — but a future consumer reading the
   probe note alone inherits the mislabel; the ledger may want a bracket
   there too.
2. S6.2 step 0 cites "the probe's P4′ primary row 24/24 and V4 row 0/24"
   — mixes confirmation-count and violation-count conventions in one
   sentence; both figures are accurate to their sources.
3. S8.3's "rerun output identical mod the four timing lines" understates:
   this pass's rerun was byte-identical INCLUDING all timing figures; the
   claim is verified a fortiori (and the TOTAL line, which also carries an
   elapsed figure, is not one of the "four").
4. In my leg-2 roster one designed-visible tower (W2) came out blind
   because ord(z̄₂) = 2 | θ₂ = 10 — an accident of my ψ₁ pick, retained as
   a second degenerate control; no bearing on the note (its own design
   table computed visibility correctly pre-seal).

## 7. Verdict

**CLEAN — 0 critical / 0 gaps.** The composed identity, its six-lemma
route, the print instantiation, both revisions, the fences, and the full
falsifier record all survive hostile re-derivation and two fresh execution
legs (13,679/0 reproduced byte-identical; 1,108/0 verifier-owned at
off-roster primes with the decorrelated ordinate leg and teeth-validated
harness). The S8.4 F2c obligation is discharged on this pass. First CLEAN
on the arc (passes 1–2 were GAPS-ONLY); per the standing bar, one further
clean model-diverse pass decides acceptance.

— TR3-S4 pass 3 (Fable), fresh context, 2026-08-03.
