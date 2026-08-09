# HE6 passPE2 — FABLE HOSTILE VERIFIER (fresh context) on the r1 text at HEAD

**VERDICT: NOT CLEAN — 0 CRITICAL / 2 GAP / 3 MINOR. Grade stays 0/2 (no upgrade).**

**Target:** `HE6_PROOF_2026-08-08.md` at HEAD (= 850e77e text; git-verified: zero
diffs 850e77e → HEAD on the note, the recon, and the PE1 record). Arc: seal
a77c376 → close 1f5a417 → Codex PE1 06f55f0 → r1 850e77e → **this pass (first
FABLE hostile leg on HE6; PE1 was the Codex leg)**. Protocol: quote-and-classify,
fix nothing. Attack order executed as charged: (1) the r1 text (R1–R9 one by one
+ HE6.B vs the recon), (2) HE6.A's proof core, (3) the HE6-1L/HE7-L1 interface
diff, (4) HE6-3(a)'s c₀ = 0 elimination, (5) free hunt. Fresh route: two legs
disjoint from the seal battery, the he6r1 682-member battery, and HE7's arc legs.

---

## S1. FINDINGS

### F-1 (GAP, machine-CONFIRMED — the r1 text, R3 site): LEMMA HE6-1L's exact reachable-set display omits the normalizer twist η_θ^{−q(k)}

> Quoted (HE6 §S1, LEMMA HE6-1L [r1]): "The set of residues realised as
> res(C(θ)/ϖ(θ)^k) by C ∈ O[x] with deg C < D′ and dv(C) = k is
> { Σ_{t ∈ T(k)} c_t·η_θ^{t} : c_t ∈ F_Q, not all 0 }"

GENHN-2's residue clause (the display's own proof input, via HE7 §S4.1's proof:
"by GENHN-2 the residue at height k is Σ_t res(a_{i₀+e₁t})η_θ^t") is normalized
by the attaining monomial — the canonical n(k) = x^{i(k)}π^{a(k)} — as GENHN §S4
states ("divide by the attaining monomial θ^iπ^v"). The ϖ-read residue therefore
equals the displayed span element TIMES the RIDER's own fixed factor:
C(θ)/ϖ(θ)^k = [C(θ)/n(k)(θ)]·[n(k)(θ)/ϖ(θ)^k] = γ·η_θ^{−q(k)}. At proper T(k)
with q(k) ≠ 0 the realized set is the COSET η^{−q}·span, not the span, and the
two differ.

**Confirmed instance (fresh leg B, exact PARI):** (e₁,f₁,h) = (2,2,3), O = ℤ₃,
Φ′ = x⁴ + 729 (single prime above 3, (e,f) = (2,2); η = res(θ²/27), η² = −1,
η ∉ F₃), ϖ = xπ^{−1}, k = 3: i₀(3) = 1, T(3) = {0} proper, q(3) = 1. Over 162
enumerated members C with dv(C) = 3 the realized ϖ-read set is **{η, 2η}**
(gp: {y, 2*y} in F₉) — **disjoint from the displayed set {1, 2} = F₃^×**.

**Non-propagation (checked, scoped):** the eight consumption routes I examined —
DEFINITION HE6-1's B_t lifts (k = (d−t)u > (D′−1)h, T full), the NON-PROPAGATION
box's own display, HE6-3/HE6-4's Ψ constructions, HE7 §S4.2's (LIFT₂) proof
calls (m_t > λ > (D′−1)h per §S4.3 [r1]), HE7's W₁/W₂ sharpness display,
tooth HE7-T-LIFT2SHARP, the he6r1 leg P3, and R_λ's §S1 definition (a
definition, not a reachability claim) — consume only the K^×-fullness clause
("ALL of K^× iff T(k) full"), which is twist-invariant (η^{−q}·K^× = K^×), or
the T(k) = ∅ clause (twist-free). No theorem of HE6/HE7 moves. Codex PE1's
adjudication of F4 and HE7 PE1's by-hand check of HE7-L1 both sat at frames
with q(k) = 0 at every proper-T height tested ((2,2,1): q(0) = q(1) = 0;
(3,1,2): T(1) = ∅), where the defect is structurally invisible; tooth
HE7-T-LIFT2SHARP checks the two fullness halves only.

**Failure scenario:** any future consumer that reads the exact-set clause at a
sub-threshold height — e.g. a deeper-order lift ledger enumerating reachable
residues below (D′−1)h — instantiates the wrong coset; at (2,2,3, k=3) every
realized residue lies outside the displayed set. **Landing sites:** HE6 §S1
(LEMMA HE6-1L) and, identically, frozen HE7 §S4.1 (LEMMA HE7-L1) — the HE7 copy
is a note-to-owner (append-only per its freeze), not a re-litigation: no HE7
pass adjudicated the sub-threshold exact-set clause.

### F-2 (GAP — machine-leg record): §S9's "runner-as-run" pin matches nothing; undisclosed post-run edit window; freeze anchor mis-stated

> Quoted (HE6 §S9): "runner-as-run `he6_checks.py` (959fff4052e9…)". Quoted
> (HE6 header [r1]): "The runner and artifacts of §S8/§S9 are BYTE-FROZEN at
> seal a77c376".

Git facts: he6_checks.py at seal a77c376 = af7009ecb005…; at close 1f5a417 and
at HEAD = 321fa4d4990e… (the seal→close diff is the WIP flip + 436 inserted
lines — the battery body); **no object in the repo has md5 959fff4052e9…**. The
committed runner's mtime (Aug 8 20:34) postdates the artifacts (20:25), so the
bytes that ran are unrecoverable from the repo. Separately, the header's freeze
anchor is wrong twice: the runner is NOT byte-identical to seal (WIP flip +
body), and the artifacts did not exist at seal — the true anchor is close
1f5a417 (verified: zero diffs 1f5a417 → HEAD on runner + both artifacts).

**Cure-in-fact executed by this pass:** isolated re-run of the committed runner
(sandbox /tmp/he6pe2_iso, md5 321fa4d verified before run) reproduces
`he6_checks_output.txt` **byte-identically modulo timing lines** and the
results json identically except `secs` fields — 72,315 GEN / 4,232 SEP /
2,226 SIG / 24 XI / 6 ORTH, 0 violations, 5/5 teeth, exit 0. So the committed
instrument generates the committed verdict; what remains defective is the
note's record sentence (a pin that fails every audit) and the missing
disclosure of the post-run edit. **Failure scenario:** an auditor verifying §S9
by hash alone rejects the leg at every commit; without this pass's re-run the
"0 violations" record rests on an unverifiable instrument identity.

### F-3 (MINOR, machine-confirmed): LEMMA HE6-0″'s twist direction is inverted (+q should be −q), and it contradicts HE6-1L's display

> Quoted (HE6 §S1, LEMMA HE6-0″ [r1, R5]): "the residue of the attaining class,
> read after division by ϖ(ξ)^{dv(A)}, is ι_ξ(γ)·η_ξ^{q}".

By the RIDER's own identity ϖ(θ)^k/n(k)(θ) = η_θ^{q}, division by ϖ^k
MULTIPLIES the n(k)-read residue by η^{−q}, so the display should read
ι_ξ(γ)·η_ξ^{−q}. Confirmed per-element at (2,2,3, k=3): C = x realizes 2y =
η^{−1} (leg B's CXRES), where the +q reading predicts η. Harmless to every use
this pass traced (only "fixed nonzero universal ι_ξ-transportable element" is
consumed — vanishing/degree/surjectivity statements are twist-direction-blind,
as the RIDER itself says), but the sign combines with F-1: HE6-0″ (twist
present, wrong sign) and HE6-1L (twist absent) are mutually inconsistent [r1]
displays of the same read.

### F-4 (MINOR): the fold's "verbatim" overstates — HE6-1L vs frozen HE7-L1 differ at 5 cosmetic points

Character diff (HE6 §S1 L113–126 vs HE7 §S4.1 L379–388): `ϖ(θ)^k` vs `ϖ(θ)^{k}`;
"which is ALL" vs "and it is ALL"; `{0,…,f₁−1}` vs `{0, …, f₁−1}`;
`(f₁−1))h` vs `(f₁−1))·h`; "…(D′−1)h**; if T(k) = ∅…" vs "…(D′−1)h**. If
T(k) = ∅…". The two display lines (the set and T(k)) are byte-identical, and
the mathematical content is identical, but both the recon R3 row and HE7's fold
box say "verbatim" — false at the byte level. **No post-freeze drift on the HE6
side** (the note is untouched since 850e77e), so the daylight is original to the
r1 landing, not drift. Failure scenario: a future byte-diff audit of the
interface flags the fold as broken and cannot tell drift from landing noise.

### F-5 (MINOR): §S7.2's (LIFT₂) display retains the universal form HE7 proved false below threshold

> Quoted (HE6 §S7.2): "**(LIFT₂)** for every level-2 height k ∈ ℤ and every
> c ∈ K₂^× there is C ∈ O[x] …"

HE7 §S4.2 proves (LIFT₂) under (†₂)/(‡₂) and shows the sub-threshold failure is
genuine; HE6's §S7.2 wish-list display keeps the unconditional quantifier, cured
only by the [r1] STATUS box's pointer ("with the level-1 (LIFT) threshold
corrected — the same defect as R3") — the level-2 threshold is implied, not
displayed. Not consumed (the box's "This note does not prove (LIFT₂)/(SLOT₂)"
keeps it honest); a reader taking §S7.2's display as HE7's statement would
re-import the R3-class defect one level up.

---

## S2. CLEAN CHARGES (what was attacked and held)

1. **HE6.B [r1] vs the recon's literal-instance theorem — NO DAYLIGHT.** The
   widened-box wording (HE6 §S1/§S7.1 vs recon §S2) agrees in content; the
   per-factor keying ("a repeated irreducible factor that is not K-rational
   linear at integer slope") was interrogated at MIXED residuals (e.g.
   (Z−s)²(Z−s₁)(Z−s₂) at ℓ = 1, first live μ = 4/n = 8): covered — HE3 §S6.3's
   stage-α step explicitly leaves coexisting labels untouched and recurses at
   the recentered key, where the remaining residual is separable and HE6.A
   applies; the "exactly the complement" sentence survives. The n ≤ 7 rider's
   inequality (L_λ ≥ 4, D′ ≥ 2 ⟹ n ≥ 8) re-derived; base-level (D′ = 1)
   repeated residuals are genre openings, not HE6.B "sides".
2. **R1–R9 applications, one by one.** R1 applied (box widened, §S7.1 [r1]);
   R2 applied AND the peel verified sound at a depth PE1 did not reach: f =
   Φ′·f̃ gives the exact development shift A_{j+1} = Ã_j, so f̃ inherits the
   locus entry bounds (positive slopes included) and "every statement below is
   applied to f̃" is legitimate; R4's ψ-cancellation proof verified complete
   (equality slots exactly i ≡ 0 mod e₁ via gcd(h,e₁) = 1; the residual is
   monic of degree f₁ vanishing at η_θ, hence = ψ; both remaining HE6-0 cases
   disposed with no proximity claim); R5 applied (modulo F-3's sign); R6/R7/R8
   applied as recorded (R8's "below" rider covers §S4's displays); R9's GENHN
   erratum annex present at GENHN_PROOF L506/L535 with the corrected node
   {dv(A_j) ≥ (μ−j)D′h + 1}.
3. **HE6.A's proof core post-r1 (attack 2) — holds at the ℓ ≥ 2 configurations
   examined, with no reliance on battery geography found.** Re-derived: the (†)
   gap-sampling elimination (Σ_{i>j}c_i = 0 per gap ⟹ triangular, c₀ = 0 on
   (D′h, λ₁); the λ = 0 corner the "all slopes are > 0" aside leaves is closed
   by the total count Σ_λ n_λ = D′μ, and on the locus by the entry bounds);
   HE6-4's strictness transfer incl. shared-root extended values; the sandwich
   steps 1–4 (orbit ≥ N_r; e·f = [L:K₀] valid over complete DVR with finite
   residue field); ι_ξ-transport of ϖ-read residues is exact BECAUSE the twist
   is an η-power — F-1/F-3 are invisible to it; ℓ-uniformity spot-checked at
   (ℓ−1)D′+1 > 0 and the j ≡ j₁ (mod ℓ) congruence. Fresh leg A corroborates
   OUTSIDE every battery: ℓ = 3 (see S3).
4. **HE6-3(a)'s c₀ = 0 elimination (attack 4, Codex's item 3)** — premises now
   supplied by R2 (label exhaustiveness) + R4 (the positive direction); the
   elimination re-derived sound; (RES) finiteness at HE6-3 via the degree-μ+1
   letter (no shared root possible).
5. **Interface (attack 3):** HE6_PROOF untouched since 850e77e (git) — no
   post-freeze drift on the HE6 side; the display lines of HE6-1L and HE7-L1
   byte-identical (residual daylight = F-4's five cosmetic points).
6. **Machine-leg tautology audit:** Q1/Q2's two sides are independent (exact
   Sylvester–Bareiss resultant over ℤ / F_p[t] vs the polygon support function
   ℓd_rD′h_F(κ) from the reader's dvs); the reader's labels feed only the
   flat/excess dichotomy and are cross-checked BOTH ways (flat at a true label
   would violate GEN; missing excess violates SEP); §S9's totals equal the
   committed json field-for-field; teeth PLANT/FLIP/BADKEY/UNDET2/CASEB re-fired
   in the isolated re-run.

---

## S3. MACHINE + FRESH-ROUTE LEGS (this pass's instruments)

**Isolated re-runs (sandbox /tmp/he6pe2_iso, md5s of runners verified = HEAD
before run):**
* `he6_checks.py` (321fa4d…): exit 0, **0 violations**, legs 72,315/4,232/
  2,226/24/6, 5/5 teeth; output byte-identical to the committed artifact modulo
  timing; json identical except `secs`. (This is F-2's cure-in-fact.)
* `he6r1_checks.py --full` (7112f7c…): exit 0, rows identical except per-row
  `secs` (677/682 PARI agreements, 0 mis-decisions, 5 Ψ|f_S non-decisions
  preserved); import pins in the artifact match HEAD md5s.
* `he6r1_supp.py`: exit 0, json identical except `secs` (peel 12/12, 5/5 PARI).

**Fresh route (`verification/openmath/he6_pe2_fresh.py` + output + json, this
pass; 5.4 s):**
* **Leg A — the ℓ = 3 side family (first ℓ = 3 LABEL battery of this unit's
  arc; the sealed batteries carried ℓ ∈ {1,2} labels only, ℓ′ = 3 appearing
  only as flat sample heights):** (e₁,f₁,h) = (2,1,1), Φ′ = x²−5 over ℤ₅,
  μ = 6, deg f = 12, λ = 7/3. **39/39 PARI σ match THEOREM HE6.A's dictionary**
  (SPLIT (Z−1)(Z−2) and (Z−1)(Z−4): 13/13 each {(6,1),(6,1)}; INERT Z²+2:
  13/13 {(6,2)}), invariant over 12 above-line perturbations per config;
  flat identity 2v₅(Res(f,Ψ_{7/3,Z−s})) = 84 EXACT at non-label letters,
  strict excess at each label, height read 2v₅(Res(Φ′,Ψ)) = 14 = 6·(7/3).
* **Leg B — the F-1/F-3 certificate (fractional-height key at f₁ = 2, the
  charge's named candidate):** frame and numbers as in F-1/F-3 above; also
  k = 9 = (D′−1)h: realized set = **8/8 of F₉^×** (the fullness clause
  survives the twist), and the frame checks (single prime, (e,f) = (2,2),
  η² = −1 ∉ F₃) all pass. 0 violations of this pass's preregistered FB-P1/2/3.
* **Coverage disclosures:** the non-prime-q candidate was NOT run (PARI
  `factorpadic` is ℚ_p-only; a q = p^k leg needs an unramified-base oracle this
  pass did not build); leg A is char-0 only; leg B is a display-refutation leg,
  not a σ leg.

---

## S4. GRADE LINE

**NOT CLEAN under the charge bar (2 findings at GAP survive: F-1, F-2).
HE6-BOX-2 counter stays 0/2** — the r1 text owes a repair round (queue: the
η^{−q(k)} coset factor in LEMMA HE6-1L's set display — same fix owed as an
append on frozen HE7 §S4.1; HE6-0″'s sign; §S9's runner-as-run pin corrected to
the committed 321fa4d… with the post-run edit disclosed, and the header freeze
anchor moved to close 1f5a417; the two "verbatim" sentences softened to
"content-identical (display lines byte-identical)"; §S7.2's (LIFT₂) display
gains its threshold) — then a fresh hostile pass. No CRITICAL: THEOREM HE6.A,
COROLLARY HE6.B [r1], and the reconciliation's composition claims all SURVIVED
this pass's attacks, including a fresh ℓ = 3 oracle leg and the mixed-residual
interrogation of the widened box's "exactly" sentence.

*Verifier: Fable (fresh context, zero prior stake), 2026-08-09. Artifacts of
this pass: `verification/openmath/he6_pe2_fresh.py`,
`he6_pe2_fresh_output.txt`, `he6_pe2_fresh_results.json`; isolated-re-run
sandbox /tmp/he6pe2_iso (ephemeral; md5 comparisons recorded above).*
