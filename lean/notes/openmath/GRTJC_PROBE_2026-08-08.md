# GRTJC PROBE — the J-C carry-algebra instrument (W-6..W-9): sealed preregistration + verdict

**Unit:** GRTJC INSTRUMENT (Phase 0 of `docs/in-progress/GRTJC_BRIEF_2026-08-05.md`,
the examples-first directive of 2026-08-05). **Genre: sealed machine probe** —
instance evidence only; nothing here is a proof step; no `.lean` touched; no gate
fired; no acceptance arc opened; **BLOCKED-ON-CARRIER-TIE stands**. The unit
MEASURES, it does not compose: it does not assert (J-C), does not discharge any
of OB-1..OB-6, and makes no claim about gr(w) beyond what the printed tables say
about the instances in its roster. **Author:** Fable instrument unit, campaign
date 2026-08-08 (wallclock 2026-08-05).

**Runner:** `verification/openmath/grt_jc_probe.py` (deterministic, exact
arithmetic, no randomness). The runner's docstring carries the FULL
preregistration — roster, per-leg sealed predictions, the two certifiers, the
independence argument, and the build-phase smoke disclosure — and **that
docstring is part of this seal**. Artifacts:
`grt_jc_probe_output.txt`, `grt_jc_probe_results.json`.

---

## S1. What is under measurement (blueprint S2.3, verbatim target)

> **(J-C)(ii)** for every level m with E_{m+1} := e₀⋯e_m > 1: the fibred carrier
> (⊕_{γ ∈ ℤ/E_{m+1}} K_{m+1}·u_γ, u_γu_{γ′} = c_{m+1}(γ,γ′)u_{γ+γ′}) built from
> the canonical D(T)/c_T of GRT-1 is isomorphic, via u_γ ↦ [φ_γ]_{TC} through
> TC-1 (localize) / TC-2 (gauge p ↦ 1) / TC-3 (residue quotient), to the
> K_{m+1}-span 𝒜(T) of the anchor classes in the degree-0 component of the actual
> graded ring gr(w_{m+1}) — with 𝒜(T)'s multiplication gr's OWN, never c_T (the
> tautology fence).

The obligation package is GRW2_TIE_DESIGN §S2.2's OB-1..OB-6. This probe puts a
measurement on each of OB-2, OB-3, OB-4, OB-6 and on the two fences (cyclic,
tautology); **OB-1's legitimacy and OB-6's carrier identification are
structurally unfalsifiable by sampling** (design note S2.2's own honesty clause)
— what is measured here is their arithmetic shadow, and §S5 lists exactly what is
NOT reached.

## S2. The indexing identity that makes the roster finite (P0-TRUNC)

The level-(m+1) analysis of a tower is the FULL top-level analysis of the tower
truncated to reads 0..m. A probe row is therefore a truncated tower T with
NR := m+1 reads, and E := e₀⋯e_{NR−1} = E_{m+1}, K := K[NR] = K_{m+1},
w := wlev(NR,·) = w_{m+1}, φ_γ := tanch(γ, NR−1) = π^{u₁}Φ₀^{s₁}⋯Φ_{NR−1}^{s_NR},
Φ_top := Φ_{NR} = the classifier's NEXT key. Legitimacy of the truncation
(Φ₀..Φ_{NR−1} do not depend on reads above NR−1) is not assumed — it is
machine-checked byte-for-byte at every truncation depth (family P0-TRUNC).

## S3. THE TAUTOLOGY FENCE — how independence is achieved (OB-5)

**The gr-side structure constant is the unique solution of a weight inequality in
O[x], and its decision procedure calls exactly four primitives:**

1. `PolyO.mul` / `PolyO.sub` / `PolyO.divmod_monic` — schoolbook polynomial
   arithmetic in O[x] (no residues, no reads);
2. `Tower.wlev(NR,·)` — the MacLane weight w_{m+1}, by iterated
   Φ-development (polynomial division + min);
3. `Tower.realize(NR, c, N)` — the graded SCALAR LIFT: a pure construction
   (iterated eq-(12) splits, ε z-powers, Φ/π-power products). It calls no
   residual read and no cocycle;
4. `Φ_top = Φ_{NR}` — the classifier's own next key (this is TC-3).

`Tower.constants` (the [ILN]† closed form c_T = z̄^δ∏_j z_j^{D_j}) and
`Tower.read` (the harness val) are **never called inside the determination or the
certification**. They enter only as the quantities COMPARED against (P2-ISO,
P2-VAL, P5-OB6). Three further guards:

* **No witness at all on the exhaustive rows.** When |K| ≤ 512 the constant is
  found by exhaustive search over K, and its UNIQUENESS is proved on those rows
  (the count of certifying scalars must be exactly 1). Above the cap a
  read-proposed witness is certified by the fence-clean procedure and uniqueness
  is sampled against a designated wrong-scalar set — a witness is not an
  assumption, and the certifier is the scoring criterion.
* **MT3, the tautology tooth.** One anchor is rescaled by a nontrivial scalar
  class; the fence-clean certifier must report constants disagreeing with c_T,
  while the c_T-defined "check" reports 0 violations by construction. Both
  numbers are printed, so the discriminating power is exhibited rather than
  asserted.
* **MT1/MT4** plant a wrong letter in the normalization and a wrong letter inside
  the scalar lift; both must be caught.

**The two certifiers** (both reported; their DIFFERENCE is the instrument's main
structural measurement):

    RAW (pre-TC-3, pure gr(w_{m+1})):
        w( φ_a φ_b X_N − Λ_N(c)·φ_{a+b} ) > a+b+N
    TC3 (post-TC-3; the ψ-quotient operationalized by division by Φ_{NR}):
        ∃ k ∈ [0,4]:
        w( (π^k(φ_aφ_b X_N − Λ_N(c)φ_{a+b})) mod Φ_{NR} ) > kE + a+b+N

with X_N := Λ_N(1), Λ_N(c) := realize(NR,c,N), N a multiple of E with
N ≥ wΦ[NR] (so s_NR(N) = 0 and multiplication by X_N is carry-free).
**Soundness of TC3:** the tested remainder R obeys π^kD = QΦ_{NR} + R, so
w(R) > kE + target forces in(π^kD) into the graded ideal generated by
in(Φ_{NR}) — D dies in the TC-3 quotient. **One-sidedness, disclosed:** only the
canonical quotient Q is tried, so a TC3 failure is not a proof of
non-membership; the π^k ladder widens the search and the observed k-distribution
is reported (it quantifies how much of TC-1's localization the identification
consumes).

**Why the offset N is structurally necessary (a measured fact, not a
convenience).** There is no weight-0 lift of a general scalar: at weight 0 the
level-NR read has a single available grid slot, so gr₀(w) realizes only K₀ =
F_{p^{d₀}}, never K_{m+1}. The scalars appear only after TC-1/TC-2 identify the
ℤ/E-component of 0 with gr_{kE} for k ≫ 0 — which is exactly why OB-1 is an
obligation and not a relabeling. The runner's Λ_N/X_N construction is that
identification made concrete, and P0-LIFT/P0-SCAL measure its defining laws.

## S4. SEALED PREDICTIONS (commit 1; battery NOT yet run)

Compressed from the runner docstring (which is the authoritative seal).

| leg | sealed identity | predicted |
|---|---|---|
| EXT-GATE | engine_ext `install()` + `check_pins()` + `agreement_gate()` re-run (standing rule, mandatory in-unit) | 0 violations |
| P0-TRUNC | truncation identity: Φ_j byte-identical at every truncation depth | 0 |
| P0-ANCH | w(φ_γ) = γ on every representative | 0 |
| P0-OB2 | **OB-2/COR-4 exactly**: φ_{γ+E} == π·φ_γ BYTE-for-byte | 0 |
| P0-LIFT | w(Λ_N(c)) = N and read(N, Λ_N(c)) = c for every c ∈ K | 0 |
| P0-SCAL | gr-side scalar multiplicativity ([Λ(c)Λ(c′)] = [Λ(cc′)X_N]) by polynomial arithmetic + w only | 0 (additivity of the O-digit lift is MEASURED-ONLY, never RED) |
| P2-OFF | offset-independence of the STRUCTURE CONSTANTS (the well-posed OB-1 offset clause): c_gr recomputed with the scalar home at N+E equals c_gr at N | 0. **Disclosed (build-phase, measured):** the naive CLASS identity [π·Λ_N(c)] = [Λ_{N+E}(c)] is FALSE — two weight-(N+E) lifts with the same read need not be the same class, since the level-NR read is not injective on a graded piece. *That non-injectivity IS TC-3's ψ-kernel*, so the offset clause is stated on the constants, which is what the carrier iso needs |
| P0-PSI | the J-B germ letter: ψ_{m,0} = −z̄ in K_{m+1}, re-verified per stage | 0 |
| **P1-RAW** | **SET IDENTITY**: {pairs with no RAW-certifying scalar} == {pairs with **δ ≥ g_m**}, g_m = deg ψ_m. Rationale: Λ_N realizes c = Σ_{i<g_m} c_i z̄^i by placing c_i at grid slot i, so a slot shift by δ < g_m is ALREADY a scalar; δ ≥ g_m needs the ψ-relation, i.e. TC-3 | **0 set-mismatches** (the count itself is measured and is nonzero on the g_m = 1 stages) |
| P1-TC3 | every scored pair has a TC3-certifying scalar, unique | 0 |
| **P2-ISO** | **THE CARRIER ISO on the nose**: c_gr == c_T = z̄^δ∏_{j≤m} z_j^{D_j} per (γ,γ′), on the scored stratum (D integral ∧ off DCX) | **0** |
| P2-REP | representative-independence: c_gr at the minimal in-window reps == c_gr at the uniform base | 0 |
| P2-VAL | baseline (accepted ITER-LAW): c_val == c_T | 0 |
| P3-FACT | c_gr == outer·inner with outer = z̄^δ, inner = ∏_{j≤m} z_j^{D_j}; inner-value census | 0 violations of the scored clause |
| P3-READ | rival readings H-B (inner dropped), H-C ((−z̄)^δ·inner), **H-D (inner letters replaced by the germ letter −z_{m+1})** | each shows ≥ 1 failure; H-D's failure count is the adjudication of the germ hypothesis AS AN INNER-FACTOR claim |
| P3-GERM | (a) val(Ĉ_m) == −z̄ ; (b) κ·val(φ_{e_mγ_{m+1}}) == −z̄ where κ is the TC3-certified class constant of the correction digit; (c) germ transport c_germ(r) == κ·c_T(e_mγ_{m+1}, γ_r) | 0 each |
| P4-DEG | γ ↦ w(φ_γ) mod E is a bijection ℤ/E → ℤ/E (the fibred independence content of OB-4) | 0 |
| P4-SPAN-M (scored) | the rank-ONE content: for each class r, perturb the anchor's own exponent vector at one level (s_{j+1} → s_{j+1} + e_j, compensated in the π-power) — a genuine non-anchor monomial of the same weight; does a TC3-certifying scalar exist? Classes that DIE in the TC-3 quotient (only c = 0 certifies) are counted separately, not as failures | 0 failures; every failure tabulated as a GENRE row |
| P4-SPAN-S (census, never RED) | weight-matched sums A + B, A = X_Nφ_{γ_r}, B = π^tφ_aφ_b. B carries no X_N factor, so its class relates to the anchor only through a different scalar offset — a failure here is NOT evidence about OB-4. Smoke found 2 such rows (C2A r=2 (1,1); C3A r=6 (1,5)); disclosed, printed, unscored | measured |
| P5-OB6 | harness-val == TC-read: c_gr == c_val on the scored stratum | 0 |
| MT1 | wrong letter (inner letters → top letter) must FAIL certification on every designated pair | 0 misses |
| MT2 | **the cyclic fence (LAW)**: (CYC) adjudication (image(c_gr) ⊆ {1, ζ′} AND a relabeling σ with σ_r + σ_s = σ_{r+s} + E·carry) on the MEASURED c_gr table. Designation fixed structurally before the run: `CYC_DESIGNATED` = the g_m = 2 rows **C2I / C3I / C4I**, where K_{m+1} = K_m[z̄] is a genuine degree-2 residual extension so z̄ ∉ ⟨z₁⟩ | ≥ 1 designated row NOT-CYCLIC (the tooth must fire). Every verdict RECORDED; CYCLIC on twist-blind rows (|K| = 2, or g_m = 1 collapsing K_{m+1} = K_m) and on the e_j = 1 flat controls is the D-REAL last-read geography, NOT RED. A CYCLIC verdict on a designated g_m = 2 row is a notable finding, reported. Relabeling search skipped (UNDECIDED, recorded) at E > 8 |
| MT3 | tautology tooth: fence-clean certifier catches a rescaled anchor; c_T-defined check does not (both counts printed) | ≥ 1 catch per designated stage |
| MT4 | garbled scalar lift Λ′(c) = Λ_N(c·z₁) must break certification of the true constant | 0 misses |

**Roster (29 rows).** (constructed tower, level m) with NR = m+1 reads, spanning
m ∈ {1,2,3} (10/10/9 rows), p ∈ {2,3,5}, d₀ ∈ {1,2,3}, mixed (e_j) with
E_{m+1} > 1 on every scored row, wild legs e_j = p, g_j = 2 branching rows (a
genuine degree-2 residual extension — z̄ ∉ ⟨z₁⟩, the strata-probe row-N
discriminator design), e_j = 1 flat rows ([RMG]'s fenced-corner genre and the
D-REAL cyclic controls), the strata NOT-CYCLIC roster's genres (its
C/D/E/H/J/K/L/M/N shapes), and the three committed ITERLAWN 4-read instances
I4A/I4B/I4C verbatim. Base rings ℤ_p and F_p[[t]]. Pair grid: all E² ordered
pairs when E ≤ 6, else a deterministic designed subset (diagonal + low pairs +
the carry boundary r+s ∈ {E−1,E,E+1}) capped at 24.

**Build-phase smoke disclosure (pre-seal, honest; part of the record).** Three
reduced probes ran during construction: (i) a primitive smoke on one row —
`realize` at m = NR works with `check=False`, the lift's w/read laws are exact
for every c ∈ K, anchors satisfy w(φ_γ) = γ, and the exhaustive certifier
returns a UNIQUE scalar equal to c_T = c_val on a δ = 0 pair; (ii) a 4-row RAW
smoke — RAW returns ZERO certifying scalars on exactly the δ = 1 pairs (4/16,
5–6/20, 4/20) and a unique correct scalar elsewhere; **this is what fixed
P1-RAW's sealed prediction to a SET IDENTITY with a nonzero count instead of 0**;
(iii) a 4-row TC3 smoke — 0 certification failures, 0 non-unique, k-distribution
{0: all}, and c_gr == c_T on every pair including the δ = 1 pairs; (iv) a 3-row
FULL-battery smoke of the sealed runner (C2A/C2I/C3A) which produced three
pre-seal corrections, all applied before the seal: **(a)** P1-RAW's set identity
sharpened from {δ ≥ 1} to {δ ≥ g_m} (C2I has g_m = 2 and RAW succeeded on its
δ = 1 pairs); **(b)** c = 0 admitted as a certifying scalar in the SPAN legs (a
class may die in the TC-3 quotient); **(c)** SPAN split into the scored monomial
family SPAN-M and the unscored SPAN-S census. That smoke also showed 0
violations in every other family, MT3 firing on 21/21 pairs, MT1/MT4 0 misses,
H-B failing on 10 of 56 scored pairs and H-D on 4, and val(Ĉ_m) = −z̄ with
κ = 1 on both eligible rows. The sealed predictions are the brief's identities,
NOT sanitized to the smoke.

## S5. What this instrument does NOT reach (fixed at seal time)

* **OB-1's legitimacy** (localization/gauge as ring-level operations at a
  composite stage) — structurally unfalsifiable by sampling; only its arithmetic
  shadow (P0-LIFT/P0-SCAL/the necessity of the offset N) is measured.
* **OB-6's carrier identification** — only its scalar shadow (P5) is measured;
  the R_{m+1}/w_{m+1} carrier layer (PROJECT_STATE standing obligation 2) is
  untouched.
* **The Δ-rank refinement of OB-4** (freeness of gr_γ over Δ = K_m[y] BEFORE
  TC-3) — explicitly NOT measured. What is measured is the fibred independence
  (degree separation mod E) and the post-TC-3 spanning (P4-SPAN).
* **Completeness of the TC3 certifier** — one-sided (canonical quotient only).
* Instance evidence only: orders ≤ 4, residue fields ≤ F₂₅/F₈, g_j ≤ 2,
  d₀ ≤ 3, no PARI leg (no new lift construction is claimed here), F_p[[t]] rows
  ride construction-identity + machine only.
* No proof step, no gr/carrier CLAIM, no density (J-D) statement, no gate;
  the P0 application gate and BLOCKED-ON-CARRIER-TIE stand.

---

## S6. VERDICT (commit 2 — written FROM the artifacts)

**Artifacts:** `verification/openmath/grt_jc_probe_output.txt`,
`grt_jc_probe_results.json` (deterministic; 29 rows, 669 scored pairs, 18.3 s;
seal commit `7212e56`). **ALL 22 SCORED FAMILIES GREEN — 0 violations, every
sealed prediction hit exactly.**

**All 29 rows ran EXHAUSTIVE** (|K| ≤ 512 on every row: |K| ∈ {2,3,4,5,8,9,16,25}).
So on every one of the 669 pairs the gr-side structure constant was determined by
exhaustive search over K with **no witness input from the harness side at all**,
and its **uniqueness is machine-proved** (exactly one certifying scalar per pair).
The π-clearing ladder was never needed: **k-distribution {0: 669}** — the
canonical division by Φ_{NR} alone discharges TC-3 on this roster.

| leg | sealed | observed | verdict |
|---|---|---|---|
| EXT-GATE | 0 | 0 (pins + agreement gate re-run, 0 new) | GREEN |
| P0-TRUNC | 0 | **0 / 151** | GREEN (the truncation identity holds byte-for-byte at every depth) |
| P0-ANCH | 0 | 0 / 285 | GREEN |
| P0-OB2 | 0 | **0 / 285** | GREEN — φ_{γ+E} == π·φ_γ **byte-for-byte** on every anchor of every row (OB-2/COR-4 exact) |
| P0-LIFT | 0 | 0 / 138 | GREEN |
| P0-SCAL | 0 | 0 / 293 | GREEN (scalar multiplicativity in gr); additivity census: **0 non-additive samples** |
| P0-PSI | 0 | 0 / 29 | GREEN (ψ_{m,0} = −z̄ per stage) |
| **P1-RAW** | set identity, count nonzero | **134 of 669 pairs have NO pre-TC-3 scalar; 0 / 29 set-mismatches** | GREEN — the set is EXACTLY {δ ≥ g_m} on all 29 rows |
| P1-TC3 | 0 | **0 / 669** (0 no-solution, 0 non-unique) | GREEN |
| **P2-ISO** | 0 | **0 / 669** | GREEN — c_gr == c_T = z̄^δ∏_{j≤m} z_j^{D_j} **on the nose, per pair** |
| P2-OFF | 0 | 0 / 116 | GREEN (constants independent of the scalar offset) |
| P2-REP | 0 | 0 / 174 | GREEN (representative-independent) |
| P2-VAL | 0 | 0 / 669 | GREEN (accepted ITER-LAW re-confirmed on this roster) |
| P3-FACT | 0 | 0 / 669 | GREEN |
| P3-GERM | 0 | **0 / 188** | GREEN (see the germ verdict below) |
| P4-DEG | 0 | 0 / 29 | GREEN |
| P4-SPAN-M | 0 failures | **328 certified / 0 zero-class / 0 FAILED** (606 skipped for non-integrality) | GREEN — **0 genre rows**: the anchor generates over K_{m+1} for every monomial perturbation tested |
| P5-OB6 | 0 | **0 / 669** | GREEN — harness-val == TC-read per pair |
| MT1 | 0 misses | 0 / 79 designated pairs | GREEN (tooth fires) |
| MT2 | ≥ 1 designated NOT-CYCLIC | **C2I NOT-CYCLIC, C3I NOT-CYCLIC**, C4I UNDECIDED (E = 16 > 8) | GREEN (tooth fires) |
| MT3 | ≥ 1 catch per stage | **197 / 206 pairs caught; ≥ 1 catch on all 28 non-skipped rows** | GREEN (tooth fires) |
| MT4 | 0 misses | 0 / 557 | GREEN (tooth fires) |

Scope census: **DCX pairs 0, non-integral-D pairs 0** — the entire grid sat inside
[ILN]†'s own scored stratum, so no pair was excluded from P2-ISO/P2-VAL/P5-OB6.

### S6.1 THE FIVE MEASUREMENTS THE COMPOSER SHOULD BUILD ON

**(M1) The carrier iso holds on the nose, and its gr-side is fence-clean.**
c_gr == c_T on 669/669 pairs across m ∈ {1,2,3}, p ∈ {2,3,5}, d₀ ∈ {1,2,3}, wild
and flat legs, g_j = 2 rows, and the three committed ITERLAWN instances — with the
gr-side constant determined by exhaustive certification that never calls c_T or
the read. Uniqueness machine-proved on every pair. This is OB-3's scalar content
and OB-2 (byte-exact) measured, not assumed.

**(M2) TC-3 IS LOAD-BEARING, AND EXACTLY WHERE.** The pre-TC-3 certifier fails on
134/669 pairs, and the failure set is EXACTLY {δ ≥ g_m} on all 29 rows (0
set-mismatches). Mechanism, now machine-located: the scalar lift Λ_N already
realizes slot shifts up to y^{g_m−1} (that is what c = Σ_{i<g_m} c_i z̄^i *is*), so
a carry of δ < g_m is a scalar for free; a carry of δ ≥ g_m needs the ψ-relation,
i.e. the TC-3 quotient. **Consequence for the composer: the OUTER factor z̄^δ of
c_T is precisely the TC-3 image of the graded slot shift y^δ — not a coordinate
artifact, and not obtainable from TC-1/TC-2 alone.** Corollary measured on the
way: the level-NR read is NOT injective on a graded piece (two weight-(N+E) lifts
with equal read can be different classes), and that non-injectivity IS TC-3's
ψ-kernel — so any draft that treats TC-3 as a relabeling is refuted here.

**(M3) THE GERM VERDICT — measured factor vs −z_{m+1}, adjudicated in two parts.**
CONFIRMED where J-B put it: on all **27 eligible stages** (g_m = 1),
**val(Ĉ_m) = −z̄ = −z_{m+1} exactly** — the germ letter is the correction digit's
own anchor value, machine-verified independently per stage. And the carrier-side
class constant κ of multiplication by [Ĉ_m] satisfies
**κ · val(φ_{e_mγ_{m+1}}) = −z_{m+1} on all 27 stages** (0 violations), with κ
itself varying across stages (measured values: 1, z̄, z̄², z̄³, z̄⁴). **So the
measured factor is −z_{m+1} divided by the anchor's own value normalization, not
−z_{m+1} bare** — κ = −z_{m+1} only on the stages where val(φ_{e_mγ_{m+1}}) = 1.
Germ transport c_germ(r) = κ·c_T(e_mγ_{m+1}, γ_r): 0 violations on every scored r.
**REFUTED as an inner-factor claim:** the brief's literal working hypothesis
("the inner normalization factor at general m is −z_{m+1}") is reading H-D, and
H-D FAILS on **138 of 669** scored pairs. The measured inner factor is
∏_{j=1}^{m} z_j^{D_j} — the INNER letters z₁..z_m, not the top letter — nontrivial
on **215 of 669** pairs (and H-B, which drops it, fails on exactly those 215: the
inner factor is load-bearing pair-for-pair, never absorbable). The germ-signed
outer reading H-C also fails (73/669). **The composer must NOT assume the germ
letter is OB-3's inner normalization; the two are different quantities, and the
instrument separates them.**

**(M4) OB-4 splits, and the hard half is not independence.** In the fibred
presentation the independence content reduces to degree separation mod E, which is
GREEN on all 29 rows (P4-DEG); the content that could actually drop is spanning,
and the monomial rank-one probe certifies 328/328 with **zero genre rows**. So
the composer's case split gets **no genre from OB-4 on this roster** — budget the
effort at OB-1 (which sampling cannot reach) instead. Two honest riders: the
Δ-rank refinement (freeness over K_m[y] BEFORE TC-3) is NOT measured, and the
SPAN-S sum census contributed 60 **zero-class** samples (classes that die in the
TC-3 quotient) with 0 unexplained — the two smoke "failures" were exactly such
zero-classes, which is why c = 0 was admitted.

**(M5) The cyclic fence is a GENRE, not a universal — with the split reproduced
independently.** On the measured c_gr tables: **14 NOT-CYCLIC / 6 CYCLIC / 9
UNDECIDED** (relabeling search skipped at E > 8). The 6 CYCLIC rows are
C2A/C2E/C2G/C2J/C3A/C4A — the twist-blind and collapse geography (|K| = 2, or
g_m = 1 collapsing K_{m+1} = K_m so z̄ ∈ ⟨z₁⟩, or the e₀ = 1 flat control) —
and this 6-cyclic / rest-not-cyclic split **independently reproduces the strata
probe's byte-frozen 22/28 NOT-CYCLIC adjudication** from a completely different
computation (gr-side certification vs harness value cocycle). Both designated
g_m = 2 rows that were decidable came back NOT-CYCLIC. **Consequence: the
composer's case split MUST carry a cyclic/non-cyclic genre column, and the cyclic
side is not only the last-read layer — it includes composite stages whose residue
tower collapses (g_m = 1 ⇒ K_{m+1} = K_m).**

### S6.2 Honest reporting of the imperfect and the unmeasured

* **MT3's 9 escapes.** 197 of 206 tautology-tooth pairs were caught; exactly one
  pair escapes on each of 9 rows (C2C/C2F/C2J/C3B/C3C/C3G/C3J/C4C/C4H — all
  prime-residue-field rows, |K| ∈ {3,5}), where the planted rescaling coincides
  with a lawful constant. The sealed criterion (≥ 1 catch per stage) held on all
  28 non-skipped rows; C4A (|K| = 2) has no nontrivial scalar class and is
  skipped, disclosed.
* **The inner-factor value names** printed in the tables (z̄^1 ×143, z̄^2 ×24,
  z̄^3 ×15, z̄^4 ×14, z̄^5 ×10, z̄^7 ×6, z̄^6 ×3) come from a printer that tries
  z̄ before z₁: on g_m = 1 rows K_{m+1} = K_m, so an inner ∏z_j^{D_j} can *equal*
  a z̄-power numerically. The **structural** statement is the scored one
  (c_gr == outer·inner with inner = ∏_{j≤m} z_j^{D_j}, 0 violations); the value
  names are a display convenience, not a claim that the inner factor is a z̄-power.
* **MT2's aggregate check runs after the family table is printed** (a cosmetic
  ordering artifact of the runner); its result lives in the JSON key
  `cyc_designated` and in the printed per-row CYCLIC table.
* **9 rows UNDECIDED for MT2** (E > 8, relabeling search skipped) — a stated
  compute fence, not a finding.
* Everything in §S5 remains unmeasured: OB-1's legitimacy, OB-6's carrier
  identification, the Δ-rank refinement, and the TC3 certifier's completeness
  (canonical quotient only — though with k = 0 sufficing on 669/669 pairs the
  ladder was never even exercised).
* **No proof step, no gr/carrier claim, no gate, no density statement.** The P0
  application gate and BLOCKED-ON-CARRIER-TIE stand.

— GRTJC INSTRUMENT unit, campaign date 2026-08-08.
