# HE6 passPE3 — FABLE HOSTILE VERIFIER (fresh context) on the r2 text at HEAD

**VERDICT: CLEAN — 0 CRITICAL / 0 GAP / 0 MINOR on the target. Grade 0/2 → 1/2.**

**Target:** `HE6_PROOF_2026-08-08.md` + `HE6R1_RECON_2026-08-08.md` at HEAD
(r2 = 8797a34/9bdfbb5/cec49ba/d1b0bc8; git-verified: the four commits are the
only post-PE2 touches of the two files). Arc: seal a77c376 → close 1f5a417 →
Codex PE1 06f55f0 → r1 850e77e → PE2 404dae1 (0C+2G+3m) → r2 → **this pass**.
Protocol: quote-and-classify, fix nothing. Attack order as charged: (1) the r2
coset display re-derived + q(k) well-definedness at every corner examined +
3-of-8 non-propagation routes at their consumption sites, (2) the HE6-0″ sign
reconciliation, (3) the §S9 record repair's four facts re-verified
independently, (4) HE6.A's core at a configuration no pass constructed
(f₁ = 3), (5) free hunt across r1+r2. Fresh route: three legs disjoint from
the seal battery, he6r1's 682, HE7's legs, and PE2's two legs.

---

## S1. FINDINGS

**None on the target survive this pass's verification** (no CRITICAL, no GAP,
no MINOR). Two out-of-scope observations, both HE7-side and both already
disclosed as HE7-side residue by the target text, recorded for HE7's queue:

* (obs-1, HE7 append, commit 5da0552 body L2516): the appended definition
  line reads `η_θ^{q(k)} := ϖ(θ)^k/n(k)(θ)` without `res(·)` — element/residue
  conflation (HE6-1L's own display, L139, has the `res`); and the appended
  coset display places η_θ^{−q(k)} inside the braces where HE6-1L [r2] places
  it outside (mathematically identical; byte-different). Not a target defect:
  the HE6 [r2] correction record claims of the append only "the coset display,
  the same (2,2,3) witness, the four-site enumeration, prefix md5 0698155b" —
  each verified true this pass.
* (obs-2): HE7's fold-box "verbatim" sentence remains unsoftened — already
  named as an HE7-side residue in the recon R3 row [r2] and in d1b0bc8.

---

## S2. CLEAN CHARGES (what was attacked and held)

1. **The corrected coset display (attack 1) — RE-DERIVED, and EXACTNESS
   re-proven in both directions.** With ϖ = x^{i₀}π^{a₀}, i₀h + e₁a₀ = 1:
   ϖ(θ)^k/n(k)(θ) = θ^{qe₁}π^{−qh} with q = (i₀k − i₀(k))/e₁ (checked:
   a₀k − (k − i₀(k)h)/e₁ = −qh follows from e₁a₀ = 1 − i₀h), so the ϖ-read =
   n(k)-read × res(n(k)/ϖ^k) = n(k)-read × η^{−q}. The n(k)-read set is
   EXACTLY the braced span: attaining slots of a dv(C) = k member are
   i = i₀(k) + e₁t with t ∈ T(k) and v(a_i) = (k−ih)/e₁ exactly (so each
   attaining coordinate is nonzero — no residue-0 coordinate can attain), and
   conversely every not-all-zero (c_t) is realized by
   C = Σ lift(c_t)π^{(k−ih)/e₁}x^i. **q(k) well-definedness at the corners
   examined:** q ∈ ℤ (i₀k ≡ i₀(k) mod e₁ since i₀ ≡ h^{−1}); q ≥ 0 (both
   representatives in [0,e₁) would force equality); e₁ = 1 gives i₀ = 0,
   q ≡ 0 (twist correctly absent); k < i₀(k)h gives n(k) a negative π-power
   (∈ K₀[x], same status the RIDER already grants ϖ) AND T(k) = ∅ AND no C
   attains k (slot arithmetic: attainment forces k ≥ (i₀(k)+e₁t)h for some
   t < f₁) — the three empty readings agree. The correction record's frame
   numbers re-checked: at (2,2,3), i₀(3) = 1, T(3) = {0}, q(3) = 1,
   ϖ(θ)³/n(3)(θ) = θ²π^{−3} of residue η, η^{−1}·F₃^× = {2η, η} — all as
   printed.
2. **Non-propagation inventory (attack 1) — routes (1), (4), (7) verified at
   their consumption sites; (8) verified definitional.** (1) DEFINITION
   HE6-1's B_t lifts prescribe ϖ-read residues at k = (d−t)u ≥ u > ℓD′h >
   (D′−1)h ≥ (i₀(k) + e₁(f₁−1))h — the fullness clause only (and the
   k-uniform bound re-derived: i₀(k) ≤ e₁−1). (4) HE7 §S4.2's proof calls
   HE6-1L at m_t ≥ (D′−1)h (its L436–437, L497–502: T(m_t) full) — fullness
   only. (7) he6r1 leg P3 (`lift2_checks... lift2_leg`, L752–785) asserts
   only |reach(k)| = p²−1 vs < p²−1 (onto/not-onto) — cardinality, invariant
   under any coset translate. (8) R_λ's §S1 display is a definition; its
   coherence under the twist re-checked: both R_λ's coefficients and
   HE6-2/2′'s transported reads are ϖ-reads, and ι_ξ(η_θ) = η_ξ transports
   the twist factor itself, so the twist cancels in every ι-transport
   (HE6-0″-based) step. Routes (2), (3), (5), (6) not re-walked (PE2's
   trace; (3) is (1) applied at Ψ constructions).
3. **HE6-0″'s −q sign (attack 2) — the one line checked, twice.** Division by
   ϖ^k multiplies the n(k)-read by res(n(k)/ϖ^k) = η^{−q} (same identity as
   item 1); ranging γ over the braced span gives ϖ-read set = η^{−q}·span =
   exactly HE6-1L [r2]'s display — the two [r2] displays are consistent. The
   witness re-computed by hand: A = x at (2,2,3), k = 3: γ = 1 (slot i = 1,
   t = 0), A(θ)/ϖ(θ)³ = π³/θ² = (θ²π^{−3})^{−1}, residue η^{−1} = 2η (η² = −1).
4. **The §S9 record repair (attack 3) — all four enumerated facts re-verified
   from scratch.** (i) md5(he6_checks.py) at HEAD = at close 1f5a417 =
   321fa4d4990e…, at seal a77c376 = af7009ecb005…; the file has exactly TWO
   versions in `git rev-list --all` history, neither 959fff…; (ii) runner
   mtime 2026-08-08 20:34:47 vs artifact mtimes 20:25:13 (9 min 34 s window,
   re-read from the filesystem); (iii) effect NIL re-established by THIS
   pass's own isolated re-run (S3 below), not by citing PE2's; (iv) the
   artifacts do not exist at seal (git show rc 128) and their md5s at close
   (403d44cfe462…, 1e1836651283…) equal HEAD — the corrected freeze anchor is
   right. The disclosure sentences are enumerated/scoped as written (no
   universal record claims found in the [r2] hunks).
5. **THEOREM HE6.A's core at a configuration no pass constructed (attack 4):
   f₁ = 3.** Dictionary re-derived by hand at (e₁,f₁,h) = (1,3,1), μ = 4,
   λ = 7/2 (single side, ℓ = 2): SPLIT with labels s, s^Q (a FROBENIUS
   pair — the exact configuration LEMMA HE6-5's ι_{gρ} = ḡ∘ι_ρ composition
   must keep in separate Galois-stable classes; f₁ = 1 batteries structurally
   cannot test this since ι is trivial there) predicts {(2,3),(2,3)}; INERT
   (r irreducible quadratic over F_{q³}, d_r = 2) predicts {(2,6)}. The
   machine leg (S3) confirms 40/40. HE6-5's proof steps re-checked at this
   instance: η_{gρ} = ḡη_ρ, β_{gρ} = ḡβ_ρ (ϖ, Φ′ have g-fixed coefficients),
   so the condition β = ι(s) is g-stable even when ḡ is Frobenius.
6. **Recon R3 row [r2] (F-4's repair):** the five enumerated byte-diffs
   spot-verified at diff #1 (HE6 L133 `ϖ(θ)^k` vs HE7 L376 `ϖ(θ)^{k}`) and
   diff #2 ("and it is ALL", HE7 L380); the row claims display-identity only
   at the r1 landing and flags the post-r2 divergence — accurate. The cited
   HE7 append prefix pin verified: first 158,362 bytes of HE7_PROOF at HEAD
   md5 0698155b… = the full file at 7e29d9e (append-only confirmed).
7. **Tautology audit (machine-leg integrity):** the sealed battery's σ oracle
   is PARI factorpadic+idealprimedec over gp, fed the raw integer
   coefficients; the reader's labels feed only the flat/excess dichotomy —
   re-confirmed on the re-run artifacts (totals equal the committed json
   field-for-field). This pass's fresh legs use a DIFFERENT oracle route
   (factor over ℚ + nfinit([g,[p]]) + idealprimedec — nf route, not
   factorpadic), decorrelated from every prior leg of the arc.

---

## S3. MACHINE + FRESH-ROUTE LEGS (this pass's instruments)

**Isolated re-run (sandbox /tmp/he6pe3_iso, fresh copy, md5 321fa4d…
verified immediately before launch):** `he6_checks.py` exit 0,
**0 violations**, legs 72,315 GEN / 4,232 SEP / 2,226 SIG / 24 XI / 6 ORTH,
**5/5 teeth fired**, 196.2 s; output identical to the committed
`he6_checks_output.txt` modulo timing lines and ONE disclosed difference: the
pins line (the runner pins he3_checks.py/he3_checks_results.json only when
present; the sandbox carried only the import-closure w10/w11/w12/engine_ext/
grt_jc_probe/jd0_checks/iterlawn_pe_reimpl/grb_order2_check). Results json
identical except `secs` and the pins block (field-by-field comparison).

**Fresh route (`verification/openmath/he6_pe3_fresh.py` + output + json;
md5s 2a69fba79d5e / ce7d809dddd1 / e09ee0704…; exit 0, 2.5 s; preregistered
FB-1..FB-4 in the docstring, 0 violations):**
* **Leg A — the first f₁ = 3 σ battery of this unit's arc** (every prior σ
  leg had f₁ = 1; PE2's f₁ = 2 leg was display-refutation, not σ):
  (1,3,1)-frames Φ′ = x³+4x+8/ℤ₂ (ψ = T³+T+1) and Φ′ = x³−9x−27/ℤ₃
  (ψ = T³−T−1), μ = 4, deg f = 12, λ = 7/2. Configs per frame: SPLIT-FROB
  (R_λ = (Z−η)(Z−η^Q), Frobenius-conjugate labels) and INERT2 (R_λ = Z²+Z+c
  irreducible over F_{q³}, brute-verified rootless). 10 members each (base +
  9 strictly-above-line perturbations), reader re-derives polygon + R_λ from
  raw integer coefficients on every member (40/40 match intended), disc ≠ 0
  checked on all 40. **PARI σ = the HE6.A dictionary 40/40**: SPLIT-FROB
  {(2,3),(2,3)} ×20, INERT2 {(2,6)} ×20, invariant under all perturbations.
* **Leg B — fresh coset certificate at q(k) = 3** (PE2's witness had
  q = 1): (e₁,f₁,h) = (2,2,5), ℤ₃, Φ′ = x⁴+3¹⁰, ϖ = xπ^{−2}, η² = −1.
  k = 7 (i₀ = 1, T = {0} proper, q = 3): 7,942 enumerated members, realized
  ϖ-read set = **{η, 2η}** = η^{−3}·F₃^× exactly as the [r2] display
  predicts — and ≠ the [r1] bare span {1,2} (disjoint). k = 15 = (D′−1)h:
  2,028 members realize **8/8 of F₉^×** (fullness twist-invariant, as
  displayed). Exact Fraction arithmetic in ℚ[x]/(x⁴+3¹⁰); no PARI needed
  (residue reads are exact by construction).
* **Leg C — the RIDER identity** res(ϖ(θ)^k/n(k)(θ)) = η^{q(k)} verified at
  every k ∈ {0,…,16} on the leg-B frame (17/17), covering the a₀ < 0 and
  k < i₀(k)h corners numerically.
* **Verifier-error disclosure (kept, per honesty norms):** the first run of
  leg A carried an off-by-one in my own F_{q³} reduction (η³ evaluated to 1),
  which corrupted the *intended* residuals symmetrically — and PARI's
  verdict then matched the CORRECTED reading of what was actually built
  (my "SPLIT" was truly Z²+(η+η²)Z+1, irreducible over F₈ → {(2,6)};
  my "INERT" c was truly split → {(2,3),(2,3)}), i.e. the oracle
  adjudicated against the constructor's corrupted intent in BOTH directions
  before the fix. Fix unit-tested (η orders 7 in F₈, 13 in F₂₇; η³ = 1+η in
  both), final run 0 violations. This is additional evidence the leg is not
  a tautology: the oracle can and did disagree.
* **Coverage disclosures:** the non-prime-q BASE oracle leg (q = p^k base
  ring) remains un-run in this arc (PE2's disclosed gap; PARI factorpadic
  and nfinit σ both sit over ℚ_p) — leg A reaches non-prime RESIDUE fields
  (F₈, F₂₇) through f₁ = 3, which exercises the K-side of the dictionary but
  not an unramified base. Leg A is char-0 only. No repeated-residual
  (HE6-BOX-1) member was built (boxed, out of scope).

---

## S4. GRADE LINE

**CLEAN under the charge bar: nothing at GAP-or-worse (and no MINOR)
survives this pass on the two target files. HE6-BOX-2 counter: 0/2 → 1/2.**
The five PE2 repairs are correctly and honestly applied at the [r2] sites
this pass examined (enumerated in S2); THEOREM HE6.A, COROLLARY HE6.B [r1],
LEMMA HE6-1L [r2], LEMMA HE6-0″ [r2] and the §S9 record survived a fresh
f₁ = 3 σ battery, a fresh q = 3 coset certificate, an independent isolated
re-run, and the re-derivations above. The two HE7-side observations (S1) are
notes for HE7's queue, not target findings. Second clean pass (PE4, fresh
context) required for acceptance at 2/2.

*Verifier: Fable (fresh context, zero prior stake), 2026-08-09. Artifacts:
`verification/openmath/he6_pe3_fresh.py`, `he6_pe3_fresh_output.txt`,
`he6_pe3_fresh_results.json`; isolated-re-run sandbox /tmp/he6pe3_iso
(ephemeral; md5 comparisons recorded above).*
