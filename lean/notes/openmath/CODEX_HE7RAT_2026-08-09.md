# HE7 RATIFICATION — CODEX ADVERSARIAL PASS (decorrelated model, post-acceptance) + ADJUDICATION

## S0. Charter and provenance

**Pass:** the ratification sweep's FIRST leg on the FROZEN accepted text of
`HE7_PROOF_2026-08-08.md` — ACCEPTED 2/2 at PE3 (arc: seal 1956151 → r1
2970615 → PE1 7b66364 → r2 83ced80 → PE2 CLEAN 8f5f2a6 → r3 e0c0240 → PE3
CLEAN 111ac7f) plus ANNEX F-1 (a4a91ee/7b3f0f1, ANNEX-LEMMA HE7-13′).
**Verifier:** Codex `gpt-5.6-sol`, reasoning effort HIGH, fresh context,
charged quote-and-classify / fix-nothing — a DIFFERENT model attacking what
seven same-family routes may share blind spots on. **The brief mandated the
attack order:** (1) LEMMA HE7-12(c)'s four never-audited items 1/7/9/10
(PE2 did 2/3/4/5/6/8/11; PE3 added none); (2) ANNEX-LEMMA HE7-13′(a)'s
block-factor construction at an INSEPARABLE residual; (3) the δ₂ = κ₂
boundary of LEMMA HE7-7 Step 2, both directions; (4) §S7's verbatim-reuse
claim (ℓ ≥ 2 → ℓd_r ≥ 2); (5) free hunt.

- **Brief:** `he7rat_brief_2026-08-09.txt` (this directory, commit 853b479),
  **159,072 chars, NO trims** (the 1,048,576-char input cap was not
  approached): PASTE A = the full HE7 note byte-verbatim incl. ANNEX F-1;
  PASTE B = HE6 §S1 lines 55–200 (frame + both standing conventions + the
  struck (LIFT) + LEMMA HE6-1L [r1] + RIDER + NON-PROPAGATION + DEFINITION
  HE6-1 + HE6-0″/0/0′/1/2/2′); PASTE C = HE6R1_RECON lines 226–410
  (LEMMAS HE6R1-1/2/3 with proofs); PASTE D = GENHN lines 405–485
  (consumption audit + LEMMA GENHN-2 + proof + twist paragraph). Known brief
  limitation, pre-registered in the scaffold: HE6-3/HE6-4/HE6-5/HE6.A
  statements not pasted (given by name); no finding turned on it.
- **Run of record:** session `019fe4c6-4ae2-7053-95f9-d5c5cc0d58d1`,
  gpt-5.6-sol, effort HIGH, launched 04:27 UTC 2026-08-09 (stdin `-` prompt
  mode — the 159 KB brief exceeds the argv limit; first launch attempt died
  at `nohup: Argument list too long` with no session started), exited
  04:34:47 (≈ 7.5 min), **74,685 tokens**, log
  `/tmp/codex_he7rat_stdin_1786249627.log`; raw final message extracted to
  `/tmp/he7rat_raw.txt` and reproduced verbatim in the appendix.
- **Decorrelation discipline:** the orchestrator wrote a pre-verdict key for
  all four attack points + free-hunt candidates BEFORE reading any Codex
  output (`he7rat_scaffold_2026-08-09.md`, this directory, committed as-was
  during the run). §S3 below records the match.

## S1. VERDICT (orchestrator adjudication, not Codex's self-grade)

**Codex returned 5 findings (1 CRITICAL-classified + 2 GAP + 2 MINOR).
After independent re-derivation of every claim: ALL 5 CONFIRMED as real
defects of the text at their quoted sites; 2 of the 5 regraded in severity
(F3 down to wording-MINOR; F2's severity split GAP-as-stated /
MINOR-by-arc-precedent flagged for Asvin). The four charged attack surfaces
themselves came back CLEAN — the two heavy findings came out of the FREE
HUNT, on §S6's ladder definition and §S1's standing convention.**

**RATIFICATION OUTCOME: CHALLENGE** (confirmed GAP-or-worse exists — the
acceptance is annotated; Asvin decides). Scope, stated exactly:

- **F1 (CONFIRMED, CRITICAL as stated)** lands on **§S6 / DEFINITION HE7-2 /
  THEOREM HE7.D / COROLLARY HE7.B(ii) ONLY** — first live at level 3, i.e.
  n ≥ 16, with NO machine leg anywhere at level 3. **The level-2 core —
  §S1–S5, §S7 (TERMINATION), §S8 (the n = 8 closure), THEOREM HE7.A/HE7.A′,
  THEOREM HE7.C, COROLLARY HE7.B(i) (n ≤ 15), and the whole machine record —
  does NOT consume DEFINITION HE7-2** (§S1 defines n₂ directly) and is
  untouched. But §S9 lists "the level-i package by induction §S6" under
  "proved here, with no residue", so the acceptance's coverage of THEOREM
  HE7.D is genuinely challenged; repair owed as a dated annex.
- **F2 (CONFIRMED, GAP as stated)** is display-level with an in-toolkit
  verbatim repair (re-derived below, §S2): the conclusion is TRUE — no
  counter-instance can exist — but the standing convention's displayed
  equivalence chain is not formal for a reducible key. Arc precedent
  (PE2 F-1, PE3 F-1) graded exactly this shape MINOR; flagged both ways.
- **F3 regraded MINOR** (wording overreach, no consumer), **F4/F5 MINOR**
  (F4 = the orchestrator's pre-verdict key, exact match).

No sealed number, no battery verdict, and no n ≤ 15 σ-claim moves. The
machine record (1,587/1,587 + all supp legs) is untouched by construction —
every finding lives in proof-display/definition text, not in any exercised
computation.

## S2. The findings, transcribed + adjudicated (Codex's numbering; raw quotes in the appendix)

| # | Codex finding (compressed) | Codex class | adjudication |
|---|---|---|---|
| 1 | DEFINITION HE7-2's normalizer recursion n_{i+1}(k) := n_i(m)·Φ_i^s (0 ≤ s < ℓ_i) is incompatible with its own base claim "n₁ = ϖ-powers": at (e₁,h) = (2,3), k = 3 the recursion gives n₁(3) = x while ϖ³ = x³π^{−3}, quotient residue η_θ — the RIDER twist. The ladder lacks a coherent normalizer/cocycle convention; THEOREM HE7.D and COROLLARY HE7.B(ii) unproved as displayed | CRITICAL | **CONFIRMED — CRITICAL as stated for THEOREM HE7.D's proof, scoped to §S6.** Re-derived: with 𝔇₀ = (x,1,v,e₁,f₁,h,…), n₁(k) = n₀(m)·x^{s(k)} has x-degree s(k) < e₁, while ϖ^k has x-degree i₀k ≥ e₁ for k ≥ e₁ (any i₀ ≥ 1) — equality impossible regardless of n₀; Codex's instance checks exactly (quotient x²π^{−3}, residue η_ξ ≠ 0, generically ≠ 1). The note presents "n₁ = ϖ-powers" as a recursion OUTPUT (same list as D₁ = D′, w₁ = dv, T₁ = D′h, all genuine outputs) — internally inconsistent. Even under the charitable reading (recursion for i ≥ 1 with n₁ := ϖ^k an override), §S6's "(SLOT). §S3 verbatim … Nothing else enters" is FALSE at level ≥ 3: §S3 Step 3's factorization ϖ^{m₀} = ϖ^{m₀−tu}·ϖ^{tu} (trivial cocycle) becomes n_i(m₀) vs n_i(m₀−tu_i)·n_i(tu_i) with a NONTRIVIAL β-power cocycle for i ≥ 2, so (SLOT_i)'s displayed residue formula needs a twist correction the "SAME proofs" claim glosses. MITIGATION (derived, not Codex's): the cocycle residue is a fixed power of the level-i letter ∈ K_i^×, so the twisted γ_t stay in K_i and the K_i-independence/no-cancellation argument survives — (SLOT_i)'s STATEMENT (exactness + nonzero residue in K_{i+1}) is twist-robust, and all consumed counts are twist-blind (the §S1 J-D0 convention). Expected repair: re-base the recursion at n₁ := ϖ-powers + carry the level-i cocycle through the τ_t mechanism of §S5.3 Step 2 (already displayed at level 2). First live at level 3 = n ≥ 16; ZERO machine exercise exists there (the annex's n = 16 leg reports 0 level-3 skips). **Level-2 core untouched: §S1 defines n₂ = ϖ^{m(k)}Φ′^{s(k)} directly; only §S6 consumes DEF HE7-2** |
| 2 | §S1 CONVENTION's chain "Ψ ∤ f_S ⟺ A₀^{(2)} ≠ 0 ⟺ dv₂(Ψ(ρ)) < ∞ at every root" needs Ψ ∤ f_S ⟹ gcd(Ψ, f_S) = 1, not formal since Ψ is NOT assumed irreducible (abstractly Ψ = ab, f_S = ac); LEMMA HE6R1-3 as pasted assumes the stronger Ψ \| f_S; the same omission recurs at the annex's f_C inference; until closed, HE7-7″/HE7-9/HE7-13′(a) are unlicensed on the stated stratum | GAP | **CONFIRMED — GAP as stated; the conclusion is TRUE and the repair is verbatim in-toolkit (no statement moves).** Re-derived repair: suppose g₀ := gcd(f_S, Ψ) ≠ 1. Every root ξ of g₀ is a root of Ψ = Ψ_{λ,r}, hence a level-2 point (LEMMA HE6-1; at a refined key Ψ̃, HE7-12(b)'s disk criterion — item 11's mechanism), so [L_ξ : K₀] ≥ D″ (HE6-0′/HE7-5); g₀'s root set (common roots of two Galois-stable sets) is Galois-stable, so deg g₀ ≥ D″ = deg Ψ ≥ deg g₀, forcing g₀ = Ψ and Ψ \| f_S. Contrapositive: Ψ ∤ f_S ⟹ gcd = 1 ⟹ dv₂(Ψ(ρ)) < ∞ ∀ρ — LEMMA HE6R1-3's own proof with "g₀ ≠ 1" replacing "Ψ \| f_S", byte-near-verbatim. Codex's abstract Ψ = ab / f_S = ac scenario is therefore IMPOSSIBLE in context (a proper common factor would be a Galois-stable factor of Ψ of degree ≥ deg Ψ). Annex leg: gcd(Ψ̃, f_C) ≠ 1 ⟹ Ψ̃ \| f_C \| f_S, contradicting Ψ̃ ∤ f_S — one line. SEVERITY FLAG: as-stated GAP (the equivalence is underived at a standing convention consumed at level 2 everywhere); by arc precedent (PE2 F-1's W ≠ 0, PE3 F-1 — verified-true, in-toolkit, display-scale) this shape was twice graded MINOR. Asvin adjudicates which grade governs the ratification |
| 3 | "The first degree at which J = 2 is possible is n = 16" / "The first n at which a level-3 object can be needed is n = 16": only the necessary direction (J ≥ 2 ⟹ n ≥ 16) is proved; no degree-16 two-jump witness exists (the annex's n = 16 family reports 0 level-3 skips) | GAP | **CONFIRMED as a defect, REGRADED MINOR (wording overreach).** The proved direction (level 3 unreachable below n = 16) is the ONLY direction any consumer uses (THEOREM HE7.C's gate, HE7.B(i)'s n ≤ 15 clause, §S8's "level 3 is degenerate"); the existential reading ("can be needed" = a witness exists at n = 16) is indeed unproven — and could even be false — but nothing consumes it. It is a scope-limiting honesty sentence, not a load-bearing claim. Repair: reword to "the first degree NOT EXCLUDED by the bound is n = 16" |
| 4 | HE7-12(c) item (7)'s dependency sentence is inaccurate: HE6R1-2 consumes not "only the HE7-7/7′ analogues" but also HE6-4 + HE6-2′ (level 1, clause (a)), (LIFT₂) + the test family + HE7-9(a) + THEOREM HE7.A(1) (clause (b)), the test family + HE7-7/7′ again (clause (c)); coverage happens to route through items (1),(2),(5),(6),(8) | MINOR | **CONFIRMED, MINOR — the orchestrator's pre-verdict key EXACTLY** (scaffold P-1, item 7: same extra dependencies, same "content survives via the wider audit" disposition). Citation-completeness erratum on one sentence of the clause-(c) audit; no transfer breaks |
| 5 | §S4.2's "a proper subgroup-coset of K₂ is reached" is wrong algebra: the sub-threshold reachable set is the nonzero part of a proper F_Q-subspace — e.g. in F₈, {1, β, 1+β} (size 3) is neither an additive subgroup/coset (size 2^k) nor a multiplicative one (7 has no order-3 subgroup) | MINOR | **CONFIRMED, MINOR** (wording in a sharpness remark). LEMMA HE7-L1's own display gives the correct object ({Σ_{t∈T(k)}c_tη^t : c_t ∈ F_Q, not all 0} — a punctured subspace); the §S4.2 sentence mislabels it. The F₈ counterexample checks. Nothing consumes the "subgroup" structure; tooth HE7-T-LIFT2SHARP verifies the exact sets by enumeration |

**CHECKED CLEAN (Codex, spot-verified against the pre-verdict key):** the
four charged surfaces ALL survived — HE7-12(c) items (1) (key-freeness of
(SLOT₂)/(LIFT₂): genuine), (9) (Ψ − w Galois-fixed, HE7-11 survives), (10)
(the refined-key sandwich routes through items (4),(2),(5),(6),(8),(9));
HE6R1-2 at the refined key (despite F4's inventory defect); ANNEX-LEMMA
HE7-13′'s full inseparability audit (HE7-5/HE7-6/HE7-9/HE7-10/HE7-11/HE7-7″
separability-free, conditional on F2), the block residual R^(C) = c·r^k with
k = L_C/(ℓ₂·deg r) ∈ ℤ_{≥1}, clauses (c) (translated label r₂^τ) and (e)
(residue −ι(s₂)); the δ₂ = κ₂ boundary BOTH directions (C₀ ≠ 0 from
r₂(0) ≠ 0; the monic top incl. the δ₂ = ∞/common-root exclusion; endpoint
uniqueness under arbitrary middle vanishing); the twist algebra (c_t ∈ ℤ via
numerator ≡ 0 mod ℓ; res(τ_t) = β_ξ^{c_t} with the displayed sign); THEOREM
HE7.C's quantitative core (no off-by-one in 4 ≤ μ_J ≤ μ/2^{J−1} ⟹
J ≤ log₂μ − 1; descent alternatives complete); DEFINITION HE7-2's gcd
recursion (lowest-terms at each node); §S8's dictionary exhaustive at
μ₂ = 2 incl. the peel row.

## S3. Decorrelation record (pre-verdict key vs the delivered pass)

Key CONFIRMED by the pass: **P-1 item (7) = Codex F4 exactly** (same extra
dependencies, same disposition); P-1 items (1)/(9)/(10) predicted clean —
clean; P-2 (annex inseparability audit clean; the f_C standing-convention
inference flagged as the weak corner — Codex's F2 names the SAME annex site
as the recurrence of its convention finding); P-3 predicted clean incl. the
C₀ ≠ 0 and twist-integrality sub-checks — clean, Codex did not even count
the C₀ display nit; P-4 predicted clean (no off-by-one) — clean.
Codex EXCEEDED the key with: **F1 (the normalizer recursion base — the key
looked at DEF HE7-2's gcd and w_i-vagueness but MISSED the n₁/ϖ-power
incoherence entirely — the pass's one heavy find)**, the sharp general form
of **F2** (the key had only its f_C shadow), **F5** (unexamined). The key's
other free-hunt candidates ((S6.3)'s ε_j = 0 compression, HE7-8's
"recentering" clause) drew no finding — consistent with my own re-derivation
that they close. Net: the decorrelated model dominated the same-side key on
the free hunt exactly where seven same-family passes had never looked (§S6's
definitional base; the reducible-key corner of a standing convention) —
the ratification sweep earned its cost on F1/F2.

## S4. Repair queue (owed as dated annexes — the accepted body is FROZEN)

1. **R1 (F1, the heavy item): ANNEX on §S6/DEFINITION HE7-2** — re-base the
   normalizer recursion (n₁ := ϖ-powers as level-1 base; recursion for
   i ≥ 1), display the level-i cocycle n_i(a)n_i(b)/n_i(a+b) = (letter
   twist) and carry it through the §S3-Step-3/§S5.3-Step-2 τ mechanism at
   level ≥ 3; restate (SLOT_i)'s residue clause twist-correctly; re-check
   (LIFT_i)'s construction under the corrected system; display why every
   consumed count is twist-blind (J-D0). Until it lands, THEOREM HE7.D and
   COROLLARY HE7.B(ii) carry an annotated grade; HE7.A(3)'s level-3 branch
   (μ₂ ≥ 4 gate, n ≥ 16) inherits the annotation. n ≤ 15 claims unaffected.
2. **R2 (F2): ANNEX paragraph on the §S1 CONVENTION** — the gcd dichotomy
   (gcd(f_S, Ψ) ∈ {1, Ψ}) via HE6R1-3's proof from g₀ ≠ 1 (displayed in §S2
   above), plus the one-line f_C rider at ANNEX-LEMMA HE7-13′(a); optionally
   an HE6R1-side erratum widening LEMMA HE6R1-3's hypothesis to gcd ≠ 1.
3. **R3 (F3): reword** the two n = 16 sentences to the non-excluded form.
4. **R4 (F4): correct** HE7-12(c) item (7)'s dependency sentence (add
   HE6-4/HE6-2′/HE7-9(a)/HE7.A(1); route through items (1),(2),(5),(6),(8)).
5. **R5 (F5): reword** §S4.2's "subgroup-coset" to "punctured proper
   F_Q-subspace".

## S5. Artifacts

- `he7rat_brief_2026-08-09.txt` — the launched brief (this directory,
  commit 853b479).
- `he7rat_scaffold_2026-08-09.md` — the pre-verdict key (this directory,
  committed as-was during the run).
- `/tmp/codex_he7rat_stdin_1786249627.log` — full run log (brief echo +
  final message); `/tmp/he7rat_raw.txt` — extracted canonical message.
- Appendix below — the raw Codex report, verbatim, first emission.

---

## APPENDIX: RAW CODEX REPORT (verbatim, first emission — session 019fe4c6-4ae2-7053-95f9-d5c5cc0d58d1)

1. **Verbatim quote:**  
   “`n_{i+1}(k) := n_i(m)·Φ_i^{s}  with ℓ_i m + s u_i = k, 0 ≤ s < ℓ_i,`”  
   together with  
   “`n_1 = ϖ-powers: level 1 is HE6's frame`.”

   **Classification: CRITICAL ERROR.**

   **Failure:** These two requirements are incompatible. Take \((e_1,h)=(2,3)\), so \(i_0=1,a_0=-1\) and \(\varpi=x\pi^{-1}\). At level \(0\), \(k=0\) forces \(n_1(0)=n_0(0)=1\). For \(k=3\), the recursion \(2m+3s=3\), \(0\le s<2\), gives \((m,s)=(0,1)\), hence
   \[
   n_1(3)=n_0(0)x=x,
   \]
   whereas “\(n_1=\varpi\)-powers” requires
   \[
   n_1(3)=\varpi^3=x^3\pi^{-3}.
   \]
   Their quotient evaluates to the nontrivial residue \(\theta^2\pi^{-3}\), exactly the RIDER twist discussed in PASTE B. Thus the recursive system is the canonical mixed-normalizer system, not HE6’s twist-free \(\varpi^k\) system. The claim that §S3–§S5 transfers at every level “with the SAME proofs” therefore lacks a coherent base normalizer and cocycle convention. THEOREM HE7.D and conclusions depending on the unrestricted ladder, notably COROLLARY HE7.B(ii), are unproved.

2. **Verbatim quote:**  
   “`Throughout §S2–S8, Ψ ∤ f_S — equivalently the Ψ-development's constant coefficient A₀^{(2)} ≠ 0, equivalently dv₂(Ψ(ρ)) < ∞ at every root ρ of f_S.`”

   **Classification: JUSTIFICATION GAP.**

   **Failure:** The first equivalence is polynomial division, but the second requires
   \[
   \Psi\nmid f_S\quad\Longrightarrow\quad \gcd(\Psi,f_S)=1.
   \]
   That is not formal because the note repeatedly emphasizes that \(\Psi\) is not assumed irreducible. Abstractly, with \(\Psi=ab\) and \(f_S=ac\), one has \(\Psi\nmid f_S\) and a nonzero \(\Psi\)-remainder, yet roots of \(a\) satisfy \(\Psi(\rho)=0\). LEMMA HE6R1-3 as pasted assumes the stronger condition \(\Psi\mid f_S\); its statement does not exclude a proper common factor. The same omission recurs in the annex when it infers that each \(f_C\) satisfies the standing convention merely from \(\widetilde\Psi\nmid f_S\). A degree/local-forcing argument may rule out proper common factors, but it is not stated or invoked. Until that dichotomy is established, finite labels need not partition all roots and COROLLARY HE7-7″, HE7-9, and ANNEX-LEMMA HE7-13′(a) are not licensed on the stated stratum.

3. **Verbatim quote:**  
   “`The first degree at which J = 2 is possible is n = D′μ with μ ≥ 8, i.e. n = 16.`”  
   and  
   “`The first n at which a level-3 object can be needed is n = 16.`”

   **Classification: JUSTIFICATION GAP.**

   **Failure:** The preceding inequalities establish only the necessary implication
   \[
   J\ge2\Longrightarrow \mu\ge8\Longrightarrow n\ge16.
   \]
   They do not construct, or prove the existence of, a degree-16 configuration requiring two jumps. The annex’s degree-16 machine family is not such a witness—it expressly reports “0 level-3 skips.” Thus “\(n=16\) is the first degree not excluded by the bound” is established; “first degree at which level 3 can be needed” is not.

4. **Verbatim quote:**  
   “`LEMMA HE7-6 is about level-1 labels — key-free; LEMMA HE6R1-2's read consumes only the HE7-7/7′ analogues, items (5)–(6).`”

   **Classification: MINOR.**

   **Failure:** PASTE C shows that HE6R1-2 does not consume only HE7-7/7′. Clause (a) invokes HE6-4 and HE6-2′; clause (b) invokes (LIFT₂), the test-family construction, HE7-7, HE7-7′, HE7-9(a), and THEOREM HE7.A(1); clause (c) again invokes the test family and HE7-7/7′. The wider HE7-12 audit happens to cover these dependencies through items (1), (2), (5), (6), and (8), so this inaccurate dependency sentence does not by itself break the transfer.

5. **Verbatim quote:**  
   “`below them the failure is genuine (a proper subgroup-coset of K₂ is reached, or the height is not attained at all).`”

   **Classification: MINOR.**

   **Failure:** The reachable nonzero residues below threshold are generally the nonzero elements of a proper \(K\)-linear or \(\mathbf F_Q\)-linear subspace, not a subgroup or coset. For example, in \(K_2=\mathbf F_8\), if only the \(1,\beta\) slots are reachable, the nonzero set is
   \[
   \{1,\beta,1+\beta\},
   \]
   of size \(3\). It is neither an additive subgroup/coset, whose size must be a power of \(2\), nor a multiplicative subgroup/coset of \(\mathbf F_8^\times\), whose order \(7\) admits no subgroup of size \(3\).

CHECKED CLEAN

- HE7-12(c), item (1): (SLOT₂) and (LIFT₂) use only \(\Phi'\)-slots, level-2 points, \(n_2\), and \(K_2\); neither mentions the key \(\Psi\).
- HE7-12(c), item (9): replacing \(\Psi\) by \(\Psi-w\) preserves membership in \(O[x]\), monicity, degree, and Galois-fixed coefficients; HE7-11’s equivariance computation survives.
- HE7-12(c), item (10): the refined-key sandwich is licensed by item (4) for local forcing, items (2),(5),(6),(8) for HE7-9/10—including their key-powered test polynomials—and item (9) for Galois stability.
- HE6R1-2 at the refined key: despite item (7)’s incomplete dependency inventory, its actual level-2 uses transfer through the refined test family and HE7-7/7′/9; its level-1 HE6-4 and HE6-2′ calls are unchanged.
- ANNEX-LEMMA HE7-13′, inseparable residual audit: conditional on the standing coprimality issue in finding 2, HE7-5, HE7-6’s factor argument, HE7-9, HE7-10, HE7-11, and COROLLARY HE7-7″ do not use separability or multiplicity one.
- ANNEX-LEMMA HE7-13′(a): HE7-10 applies to \(f_C\) once its stated block hypotheses hold; it forces every irreducible factor of \(R^{(C)}\) to be \(r\), yielding \(R^{(C)}=c\,r^k\) and \(k=L_C/(\ell_2\deg r)\in\mathbf Z_{\ge1}\).
- ANNEX-LEMMA HE7-13′(c),(e): translation \(r^\tau(Z)=r(Z+s_2)\) preserves monicity, irreducibility, degree, and nonzero constant term; the residue in (e) is correctly \(-\iota_\rho^{(2)}(s_2)\), with minimal polynomial \(Z+s_2\).
- HE7-7 Step 2 boundary: \(c_{2,0}=r_2(0)\ne0\) makes \(C_0\) a nonzero exact-height lift; the monic top term handles \(\delta_2<\kappa_2\), including exclusion of a common root with \(\Psi\); arbitrary vanishing middle coefficients does not disturb endpoint uniqueness.
- HE7-7 twist: \(c_t\in\mathbf Z\) because its numerator is \(0\bmod\ell\), and the product-normalizer identity gives \(\operatorname{res}(\tau_t)=\beta_\xi^{c_t}\) with the displayed sign.
- THEOREM HE7.C quantitative core: \(L_\lambda\ge m(\ell d_r)\ge4\), \(\mu_2\le\mu/(\ell d_r)\le\mu/2\), and \(J\le\log_2\mu-1\) have no off-by-one error. Splits, peels, jumps, and the annex’s per-block refinement routing give the required descent/finite-tail alternatives.
- DEFINITION HE7-2’s gcd condition: each new slope is explicitly written in lowest terms, so \(\gcd(u_i,\ell_i)=1\) is available at each node; the defect is the normalizer recursion, not the gcd recursion.
- §S8’s \(n=8\) dictionary is exhaustive on its boxed \(\mu_2=2\) configuration, including the peel row.

Verdict: HE7’s level-2 and annex calculations survive the charged boundary, twist, inseparability, and refined-test-polynomial checks, but ratification of the whole document fails. The level ladder has an internally inconsistent normalizer recursion, and the standing convention omits the argument excluding proper common factors of a possibly reducible key. The claimed degree-16 “first need” is also stronger than the proved lower bound.
