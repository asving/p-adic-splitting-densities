# O10_pass1_verify — hostile verification pass 1 of `O10_phaseB_attempt.md`

Date: 2026-07-31. Verifier: Fable (fresh context, no repo access beyond the
single audited file `lean/notes/openmath/O10_phaseB_attempt.md`). Charge:
quote-and-classify, fix nothing. Audited items: Lemma 1 (Sylvester block
det), Lemma 2 (Smith-profile constancy on the polydisc — the new mechanism),
the Step-3 T-bijection (Newton absorption), Theorem 2's product law at every
N ≥ τ, and the D-8 buffer's role (value vs law). Classification scheme per
the workspace discipline: **CRITICAL ERROR** (breaks the logical chain) vs
**JUSTIFICATION GAP** (assume and continue) vs **NOTE** (precision/wording,
no truth defect).

## Verdict

**PASS 1 CLEAN: zero critical errors and zero load-bearing justification
gaps found in the five charged items.** Every proof step in Lemmas 1–3,
Theorem 1 (Steps 1–5), Corollary 1, and Theorem 2 was re-derived
independently and checks. Findings below: 3 NOTEs (precision/wording) and
2 GAPs, both of which are *declared* conditionalities or out-of-file cites
rather than hidden defects — recorded so the acceptance ledger prices them.

---

## Item 1 — Lemma 1 (Sylvester block determinant): VERIFIED

Statement audited: "det Φ_h = ± Π_{i<j} Res(h_i, h_j)."

* **Base case m = 2.** Quote: "the matrix of (a₁, a₂) ↦ a₁h₂ + a₂h₁ in the
  monomial bases is (a row/column arrangement of) the Sylvester matrix of
  (h₂, h₁)". Checked: with deg a₁ < d₁ multiplying h₂ (deg d₂) and
  deg a₂ < d₂ multiplying h₁ (deg d₁), this is precisely the classical
  Sylvester map of the pair, target [x]_{<d₁+d₂}; det = ±Res. The sign
  disclaimer ("it plays no role below since only v_p(det) is used") is
  correct — every downstream use is of v_p(det) or minor valuations only.
* **Induction step.** Quote: "Φ_{m+1} = Φ₂^{(g,h_{m+1})} ∘ (Ψ ⊕ id)."
  Checked the degree bookkeeping the display suppresses: Ψ lands in
  [x]_{<n_m} and deg g = n_m, so (Ψ(a), a_{m+1}) is a legitimate input to
  the pair map for (g, h_{m+1}); codomain [x]_{<n_m + d_{m+1}} matches.
  Determinant multiplicativity over the direct sum and
  Res(AB, C) = Res(A, C)Res(B, C) for monics (exact, no leading-coefficient
  correction needed) are correctly invoked; Res(g, h_{m+1}) =
  Π_{i≤m} Res(h_i, h_{m+1}) closes the induction. VERIFIED.
* **Cokernel remark.** "length coker = v_p(det)" for an injective map of
  rank-n free ℤ_p-modules: standard Smith-form fact; injectivity is
  supplied by pairwise coprimality (Res ≠ 0 ⟹ det ≠ 0). VERIFIED.

## Item 2 — Lemma 2 (in-polydisc Smith-profile constancy): VERIFIED

This is the load-bearing new mechanism; I checked it adversarially in both
directions.

* Entries of Φ_h are coefficients of Π_{i≠j} h_i — ℤ-polynomial in the
  h-coefficients — so h ≡ f mod p^τ (coefficientwise) does give
  entry-wise congruence mod p^τ, hence **every k×k minor satisfies
  minor(h) ≡ minor(f) mod p^τ**. VERIFIED (multilinearity is not even
  needed; polynomiality over ℤ suffices).
* The pinning. d_k = v_p(gcd of k×k minors) = min over minors of v_p (DVR).
  Quote: "d_k(f) ≤ d_n(f) = ρ < τ (the d_k are partial sums of the nonneg.
  sorted e_i(f))". Checked: d_k = e₁+…+e_k ≤ Σe_i = d_n = ρ since e_i ≥ 0,
  and d_n(f) = v_p(det Φ_f) = ρ is Lemma 1 **applied at f**, where pairwise
  coprimality is a §1 hypothesis — Lemma 1 is never applied at h, so no
  circularity. Direction 1: a minor attaining d_k(f) has valuation < τ,
  hence its h-counterpart has the *same* valuation (congruence mod p^τ
  preserves valuations < τ exactly), so d_k(h) ≤ d_k(f). Direction 2: if
  d_k(h) < d_k(f) ≤ ρ < τ, the h-attaining minor's valuation is < τ,
  exactly preserved back, contradicting minimality of d_k(f). Both
  directions VERIFIED.
* Well-definedness of the profile at h: det Φ_h ≡ det Φ_f mod p^τ with
  v_p(det Φ_f) = ρ < τ forces det Φ_h ≠ 0, so Φ_h is injective and the
  (e_i(h)) exist. (The file leaves this implicit; it is one line and the
  ingredients are on the page — NOTE N1 below.) e_max ≤ Σe_i = ρ. VERIFIED.

## Item 3 — the T-bijection / Newton absorption (Theorem 1, Steps 1–4): VERIFIED

I re-derived the whole chain, including the mod-p^M well-definedness
subtleties the file compresses.

* **Step 1 (parametrization).** Difference of two monic degree-d_j
  elements of A_j(N) is a polynomial of degree < d_j with coefficients in
  p^τℤ/p^Nℤ: correct. The fiber condition transported to lifts is
  lift-independent (changing a lift by p^N changes Φ_h(a) + Q(a) by
  multiples of p^N — polynomiality over ℤ_p). The p-power bookkeeping
  Q(p^τ b) = p^{2τ} Q̃(b) with Q̃ having ℤ_p coefficients: exponent
  τ(|S|−2) ≥ 0 for |S| ≥ 2, correct. Division by p^τ giving (⋆) mod
  p^M = p^{N−τ}, and dependence of (⋆) on b̄ mod p^M only: VERIFIED.
* **Step 2 (Smith change of variables).** By Lemma 2 the exponents in
  D are the base-point (e_i) **for every fiber's lift h** — this is
  exactly where the new mechanism is consumed, and it is consumed
  correctly (h ≡ f mod p^τ holds because h lifts a member of Π A_j(N)).
  Multiplying by U^{−1} ∈ GL_n(ℤ_p) preserves the solution set mod p^M;
  c := Vb is a bijection of (ℤ/p^M)^n; S := U^{−1}∘Q̃∘V^{−1} again has
  ℤ_p coefficients. VERIFIED.
* **Step 3 (T-bijection).** Well-definedness: τ − e_i ≥ 1 since
  e_i ≤ ρ < τ (SEP + Lemma 2) — and multiplying a class mod p^M by
  p^{τ−e_i} is representative-independent mod p^M. Injectivity: the
  finite-difference factorization P(c) − P(c') = Σ δ_i G_i(c,c') is a
  polynomial identity over ℤ_p, valid mod p^M; it gives
  v_p(S_i(c) − S_i(c')) ≥ w, hence v_p(δ_i) ≥ min(M, (τ−e_i) + w) ≥
  min(M, 1+w), so w ≥ min(M, 1+w), which forces w ≥ M (if w < M then
  w ≥ 1+w, absurd). The capped valuation v_p(·) := min(v_p rep, M) is
  representative-independent and satisfies the two properties used
  (ultrametric bound; shift by p^k). Injective ⟹ bijective on the finite
  set. VERIFIED — the "Newton absorption" is legitimately a one-shot
  injectivity argument, no iteration or convergence needed.
* **Step 4 (count).** The equivalence (⋆⋆)_i ⟺ T(c)_i ≡ 0 mod p^{M−e_i}
  for e_i ≤ M: checked via a ℤ_p representative (p^{e_i}X ≡ 0 mod p^M ⟺
  X ≡ 0 mod p^{M−e_i}). The e_i > M case: (⋆⋆)_i is vacuous because
  p^{e_i}c_i ≡ 0 AND p^τ S_i(c) ≡ 0 mod p^M — the latter needs τ ≥ M,
  which holds since M < e_i ≤ ρ < τ. (The file says only "vacuous"; the
  τ ≥ M sub-check is real but immediate — NOTE N1.) Solution set =
  T^{−1}(G), #G = p^{s(M)}, T bijective ⟹ fiber count p^{s(M)},
  fiber-independent because (e_i) is (Lemma 2). VERIFIED. (ii) M ≥ e_max
  ⟹ s(M) = ρ, and e_max ≤ ρ makes N ≥ τ+ρ sufficient: VERIFIED.
* **Step 5 (blindness).** T(c) − T(c') has i-th coordinate of valuation
  ≥ max(M − e_i, 0) ≥ M − e_max in all cases (including e_i > M, where the
  bound is vacuous but the conclusion M − e_max < 0 is too); then
  w ≥ min(M − e_max, 1 + w) forces w ≥ M − e_max; V^{−1} has ℤ_p entries
  so min-valuation only goes up; a = p^τ b shifts by τ, total N − e_max.
  VERIFIED.
* **Corollary 1.** Well-definedness of ε via (iii)+K_j ≤ N−e_max: checked,
  including that fiber members *outside* ΠC_j still read to the same
  class. The set identity μ_N^{−1}(Σ) = ΠC_j (the keyed-at-K_j transfer
  t_j ≡ t'_j mod p^{K_j}, t'_j ∈ C_j ⟹ t_j ∈ C_j): checked. Fiber count
  p^{−s(M)}Π p^{(N−K_j)d_j} via "#μ_N^{−1}(E) = p^{s(M)}·#E for E ⊆ Σ"
  and the per-class count p^{(N−K_j)d_j} inside A_j(N): checked. VERIFIED.

## Item 4 — Theorem 2's product law at every N ≥ τ: VERIFIED, with one precision NOTE

* The central set identity, quote: "μ_N^{−1}(Σ ∩ S_j) = Π_i C_i ∩
  pr_j^{−1}(Ẽ_j) … this uses exactly (A3)". Checked: for t ∈ ΠC_j with
  μ_N(t) = F̄, ε(F̄)_j = t_j mod p^{K_j} (any-member well-definedness,
  Theorem 1(iii) + K_j ≤ N−e_max), so F̄ ∈ S_j ⟺ t_j ∈ Ẽ_j. The univ
  option folds in as Ẽ_j = A_j(N). VERIFIED.
* The three count displays and the algebra: both sides equal
  φ^{−m} Π_j #(C_j ∩ Ẽ_j) · (Π_i #C_i)^{m−1}; RHS bookkeeping
  Π_j Π_{i≠j} #C_i = (Π_i #C_i)^{m−1}: checked. The constant φ = p^{s(M)}
  cancels for any value — the "constancy, not unit value" mechanism is
  exactly right. Empty degeneracies consistent. VERIFIED.
* **NOTE N2 (vacuity window, not an error).** For τ ≤ N < τ + e_max no
  adapted presentation exists at level N: (A3) demands a key depth
  K_j ≤ N − e_max, while §1's keyed-at-depth definition has range
  τ ≤ K ≤ N, and C_j ⊆ A_j(N) can be keyed no shallower than τ. So the
  quantified Theorem 2 is *vacuously* true on that initial segment, and
  the repeated rhetoric — §0 "at EVERY level N ≥ τ (not only in the guard
  range)", §4.2 Remark (1) "the product law holds at EVERY N ≥ τ under
  (A1)–(A3), with no lower N-guard beyond read depth", §5.2 "the product
  law holds at every N ≥ τ with reads ≤ N − e_max" — is true as stated
  (the read-depth clause IS the guard) but does not display that the
  nonvacuous range is N ≥ τ + e_max. Harness T1's genuinely sub-guard
  content (fiber sizes 1/4/8/16) is a Theorem-1 claim, which IS nonvacuous
  at all N ≥ τ. Classification: NOTE — a reader porting "law at every
  N ≥ τ" into the Lean statement repair (§6) should carry the
  presentation-existence precondition, not a bare N ≥ τ.

## Item 5 — the D-8 buffer's role (value vs law): VERIFIED, with one wording NOTE

* Guard arithmetic of §4.3(a), quote: "N ≥ τ(c) + ρ(c) ≥ τ(c) + e_max and
  N − e_max ≥ N − ρ(c) ≥ thr(c) + ρ(c) ≥ K". Checked against (I-τ)
  (τ ≤ thr+ρ, τ ≥ ρ+1, K ≤ thr+ρ) and N ≥ thr+2ρ: N ≥ (thr+ρ)+ρ ≥ τ+ρ;
  M ≥ ρ ≥ e_max puts the level in Theorem 1(ii)'s range (value p^ρ,
  clause (c) = Corollary 1 in the guard range); N−e_max ≥ N−ρ ≥ thr+ρ ≥ K
  gives (A3). All inequalities VERIFIED.
* Clause (d) and §5.2's split — the LAW carries only the read-depth guard,
  the VALUE p^{ρ(c)} carries N ≥ thr+2ρ: this is a faithful reading of
  Theorem 1(i)+(ii) and Theorem 2, and (d)'s proviso "reads stay ≤ N−ρ(c)"
  correctly implies (A3) via e_max ≤ ρ. The sub-guard value p^{s(M)}
  "still constant, still cancelling" is Theorem 1(i) + the φ-cancellation.
  VERIFIED. D-8r's reduction to a read-ceiling discipline follows.
* **NOTE N3 (headroom phrasing).** §4.3(d)/§5.2(ii)'s "gives the reads
  ρ(c) headroom" is loose: headroom to the true well-definedness ceiling
  N − e_max is (N−e_max) − (thr+ρ) ≥ ρ − e_max, which is **0** when
  e_max = ρ (a case the battery contains: any ρ concentrated in one
  elementary divisor). The defensible reading — reads sit ρ(c) below the
  working level N, i.e. K ≤ N − ρ(c), which is what clause (d) actually
  uses — is correct. Classification: NOTE (wording; no downstream step
  consumes the stronger reading).

## Out-of-scope-of-this-file dependencies (declared; recorded as GAPs so they stay priced)

* **GAP G1 (box-count transport; cited, not re-derived).** Quote (§1):
  "at the pinned chart each monic F mod p^N corresponds to exactly one box
  point pattern of its n·N coefficient digits, so all cardinalities below
  transport verbatim to box counts (M07 brief §2.1)"; consumed by §4.3(b)
  ("box counts = coefficient-class counts, §1"). Not checkable from this
  file. Since §4.3 is in any case conditional on (I-τ), this rides the
  same conditionality — but it is a distinct claim from (I-τ) and should
  be verified where M07 brief §2.1 is in scope. Classification:
  justification gap (external cite), assumed and continued.
* **GAP G2 (harness unverifiable here).** The 68/68 numerics record (§7)
  and the sealing narrative (§7.3) cannot be audited from the single file
  (no access to `verification/o10_kcount_harness.py`). The mathematical
  verdict above is independent of the harness; the harness's evidential
  weight should be confirmed by a run in a session with repo access.
  Classification: justification gap for the *numerics record* only —
  no proof step cites the harness.
* The remaining conditionality — (I-τ)/K-LOC open, K-FACT consumed as the
  GMN citation, OL-2 untouched, item-27 repair PARKED — is displayed
  correctly and consistently in §0, §4.3, and §8; the honesty ledger's
  perimeter statement ("NOTHING here claims the engine's realized site
  strata satisfy (A1)–(A3)") matches what is actually proved. No hidden
  strengthening found.

* **NOTE N1 (two one-line implicit sub-checks, both true).** (a) Lemma 2
  leaves implicit that Φ_h is injective (needed for its Smith profile to
  exist): det Φ_h ≡ det Φ_f mod p^τ with v_p(det Φ_f) = ρ < τ ⟹
  det Φ_h ≠ 0. (b) Step 4's "for e_i > M … vacuous" needs p^τ S_i(c) ≡ 0
  mod p^M, i.e. τ ≥ M — true since M < e_i ≤ ρ < τ. Both are immediate
  from displayed material; recorded only so pass 2 need not re-derive.

## Summary table

| # | Class | Where | One line |
|---|-------|-------|----------|
| — | critical errors | — | **none found** |
| G1 | justification gap (external cite) | §1 → §4.3(b) | box-count transport rests on M07 brief §2.1, unverifiable from this file |
| G2 | justification gap (numerics record) | §7 | harness results not auditable single-file; proofs independent of them |
| N1 | note | Lemma 2, Step 4 | two implicit one-line sub-checks (Φ_h injective; τ ≥ M in the e_i > M case), both true |
| N2 | note | Thm 2 / §0 / §5.2 | "law at every N ≥ τ" is vacuous for N < τ + e_max (no presentation exists); carry the precondition into the item-27 repair |
| N3 | note | §4.3(d)/§5.2 | "ρ(c) read headroom" means K ≤ N − ρ(c); headroom to the true ceiling is ρ − e_max, possibly 0 |

**Pass 1 verdict: ACCEPT-track.** Zero critical errors, zero load-bearing
gaps in the charged items; the two recorded gaps are declared external
dependencies, and the three notes are precision items for the Lean
statement repair. Per the workspace discipline (accept only after several
consecutive clean passes), this is clean pass 1 of the required sequence,
not final acceptance.
