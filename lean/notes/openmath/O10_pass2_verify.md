# O10_pass2_verify — hostile verification of `O10_phaseB_attempt.md`, PASS 2

Date: 2026-07-31. Verifier: Claude (Fable 5), FRESH context, model-diverse pass
(pass 1 recorded clean; this pass did NOT read the pass-1 report or any prior
verification artifact — the target document was read standalone, per charge).
Charge focus: (1) Lemma 1 (Sylvester block determinant), (2) Lemma 2
(Smith-profile constancy — the new mechanism), (3) the T-bijection absorption
(Theorem 1 Steps 3–4), (4) Theorem 2 at every N ≥ τ, (5) the D-8 buffer
value-vs-law distinction. Protocol: quote-and-classify (CRITICAL ERROR vs
JUSTIFICATION GAP); nothing fixed; a ∀-by-example is CRITICAL.

Independent evidence gathered this pass (beyond reading): re-ran
`verification/o10_kcount_harness.py` — **68 PASS / 0 FAIL / 8 INFO reproduced
exactly**, including T4's breakage ratios (2 at B4 with p = 2; 3 at B10 with
p = 3) and T5's straddling counts (4/4 at B3, 32/32 at B5, 5/5 at B8; 0
straddling at B4/B10, consistent with the document's "in general"); and an
independent throwaway script checking Lemma 2 directly (B10 pair at p = 3,
τ = 4: determinantal-divisor vector d = (0, 0, 1, 3) invariant across random
polydisc perturbations — note e_max = 2 < ρ = 3 there, matching the harness's
blindness moduli p^{N−2}).

## §V1 Item-by-item verification

### V1.1 Lemma 1 (Sylvester block determinant) — VERIFIED

- Base m = 2: (a₁, a₂) ↦ a₁h₂ + a₂h₁ with deg a₁ < d₁ = deg h₁,
  deg a₂ < d₂ = deg h₂ is exactly the Sylvester pairing of (h₂, h₁); det =
  ±Res, and only v_p(det) is consumed downstream, so the sign is genuinely
  immaterial as claimed. Hand-checked at h₁ = x−a, h₂ = x−b: matrix
  [[−b, −a], [1, 1]], det = a − b. ✓
- Induction step: the displayed factorization Φ_{m+1} = Φ₂^{(g,h_{m+1})} ∘
  (Ψ ⊕ id) is an identity of linear maps (checked by expanding both sides on a
  general tuple), and the degree bookkeeping closes: Ψ lands in degree
  < n_m = deg g, matching Φ₂'s first slot. Multiplicativity Res(AB, C) =
  Res(A, C)Res(B, C) for monic A, B is standard and correctly invoked. ✓
- The coker-length remark (length = v_p(det) for an injective map of equal-rank
  free ℤ_p-modules) is the standard Smith-form fact; injectivity follows from
  pairwise coprimality (det = ±ΠRes ≠ 0). ✓
- Numeric: harness T0, 10/10 (v_p(det Φ) = ρ on the whole battery), re-run
  confirmed. No finding.

### V1.2 Lemma 2 (Smith-profile constancy) — VERIFIED

The two-sided minor-valuation argument is airtight:

- Entries of Φ_h are ℤ-polynomial in the coefficients of the h_i, so every
  k×k minor of Φ_h ≡ the corresponding minor of Φ_f mod p^τ. ✓
- d_k(f) ≤ d_n(f) = ρ < τ (partial sums of sorted nonnegative e_i, Lemma 1 at
  f). A minor attaining d_k(f) has valuation < τ, hence its h-counterpart has
  the SAME valuation (congruence mod p^τ preserves valuations < τ exactly),
  giving d_k(h) ≤ d_k(f). ✓
- The converse direction correctly handles the adversarial case where a
  DIFFERENT minor attains d_k(h): if d_k(h) < d_k(f) ≤ ρ < τ, the attaining
  h-minor's valuation transfers exactly back to f, contradicting minimality of
  d_k(f). ✓
- Profile = consecutive differences of the d_k (determinantal-divisor theorem
  over the PID ℤ_p, standard); Σe_i = ρ; e_max ≤ ρ. Well-definedness of the
  n-term profile at h: d_n(h) = ρ < ∞ forces det Φ_h ≠ 0, i.e. injectivity —
  the order of reasoning is sound (minors first, injectivity as a consequence).
  ✓
- Independent numeric check this pass (see header): profile constancy holds on
  random polydisc samples at the ρ = 3 wild pair. No finding.

### V1.3 The T-bijection absorption (Theorem 1, Steps 1–4) — VERIFIED

- Step 1 (parametrization): the fiber ↔ {b̄ ∈ (ℤ/p^M)ⁿ : (⋆)} bijection is
  correct. Difference of two monic degree-d_j polynomials ≡ f_j mod p^τ lies
  in (p^τℤ/p^N)[x]_{<d_j} ≅ (ℤ/p^M)-vectors; the |S|=1 / |S|≥2 split of the
  product expansion is exact; Q(p^τb) = p^{2τ}Q̃(b) with Q̃ having ℤ_p
  coefficients (since |S| ≥ 2); division by p^τ converts the mod-p^N condition
  to (⋆) mod p^M; both Φ_h(b) and Q̃(b) mod p^M depend only on b mod p^M
  (ℤ_p-coefficient polynomial maps), so the condition is well-posed on
  classes. ✓
- Step 2: Smith form Φ_h = UDV with the exponents pinned fiber-independently
  by Lemma 2 — this is the load-bearing use of the new mechanism and it is
  used correctly (U, V, S may vary with the fiber; only (e_i) must not, and
  the final count depends only on (e_i) and M). Multiplying by U^{−1} ∈
  GL_n(ℤ_p) and substituting c = Vb preserves solution sets mod p^M. ✓
- Step 3 (T well-defined + injective): τ − e_i ≥ τ − ρ ≥ 1, so T is defined.
  The injectivity argument is correct: the finite-difference factorization
  P(c) − P(c') = Σ(c_i − c'_i)G_i(c, c') with ℤ_p-coefficient G_i is valid on
  representatives and descends (the capped valuation v_p(·) := min(v_rep, M)
  is representative-independent in the relevant range); δ_i =
  −p^{τ−e_i}(S_i(c) − S_i(c')) gives w ≥ min(M, 1 + w), forcing w ≥ M.
  Injective on a finite set ⇒ bijective. ✓
- Step 4 (the count): for e_i ≤ M, p^{e_i}c_i + p^τS_i(c) = p^{e_i}T(c)_i in
  ℤ/p^M identically, and p^{e_i}X ≡ 0 mod p^M ⟺ X ∈ p^{M−e_i}(ℤ/p^M); for
  e_i > M both terms vanish (τ > ρ ≥ e_i > M), the constraint is vacuous, and
  G's i-th component is correctly all of ℤ/p^M. Solution set = T^{−1}(G),
  #G = p^{s(M)}, bijectivity transfers the count. ✓
- Step 5 (blindness) and Corollary 1(a)–(c): the min-valuation propagation
  through G-membership, the unimodular V, and the p^τ rescaling are all
  correct (v ≥ τ + (M − e_max) = N − e_max); the fiber-saturation argument
  μ_N^{−1}(Σ) = ΠC_j and the class-count Π_j p^{(N−K_j)d_j} (each depth-K_j
  class of a keyed C_j inflates by exactly p^{(N−K_j)d_j} inside A_j(N),
  using K_j ≥ τ) check out. ✓
- Numeric: T1 (24/24, including all sub-guard levels), T2 (23/23) re-run
  confirmed; T2 tests exactly the ≥-direction that Theorem 1(iii) claims.
  No finding.

### V1.4 Theorem 2 at every N ≥ τ — proof VERIFIED; range claim see Finding 1

The proof is correct at every N ≥ τ at which its hypotheses can be
instantiated: the four preimage identities (μ_N^{−1}(Σ) = ΠC_j;
μ_N^{−1}(Σ∩S_j) = ΠC_i ∩ pr_j^{−1}(Ẽ_j), including the `univ` option via
Ẽ_j = A_j(N); μ_N^{−1}(Σ∩⋂S_j) = Π(C_j∩Ẽ_j)) each verified in both
inclusions; all four preimage sets are fiber-saturated because C_j, Ẽ_j are
keyed at depth ≤ N − e_max and fiber members agree to that depth (Theorem
1(iii)); constant fiber size φ = p^{s(M)} (Theorem 1(i)) converts preimage
counts to φ × image counts; and both sides of the product law expand to
φ^{−m} Π_j #(C_j ∩ Ẽ_j) · (Π_i #C_i)^{m−1} — the φ-cancellation is exact and
value-independent, as claimed. Empty degeneracies consistent; m = 1, 2, ≥ 3
all fine; N = τ degenerates correctly. The §4.3 guard arithmetic (a)–(c) all
checks under (I-τ): N ≥ thr+2ρ ⇒ N ≥ τ(c)+ρ ≥ τ(c)+e_max and N−e_max ≥
N−ρ ≥ thr+ρ ≥ K. No ∀-by-example anywhere: all five proofs are fully general;
the numerics are presented as falsifiers, not as justification. The RANGE
advertisement "every N ≥ τ" is where Finding 1 lives.

### V1.5 The D-8 buffer value-vs-law distinction — DEFECTIVE AS NARRATED
(Finding 1)

## §V2 Findings

### Finding 1 — JUSTIFICATION GAP (the charged D-8 value-vs-law separation
collapses under the document's own definitions; every affected displayed
theorem remains true)

Quotes:

> §1: "A subset C ⊆ A_j(N) is **keyed at depth K** (τ ≤ K ≤ N) if membership
> depends only on g mod p^K."

> §4.2 Remark (1): "consequently the product law holds at EVERY N ≥ τ under
> (A1)–(A3), with no lower N-guard beyond read depth."

> §4.3(d): "the guard's 2ρ(c) buffer is what makes the fiber VALUE p^{ρ(c)}
> and gives the reads ρ(c) headroom, not what makes the law true."

> §5.2: "the PRODUCT LAW carries the (I-τ) read-depth guard; the FIBER-VALUE
> clause carries the N ≥ thr + 2ρ guard; below it the value is p^{s(M)} —
> still constant, still cancelling."

> §0: "the product law needs only the read-depth guard, and the 2ρ buffer
> buys the explicit fiber value p^ρ (§5.2)."

The defect: keying is DEFINED only for depths K ≥ τ (§1, quoted above), and
(A3) demands K_j ≤ N − e_max; hence an adapted presentation exists **iff
N ≥ τ + e_max, i.e. M ≥ e_max — which is precisely Theorem 1(ii)'s condition
for s(M) = ρ**. Consequently:

  (i) Theorem 2's "at every level N ≥ τ" is VACUOUS on τ ≤ N < τ + e_max
      (whenever ρ ≥ 1): no adapted presentation exists there, so the range
      advertisement overstates without being false.
 (ii) In EVERY nonvacuous instance of Theorem 2, the fiber constant is
      already φ = p^ρ. The §5.2 regime "law holds with value p^{s(M)} ≠ p^ρ,
      still cancelling" is EMPTY: the product law's effective threshold and
      the fiber-value-p^ρ threshold coincide exactly at N = τ + e_max. What
      the 2ρ(c) buffer buys beyond that shared threshold is read headroom
      only — §4.3(d)'s attribution "is what makes the fiber VALUE p^{ρ(c)}"
      is a misattribution (the value is p^ρ at every level where the law can
      be stated at all, buffer or no buffer).

Concrete anchor (from the harness, re-run this pass): at B10 (p = 3, ρ = 3,
e_max = 2, τ = 4), fibers of size p^{s(M)} ≠ p^ρ occur only at N = 4, 5 —
levels where N − e_max < τ, so no cell/event read is legal and no product-law
instance exists; the first law-legal level N = 6 already has fiber p³ = p^ρ
(the harness itself labels N = 6 "(GUARD)").

Why GAP and not CRITICAL: every displayed theorem (Theorem 1, Corollary 1,
Theorem 2, §4.3(a)–(c)) is true as stated, and the sub-guard claims are true
(the vacuous ones vacuously; Theorem 1(i)'s sub-guard fiber counts genuinely
and non-vacuously — that part of §5.2/OL-4 is real). The genuinely
constant-but-≠p^ρ sub-guard FIBERS exist; only their pairing with a stated
product law does not. The narrative is recoverable by widening "keyed" to
allow depths K < τ (e.g. C_j = A_j(N) as a depth-0 set — Theorem 2's proof
only needs fiber-saturation at depth ≤ N − e_max, not K ≥ τ), but that is not
the definition on the page, and Corollary 1(c)'s class-count formula
Π p^{(N−K_j)d_j} would then need repair (it uses K_j ≥ τ). Downstream
consumers are unaffected: §5.3's audit and §4.3(b)–(c) operate at or above
the full guard.

### Finding 2 — JUSTIFICATION GAP (minor; external transport claim consumed
without display)

Quote (§1):

> "Box-side counts: at the pinned chart each monic F mod p^N corresponds to
> exactly one box point pattern of its n·N coefficient digits, so all
> cardinalities below transport verbatim to box counts (M07 brief §2.1)."

This transport is consumed at §4.3(b) ("box counts = coefficient-class
counts, §1") but rests on an external document; the target file, read
standalone, displays neither the pinned chart nor the correspondence. Minor:
§4.3 is in any case conditional on the displayed open interface (I-τ), and
the honesty ledger (§8) fences the engine-side application correctly — but a
standalone reader cannot check clause (b)'s box-count phrasing from this
document alone.

## §V3 Minor notes (below finding threshold)

- §4.1's "E_j keyed at depth K_j" is a category slip: E_j is a set of
  depth-K_j reads (residue tuples), for which §1's keying notion (defined for
  subsets of A_j(N)) does not literally apply; the intended meaning
  (Ẽ_j := read-preimage is keyed at K_j) is unambiguous and is what the
  Theorem 2 proof uses.
- §4.1's S_j = {F̄ : ε(F̄)_j-read ∈ E_j} is only defined on μ_N(ΠA_j(N)),
  though S_j is announced as a subset of "the ambient level-N monics";
  harmless — only Σ ∩ S_j is ever counted.
- Corollary 1's hypothesis "τ ≤ K_j ≤ N − e_max" silently presupposes
  N ≥ τ + e_max for instantiability — the same phenomenon as Finding 1, noted
  here because Corollary 1 at least displays the K_j ≥ τ bound that (A3)
  leaves implicit.
- §7's "T2 … fiber blindness exactly mod p^{N−e_max}": the harness tests the
  agreement (≥) direction, which is all Theorem 1(iii) claims; "exactly"
  refers to the predicted modulus, not to sharpness. No overclaim consumed.

## §V4 What was NOT verified (out of scope, correctly fenced by the document)

K-FACT (GMN citation perimeter), (I-τ)/K-LOC (displayed open interface),
OL-2, the §6 item-27 repair shape, and the §8 literature-novelty flags. The
document's own conditionality display for these is accurate and consistently
maintained (§0, §4.3, §5.3, §8) — no unconditional engine-level claim is made
anywhere.

## VERDICT: SOUND-WITH-GAPS

All five charged targets have correct proofs as displayed: Lemma 1, Lemma 2
(the new mechanism is airtight and correctly load-bearing), the T-bijection
absorption, and Theorem 2's proof at each instantiable level, with the
falsifier suite reproduced 68/0. The two findings are justification gaps, not
breaks in the logical chain: (1) the advertised sub-guard value-vs-law
separation (§0/§4.2 R1/§4.3(d)/§5.2) is narrated over a regime that is empty
under the document's own keyed-depth definition — the law's and the
value-p^ρ's effective thresholds coincide at N = τ + e_max, so the 2ρ buffer
buys read headroom only; (2) the box-count transport is an undisplayed
external dependency. No critical error; no ∀-by-example.
