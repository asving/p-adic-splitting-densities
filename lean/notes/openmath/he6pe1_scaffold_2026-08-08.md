# HE6-PE1 ORCHESTRATOR PRE-VERDICT KEY (written BEFORE reading any Codex output)

Timestamp: written immediately after brief assembly, before/at launch, before any Codex
output was read. Purpose: decorrelation per the CODEX_WMULTDCX precedent — my own
independent verification key for the four mandated attack points + free-hunt candidates,
derived by hand from HE6_PROOF_2026-08-08.md, GENHN S3/S4, HE3 S1/S3-S6.

## Attack point (1): LEMMA HE6-1 Step 1 — MY VERDICT: SOUND (all algebra re-derived)

- Bound dv(B(xi)) >= m − (D′−1)ε: from min_i(e₁v(b_i)+i·dv(ξ)) = min_i(e₁v(b_i)+ih−iε)
  ≥ m − (D′−1)ε since i ≤ D′−1. ✓
- Case dv(ξ) ≥ h: δ = D′h EXACT by HE6-0 (both subcases: v(ξ)>h/e₁, or =h/e₁ with T2
  failing). t=d term = Φ′(ξ)^{ℓd}, dv = ℓdD′h exact. t<d: (d−t)u + ℓtD′h > ℓdD′h using
  u = ℓκ > ℓD′h. Unique strict min ✓.
- Case dv(ξ) < h: excess_t ≥ (d−t)u − (D′−1)ε + ℓtD′dv(ξ) − ℓdD′dv(ξ)
  = (d−t)ℓ[κ − D′dv(ξ)] − (D′−1)ε = (d−t)ℓ[(κ−D′h) + D′ε] − (D′−1)ε
  ≥ ℓ(κ−D′h) + (ℓD′−D′+1)ε > 0. All three displayed lines EXACT as inequalities. ✓
- CAVEAT feeding from HE6-0 (see free hunt F-A below): only the exactness δ = D′·min(dv(ξ),h)
  is consumed, and THAT clause of HE6-0 is sound; the suspect part of HE6-0's proof is the
  (T1)/(T2)-holds direction, not consumed by Step 1.

## Attack point (2): (LIFT) — MY VERDICT: STATEMENT OVERREACH AT SMALL k (real finding);
## ALL USE SITES SURVIVE

- To get dv(C) = k exactly with C ∈ O[x], some slot j must satisfy e₁v(a_j) + jh = k with
  v(a_j) ≥ 0; j ≡ i(k) mod e₁ forced (gcd(h,e₁)=1), so j = i(k)+e₁t and
  v(a_j) = (k − i(k)h)/e₁ − th ≥ 0 requires k ≥ (i(k)+e₁t)h.
- Hence for k < i(k)·h there is NO such C: (LIFT) as stated ("every k ∈ ℤ_{≥0}") is FALSE.
  Concrete: e₁ = 2, h = 3, k = 1 → i(k) = 1, needs v(a₁) = −1. Requires h ≥ 2 (invisible to
  the h = 1 machine rows).
- Use sites: DEFINITION HE6-1 uses k = (d−t)u ≥ u = ℓκ > ℓD′h ≥ D′h > (D′−1)h, so ALL f₁
  slots i(k), i(k)+e₁, …, i(k)+e₁(f₁−1) ≤ D′−1 have v ≥ 0. Surjectivity onto K: residues
  Σ_t res(a_{i+e₁t})η^t exhaust K (basis 1..η^{f₁−1}); the ϖ^k-vs-GENHN-2 normalization
  differ by a FIXED power of η (unit), so K^× is still exhausted. → classification if Codex
  finds it: statement error / justification gap; conclusion at use sites survives with the
  restriction k > (D′−1)h (or k ≥ i(k)h + e₁(f₁−1)h).

## Attack point (3): HE6-3(a) — MY VERDICT: SOUND, with one unstated finiteness lemma

- (†) derivation: ξ-side D″h_F(κ) needs every root of Ψ_κ generic (ι(r₀) of degree μ+1
  can't kill R_λ nor be a min poly of any β_ρ since deg r_ρ ≤ μ) ✓; ρ-side ε(ρ) = 0 same
  reason ✓.
- FINITENESS (unstated): f and Ψ_κ = Ψ_{κ,r₀} cannot share a root — a shared ρ would have
  min poly of β_ρ = ι_ρ(r₀), degree μ+1 > μ ≥ deg r_ρ, contradiction. So Res ≠ 0 and both
  sides finite. The note never says this → candidate JUSTIFICATION GAP (easily closed).
- c₀ bookkeeping: c₀ := −D′Σ_{λ≤D′h}L_λλ correct after moving n_λ = 0 (from HE6-0 + HE3-0's
  (T1)/(T2), sound) terms; affine identity on rationals in (D′h, λ₁) (nonempty since
  λ₁ > D′h) forces Σc = 0, c₀ = 0; slopes are > 0 (dv(A_j) ≥ (μ−j)S+1 > 0 = dv(A_μ), lower
  hull decreasing; DEFINITION 1 pins u,ℓ > 0) so L_λ = 0 ✓. (b) triangular elimination in
  gaps ✓.

## Attack point (4): HE6.B scope — MY VERDICT: THE EXCLUSION IS NOT EXACTLY THE COMPLEMENT
## (real finding, the sharpest of the four)

Node configurations at a terminal/intermediate read:
 (i) ℓ = 1, repeated LINEAR factor: stage-α refine, HE3-2(b)+HE3-3, HE6 §S6.3 — covered ✓.
 (ii) ℓ = 1, repeated irreducible factor of DEGREE ≥ 2, mult ≥ 2: a stage-CS event with
  inner data (1, deg r, m), e₁′f₁′ = deg r ≥ 2 (HE3 §S6.3). NOT excluded by HE6.B's wording
  ("ℓ ≥ 2 carrying a repeated residual factor") and NOT covered by THEOREM HE6.A (R_λ
  inseparable). Its only handling is HE3's stage-CS recursion — and HE6 §S7.1's OWN
  criticism ("the recursion computes the factorization of the resolvent F over R, whose
  roots are not roots of f (Y ↦ Φ′ is not a ring map), so the inner class SIZES are not
  transported") applies verbatim at e₁′ = 1 too. → the crack: HE6.B should exclude ALL
  stage-CS events (equivalently all repeated residual factors that are not K-rational-linear),
  not only ℓ ≥ 2 ones; OR §S7.1's counting-half criticism is overdrawn — either way the
  "exactly" claim fails. Expected classification: CRITICAL for COROLLARY HE6.B's scope
  sentence (the theorem HE6.A itself is untouched).
 (iii) ℓ ≥ 2 separable: THEOREM HE6.A ✓ (the closed box).
 (iv) ℓ ≥ 2 repeated: excluded (HE6-BOX-1) ✓ honest.
Note: HE6.B's identification "excluded histories = GENHN-T(a)'s stage-CS events with inner
e₁′ = ℓ ≥ 2" is internally consistent with (iv) but silently passes over (ii).

## Free-hunt candidates (mine)

F-A. HE6-0, third case ((T1)/(T2) hold ⟹ dv(Φ′(ξ)) > D′h): the parenthetical converse
  "v(ξ−θ_i) = h/e₁ would force res((ξ−θ_i)/ϖ^h·unit) ≠ 0, i.e. η_ξ ≠ η_{θ_i}" is FALSE
  per-i: counterexample e₁ = 3, Q ≡ 1 mod 3, Φ′ = x³ − ẑπ, ξ = ζ₃θ(1+w): η_ξ = η_θ yet
  v(ξ−θ) = h/e₁ exactly (ξ is close to the OTHER root ζ₃θ). The conclusion is TRUE and
  provable cleanly via GENHN-2's tie clause at Φ′'s own lattice slots (residual = ψ,
  ψ(η_ξ) = 0 ⟹ cancellation ⟹ dv > D′h), but the note's per-i residue argument is broken.
  Expected: JUSTIFICATION GAP (conclusion survives; proof-display error). NOTE: Step 1 of
  HE6-1 consumes only the OTHER cases of HE6-0 (exactness when (T1)/(T2) fail), which are
  sound; HE6-3(a)'s n_λ = 0 for λ ≤ D′h consumes "(T1)/(T2) ⟹ > D′h" — the flawed leg —
  so this gap feeds attack 3's perimeter.
F-B. (RES) finiteness in HE6-4: if f and Ψ_{λ,r} share a root the display is ∞ = ∞; but a
  shared root IS a root of f carrying the label (HE6-1), so S_{λ,r} ≠ ∅ anyway — gap at
  worst, one line.
F-C. HE6-2/2′ residue-transport ("same universal polynomial in η"): sound given the fixed
  ϖ-convention (twist = fixed η-power, identical at θ and ξ); watch whether Codex flags the
  wrap bookkeeping.
F-D. HE6-5: ι_{gρ} = ḡ∘ι_ρ composition — sound; ε(ξ) definition needs δ's denominator | ℓ
  (fine at labels).
F-E. THEOREM HE6.A step 4: e·f = [L:K₀] for complete discretely-valued L/K₀ with finite
  residue field ✓ classical; orbit-size ≥ N_r from HE6-0′ + f separable (disc ≠ 0) ✓.
F-F. ϖ-convention: a₀ may be NEGATIVE (e₁ = 2, h = 3 → ϖ = x·π^{−1}), so ϖ ∉ O[x]; all
  uses are evaluations at nonzero points / normalizations, so harmless — but "ϖ := x^{i₀}π^{a₀}"
  presented as if integral could draw a flag; and (LIFT)'s res(C(θ)/ϖ(θ)^k) is well-defined
  regardless.

## Predicted grade outcome

Survives as: THEOREM HE6.A sound modulo repairable gaps (F-A proof display; (LIFT) k-range);
COROLLARY HE6.B's scope sentence needs a REPAIR (case (ii) crack) — the honest statement is
"histories whose stage-CS events are all... none", i.e. exclusion must cover ℓ = 1 repeated
non-linear residuals too (or re-derive them via the order-2 key at integer height, which is
exactly the §S7.2 machinery = same box). HE6-BOX-1 as a mathematical residue is therefore
slightly WIDER than stated: the (LIFT₂)/(SLOT₂) program covers both ℓ = 1 and ℓ ≥ 2 repeated
non-linear cases.
