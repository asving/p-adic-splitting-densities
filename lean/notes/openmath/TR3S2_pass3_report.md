# TR3-S2 hostile pass 3 (Fable, fresh context) — 2026-08-02

**Target:** `lean/notes/openmath/TR3S2_2026-08-08.md` at REVISION 1 (commit 5844572) +
`verification/openmath/tr3s2_check.py` + `tr3s2_check_run3_output.txt`.
**Independence:** pass-1 and pass-2 reports NOT read (only the note's own REVISION-1
summary of pass 1, which is part of the target text). Upstream consulted: accepted
TR3S1_2026-08-08.md (genre + inherited pins) and GRB_ORDER2_2026-08-05.md (S3.4
REV-11 statement of record; R2.3 TR-3-ORD-X display). The corrupted
/tmp/litunit/fgmn.txt was NOT consulted; all FGMN displays checked against the
TR3-S1 accepted pins and their recorded non-textual legs.
**Method:** full pass, every step of the compose chain re-derived by hand; the four
named attack surfaces (KEY0, WIT, rescoped divergence, EXP/ordinate bookkeeping)
re-derived independently; one full instance hand-walked on a twist-visible tower
never used by me before; script code-audited line-by-line and re-run (reproduced
byte-identically); all counts reconciled against note, run-1/2/3 logs, and the
recorded strata_probe output.

**VERDICT: CLEAN — 0 critical errors, 0 justification gaps.**
Five non-classifiable observations recorded at the end (none blocks acceptance;
none alters a claim's stated scope or strength).

---

## 1. The compose chain, step by step (all verified)

### S1 pins (inherited + the two genuinely new consumptions)
* (12-int₁)/(12-int₂), the normalized Bézout pair as displayed hypothesis, the
  corrected ǫ₁(β) = z₁^{ℓ₀′s(β)−ℓ₀u(β)}, Def 3.16 at both levels, Def 3.18,
  (SLOT-gen), w₁/w₂, GMN 2.19–2.21 + (18) + Def 2.5 — checked against the
  ACCEPTED TR3-S1 pin block; the e₀-generalizations are exactly the displayed
  ones. Def 2.5 ⟹ v₂ = w₁ recomputed: v₂(P) = e₀·min_m(w₀(b_m)+mh₀/e₀) = w₁(P). ✓
* (SLOT-gen) re-derived: µ₂(φ₂) = w₂^F(φ₂)+λ₂ = g₀h₀ + h₁/(e₀e₁) = γ₂/E₂, so
  β_j = e₀(α − s_jγ₂/E₂) = (γ − s_jγ₂)/e₁; integrality from γ ≡ s(γ)h₁,
  γ₂ ≡ h₁, s_j ≡ s(γ) (mod e₁). ✓ Degenerates to TR3-S1's (SLOT) at e₀ = 1. ✓
* The level-1 dilation claim (Γ₁ = (1/e₀)ℤ, β = e₀α, (s(α),u(α)) = (s(β),u(β))
  under u·e₀+s·h₀ = e₀α) checked: FGMN's eq-(12) at level 1 with
  (e₁,h₁)^F = (e₀,h₀), e(µ₁) = e₀ is verbatim (12-int₁). ✓

### S2 (σ-identifications at general e₀)
* σ₀ untouched by e₀ ✓ (level-0 data e₀-free; (RES0) verbatim).
* σ₁ well-definedness: A-GEN at a = Φ₁ (degree-free scope note honored);
  j₀ = ⌊s₁(Φ₁)/e₀⌋ = m₀(Φ₁) since s₁ = s(β)+m₀e₀, 0 ≤ s(β) < e₀ ✓.
* Monicity upgrade recomputed: top Φ₀-digit of the monic degree-e₀g₀d₀ lift is
  b_{e₀g₀} = 1 (any higher digit would force deg ≥ e₀g₀d₀ + something);
  ordinate e₀·0 + e₀g₀h₀ = β on-line, and e₀g₀ is the maximal development
  abscissa ⟹ it is the FINAL on-line abscissa ⟹ leading coefficient 1 at
  stride-index (e₀g₀−s₁)/e₀; lawful degree g₀ ⟹ s₁(Φ₁) = 0; s(β) = 0 from
  s(β) ≡ ℓ₀e₀g₀h₀ ≡ 0 (mod e₀); monic associate of monic ψ₀ = ψ₀. ✓
  No circularity: A-GEN targets K₀[y] through σ₀ only. ✓ (SQ) is the quotient
  construction, verbatim accepted genre. ✓

### S3 Lemma A-GEN (attack surface B) — re-derived in full
* (A1-gen) slot weights: δ_{m′} = β/e₀ − (s(β)+m′e₀)h₀/e₀ = u(β) − m′h₀ using
  e₀u(β) = β − s(β)h₀. Re-derived; matches TR3-S1's β−mh₀ at e₀ = 1. ✓
* (A2-gen) domain: at read abscissas, β − mh₀ = e₀δ_{m′} exactly, so
  w₀(b_m) ≥ δ_{m′}. ✓
* (A3-gen) dichotomy incl. δ < 0 and b_m = 0 corners: reduction of a poly with
  all-positive-valuation coefficients is 0; on-line nonvanishing from
  deg b_m < d₀ = deg φ̄₀. ✓
* (A3.5-gen): on-line ⟹ mh₀ ≡ β (mod e₀) ⟹ m ≡ ℓ₀β ≡ s(β); least-residue
  normalization puts every on-line m in the progression with m′ ≥ 0; Def 3.16's
  print sums over ALL j ≥ 0 (pin), so no on-line abscissa escapes. ✓
* (A4-gen): same argmin set on the GMN side (their component = minimizers of
  e₀w₀(b_m)+mh₀); on the line the GMN ordinate u_m = w₀(b_m) = δ_{m′}, so the
  values agree via (RES0); window off-line abscissas are 0 on both sides;
  re-indexing gives y^{m₀}·R₁(a)(y). ✓

### S4 Lemma EXP (attack surface, S9.1) — recomputed independently
Multiply by e₀, substitute e₀u = β − sh₀:
LHS·e₀ = e₀ℓ₀′s − ℓ₀(β−sh₀) + (s₁−s) = s₁ − ℓ₀β + s(ℓ₀′e₀+ℓ₀h₀−1) = s₁ − ℓ₀β.
RHS·e₀ = s₁ − ℓ₀β − ℓ₀Se₀g₀h₀ + e₀ℓ₀g₀h₀S = s₁ − ℓ₀β. Both = the S-free
integer (s₁−ℓ₀β)/e₀ (integer by s₁ ≡ s ≡ ℓ₀β mod e₀). ✓ The (18)-ordinate term
−ℓ₀S·e₀g₀h₀/e₀ cancels the character term +θS EXACTLY — this is the whole
twist mechanism, and it is correct. t₁-integrality at u_S = β+Se₀g₀h₀ follows
(mod-e₀ kill of the S-term). ✓ e₀ = 1 degeneration: (EXP) reads m₀ = s₁,
matching accepted TR3-S1's t₁ = s₁ collapse. ✓
Consumption sites audited per S9.1: ǫ₁ takes the (12-int₁) data OF β_j; t₁
takes the ordinate u_{s_j} = β_j + s_j·e₀g₀h₀ (= w₁(a)+s_j·w₁(Φ₁) on-line).
Both correct at the S5(ii) chain and in the harness (eps1(gj) vs
t1 = (s1 − l0·umap[sj])/e0). ✓

### S5 theorem (support, per-slot, assembly)
* (i): e₁u_i + ih₁ = e₁w₁(a_i) + iγ₂ two-liner recomputed; on-line congruence
  i ≡ s(γ); FGMN slot-on-line ⟺ w₁(a_{s_j}) = β_j is the same equality via
  (SLOT-gen); j₀ = (s−s(γ))/e₁ = ⌊s/e₁⌋. The FGMN/GMN polygons share the
  argmin set (the shear by i·v₂(φ₂) is absorbed into the same minimized
  quantity), so FGMN's Def-3.18 abscissa s(f) = GMN's s₀(f). ✓
* (ii) off-line: read digits satisfy e₀w₀(b_m)+mh₀ ≥ w₁(a) > β_j ⟹ dichotomy
  0; covers a = 0, β_j < 0, and abscissas outside GMN's window; domain
  w₁(a_i) ≥ β_i from γ = min. Both sides 0. ✓
* (ii) on-line chain: σ₁(ǫ₁(β_j)) = z̄^{ℓ₀′s−ℓ₀u} → (SQ) → A-GEN(b) gives
  z̄^{(ℓ₀′s−ℓ₀u)+m₀}·R₁(a)(z̄) → EXP at (β_j, S = s_j) rewrites the exponent
  as t₁(s_j) + θs_j → GMN Def 2.20. Every link re-derived. ✓
* Nonvanishing: deg a < deg Φ₁ ⟹ Φ₀-digits at m ≤ e₀g₀−1 ⟹ y-degree
  ≤ ⌊(e₀g₀−1−s)/e₀⌋ ≤ g₀−1 (recomputed: e₀g₀−1 = e₀(g₀−1)+(e₀−1));
  a nonzero K₀-polynomial of degree < g₀ = deg ψ₀ cannot vanish at z̄. Support
  exactness both sides follows. The degree bound is consumed exactly here and
  nowhere in A-GEN — scope note honest. ✓
* (iii): re-indexing and the y^{j₀} division (initial slot nonzero, Def-3.18
  j₀ = ⌊s/e₁⌋ agrees with the observed leading index) give
  σ₁(R^F₂(f))(y) = z̄^{θs}·R_λ(f)(z̄^{θe₁}y). Algebra checked:
  z̄^{θ(s+ke₁)} = z̄^{θs}(z̄^{θe₁})^k. ✓

### Lemma WIT (attack surface B of the charge) — re-derived in full
* (W1): u(β) = (β−s(β)h₀)/e₀ ≥ (β−(e₀−1)h₀)/e₀ ≥ (g₀−1)h₀ for
  β ≥ (e₀g₀−1)h₀; both β¹ = W and β⁰ = γ₂+W qualify. ✓
* (W2): the displayed sum IS a Φ₀-development (abscissas s(β)+ke₀ ≤ e₀g₀−1
  distinct, digit degrees < d₀, exponents ≥ 0 by (W1)); every included digit
  sits at level-1 value exactly β (e₀(u−kh₀)+(s+ke₀)h₀ = e₀u+sh₀ = β), so
  w₁(a) = β with on-line set {s+ke₀ : x_k ≠ 0}; deg a ≤ e₀g₀d₀−1 < deg Φ₁. ✓
* The k₋-cancellation recomputed: t₁ = (s(β)+k₋e₀−ℓ₀u)/e₀ = t(β,u)+k₋ and
  R₁(a)(z̄) = z̄^{−k₋}x (the k < k₋ basis terms vanish by minimality of k₋),
  so c^G = z̄^{t(β,u)}·x — the shift cancels EXACTLY; x ↦ c^G is multiplication
  by a fixed unit, hence the K₁*-bijection/freeness claim. ✓
* (W3): both t's integral — ℓ₀u₀ ≡ ℓ₀β⁰ and ℓ₀u₁ ≡ ℓ₀β¹ (mod e₀) since the
  ordinate increments carry the factor e₀. ✓
* (W4) slot arithmetic recomputed: ordinates u_0 = γ₂+W, u_{e₁} = W+e₁e₀g₀h₀;
  values e₁(γ₂+W) on BOTH (using γ₂ = e₁e₀g₀h₀+h₁); no other digits ⟹
  component = the segment, on-line set exactly {0, e₁}, γ = e₁(γ₂+W),
  s(γ) = 0 (γ ≡ 0 mod e₁), s₀ = 0, d = 1; the pre-twisted targets give
  c^G_0 = x⁰, c^G_{e₁} = x¹ on the nose. ✓ Works at e₁ = 1 and at e₀ = 1. ✓

### S5 Remark 2 (units-only refutation)
Re-derived sharper than displayed: for the WIT f at x⁰ = x¹ = 1,
σ₁(R^F₂(f)) = 1 + cy and R_λ(f) = 1 + y; any σ₁′ = τ∘σ₁ gives coefficients
(1, τ(c)), and σ₁′(R^F₂(f)) = u_f·R_λ(f) forces u_f = 1 and τ(c) = 1 ⟹ c = 1
(τ injective, τ(1) = 1) — a SINGLE witness kills it. The note's displayed
ratio argument reaches the same conclusion (see Observation 1 on its wording).
The refutation's scope "every state with c ≠ 1" is exactly right, and at
c = 1 states the two-form is itself units-only (S7 bullet) — consistent. ✓

### S6.1 (TR-3'-GEN(ii) closure)
Checked against the GRB leaf S3.4 REV-11 text verbatim: clause (ii) is the
conjectured corrected-ǫ twist law, UNTESTED (N-1 deferral (b)); the theorem
delivers the executed threading with the closed form; inputs = the same
(GR-B-STR) ladder TR3-S1 consumed. The two-stratum closure display carries
"attempt grade for the (ii) half pending hostile passes" — honest. The ∼-form
consumer clause is correctly rescoped to c = 1 states (I checked the
converse: at c ≠ 1 the WIT witness breaks associates-∼, so "exactly at
c = 1" is right at state level). ✓

### S6.2 step 0 + Lemma KEY0 (attack surface A) — degree accounting recomputed
KEY0: (1) deg Φ₂^h = e₁g₁·deg Φ₁ ⟹ development abscissas ≤ e₁g₁ ⟹
s′ ≤ e₁g₁. (2) Side read has degree exactly d (both end slots on-line with
nonzero coefficients by S5(ii), development digits satisfy the degree bound);
σ₁ coefficientwise iso + side read = ψ₁ ⟹ d = g₁. (3) s₀ = s′ − e₁g₁ ≤ 0 and
s₀ ≥ 0 ⟹ s₀ = 0, s′ = e₁g₁, window [0, e₁g₁]. (4) two-form at s₀ = 0 reads
ψ₁(y) = R_λ(Φ₂^h)(cy) ⟹ R_λ(Φ₂^h) = T_{c⁻¹}ψ₁, coefficients ψ₁_k·z̄^{−θe₁k}.
All four steps re-derived; the pass-1 silent input (s₀ = 0) is now a displayed
consequence, correctly. ✓ Twist-visibility criterion checked: monicized
T_{c⁻¹}ψ₁ has coefficients ψ₁_k·c^{g₁−k}; ∼ ψ₁ fails iff some k < g₁ has
ψ₁_k ≠ 0, c^{g₁−k} ≠ 1 — exactly the displayed criterion, and exactly what
the (c-iii) meter implements. ✓

### S6.2 steps 1–3 + (ORD-INV)
* Step 1: top digit 1 at abscissa e₁g₁, on-line (e₁u + e₁g₁h₁ = e₁g₁γ₂
  recomputed); lawful degree forces s₀(Φ₂) = 0; inner data R₁(1) = 1,
  s₁(1) = 0 give c^G_{e₁g₁} = z̄^{(0−ℓ₀e₁g₁e₀g₀h₀)/e₀} = z̄^{−θe₁g₁}
  (integrality manifest); ∼ψ₁ + leading-coefficient comparison pins
  R_λ(Φ₂) = z̄^{−θe₁g₁}ψ₁; two-form at s₀ = 0 gives
  σ₁(ψ₂^F) = z̄^{−θe₁g₁}·T_cψ₁. ✓ (KP_i) consumption displayed. ✓
* Step 2 chain: T_c automorphism preserves ord under simultaneous label/argument
  rescaling; scalars change nothing; step-1 + two-form substitution; σ₁-iso
  invariance. Each equality justified; this is also why ord-consumers survive
  the twist — correctly displayed. ✓
* (ORD-INV): matched-label form; both instantiations (GMN-lawful, harness key)
  are proved by the same transport; labels stay irreducible (automorphism
  image / scalar of an irreducible). ✓
* Step 3: Cor 5.15 with [T]-properness NOT discharged — displayed, inherited
  exactly as accepted TR3-S1. Conditionality display "(KP_i)+[T]" present at
  the theorem line AND the consumer line. ✓
* R2.3 cross-check: the leaf's TR-3-ORD-X ties labels by clause (3)
  "ψ_i ∼ R_λ(Φ_{i+1})" — i.e. the GMN-LAWFUL key; S6.2 executes exactly that
  case, so the note's claim to prove R2.3's displayed form is faithful, and
  the step-0 display is an ADDITION (consumer warning), not a weakening. ✓
  GD3-MIN Route B / clause-(4) sit on TR-3-ORD-X and GD3-FULL/OL-B on
  TR-3'-GEN per the leaf's own routing — the note's consumer lines match. ✓

### Rescoped key-divergence claims (attack surface C) — site sweep
Grepped every "diverge/bifurcate/universal" site: S0 verdict line + table row,
S6.2 step 0 (pre-revision claim quoted in place), the mismatched-pairing
sentence (fails exactly on twist-visible; 214 all on the 20), the consumer
note, S7 bullets, S8.2 narrative, S9 items 5/7, and the two adjacent
rescopes (S6.1 ∼-form clause; S6.2 step-1 leading coefficient). ALL carry the
twist-visible criterion or the c ≠ 1 scope; NO site claims universal
divergence at e₀ ≥ 2; no dependent claim assumes it (ORD-INV and all
consumer services are matched-label / convention-displayed). The script's
run-1 historical text is bracket-annotated as OVERBROAD with the correct
criterion — consistent. ✓

### S6.3, S7 (scope box)
S6.3 inherits S6.2 with the same conditionality — consistent with TR3-S1 S6.3's
accepted wording extended to all order-2 states. ✓ S7's eight bullets checked
against the body: each names its exact non-claim (depth ≥ 3, σ_j family,
normalization scope with the S1 transformation law — itself re-derived:
t₁ ↦ t₁ − qu_i and u_{s+ke₁} = u(f)−kh₁ give R'_λ(y) = z^{−qu(f)}R_λ(z^{qh₁}y);
units-only refutation scope; key-convention leaf-fold deferral; D-ITER hard
fence — verified: no ITER-LAW/anchor/cocycle object appears in S2–S6; DVR
scope; degree scope). ✓

## 2. Independent hand-walked instance (my own, not from any harness)

Tower: d₀ = 1, (e₀,h₀,g₀) = (2,1,2), (e₁,h₁,g₁) = (2,1,1) over ℤ₂;
K₀ = F₂, ψ₀ = y²+y+1, K₁ = F₄ = F₂(ω); ℓ₀ = 1, ℓ₀′ = 0, θ = 2, c = ω⁴ = ω ≠ 1
(twist-visible). Φ₀ = x, Φ₁ = x⁴+2x²+4 (w₁(Φ₁) = 4 ✓, R_{λ₀}(Φ₁) = 1+y+y² = ψ₀ ✓),
γ₂ = 9. WIT witness at x⁰ = x¹ = 1: W = 3, β⁰ = 12, β¹ = 3; t(β⁰,u₀) = −6,
t(β¹,u₁) = −5; a₀ = realize(ω⁶ = 1, 12) = 2⁶; a₁ = realize(ω⁵ = ω², 3) = x³+2x;
f = 64 + (x³+2x)Φ₁². Computed BOTH sides by hand:
* GMN: γ = 24, on-line {0,2}, c^G_0 = z̄^{−6}·1 = 1, c^G_2 = z̄^{−5}·(1+ω) = 1;
  R_λ(f) = 1 + y. (WIT delivers the equal-nonzero pair. ✓)
* FGMN: β_j = 12−9j; slot 0: ǫ₁(12) = z₁^{0·0−1·6} = 1, inner read = 1, C^F_0 = 1;
  slot 1: ǫ₁(3) = z₁^{−1} = ω², inner read (1+y at m₀ = 0) at z₁ = ω², C^F_1 = ω⁴ = ω.
* Per-slot law: z̄^{θs₁}c^G_2 = ω⁴·1 = ω = C^F_1 ✓; EXP at slot 1:
  LHS (0−1)+0 = −1 = RHS −5+2·2 ✓; two-form: 1+ωy = (1+y)|_{y→ωy} ✓;
  refutation ratios: FGMN ω vs GMN 1, factor exactly c = ω ✓.
KEY0 face on the same tower: T_{c⁻¹}ψ₁ for ψ₁ = y+ω is ω²y+ω, monicized
y+ω² ≠ ψ₁ — divergent, matching the criterion (ψ₁_0 = ω ≠ 0, c¹ ≠ 1). ✓

## 3. Script audit and reconciliation

* **Code semantics match the preregistration text**: TS2a iterates the union
  range, checks support against the fresh-GMN on-line set, then (k1) the
  INTEGER (EXP) instance, (k2) the A-GEN factorization through the fresh gmn1,
  (k3) the closed form; TS2b the assembled two-form list + length/ends + j₀
  law; TS2c (c-i) harness key = T_{c⁻¹}ψ₁ tie (KEY0's conclusion), (c-ii) a
  CONSTRUCTED GMN-lawful key with the explicit z̄^{−θe₁g₁} scalar (step 1's
  conclusion), (c-iii) the divergence meter with obs = "monicized R_λ(Φ₂) ≠ ψ₁"
  vs pred = the twist-visible criterion — the meter LABEL in the run-3 output
  is the rescoped IFF, matching S6.2 step 0 verbatim; TS2d both MATCHED
  pairings (the ORD-INV instantiations); TS2e the e₀ = 1 controls; TS2f the
  literal Lemma-WIT construction (W, β⁰, β¹, pre-twists z̄^{−t(β,u)},
  f = a₀+a₁Φ₁^{e₁}) verified through the fresh GMN side, with the two-slot
  property, equal-coefficients-at-target, side-read shape, refutation
  inequality AND the exact factor c. The twist-visible ⟹ c ≠ 1 implication is
  checked, not assumed. eq12/bezout implement the normalized hypothesis
  (hard-coded, so the family cannot falsify it — declared). fp_ord is exact
  iterated division by the monic label. ✓
* **Counts**: 68 samples/tower × 52 towers = 3,536 for TS2a/b/d; 16 controls
  × 68 = 1,088; 52 label ties; 20 WIT witnesses (32 c = 1 skipped, and the
  16+16 decomposition in S8.3 is forced: all 16 e₀ = 1 controls have θ = 0);
  TOTAL 11,768. All match the note and the log. ✓
* **Roster**: 9 e₀ ≥ 2 rows (C/D/E/H/J + K/L/M/N — NEW_ROWS checked: all
  e₀ ≥ 2, N carries g₁ = 2) + 4 e₀ = 1 controls, × 4 rings. ✓
* **Re-run (this pass)**: `python3 tr3s2_check.py` reproduced the run-3 log
  byte-for-byte (all six family rows 0; meters 20 == 20, 32 skipped, 0
  construction failures; histogram 0:3192 1:182 2:162; TOTAL 11,768;
  ALL GREEN). ✓
* **Run-1/run-2 logs**: run 1 shows exactly the note's amendment story —
  TS2a/b/e GREEN (theorem rows never red), TS2c 20/52 + TS2d 214/3,536 RED
  (234 total), the sampled violation lines all on e₀ ≥ 2 towers with the
  mismatched-label pairing; run 2 (v2, matched labels) ALL GREEN, 11,748,
  histogram identical to run 3. Note's S8.2 narrative and the "run-2 family
  rows byte-reproduced" claim verified. ✓
* **S8.1 recorded strata_probe rows**: A0 0/20,828, A1 0/7,255, A2 0/4,297,
  A3 0/3,640, A5 0/1,252, A6 1,023/1,023, A7 293/293, CERT 0/344 — all match
  the recorded strata_probe_output.txt; the tail of that log is FAMILY B
  (D-ITER), correctly NOT consumed. ✓
* **Extraction discipline**: fgmn.txt never consulted; the corrected Def 3.15
  consumed with N-1's T0/P3/P12 legs (inherited, as declared). The freshly
  consumed GMN t-formula/(18) at e₀ ≥ 2 carries: the N-1 layout re-extraction
  (single unprimed ℓ), the S4 integrality re-derivation, and the A0 20,828-
  sample integrality meter. I checked the integrality leg genuinely
  discriminates: the ℓ↔ℓ′ misreading gives t' = (s₁−ℓ₀′u)/e₀, which at
  (e₀,h₀) = (2,1) reads s₁/2 and FAILS integrality at any odd s₁ — realizable
  — so a misread formula would have violated GMN's own printed integrality
  and the sealed meter. The residual exposure is honestly flagged (S9.8). ✓

## 4. Observations (non-classifiable; no fix required for acceptance)

1. **S5 Remark 2 wording**: "ratios of corresponding coefficients are
   invariant under both per-argument scalars and any relabeling" is loose —
   under relabeling the ratio transforms by τ (as the same sentence's
   parenthetical τ(x)/τ(y) = τ(x/y) states); "invariant" holds only for the
   scalar leg. The operative kill is correct and even understated: a SINGLE
   equal-coefficient witness forces τ(c) = 1 ⟹ c = 1, no "for all such f
   simultaneously" needed. Conclusion unaffected.
2. **S6.1 "proves exactly this"**: the REV-11(ii) conjecture's wording was
   "the discrepancy is the corrected weight-driven unit ǫ threaded per slot";
   what is proved is the closed form the threading YIELDS (z̄^{θs_j} per slot,
   after GMN's own t-twist is accounted). The note displays the closed form in
   the same sentence, so no misdirection — but "exactly" is a genre-match on
   an informal conjecture, not a formula-match.
3. **TS2f preregistration timing** is attested (script ADDENDUM "preregistered
   BEFORE run 3") but not machine-checkable: the addendum and the run-3 log
   land in the same commit (5844572). Same procedural limitation as previously
   accepted units; the run-1 → run-2 amendment IS separately evidenced by the
   recorded run-1 log.
4. **S8.3's "32 = 16 e₀ = 1 controls + 16 e₀ ≥ 2 instances"** decomposition is
   not printed by the harness (which prints only "skipped: 32"); it is forced
   arithmetic, and correct.
5. **KEY0 is hypothesis-conditional on the FGMN-normalized key's existence**
   (side read = ψ₁ exactly); existence rides the harness build (N-1 T5,
   TS2c c-i, 52/52) and realize1's guarantee, not a displayed lemma. Since
   KEY0 is a consumer-warning display (the divergence direction) and ORD-INV's
   proved instantiations do not need existence beyond the tested builds, this
   is scope-honest as written.

## 5. Verdict

**CLEAN — 0 critical, 0 justification gaps** (third pass; first Fable pass on
REVISION 1). The compose chain (S2–S5), both new lemmas (EXP, A-GEN), the
REVISION-1 additions (KEY0, WIT, the twist-visible rescope at every site), the
consumer displays (S6.1–S6.3 with (KP_i)+[T] inherited), the scope box, and
the full falsifier record are verified, including an independent hand-walked
twist-visible instance and a byte-identical re-run of the preregistered
falsifier (11,768 samples, 0 violations).

— pass 3 verifier (Fable, fresh context), 2026-08-02
