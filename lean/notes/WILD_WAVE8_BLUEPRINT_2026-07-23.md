# WILD_WAVE8_BLUEPRINT — class-3 phase 1: the development bijection (D1-marginal) in Lean
*(2026-07-23. The general-n program's first step, per the accepted note
`MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` §8 wave order item 4: "only after Case E passes
and D1 is proved on paper for one deg φ = 2 order-1 read". BOTH preconditions are met:
Case E PASSED 2026-07-23 (`verification/case_e_gate.py`, commit ad5c02e — count 3/64 exact
at N = 2,3,4 in original coordinates; 36/36 type certificates (2,2)); §1 below is the
D1-marginal paper proof. Status: DRAFT pending Codex pass on §1.)*

## §0. Where this sits in the general-n program

The n = 2 uniformity capstone (`montes_uniform_n2`, W6q) is done. The note's general-n
perimeter has exactly one genuinely open counting ingredient: **OPEN-D1**, the
development-digit ledger for deg φ ≥ 2 reads, in two strengths:
- **D1-marginal** (ONE read): the φ-adic development digits of a single cluster read count
  exactly — pure counting, proved in §1 below. This unlocks depth-0 class-3 strata
  (Case E's kind) in Lean.
- **JOINT-D1** (all reads of a depth-≥1 history jointly): still OPEN; the note's
  non-import #12 discipline applies — if it resists pure counting, STOP and report; never
  axiomatize it. NOT needed for phase 1.

Phase 1 (this wave, W8a): the development bijection + the Case-E stratum machine-checked —
the exact W5a pattern (land the bijection first, everything else builds on it).
Phase 2+ (scoped in §3, not executed here): the (2,2) leaf master over the unramified
base, menu/axiom re-scope #7 for class-3 literals, the depth-0 class-3 density legs, and
— the long pole — joint-D1 or its honest conditional carry.

## §1. Math ground truth: D1-marginal at one deg-φ = 2 order-1 read (proof)

**Setting.** p any prime; φ = x² + sx + t ∈ ℤ_p[x] monic quadratic (the canonical lift of
an irreducible φ̄ over F_p; irreducibility is NOT used in this section — the bijection is
purely algebraic). f = x⁴ + c₃x³ + c₂x² + c₁x + c₀ monic quartic. The φ-adic development
is the unique expansion f = φ² + a₁·φ + a₀ with deg a₁, deg a₀ ≤ 1, obtained by two
divisions by the monic φ. Write a₁ = a₁₁x + a₁₀, a₀ = a₀₁x + a₀₀.

**Lemma D1m (unitriangular development).** In the coordinate order
(c₃, c₂, c₁, c₀) ↦ (a₁₁, a₁₀, a₀₁, a₀₀), the development map Ψ is an AFFINE map over ℤ[s,t]
whose linear part is lower-unitriangular; explicitly:

  a₁₁ = c₃ − 2s
  a₁₀ = c₂ − s·c₃ + (s² − 2t)
  a₀₁ = c₁ − s·c₂ + (s² − t)·c₃ + (2st − s³)
  a₀₀ = c₀ − t·c₂ + st·c₃ + (t² − s²t)

*Proof.* Two long divisions by the monic φ. First, f = q₁·φ + a₀ with q₁ = x² + q₁₁x + q₁₀:
matching coefficients top-down, q₁₁ = c₃ − s and q₁₀ = c₂ − t − s·q₁₁ = c₂ − s·c₃ + s² − t;
then a₀₁ = c₁ − s·q₁₀ − t·q₁₁ and a₀₀ = c₀ − t·q₁₀, which expand to the displayed forms.
Second, q₁ = 1·φ + a₁ gives a₁₁ = q₁₁ − s = c₃ − 2s and a₁₀ = q₁₀ − t = c₂ − s·c₃ + s² − 2t.
Each aᵢⱼ is cᵢ' + (ℤ[s,t]-linear in the earlier c's) + constant, with the diagonal
coefficient 1 as displayed. ∎

**Corollary D1m-count (exact cylinder transport).** For every N ≥ 1, Ψ induces a BIJECTION
of (ℤ/p^N)⁴ (an affine map with unitriangular linear part has determinant 1, and Ψ has
ℤ[s,t]-coefficients, so it commutes with reduction mod p^N). Hence for EVERY subset
S ⊆ (ℤ/p^N)⁴ of development digit-vectors:

  #{ f mod p^N : (a₁₁, a₁₀, a₀₁, a₀₀) mod p^N ∈ S } = |S|.                        (D1m)

Development-digit conditions count EXACTLY their nominal cylinder volume — nothing about
the conditions is used (no independence, no shape restriction); the entire content is the
unitriangular change of coordinates. ∎

**Corollary D1m-CaseE (the gate's ledger; N ≥ 2 REQUIRED** — at N = 1 the
height-1 digit is unavailable and the exponents below go negative; Codex pass-1 gap,
confirmed sufficient**).** The Case-E stratum (root read f̄ = φ̄², i.e.
all four aᵢⱼ ≡ 0 mod p; v_Gauss(a₀) = 1 exact with nonzero height-1 digit pair; and
v_Gauss(a₁) ≥ 1) is the cylinder S with: a₁'s two coordinates ≡ 0 mod p (count p^{N−1}
each), a₀'s two coordinates ≡ 0 mod p with height-1 digit pair ≠ (0,0) (count
(p² − 1)·p^{2(N−2)} = (Q−1)·Q^{N−2} pairs, Q := p²). By (D1m):

  count = Q^{N−1} · (Q−1)·Q^{N−2},   mass = (Q−1)·Q^{−3}.                          (★)

At p = 2: 3/64, i.e. 12 of 256 at N = 2 — the machine-verified gate values. ∎

**Remarks for the Lean statement.**
1. The Gauss valuation v(a₀) = min(v(a₀₁), v(a₀₀)) and the "unit F_Q-digit" condition is
   exactly "the height-1 digit PAIR is nonzero" — no F₄-field structure is needed for the
   COUNT (the field structure enters only at the faithfulness/leaf-reading stage, phase 2).
2. The bijection statement is for FIXED φ (fixed s, t). The general-n, general-deg-φ
   analogue (division tower by several monic keys) has the same block-unitriangular
   structure — stated as the expected phase-2 generalization, NOT proved here; phase 1
   needs only the displayed 4-variable instance.
3. What D1m does NOT give: reads at depth ≥ 1 of a class-3 history recenter/rescale INSIDE
   the previous read's fiber; the joint ledger (all reads simultaneously free) is the open
   JOINT-D1. The Case-E stratum is depth-0, fully covered by D1m.
4. Empirical status: (★) verified EXACTLY at p = 2, N = 2,3,4 by census in original
   coordinates (the gate), which exercises precisely the Lemma-D1m mechanism.

## §2. Lean wave plan — W8a (the development bijection + the Case-E stratum)

One new leaf module `OM/DevBijection.lean` (purely additive, general p), the W5a pattern:
- `devMap (s t : ℤ_p or ZMod-level) : the affine equiv` — implement at the BOX level:
  for each N, an `Equiv` of `(ZMod (p^N))⁴` given by the four displayed forms (linear part
  unitriangular ⟹ explicit inverse by back-substitution; provide both directions and the
  `Equiv` laws by `ring`-style algebra), PLUS the genuine-coefficient level: for monic
  quartic f over ℤ_p, the development components as ℤ_p-polynomial expressions in
  (c₃, c₂, c₁, c₀) with the division identity f = φ² + a₁φ + a₀ PROVED (`ring` after
  expansion), and the box-commutation (toZModPow of the genuine components = devMap of the
  toZModPow coefficients).
- Check first whether `OM/Development.lean`'s φ-adic development can be consumed for the
  genuine-level identity (it formalizes the development in the classifier's vocabulary);
  if its form is awkward for the explicit 4-variable instance, prove the identity directly
  (self-contained `ring`) and add a compatibility remark — do NOT modify Development.lean.
- `CaseECell (N) (a : fourBox p N) : Prop` — the (★) cylinder in development coordinates;
  `card_caseECell : count = (p²−1)·p^{2N−4}·p^{2(N−1)}`-form (organize the exponent
  bookkeeping as in ChainMenuU's card lemmas; require N ≥ 2);
- `card_caseE_originalCoords` — THE point: the same count for the ORIGINAL-coordinate
  fiber {f-box : devMap applied to it ∈ CaseECell} via the equiv (the D1m-count transport,
  a `card_comp_equiv` application);
- Gates: p = 2, N = 2 count = 12 (`decide` or `Nat.card` evaluation); the p = 3 count at
  N = 2 (= (9−1)·9⁰·9¹ = 72? compute: (Q−1)Q^{N−2}·Q^{N−1} at Q=9, N=2: 8·1·9 = 72) as a
  second decide gate; the mass form 3/64 at p = 2 as a ℚ-identity.
- AxCheck: all core-only. No sorry. No axiom. NOTE: this module makes NO type/leaf claim —
  keying/faithfulness is phase 2; the docstring must say so (honest scope).

## §3. Phase 2+ scoping (named, not executed)

- **W8b**: the (2,2)-leaf master over the unramified base: f irreducible /ℚ_p with every
  bundle forced to (e,f) = (2,2) on the Case-E stratum — the Lean analogue of the gate's
  W-factorization argument; assets: `UnramifiedBase.lean` (O'' = AdjoinRoot g), the
  compData/affine transport bank. Then menu/axiom re-scope #7 (class-3 literals at a fresh
  head; per-literal statement map = GMN Thm 2.11/Def 2.12 + order-1-in-φ Cor 1.20 reads —
  the citations are already pinned for order ≤ 1 in φ-degree ≥ 2 form per the W4c mixed
  work; the guardian will audit the delta).
- **W8c**: the depth-0 class-3 density legs at n = 4 (the Case-E stratum joining a
  four-degree menu — sits alongside the landed W4 mixed-e strata).
- **The wall, honestly**: depth-≥1 class-3 chains need JOINT-D1. Two honest routes only:
  prove it (pure counting — the note's belief) or carry the affected strata as explicit
  conditional legs (the W5-era pattern). Decision AFTER W8a/b land; non-import #12 stands.

## §4. Definition of done (W8a)

1. `OM/DevBijection.lean` green, core-only, no sorry; the division identity and the equiv
   proved, not assumed.
2. Gates: p=2 N=2 count 12; p=3 N=2 count 72; the 3/64 mass identity.
3. Census: capstones byte-identical (additive module).
4. Blueprint §1 Codex-verified before dispatch; docs/log updated at landing.

---

## §5. ADDENDUM (2026-07-23, post-Case-F): JOINT-D1 — the conjectured mechanism, now
empirically pinned at depth 1

**Case F (the depth-1 joint-D1 probe) PASSES** (`verification/case_f_gate.py`, N = 5):
n = 4, p = 2, the history ⟨root read ḡ²; descend read at φ = x²+x+1, slope −1, square
residual with center c̃ ∈ F₄ˣ; child key φ' = φ + 2ĉ, ĉ the minimal-support lift⟩:
- F0: first-read stratum mass EXACTLY 3·2^{−10} (nominal product);
- F1: child cluster v(a₀') ≥ 3, v(a₁') ≥ 2 on the whole stratum (heights 2m+1, m+1 at
  m = 1 — the deg-2-key staircase frame);
- F2 (the crux): per fixed c̃, the child digit vector (a₀'/8, a₁'/4 windows) is EXACTLY
  UNIFORM (all 256 buckets of size 4 at N = 5) — the joint ledger is product-exact;
- F3: the child ram-leaf (v(a₀') = 3 exact) product count exact per c̃;
- bonus: the child (v(a₀'), v(a₁')) distribution is exactly geometric (ratio 4 per step)
  — the child H-ladder.

**The mechanism (to prove — the campaign's next math task).** Volume bookkeeping from
F0/F1: mass(S_c̃) = 2^{−4}·2^{−6} = 2^{−10} = vol{v(a₀') ≥ 3 ∧ v(a₁') ≥ 2}. Together with
F2-uniformity this pins the statement:

> **Conjecture J1-step (the class-3 descend bijection).** For fixed history values (fixed
> c̃, hence fixed ĉ and φ' = φ + p^m·ĉ), the re-development map
> Θ_ĉ : (a₁, a₀) ↦ (a₁', a₀') is an affine bijection with ℤ_p-coefficients (composition
> of the D1m unitriangular map at φ' with the inverse at φ — both proved-shape), and it
> maps the parent descend stratum S_c̃ (root-read + slope-m square-residual-center-c̃
> digit conditions) BIJECTIVELY onto the child cluster box
> {v(a₀') ≥ 2m+1, v(a₁') ≥ m+1} — the deg-φ = 2 analogue of the n = 2 whole-window
> staircase bijection (note Lemma 2.3 / Lean `RecenterBox.stratumPairEquiv`).

If J1-step holds (with its general-m, general-deg-φ block form), JOINT-D1 follows by
iterating: each descend re-enters a fresh child cluster box measure-exactly, so the
digits of successive reads are jointly free — the depth-1 chain rule (R2) the note asked
for, in bijection form. Proof plan: explicit matching-coefficients computation of Θ_ĉ
(the φ' = φ + p^mĉ substitution + one re-reduction of the deg-2 cross terms ĉ·a₁, ĉ²
by φ' — all ℤ[s,t,ĉ]-affine, expected unitriangular in the height filtration); then
inclusion Θ_ĉ(S_c̃) ⊆ child box (the F1 computation, done above symbolically for m = 1:
a₀'-pre = p^{2m}(ĉ² + w) − p^mĉ·a₁ with (ĉ² + w) ≡ 0 mod p by the center equation) +
volume equality ⟹ bijection. When stuck: smaller/explicit cases per the directive
(vary m, p = 3, deg ψ = 2 children where deg φ' = 4).

**Campaign order (updated):** (i) J1-step proof on paper + Codex passes; (ii) W8b (the
(2,2) leaf master + re-scope #7) in parallel — Lean work independent of J1; (iii)
J1-step in Lean (the W5a pattern again); (iv) D3/D5 (the n ≥ 3 deg-1-key analogues —
expected to fall to the SAME bijection mechanism, which is how Lemma 2.3 proved the
whole-window case); (v) the general-n menu/assembly waves; (vi) the depth⟹disc Montes
axiom (boundary #6, pre-audited form) for general-n exhaustion — guardian audit
required, as for every axiom touchpoint (directive: semantic audits maintained
throughout).

**§5.1 Sign correction (2026-07-23, caught while deriving Θ_ĉ symbolically).** The
general-p child key is φ' = φ − p^m·ĉ (complete the square: on S_c̃, f ≈ (φ − c̃p^m)²;
then digit_{2m}(a₀') = c̃² + c̃·(−2c̃) + c̃² = 0 for ALL p). The + sign used in
`case_f_gate.py` is p = 2-benign only (the discrepant term 4c̃² gains v₂ ≥ 2). The Θ_ĉ
matching-coefficients derivation (all four explicit component formulas, unitriangular,
≡ id mod p^m) is drafted; MANDATORY next gates before the J1-step write-up is trusted:
(i) Case F at p = 3 with the minus sign (odd-p joint uniformity), (ii) the symbolic
inclusion Θ_ĉ(S_c̃) ⊆ child box re-checked at odd p with the corrected sign, (iii) the
same at a deg ψ = 2 child (deg φ' = 4) — the other class-3 descend species.
