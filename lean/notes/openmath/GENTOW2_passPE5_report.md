# GENTOW2 passPE5 — HOSTILE VERIFIER REPORT (fresh context), 2026-08-10

**VERDICT: [PENDING — fresh route in flight]**

Target: lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md at HEAD
(d798529; md5 399017ac32aac64e14c2bff5083c2c4d), the r3-repaired note
(arc: seal → PE1 → r1 → PE2 → r2 → PE3 CLEAN 1/2 → rider → PE4 NOT
CLEAN [B-2 machine-refuted letter-live, counter reset 0/2] → r3 =
commits 117b2c0/8d62554/acdf97a/d798529). PE4 report + all r3 commits
read first. Charge: quote-and-classify, fix nothing; CLEAN bar =
nothing GAP-or-worse; counter restarts only on CLEAN.

## A1. LEMMA GENTOW2-B″ RE-DERIVED (attack 1) — HOLDS

Re-derivation done independently this pass, then compared:

* **γ-calculus.** Value-0 Laurent monomials x^i π^a Φ′^b: value
  equation ih₁e₂ + ae₁e₂ + bu₂ = 0; mod e₂ forces bh₂ ≡ 0 (u₂ =
  e₂V₂ + h₂; gcd(h₂,e₂) = 1 — PDF p.16 top line re-read this pass)
  so e₂ | b; quotient by γ₂^{b/e₂} (an x,π,Φ′-monomial via π₂ =
  x^{ℓ₁}π^{ℓ′₁}) leaves value-0 x^{i′}π^{a′} = γ₁^{i′/e₁}
  (gcd(h₁,e₁) = 1). Residues z₁, z₂ via Def 3.12 + Prop 1.15 through
  the C-m1 bridge (PE4-vetted). ✓ Re-derived, matches S5.2.
* **Proof steps (i)–(iv).** (i) Cor 4.7(2) iteration: quote [Q8]
  carries no degree hypothesis; each peeled factor's grade (κ̄, 0)
  ∈ Γ₂ ✓; y-degree 0 by Cor 4.4(3) (s = s′ = 0 single-point
  polygon; layout L1088 re-read: "deg Ri,α(g) = ⌊s′(g)/ei⌋") ✓.
  (ii) Def 1.8 defines ν by the Φ₂-expansion minimum — verified
  VISUALLY on PDF p.5 this pass ✓; every term in P_{β_t}(µ₃), Cor
  4.7(1) additivity ✓. (iii) the dichotomy: e₃ ∤ j → jλ₃ ∉ Γ₂
  (gcd(h₃,e₃) = 1) while ν(Q_j) ∈ Γ₂ (deg < m₃ Φ₂-free, Prop 1.9(2)
  + µ-minimality — PDF p.6 visual ✓), value ∉ Γ₂ ∌ β_t; e₃ | j →
  eq (14) puts the term at y-degree j/e₃ ≥ 1 ✓; ν > β_t → Lemma
  3.17 kills ✓. (iv) G(x₀) = Q₀(x₀) (x₀ a Φ₂-root, Φ₂-adic
  expansion) → digit(Q₀) = res(ẑ)·res(N^d/M) = ϑ(t)·ϑ(t)^{−1} = 1
  ≠ 0; B-1 in scope (deg Q₀ < m₃) gives exactness; B′(3) gives
  R_{3,β_t}(Q₀) = u(β_t) ✓. Equating y-degree-0 parts in F₃[y] is
  valid (polynomial identity, graded by y-degree). **The proof
  goes through.**
* **LD/LP1 numbers re-derived by hand this pass.** LP1: γ₁ = x²/2,
  γ₂ = Φ′²/x⁹ (ℓ₁ = 1, ℓ′₁ = 0, u₂ = 9); N²/M = xΦ′²/32 ↦ lattice
  split (1,−5,2) = 1·(−9,0,2) + 5·(2,−1,0) → res = z₂z₁⁵ = z₁²
  (z₂ = 1, z₁³ = 1) = ϑ(0)^{−1}; ϑ(0) = z₁ ✓ = decode COC pin.
  Predicted P: LD1 y²+z₁y+z₁, LD2 y²+z₁y+1 ✓ = decode MP1/MP2.
  ϑ(1) = 1 (d = 1, M = N) ✓. LD3 single trivial slot ✓. Also
  checked: the decode division identity r3² = res(k̂₁/N)r3 +
  res(k̂₀/N²) is exact algebra at a Φ₃-root, and res(k̂₀/N²) =
  c₀·ϑ(0) — the decode frame measures ϑ with w quotiented, as the
  note says.

## A2. RESTATED LEMMA GENTOW2-B + ADMISSIBILITY (attack 2) — HOLDS

* ψ₃^{(w)} := w^{f₃}ψ₃(y/w) = y^{f₃} − Σ a_t w^{f₃−t} y^t: monic ✓,
  deg f₃ ✓, constant w^{f₃}ψ₃(0) ≠ 0 ✓, irreducible (y ↦ y/w is a
  K₂[y]-automorphism substitution; a factorization would pull back)
  ✓. THEOREM GENTOW2-A's hypothesis set is exactly {monic
  irreducible, deg f₃ ≥ 1, ψ(0) ≠ 0} + (i)/(ii) — it accepts
  ψ₃^{(w)} for EVERY w ∈ K₂^×; its quantifier is "ANY monic Φ₃ with
  (i)+(ii)" (PE4 walked this assembly end-to-end; spot-checked
  here). ✓
* Prescription algebra: c_t = ϑ(t)^{−1}a_t → u(β_t)c_t =
  ϑ(t)w^{f₃−t}ϑ(t)^{−1}a_t = w^{f₃−t}a_t → R = y^{f₃} −
  Σ a_t w^{f₃−t}y^t = ψ₃^{(w)} ✓ exact. c₀ ≠ 0 ⟺ a₀ ≠ 0 ✓; digit
  supply = T(b)′(iii) lifts ✓.
* Consumers: the S4 consumption note consumes clauses (c)+(d) only
  (level-2 data, w-free); residue field F₃[y]/(ψ₃^{(w)}) ≅
  F₃[y]/(ψ₃) (root scaling by w ∈ F₃) — factor patterns and degrees
  w-invariant. No downstream site found that consumes the literal
  digit-string spelling. ✓

## A3. FLIPPED HONESTY BOX / w-BLINDNESS (attack 3) — ARGUED, with
## one inventory-drift residue (m2)

The chain is argued, not asserted: B′(5) + B″(6) give realized =
w^{f₃}P(y/w); B″'s Consequently states P's irreducible-factor
pattern is attained for every w (substitution automorphism); and
#primes ↔ #distinct residual factors is the Lemma 5.3(2)/Thm 6.6
surface (PDF-verified in PE4's [F1] walk). The box's re-reading of
the 13-witness record ("supports ϑ = 1 at its own tested slots,
structurally w- and z₁-blind") is accurate — indeed conservative:
by the γ-calculus, ϑ ≡ 1 is FORCED on letter-dead geography (z₁ =
z₂ = 1 kills every letter monomial), and the two standing witnesses
with z₂ ≠ 1 potential (N1: f₂ = 2) have f₃ = 1 (trivial cocycle),
so the record could not have constrained a γ₂-leg either way — the
r3's own suggested fresh surface, taken below. Residue: the Thm 6.6
leg lives in the PE4 report and S8's T2 disclosure, not in the
note's S6.1 inventory — folded into finding m2.

## A4. NEW PDF ROWS 20–22 (attack 4) — ALL MATCH, both legs re-run

* Row 20, Lemma 3.13(1): layout L836–840 ✓ + PDF p.16 VISUAL ✓ —
  "µᵢ(πᵢ) = 1/e(µᵢ₋₁), µᵢ(πᵢ₊₁) = 1/e(µᵢ)"; eq (11) on the same
  page displays the stability µᵢ(πᵢ₊₁) = µⱼ(πᵢ₊₁) that C-m1's
  "EXACT stable value" clause rides. MATCH.
* Row 21, Def 1.8: layout L250–255 ✓ + PDF p.5 VISUAL ✓ — the
  augmented valuation IS defined by the φ-expansion minimum
  (µ′(g) = min µ′(gₛφˢ)), exactly B″ step (ii)'s consumption. MATCH.
* Row 22, Prop 1.9(2): layout L258–261 ✓ + PDF p.6 VISUAL ✓ — "µ(g)
  = µ′(g) if and only if φ ∤µ g". The note's instantiated gloss
  ("Φ₂-free ⟹ ν = µ₂") adds the one-step µ-minimality bridge
  (deg < deg φ ⟹ φ ∤µ g), which is FGMN Lemma 1.3(4)/p.5 territory
  — acceptable instantiation, noted in m2's species. MATCH.

## M. MACHINE-LEG INTEGRITY — ALL PINS EXACT, 5/5 RE-RUNS
## BIT-IDENTICAL, TAUTOLOGY AUDITS NEGATIVE

* **Pins at HEAD (13/13 exact):** PDF da846c82f1fcb619cefb3feb8164191e;
  checks.py 2603eb7c / run2 832aa838; pe1 a70dd986/e66e8ea5; pe2
  f2d6f1fa/d26cacf5; r2 probe d0c0ebeb/b79121a2; pe3 9755cce9/6bbb87f8;
  pe4_fresh ab0d3d5d/2b596b7e; pe4_decode 3f0cb151/50d7b17f.
* **Seal chains of the r3-load-bearing PE4 instruments verified:**
  pe4_fresh blob at seal 23def87 = HEAD blob (md5 ab0d3d5d);
  runner-only commit; output-only at 253ba13 (kept as-is, RED 62/9).
  pe4_decode blob at seal 90f50af = HEAD blob (3f0cb151); output-only
  at af9a19f (GREEN 14/0). First-run-under-seal on both.
* **Isolated re-runs (fresh /tmp copies), 5/5 BIT-IDENTICAL:**
  gentow2_checks 41/0 exit 0; r2_letter_probe 21/0 exit 0; pe3_fresh
  50/0 exit 0; pe4_fresh 62/9 RED exit 1 (the by-design nonzero exit;
  output byte-equal to the committed artifact); pe4_decode 14/0 exit 0.
* **Tautology audit, pe4_decode (the instrument B″ cites — never
  before audited):** GP leg computes r1/r3/m1/m0/coc via independent
  nfmodpr reads; expectations docstring-literal; DISCRIMINATING
  paired checks (MP1 vs MP2 and MULT0R1 vs MULT0ONE both computed
  per frame with opposite expected truth values). No circularity.
* **Tautology audit, pe4_fresh:** A-route = own exact integer
  arithmetic (expansions by monic division, dv-ladders, Bareiss
  resultants); B-route = PARI factorpadic + per-factor
  nfinit([·,[2]]) + idealprimedec/nfeltval/nfmodpr; predictions
  docstring-literal, sealed pre-run. The 9 violations are all
  B-2-derived predictions (self-implicating by design, disclosed).
  No circularity.
* r3 commits touch ONLY the note (.md) — sealed artifacts
  byte-untouched through r3, as S11 claims. ✓

## F. FRESH ROUTE — [section completed after the sealed run; see
## below]

## G. GRADE LINE — [pending]
