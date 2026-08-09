# HE7 ANNEX-PASS #2 — HOSTILE VERIFIER REPORT (the acceptance attempt, scoped to the annex stack)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 2 MINOR (new), scoped to the annex
stack; pass-1's M-1 verified by machine recount (47 + 55 = 102) and judged
NON-BLOCKING (run-record sentence, arc precedent).** Both committed machine
legs re-run isolated BIT-IDENTICAL (results-JSON leaf-diff EMPTY, timing
leaves included); the fresh route (four new axes at once: p ∈ {3,11},
n = 24 / μ₃ = 3, dual-PLUS-non-PARI oracle, i = 3 symbolic) is GREEN with
0 violations on first run. Per the charge: **the annex stack is ACCEPTED
2/2 — the Codex CHALLENGE on HE7 is FULLY DISCHARGED**, the first complete
challenge-to-discharge cycle of the ratification program. HE7 is fully
frozen including both annexes; dated appends only.

**Pass:** HE7-ANNEX-PASS-2, fresh context, zero prior stake, 2026-08-09.
**Target:** the ANNEX STACK of `HE7_PROOF_2026-08-08.md` ONLY — ANNEX F-1
(a4a91ee/7b3f0f1: ANNEX-LEMMA HE7-13′ + `he7annex_supp.py`) and ANNEX R
(f3ca2f1/f2fbcf0: ANNEX-DEF HE7-2′, R1-a/R1-b/R1-c/R1-d, R2-a, riders
R3–R5, `he7rannex_supp.py`). The frozen body's 2/2 was NOT at stake.
Pass-1 (`HE7_annexpass_report.md`, 4a613d8) was CLEAN with 1 MINOR,
unrepaired (no annex round between passes); stack counter stood 1/2.
Protocol: quote-and-classify, fix nothing. Context read: annexes in full;
body §S1 (frame + both CONVENTIONs + (SLOT₂)/(LIFT₂)), §S2 (HE7.B/HE7.D
statements), §S3, §S4.2–4.3, §S5 (HE7-3/4/5/7, S5.3 Step 2, S5.8), §S6;
`CODEX_HE7RAT_2026-08-09.md`; pass-1's report; all four runners.

---

## S1. FINDINGS

### MINOR (2 new)

**M-A (ANNEX R, R1.3 — instrument mislabel in the machine-leg record).**
Quote (R1.3, pre-run design paragraph): "every member is scored against
PARI `factorpadic` on the actual degree-16 polynomial (the ANNEX F-1
leg's deg-16 oracle with the p-maximal hint)". The committed runner
(`he7rannex_supp.py` de5ba60c, line 78) imports and calls `pari_sigma16`
— PARI global `factor` + `nfinit([F,[p]])` + `idealprimedec` — and
`factorpadic` is called NOWHERE in the stack; the runner's own docstring
says "factorpadic-EQUIVALENT oracle" (its P2), which the note text
dropped to "factorpadic". *Failure scenario:* an instrument auditor
reading R1.3 concludes the R leg used a different PARI algorithm (local
ROUND4) than the F-1 leg (global factorization + Buchmann–Lenstra
decomposition), i.e. that the stack carries intra-PARI oracle diversity
— it carries none: all three stack legs (both annex legs and pass-1's
fresh leg) import the single shared `pari_sigma16` implementation.
*Scope:* one record sentence; the parenthetical already names the true
route; no number, σ, or verdict moves. The substance the mislabel
gestures at is now MOOT: this pass's fresh leg ran actual `factorpadic`
(plus a non-PARI check) on every re-generated member of both legs —
all agree (§S4, W1). *Repair owed:* reword to "the F-1 leg's
factor+idealprimedec oracle (factorpadic-equivalent)" in a dated line.

**M-B (ANNEX R, R1-d — two frozen proof-provenance clauses left
unriddered).** R1.1's preamble riders §S6's two body sentences by name
("These two replace §S6's '(SLOT). §S3 verbatim … Nothing else enters'
and '(LIFT). §S4.2 verbatim' — the sentences F1 falsified"). But the
same falsified transfer claim sits verbatim in two FROZEN STATEMENT
displays, and neither receives a rider: (i) THEOREM HE7.D's clause "all
hold, **with the SAME proofs**" (§S2) — which R1.0 itself quotes as the
incoherent claim ("§S6's 'with the SAME proofs' had no coherent
normalizer/cocycle convention"); (ii) COROLLARY HE7.B(ii)'s "THEOREM
HE7.D is proved by the induction of §S6, **whose inductive step is
exactly §S3–S5** with the substitution table". Under the annex, the
inductive step is NOT exactly §S3–S5: (SLOT)/(LIFT) are R1-b/R1-c,
which carry the θ_t bookkeeping §S3/§S4.2 lack. R1-d's own sentence
"THEOREM HE7.D holds **as stated** with DEFINITION HE7-2 read through
ANNEX-DEF HE7-2′" strictly includes the "SAME proofs" clause it cannot
mean. *Failure scenario:* a reader consuming HE7.B(ii)'s display
post-annex re-derives the proof route from the frozen sentence and
lands on the pre-annex (falsified) verbatim-transfer claim — the exact
confusion F1 named. *Why MINOR, not GAP:* the CONCLUSION strings —
what downstream consumes — are delivered intact (§S2 charge (2) below);
R1-d's colon-clause displays the corrected route two lines later; BOX-1
states the re-routing; no consumer consumes the provenance clauses.
This is rider-completeness at the annex pattern's own standard ("each
repair … naming its exact target"), same class as R3's wording-MINOR.
*Repair owed:* one dated rider line: read "with the SAME proofs" /
"exactly §S3–S5" as "with (SLOT) := ANNEX-THEOREM R1-b, (LIFT) :=
ANNEX-THEOREM R1-c, and the §S5 transfer audited per R1.2 (R1-d)".

### Pass-1's M-1 — verified, and judged non-blocking

M-1 (the "102 slot instances" sentence conflating a shared counter) was
NOT repaired between passes; no annex round occurred, so no repair was
owed yet. This pass re-verified it by machine on the re-generated
members: the corrected chain alone fires the deep letter on **47** slot
instances; the P3 tooth reader's re-reads add **55**; total **102** —
pass-1's split confirmed exactly (`he7annexpass2_fresh_results.json`,
leg W1_R). Disposition: a run-record sentence with no σ, count, or
verdict consequence; by arc precedent (HMENU3-ANNEX-A minors-only;
HE7's own r3 minors-only round holding the clean count) a record-
sentence MINOR does not block acceptance. **It does not block.** The
repair queue for the editors is now three dated one-liners: M-1, M-A,
M-B.

---

## S2. ATTACK-ORDER RECORD (the five charged surfaces)

**(1) R1-b's residue sum at g ≥ 2, walked on paper — CLEAN, and pushed
one level deeper than the charge.**

*Level-3 two-class instance (i = 2, the read at level-3 points).*
Frame (2,1,1): ϖ = x, Φ′ = x²−p, u = 5, ℓ = 2, r = Z−s (K₂ = F_p).
Level-2 datum (λ₂, r₂) = (11, r₂), ℓ₂ = 1, r₂ ∈ F_p[Z] QUADRATIC
irreducible: g₂ = 2, K₃ = F_{p²}, D₃ = 8. At ℓ₂ = 1 the recursion gives
s₂(k) ≡ 0, m₂(k) = k, so n₃ = n₂. Take k = 22: n₃(22) = ϖ^{11}
(2·11 + 5·0 = 22); the single class has TWO slots t ∈ {0,1} at heights
22 − 11t. θ₁ = n₂(11)²/n₂(22) = (ϖ³Φ′)²/ϖ^{11} = Φ′²/ϖ⁵ = Λ₁, so
ϑ₁ = β₁ = s. The sum, per (R1.2): C(ξ)/n₃(22)(ξ) =
[c₀/n₂(22)](ξ) + [c₁/n₂(11)](ξ)·[Ψ/n₂(11)](ξ)·Λ₁(ξ), residue
ι^{(3)}(γ₀ + s·γ₁·β₂). Since r₂ is irreducible quadratic, {1, β₂} is a
K₂-basis of K₃; the coordinates γ₀ and s·γ₁ lie in K₂ and vanish iff
the γ's do (s a unit) — no cancellation, exactly R1-b's display; a
ϑ-collision (ϑ₁ = 1 at s = 1) rescales one basis coordinate and is
harmless, confirming pass-1's basis-separation reading.

*Level-4 instance (i = 3): the first TWO-LETTER within-class unit.*
Tower ℓ₂ = 2 (u₂ = 21, r₂ = Z−s₂, g₂ = 1, K₃ = F_p, Φ₃ = Ψ₂ deg 8,
T₃ = 42), then ℓ₃ = 1, u₃ = 43, r₃ quadratic (g₃ = 2, K₄ = F_{p²},
D₄ = 16). Take k = 86 = m₀: n₄(86) = n₃(86) = ϖ^{19}Φ′ (86 → m₂ = 43 →
(m,s) = (19,1)); n₃(43) = ϖ³Φ′Ψ (43 → s₂ = 1, m₂ = 11 → n₂(11)·Ψ).
Direct: θ₁ = n₃(43)²/n₃(86) = ϖ⁶Φ′²Ψ²/(ϖ^{19}Φ′) = Ψ²Φ′/ϖ^{13}
= [Ψ²/(ϖ⁸Φ′)]·[Φ′²/ϖ⁵] = **Λ₂Λ₁**. Via (R1.1): τ₃(43,43) =
Λ₂^{c}·τ₂(11,11)·τ₂(22,21) with c = (1+1−0)/2 = 1, τ₂(11,11) =
(ϖ³Φ′)²/ϖ^{11} = Λ₁, τ₂(22,21) = ϖ^{11}·ϖ⁸Φ′/(ϖ^{19}Φ′) = 1 — same
answer by an independent route. Residue sum: ι^{(4)}(γ₀ + (s·s₂)·γ₁·β₃)
with ϑ₁ = s·s₂ a genuinely two-letter fixed unit, {1, β₃} a K₃-basis of
K₄ — R1-b's mechanism intact one level beyond anything in the stack.
Machine mirror: leg W0 (10,141 exact checks; W0b asserts this exact
instance; 600 multi-letter θ instances decomposed as letter monomials —
R1-a(iii) at i = 3). Also re-checked by hand: the telescoping product
collapses to θ_t exactly; (R1.2) is an exact monomial identity; R1-c's
bound arithmetic m₀ ≥ (g_i−1)u_i + bound_i at k ≥ bound_{i+1}.

**(2) R1-d's discharge chain vs the frozen conclusion strings — CLEAN
on conclusions; finding M-B on two embedded provenance clauses.**
Compared verbatim: THEOREM HE7.D's conclusion list "(SLOT_i), (LIFT_i),
the disk criterion, the two evaluation displays, the slope counts, the
nonemptiness certificate, Galois equivariance and the class-size
theorem" — R1-b delivers (SLOT_i) with the consumed clauses unchanged
("exactness, nonzero residue, residue in K_{i+1}, ξ-independence"; only
the residue COORDINATES move, γ_t ↦ γ_tϑ_t); R1-c delivers (LIFT_i)
"statement verbatim as THEOREM HE7.D's" (checked against §S2's display:
bound recursion bound_{i+1} = (L_i−1)u_i + ℓ_i·bound_i identical); the
remaining seven items route through R1.2 items 1–7, whose per-item
consumption claims I re-checked against the §S5/§S6 texts (values-only
items are twist-free; HE7-7's Step-2 display already carries the
bracket τ_t; DEFINITION HE7-3's prescription is already inverse-twisted
and R1-c absorbs any fixed K_{i+1}^×-unit; HE7-11's premise is now
well-posed since n_{i+1} is a definite Laurent monomial). COROLLARY
HE7.B(ii)'s conclusion "[GENHN-HE(μ)] holds at every leaf … complete
**modulo the arc grade of this note**" survives with its conditionality
sentence unchanged, at the annex's self-disclosed transfer-audit grade.
The two embedded provenance clauses are M-B.

**(3) The F-1 ↔ R interplay — CLEAN.** ANNEX-LEMMA HE7-13′ (committed
BEFORE HE7-2′) is a LEVEL-2 lemma: every object it manipulates — n₂,
dv₂, ι^{(2)}, (LIFT₂)'s evaluation fact, LEMMA HE7-12 — is defined
directly in §S1/§S5.8, and ANNEX-DEF HE7-2′ REPRODUCES levels 1–2
byte-for-byte (R1-a(iv), re-derived by hand: n₂(k) = ϖ^{m(k)}Φ′^{s(k)},
Λ₁ = Φ′^ℓ/ϖ^u, τ₂ = Λ₁^c). So HE7-13′'s displayed proof consumes
nothing HE7-2′ re-based. Its LEVEL-i transfer (the §S6(iii) reading)
routes through the repaired package: labels/vanishing via R1.2 item 4,
Galois stability item 5, the refine's lift via R1-c (item 6, twist
absorbed — the lift's residue is ι(s_{i+1}) in the FIXED system, which
is what clauses (b)/(c)'s residue-match and residue-subtraction
arguments need), residue additivity at fixed height is a single-system
fact (item 3's coherence). The reverse dependence — HE7-13′(a)'s f_C
convention leg needs R2-a — is rider (ii) of R2-a, closed in-stack
(pass-1 R-a). NEW machine evidence for the composition: leg W2
exercises HE7-13′ AT level-3 nodes read through the HE7-2′ chain — 17
mixed-node parkings with the translated companion residual EXACT at
entry and 18 persistent re-checks (clause (c) one level up), 11 pure
refines with the refined side gone (HE7-13 as displayed, level 3) —
the first machine contact of the two annexes composed.

**(4) The instruments — the shared blind spot CONFIRMED as a fact, then
KILLED by measurement.** Fact: all three stack legs score σ through ONE
implementation, `pari_sigma16` (`he7annex_supp.py` defines it;
`he7rannex_supp.py` and `he7annexpass_fresh.py` import it) = PARI
global `factor` + `nfinit([F,[p]])` (p-maximal hint) + `idealprimedec`.
Before this pass there was NO non-`pari_sigma16` σ-check anywhere in
the stack (the exact ℤ[x] forward reader is PARI-free but is the device
under test). This pass adds two decorrelated instruments and runs them
on every re-generated committed member and every fresh member: (o2)
PARI `factorpadic` — an algorithmically distinct route (local ROUND4
vs global + Buchmann–Lenstra) — checked on factor count, degree
multiset, and per-factor tame disc parity (all predicted e even and
prime-to-p except 3 disclosed wild fresh members, so v_p(poldisc F) ≡ f
mod 2 index-independently, which splits the degree-ambiguous pairs like
(16,1) vs (8,2)); (o3) a NON-PARI leg: sympy exact integer discriminant
of the full member, v_p(disc f) ≡ Σ f_i(e_i−1) mod 2 (tame). Result:
**96/96 + 79/79 + 48/48 triple-oracle agreement, 0 violations** (§S4).
The mislabel that would have hidden this monoculture is finding M-A.

**(5) Free hunt — no further findings.** Checked and clean: R1-a(i)
value induction (w_{i+1} = ℓ_i w_i on 𝒫_{i+1} ⊆ 𝒫_i, Λ_i value 0);
R1-a(ii) carry derivation (range (−ℓ_i, 2ℓ_i), ≡ 0 mod ℓ_i via
gcd(u_i, ℓ_i) = 1, whence c ∈ {0,1}; m-identity ℓ-multiplied); (R1.1)
expansion re-derived (Φ^{cℓ}/n_i(cu_i) = Λ_i^c at both c); R1-b Step 2
class separation (s·u_i bijection mod ℓ_i); the i = 1 degenerations
(θ_t ≡ 1, (SLOT₂)/(LIFT₂) byte-match against §S1's displays); HE7-13′
clauses (b)–(e) re-derived from the single evaluation fact incl. (e)'s
residue −ι(s₂) and its fence; the honesty box (no k = m consumption:
text + all three runners grepped); R2-a's orbit argument incl. the
refined-key leg via HE7-12(b) and BOTH consumption riders; R3's rider
direction (consumers use only the necessary direction — checked at
HE7.C's gate, HE7.B(i), §S8); R4's completed inventory against LEMMA
HE7-12(c) item (7)'s actual sentence; R5's F₈ witness ({1, β, 1+β},
size 3, no subgroup/coset — recomputed); both BOX-1 appends' claims
against the git record; "what does not move" lists spot-checked. The R
leg's `refine3` counter (34) is another shared corrected+tooth counter,
but the NOTE quotes only the correct member-level numbers (19 members,
one step each) — no finding.

---

## S3. MACHINE LEGS (isolated re-verification)

**Pins verified at pass open** (md5, committed tree): `he7annex_supp.py`
a5d00403…, `he7rannex_supp.py` de5ba60c…, `he7rannex_supp_output.txt`
6b320011…, `he7rannex_supp_results.json` aca0edc1…, `he7_pe3_probe12.py`
61d9f81c…, `he7annexpass_fresh.py` dc7ddf63… (+ output 74d75634…,
results b728a274…). **Byte-freeze verified from git:** pre-F-1 body
md5 6f2f4c75 (= file @ a4a91ee^) is a strict 100,975-byte prefix of the
current file; post-F-1 md5 85d57dfa (= file @ f3ca2f1^) a strict
124,603-byte prefix — both checked byte-for-byte. Both annexes are
strict appends.

**Committed-record reconciliation.** Every number in both annex run
records re-read from the committed JSONs: R leg 79 members / 79 PARI /
18 flips (K2 10 + K2R 8) / 19 refine-members (15 K2R + 4 K2) / genres
32+31+16 / 1 disc-discard / deep-letter 102; F-1 leg 96/96, P2 128 +
132, P4 48/48, P5 16/16, 148 refines, R-a route 32 — all match.

**Isolated re-runs** (`/tmp/he7_ap2_sandbox`, committed artifacts
untouched): BOTH legs GREEN and **bit-identical — results-JSON
leaf-diff vs the committed artifacts EMPTY on both** (timing leaves
3.5 s / 2.6 s included). F-1: 96/96, all five predictions re-fired.
R: 79/79, tooth 18/79 reproduced.

---

## S4. FRESH ROUTE — GREEN, first run, 0 violations

`verification/openmath/he7annexpass2_fresh.py` (md5 9076d68f…; output
1cc87244…; results e0258e02…), disjoint from all prior stack routes on
four axes at once (primes, degree, oracles, symbolic depth):

**W0 (EXACT, no oracle — the i = 3 / level-4 layer; pass-1's Q0 stopped
at i = 2).** Exponent-vector arithmetic over (ϖ, Φ′, Ψ, Ψ₂) for the
4-level tower (ℓ₃ = 2, u₃ ∈ {4u₂+1, 4u₂+3, 4u₂+9}, u₂ ∈ {21,23}):
n₄'s value identity at weights (8, 20, 2u₂, u₃); the (R1.1) recursion
AT i = 3 with carry c₃ ∈ {0,1}; θ_t's telescoping into τ₃-values and
the (R1.2) identity as exact vector identities; every θ_t decomposed as
a Λ-letter monomial (R1-a(iii) at i = 3; 600 genuinely multi-letter
instances); plus W0b, the §S2(1) paper-walk instance θ₁ = Λ₂Λ₁ asserted
exactly. **10,141 exact checks, 0 violations.**

**W1 (triple oracle on the committed annex legs' own members).** Both
legs' member polynomials re-generated deterministically (rng 20260809,
committed loop order — validated: the R leg's 79 σ's match the
committed rows 79/79 in order, and the F-1 leg's per-cell σ histograms
match all 8 committed rows). Every member scored by o1 = the shared
`pari_sigma16`, o2 = `factorpadic` + degree multiset + tame disc
parity, o3 = non-PARI sympy disc parity: **F-1 96/96, R 79/79
triple-agreement.** M-1 recount: deep-letter corrected-chain **47** +
tooth re-reads **55** = **102**; corrected refines 19.

**W2 (n = 24, μ₃ = 3, p ∈ {3, 11} — level 3 at a NEW degree and NEW
primes; the annexes composed).** 48 members f = Ψ₂³ + A₂Ψ₂² + A₁Ψ₂ +
A₀, ladder (μ, μ₂, μ₃) = (12, 6, 3) read FORWARD (level-1 residual
(Z−s)⁶; level-2 single side u₂/2 with residual (Z−s₂)³ — the jump
gate; first machine σ at n = 24 and at μ₃ = 3 anywhere). Kinds: M2X
forced (Z−c)²(Z−d) — MIXED level-3 nodes, first anywhere: the per-class
route one level up (companion decided at the current key; refined
thread; parked side at the refined slope must persist with residual
(Z−(d−c)) EXACTLY — HE7-13′(c)∘HE7-2′): **17 mixed parkings exact +
18 persistent re-checks**; M2C forced (Z−c)³ pure: **11 refines, the
refined side gone every time** (HE7-13 as displayed, level 3); M2S
random cubics (incl. (8,3) letters — irreducible cubic residuals, new);
M1 ℓ₃ = 3 (e = 24, p = 11); M3 two-sided. Results: **σ == o1 48/48,
o2 48/48, o3 48/48; Σef = 24 every member; genres {(8,1),(16,1)}×12,
{(24,1)}×12, {(8,1),(8,2)}×10, {(8,1),(8,1),(8,1)}×8, {(8,3)}×6; TOOTH
14/48 flip when the deep letter is dropped** (the τ₃ Λ₁-component
machine-load-bearing at the new degree/primes). Disclosures: 3 members
went wild at p = 3 (a pure-cube refine landing an ℓ₃ = 3 slope, e = 24,
3 | e): for these o2 ran degree-multiset-only and o3 was skipped (the
tame parity formula is invalid there); o1 scored them normally. Members
ℤ_p only, as in both annex legs. Smoke record: one smoke (4 members)
found the wild-member oracle-applicability gap in MY instrument (not in
any annex claim); the o2/o3 wild-skip guard was added before the sealed
full run; no reader logic changed.

---

## S5. CLEAN CHARGES (verified, no finding)

1. R1-b's residue sum at a concrete level-3 two-class instance and at a
   level-4 two-letter instance (paper, two routes each + machine W0).
2. R1-a(i)/(ii)/(iii)/(iv) re-derived; carry c ∈ {0,1}; letter-monomial
   claim machine-decomposed at i = 3 (600 multi-letter θ's).
3. R1-c: inverse-twist absorption + bound recursion re-derived; = (‡₂)
   at i = 1.
4. R1-d conclusion strings deliver the frozen displays' conclusions
   (modulo M-B's provenance-clause riders).
5. R1.2 items 1–7 re-checked against the §S5/§S6 texts they audit.
6. HE7-13′ ↔ HE7-2′ composition coherent both directions (R2-a rider
   (ii) closing F-1's f_C leg; levels 1–2 byte-identity carrying
   HE7-13′'s own proof); machine-exercised at level 3 (W2).
7. HE7-13′ (a)–(e) + honesty box + wiring bullets re-derived; R2-a
   incl. the refined-key leg; R3/R4/R5 riders accurate.
8. All md5 + byte-freeze pins; both committed legs re-run bit-identical;
   every run-record number re-derived from committed artifacts.
9. The R leg's member generation reproduces the committed σ's 79/79 —
   the record is regenerable, not merely stored.
10. Pass-1's M-1 split machine-confirmed (47 + 55 = 102).

## S6. GRADE LINE

**CLEAN — 0 CRITICAL, 0 GAP, 2 MINOR (M-A instrument-name in one R1.3
record sentence; M-B two unriddered provenance clauses in HE7.D /
HE7.B(ii)), plus pass-1's M-1 confirmed and non-blocking. Nothing
GAP-or-worse survived verification. Per the pass charge: the ANNEX
STACK (ANNEX F-1 + ANNEX R) is ACCEPTED 2/2, and the Codex CHALLENGE
on HE7 (CODEX_HE7RAT_2026-08-09.md, F1–F5) is FULLY DISCHARGED — the
first complete challenge-to-discharge cycle of the ratification
program. HE7 is fully frozen including both annexes: dated appends
only.** Standing conditionality, unchanged and self-disclosed: R1.2 /
R1-d remain at annex (transfer-audit) grade — acceptance of the stack
freezes the text, it does not upgrade that grade — and COROLLARY
HE7.B(ii) keeps its "modulo the arc grade" sentence. Owed at the
editors' convenience, one dated line each: M-1 (47 + 55 split), M-A
(oracle name), M-B (the two provenance riders).
