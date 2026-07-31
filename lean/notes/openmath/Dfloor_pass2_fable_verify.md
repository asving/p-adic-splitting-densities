# Dfloor rev 2 — hostile verification pass 2 (Fable, fresh context, model-diverse)

Target read STANDALONE: `lean/notes/openmath/Dfloor_phaseB_verifybrief_rev2.md`
(the ONLY document consulted; the first pass-2-era report was not read, per
charge). Discipline: quote-and-classify; *critical error* = breaks the logical
chain; *justification gap* = missing but repairable step, conclusion assumed
and verification continued downstream. Special charge items: the Haar
construction, strict clause (iv), TRANSFER's interpolation, BASE-1's semantic
scope + the (f) fence, the n ≥ 1 hypothesis placement, ADD's reorder, and a
scan for any ∀-by-example (auto-CRITICAL if found).

**VERDICT: SOUND — 0 critical errors, 3 minor justification gaps (none
load-bearing, all locally repairable). All six charged rev-2 repair points
verified in place. No ∀-by-example anywhere in the proof chain.**

---

## 1. Setting, H0, H1, H2 — the Haar construction (charge item i)

**Quote (L69–78):** "C_N(x) := { a ∈ G : a ≡ x (mod p^N) coordinatewise } …
C_N(x) is the CLOSED ball of radius p^{−N} … clopen either way (H0)."
**VERIFIED.** Under d(a,b) = max|a_i−b_i|_p, d(a,x) ≤ p^{−N} ⟺ v(a_i−x_i) ≥ N
for all i ⟺ a ≡ x mod p^N. Closed-ball identification correct (the rev-2
repair of V17's item 4 is in place); clopenness from ultrametric.

**Quote (L85–93, H0 proof):** "Balls of positive radius in an ultrametric
space are clopen. G is compact … Countability: p^{nN} classes per level …
opens are countable unions of cylinders, so Borel ⊆ σ(cyl)."
**VERIFIED.** Each step standard and correctly assembled; the countable-union
claim follows because the base is countable in total.

**Quote (L114–120):** "𝒜 := the collection of finite unions of cylinders. 𝒜 is
an algebra of sets: two cylinders are nested or disjoint … the complement of
a level-N class is the union of the other p^{nN} − 1 classes; G = C₀ ∈ 𝒜."
**VERIFIED.** Complements of finite unions are finite intersections of
members of 𝒜, and 𝒜 is ∩-closed (cylinder ∩ cylinder ∈ {cylinder, ∅}); ∅ is
the empty union. Algebra axioms all check.

**Quote (L120–125):** "μ₀(A) := #{level-N classes contained in A}·p^{−nN}.
Well-defined: refining N → N+1 multiplies the count by exactly pⁿ and the
weight by p^{−n}."
**VERIFIED.** The count is intrinsic to the set A (no representation
dependence to rule out), and each level-M class splits into exactly
p^{n(N−M)} level-N classes as displayed; induction on the refinement gives
level-independence for all N ≥ the max level of A's constituents.

**Quote (L126–129, σ-additivity):** "if A = ⨆_{k≥1} A_k with A, A_k ∈ 𝒜, then
A is compact (clopen in compact G) and each A_k is open, so finitely many A_k
cover A; disjointness forces all remaining A_k to be empty."
**VERIFIED.** This is the correct compactness reduction: if A_{k₁},…,A_{k_m}
cover A, any other A_j ⊆ A ⊆ ⋃_i A_{k_i} is disjoint from every A_{k_i},
hence empty. Premeasure σ-additivity on the algebra is exactly what the cited
Carathéodory theorem (Folland 1.14) consumes; σ(𝒜) = Borel by H0.

**Quote (L134–138, invariance):** "C_N(x) + g = C_N(x + ḡ) … A ↦ μ(A + g)
also extends μ₀. Two finite measures agreeing on the π-system 𝒜 (closed
under intersection, contains G) agree on σ(𝒜) (the π–λ / Dynkin theorem)."
**VERIFIED.** Both π–λ uses (invariance here, uniqueness at L140–143) are
legitimate: probability measures (finite, equal total mass via G ∈ 𝒜),
π-system generating Borel. The uniqueness argument — the p^{nN} level-N
classes are pairwise translates partitioning G, forcing ν-mass p^{−nN} — is
airtight.

**Quote (L107–112, the (2′) clause):** "(2′) IF n ≥ 1, singletons are μ-null
(the hypothesis n ≥ 1 is NOT removable: at n = 0 … μ is the Dirac mass δ_{()}
… and the singleton {()} has mass 1, while p^{−nN} = 1 for all N)."
**VERIFIED — charge item: n ≥ 1 hypothesis placement.** The hypothesis is
displayed in the statement, re-displayed in the proof (L145–147: "the
convergence to 0 is exactly where n ≥ 1 enters"), and the n = 0
reconciliation with BASE-0(b)'s Dirac mass is explicit and correct. The one
consumption site of singleton-nullity is Appendix A's m = 1 base (L761–762),
which explicitly instantiates n = 1 and names the hypothesis: "singletons are
null by Prop H1 (2′) — the n = 1 instance, so the n ≥ 1 hypothesis of (2′)
is satisfied." No other consumer found; no n = 0 claim conflicts with the
Dirac mass. V17 repair (1) confirmed in place.

**Quote (L149–154, product form):** "μ₁^{⊗n} is a Borel probability measure …
translation-invariant … By the uniqueness just proved, μ₁^{⊗n} = μ."
**VERIFIED.** No circularity: the product clause consumes the n = 1 instance
of the already-established existence/uniqueness, and the general-n uniqueness
proof is independent of the product clause.

**H2 (L156–161):** standard disjointification; decreasing case on complements
valid in a probability space. **VERIFIED.**

**Nitpick (not a gap):** H1's statement "at any common level N" (L104) is
mildly ambiguous — it must mean any N at which every constituent cylinder
decomposes into level-N classes (N below a cylinder's level gives count 0).
The proof's usage (L118: "for all sufficiently large N") disambiguates; no
consumer misreads it.

## 2. FIN, SEP, TYPE, PART

**FIN (L174–179):** multiset of ≤ n pairs from {1..n}² as image of
{1..n} → pairs ∪ {blank}; bound (n²+1)ⁿ. **VERIFIED** (crude but correct).

**SEP (L239–257):** disc = (−1)^{n(n−1)/2}Res(f,f′) via the resultant product
formula with the (i,j)/(j,i) pairing sign count — correct; integrality and
continuity from Sylvester — correct; (ii) both directions displayed —
correct. (iii) **Quote (L255–257):** "Evaluate at f = ∏(X − pⁱ): the roots pⁱ
are pairwise distinct … so disc ≠ 0 at this coefficient vector."
**VERIFIED — and NOT a ∀-by-example:** the claim is existential
(disc-as-polynomial is not identically zero), so a single witness is the
correct proof form.

**TYPE (L272–281):** monic normalization in the UFD ℚ_p[X] (units = nonzero
constants, leading-coefficient comparison forces c = 1) makes the factor
multiset well-defined; pairwise distinctness from separability; degree count
consumes exactly I-2 and nothing more about e/f (charge check (iv) of §9:
confirmed — e·f = deg per factor is the only e/f fact used). **VERIFIED.**

**PART (L283–290):** S open as preimage of ℤ_p∖{0}; partition from
single-valuedness. **VERIFIED.**

## 3. MEAS-BRIDGE — the strict clause (iv) (charge item ii)

**Lemma EX (L309–316):** class mass p^{−nN} > 0 vs. null {disc = 0} gives a
separable lift; a lift witnesses both verdicts, forcing at-most-one σ in both
conventions. **VERIFIED** (for the strict convention any lift suffices; EX is
needed for the lax uniqueness and is correctly available).

**Clause (iii) (L334–338):** lifts of a child class are lifts of the parent —
correct in both conventions (in the lax bracket EX is invoked defensively;
the definition (6) holds even vacuously, so nothing is at risk either way).
**VERIFIED.**

**Clause (iv), strict — the charged EXACT equality. Quote (L340–345):**
"(⊆) If a ∈ D_σ(N) then f_a is itself a lift of a's class, hence separable
with σ(f_a) = σ: a ∈ L_σ. (⊇) Let a ∈ L_σ and v := v(disc f_a) < ∞; put
N := 2v + 1. Every lift g of a's level-N class satisfies g ≡ f_a
(mod p^{2v+1}) … by I-1: g is separable and σ(g) = σ(f_a) = σ. … So the union
is EXACTLY L_σ."
**VERIFIED.** (⊆) is immediate from (5). (⊇): a ∈ L_σ ⟹ disc f_a ∈ ℤ_p∖{0}
⟹ v ∈ ℤ_{≥0}, matching I-1's hypothesis exactly; g and f_a are both lifts of
a mod p^{2v+1}, so g ≡ f_a at the required modulus; I-1 (stated in §2 with
degree n ≥ 1, separable, wild-valid) delivers separability + type transport
for EVERY lift, which is literally (5). Strict equality holds with no null
set — confirmed EXACT. The lax bracket L_σ ⊆ ⋃D° ⊆ L_σ ∪ {disc = 0}
(L345–347) is airtight: the dichotomy "f_a separable (then a ∈ L_σ) or
disc f_a = 0" is exhaustive.

**Clauses (i), (ii), (v) (L349–363):** (i) countable union of clopen sets
(with the direct neighborhood C_{2v+1} ⊆ L_σ alternative) — open, Borel;
(ii) finite additivity over the disjoint cosets; (v) monotone limit via H2 +
(iv); lax squeeze via the null delta. **VERIFIED.**

**BRACKET (L375–383):** the upper bound's trichotomy (σ-decided ⟹ σ′ = σ via
f_a as lift; else undecided) is complete; disjointness for the undec mass
formula (L369–374) correctly cites EX across σ and coset-disjointness within
σ. **VERIFIED.**

**SEM-DRAIN (L385–392):** ⋂U_N = G∖S = {disc = 0} chases through (iv) + PART
correctly; H2 from above + the null clause. **VERIFIED.**

**SEM-DRAIN-RATE (L394–406):** the integer arithmetic 2v+1 > N ⟺ v ≥ ⌈N/2⌉
checks in both parities (N even: v > (N−1)/2 ⟺ v ≥ N/2; N odd: v ≥ (N+1)/2);
U_N ⊆ {v(disc) ≥ ⌈N/2⌉} with v(0) = ∞ absorbing the nonseparable case; I-3's
tail at m = ⌈N/2⌉ gives the displayed envelope; n ≥ 2 hypothesis matches
I-3's. The strict-vs-lax upgrade really is the displayed one-liner (the
contradiction argument uses only I-1 and the strict definition).
**VERIFIED.**

**§4.3 scope note:** decided_σ(N) claimed only as the SEMANTIC counts;
classifier counts and the Lean `decided`/`hExhaustP` tie explicitly fenced to
O-nodes/K-12. Consistent with §8. **VERIFIED.**

## 4. SUM-ONE, ID, TRANSFER — the interpolation (charge item iii)

**SUM-ONE (L428–437):** G = {disc = 0} ⊔ ⨆L_σ, finite additivity over FIN,
null clause. **VERIFIED.**

**Lemma ID (L439–446). Quote:** "Write R = A/B with A, B ∈ ℚ[t], B ≠ 0. For
z ∈ Z: B(z) ≠ 0 and A(z)/B(z) = 0 …"
**JUSTIFICATION GAP (minor).** For an ARBITRARY representation R = A/B,
"R defined at z" (the statement's parenthetical: "denominator nonzero") does
not license B(z) ≠ 0 — e.g. R = 1/1 also equals (t−z)/(t−z). Repair is
one word: take the REDUCED representation (gcd(A,B) = 1), for which
definedness of R at z is precisely B(z) ≠ 0; the root-count argument then
runs verbatim. Conclusion assumed; downstream (TRANSFER, T-F) unaffected.

**TRANSFER (L448–455). Quote:** "Q := (Σ_σ R_σ) − 1 ∈ ℚ(t): a finite sum by
FIN. For p ∈ P: Q is defined at p and Q(p) = Σ_σ α(n, σ; p) − 1 = 0 by
SUM-ONE(iii). P is an infinite set of integers, so Q = 0 by ID."
**VERIFIED, with one micro-gap.** The interpolation logic is correct and is
NOT a ∀-by-example: a rational function vanishing at infinitely many integers
where defined is identically zero (Lemma ID) — a genuine general argument.
The hypothesis structure is honest: the conclusion Σ R_σ = 1 is drawn ONLY
under the displayed hypothesis "α = R_σ(p) for all p in an infinite P";
nothing unconditional is claimed at general n (the general-n instance at
L463–471 is explicitly CONDITIONAL on the T-U ledger, with (REG-p) correctly
flagged as an external predicate entering only as the name of P, and
infinitude of P correctly derived from I-4 + Euclid).
**JUSTIFICATION GAP (micro):** "Q is defined at p" from each R_σ defined at p
uses the (true, unstated) fact that a finite sum of rational functions each
regular at p is regular at p (the local ring at p is a ring). One line;
downstream unaffected.

**Instances (L457–474):** n = 1 grounded in BASE-1; n = 2 rests on the
IMPORT I-5(a) — correctly labeled VERIFIED-LEAN import, not proved here, and
the direct table check (1+q)/(q+1) = 1 is right; ID over prime powers remark
is sound (the proof never used primality of Z's elements). **VERIFIED.**

## 5. BASE-1 — semantic scope + the (f) fence (charge item iv)

**(a)–(d) (L510–520):** the degree-1 combinatorics (unique type via
e·f = 1 over positive integers, ∅ excluded by degree), disc = 1 by the empty
product (consistent with SEP's n ≤ 1 convention), K_f ≅ ℚ_p with e = f = 1
computed directly ("I-2 is not even needed" — correct), every lift of every
class separable of type {(1,1)} hence strict-(5)-decided at every N including
N = 0. **VERIFIED.**

**(e) — the charged scope check. Quote (L490–495):** "[SEMANTIC clauses only]
with R_{(1,1)} := 1 ∈ ℚ(t): α(1, σ; p) = R_σ(p) at every prime, the bracket
is exact at every level, drainage is trivial, and Σ_σ R_σ = 1 — i.e. the
SEMANTIC content of the uniformity root at n = 1 … holds UNCONDITIONALLY."
**VERIFIED.** Every clause of (e) follows from (c)+(d) alone: α = μ(G) = 1,
decided/p^N = 1, undec = 0, singleton sum. Audited (e) word-by-word for
smuggled algorithmic content: none — the parenthetical explicitly restricts
to "(U-GEN)(i)–(ii)'s measure clauses read with the semantic counts (5)" and
"(U-DENS)'s density identity". Clean.

**(f) — the fence. Quote (L496–508):** "[FENCE — NOT PROVED HERE …] the
ALGORITHMIC half of (U-GEN)/(U-DENS) at n = 1 — that the OM classifier/engine
at n = 1 has exactly ONE state, that its producing finite solve … is the 1×1
system (1)·C = (1) …, and that its decided counts are FAITHFUL to the
semantic counts (5) — is classifier-side content and does NOT follow from
this package: 'one semantic type' (clause (a)) does not by itself yield 'one
algorithmic state'. … Consequently the FULL (U-GEN)+(U-DENS) at n = 1 … is
NOT claimed by this brief."
**VERIFIED — V17 repair (2) confirmed.** The fence names the residue
precisely (state count, 1×1 solve, count faithfulness), routes it to the
correct nodes (O-1/O-2/O-3/O-5, O-4's OL1-ii, T-8), states the correct
logical point (semantic type-uniqueness does not imply classifier-state
uniqueness), and explicitly disclaims the full node. §0's deliverable bullet,
§6.1's header, the Consumers paragraph (L629–631: "the solve STRUCTURE at
n = 1 … is classifier-side — BASE-1(f)'s fence"), and §8's NOT-CLAIMED entry
all say the same thing — no leak found anywhere in the document.

**Base-change remark (L524–531):** flagged as a remark feeding D-3, with the
(f) fence explicitly carried over ("the (f) fence applies verbatim to its
algorithmic half"). The claim that (a)–(d) use only complete-discretely-
valued-with-finite-residue-field structure is correct on inspection of the
proofs. **VERIFIED** (as a remark; it is not a numbered theorem).

## 6. BASE-0, ADD (the reorder — charge item vi), (C0)–(C2), LIN

**BASE-0 (L535–550):** empty-product conventions used consistently
(disc 1 = 1, σ(1) = ∅ via TYPE's k = 0 case, Dirac = Haar at n = 0 —
consistent with H1(2′)'s exclusion of n = 0). **VERIFIED.**

**Lemma ADD — the charged reorder. Quote (L562–569):** "SEPARABILITY OF gh
FIRST — so that TYPE may then be applied to gh (TYPE's hypothesis is
separability; establishing it first removes any circularity). … a common root
α of g and h would have its minimal polynomial over ℚ_p dividing both g and
h, hence dividing gcd(g, h) = 1 — impossible."
**VERIFIED — V17 repair (3) confirmed.** Separability of gh is now
established before any appeal to TYPE, from within-factor separability plus
the gcd argument (min-poly divides both since g(α) = h(α) = 0 with
g, h ∈ ℚ_p[X]); the subsequent type identity correctly notes that
monic-factorization uniqueness needs only the UFD structure, not
separability. Order of operations is clean.
**JUSTIFICATION GAP (minor), the finite-J induction (L580–581):** "Finite J:
induction on |J|; J = ∅ is BASE-0(a)." The induction step applies the
two-factor case to (∏_{j∈J′} g_j, g_k), which requires the PRODUCT to be
coprime to g_k — true from pairwise coprimality (an irreducible common factor
would divide some g_j in the UFD), but this one-line step is not displayed.
Repairable in place; conclusion assumed; downstream ((C1)'s empty-family
consistency, T-6 consumption) unaffected.

**(C0)–(C2) (L583–617):** (C0)'s monoid/grading/cancellativity all correct at
the multiplicity-function level. (C1)'s finiteness (finitely many
sub-multisets, complement determined by cancellativity), unit law, and
associativity-via-ordered-triples check out; ⊛_∅ := δ_∅ is a DEFINITION with
Lemma ADD's J = ∅ case as its semantic consistency — correctly framed.
(C2): (τ-lin) proved (Lemma LIN, verified — trivial extension e = f = 1);
(τ-irr) at d > 1 and (τ-hen) at d̄ > 1 explicitly "FIXED HERE AS A
CONVENTION, NOT PROVED" and fenced to O-5 — matching §8's
CONVENTIONS-FIXED-NOT-PROVED entry exactly. **VERIFIED** (charge check (vi)
of §9: conventions consistent, fences exact).

## 7. Falsifier section §7 — the ∀-by-example scan (charge item: CRITICAL if found)

**Prop N2 (L648–662):** re-derived independently: D = D₀ + 2b₀p^Nβ + p^{2N}β²
− 4p^Nγ; p odd: the unit 4 makes the γ-orbit all of p^Nℤ_p, absorbing the
β-terms — exact criterion correct; p = 2: γ-orbit 2^{N+2}ℤ₂, and the β-mod-2
dependence checks (2^{N+2}b₀δ absorbed; 2^{2N}(4βδ+4δ²) needs 2N+2 ≥ N+2,
i.e. N ≥ 0; the N = 1 case 4β² mod 8 ∈ {0, 4} by parity — recomputed).
**VERIFIED.**

**T-F — the charged interpolation certificate (L693–713).** Recomputed
INDEPENDENTLY in exact rational arithmetic (this pass, not the project's
script): over 6·P5, the six displayed terms have degrees {5,5,5,4,3,5} (all
≤ 5 as claimed), and their sum is IDENTICALLY ZERO:
(q⁵−q⁴+q³) + 3(q⁵+q⁴+q³) + 2(q⁴+q³)(q+1) + 6(q⁴+q²+q) + 6(q²+1)(q+1)
= 6q⁵+12q⁴+12q³+12q²+12q+6 = 6·P5. Point checks at q = 2..11 also re-run:
all equal 1; n = 2 table sums to 1 identically.
**VERIFIED — and NOT a ∀-by-example.** The logic is degree-bounded polynomial
interpolation: deg A ≤ 5 established by inspection of displayed terms, so
vanishing at 6 points with P5(q) ≠ 0 forces A = 0 by Lemma ID's root count.
That is a complete general argument; the 199 checked points are redundancy,
not the proof. (Rev-2 repair (5) — the certificate now auditable in-package —
confirmed: this pass audited it without touching the sealed file.)

**T-A–T-E, T-B witness certification, observed-structure bullet:** these are
script-result REPORTS, consumed by nothing in §§1–6; the brief's theorems
never cite them. T-E's modulus-2v sharpness probe is explicitly "reported,
not asserted"; the undec(N) = p^{−N} bullet is "recorded, not asserted" with
a correct provability sketch at odd p (undecided ⟺ p^N | D₀, one c₀ per b₀).
As a standalone reader I cannot re-run the script, but no logical weight
rests on it. **VERIFIED (as fenced).**

**Scan result: NO ∀-by-example anywhere in the proof chain.** The only
example-shaped moves are SEP(iii) (a legitimate ∃-witness), T-F (legitimate
finite interpolation with a verified degree bound), and the n = 2 instance
(an explicit IMPORT, not an in-package proof).

## 8. Appendix A and the honesty ledger

**Lemma NULL (L753–771):** induction on m; m = 1 base cites (2′)'s n = 1
instance WITH the hypothesis named (the charged placement check — clean);
step via Tonelli with the measurability of y′ ↦ μ₁(Z_{y′}) asserted on a
closed (hence Borel) Z and product-measure associativity from H1. The n = 1
discriminant case correctly noted empty. **VERIFIED.** The three-carrier
redundancy note is accurate: §§4–6's qualitative results need only this
appendix + I-1 + I-2.

**§8 ledger:** cross-checked every PROVED-HERE entry against the body — each
is proved above; every NOT-CLAIMED entry names a real fence present in the
text (§4.3, BASE-1(f), (C2), K-12); the strict/lax seam warning is correct
and the deltas are as proved. The self-grade "PROVED-UNVERIFIED until
fresh-context adversarial passes accept" is honest. **VERIFIED.**

---

## Findings table

| # | Location | Quote (abbrev.) | Class |
|---|----------|-----------------|-------|
| 1 | Lemma ID proof (L443–444) | "Write R = A/B … For z ∈ Z: B(z) ≠ 0" | JUSTIFICATION GAP (minor): needs the reduced representation to link definedness to B(z) ≠ 0; one-word repair |
| 2 | Lemma ADD, finite J (L580–581) | "Finite J: induction on \|J\|" | JUSTIFICATION GAP (minor): coprimality of the partial product with the next factor used but not displayed; one-line UFD repair |
| 3 | TRANSFER proof (L453–454) | "Q is defined at p" | JUSTIFICATION GAP (micro): finite sums of functions regular at p are regular at p — unstated one-liner |

Critical errors: **none**. All six charged rev-2 items (Haar bookkeeping,
strict (iv) exactness, TRANSFER's interpolation, BASE-1 scope + (f) fence,
n ≥ 1 placement, ADD reorder) pass. Independent recomputation performed this
pass: T-F cleared numerator A ≡ 0 (exact polynomial arithmetic), degree
bounds, q = 2..11 point checks, n = 2 table, Prop N2's p = 2 parity claim.

**Pass-2 verdict: ACCEPT (SOUND, minor gaps only).** Per the standing
acceptance rule this counts as one clean pass; acceptance requires the
consecutive-clean-pass quota, not this report alone.
