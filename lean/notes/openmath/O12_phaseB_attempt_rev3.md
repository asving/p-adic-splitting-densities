# O12 — (REG-p) emptiness at 𝔅_n — Phase-B attempt REV 3 (Fable, 2026-07-31)

Repair of the V9 hostile verification (`V9_o12rev2.jsonl`, verdict UNSOUND)
of the rev-2 attempt (`O12_phaseB_attempt_rev2.md`) / brief
(`O12_phaseB_verifybrief_rev2.md`). V9 CONFIRMED both rev-2 repairs (the
L6a/L6b cell-and-exponent lemmas, incl. the c′_j and nested-minimum
calculations; the O2/O2′/O3 fixed-point algebra with both unit solve
denominators) and everything carried from rev 1 (L1–L4, the O3 gcd, the
determinants and margins, ℛ's closure, the p/δ-uniformity, the backup
theorem). It found ONE critical error, TWO justification gaps. This rev
repairs all three; the orchestrator's charge — the joint count-rationality
lemma — is §1 (new Lemma L6d + Fact F, proved by the fibered-product-over-
the-vertex-torus attack, exactly as dispatched).

The repaired self-contained brief is `O12_phaseB_verifybrief_rev3.md`
(rev-2 verified parts byte-stable: the brief was produced by copying rev 2
and editing only the preamble, §1's two instance sentences, §2.2's one
pointer, §2.3, §3 (L6c's final sentence + new Fact F/L6d + L6′'s citation),
Theorem 2's proof, §7's one display, §8's new paragraph, §9). New
falsifier: `verification/openmath/O12_rev3_checks.py` (§4; ALL PASS, zero
findings), run BEFORE the lemma was enshrined.

## 0. V9 findings → dispositions (no silent drops)

| V9 finding | class | disposition |
|---|---|---|
| F1: E(e) is not actually an explicit table — no terminal/split/junction/entrance/shape/β-row formulas; "finite ℚ(q)-combinations" could smuggle arbitrary denominators (e.g. q−2); the claimed 𝒢-exhibitions occur nowhere | CRITICAL | **FIXED §2**: §2.3 rewritten as SEVEN displayed row families (i)–(vii), each a formula with its 𝒢 generation in brackets; the former "ℚ(q)-combinations" are now displayed as 0/1-coefficient sums of products (no scalars beyond the masses themselves can enter); the one non-displayed ingredient (which verdict tuples feed which verdict) is isolated as a FINITE composition datum and Theorem 2 is proved for EVERY choice |
| F2: L6c proves depth-independence of the residue law but NOT that every joint residual-shape count is a polynomial of the stated kind uniformly over residue characteristics — adjacent faces SHARE vertex coefficients | GAP (the substantive residue) | **FIXED §1**: new Lemma L6d proves the joint probability is exactly ∏_j P_{ρ_j}(q)·(q^{d_j}−q^{d_j−1})^{−1} — (g1)·(g2) forms — via the torus identity (T1) + fibered telescoping over the shared vertex values; new Fact F proves the P_ρ/N_π counts are universal polynomials (Möbius/necklace); L6c's overclaiming final sentence deleted (its proof never argued it); L6′ re-pointed at L6d |
| F3: the §7 degree-2 solved vector displayed in reversed order relative to its displayed row order (no pole — same denominators — but "EXACTLY the componentwise solve" not literally true) | GAP | **FIXED §3**: display corrected to the row order, (q²/(q²+q+1), (q+1)/(q²+q+1)), annotated "in the SAME row order"; the componentwise divisions displayed alongside are unchanged (they were already correct and pin the pairing) |

Everything V9 confirmed is carried byte-stable (§5).

## 1. Repair of F2 (the charge): Lemma L6d, joint count-rationality

Setting (L6c, verifier-accepted): conditioned on {polygon = P} with
face-kind κ = (L_j, b_j)_{j=1..k}, d_j := L_j/b_j, the residues at the
integer-height columns are INDEPENDENT — uniform on F^× (F := F_{q₀}) at
the k vertex columns x_1, …, x_k, uniform on F at the interior
integer-height columns (d_j − 1 per face), constant 1 at the anchor column
e. Face j's residual polynomial, oriented left-vertex-to-leading,

    R_j(z) = V_j z^{d_j} + (interiors) + V_{j+1},   V_j := u_{x_j},
    V_{k+1} := 1 (anchor),

so consecutive faces SHARE the vertex residue V_{j+1} (their column ranges
intersect exactly in {x_{j+1}}) — the residual polynomials are NOT
independent random variables. The V9 objection: identifying independent
COLUMN residues does not by itself make the joint factorization-shape
event a standard point-count ratio.

**Fact F** (universal pattern counts; full proof in the brief §3). Over
every F_q: monic irreducibles of degree D number
M_D(q) = D^{−1}Σ_{δ|D}μ(δ)q^{D/δ} (z^{q^D} − z is squarefree and is the
product of all monic irreducibles of degree dividing D; compare degrees,
Möbius-invert). For a pattern ρ (multiset of (degree, multiplicity) atoms;
c_{D,m} atoms equal to (D, m); r_D := Σ_m c_{D,m}):

    N_ρ(q) = ∏_D (M_D(q))_{r_D} / ∏_m c_{D,m}!     [all monics with ρ]
    P_ρ(q) = same with M_1 = q ↦ q − 1             [+ nonzero constant]

(unique factorization: choose r_D distinct irreducibles per degree, assign
the multiplicity multiset; the only irreducible with zero constant term is
z itself). Universal polynomials in q — characteristic-free.

**Lemma L6d.** For every face-kind κ, every z-free shape vector
ρ⃗ = (ρ_1, …, ρ_k) (deg ρ_j = d_j), every admissible P of kind κ, and every
residue field F_{q₀}:

    Prob(pattern(R_j) = ρ_j ∀j) = ∏_{j=1}^k P_{ρ_j}(q₀)·(q₀^{d_j} − q₀^{d_j−1})^{−1}.  — (JC)

One fixed element of ℚ(q), of the displayed (g1)/(g2) kind, uniform over
residue characteristics; the face shape events are mutually independent
even though the R_j share coefficients.

*Proof (the dispatched fibered-product attack).*
(T1) *Torus identity*: for every d ≥ 1, z-free ρ of degree d, and EVERY
c ∈ F^×: #{R : deg R = d, R(0) = c, pattern ρ} = P_ρ(q₀), independent of
c — the bijection R ↦ lead(R)^{−1}R onto {monic, nonzero constant, ρ}
(inverse S ↦ (c/S(0))·S; patterns are invariant under unit scalars; both
composites are the identity — displayed in the brief).
*Telescoping*: condition on the shared vertex vector (V_1, …, V_k). Given
it, the faces' interiors are independent, so with n_j(ρ_j; λ, c) := the
interior count at leading λ, constant c,

    #Joint = Σ_{V ∈ (F^×)^k} ∏_j n_j(ρ_j; V_j, V_{j+1}).

V_1 occurs only in the first factor; Σ_{V_1} n_1(ρ_1; V_1, V_2) =
#{R : deg d_1, R(0) = V_2, ρ_1} = P_{ρ_1}(q₀) by (T1) — a CONSTANT,
independent of the shared value V_2. It factors out; V_2 then occurs only
in the second factor; iterate left to right; the last step is (T1) at the
anchor value c = 1. So #Joint = ∏_j P_{ρ_j}(q₀). Divide by the
configuration count (q₀−1)^k·q₀^{Σ(d_j−1)}: exactly (JC). Consistency:
Σ_ρ P_ρ = q^d − q^{d−1}, so (JC) sums to 1; the same telescoping computes
each marginal, so joint = ∏ marginals. ∎

*Why a lemma was genuinely needed (the falsifier's REFUTES-hook).* The
pointwise conditional counts DO depend on the shared vertices: for the
double-root shape at d = 2 and odd q₀, n(ρ; λ, c) = 1 + χ(c/λ) ∈ {0, 2}
(χ = quadratic character; b² = 4λc), non-polynomial per fixed vertex pair
and char-dependent (at q₀ even it is constantly 1). Only the torus-summed
count is universal — (T1) is exactly that statement. CHECK D (§4) verifies
both halves.

Consumers re-pointed: L6c's final sentence (the verifier's quoted
overclaim) now defers to L6d; L6′'s "residual factor from L6c" is now
"the (JC) product of L6d, constant across the family"; §2.3(iii) displays
the closed polygon mass m(κ, ρ⃗) with (JC) as an explicit factor.

## 2. Repair of F1: E(e) as seven displayed row families

§2.3 of the brief is rewritten. The row families, each with a displayed
formula and its bracketed 𝒢 generation: (i) kernels (per booking; the O3
kernel exhibited as its (g4) resummation); (ii) divisor-pattern masses
m(π) = q^{−(E−e)}·N_π(q)·q^{−e} with N_π now a PROVED universal polynomial
(Fact F); (iii) polygon-family masses

    m(κ, ρ⃗) = q^e·[Σ_{ε∈Enum(κ)} (1−q^{−1})^k q^{−N_min(ε)}
               ∏_{j<k} q^{c_j}/(q^{c_j}−1)] · ∏_j P_{ρ_j}(q)(q^{d_j}−q^{d_j−1})^{−1}

(cell sum from L6a/L6b; shape factor from L6d); (iv) verdict rows
row_σ(F) = m(F)·Σ_{comp_F(σ⃗)=σ} ∏_i β_{μ_i}(σ_i)(q^{D_i}) and their
aggregates t_σ — SUMS OF PRODUCTS WITH 0/1 COEFFICIENTS, which kills V9's
"arbitrary denominators such as q−2" avenue: no scalar beyond the masses
and β-legs can enter (plus the two displayed booking adjustments: +κ₁
under O2, ×q^E/(q^E−1) under O3); (v) the entrance/shape weights as a
finite concrete (g2)/(g4) list with bounded indices; (vi) β-legs under
(g5); (vii) the solved β_e(σ) via (g7). Terminal/split/junction = the
r = 0/1/≥2 cases of (iv).

The one ingredient that is table data rather than formula — WHICH verdict
tuples compose to which verdict (comp_F) — is isolated as a finite
parameter; 𝔅_n is honestly a finite FAMILY of tables (bookings ×
composition data), and Theorem 2/the claim are proved for EVERY member
(0/1-combinations of ℛ elements lie in ℛ whatever the datum selects).
Semantic faithfulness of any particular datum is value-correctness,
outside the claim (§1 scope, unchanged). Theorem 2's proof now walks
(i)–(vii) explicitly instead of asserting "each member is exhibited".

## 3. Repair of F3: the §7 display

"solve ((q+1)/(q²+q+1), q²/(q²+q+1))" → "solved vector, in the SAME row
order, (q²/(q²+q+1), (q+1)/(q²+q+1))" — matching the displayed terminal-
mass order (1 − 1/q, 1/q − q^{−3}) and the (unchanged, already correct)
componentwise divisions displayed next to it, which pin the pairing:
(1 − 1/q)/(1 − q^{−3}) = q²/(q²+q+1). Rev-2's CHECK 3b had verified
exactly this pairing; only the §7 tuple order was wrong. No content
change (both components share the denominator q²+q+1).

## 4. Numerics executed (falsifier-first; run before enshrining L6d)

Script `verification/openmath/O12_rev3_checks.py`; log
`logs/O12_rev3_checks.log`; results `O12_rev3_results.json`. ALL PASS:

* **CHECK A (Fact F, P_ρ).** Brute-force factorization censuses of all
  monic z-free polynomials over F_p, p ∈ {2,3,5,7,11,13}, d ≤ 4 (d = 4 for
  p ≤ 7): every pattern count matches P_ρ(p) exactly; totals match
  p^d − p^{d−1}. REFUTES-hook: any mismatch kills Fact F(iii).
* **CHECK B (T1).** Honest enumeration over ALL leading coefficients (no
  scaling shortcut), p ≤ 7, d ≤ 3: at EVERY fixed constant c ∈ F^×
  (including the anchor c = 1) the pattern counts equal P_ρ(p).
* **CHECK C (L6d/(JC), the finding's direct falsifier).** Full enumeration
  of the anchored shared-vertex residue model for face-degree chains
  (2,2), (2,1), (1,2), (2,3), (3,2), (2,2,2), p up to 13 ((2,2) case) —
  every joint shape count equals ∏_j P_{ρ_j}(p) EXACTLY, support and
  totals included, and the empirical face-shape events are exactly
  independent. A single deviating joint bucket would have refuted L6d.
* **CHECK D (nontriviality).** The pointwise double-root counts across
  vertex pairs: exactly {0, 2} at p ∈ {3,5,7}, exactly {1} at p = 2 — the
  shared-vertex coupling is real and characteristic-sensitive pointwise;
  universality appears only after the torus sum, as (T1) claims.
* **CHECK E (Fact F, N_π).** All-monic censuses (z allowed) match N_π(p),
  p ≤ 7, d ≤ 4 — the row-family-(ii) ingredient.

Scoping note: CHECK C tests the residue MODEL of L6c (which V9 accepted:
"the column residues are independent"); an end-to-end p-adic re-derivation
of that model was already exercised by rev-2 CHECK 1 (hull-fiber volumes)
and is not re-run here. Rev-1/rev-2 numerics stand unchanged.

## 5. Byte-stable perimeter (what V9 confirmed; carried verbatim)

Lemmas L1, L2, L3, L4, L5, L7 and proofs; L6a and L6b statements and
proofs (V9: "the cell description in L6a is correct", "the elementary
exponent calculation in L6b(i) is also correct", "the nested-minimum
argument in L6b(ii) correctly propagates", "the k=1 case really is
finite"); L6c's residue law (V9: "L6c correctly establishes…"); the §2.4
bookings and balance equations (V9: "the fixed-point algebra is correct",
the O2 no-feedback booking "is a genuine solve", "both possible solve
denominators are units of ℛ"); Theorem 1 (1)(2)(3); Corollary D and
margins; Theorem 3's quantifiers; Theorem 4; the §7 degree-3 data; the §8
rev-1/rev-2 corroborations. The scope declaration is unchanged.

## VERDICT

VERDICT: REPAIRED (all three V9 findings closed: the substantive residue —
the joint count-rationality of shared-vertex residual-shape events — is
now Lemma L6d, proved by conditioning on the shared vertex torus and
telescoping the torus identity (T1) face by face, with Fact F supplying
characteristic-free necklace/multiset counts; its direct falsifier (full
joint-law enumeration over chains up to three shared vertices, p up to 13,
plus the {0,2}-vs-{1} pointwise-variation hook) passed with zero findings
BEFORE the lemma was enshrined. The E(e) critical is closed by displaying
the entry table as seven explicit row families with bracketed grammar
generations and 0/1-coefficient combination structure, the sole
non-formula ingredient isolated as a finite composition datum over all of
whose values the theorem is proved. The reversed §7 display is corrected
to the row order with the pairing pinned by the adjacent componentwise
divisions. The O-12 theorem stands at its rev-1 honest scope: at 𝔅_n,
every booking and composition datum on record, every block determinant and
every entry denominator is cyclotomic-type; the (REG-p) failing set is
EMPTY at every prime, every pool value, every descent depth. Seams
unchanged: instance pin = D-11/O-2/T-7/O-14d; value correctness excluded
(F1 on record); contingent OL-O12-1 fires only for future non-𝔅_n
organizations.)
