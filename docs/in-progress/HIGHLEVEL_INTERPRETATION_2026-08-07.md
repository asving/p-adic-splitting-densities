# HIGH-LEVEL INTERPRETATION — four candidate frames for the carry algebra (Witt/δ-rings, graded reduction + CFT, motivic integration, Herbrand), each tested on committed towers — the headline: the section carry κ IS the fundamental class of H²(ℤ/E, ℤ) (measured class = 1 on all three test towers), the wild part of the carry class PROVABLY DIES over finite residue fields (measured: tame ℤ/2 survives on T2C, all-wild classes trivial on T3A/T2A), and the recommended frame is H-B (graded reduction of valued fields, Tignol–Wadsworth genre)

**Unit:** RESEARCH/INTERPRETATION (read-only on the corpus; this one note).
**Genre: INTERPRETATION note — nothing is proved at grade, no note is edited,
no gate fires, no open leg is discharged.** Every "measured" number below is
from a scratch instrument (Appendix A, disclosed verbatim; no seal, no
teeth). Grades of everything consumed ride their owning notes. Author:
Fable interpretation unit, 2026-08-07, answering Asvin's side question of
2026-08-07: *"could we find a high level interpretation of the proof that
might allow us to use higher powered machinery … like how class field
theory has both low level and high level proofs and the more abstract
machinery contextualizes it better"* — with his observation that the
cocycles come from a low-level source: the tower of extensions of the
value group, i.e. **carries in mixed-radix positional notation**.

**Sources consumed (skimmed for structure, not re-verified):**
`WELD_SYNTHESIS_2026-08-05.md` (the one-cochain verdict; c = z̄^δ·∂E),
`WELDMASTER_2026-08-08.md` (WELD-M, WM-COB, WM-CLASS, PERIM-μ),
`GRTJC_PROOF_2026-08-08.md` (W-9 twisted group algebra; JC-LOC),
`GRTJB_PROOF_2026-08-08.md` (the shear Σ_q), `GRTW2_PROOF_2026-08-08.md`
(W2-OPEN-2), `docs/HUMAN_PROOF.md` §§0–5, `LEDGERLAMBDA_2026-08-08.md`
(the quantum table), `lean/LeanUrat/PadicMeasure.lean` (AX_cellRecursion =
Igusa §7.4). Engine for all tests: the committed
`verification/openmath/iterlawn_pe_reimpl.py`, verbatim import.

---

## §0. The object being interpreted (episodic re-grounding, ten lines)

A tower T carries reads (e_j, h_j, g_j), j = 0..n: at each level the value
group grows by index e_j (slope h_j/e_j in lowest terms) and the residue
field by degree g_j (residual letter z_j, a root of ψ_j). E := e_0⋯e_n.
Every abscissa γ ∈ ℤ splits into level digits s_j := ℓ_{j−1}β_j mod e_{j−1}
(ℓ = normalized Bézout inverse of h mod e) — a **twisted mixed-radix
positional expansion** of γ along the value-group tower. Multiplying two
anchor monomials costs the **carry cocycle** c(γ,γ′) = z̄^δ·∏_j z_j^{D_j}
∈ K^*: integer carries δ (top) and D_j (level j), each priced by a residual
letter. The accepted structure theorems: 𝒜(T) = K^c[ℤ/E], the twisted group
algebra (JC W-9); the inner factor is a coboundary of the one-cochain
t_j(β) = (ℓβ − s)/e — WM-COB: c = z̄^δ·∂E — so the class survives as
[c] = [z̄^δ·ρ_T^{−κ}] ∈ H²(ℤ/E, K^*) (WM-CLASS), and abstractly
𝒜(T) ≅ K[v]/(v^E − ζ_T) at every stage (JC-F1). The polygon side
transports by the shear Σ_q(i,u) = (i, e_q·u + h_q·i) (JB). Asvin's
observation is that ALL of this is odometer arithmetic: digits, carries,
and the prices of carries. The question is which high-powered frame, if
any, this odometer is the low-level shadow of.

Four frames are evaluated. For each: (i) the dictionary, tested exactly on
committed towers (T2A, T2C, T3A — the weld-probe roster specs, imported
byte-for-byte); (ii) what adopting it would prove or reorganize —
specifically whether **W2-OPEN-2** (canonical-lift covariance above twist
junctions), **(DMULT-s)** (the exact multiplicativity tier), or the **J-D
count equality** becomes natural; (iii) where it breaks. Verdicts are
ranked in §5, with ONE frame recommended for a future unit.

---

## §1. H-A — WITT VECTORS / δ-RINGS: verdict **FAILS CLEANLY**, with the breaking points named (the frame's content is already the corpus's WM-COB; its power lives in exactly the structure the graded reduction was built to kill)

### 1.1 The dictionary attempted

| corpus object | Witt/δ-ring candidate |
|---|---|
| level digits s_j ∈ ℤ/e_{j−1} | Witt components of W_{n+1} |
| integer carries δ, D_j | Witt addition-law carry polynomials |
| the one-cochain t_j(β) = (ℓβ−s)/e | the p-derivation δ(x) (Joyal/Buium): a non-additive "digit-quotient" operator whose coboundary is the carry |
| LED-Λ's quantum q_l = h_l·∏_{l<t<m} e_t | the mixed-radix **place value** of level l |
| WM-COB (D_j = ∂t_j) | "carries are the coboundary of digit truncation" — the mechanism that makes (r, δ) split W₂ as sets |
| letter prices z_j^{D_j} | — no counterpart (see 1.4) |

The structural identification at the mechanism level is genuine: t_j plays
exactly the role of a Buium-style carry operator (a set map ℤ → ℤ whose
failure of additivity is a 2-cocycle representing the value-group
extension), and WM-COB(i) is the universal statement of that mechanism. On
an all-wild tower (every e_j = p) the group ℤ/E is ℤ/p^{n+1} =
W_{n+1}(𝔽_p) as a group, so the frame predicts the ledger's integer layer
IS Witt addition. That prediction was tested exactly, twice.

### 1.2 Test 1 (the charged level-2 comparison, by hand): positional vs Teichmüller sections of ℤ/9 — the two carry laws DIFFER at p = 3, coincide at p = 2

W₂(𝔽_p) ≅ ℤ/p² uses **Teichmüller** coordinates n = ω(a₀) + p·ω(a₁); the
carry is the Witt polynomial c_W(a,b) = −Σ_{i=1}^{p−1} (1/p)·C(p,i)·aⁱb^{p−i},
for p = 3: c_W(a,b) = −ab(a+b). The corpus uses the **positional** section
(digits 0..e−1, floor carry). On ℤ/9, the integer 2 has positional digits
(2, 0) but Teichmüller digits (2, 1) — check: ω(2) = 8 in ℤ/9 (8 ≡ −1,
(−1)² = 1), and 2 = 8 + 3·1. Hence for the simplest pair 1 + 1 = 2:

    positional carry: ⌊(1+1)/3⌋ = 0
    Witt carry:       −1·1·(1+1) = −2 ≡ 1 (mod 3)   [matches 2 = (2,1)_Teich]

Same cohomology class in H²(ℤ/3, ℤ) (both present the extension ℤ/9),
**different cochains** — and the corpus's own hard-won lesson (the (CYC)
fence: presentation vs class; JC-F1) says the ledger lives at cochain
level, where this difference is load-bearing. At p = 2 the sections
coincide ({0,1} = Teichmüller lifts), so only there could the literal Witt
form hold. The engine confirms the corpus side: WM-COB's D_j = ∂t_j is the
floor/positional law (25,409/0 sealed in WELDMASTER S5).

### 1.3 Test 2 (engine, Appendix A): even at p = 2 the naive odometer identity FAILS — the carries are weight-frame conjugated

Naive hypothesis: (δ, D_n, …, D_1) = the plain base-(e_n,…,e_0) carries of
adding the integers γ, γ′. Result on window-section pairs:

    T2C (p=3, e=(2,3)):   match 16 / mismatch 20
    T3A (p=2, e=(2,2,2)): match 24 / mismatch 40
    T2A (p=2, e=(2,2)):   match 12 / mismatch  4

Witness (T2A, γ = γ′ = 9, classes 1+1 mod 4): digits carry exactly as the
odometer says (s = (0,1)+(0,1) → (1,0), top carry δ = 1 ✓), but the
level-1 carry is **D_1 = 4**, where the plain odometer carry is 0: the
carry-in enters through [ILN]†'s shift chain S_1 = δ·γ_2 = 9 and
D_1 = (s-defect + ℓ_0·S_1)/e_0 = (−1+9)/2 = 4. The ledger's carry integers
are the odometer's carries **conjugated into the weight frame** (multiplied
through the γ_j / (ℓ′−ℓ·wΦ) descent operator — the same affine operator as
W-2's χ-chain). So the honest statement is: *the integer layer is a
Bézout-twisted odometer whose carry values are read in sheared (weight)
coordinates* — which is precisely WM-COB + [ILN]† S0.3, i.e. the corpus
already owns the correct form of this frame, in its own language.

### 1.4 Where the frame breaks (three named points) and what it would buy (nothing owed)

1. **Mixed radix.** Witt functors are p-typical (or big). There is no Witt
   functor with universal/integral addition laws in radix (e_0,…,e_n) for
   arbitrary e_j; ramified Witt vectors (Drinfeld/Hazewinkel W_{O,π})
   handle π-typical towers over a fixed O but not slopes h_j/e_j in lowest
   terms with residual growth g_j interleaved.
2. **Section mismatch at p ≥ 3** (test 1): Teichmüller ≠ positional; the
   ledger is pinned to the positional/eq-12 section by the print dictionary
   (JA-EPS), so the Witt coordinates are the WRONG presentation for it.
3. **The prices.** Witt carries are additive polynomials that MIX digit
   values; the corpus's carries are K^*-monomials z_j^{D_j} in fixed
   letters. This is not an accident to be fixed but the design: the graded
   pieces are 1-dimensional anchor lines, i.e. **the graded reduction
   kills exactly the digit-mixing that Witt addition polynomial structure
   describes**. The Witt frame's actual power (functoriality, Frobenius,
   ghost components, prismatic descendants) applies to the FILTERED object
   O_K[x]/(f), not to its associated graded — and the whole strategy of
   the corpus is to work in gr, where multiplication is monomial + carry.

Adopting H-A would rename t_j ("carry derivation") and WM-COB ("δ-ring
splitting mechanism") without proving W2-OPEN-2, (DMULT-s), or J-D. A
frame that fails this cleanly is a useful verdict: **the carry algebra is
odometer arithmetic, but it is NOT Witt arithmetic; the deviation (Bézout
twist + weight conjugation + letter pricing) is exactly the content of
[ILN]† S0.3 that a general theory would not supply.**

---

## §2. H-B — GRADED REDUCTION OF VALUED FIELDS + KUMMER/CFT: verdict **HOLDS, and yields the one genuinely new theorem-shaped output of this note** (the fundamental-class reading of κ, measured; the wild-triviality of the carry class, measured on all three towers)

### 2.1 The dictionary (every row already latent in the corpus)

| corpus object | valued-field / CFT object |
|---|---|
| B = gr(w)[in(π)^{−1}] ≅ gr_{K[x]}(w) (JC-LOC) | the **graded reduction** of the valued ring (Temkin; Teissier's graded algebra of a valuation; the FGMN graded package the note already cites) |
| 𝒜(T) = K^c[ℤ/E] (W-9) | the graded reduction of the local field L_T cut out by the type: a **graded field** with value group (1/E)ℤ, degree-0 part K — the objects of Tignol–Wadsworth, *Value Functions on Simple Algebras, and Associated Graded Rings* (Springer Monographs, 2015) |
| the value-group tower ℤ ⊂ (1/e_0)ℤ ⊂ … ⊂ (1/E)ℤ | the ramification filtration of value groups; ℤ/E = Γ_L/Γ_K |
| the section carry κ(ν,ν′) = (σν+σν′−σ(ν+ν′))/E | **the fundamental class**: the standard 2-cocycle presenting 0 → ℤ → (1/E)ℤ → ℤ/E → 0, the generator of H²(ℤ/E, ℤ) ≅ ℤ/E |
| the letter pricing m ↦ z^m | the coefficient map H²(ℤ/E, ℤ) → H²(ℤ/E, K^*) induced by ℤ → K^*, 1 ↦ z |
| [c] = [z̄^δ·ρ_T^{−κ}] (WM-CLASS) | the class of gr(L_T) = an **image of integer carry classes under letter pricing** |
| ζ_T, 𝒜 ≅ K[v]/(v^E − ζ_T) (JC-F1) | the **Kummer class** ζ_T ∈ K^*/(K^*)^E of the graded field — symbol data |
| anchor/lift changes acting by unit characters (M2/M4) | change of homogeneous basis = coboundary functoriality of the symbol |

Two measured legs ground the load-bearing rows (Appendix A, scratch):

**(HB-1) class[κ] = 1 ∈ H²(ℤ/E, ℤ) ≅ ℤ/E on T2C, T3A, T2A** (orbit-sum
invariant Σ_k κ(1,k) mod E = 1 at E = 6, 8, 4 respectively). So the
corpus's section carry is not merely *analogous to* but **is the measured
generator** — the fundamental class of the value-group extension. This is
Asvin's observation made into a classical anchor: the generator of
H²(ℤ/n, ℤ) is the carry cocycle of positional notation, and local CFT's
invariant map for unramified extensions is computed by literally reading
off that carry (val: H²(G, L^*) → H²(G, ℤ) ≅ ℤ/n, Serre *Local Fields*
XIII / *Corps Locaux*). The corpus's ℤ/E sits on the value-group side
(totally-ramified direction) rather than the Galois side, so the exact
statement is the dual one — but it is the same cocycle.

**(HB-2) class[δ] = (E/e_n)·ℓ_n mod E on all three towers** (measured
4 = 2·2 mod 6, 4 = 4·1 mod 8, 2 = 2·1 mod 4): the outer carry class is the
inflation to ℤ/E of the top-read carry class, twisted by the Bézout unit.
(Displayed as measured; the one-line proof via the digit projection
ℤ/E → ℤ/e_n is a candidate for the recommended unit, not asserted here.)

### 2.2 The tame hand case (the charged test): NR = 1 reproduces the symbol algebra exactly

One read (e, h, g) = (2, 1, 1) over base residue 𝔽_3 (a ramified quadratic
over ℚ_3): E = 2, no inner letters, c(a,b) = z̄^{⌊(a+b)/2⌋} — the graded
reduction of ℚ_3(√(z̄·3)) is 𝔽_3[v]/(v² − z̄) with the class z̄ mod
(𝔽_3^*)² deciding √3 vs √−3. This is verbatim the Kummer-symbol
presentation; the associated cyclic algebra (χ, π) is the one whose inv
local CFT computes, and the carry cocycle is its H²(ℤ/2, ℤ)-skeleton. The
candidate interpretation ("carry cocycle = image of the local fundamental
class under graded reduction") **holds in the tame cyclic case** in this
symbol form.

### 2.3 The wild case — and the frame's most useful output: the wild carry class is PROVABLY INVISIBLE at class level

For finite K^* (order q_K − 1), H²(ℤ/E, K^*) = K^*/(K^*)^E ≅
ℤ/gcd(E, q_K−1) — **the tame quotient**. At a wild tower E is a p-power
and q_K ≡ 1 has no p-part, so gcd = p-free: *every wild carry class dies*.
Measured (Appendix A):

    T2C (p=3, E=6, K=𝔽_3):  ζ_T = −1, order 2 — class NONTRIVIAL, and equal
                            to the full tame quotient ℤ/gcd(6,2) = ℤ/2
                            (the e_0 = 2 tame step's quadratic symbol;
                            consistent with z_1 = −1)
    T3A (p=2, E=8, K=𝔽_4):  ζ_T of order 3; gcd(8,3) = 1 — class TRIVIAL
    T2A (p=2, E=4, K=𝔽_4):  ζ_T of order 3; gcd(4,3) = 1 — class TRIVIAL

Three consequences, in decreasing solidity:

1. **The (CYC) fence is forced, not accidental.** JC-F1 found 𝒜(T) ≅
   K[v]/(v^E − ζ_T) abstractly at every stage while the anchor-indexed
   presentation stays non-cyclic — the frame says this MUST happen at wild
   primes: the class group has no room for wild information (a wild graded
   field over a finite residue field is even non-étale as an ungraded
   algebra: v^{p^k} − η^{p^k} = (v − η)^{p^k} in char p — the graded
   reduction of a wildly ramified field is "purely nilpotent" to the
   ungraded eye, yet a graded field). **All wild content is cochain-level.**
   This is a high-level explanation of why the whole campaign runs a
   LEDGER (cochain/presentation bookkeeping with fences) rather than a
   cohomology computation: at wild primes there is nothing at class level
   to compute.
2. **The CFT contextualization Asvin asked for, stated honestly.** Tame:
   the carry class = the tame symbol = (the graded shadow of) the
   fundamental class; abstract machinery (Kummer theory, graded Brauer/
   Tignol–Wadsworth) proves the bookkeeping in three lines. Wild: the
   Galois-side fundamental class is still there (inv is an isomorphism!),
   but the graded reduction functor kills its reflection; the wild
   information migrates to the filtration ON the units — in higher-CFT
   language, to the graded pieces of the unit filtration of Milnor K
   (Bloch–Kato: U^i K^M_2 / differential forms), which is Kato's territory.
   So "use higher CFT" is not a shortcut to our theorem; it is the correct
   NAME for the wall: q-uniformity of wild data = uniformity of exactly
   the graded unit pieces where standard motivic/cohomological uniformity
   stops. (Speculative paragraph; flagged as such.)
3. **A cheaper (DMULT-w) citation is plausible.** The graded-field facts
   the corpus consumes from FGMN through JC-LOC (homogeneous components
   are 1-dimensional; in(f)in(g) = in(fg) on B) are exactly the opening
   chapters of Tignol–Wadsworth's graded package — a second, independent
   literature leg for (F-c)'s citation fence if the FGMN numbering
   re-verification stays owed.

### 2.4 What H-B would prove or reorganize (the owed-items audit)

* **W-9 / JC-F1 / WM-CLASS**: become instances of graded-field structure
  theory (a graded field with cyclic value-group quotient over its
  degree-0 part is a Kummer twisted group algebra; class = ζ mod E-th
  powers). Reorganization, not new theorems — the corpus proved them
  already; the frame supplies the "why".
* **W2-OPEN-2** (the one irreducibly-new open lemma: two byte-different
  same-type key chains above a twist junction compute the same
  valuation/residual up to units): the frame NAMES its literature shape —
  **unicity of the valuation attached to a complete type** (MacLane–Vaquié;
  the "types parameterize valuations" theorems of the FGMN school; in
  Berkovich terms: the type data pins a point of the valuative tree, and
  both chains present that point). W2's own four-route adjudication
  already checked the classical key-equivalence route and found the
  recorded warrant (≥ key weight) strictly below the classical hypothesis
  (≥ assigned value) — so this is NOT claimed derivable; the honest
  statement is that H-B upgrades W2-OPEN-2 from "an open box with no
  home" to "a candidate instance of a named literature theorem-shape,
  acquirable only as a NEW faithful consumption with its own transcription
  and audit" (the alternative-discharge route W2 §5.2 itself flags).
* **(DMULT-s)** (ω ≡ 1, the measured exact tier): graded-unit rigidity
  makes the ∂(a/E) = 1 finding (synthesis §2.5) *natural* — the ratio
  a_λ/E(λ) is a homogeneous unit system whose coboundary vanishes, i.e. a
  character — but existence of SOME multiplicative normalization is all
  the abstract theory gives; that THE committed normalization is
  multiplicative stays a computation. Not discharged.
* **J-D count equality**: untouched (it is a measure statement; see H-C).

### 2.5 Where H-B breaks / becomes speculative

* 𝒜(T) is **commutative** (the carry cocycle is symmetric), so the class
  lives in Kummer theory (Ext¹/symmetric H²), not in the Brauer group
  proper; "symbol algebra" language is safe only in its graded/Kummer
  form. The full Brauer/Tignol–Wadsworth machinery for noncommutative
  graded division algebras is available but not needed by the corpus.
* The literal candidate "c = image of the local fundamental class under
  graded reduction" is exact tamely (§2.2) and **provably lossy wildly**
  (§2.3) — anyone hoping the CFT frame would *carry* the wild bookkeeping
  is refuted by the measurement, not just unaided.
* The Kato/higher-CFT paragraph is direction, not result.

---

## §3. H-C — MOTIVIC/DEFINABLE INTEGRATION: verdict **CORRECT AS POSITIONING, EMPTY AS MACHINERY** — the corpus itself contains the separating counterexample, and the honest high-level statement is a new uniformity mechanism where motivic transfer has none to offer

### 3.1 The separator is already in the corpus's conventions

HUMAN_PROOF §0, load-bearing display: at p = 2 the **value-weighted**
integral ∫|disc| = 7/12 ≠ 2/3 (its tame rational value), while the
**volume** of the same locus is the uniform q/(q+1). A Denef–Pas definable
integral — about as classical as they come — genuinely fails q-uniformity
at the wild prime, on the very family our theorem covers. Consequence: the
Goal Theorem (ρ(n,σ;q) = R_σ(q) for ALL prime powers, wild included,
palindromic) **cannot be an instance of any general motivic-uniformity
principle**, because no such principle is true in the wild regime for
arbitrary definable integrals. Standard results (Denef–Loeser,
Cluckers–Loeser transfer) are p ≫ 0 by construction.

### 3.2 What the OM stratification actually is, definability-wise

Each finite-depth OM stratum IS Denef–Pas definable, by a formula uniform
in p (polygon = valuation inequalities on coefficients; residual
polynomials = angular-component data at the lattice points). The wild
failure is not definability of the strata; it is that the motivic toolkit's
uniform-rationality guarantees stop at p ≫ 0. So the charged phrasing
("not definable in Denef–Pas but carry-definable") should be corrected to:
**definable as ever; uniformizable only by the carry mechanism.** The
mechanism, named from the corpus's own parts:

    volumes of type strata = (L3 universal residue-shape polynomials S_λ(q))
                           × (L4/BB1 lattice q-powers, char-free exponents)
                           over the L5fix finite p-independent shape menu,
    and the entire wild carry layer acts by unit characters with
    measure-preserving fibers — the synthesis's candidate lemma (J-D0)
    COUNT GAUGE-BLINDNESS: counts/volumes are invariant under the whole
    value-layer gauge (JA-RES characters, (ξ,w), ℓ-orbit rescalings).

**The high-level statement:** *Haar volume is carry-gauge-invariant; the
discriminant exponent is not.* v(disc) prices the carries (the wild part
of the different is exactly where the carry ledger pays letters), so
weighting by |disc| re-imports the wild data that volume quotients out —
and uniformity dies (7/12). The class of integrals the carry algebra
uniformizes, stated precisely: integrals ∫ F(type(f)) dμ of bounded
functions **factoring through the (coarse or OM-tree) type map** — i.e.
the σ-algebra generated by the carry-free skeleton (polygon lattice data +
residue shapes), with p-free weights. Conjecturally the right "language"
closes this class under the tree recursion (a "carry-definable" quantifier
package); nothing here needs that generality.

### 3.3 Situation against the mass-formula literature

Serre's mass formula (1978) and its descendants (Bhargava's mass formulae
for étale algebras; Kedlaya's and Krasner's counts) are the known
wild-inclusive q-uniform statements, and they are volume/count statements
of exactly this gauge-blind type — Serre's Eisenstein-cell computation is
an L4-style lattice volume (the corpus's (2,1,1) Eisenstein shape density
(q−1)/q³, synthesis §3.1, is the depth-1 relative). The Goal Theorem
refines this family from masses to the full factorization-type density
with the palindromic functional equation — the interpretation is that
**the carry algebra is the uniformity mechanism that the mass-formula
family was always secretly using** (Frobenius bijective on points,
inseparable on tangents — HUMAN_PROOF's one-sentence mechanism), now made
into a transport theory with its own cocycle bookkeeping.

### 3.4 Owed-items audit and break points

Proves now: nothing. hExhaust and drainage are untouched (the measure
route's AX_cellRecursion is plain Igusa §7.4 cell decomposition, already
cited; motivic language adds no leg). J-D: H-C is J-D's native frame —
(J-D0) is literally the "carry-gauge-invariance of volume" principle — but
the frame supplies vocabulary, not the proof. Break point: any attempt to
strengthen "carry-definable" into an actual model-theoretic language with
a rationality theorem is a research program, not a unit.

---

## §4. H-D — HERBRAND TRANSITION: verdict **FORMAL ANALOGY EXACT, LITERAL FACTORIZATION FALSE** (witness displayed), with the correct identification being the Okutsu depth function, and a real literature tie at the Eisenstein slice

### 4.1 The shared affine calculus

The shear Σ_q: (i, u) ↦ (i, e_q·u + h_q·i) acts on slopes by
σ ↦ e_q·σ + h_q (JB-VTX(c)); composed up the tower:

    σ ↦ E_{n+1}·σ + Σ_{l=0}^{n} h_l·∏_{l<t≤n} e_t        (T3A: σ ↦ 8σ + 7),

and the constant's summands are LED-Λ's quanta q_l = h_l·∏ e_t — the
**place values** of the mixed radix, re-surfacing as the transition
constant's digits. Herbrand's ψ_{L/K} is piecewise affine with slopes
1, e_1, e_1e_2, … composing along towers by the same affine semigroup —
the ramification-polygon literature states the identification directly:
the ramification polygon of an Eisenstein polynomial "is a formulation of
the Herbrand invariant" (Krasner originally; the modern theory is
Pauli–Sinclair, *ramification polygons + residual polynomials*,
arXiv:1504.06671/1512.06946 school). So the polygon-transport half of
WELD-M's (M1) does live in a classical transition calculus.

### 4.2 The breaking witness: residual degrees enter the OM recursion and never enter ψ

The OM weight recursion is γ_{j+1} = e_j·(e_{j−1}·g_{j−1}·γ_j) + h_j —
the factor g_{j−1} because key DEGREES grow by g (Okutsu depth), while
Herbrand transition functions are blind to residual growth (unramified
steps have ψ = id). Committed witness: **T2A** (p = 2, reads
(2,1,2),(2,1,1), g_0 = 2) has γ = (1, 9) — engine-read gam = [1, 9] — where
the Herbrand-shaped value for the same (e, h) data is 2·(2·1)+1 = 5 ≠ 9.
The M1 face does **not** literally factor through Herbrand transition
functions of the tower. The correct identification of the composed shear
is the **Okutsu depth/degree bookkeeping** (deg Φ_{j+1} = e_j g_j deg Φ_j),
of which the Herbrand function is the g ≡ 1, d₀ = 1 shadow — exactly the
Eisenstein/totally-ramified-monogenic slice where the Pauli–Sinclair tie
holds and Serre LF IV applies (Abbes–Saito for the non-Galois filtration,
flagged, not consumed).

### 4.3 Owed-items audit

Nothing advances: (M1) is already proved internally (JB-AFF/JB-VTX at
their grades) — a textbook citation would decorate, not discharge; and
W2-OPEN-2 / (DMULT-s) / J-D never touch ramification filtrations.
Interpretive residue worth keeping: **at the Eisenstein slice our shear
IS Herbrand's ψ**, so any future comparison with the extension-counting
literature (Krasner, Serre mass formula, Pauli–Sinclair enumeration by
ramification polygon) can be routed through that slice with confidence.

---

## §5. RANKING AND RECOMMENDATION

| frame | (a) interpretive value now | (b) plausibility of proving something owed | verdict line |
|---|---|---|---|
| **H-B graded reduction + Kummer/CFT** | HIGH — fundamental-class reading measured (class[κ] = 1); wild class-death measured; explains (CYC) and the ledger's cochain-level necessity | REAL BUT PRICED — names W2-OPEN-2's literature shape (new consumption + audit needed); second citation leg for (DMULT-w); (DMULT-s) made natural, not proved | **HOLDS; recommended** |
| **H-C motivic/definable** | HIGH — positions the theorem against Serre/Bhargava/Cluckers–Loeser; the corpus's own 7/12 example shows it is NOT a motivic corollary; names the new mechanism (carry-gauge-invariance of volume) | LOW — vocabulary for (J-D0), no new leg | correct as positioning |
| **H-A Witt/δ-rings** | MEDIUM — the odometer skeleton is real; the mechanism (carry = ∂ of digit truncation) is WM-COB | NIL — breaks at mixed radix, Teichmüller section (p ≥ 3 witness ℤ/9), weight conjugation (D_1 = 4 witness), letter pricing | fails cleanly |
| **H-D Herbrand** | LOW-MEDIUM — shared affine calculus; Eisenstein-slice tie genuine | NIL — g_0 = 2 witness (γ_2 = 9 ≠ 5); (M1) already proved internally | analogy, not factorization |

**Recommended single candidate for a future complete-theorem unit: H-B**,
as a GRADED-REDUCTION/CLASS unit with three deliverables, in order of
increasing risk:

1. **THEOREM (CLASS-TAME).** For every tower of the class pin over residue
   𝔽_{q_K}: H²(ℤ/E, K^*) ≅ ℤ/gcd(E, q_K−1), the class [c] equals its tame
   reflection, and at all-wild towers [c] = 1 — with class[κ] = 1 (the
   fundamental class) and class[δ] = (E/e_n)·ℓ_n proved rather than
   measured. Small, self-contained, consumes WM-CLASS + JC-F1; upgrades
   the (CYC) presentation-vs-class fence from observation to theorem;
   the Appendix A measurements are its preregistered predictions.
2. **The Tignol–Wadsworth citation leg**: transcribe the graded-field
   facts (component 1-dimensionality; Kummer form of graded fields with
   cyclic value quotient) as an independent literature leg beside FGMN for
   the (F-c) fence — standard faithfulness discipline (published source,
   transcription, audit).
3. **The W2-OPEN-2 adjudication probe** (highest risk, highest owed
   value): determine whether the MacLane–Vaquié/FGMN "type determines the
   valuation" unicity theorems, faithfully transcribed, cover the
   above-twist-junction chain comparison — explicitly allowed to return
   BLOCKED with the exact hypothesis gap (the ≥-key-weight vs
   ≥-assigned-value gap the W2 route-3 adjudication already displayed).

Per the effort directive: this note itself proves nothing, upgrades
nothing, and discharges nothing; all grades ride their owning notes.

**External sources named in this note** (memory-cited; lookup/transcription
owed before any consumption): Tignol–Wadsworth, *Value Functions on Simple
Algebras, and Associated Graded Rings*, Springer Monographs 2015
(https://mathweb.ucsd.edu/~wadswrth/vfgr.pdf for the precursor paper);
Pauli–Sinclair ramification polygons (https://arxiv.org/pdf/1504.06671,
https://arxiv.org/pdf/1512.06946); Serre, *Corps Locaux* XIII (inv via
valuation) and LF IV (Herbrand); Serre mass formula (CRAS 1978); Bhargava
mass formula (2007); Kedlaya counting (2007); Temkin graded reduction;
Teissier graded algebra of a valuation; MacLane–Vaquié key polynomials;
Joyal/Buium δ-rings; Bloch–Kato unit filtration of Milnor K; Abbes–Saito;
Cluckers–Loeser; Denef–Pas; Igusa §7.4 (= the committed AX_cellRecursion
citation).

---

## Appendix A — the scratch instruments (disclosed verbatim; NOT sealed runners: no preregistration, no teeth, exploratory grade only)

Engine: committed `verification/openmath/iterlawn_pe_reimpl.py`, verbatim
import. Towers: T2A/T2C/T3A = the weld-probe roster specs, copied
byte-for-byte from `WELD_SYNTHESIS_2026-08-05.md` Appendix A.

### A.1 `/tmp/hl_interp_tests.py` (odometer + naive-carry test + ζ_T)

```python
import sys
sys.path.insert(0, '<repo>/verification/openmath')
import iterlawn_pe_reimpl as ITL

SPEC_T2C = dict(id='T2C', ring='Zp', p=3, d0=1, Phi0=[0, 1], reads=[(2,1,1),(3,2,1)],
                psi=[[1,1],[('z',1,1),1]], pairn=6)
SPEC_T3A = dict(id='T3A', ring='Zp', p=2, d0=2, Phi0=[1, 1, 1],
                reads=[(2,1,1),(2,1,1),(2,1,1)],
                psi=[[('X',1),1],[('z',1,1),1],[('z',2,1),1]], pairn=8)
SPEC_T2A = dict(id='T2A', ring='Zp', p=2, d0=1, Phi0=[0, 1], reads=[(2,1,2),(2,1,1)],
                psi=[[1,1,1],[('z',1,1),1]], pairn=6)

def kpow(K, x, n):
    if n < 0: return kpow(K, K.inv(x), -n)
    acc = K.one()
    for _ in range(n): acc = K.mul(acc, x)
    return acc

def c_val(T, ga, gb):
    NR = T.NR
    c = T.constants(ga, gb)
    K = T.K[NR]
    acc = kpow(K, T.z[NR], c['delta'])
    for j in range(1, NR):
        zj_top = T.embed(T.z[j], j, NR)
        acc = K.mul(acc, kpow(K, zj_top, c['D'][j]))
    return acc, c

def E_of(T):
    E = 1
    for e in T.e[:T.NR]: E *= e
    return E

def section(T):
    E = E_of(T); sig = {}; g = 0
    while len(sig) < E and g < 100*E:
        if T.inW(g):
            nu = g % E
            if nu not in sig: sig[nu] = g
        g += 1
    return sig

for spec in (SPEC_T2C, SPEC_T3A, SPEC_T2A):
    T = ITL.build_tower(spec)
    NR = T.NR; E = E_of(T)
    sig = section(T)
    reps = [sig[nu] for nu in range(E)]
    # naive positional odometer on gamma itself, radices top-read-first
    def plain_carries(x, y, radices):
        cs = []; carry = 0
        for r in radices:
            xd, x = x % r, x // r
            yd, y = y % r, y // r
            tot = xd + yd + carry
            carry = tot // r
            cs.append(carry)
        return cs
    radices = list(reversed(T.e[:NR]))
    match = mismatch = 0
    for ga in reps:
        for gb in reps:
            if not T.inW(ga+gb): continue
            c = T.constants(ga, gb)
            corpus = [c['delta']] + [c['D'][j] for j in range(NR-1, 0, -1)]
            plain = plain_carries(ga, gb, radices)
            if corpus == plain: match += 1
            else: mismatch += 1
    K = T.K[NR]
    zeta = K.one()
    for k in range(1, E):
        v, c = c_val(T, sig[1], sig[k])
        zeta = K.mul(zeta, v)
    # multiplicative order of zeta_T
    o = 1; acc = zeta
    while str(acc) != str(K.one()):
        acc = K.mul(acc, zeta); o += 1
        if o > 5000: o = None; break
    print(spec['id'], 'match/mismatch:', match, mismatch, 'ord(zeta_T):', o)
```

Output (2026-08-07 run, condensed; full digit/carry tables reproduced in
§1.3): T2C match 16 / mismatch 20, ord(ζ_T) = 2 (K = 𝔽_3); T3A match 24 /
mismatch 40, ord(ζ_T) = 3 (K = 𝔽_4); T2A match 12 / mismatch 4,
ord(ζ_T) = 3 (K = 𝔽_4). Witness row (T2A): γ = γ′ = 9 → s(9) = (0,1),
s(18) = (1,0), δ = 1, **D_1 = 4**. Engine frame data: T2C ℓ = (1,2),
γ = (1,8); T3A ℓ = (1,1,1), γ = (1,5,21), wΦ = (2,10,42), section
σ = [0,25,10,35,4,21,14,31] (classes ≡ γ mod 8 ✓); T2A γ = (1,9),
wΦ = (4,18), z_1 letters as committed.

### A.2 `/tmp/hl_interp_tests2.py` (integer H² classes by orbit sums)

```python
import sys
sys.path.insert(0, '<repo>/verification/openmath')
import iterlawn_pe_reimpl as ITL
SPECS = [  # T2C, T3A, T2A specs exactly as in A.1
 dict(id='T2C', ring='Zp', p=3, d0=1, Phi0=[0, 1], reads=[(2,1,1),(3,2,1)],
      psi=[[1,1],[('z',1,1),1]]),
 dict(id='T3A', ring='Zp', p=2, d0=2, Phi0=[1, 1, 1],
      reads=[(2,1,1),(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1],[('z',2,1),1]]),
 dict(id='T2A', ring='Zp', p=2, d0=1, Phi0=[0, 1], reads=[(2,1,2),(2,1,1)],
      psi=[[1,1,1],[('z',1,1),1]]),
]
def E_of(T):
    E = 1
    for e in T.e[:T.NR]: E *= e
    return E
def section(T):
    E = E_of(T); sig = {}; g = 0
    while len(sig) < E and g < 100*E:
        if T.inW(g):
            nu = g % E
            if nu not in sig: sig[nu] = g
        g += 1
    return sig
for spec in SPECS:
    T = ITL.build_tower(spec); NR = T.NR; E = E_of(T); sig = section(T)
    Sdelta = 0; Skappa = 0
    for k in range(E):
        c = T.constants(sig[1], sig[k])
        Sdelta += c['delta']
        Skappa += (sig[1] + sig[k] - sig[(1+k) % E])//E
    print(spec['id'], 'class[delta] =', Sdelta % E, 'class[kappa] =', Skappa % E, 'mod', E)
```

Output (2026-08-07 run, verbatim):

    T2C: E=6  class[delta]=4 mod 6  class[kappa]=1 mod 6
    T3A: E=8  class[delta]=4 mod 8  class[kappa]=1 mod 8
    T2A: E=4  class[delta]=2 mod 4  class[kappa]=1 mod 4

(Orbit-sum invariant: for an integer 2-cocycle c on ℤ/E, Σ_{k=0}^{E−1}
c(1,k) mod E computes its class under H²(ℤ/E, ℤ) ≅ ℤ/E. The D_j orbit
sums do NOT vanish mod E because ∂t_j descends to ℤ/E only after the
ρ_T^κ period correction — which is exactly WM-CLASS's content; the class
identity is untouched.)

— HIGH-LEVEL INTERPRETATION unit, 2026-08-07.
