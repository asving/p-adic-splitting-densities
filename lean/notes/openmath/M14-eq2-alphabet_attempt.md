# M14-eq2-alphabet — attempt (Fable, 2026-07-31)

## Resolution in one paragraph

Both conjuncts of (EQ-2) are PROVED here conditional on an explicitly
displayed four-item hypothesis package (R1)–(R4) that is a *sub-slice of
REL.1* — the corpus's own recorded conditionality for this row ("(EQ-2) …
OPEN, REL.1-conditional"), so no new conditionality is introduced.
Conjunct (i) (F_{p^δ}-linearity of the re-based slot map) needs only the
re-based stage package and is proved by exhibiting the canonical residue
action: Teichmüller multiplication descends to an honest F_{p^δ}-module
structure on each graded piece, and the piece map R_γ = (·)·T^{−γ} is
L₀-linear, hence F_{p^δ}-linear (Lemma 2). Conjunct (ii) (a_δ = δ·a₁ on the
δ-stable domain) is proved by an induction up the tower prefix: the entire
numerical skeleton of the alphabet recursion — weight sets 𝒲_k, anchor slots
j₀, slot heights γ_i, attainable index sets I(γ) — is determined by the stage
tuples (e_k, h_k, g_k) alone (Lemma 1, unconditional), which δ-stability
matches across the base change; the base alphabet scales by δ ([F₁^{(δ)}:F_p]
= δ·d), and the product display propagates the factor δ through every stage
(Theorem). A by-product characterizes the δ-stable domain: under the
same-keys transport, a position of accumulated residue degree m is δ-stable
iff gcd(m, δ) = 1 (Lemma 4, conditional on the owed transport dictionary).
Verdict: REDUCED — to (R1)–(R4), i.e. to REL.1's tower/ledger slice.

Notation as in the brief (`M14-eq2-alphabet_brief.md`): q := p^δ,
F_δ := F_q ⊂ F̄_p, O_δ := W(F_q), A^{(δ)} := O_δ[x]; the ℤ_p-side tower has
stages k = 1, …, K with coefficient spaces C_k, keys Φ_k, residue fields F_k
([F₁ : F_p] = d, F_{k+1} = F_k[z]/(ψ_k), g_k = deg ψ_k), read indices
(e_k, h_k), Bézout t_k, weight sets 𝒲_k; superscript (δ) marks the re-based
(matched) objects. a(k, γ) := dim_{F_p} 𝔸(k, γ) at the stage-k position of
height γ; the Lean row's `aDim δ x` is a(δ-side) and `aDim 1 x` is a(ℤ_p-side).

## 1. Reading of the obligation

The Lean row `cl8_eq2 : ∀ p [Fact p.Prime], EQ2law p (KC.AD p)` asserts, at
the intended (not yet built) instance and per prime: for all δ ≥ 1 and
positions x with `posLetter δ x = posLetter 1 x`,
(i) `IsLinearMap F_δ (slotMap δ x)` and (ii) `aDim δ x = δ * aDim 1 x`.
The instance reading (brief §"intended concrete reading") makes this exactly
the note's (EQ-2) law on its pinned per-position-class domain. Throughout, a
position class x = (tower-prefix shape; stage index k+1 ≤ K+1; height γ), and
δ-STABILITY is read as PREFIX stability: the matched re-based prefix realizes
the same letters, i.e. the same (e_j, h_j, g_j) for j ≤ k and the same d, with
every re-based residual polynomial irreducible of the matched degree. (§8.2
records why the instance MUST encode this in `posLetter` and what evidence
says letter-only stability is insufficient.)

## 2. The hypothesis package (R) — the REL.1 slice consumed

The note types (EQ-2) as "OPEN, REL.1-conditional" and orders it as "an
output of [REL.1's] walk, never an input". Accordingly the proof below
consumes exactly the following displayed re-based facts and nothing else.
Each is the verbatim O_δ-analogue of an ACCEPTED base-ℤ_p statement, i.e. an
item of REL.1's re-scoping pass:

- **(R1) Re-based stage package.** At the matched prefix over O_δ, the stages
  satisfy §B2-DEF's axioms (S1)–(S6) over the base O_δ with the D.0 scale
  bookkeeping; in particular: w is a valuation ((S1), multiplicative), the
  base-stage weight on constants is w₁(c) = e₁·v(c) (v = Gauss valuation of
  O_δ, normalized v(p) = 1), coefficient weights stretch by w_{k+1} = e_{k+1}·w_k
  (D.0), (L^coeff)₀ = F^{(δ)} ((S4)), and the rank-1 piece maps
  R_γ : L_γ → L₀, ξ ↦ ξ·T^{−γ} are L₀-linear with R multiplicative (D.1(e) —
  a purely graded-algebra fact whose base-side proof is base-agnostic).
- **(R2) Re-based digit/alphabet displays.** D.3(e)(ii)'s displays hold over
  O_δ: the digit recursion (ii.2), the alphabet product display
  𝔸^{(δ)}(γ) = u^{(δ)}(γ)·{Σ_{i∈I^{(δ)}(γ)} c_i·z̄^i : c_i ∈ 𝔸_k^{(δ)}(γ_i)}
  with |𝔸^{(δ)}(γ)| = Π_{i∈I^{(δ)}(γ)} |𝔸_k^{(δ)}(γ_i)| (mechanism: 𝔸_k^{(δ)} ⊆
  F_k^{(δ)} and (1, z̄, …, z̄^{g_k−1}) an F_k^{(δ)}-basis of F_{k+1}^{(δ)}),
  and the base clause 𝔸₁^{(δ)}(e₁v) = F₁^{(δ)} (the base digit display onto).
- **(R3) Re-based weight-set recursion.** D.9(a) over O_δ:
  𝒲^{(δ)}_{k+1} = e_{k+1}·⋃_{0≤j<e_k g_k}(𝒲^{(δ)}_k + j·h_k), with base
  𝒲₁^{(δ)} = e₁·ℤ≥0 (single-slot realizers p^v·(unit) exist over O_δ exactly
  as over ℤ_p).
- **(R4) Stability semantics.** x is δ-stable in the prefix sense of §1: the
  matched prefix has stage tuples (e_j, h_j, g_j)_{j≤k} and base degree d
  equal to the ℤ_p-side ones, with each ψ_j^{(δ)} irreducible of degree g_j
  over F_j^{(δ)} (this is what letter persistence, matched per the (a6)/(EQ-1)
  dictionary, MEANS; the dictionary itself is a separate owed REL.1 artifact).

Honesty check on the package: (R1)–(R3) are not proved anywhere yet — they
ARE (part of) REL.1, the corpus's open kernel; (R4) is definitional given the
owed dictionary. The reduction below is therefore exactly the conditionality
the ledger already displays for this row, made itemized and minimal (nothing
of REL.1's counting layer — Theorem C(a)/(b), PIN-WELLDEF, (ZC) — is used).

## 3. Lemma 1 — the numerical skeleton is shape-determined (unconditional)

**Lemma 1.** Suppose two towers (any two bases) satisfy the D.9(a) recursion
of (R3) with the same numerical data d, (e_j, h_j, g_j)_{j≤k}. Then:
(a) 𝒲^{(δ)}_j = 𝒲_j for all j ≤ k, and the top-space weight sets agree;
(b) for every height γ at stage j+1 ≤ k+1: the stretch γ*, the anchor slot
j₀ ≡ t_j·γ* (mod e_j), the slot heights γ_i = γ* − (j₀ + i·e_j)·h_j
(0 ≤ i < g_j), and the attainable index set I(γ) = {i < g_j : γ_i ∈ 𝒲_j}
coincide on the two sides.

*Proof.* (a) Both weight-set sequences satisfy the same recursion
𝒲_{j+1} = e_{j+1}·⋃_{0≤i<e_j g_j}(𝒲_j + i·h_j) with the same base
𝒲₁ = e₁·ℤ≥0 — a purely arithmetic recursion in the shared data — so they are
equal by induction on j; the top-space set is the j = k instance without the
final stretch, likewise equal. (b) γ* = γ/e_{j+1} (γ at the top) uses only
e_{j+1}; t_j is the mod-e_j inverse of h_j, shared; j₀ and each γ_i are
arithmetic in (γ*, t_j, e_j, h_j), shared; I(γ) then agrees by (a). ∎

*Status: (c) claimed new (project-specific bookkeeping); the proof is
complete and unconditional given that both towers satisfy (R3)'s recursion —
on the base side D.9(a) is accepted, on the re-based side it is (R3).*

## 4. Lemma 2 — the residue action and F_δ-linearity (conjunct (i))

**Lemma 2.** Assume (R1) at a re-based prefix. Let τ : F_q → O_δ be the
Teichmüller section (multiplicative: τ(ζζ′) = τ(ζ)τ(ζ′); additive mod p:
τ(ζ+ζ′) ≡ τ(ζ)+τ(ζ′) (mod pO_δ)) [known: Serre, *Corps Locaux*, Ch. II §4–5;
standard Witt-vector theory]. Then for every stage k of the prefix and every
height γ:

(a) w_k(τ(ζ)·f) = w_k(f) for every ζ ∈ F_qˣ and f ≠ 0; hence ζ·[B]_γ :=
[τ(ζ)·B]_γ is a well-defined F_q-scalar action on the graded piece
gr_γ := A^{(δ)}_{≥γ}/A^{(δ)}_{>γ}, making gr_γ an F_q-vector space and each
coefficient piece gr^{C}_γ an F_q-subspace;
(b) the map ι : F_q → (gr)₀, ι(ζ) := [τ(ζ)]₀ (ι(0) := 0) is a ring embedding
with image inside F^{(δ)} = (L^coeff)₀;
(c) the piece map R_γ : gr_γ → L₀ is additive and F_q-linear:
R_γ(ζ·ξ) = ι(ζ)·R_γ(ξ); consequently the height-γ digit map
d_γ = R_γ ∘ ([·]_γ) on the level set {w ≥ γ} is additive and F_q-equivariant.

*Proof.* (a) First w_k(τ(ζ)) = 0: at the base stage, τ(ζ) is a constant of
Gauss valuation 0 and w₁(τ(ζ)) = e₁·v(τ(ζ)) = 0 by (R1)'s base display; at a
deeper stage, τ(ζ) ∈ C_{k+1} is its own Φ_k-development (single slot j = 0),
so w_{k+1}(τ(ζ)) = e_{k+1}·w_k(τ(ζ)) = 0 by D.0's stretch, closing the
induction. Then w_k(τ(ζ)f) = w_k(τ(ζ)) + w_k(f) = w_k(f) by (S1)
multiplicativity. So multiplication by τ(ζ) preserves A_{≥γ} and A_{>γ} and
descends to gr_γ; it is additive in the vector (ring distributivity). Module
axioms in the scalar: τ(1) = 1 gives 1·ξ = ξ; τ(ζζ′) = τ(ζ)τ(ζ′) gives
associativity; for distributivity, τ(ζ+ζ′) − τ(ζ) − τ(ζ′) ∈ pO_δ and
w_k(p·B) = w_k(p) + w_k(B) > w_k(B) ≥ γ (w_k(p) > 0: base w₁(p) = e₁ ≥ 1,
then stretched by positive factors), so [τ(ζ+ζ′)B]_γ = [τ(ζ)B + τ(ζ′)B]_γ =
ζ·ξ + ζ′·ξ. Coefficient pieces: τ(ζ)·B has the same x-degree as B, so C is
preserved. (b) ι is multiplicative and additive-in-degree-0 by the same two
computations (τ multiplicative; the mod-p defect dies in degree 0 because
w(p) > 0); nonzero classes are nonzero, and a ring hom from a field is
injective. ι(ζ) is the class of a CONSTANT of O_δ — an element of the
coefficient side needing no localization — so ι(ζ) ∈ (L^coeff)₀ = F^{(δ)} by
(R1)'s (S4). (c) R_γ is L₀-linear (R1's D.1(e)); for the scalar:
R_γ(ζ·ξ) = (ι(ζ)·ξ)·T^{−γ} = ι(ζ)·(ξ·T^{−γ}) = ι(ζ)·R_γ(ξ) by commutativity
and the fact that [τ(ζ)B]_γ = ι(ζ)·[B]_γ in the graded ring (initial form of
a product with w additive — D.1(c)). The digit map factors through
B ↦ [B]_γ (additive on {w ≥ γ}, with the convention [B]_γ = 0 when
w(B) > γ, and F_q-equivariant by (a)); compose with R_γ. ∎

Two remarks. (1) NO stability is consumed: Lemma 2 holds at every re-based
position where the re-based stage exists; stability only selects WHICH
re-based position is "the matched x". (2) At δ = 1, `Stable 1 x` is trivially
true for every x and conjunct (i) reduces to F_p-linearity, which is
additivity (prime field) — the accepted base-side D.3(e)(i); conjunct (ii)
reduces to a₁ = 1·a₁. So the δ = 1 slice of `EQ2law` carries no new content.

*Status: (c) claimed new in this packaging; the Teichmüller facts and graded
generalities are (a) known; conditional on (R1) only.*

## 5. Theorem — the dimension law a_δ = δ·a₁ (conjunct (ii))

**Lemma 3 (base case).** Under (R1), (R2), (R4): at a base-stage position
(1, e₁v), 𝔸₁^{(δ)} = F₁^{(δ)} and 𝔸₁ = F₁ (the two base displays), and
dim_{F_p} F₁^{(δ)} = [F₁^{(δ)} : F_q]·[F_q : F_p] = d·δ = δ·dim_{F_p} F₁,
using (R4)'s matched base degree [F₁^{(δ)} : F_q] = d. ∎

**Theorem (EQ-2)(ii).** Under (R1)–(R4), for every position (k+1, γ) in the
δ-stable prefix of x (including x itself at the top space):
a^{(δ)}(k+1, γ) = δ · a(k+1, γ).

*Proof.* Induction on the stage index, base = Lemma 3. Step: assume the law
at every stage-k position of the prefix. Note each slot position (k, γ_i)
appearing below IS a stage-k position of the same prefix (its prefix is an
initial segment of x's), hence δ-stable under (R4)'s prefix reading, so the
induction hypothesis applies to it. Compute:

  |𝔸^{(δ)}(k+1, γ)| = Π_{i∈I^{(δ)}(γ)} |𝔸_k^{(δ)}(γ_i)|        [(R2) product
      display; its mechanism consumes ψ_k^{(δ)} irreducible of degree g_k
      over F_k^{(δ)} — exactly (R4)'s letter persistence at stage k+1]
    = Π_{i∈I(γ)} |𝔸_k^{(δ)}(γ_i)|                               [Lemma 1(b):
      I^{(δ)}(γ) = I(γ), and the heights γ_i agree]
    = Π_{i∈I(γ)} p^{δ·a(k, γ_i)}                                 [induction]
    = p^{δ·Σ_{i∈I(γ)} a(k, γ_i)} = p^{δ·a(k+1, γ)}               [accepted
      base-side product display, giving a(k+1, γ) = Σ_{i∈I(γ)} a(k, γ_i)].

If I(γ) = ∅ both alphabets are {0} (a = 0 = δ·0). The forced units u(γ),
u^{(δ)}(γ) are bijections and never affect cardinalities. Taking log_p gives
a^{(δ)}(k+1, γ) = δ·a(k+1, γ). ∎

**Corollary (consistency + Lean `card_eq`).** Under (R1)–(R2): 𝔸^{(δ)}(γ) =
R_γ(gr^{C}_γ) is the image of an F_q-subspace under an F_q-linear map (Lemma
2), hence an F_q-subspace of F^{(δ)}-side values; in particular δ | a_δ
(consistent with the Theorem), |𝔸_δ| is an exact p-power (the instance's
`card_eq` field), and the slot-map range is already an additive subgroup, so
`alpha_attain`'s `AddSubgroup.closure` is a no-op at the intended instance. ∎

*Status: (c) claimed new; complete proofs conditional on (R1)–(R4) as
displayed. This is, to my knowledge, not in the literature in this form: the
per-height attainable alphabets 𝔸(γ) ⊊ F_{k+1} at shallow heights are a
project construction (standard OM/Montes theory works with full residue
fields; cf. GMN, "Newton polygons of higher order in arithmetic", J. Number
Theory 2012 — no shallow-height alphabet appears there).*

## 6. Lemma 4 — the δ-stable domain, characterized (test-design tool)

**Lemma 4.** Same-keys transport setting: the re-based read is of the same
input data with the ℤ_p-tower keys viewed in O_δ[x] (the natural matching the
(a6)/(EQ-1) dictionary is owed to produce), so that residual polynomials
transport verbatim along F_k ↪ F_k·F_q. Let m := d·g₁···g_k be the
accumulated residue degree through x's letter. Then x is δ-stable iff
gcd(m, δ) = 1, and in that case F_j^{(δ)} = F_j·F_q for all j ≤ k+1.

*Proof.* Two standard facts: (F1) an irreducible ψ of degree g over a finite
field E stays irreducible over an extension E′/E of degree δ′ iff
gcd(g, δ′) = 1 (it factors into gcd(g, δ′) conjugate factors of degree
g/gcd(g, δ′)) [known: Lidl–Niederreiter, *Finite Fields*, Thm. 3.46]; (F2)
[E·F_q : E] = δ/gcd(δ, [E : F_p]) (composita of finite fields). Induct up the
prefix. Stage 1: the base residual (degree d over F_p) stays irreducible over
F_q iff gcd(d, δ) = 1 (F1 with E = F_p, δ′ = δ); then F₁^{(δ)} = F₁·F_q with
[F₁^{(δ)} : F₁] = δ (F2). Step: given the prefix stable through stage j with
gcd(m_j, δ) = 1, m_j := d·g₁···g_{j−1}, we have [F_j·F_q : F_j] = δ (F2), and
ψ_j stays irreducible over F_j^{(δ)} = F_j·F_q iff gcd(g_j, δ) = 1 (F1); then
m_{j+1} = m_j·g_j is again coprime to δ. At the first failure the residual
factor splits — the species changes and x is out of domain; if no failure,
every letter persists. Both directions follow. ∎

*Status: (F1)/(F2) are (a) known; the characterization is (c) claimed new,
CONDITIONAL on the same-keys transport identity (that the re-based run of the
same input realizes the verbatim-transported residual polynomials) — a
REL.1/(a6)-dictionary fact, flagged, not proved here. Lemma 4 is NOT consumed
by §§3–5 (there stability is a hypothesis); it predicts WHERE the hypothesis
holds, which the numeric tests below use. It also independently reproduces
the note's worked instance: p = 3, ψ = z² + 1, δ = 2 has gcd(g, δ) = 2 ≠ 1 —
split, out of domain, exactly as recorded.*

## 7. Faithfulness notes for the eventual Lean instance

- **7.1 SlotDom must be the graded piece.** The Teichmüller "action" on the
  raw coefficient level set is NOT a module structure ((ζ+ζ′)·B = ζ·B + ζ′·B
  fails in O_δ[x] by the mod-p defect); it becomes one exactly on gr_γ
  (Lemma 2(a)). An instance declaring `Module (Fsub p δ)` on the raw level
  set via τ would be unsound. This matches the standing CInterface trap F3-1
  ("the additive object is the level-set-digits → graded-piece composite …
  never jet-additivity on box points").
- **7.2 `Stable` must entail prefix stability.** The Theorem's induction
  consumes stability of every sub-position; with letter-only stability at x
  the induction hypothesis is unavailable, and the note's F₉ instance shows
  interior splitting genuinely redistributes alphabet dimensions. The
  instance should make `posLetter δ x` encode the matched prefix (e.g.
  return a designated off-domain letter when any prefix residual splits), so
  that the Lean `Stable` ⟺ (R4). An instance with a coarser `posLetter` is
  NOT covered by this proof and is expected to admit countermodels.
- **7.3 `card_eq` and `alpha_attain`** are discharged by the Corollary.
- **7.4 The module structures are instance data**: `IsLinearMap` is asserted
  w.r.t. the carried structures; the instance must carry Lemma 2's structures
  (τ-action on gr; ι-multiplication on the carrier) for conjunct (i) to have
  its intended meaning.

## 8. What remains open (the reduction targets)

- **(O1)** The re-based stage/ledger package (R1)–(R3) — REL.1's tower slice.
  This is the corpus's standing open kernel; nothing here shrinks it, but
  §§4–5 show (EQ-2) needs ONLY this slice, not REL.1's counting layer.
- **(O2)** The (a6)/(EQ-1) matching dictionary defining "the matched
  position" and `posLetter δ` (consumed as (R4); also the conditionality of
  Lemma 4's transport setting).
- **(O3)** The Lean instance itself (`AlphabetData` fields per §7), and the
  Lean derivation of the row from a formalized (R)-package.

## VERDICT

**REDUCED.** Both conjuncts of (EQ-2) are proved from the explicit package
(R1)–(R4): conjunct (i) from (R1) alone (Lemma 2 — at every position, no
stability needed); conjunct (ii) from (R1)–(R4) (Theorem, via the
unconditional skeleton Lemma 1). The package is a proper sub-slice of REL.1,
the conditionality the ledger already records for this row, so the reduction
strictly sharpens the row's status: (EQ-2) is not an independent open kernel
but a consequence of REL.1's tower/ledger slice plus arithmetic. Bonus
artifacts: the F_q-subspace corollary (discharging `card_eq`/`alpha_attain`
shape duties), the domain characterization gcd(m, δ) = 1 (Lemma 4,
dictionary-conditional), and two instance-design constraints (§7.1, §7.2)
that the eventual Lean instance must respect. Not literature-axiom-eligible:
no published statement matches the shallow-height attainable alphabets (the
closest literature — GMN's higher-order Newton polygons, Montes/Nart types
under base change — has the full-residue-field case only, where (ii) is the
degree formula [F_{k+1}·F_q : F_p] = δ·[F_{k+1} : F_p] under coprimality).

## NUMERIC-TESTS

All tests are sympy-implementable (finite-field arithmetic via polynomial
quotients; Galois rings GR(p^M, δ) = (ℤ/p^M)[a]/(f) with f a lift of an
irreducible degree-δ polynomial; Teichmüller via a ↦ a^{q^M}-iteration).

1. **T1 — one-stage tower, exhaustive vs sampled δ-scaling (the main
   falsifier).** p = 3, base key x (d = 1), read (e₁, h₁) = (2, 1) (t₁ = 1),
   ψ = z² + 1 over F₃ (g = 2, irreducible). Top space Ĉ = {deg_x < 4},
   digits in F₉ = F₃[z]/(z²+1). ℤ₃-side: enumerate ALL B = Σ b_j x^j,
   b_j ∈ ℤ/3⁴ (3^16 ≈ 4.3·10⁷ — subsample to b_j ∈ ℤ/27 exhaustive = 5·10⁵
   if slow); compute w(B) = min_j(2·v₃(b_j) + j), and for γ := w(B) ≤ 6 the
   digit Σ_{min slots j} (b_j/3^{v} mod 3)·z^{(j−j₀)/2} ∈ F₉ (j₀ = γ mod 2);
   collect value sets 𝔸(γ). PREDICTED: |𝔸(0)| = |𝔸(1)| = 3 (shallow:
   I = {0}), |𝔸(γ)| = 9 for γ ≥ 2. δ = 3 side (gcd(m, δ) = gcd(2, 3) = 1 —
   in-domain by Lemma 4): O₃ = GR(3^4, 3) via a³ − a − 1; ψ = z² + 1 stays
   irreducible over F₂₇ (verify with sympy factor_list over GF(27)); sample
   10⁶ random B with coefficients in GR(3^4,3), same computation with
   residues in F₂₇, digits in F₂₇[z]/(z²+1) = F₇₂₉; collect observed value
   sets per γ ≤ 4. CONFIRMS (EQ-2)(ii) iff |𝔸^{(δ)}(γ)| = |𝔸(γ)|³ exactly:
   27 at γ ∈ {0, 1}, 729 at γ ≥ 2 (sampling saturates: ≤ 729 values, ≥ 10⁴
   hits per γ). REFUTES if any stabilized count differs, or any observed
   value falls outside the predicted F₂₇-span {Σ_{i∈I(γ)} c_i z̄^i}.
   CONFIRMS conjunct (i) (Lemma 2's equivariance, q = p^δ = 27) if
   d_γ(τ(ζ)·B) = ζ·d_γ(B) for 10⁴ random pairs (ζ ∈ F₂₇ˣ, B), where τ(ζ) is
   the Teichmüller lift computed in GR(3^4, 3) by iterating u ↦ u^{27} to its
   fixpoint, and if each observed 𝔸^{(δ)}(γ) is closed under addition and
   under multiplication by F₂₇ (the F_q-subspace corollary).
2. **T2 — the p-power and F_p-subspace law (Corollary).** In both sides of
   T1, assert every collected 𝔸 is an additive subgroup (closed under + and
   containing 0) and |𝔸| is a power of p. REFUTES the Corollary (and the
   instance's `card_eq`) on any failure.
3. **T3 — out-of-domain sanity (the note's instance, independent re-run).**
   p = 3, same tower, δ = 2: verify z² + 1 factors over F₉ into two linear
   factors (sympy over GF(9)); per branch, the continuation field is F₉ and
   the per-branch full-height alphabet is F₉ (a_branch = 2 ≠ δ·a = 4) —
   reproducing the note's recorded out-of-domain numbers. CONFIRMS the domain
   pin is necessary (a passing naive comparison here would instead suggest
   the pin is too conservative). Also check Lemma 4's prediction table on
   this family: (g, δ) ∈ {(2,2): split, (2,3): stable, (2,4): split,
   (2,5): stable, (3,3): split, (3,2): stable} via sympy factorization of an
   irreducible degree-g ψ over GF(p^δ)-extensions of the tower field.
4. **T4 — two-stage tower, recursion-level scaling.** p = 2, stage 1
   (e₁, h₁) = (2, 1), ψ₁ = z² + z + 1 (F₄); stage 2 read (e₂, h₂) = (2, 3)
   (gcd = 1) with ψ₂ an irreducible cubic over F₄ (e.g. z³ + z + w, w a
   generator — verify irreducible); δ = 5 (gcd(m, δ) = gcd(6, 5) = 1).
   Implement the ALPHABET RECURSION symbolically on both sides (weight sets
   by D.9(a); dims by a(k+1, γ) = Σ_{i∈I(γ)} a(k, γ_i); base dims 1 resp. 5)
   for all heights γ ≤ 100. CONFIRMS Lemma 1 + the Theorem's arithmetic iff
   a^{(δ)}(γ) = 5·a(γ) at every height and every stage — including shallow
   heights where a < [F₃ : F_p]-full. (This tests the induction's
   bookkeeping, not the displays; the displays are tested by T1.)
   OPTIONAL heavy version: brute-force stage-2 digits over GR(2^M, 5),
   M = 4, sampled 10⁶, against the recursion's predicted value sets —
   implements the full two-stage residual computation (~150 lines).
5. **T5 — cross-check against the outlined REL-n4 gate** (p = 2, n = 4,
   δ = 2, conditioning on an irreducible quadratic root read): once that
   gate's spec sheet exists, its exponent comparisons at δ-stable positions
   must instantiate the Theorem (q ↦ q² exponent preservation); any exponent
   mismatch at a certified-stable position REFUTES (EQ-2)(ii) as a whole,
   not just the gate.

### PRELIMINARY RUN (executed 2026-07-31, this session)

A mini version of T1 was run (p = 3, tower x/(e,h) = (2,1)/ψ = z²+1, δ = 3;
base side exhaustive over (ℤ/27)⁴ = 531441 boxes, GR(3³, 3)-side 4·10⁵
biased samples; digit = un-normalized leading residual pair over the residue
field; alphabet = {0} ∪ {values at weight exactly γ} — note the value set on
{w ≥ γ} always contains 0, contributed by deeper B; a first run that forgot
the 0 came out shifted by exactly one at every height, confirming the
level-set reading of the domain). RESULT — all PASS:

  |𝔸(γ)|, γ = 0..4:        3, 3, 9, 9, 9      (predicted 3, 3, 9, 9, 9)
  |𝔸^{(δ)}(γ)|, γ = 0..4:  27, 27, 729, 729, 729 = |𝔸(γ)|³ exactly
  shallow-span check (γ ∈ {0,1}: z̄-component ≡ 0 on both sides): PASS
  additive closure of the shallow base alphabet: PASS

This confirms the δ-scaling AT SHALLOW HEIGHTS (I(γ) = {0} ⊊ {0,1}) and the
skeleton matching, on an in-domain instance (gcd(m, δ) = gcd(2, 3) = 1).
Caveat: with d = 1 the per-slot alphabets are full fields, so the run does
not yet exercise a NESTED proper sub-alphabet — that is T4's job (two-stage
tower), still to be run.
