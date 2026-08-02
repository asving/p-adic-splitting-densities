# HDISCHARGE_H4 — discharge blueprint for (H4a) = (R1)–(R4) and (H4b) = (UB-X) incl. (K3-δ)

*(H4 discharge lead, 2026-08-05 swarm (ledger §"ASVIN DIRECTIVE (2026-08-05): THE
HYPOTHESIS-DISCHARGE SWARM"). Authority: `docs/ROOT_ASSEMBLY_2026-08-02.md` at
REVISION 12 — the (ROOT-C) block (H4a)/(H4b) displays + the §3.1 rows "(R1)–(R4)"
and "(UB-X)". Math sources of record: `lean/notes/openmath/M14-eq2-alphabet_brief.md`
+ `M14-eq2-alphabet_attempt.md` (the O-8b conditional proof — where (R1)–(R4) are
ITEMIZED), `lean/notes/MOVES_2026-07-24.md` §B2-DEF (line 1849 ff.; the T-1 stage
laws being re-scoped) and §[2r]/REL.1 (~line 9379) + §R.1 (EQ-1)/(EQ-2) (~line 9540),
`lean/notes/openmath/O11_phaseB_attempt.md` §3.4 (K3-c) + §5 row 18 (the D-c
interface), `docs/MATH_COMPLETION_TREE_2026-08-01.md` nodes O-8b (§ item 9) and D-3
(UNRAM-TRANSFER). Blueprint-only unit: NO `.lean` file lands with this unit; every
§L statement below was COMPILE-PROBED against the built corpus (probe record §L.0).)*

## 0. The group, verbatim (what must be discharged)

**(H4a) = (R1)–(R4)** [ROOT §3.1 row]: *"the T-1 stage-tower laws re-proved verbatim
over O_δ = W(F_{p^δ})"*. Owner O-8b (M14's conditional proof closes given them).
Consumed by clause (UB) (Step 16) AND clause (R) (Step 18's K3-c — the base-changed
β-legs at q ↦ q^δ, δ > 1 pools; O-11 r2's declared row D-c). Grade: [M], "expected
mechanical ('nobody has written it')"; borderline [M]/[T], kept [M] for honesty.
N8 numerics exhaustive (199,723 alphabets, 17 fields, 0 violations).

**(H4b) = (UB-X)** [ROOT §3.1 row], three members:
  (a) the per-leaf O_δ re-base audit for the ℚ_p-stated leaves (the "per-leaf scope
      hygiene" of the D-3 collapse, declared at the GD dispatch but unwritten);
  (b) δ-stable position classes exhaust the realized ledger at every δ — whose
      restriction to Step 18 K3-c's realized δ > 1 pools is the named fragment
      **(K3-δ)**, consumed by clause (R) [REVISION 4, finding VC4-1];
  (c) full solve + type aggregation commute with unramified base change.
Only (H4b) MINUS (K3-δ) is clause-(UB)-exclusive. ROOT's standing disposition for
(K3-δ): *"A direct match display (or a re-scope) rides the next O-11/O-8b touch and
would return clause (R) to (H4a)-only at this interface."*

**Itemization of (R1)–(R4)** (M14 attempt §2 — the operative fine structure; each is
the O_δ-analogue of an ACCEPTED base-ℤ_p §B2-DEF statement):
- **(R1) Re-based stage package**: §B2-DEF axioms (S1)–(S6) over base O_δ with the
  D.0 scale bookkeeping (w a valuation; w₁(c) = e₁·v(c), v = Gauss valuation
  normalized v(p) = 1; stretch w_{k+1} = e_{k+1}·w_k; (L^coeff)₀ = F^{(δ)};
  R_γ : L_γ → L₀ L₀-linear, R multiplicative — D.1(e)).
- **(R2) Re-based digit/alphabet displays**: D.3(e)(ii) over O_δ — the digit
  recursion (ii.2), the alphabet product display |𝔸^{(δ)}(γ)| =
  Π_{i∈I^{(δ)}(γ)} |𝔸_k^{(δ)}(γ_i)| (mechanism: (1, z̄, …, z̄^{g_k−1}) an
  F_k^{(δ)}-basis of F_{k+1}^{(δ)}), and the base clause 𝔸₁^{(δ)}(e₁v) = F₁^{(δ)}.
- **(R3) Re-based weight-set recursion**: D.9(a) over O_δ — 𝒲^{(δ)}_{k+1} =
  e_{k+1}·⋃_{0≤j<e_k g_k}(𝒲^{(δ)}_k + j·h_k), base 𝒲₁^{(δ)} = e₁·ℤ≥0.
- **(R4) Stability semantics**: prefix δ-stability — matched prefix has equal stage
  tuples (e_j, h_j, g_j)_{j≤k} and base degree d, every re-based residual ψ_j^{(δ)}
  irreducible of degree g_j (what letter persistence per the (a6)/(EQ-1) dictionary
  MEANS; the dictionary itself a separate owed REL.1 artifact).

**CONTEXT-NOTE MISLABEL, on record.** The swarm dispatch glossed (H4a) as
"quantitative stabilization rates (RATE-refinement material parked in the notes)".
That gloss matches NO repo artifact: the only RATE-named object is Corollary
SEM-DRAIN-RATE (Dfloor, Step 1 — VERIFIED, unconditional, not an (H4) member), and
the authoritative (R1)–(R4) are the re-based stage-tower laws above. This blueprint
follows the ROOT/§3.1/M14 statements exclusively. If a distinct "RATE refinement"
obligation exists somewhere, it is NOT (H4a) and needs its own adjudication.

**Naming collision, on record.** `LeanUrat.HC1.REL1Pack` bundles four statement defs
whose FILES are named R1–R4 (`R1_LSTStmt`/`R2_TYPStmt`/`R3_DOMStmt`/`R4_SecB1Stmt`
— the REL.1 LST/TYP/DOM/§B1 clause bundle). Those are a DIFFERENT decomposition of
REL.1 from M14's (R1)–(R4) (stage axioms / digit displays / weight recursion /
stability). Both are REL.1 slices; neither subsumes the other; no unit below may
cite "R1–R4" without the qualifier "M14's" or "HC1's".

## 1. Where the group sits (consumption map, for wave-planning)

- (H4a) → Step 16 (O-8b: the alphabet law at δ-stable classes, M14's proof ON FILE
  conditional on (R1)–(R4); pending pass P(O-8b/M14) is a NAMED §3.2 row) and
  Step 18 K3-c (clause (R): verdict rows' base-changed β-legs at q ↦ q^δ).
- (K3-δ) → Step 18 K3-c's realized pools; clause (R)'s attribution consumes it
  explicitly until a match display or re-scope lands at the O-11/O-8b interface.
- (H4b)(a)/(c) → Step 16 / clause (UB) only.
- Retirement chain for (H4a), exact: (i) the (R1)–(R4) re-scoping pass lands as a
  leaf note + hostile passes (units §M below); (ii) M14's conditional proof then
  closes O-8b (already on file — nothing to rewrite); (iii) the §3.2 row
  P(O-8b/M14) fires (fresh hostile pass on the NOW-unconditional composite);
  (iv) the §3.1 (R1)–(R4) row retires; ROOT Step 16/18 displays sync. Steps
  (iii)/(iv) are ROOT-owner moves, not this blueprint's.
- Adjacent, NOT this group: REL.2(e) β-IDENTIFICATION (the [2r]-side typing of the
  same D-c seam — (e1)–(e5), owned by the CL-8/[2r] rows); (GR-B) at orders ≥ 2
  ((H1)(a) — O-11's K3-c route note prices the order-≥ 2 residue of the DVR
  discipline there, but the ROOT keeps (R1)–(R4) its own row and THIS blueprint
  discharges the row as stated, all orders, over the §B2-DEF presentation).
  MovesRBase's BASE-INDEX CONVENTION (δ ABSOLUTE; `relExt m δ' = O (m·δ')`) binds
  every unit below (matches REL.2(e2)).

## 2. (H4a) — door: PROVE (a derivation-grade re-scoping pass; no fiat)

**Door adjudication.** LITERATURE-RETARGET is NOT available for the row itself:
standard OM/Montes theory (GMN 2012; Montes–Nart) works with full residue fields —
no published statement matches §B2-DEF's shallow-height attainable alphabets 𝔸(γ)
(M14 attempt, VERDICT block: "the closest literature … has the full-residue-field
case only"). CONSTRUCTION-CONFORMANCE alone cannot discharge it either: the Lean
tower layer is field-generic (§L.0), but the [M] row is about the NOTE corpus
(§B2-DEF's displays and their proofs), whose re-scope must be WRITTEN and passed.
Door = PROVE, with pinned literature INPUTS (Witt-vector/Teichmüller facts: Serre,
Corps Locaux II §4–6; finite-field facts: Lidl–Niederreiter Thm 3.46) and the Lean
conformance units of §L as the machine-checked skeleton.

**The one strategic decision (recommended): prove over W(F_q) for an ARBITRARY
finite field F_q, not per-δ.** State and prove (R1)–(R3) over A^{(q)} := W(F_q)[x],
F_q arbitrary finite (equivalently: an arbitrary absolutely-unramified complete DVR
with finite residue field — that class IS {W(F_q)}). Then base ℤ_p = the q = p
instance and base O_δ = the q = p^δ instance of ONE theory; the two-sided comparison
(M14 Lemma 1) consumes only the shape-determinacy of the skeleton, proved once.
Precedents on file: the GD23 generality audit (V26-confirmed: "no proof uses
completeness, perfectness, or a Teichmüller section") and O-9/M08's census over any
complete DVR — the adopted arbitrary-DVR discipline (DELTA-2 §D2.6 step 3). This
kills the "two parallel theories" duplication and makes (R4)'s matched-prefix
comparison a statement about two instances of one construction.

**Honesty on "verbatim".** The §3.1 row says "re-proved verbatim"; REL.1's own text
(MOVES ~9379, pass-1 gap 2) says MUTATIS MUTANDIS, NOT verbatim: every
residue-theoretic OBJECT (base residue field, residual polynomials, tower fields,
graded pieces, attainable images, irreducibility conditions, residue bases) is
RECONSTRUCTED over F_q, never obtained by substituting a cardinality; only the
base-independent skeleton (coefficient order, unitriangular polynomial identities,
valuation geometry, additive equal-fiber counting) carries over as written. The
LAWS' statements are verbatim; the objects are rebuilt. Every §M unit below quotes
this rule in its charge.

**Fine-grained section plan for the (R1)–(R3) pass** (unit H4-M1; §B2-DEF display
by display, base-touching steps enumerated — the REL.1 walk-order rule "the flagged
hiding spot FIRST" applied to this slice):

1. **D.0 over W(F_q)** — stage tuple σ = (w, Φ, C, U, T, F, z) with A = W(F_q)[x];
   the Gauss valuation v (v(p) = 1 — unchanged: W(F_q)/ℤ_p is unramified); the
   value-group-ℤ normalization; the scale stretch bookkeeping. Base touches: the
   base residue field is F_q (reconstructed, not |F| substituted); w₁(c) = e₁·v(c)
   on constants. Expected base-free: the D.0 conventions consume v's discreteness
   and v(p) = 1 only. FIRST CHECKPOINT (the hiding spot, mirroring REL.1 walk item
   (i)): any §B2-DEF display reading "𝔽_p-linear on base coordinates" must RETYPE
   to additive on F_q-digit blocks, walked not asserted. CONNECTIVE DISPLAY OWED
   here (Codex fold, finding 13): additivity is the retype target BY DESIGN
   (REL.1 walk item (i): additivity is all TYP(b) consumes; F_q-linearity is
   "the EXPECTED outcome, walked not available by fiat") — the full F_q-scalar
   structure of the re-based slot map is M14 Lemma 2's THEOREM, proved FROM
   (R1) (D.1(e) L₀-linearity + the Teichmüller action on graded pieces); the
   pass must display that its retyped coordinate statement composes with
   D.1(e) into exactly Lemma 2's hypotheses, so no scalar-structure gap opens
   between the walk and the on-file proof.
2. **(S1)–(S3) over W(F_q)** — valuation, K1(Φ/w) development minimum, slot
   decomposition. Proofs are valuation-geometric/ultrametric; expected base-free.
   Named risk: (S3)'s group isomorphism consumes the slot basis (S6) whose
   constructive tier reads residue representatives — reconstructed over F_q.
3. **(S4)–(S6) over W(F_q)** — (L^coeff)₀ = F; monomial digits + stride (S5);
   constructive slot basis (S6, both tiers). Base touches: F is now F_q-built
   (tower fields F_{k+1} = F_k[z]/(ψ_k) with ψ_k irreducible OVER THE RE-BASED
   F_k — irreducibility is part of the re-based stage DATA, not transported).
4. **D.1 over W(F_q)** — graded ring, initial forms, the localization L, the
   degree-1 unit T, R(f) := [f]·T^{−w(f)}; D.1(e) L₀-linearity on pieces +
   multiplicativity. Purely graded-algebra; base-free (M14 (R1) already flags
   D.1(e) as "a purely graded-algebra fact whose base-side proof is base-agnostic"
   — the pass VERIFIES this by walking it, not by citing the flag).
5. **D.3(e)(i)/(ii) over W(F_q)** — the piece maps, literal digit coordinates, the
   digit recursion (ii.2) with anchor slot j₀ ≡ t_k·γ* (mod e_k), slot heights
   γ_i, attainable index set I(γ), the alphabet product display + injectivity
   mechanism ((1, z̄, …, z̄^{g_k−1}) an F_k-basis of F_{k+1}), the off-alphabet
   guard, and the BASE CLAUSE 𝔸₁(e₁v) = F₁. NAMED CHECKPOINT (Codex fold,
   finding 4 — the drafted realizer was wrong): at base degree d > 1, constants
   of W(F_q) realize only F_q ⊊ F₁; the base clause needs the FULL first
   residual field, realized by x-dependent slot content — p^v·B with
   B ∈ C₁ = {deg_x < d} running over coefficient lifts whose base digit reading
   (the θ-basis residue vector (b̄₀, …, b̄_{d−1}) ↦ Σ b̄_m θ^m) is onto F₁;
   the pass must DISPLAY this onto-ness over W(F_q) (reduction W(F_q) → F_q
   surjective + the (S6) basis), not cite "unit lifts". No Teichmüller section
   is needed anywhere in this section (GD23 discipline preserved). This is
   (R2)'s home and the pass's core section.
6. **D.9(a) over W(F_q)** — the weight-set recursion; base 𝒲₁ = e₁·ℤ≥0 from the
   D.0 base display. This is (R3)'s home; NOTE the two base clauses are DIFFERENT
   in strength: the weight clause needs only ONE realizer per weight (p^v·(any
   unit constant) suffices), while step 5's ALPHABET clause needs onto-ness onto
   F₁ (the corrected realizer family). Purely arithmetic given (S2)/(S3).
7. **Consumption audit** — the (R1)–(R3) slice consumes §A/§B1 inputs (accepted
   over ℤ_p). Per display, LIST the consumed §A/§B1 statements and classify:
   base-free skeleton (carries as written) vs residue-theoretic (needs its own
   re-scope — if ANY lands here, the pass's perimeter widens and the unit reports
   it rather than absorbing it silently; M14's package claims the counting layer
   (Theorem C(a)/(b), PIN-WELLDEF, (ZC)) is NOT consumed — verify by the walk).
8. **The δ-instance display** — specialize q := p^δ, re-deriving M14's (R1)–(R3)
   package verbatim as instances; display the BASE-INDEX CONVENTION (δ absolute).

**Open points named now (not hidden):** (i) step 7's audit may surface §A/§B1
residue-theoretic consumptions beyond the slice — the known-unknown of this door;
(ii) the (S6) constructive tier's residue-representative bookkeeping over F_q is
expected mechanical but is the likeliest wobble point (falsifier gate N-T4, §N);
(iii) nothing in this unit discharges (R4) — see H4-M2.

**(R4) plan (unit H4-M2 — the matching dictionary, definitional layer).** (R4) is
definitional GIVEN the (a6)/(EQ-1) matching dictionary (the owed REL.1 artifact
defining "the matched position" and `posLetter δ`). H4-M2 writes the dictionary AT
THE SLICE THIS GROUP NEEDS: (i) TWO objects, kept rigorously apart (Codex fold,
finding 5 — the REL.1 rule: the O_δ classifier's OWN tower is RECONSTRUCTED over
F_q, never scalar-extended): (i-a) the re-based classifier's own tower (the
construction — REL.1's object, consumed, not defined here), and (i-b) the
same-keys COMPARISON tower (ℤ_p-tower keys viewed in O_δ[x], residuals read along
F_k ↪ F_k·F_q) — a comparison DEVICE; the dictionary's central display is WHEN
the two coincide at a matched prefix (expected: exactly at prefix-stable
positions — a lemma to prove, not a definition to decree); (ii) `posLetter δ x`
with the M14 §7.2 constraint hard-coded — prefix stability via a designated
off-domain letter — PLUS the equivalence PROVED, not assumed (Codex fold,
finding 12): the letter grammar is injective on the encoded prefix data
(`SpeciesSyntax.shape`/side data — the note's `letter_det` typing) and the
off-domain letter is outside the grammar's range, so that Lean
`Stable` ⟺ (R4) is a displayed lemma; (iii) Lemma 4's gcd(m, δ) = 1
characterization upgraded from "test-design tool" to a proved lemma of the
dictionary (inputs (F1) Lidl–Niederreiter 3.46 and (F2) compositum degrees,
pinned literature); (iv) the worked F₉ instance re-derived as the out-of-domain
example. RISK, displayed: the dictionary is ALSO consumed by (UB-X)(b)
adjudication (§3); H4-M2 is the shared gate unit of this blueprint.

## 3. (H4b) — doors per member

### 3.1 (UB-X)(a), the per-leaf O_δ re-base audit — door: PROVE (audit-grade)

The D-3 collapse (adjudicated at the GD dispatch) reduced the unramified-transfer
node to: GD families + O-9 census already stated over an arbitrary
absolutely-unramified complete DVR (GD23 V26; M08) + the O-8b alphabet slice
((H4a)) + PER-LEAF SCOPE HYGIENE for the remaining ℚ_p-stated leaves. That hygiene
audit is member (a). Unit H4-M3 writes the per-leaf table over the D-3 leaf list
(completion tree, D-3 node) + the (UB) chain's Step-16 Consumes-list:

| leaf (ℚ_p-stated) | consumed at | expected class |
|---|---|---|
| Dfloor D-1/D-2/D-4 (Haar floor, cylinders, ns-null, level-N mass p^{−nN} ↦ q_δ^{−nN}) | Step 1 → (UB) via transported chain | RE-BASE MECHANICAL (measure-theoretic; base = any compact DVR; Appendix A's resultant/Vandermonde base-free) |
| K-DICT (O-2/O-2a dictionary layers not already DVR-stated) | Steps 7/10–12 | AUDIT: split DVR-general core (GD23 perimeter) vs ℚ_p-worded remainders |
| K-RUN (O-3) | Steps 10–12 | AUDIT (same split) |
| K-HALT/ASSEMBLY (O-5/O5triple: leaf labels, Thm E separable-lift scope) | Steps 11/12, 17 (M3) | AUDIT; per-box lift uniformity D-15 re-based |
| drainage (O-4/O4T TR-OM; AGR seam = CU-2 + CU-4 + GMN Cor 4.19) | Step 13 | AUDIT; GMN Cor 4.19's stated generality checked at the pin (§4 roster), not assumed |
| CU cluster (CU-1..CU-4, CU-2t) | Steps 10–12 | AUDIT (proofs ride GD/GMN layers; re-based statements to display) |
| O-1thr (D-14/D-15 cylinder laws) | Step 18 K4-CYL | RE-BASE MECHANICAL expected (valuation-geometric) |
| O-10 sibling independence (K-COUNT/K-JAC) | Step 15 → K1 | AUDIT (factor-coordinate proofs; Jacobian p^{−ρ} ↦ q_δ^{−ρ}) |
| **LIT-4/(OM-SAT)** — audited scope "K = ℚ_p exactly" | dictionary node O-2 (Steps 11/12 via Cor 1.20/3.8) | **REAL CONTENT, named**: re-derive the OM-SAT certificate over K_δ from the pinned GMN loci at their printed generality, or re-scope; the ROOT LIT-4 entry itself names this duty as "(UB-X)(a) content" |

Charge per row: display the leaf's re-based STATEMENT; classify the proof as
(i) stated-general already, (ii) p-free symbolic (no base), (iii) mechanical
re-base (proof template carries; write the delta), (iv) real content (write the
proof or open a named lemma). NO row may be closed by "the theory transfers"
(the REL.1 rule). Honest expectation: LIT-4 is class (iv); most others (i)–(iii).
The unit's output feeds the ROOT Step-16 display ("declared but unwritten" → a
written audit with named residue).

### 3.2 (UB-X)(b) + (K3-δ) — door: PROVE, with a STATEMENT-PRECISION gate first

**Finding, displayed (the blueprint's sharpest item; scope corrected at the
Codex fold, finding 1).** Member (b) is NOT WELL-POSED as worded: "realized
ledger" and the cross-base matching of position classes have NO recorded
definition (the (a6)/(EQ-1) dictionary is an owed REL.1 artifact), so (b) can
be neither proved nor refuted as it stands. Under ONE candidate reading — the
same-keys-transport matching — there is refutation PRESSURE: M14 Lemma 4
(dictionary-conditional) makes a transported position with gcd(m, δ) > 1
unstable, and the note's worked F₉ instance is out-of-domain in exactly that
way; whether the O_δ classifier's OWN realized ledger contains such a matched
position at a given (n, p, δ) is an open realization question, NOT an
established countermodel — and composite δ alone does not force a realized m
sharing a factor with δ. N-gate N-K3 (§N) probes this empirically. So the
member is dischargeable only after a STATEMENT-PRECISION step (define the
matching + "realized"; then prove, restrict, or re-scope), choosing between:

- **Route A — the direct match display, (K3-δ)-only scope.** Prove exactly the
  fragment clause (R) consumes: K3-c's REALIZED δ > 1 pools are δ-stable position
  classes. The pools arise as family-(vi) β-legs β_{μ}(σ)(q^{D}) — continuation
  reads at accumulated residue degree D (the child's tower fields); the
  β-IDENTIFICATION seam (REL.2(e), adjacent) types each pool as a REL.1-side
  state over O_D. THE PROOF OBLIGATION, exact (corrected at the Codex fold,
  finding 2 — intrinsic irreducibility of the O_D-side residuals over their own
  fields does NOT imply cross-base letter equality): per realized pool, display
  matched-prefix letter equality against the (a6)/(EQ-1) dictionary (H4-M2) —
  i.e. a per-pool argument that the matched prefix's stage tuples and residual
  degrees persist (under the same-keys matching this is a gcd/structure
  condition on the pool's accumulated residue degrees, Lemma 4's criterion; a
  pool violating it is a REFUTER of Route A, which N-K3 hunts). Deliverable:
  (K3-δ) retires from clause (R); clause (R) returns to (H4a)-only at this
  interface (ROOT's anticipated outcome). Member (b) at FULL scope stays open.
- **Route B — the intrinsic re-scope (recommended target).** Replace the
  cross-base matching by the intrinsic per-base ledger law: for every δ and every
  position y the O_δ classifier REALIZES, a_δ(y) = δ · a_sym(letter_δ(y)), where
  a_sym is the letter's p-free symbolic exponent (the ℤ_p-side per-letter law is
  Theorem C's accepted conformance at q = p). Proof shape: (R1)–(R3) at base
  W(F_q) (H4-M1, all q at once) + M14's Theorem run against the SYMBOLIC skeleton
  (the letter's catalogue slot tree) instead of against the ℤ_p realization — the
  skeleton comparison is H4-M1's Lemma-1 leverage; NO cross-base dictionary and no
  δ-stability hypothesis remain. STATUS OF ROUTE B, exact (corrected at the Codex
  fold, finding 3): Route B does NOT discharge the rows AS STATED — the intrinsic
  law does not imply that realized positions are δ-stable, and the authoritative
  (UB-X)(b)/(K3-δ) texts quantify over stability. Route B is a REPLACEMENT
  obligation: it retires the current rows only through a ledger-level re-scope
  (per ROOT, riding the next O-11/O-8b touch) that substitutes the intrinsic law
  as the row content, with a displayed argument that the CONSUMERS (Step 16's
  alphabet-law scope; Step 18 K3-c's per-pool exponent reads) need exactly the
  intrinsic law. Until the ROOT owner lands that re-scope, nothing is discharged
  by a Route-B proof; the proof + re-scope brief travel together (H4-M5 + H4-M7).

Unit H4-M4 executes the precision step (writes both routes' exact statements,
adjudicates with the dictionary H4-M2 in hand, recommends B unless the dictionary
lands a cheap A); unit H4-M5 proves the selected route. The Lean faces (§L: H4-L7/
L8) type the CURRENT rows — Route A's shape (stability-quantified exhaustion +
restriction); they are NOT Route-B faces (finding 3: Route B's stability-free
intrinsic law is a different statement — its Lean face is fenced as H4-F5).
Provers can land L7/L8 now; a Route-B adoption re-points consumers to H4-F5.

### 3.3 (UB-X)(c), solve + aggregation commute with base change — door: PROVE

Statement to prove (unit H4-M6), AS A DISPLAYED CONDITIONAL — never by consuming
"the transported chain" wholesale (Codex fold, finding 8: Step 16's transported
chain is what clause (UB) BECOMES once this group lands; consuming it to prove
(c) would be circular): GIVEN (i) the (UB-X)(a) audit CLOSED (H4-M3, every row
class (i)–(iii) or its class-(iv) lemma proved), (ii) the selected §3.2 law on
file (H4-M5; under Route B, with its ROOT re-scope landed), and (iii) the
inherited §3.1 rows (H1)–(H3)/(H5)–(H9) at their standing conditionality — THEN
for every δ ≥ 1 and every degree-n splitting type τ over K_δ, the O_δ-side
assembled per-τ series (the block solve on the O_δ-realized species catalogue,
censuses at q₀ = p^δ, aggregated by the type map) equals R_τ(p^δ), the SAME ℚ(q)
element specialized. The unit's OWN content, exact: (1) the solve is ONE
symbolic system over ℚ(q), p-free menu/coefficients/pivots (Step 5, VERIFIED
scope); (2) the (EQ-1) species-catalogue invariance at the needed slice — an
EXPLICIT INPUT OBLIGATION of this unit, discharged by H4-M1 step 8's expanded
charge (the "no species definition consumes q" check is walked there against
the same §B2-DEF text; finding 8's second head), NOT presumed; plus the
type-catalogue display (degree-n splitting types over any local field are the
same (e, f)-multiset combinatorics — base-free) and the aggregation-map
base-independence display; (3) evaluation at q₀ = p^δ is a ring-hom on the
regular subring, defined at EVERY prime power — O-12's pole-freeness covers
q₀ = p^δ (VERIFIED leaf #2; no new work); (4) the assembly bookkeeping tying
(1)–(3) to the premises (i)/(ii). Expected difficulty: MED; no new open kernel
anticipated, but the unit REPORTS one rather than absorbing it if the
bookkeeping surfaces a consumption outside premises (i)–(iii).

## L. LEAN UNIT SPECS (compile-probed verbatim; target `lean/LeanUrat/Scaffold/HDischarge/H4/`)

### L.0 Probe record

Probe file assembled 2026-08-05 (this unit), compiled against the BUILT corpus:
`lake env lean` on a scratch file importing `Mathlib`, `LeanUrat.MovesRBase.Defs`,
`LeanUrat.Scaffold.Hypotheses`, `LeanUrat.HC1.R5_EQ2Pass` — CLEAN (zero errors,
zero sorries), and RE-PROBED CLEAN after the Codex-fold amendments
(`StageTuple.Bez` added, `H4aConsumptionFace` renamed/re-documented — findings
11/6). Units H4-L3/L4/L5/L8 are PROVED AT PROBE (full proof text below);
L1/L2/L6/L7 are defs/structures (no proof obligation). One repair during probing,
recorded for provers: `SlotTree` as a `List`-nested inductive broke `induction`
(Lean nested-inductive limitation); the `(m : ℕ) (children : Fin m → SlotTree)`
form below is the working one — do NOT "simplify" it back to a `List`.

REUSED carriers (never duplicate): `MovesRBase.SpeciesSyntax`/`AlphabetData`/
`AlphabetData.Stable`/`EQ2law`/`Fsub`/`O`/`qq`/`relExt` (base-index convention:
δ ABSOLUTE); `MovesU.DefsLedger.UpstreamTyped.cl8_eq2` (the consumed row — its
statement is NORMATIVE for the discharge shape); `LeanUrat.HC1.CarrierPackR`/
`REL1Pack`/`EQ2lawIfREL1'` (HC1's REL.1 bundle — cited for the collision note
only; NOT consumed by these units); `Scaffold.RootHyps.h4a_r1r4`/`h4b_*` (bare
`Prop` fields; refinement is BP_VI-owned, §L.9).

### L.1 File `Defs.lean` — units H4-L1, H4-L2, H4-L7

```lean
namespace LeanUrat.Scaffold.HDischarge.H4

open MovesRBase

/-- One OM read's numerical stage tuple `(e, h, g)` with Bézout companion `t`
(`h·t ≡ 1 mod e`). Shape data only — no residue field. -/
structure StageTuple where
  e : ℕ+
  h : ℤ
  t : ℤ
  g : ℕ+
deriving DecidableEq

/-- The Bézout invariant `h·t ≡ 1 (mod e)` — legality predicate for stage
tuples (finding 11 of the blueprint's Codex review: `anchorSlot` is intended
ONLY at legal tuples; instances must supply `Bez` alongside the raw data). -/
def StageTuple.Bez (s : StageTuple) : Prop :=
  (s.h * s.t) % (s.e : ℤ) = 1 % (s.e : ℤ)

/-- D.9(a) weight sets as a FUNCTION of the shape history (top stage first):
`𝒲₁ = e₁·ℤ≥0`; `𝒲_{k+1} = e_{k+1}·⋃_{0≤j<e_k g_k} (𝒲_k + j·h_k)`.
M14 Lemma 1(a) is thereby definitional; the per-base content is the
CONFORMANCE row (R3) of `LedgerSkel`. -/
def wSet : List StageTuple → Set ℤ
  | [] => ∅
  | [s] => Set.range fun v : ℕ => (s.e : ℤ) * v
  | s :: sk :: prior =>
      (fun w => (s.e : ℤ) * w) ''
        (⋃ j ∈ Finset.range ((sk.e : ℕ) * (sk.g : ℕ)),
          (· + (j : ℤ) * sk.h) '' wSet (sk :: prior))

/-- Anchor slot `j₀ ≡ t_k·γ* (mod e_k)` (D.3(e)(ii) skeleton). -/
def anchorSlot (sk : StageTuple) (γs : ℤ) : ℤ := (sk.t * γs) % (sk.e : ℤ)

/-- Slot heights `γ_i = γ* − (j₀ + i·e_k)·h_k`. -/
def slotHeight (sk : StageTuple) (γs : ℤ) (i : ℕ) : ℤ :=
  γs - (anchorSlot sk γs + (i : ℤ) * (sk.e : ℤ)) * sk.h

/-- Attainable index set `I(γ) = {i < g_k : γ_i ∈ 𝒲_k}`. -/
def attainIdx (sk : StageTuple) (W : Set ℤ) (γs : ℤ) : Set ℕ :=
  {i : ℕ | i < (sk.g : ℕ) ∧ slotHeight sk γs i ∈ W}

/-- The finite slot tree below one ledger position: leaves = base-stage reads,
nodes = the `I(γ)`-indexed slot recursion (D.3(e)(ii)); `m` = the attainable
index count `|I(γ)|` at the node. -/
inductive SlotTree where
  | base : SlotTree
  | node (m : ℕ) (children : Fin m → SlotTree)

/-- Alphabet `F_p`-dimension along a slot tree with base-leaf dimension `dbase`
(the product display `|𝔸(γ)| = Π_{i∈I(γ)} |𝔸_k(γ_i)|` read at exponents:
`a(k+1, γ) = Σ_{i∈I(γ)} a(k, γ_i)`). -/
def SlotTree.dimOf (dbase : ℕ) : SlotTree → ℕ
  | .base => dbase
  | .node m cs => ∑ i : Fin m, (cs i).dimOf dbase

variable (p : ℕ) [Fact p.Prime]

/-- **H4-L2 (`LedgerSkel`)** — the DIMENSION-LEVEL conformance carrier: the
typed face of the NUMERICAL slice of what M14's Theorem consumes from
(R1)–(R4) — and ONLY that slice (Codex review finding 7: the stage axioms,
digit maps, alphabet-product bijection, weight-set conformance, and (R4)
irreducibility data are NOT typed here; they are exactly the content the
eventual instance's rows must be PROVED from, at the H4-F6 carriers).
`tree δ x` = the realized height-lattice skeleton of position `x` over `O_δ`;
`dbase δ x` = the realized base dimension `[F₁^{(δ)} : F_p]`. Rows: the (R2)
product display read at dimensions (`dim_conf`), Lemma 1 + (R3) + (R4)
read at skeletons (`tree_stable`), Lemma 3's base scaling (`dbase_stable`) —
CONFORMANCE ROWS to be supplied by the instance, never proved abstractly. -/
structure LedgerSkel (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) where
  tree : ℕ+ → AD.Pos → SlotTree
  dbase : ℕ+ → AD.Pos → ℕ
  dim_conf : ∀ (δ : ℕ+) (x : AD.Pos),
    AD.aDim δ x = (tree δ x).dimOf (dbase δ x)
  tree_stable : ∀ (δ : ℕ+) (x : AD.Pos),
    AlphabetData.Stable p AD δ x → tree δ x = tree 1 x
  dbase_stable : ∀ (δ : ℕ+) (x : AD.Pos),
    AlphabetData.Stable p AD δ x → dbase δ x = (δ : ℕ) * dbase 1 x

/-- **H4-L7 (`RealizedLedger`)** — the realized-ledger carrier: `realized δ` is
the set of position classes the re-based classifier realizes over `O_δ`;
`Pool` indexes Step-18 K3-c's realized δ > 1 pools (the base-changed β-legs),
each riding a realized position (`pool_realized`) at pool index > 1. -/
structure RealizedLedger {Sp : SpeciesSyntax} (AD : AlphabetData p Sp) where
  realized : ℕ+ → Set AD.Pos
  Pool : Type
  poolIdx : Pool → ℕ+
  poolPos : Pool → AD.Pos
  pool_gt_one : ∀ P : Pool, 1 < (poolIdx P : ℕ)
  pool_realized : ∀ P : Pool, poolPos P ∈ realized (poolIdx P)

end LeanUrat.Scaffold.HDischarge.H4
```

FAITHFULNESS NOTES (binding on provers): (i) `LedgerSkel.tree_stable` bundles
M14 Lemma 1 + (R3) + (R4) INTO the carrier — a CONFORMANCE ROW to be supplied
by the eventual instance, never proved abstractly; the abstract layer proves
only what follows FROM it (H4-L4/L5). The instance bears the mathematical
content (Codex review finding 7, accepted): the four laws' FULL typed carriers
(stage axioms, digit maps, product bijection, weight-set conformance tying
`tree` to `wSet`/`attainIdx`, (R4) data) are fenced unit H4-F6, designed AFTER
H4-M1's note lands (Lean types follow the proven note, per corpus discipline);
until then H4-L2's rows are honest named assumptions, not discharge.
(ii) `dim_conf`'s `dbase δ x` at δ = 1 must read `[F₁ : F_p] = d` (M14 Lemma
3); instances violating M14 §7.2 (prefix-stability encoding in `posLetter`)
are NOT covered — quote the §7.2 constraint in the instance file's header.
(iii) `RealizedLedger` types the INTERFACE SHAPE only (positions, indices,
membership) — no β-leg, residue-degree, or clause-(R) semantics (finding 14,
accepted): the value-side fields land at fenced H4-F2, and `k3delta_of_ubxb`
is exactly the elementary restriction law ROOT's `stable_implies_k3delta`
displays — faithful at that altitude, claiming nothing more. L7/L8 type the
CURRENT (Route-A-shaped) rows; Route B's face is fenced H4-F5 (finding 3).

### L.2 File `Kernel.lean` — units H4-L3, H4-L4, H4-L5, H4-L8 (PROVED AT PROBE)

```lean
/-- **H4-L3.** Dimension scaling along a fixed slot tree: `dimOf (δ·d) = δ · dimOf d`.
The arithmetic core of M14's Theorem (ii) — the factor δ propagates through
every stage of the product display. -/
theorem SlotTree.dimOf_scale (δ d : ℕ) :
    ∀ t : SlotTree, t.dimOf (δ * d) = δ * t.dimOf d := by
  intro t
  induction t with
  | base => rfl
  | node m cs ih =>
      simp only [SlotTree.dimOf, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => ih i

/-- **H4-L4** — (EQ-2)(ii) from the conformance carrier. -/
theorem eq2_dim_of_skel {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (L : LedgerSkel p Sp AD) :
    ∀ (δ : ℕ+) (x : AD.Pos), AlphabetData.Stable p AD δ x →
      AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x := by
  intro δ x hst
  rw [L.dim_conf δ x, L.tree_stable δ x hst, L.dbase_stable δ x hst,
    SlotTree.dimOf_scale, L.dim_conf 1 x]

/-- **H4-L5** — `EQ2law` from the conformance carrier plus the conjunct-(i)
linearity row (M14 Lemma 2's conclusion, typed as a hypothesis until the
graded-piece module carrier lands). This is the typed discharge route for
`UpstreamTyped.cl8_eq2`. -/
theorem eq2law_of_skel {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (L : LedgerSkel p Sp AD)
    (hlin : ∀ (δ : ℕ+) (x : AD.Pos), AlphabetData.Stable p AD δ x →
      IsLinearMap ↥(Fsub p δ) (AD.slotMap δ x)) :
    EQ2law p AD :=
  fun δ x hst => ⟨hlin δ x hst, eq2_dim_of_skel p L δ x hst⟩

/-- (UB-X)(b) typed: δ-stable position classes exhaust the realized ledger at
every δ. -/
def UBXbStmt {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ → AlphabetData.Stable p AD δ x

/-- (K3-δ) typed: (UB-X)(b) RESTRICTED to K3-c's realized δ > 1 pools. -/
def K3deltaStmt {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) : Prop :=
  ∀ P : RL.Pool, AlphabetData.Stable p AD (RL.poolIdx P) (RL.poolPos P)

/-- **H4-L8** — the fragment law at the typed faces (ROOT's
`stable_implies_k3delta`, carrier form): full (UB-X)(b) implies (K3-δ). -/
theorem k3delta_of_ubxb {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) (h : UBXbStmt p RL) : K3deltaStmt p RL :=
  fun P => h (RL.poolIdx P) (RL.poolPos P) (RL.pool_realized P)
```

(Namespace/variable context as in L.1; the probe compiled L.1 + L.2 as one file —
splitting into `Defs.lean`/`Kernel.lean` needs only the import line
`import LeanUrat.Scaffold.HDischarge.H4.Defs` and re-opening
`namespace LeanUrat.Scaffold.HDischarge.H4` + `variable (p : ℕ) [Fact p.Prime]`.)

### L.3 File `TypedFaces.lean` — unit H4-L6

```lean
/-- The typed face of (H4a)'s CONSUMPTION SHAPE (what Steps 16/18 read:
the per-prime (EQ-2) law at carried `AlphabetData`, verbatim the
`UpstreamTyped.cl8_eq2` row) — NOT a refinement candidate for
`RootHyps.h4a_r1r4`: (H4a) is the four stage-tower laws, and EQ-2 is their
downstream consequence (Codex review finding 6); refining the field to this
face would silently weaken the row. -/
def H4aConsumptionFace (KCAD : ∀ (p : ℕ) [Fact p.Prime],
    (Sp : SpeciesSyntax) × AlphabetData p Sp) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], EQ2law p (KCAD p).2
```

STANDING WARNING (finding 6, accepted): `RootHyps.h4a_r1r4`'s refinement target
is the FOUR-LAW package (H4-F6's carriers, post-H4-M1), never this consumption
face — a face-level refinement would replace the hypothesis being discharged.

### L.4 File `AxChk.lean` — unit H4-L9 (MECH)

`#print axioms` lines for every L-unit declaration above (explicit finite list, no
wildcard), per the AxChk_baseline discipline. Expected footprint: Lean-core only.

### L.5 Fenced FUTURE units (assigned to NO wave; do not attempt)

- **H4-F1**: the `LedgerSkel` INSTANCE from the engine (HC1 `Tower p F` at
  `F := Fsub p δ` — the corpus tower layer is already field-generic, so the
  instance is a conformance construction, not new theory). Gated on H4-M1/M2
  landing (the instance's `tree_stable` row IS (R3)+(R4)).
- **H4-F2**: the `RealizedLedger` instance at the value side (K3-c's pools from
  the pack's family-(vi) legs) — gated on §3.2's route adjudication (H4-M4) and
  on BP_IV/BP_V value-side carriers.
- **H4-F3**: `RootHyps.h4a_r1r4`/`h4b_*` FIELD REFINEMENT to the typed faces —
  BP_VI-owned (sync duty, `Scaffold/Hypotheses.lean` header); this blueprint only
  SUPPLIES the faces (H4-L6, `UBXbStmt`, `K3deltaStmt`).
- **H4-F4**: Lemma 2's graded-piece module carrier (the Teichmüller action on
  `gr_γ`; M14 §7.1's trap — the raw level set is NOT a module) discharging
  H4-L5's `hlin` row. Gated on H4-M1 (R1) landing.
- **H4-F5** [added at the Codex fold, finding 3]: the Route-B Lean face — the
  stability-free intrinsic exponent law (`∀ δ, ∀ x ∈ realized δ,
  aDim δ x = δ * aSym (letter δ x)` over a symbolic-exponent carrier). Gated on
  H4-M4 selecting Route B AND the ROOT re-scope landing; consumers re-point
  from `UBXbStmt`/`K3deltaStmt` only then.
- **H4-F6** [added at the Codex fold, findings 6/7]: the FULL four-law typed
  carriers — stage-axiom pack ((S1)–(S6)/D.0/D.1(e) over `O p δ`), digit/
  alphabet-display pack (D.3(e)(ii): recursion + product bijection + base
  clause), weight-set conformance (`tree`/`wSet`/`attainIdx` tied), (R4) data —
  the honest refinement target for `RootHyps.h4a_r1r4`. Designed AFTER H4-M1's
  note passes (types follow the proven note); consumes MovesRBase `O`/`Fsub`
  and coordinates with HC1's `CarrierPackR` (collision note, §0) without
  duplicating it.

## M. MATH-NOTE UNIT SPECS (the actual [M] discharge; owners = prover Fables + Codex twins)

| id | deliverable (target file) | charge | consumes | difficulty | gate |
|---|---|---|---|---|---|
| **H4-M1** | `lean/notes/openmath/H4M1_rpack_attempt.md` — the (R1)–(R3) re-scoping pass over W(F_q), §2's eight sections | derivation-grade walk of §B2-DEF displays D.0/(S1)–(S6)/D.1/D.3(e)/D.9(a) over arbitrary finite residue field; consumption audit (§2 step 7); δ-instance display (step 8) — step 8 EXPANDED at the Codex fold (finding 8): it ALSO executes the (EQ-1) slice check ("no species definition consumes q", walked against the same §B2-DEF text) that H4-M6 consumes; the mutatis-mutandis rule quoted and obeyed; the step-5 base-clause onto-ness checkpoint (finding 4) and the step-1 Lemma-2 connective display (finding 13) are named duties of the charge | §B2-DEF (ACCEPTED); REL.1 walk-order rule; Serre Corps Locaux II §4–6 (pinned); GD23 V26 precedent | **HARD** (the group's core; "expected mechanical" is the tree's grade, not a waiver) | hostile pass ×2 (fresh contexts, one Codex); N-T4 run BEFORE pass 1 |
| **H4-M2** | `lean/notes/openmath/H4M2_dict_attempt.md` — the (a6)/(EQ-1) matching dictionary at this group's slice + (R4) + Lemma 4 proved | §2's (R4) plan items (i)–(iv); M14 §7.2/§8.2 constraints hard-coded | M14 Lemma 4; Lidl–Niederreiter 3.46 (pinned); (EQ-1) text | MED | hostile pass ×1 + N-K3's gcd table |
| **H4-M3** | `lean/notes/openmath/H4M3_leafaudit.md` — the (UB-X)(a) per-leaf table executed | §3.1's table, all nine rows classified (i)–(iv), re-based statements displayed; rows found mid-audit ADDED, never absorbed. COMPLETION CRITERION (Codex fold, finding 9): (a) counts DISCHARGED only when every row is class (i)–(iii) CLOSED or its class-(iv) lemma is PROVED; an open named lemma (LIT-4 the expected case) leaves (a) OPEN with that lemma as its displayed residue, and H4-M6/M7 stay BLOCKED on it | D-3 node; Step-16 Consumes-list; LITUNIT pins | MED (audit) + the LIT-4 row possibly HARD | hostile pass ×1; no numerics |
| **H4-M4** | `lean/notes/openmath/H4M4_k3delta_adjudication.md` — §3.2's precision step | both routes' exact statements; the split-countermodel pressure on naive (b) displayed; recommendation + ROOT-sync note (a Route-B adoption is a ledger statement change — ROOT owner's touch, per the standing rule) | H4-M2 (the dictionary); O-11 §3.4 (K3-c); REL.2(e) adjacency | MED | Codex adversarial read of the adjudication |
| **H4-M5** | `lean/notes/openmath/H4M5_k3delta_attempt.md` — the selected route PROVED | Route A: the match display at K3-c's pools; Route B: the intrinsic per-letter law over W(F_q) (M14 Theorem vs the symbolic skeleton) | H4-M1 + H4-M4 (+ H4-M2 on Route A) | MED–HARD (route-dependent) | hostile pass ×2; N-K3 sealed predictions |
| **H4-M6** | `lean/notes/openmath/H4M6_commute_attempt.md` — (UB-X)(c) proved AS THE §3.3 DISPLAYED CONDITIONAL | §3.3's plan (1)–(4) at the corrected conditional form (finding 8): premises (i) M3 CLOSED, (ii) M5's law (with ROOT re-scope if Route B), (iii) inherited rows — never "the transported chain" wholesale; the (EQ-1) input consumed FROM H4-M1 step 8's expanded walk, displayed | H4-M1 step 8 ((EQ-1) slice); H4-M3 CLOSED; H4-M5; O-12 pole-freeness (VERIFIED); Step 5's p-free solve | MED | hostile pass ×1 |
| **H4-M7** | ROOT-sync brief (for the ROOT owner, NOT a self-serve edit): retirement chain §1 executed — (H4a) row retire + P(O-8b/M14) firing + (K3-δ) attribution return | after M1+M2 land AND their passes; separately after M4/M5 | the landed units | MECH | ROOT owner executes; this unit only drafts the delta |

## W. WAVE PLAN

[Wave order corrected at the Codex fold, finding 10.]

- **Wave 0 (Lean statement layer; 1 prover):** H4-L1+L2+L7 (`Defs.lean`) → H4-L3/
  L4/L5/L8 (`Kernel.lean`; proofs supplied above — transcription + green build) →
  H4-L6, H4-L9. All MECH/EASY; single sequential unit is fine (shared files).
- **Wave 1 (math, parallel):** H4-M1 (the core; 1 Fable + Codex twin), H4-M2,
  H4-M3 — mutually independent. N-T4 runs before M1's pass 1.
- **Wave 2 (after M2):** H4-M4 (adjudication; needs the dictionary in hand);
  N-K3 sealed and run here (its verdict feeds M4's route call).
- **Wave 3 (after M1 + M4; + M2 on Route A):** H4-M5 alone.
- **Wave 4 (after M3 CLOSED + M5; if Route B, ALSO after the ROOT re-scope
  lands — the authorization precedes any discharge claim):** H4-M6.
- **Wave 5:** H4-M7 (ROOT-sync drafts: the (H4a) retirement chain; the §3.2
  P(O-8b/M14) firing brief; the Route-B re-scope brief if selected — drafted
  for the ROOT owner, never self-served); H4-F1/F4/F6 unfence next.
- Cross-group: nothing here blocks on H1–H3/H5–H9; H4-M5 Route A touches the
  REL.2(e) seam (CL-8/[2r] owner) — coordinate, don't absorb.

## N. NUMERICS / FALSIFIER GATES

- **N-N8 (done, standing):** `verification/openmath/N8-eq2-alphabet_eq2_carry_alphabet.py`
  — 199,723 alphabets, 17 fields, 0 violations (the row's existing exhaustive flag).
- **N-T4 (NEW; run before H4-M1 pass 1):** M14's Test 4, still unrun — two-stage
  tower p = 2, (e₁,h₁) = (2,1), ψ₁ = z²+z+1, stage-2 (e₂,h₂) = (2,3), ψ₂ irreducible
  cubic over F₄, δ = 5: symbolic alphabet recursion both sides, all heights γ ≤ 100;
  REFUTES (R2)/(R3) drafting if any a^{(δ)}(γ) ≠ 5·a(γ) — the first gate that
  exercises a NESTED proper sub-alphabet (the executed T1 mini-run had d = 1, full
  per-slot fields; M14's own caveat).
- **N-K3 (RUN 2026-08-08 — ALL GREEN; seals H4-M4/M5):** enumerate the n = 3
  pack's verdict-row β-legs' δ > 1 pools; per pool, check the realized species
  against Lemma 4's gcd criterion and against Route B's intrinsic exponent law
  (a_δ = δ·a_sym at the realized letter). Predictions sealed pre-run per the
  standing falsifier discipline. A violation of the INTRINSIC law refutes Route B
  (and (EQ-2) itself — escalate); a gcd-criterion violation at a realized pool
  kills Route A's cheap match. **EXECUTED:** `verification/openmath/nk3_check.py`
  (+ output/JSON; M5 §6's P1–P4 tested as-sealed; PARI oracle) — 376/376 checks,
  0 violations: exhaustive pool roster at p ∈ {2,3} (531,441 + 32,768 boxes,
  pattern counts exact; pools (s1-f2/2) 177,147·8,192, (s1-f3/3) 157,464·8,192,
  (deep-g2/2) 13,608·1,472, (deep-g3/3) 648·256); intrinsic law EXACT at every
  probed pool incl. per-branch at split pools (the F₉-shape contrast a_branch =
  2 ≠ δ·a₁ = 4 MEASURED — T3's re-based run executed); M2 gcd table verified
  exhaustively; NO intrinsic violation (branch (iii) does not fire); NO Route-A
  refuter under the β-leg-born reading (structurally absent at n = 3, verified —
  first possible at n ≥ 4); free-re-base non-coprime rows split per L–N
  (pressure displayed, carrier-conditional, no branch fired). Full record: M5
  note §8.
- **N-REL-n4 (outlined in the M14 brief, still unspecced):** p = 2, n = 4, δ = 2
  conditioning on an irreducible quadratic root read — spec sheet rides H4-M1.

## X. Codex verification record (run + fold, 2026-08-05)

One adversarial Codex review ran per the directive (budget at launch: 2% of the
7-day window). Full verbatim report: `lean/notes/openmath/H4_bp_review.md`.
Verdict as returned: **BLUEPRINT-REVISE — 10 CRITICAL, 4 GAP**. Every finding
dispositioned below and FOLDED IN PLACE in this same revision; the two Lean-spec
amendments were RE-COMPILE-PROBED clean (§L.0). The blueprint's architecture
(doors, unit set, §3.2 precision-gate) SURVIVED; the fold repaired statements,
charges, and ordering.

| # | class | finding (compressed) | disposition |
|---|---|---|---|
| 1 | CRIT | the (UB-X)(b) "countermodel" not established (dictionary-conditional; composite δ does not force gcd > 1 at a REALIZED m; F₉ instance ≠ realization argument) | **ACCEPTED — FIXED** §3.2 opening rewritten: (b) is NOT WELL-POSED as worded; refutation PRESSURE under one candidate reading, no countermodel claimed; N-K3 probes empirically. Reinforces the precision-gate structure |
| 2 | CRIT | Route A conflated intrinsic irreducibility with cross-base stability ("stability by construction") | **ACCEPTED — FIXED** Route A's mechanism replaced by the exact per-pool proof obligation (matched-prefix letter equality against the dictionary; Lemma-4 gcd/structure condition; N-K3 as refuter) |
| 3 | CRIT | Route B does not discharge the STATED rows; L7/L8 "route-neutral" claim false (they assert `Stable`) | **ACCEPTED — FIXED** Route B re-labeled a REPLACEMENT obligation gated on the ROOT re-scope; L7/L8 re-documented as CURRENT-row (Route-A-shaped) faces; Route-B face fenced as new H4-F5 |
| 4 | CRIT | base-alphabet realizer wrong: Teichmüller units realize only F_q ⊊ F₁ at d > 1 | **ACCEPTED — FIXED** §2 step 5 rewritten: x-dependent slot realizers with the θ-basis digit reading onto F₁, onto-ness a DISPLAYED duty of H4-M1; step 6 now separates the (weaker) weight-clause realizer need |
| 5 | CRIT | the (R4) dictionary draft blurred same-keys transport (comparison) with the reconstructed O_δ tower (REL.1 rule) | **ACCEPTED — FIXED** H4-M2 charge item (i) split into (i-a) construction vs (i-b) comparison device, with the coincidence-at-stable-prefixes display named as a LEMMA of the dictionary |
| 6 | CRIT | `H4aTypedFace` is not an (H4a) refinement (EQ2law is downstream of the four laws; refining the field would weaken the row) | **ACCEPTED — FIXED** renamed `H4aConsumptionFace`, re-documented as the consumption shape only; standing warning added; the honest refinement target = H4-F6's four-law carriers; re-probed clean |
| 7 | CRIT | `LedgerSkel` docstring overclaimed ("the typed face of what M14's Theorem consumes"); rows smuggle the numerical conclusions; `tree` unconnected to `wSet`/`attainIdx` | **ACCEPTED — FIXED** docstring rewritten to DIMENSION-LEVEL slice with the untyped content enumerated; faithfulness note (i) expanded; full carriers fenced as H4-F6 (typed after H4-M1's note, per corpus discipline). The reduction theorems L4/L5 stand as honest conditionals |
| 8 | CRIT | (c)'s proof consumed "the transported chain" (unavailable/circular) and an unsupplied (EQ-1) | **ACCEPTED — FIXED** §3.3 restated as a DISPLAYED CONDITIONAL with premises (i)–(iii); (EQ-1) made an explicit input obligation discharged by H4-M1 step 8's EXPANDED charge; M6's consumes-line synced |
| 9 | CRIT | H4-M3 could leave (a) undischarged (open named lemma) while M6/M7 consume it | **ACCEPTED — FIXED** M3 completion criterion added (CLOSED = every row (i)–(iii) or class-(iv) lemma PROVED; else (a) stays OPEN and M6/M7 BLOCKED) |
| 10 | CRIT | wave plan violated its own dependencies (M6 ∥ M5 while consuming M5's law; M3 not gated; Route-B authorization ordering) | **ACCEPTED — FIXED** waves restructured: W3 = M5 alone; W4 = M6 after M3-CLOSED + M5 (+ ROOT re-scope if Route B); W5 = M7 |
| 11 | GAP | `StageTuple` lacks the Bézout invariant `anchorSlot` presumes | **ACCEPTED — FIXED** `StageTuple.Bez` legality predicate added to L.1 (compile-probed); instances must supply it |
| 12 | GAP | `posLetter` hard-coding ≠ a proof of `Stable` ⟺ (R4) (injectivity/collisions unaddressed) | **ACCEPTED — FIXED** H4-M2 item (ii) now requires the equivalence PROVED (grammar injectivity on encoded prefix data + off-domain letter outside the range), displayed as a lemma |
| 13 | GAP | additivity retype weakens the needed F_q-scalar structure | **PARTIAL REBUT + FIXED** the additivity target is REL.1's own walk design (item (i): additivity is all TYP(b) consumes; linearity "walked not available by fiat"), and full F_q-linearity is M14 Lemma 2's THEOREM from (R1) — not an (R1) clause; the missing piece was the CONNECTIVE display, now a named duty at §2 step 1 (retyped coordinates ∘ D.1(e) = Lemma 2's hypotheses) |
| 14 | GAP | `RealizedLedger` types no K3-c semantics; `k3delta_of_ubxb` is elementary restriction | **ACCEPTED — FIXED** faithfulness note (iii) rewritten: interface shape only, value-side fields at fenced H4-F2; the elementary restriction law is exactly ROOT's displayed `stable_implies_k3delta` — faithful at that altitude, nothing more claimed |

Residual after fold: none unaddressed. The review's verdict stands as issued
against the PRE-FOLD text; this §X + the in-place repairs are the fold. Next
verification touch: the per-unit hostile passes named in §M (the real gates —
nothing in this blueprint is discharged by the blueprint itself).


