/-
# H4-M6 — (UB-X)(c) PROVED AS §3.3's DISPLAYED CONDITIONAL: solve + type aggregation commute with unramified base change (Fable prover H4-M6, HDISCHARGE_H4 division, Wave 4)

Unit H4-M6 of `lean/blueprints/HDISCHARGE_H4.md` (§M table row 6 + §3.3). This
file is a LITERATE LEAN MARKDOWN NOTE (the H4-M2/M4/M5 format): prose in
comment blocks, every Lean declaration compiles. Gate command (from `lean/`):
`lake env lean notes/openmath/H4M6_commute_attempt.md` — green, zero sorry.
The unit's OTHER gate: hostile pass ×1 (ledger at §8).

CHARGE (blueprint §M row, verbatim): "`lean/notes/openmath/
H4M6_commute_attempt.md` — (UB-X)(c) proved AS THE §3.3 DISPLAYED CONDITIONAL
| §3.3's plan (1)–(4) at the corrected conditional form (finding 8): premises
(i) M3 CLOSED, (ii) M5's law (with ROOT re-scope if Route B), (iii) inherited
rows — never "the transported chain" wholesale; the (EQ-1) input consumed FROM
H4-M1 step 8's expanded walk, displayed | H4-M1 step 8 ((EQ-1) slice); H4-M3
CLOSED; H4-M5; O-12 pole-freeness (VERIFIED); Step 5's p-free solve | MED |
hostile pass ×1."

STATEMENT-FENCE RECORD: the blueprint has NO §L Lean spec for H4-M6 (it is a
§M math-note unit); the charge text is transcribed verbatim above and the
blueprint §3.3 statement is transcribed verbatim in §1.1 below. Following the
H4-M5 precedent (its pass-1 finding 5, accepted there): this note lands NO
law-shaped Lean declaration — the H4 Lean faces are fenced (H4-F1/F2/F5/F6,
blueprint §L.5) and the Route-B face's second gate (the ROOT re-scope) has not
fired. The namespace `LeanUrat.Scaffold.HDischarge.H4.UBXc` holds six
GENERIC algebra/arithmetic seeds (§4.L/§5.L below) — the bridging identity
p^(δ·a) = (p^δ)^a, the ring-hom solve-transport and unit-pivot-uniqueness
displays, and three instantiations/extractions of the EXISTING O-12 Lean
face (`LeanUrat/MovesU/O12PoleFree.lean`, consumed by IMPORT, verbatim) at
the evaluation point q₀ = p^δ. None of them mentions a corpus carrier of
the H4 group; none is a face of (UB-X)(c).

## §0. VERDICT SUMMARY + PREMISE-STATUS LEDGER (read this first)

1. **(UB-X)(c) is PROVED AS THE §3.3 DISPLAYED CONDITIONAL** (§5 Theorem):
   GIVEN premises (i)/(ii)/(iii) of §1.1 — carried here as the named rows
   [P-AUDIT], [P-LAW], [P-INHERIT] of §1.3 — for every δ ≥ 1 and every
   degree-n splitting type τ over K_δ, the O_δ-side assembled per-τ series
   (the block solve on the O_δ-realized species catalogue, censuses at
   q₀ = p^δ, aggregated by the type map) equals R_τ(p^δ), the SAME ℚ(q)
   element specialized. The proof is exactly §3.3's plan (1)–(4): the one
   p-free symbolic solve (§2), the (EQ-1) slice + the type-catalogue and
   aggregation-map displays (§3), the q₀ = p^δ evaluation ring-hom (§4), and
   the assembly bookkeeping (§5).
2. **NOTHING IS DISCHARGED BY THIS NOTE.** The premises' ON-FILE status at
   composition, displayed per the honesty invariant:
   - **Premise (i) is UNSATISFIED on file.** H4-M3's own verdict
     (`H4M3_leafaudit.md` §0): "(UB-X)(a) stays OPEN, with Lemma RRE-δ as its
     displayed residue, and H4-M6/H4-M7 stay BLOCKED on it" — row 10 (the
     O-14a′ run-realizer supply at ambient F = F_{p^δ}) is class (iv) with
     its lemma OPEN. Per the blueprint's completion criterion (Codex fold,
     finding 9), (a) does NOT count discharged.
   - **Premise (ii) is PARTIALLY on file.** H4-M4 selected ROUTE B; H4-M5
     proved the intrinsic law (RB) — a_δ(y) = δ·a_sym(letter_δ(y)) — AS A
     DISPLAYED CONDITIONAL on its own rows [RUN-PROD]/[LEDGER-READ]/
     [LET-DATA]/[SYM-ID]/[M1-STATUS]. The Route-B ROOT re-scope has NOT
     landed (no H4-M7 artifact on file; H4-F5's second gate unfired, per
     H4-M5's own statement-fence record). Premise (ii) as §3.3 words it
     ("with its ROOT re-scope landed") therefore also stands as HYPOTHESIS.
   - **Premise (iii)** is the standing conditionality of the corpus
     ((H1)–(H3)/(H5)–(H9)), hypothesized as such — it is never "satisfied",
     it is priced.
   Consequently this note's deliverable is the CONDITIONAL, ready to fire
   when the Wave-4 gates land (M3's RRE-δ lemma proved; the ROOT re-scope
   landed). Any reader claiming "(UB-X)(c) discharged" from this note is
   misreading it.
3. **The circularity fence held (finding 8).** The transported chain — what
   Step 16's clause (UB) becomes once the H4 group lands, i.e. the
   Steps-17/18/18b evaluation chain riding q ↦ q^δ — is consumed NOWHERE
   below. §6's consumption audit enumerates every input; clause (UB), Step 16's
   package, Step 18's series-tie (O-11), and Step 18b appear on no line. In
   particular the conclusion's LHS is the SOLVE OUTPUT on the O_δ-realized
   catalogue (§3.3's own parenthesis), never "the tree series" — so Step 18
   is not needed even as a definition supplier.
4. **One consumption surfaced OUTSIDE premises (i)/(ii), reported per the
   charge's closing sentence, adjudicated INSIDE premise (iii):** the
   arbitrary-DVR census layer (Step 14 / GD23's V26-confirmed generality,
   consumed at §5 walk A2) carries (FRESH)/(ADM) conditionality at orders
   ≥ 2. That is exactly an "inherited §3.1 row at standing conditionality"
   — premise (iii)'s (H2)=(FRESH) and (H3)⊇(ADM) — so it is WITHIN the
   displayed premise bundle; no new open kernel is opened. Displayed at A2
   and audited at §6.

## §1. THE STATEMENT

### 1.1 Blueprint §3.3, verbatim (the statement this unit proves)

> Statement to prove (unit H4-M6), AS A DISPLAYED CONDITIONAL — never by
> consuming "the transported chain" wholesale (Codex fold, finding 8: Step
> 16's transported chain is what clause (UB) BECOMES once this group lands;
> consuming it to prove (c) would be circular): GIVEN (i) the (UB-X)(a)
> audit CLOSED (H4-M3, every row class (i)–(iii) or its class-(iv) lemma
> proved), (ii) the selected §3.2 law on file (H4-M5; under Route B, with
> its ROOT re-scope landed), and (iii) the inherited §3.1 rows
> (H1)–(H3)/(H5)–(H9) at their standing conditionality — THEN for every
> δ ≥ 1 and every degree-n splitting type τ over K_δ, the O_δ-side
> assembled per-τ series (the block solve on the O_δ-realized species
> catalogue, censuses at q₀ = p^δ, aggregated by the type map) equals
> R_τ(p^δ), the SAME ℚ(q) element specialized. The unit's OWN content,
> exact: (1) the solve is ONE symbolic system over ℚ(q), p-free
> menu/coefficients/pivots (Step 5, VERIFIED scope); (2) the (EQ-1)
> species-catalogue invariance at the needed slice — an EXPLICIT INPUT
> OBLIGATION of this unit, discharged by H4-M1 step 8's expanded charge
> (the "no species definition consumes q" check is walked there against
> the same §B2-DEF text; finding 8's second head), NOT presumed; plus the
> type-catalogue display (degree-n splitting types over any local field
> are the same (e, f)-multiset combinatorics — base-free) and the
> aggregation-map base-independence display; (3) evaluation at q₀ = p^δ is
> a ring-hom on the regular subring, defined at EVERY prime power — O-12's
> pole-freeness covers q₀ = p^δ (VERIFIED leaf #2; no new work); (4) the
> assembly bookkeeping tying (1)–(3) to the premises (i)/(ii). Expected
> difficulty: MED; no new open kernel anticipated, but the unit REPORTS
> one rather than absorbing it if the bookkeeping surfaces a consumption
> outside premises (i)–(iii).

### 1.2 Conventions

Bases as in H4-M1 §8.1 / H4-M3 §1 (the MovesRBase BASE-INDEX CONVENTION,
δ ABSOLUTE): O_δ := W(F_{p^δ}), K_δ := O_δ[1/p], residue field
F_δ := F_{p^δ}, q₀ := p^δ = |F_δ|. Since K_δ/ℚ_p is unramified, v(p) = 1
and p is a uniformizer of O_δ. "The solve" is Step 5's object (ROOT
`docs/ROOT_ASSEMBLY_2026-08-02.md`): the block-triangular linear system at
the intended instance 𝔅_n, assembled from T-4's menu, T-7s's tables and
T-8's block organization, with per-type solved values R_τ ∈ ℚ(q).
ℛ := ℚ[q][𝒮⁻¹] is O-12's regular subring (𝒮 the cyclotomic-type
multiplicative set; Lean face `LeanUrat.MovesU.MemRcyc`). "Letter" and
"a_sym" are H4-M5's objects: the realized species letter and its p-free
symbolic exponent (H4-M5 §2 Def SYM).

### 1.3 The premise bundle, as NAMED rows (the [M]-hypotheses of this note)

Per the standing rule these are named structure rows of the conditional —
never axioms, never discharged by fiat, and their on-file status is §0.2's.

- **[P-AUDIT]** (= §3.3 premise (i)): the (UB-X)(a) per-leaf O_δ re-base
  audit is CLOSED — every H4-M3 row is class (i)–(iii) CLOSED or its
  class-(iv) lemma is PROVED. Operationally, what this row supplies below:
  every leaf the O_δ-side chain consumes (dictionary, run/CU, drainage,
  cylinder-law, census-interface, realizer-supply rows — H4-M3 §2's ten
  rows, INCLUDING row 10's Lemma RRE-δ) holds in its displayed re-based
  form over O_δ, so "the O_δ-realized species catalogue with censuses at
  q₀" is a WELL-FORMED object: the classifier runs, its realizer supply
  exists at ambient F_δ, and its realized ledger is the audited one. This
  row contributes well-formedness ONLY — no equation of §5 cites it for a
  value.
- **[P-LAW]** (= §3.3 premise (ii)): H4-M5's Route-B intrinsic law holds
  at the O_δ-realized ledger — for every realized position y,
  a_δ(y) = δ · a_sym(letter_δ(y)) — AND its ROOT re-scope has landed (the
  ledger-level substitution making the intrinsic law the operative row
  content, per blueprint §3.2 Route B). Consumed at H4-M5's ON-FILE status:
  the law is itself conditional on H4-M5 §1.3's rows [RUN-PROD],
  [LEDGER-READ], [LET-DATA], [SYM-ID], [M1-STATUS]; those rows TRAVEL
  INSIDE this premise (hypothesizing (ii) hypothesizes them). NO
  δ-stability and no cross-base dictionary enters through this row —
  that is Route B's displayed deletion (H4-M5 §4, §5.1).
- **[P-INHERIT]** (= §3.3 premise (iii)): the inherited §3.1 rows
  (H1)–(H3)/(H5)–(H9) at their standing conditionality, exactly as Step
  16's honest-scope display prices them for the O_δ-side chain: Step 8 is
  (GR-B)-conditional at orders ≥ 2 ((H1) group); Step 14's census is
  (FRESH)/(ADM)-conditional at orders ≥ 2 ((H2)/(H3)); the pack
  correspondence-plus-row-laws (H5)=(PACK, i–iv) identify the realized
  pack with the intended 𝔅_n instantiation entry-for-entry at q ↦ q^δ;
  (H6)–(H9) ride as displayed. This row supplies, in particular, the
  IDENTIFICATION through which "the block solve on the O_δ-realized
  species catalogue" is an instance of Step 5's 𝔅_n system ((H5) with
  Step 5's (B-INST) pin), and the (PACK-iii) wsh_ok membership of every
  row series in ℛ.

UNIT-INTERNAL INPUTS, with on-file grades (not premises — consumed
artifacts): H4-M1 §8.3's (EQ-1) slice table (PROVED at M1's §0.4
perimeter; consumed at on-file status — M1's two hostile passes ride
Wave 1's gate and are not asserted here); Step 5's solve structure +
(SL≥2) display (VERIFIED at honest scope — leaf #2); O-12's
pole-freeness incl. the Lean face `MovesU/O12PoleFree.lean` (same
VERIFIED leaf; `#print axioms` clean per that file's own footer).

### 1.4 The two sides of the commute, defined exactly

- **RHS.** R_τ ∈ ℚ(q) is the symbolic per-type solved value of Step 5's
  ONE system at 𝔅_n; "R_τ(p^δ)" means: evaluate THE SAME ℚ(q) element at
  the rational point q₀ = p^δ (well-defined by §4 — R_τ ∈ ℛ and ℛ members
  are defined at every rational ≥ 2).
- **LHS.** The O_δ-side assembled per-τ series, per §3.3's own
  parenthesis: run the block solve ON the O_δ-realized species catalogue
  — the linear system whose unknowns are indexed by the realized species/
  composition states of the O_δ classifier, whose coefficients are the
  realized censuses and per-letter alphabet/β-leg reads AT NUMERIC VALUES
  (base F_δ, so cardinality reads are powers of q₀) — then aggregate the
  per-species solved values by the type map into per-τ totals. NOTE this
  is the SOLVE output, not the σ-graded tree series; the tree-series tie
  is Step 18 (clause (R)) and is neither used nor asserted here.

## §2. PLAN ITEM (1) — the solve is ONE p-free symbolic system (Step 5, VERIFIED scope, displayed)

**Display S (Step 5's statement, quoted at its honest scope).** ROOT Step 5:
"at the abstract solve family 𝔅_n ..., for all three on-record kernel
organizations, EVERY block determinant and EVERY assembled denominator —
table coefficients, height resummations, normalizations, the final R_τ — is
cyclotomic-type (a unit of ℛ), hence nonvanishing at every prime power ≥ 2:
the failing set is EMPTY." Status: "VERIFIED at honest scope — leaf #2"; the
honest scope carried verbatim: "zeros/poles at 𝔅_n — VALUE correctness is
NOT part of this claim (that is D-11 + O-11); the extension to the eventual
general-n pack is gated by D-11 (instance pin) + the contingent OL-O12-1".
This note consumes Display S exactly there: pole/unit structure of the ONE
symbolic system; the identification of the realized pack with 𝔅_n is
[P-INHERIT]'s (H5)/(B-INST), and VALUE correctness is consumed nowhere.

**Display S′ (p-freeness — sourced at the construction, not at the
grammar; pass-1 finding 3 folded).** The p-freeness of §3.3's "p-free
menu/coefficients/pivots" is BY CONSTRUCTION of the intended instance: 𝔅_n
is ONE abstract object, "the §2.1-defined intended instance" assembled from
T-4's menu, T-7s's tables and T-8's block organization (Step 5's (B-INST)
display, quoted: "the pack consumed by Steps 17/18 is BY CONSTRUCTION the
𝔅_n member assembled from T-4's menu, T-7s's tables, and T-8's block
organization") — defined ONCE over ℚ(q), with p and δ appearing nowhere
among its defining data: its combinatorial data are the letter/type
integers (base-free at the walked slice, §3.1) and its entries are
q-expressions. O-12's grammar (g1)–(g6) (`MovesU/O12PoleFree.lean`,
`Gram`) then supplies the SHAPE of those entries — membership in ℛ — not
the p-freeness itself. What ties any particular base's realized pack to
this one object is exactly [P-INHERIT]'s (H5)/(B-INST) identification;
Display S′ claims nothing about realized packs.

**Display S″ (the uniqueness structure — (SL≥2) + the carrier shape,
quoted; pass-1 finding 1 folded).** ROOT Step 5's (SL≥2) display, the
parts consumed at §5 walk B: "(a) self-loops live inside one block: every
INTER-block booking descends strictly ... so the block solve is triangular
with the within-block (S-loop) return as the ONLY diagonal entry". The
diagonal data present as SCALAR block determinants: the O-12 Lean face's
own carrier shape (`AbsSolveTable` docstring, quoted: "per block a
(1×1-kernel) determinant Φ_e ∈ ℚ(q) ... The four 𝔅_n bookings, with every
composition and allocation datum, present as members of this shape"), and
Display S covers exactly these: "EVERY block determinant ... is
cyclotomic-type (a unit of ℛ)" — an ℛ-unit meaning both Φ_e and Φ_e⁻¹ lie
in ℛ (the face's `RcycDiscipline`). CONSEQUENCE, at the displayed
altitude: the ONE system is block-triangular (inter-block order strict)
with per-block scalar determinants Φ_e that are ℛ-units; solving = one
Φ_e-division per block along the triangular order (back-substitution).
UNIQUENESS over ℚ(q) and after evaluation both reduce to: each Φ_e (resp.
each evaluated Φ_e(q₀)) is invertible — the evaluated case is §4's
Display E via the face's `RegAt` nonzero clause, extracted at Seed 6.
That the realized O_δ-side system presents as a member of this same
carrier shape rides [P-INHERIT]'s (H5)/(B-INST), like every other
realized-pack identification in this note.

**Display X (solution membership in ℛ; pass-1 finding 2 folded).** Every
per-species component of the symbolic solution lies in ℛ: by S″ the solve
is back-substitution along the triangular order, each step of the form
x_block = Φ_e⁻¹·(finite ℛ-linear combination of entries and already-solved
components); entries lie in ℛ (Display S: "EVERY assembled denominator —
table coefficients, height resummations, normalizations, the final R_τ"),
Φ_e⁻¹ ∈ ℛ (S″), and ℛ is a ring — so by induction along the (finite,
strict) triangular order every component x_σ⃗(q) ∈ ℛ, not only the
aggregated R_τ.

## §3. PLAN ITEM (2) — the catalogue and aggregation displays

### 3.1 The (EQ-1) slice, consumed FROM H4-M1 §8.3 (displayed, not presumed)

H4-M1's step-8 expanded charge executed the check this unit consumes; its
verdict, quoted verbatim (`H4M1_rpack_attempt.md` §8.3):

> VERDICT: within the walked §B2-DEF slice, no species definition consumes
> q. What changes under re-basing is exactly the REALIZATION side — digit
> value sets 𝔸 (cardinality q^{a_q}, Lemma STAB), scalar groups, u(γ)'s
> value — never a defining field.

and its SCOPE FENCE, quoted with equal prominence:

> this check covers the T-1 stage/ledger grammar (§B2-DEF's slice); species
> fields living OUTSIDE the walked text — the multiplicity μ (D.8's
> landing/read selection), side selection, polygon conventions of the
> catalogue layer — are not walked here, and H4-M6's §3.3 plan item (2)
> consumes exactly THIS slice check plus its own type-catalogue display for
> the remainder.

What the slice buys §5: the LETTERS — the species' defining integer data
(d; (e_j, h_j, g_j); stage index; height) — are the same grammar objects
over every base; a letter is never q-forbidden and never q-created within
the walked slice. What it does NOT buy (the fence): the catalogue-layer
occurrence bookkeeping (WHICH compositions the realized pack books, with
which multiplicities μ and side/polygon conventions). That remainder is
NOT proved base-free here either: in §5 it rides [P-AUDIT] (the audited
re-based leaves) and [P-INHERIT]'s (H5) correspondence at q ↦ q^δ —
displayed at walk A1 and audited at §6.

### 3.2 Display T — the type catalogue is base-free integer combinatorics

**Display T.** For ANY local field K with finite residue field (in scope:
every K_δ, δ ≥ 1), a degree-n splitting type is the unordered multiset
τ = {(e₁, f₁), …, (e_r, f_r)} of (ramification index, residue degree) pairs
of the factor fields of a degree-n étale K-algebra, with Σᵢ eᵢfᵢ = n.
(T-a) *The index set is base-free by construction:* Types(n) := {multisets
of pairs of positive integers with Σ ef = n} is a finite set defined by n
alone — the SAME set for every K_δ and for ℚ_p. Nothing to prove: the
parameterization consumes only n.
(T-b) *No type is base-forbidden (onto-ness at every K_δ):* every
τ ∈ Types(n) is realized over every K_δ. Per pair (e, f): the unramified
extension of K_δ of degree f exists and is unique (it is K_{δf} — finite
fields have extensions of every degree; the Witt/Teichmüller equivalence
pinned at H4-M1's row, Serre, Corps Locaux II §4–6); a totally ramified
extension of degree e exists (Eisenstein: x^e − p over K_δ, since
v(p) = 1; Serre, Corps Locaux — section number flagged for lookup, standard
Eisenstein theory); their compositum L over K_δ has invariants (e, f), and
the product Πᵢ L_{(eᵢ,fᵢ)} is a degree-n étale algebra of type τ. Status:
(a) known — standard local-field structure theory; no corpus leaf is
consumed. Role in §5: the τ-index of the aggregation is the SAME finite
index set on both sides, with no empty-type degeneracy to bookkeep.

### 3.3 Display A — the aggregation map is base-independent

**Display A.** The aggregation step sends the solve's per-species/
per-composition solved values to per-τ totals: a composition datum σ⃗ =
(σ₁, …, σ_r) (the exit composition the verdict rows book — the shape
visible at [P-INHERIT]'s (PACK-iv) display, whose β-legs read at
accumulated residue degrees D_i) is mapped to
type(σ⃗) := {(e(σᵢ), f(σᵢ))}ᵢ ∈ Types(n), where e(σᵢ) and f(σᵢ) are the
slot's total ramification index and total residue degree — INTEGER-valued
functions of the letter data (the stage tuples' e_j, the degree data d,
g_j) and of the composition's accumulated-degree bookkeeping (the integers
D_i). By §3.1's slice verdict these defining fields are base-free grammar
integers; hence type(·) is THE SAME function of the composition datum over
every base — the map commutes with re-basing IDENTICALLY, before any
evaluation. FENCE, displayed: WHICH composition data occur (the occurrence
multiset the realized pack books) is catalogue-layer occurrence data — the
§3.1 fence's remainder — and rides [P-AUDIT] + [P-INHERIT]'s (H5), never
this display. Display A asserts only: the FUNCTION aggregating solved
values by type is base-independent.

## §4. PLAN ITEM (3) — evaluation at q₀ = p^δ is a ring-hom on ℛ, defined at every prime power (O-12, VERIFIED; no new work)

**Display E.** ℛ = ℚ[q][𝒮⁻¹] is the subring of ℚ(q) on which evaluation at
any rational x ≥ 2 is a well-defined ring homomorphism ev_x : ℛ → ℚ: every
member of the multiplicative set 𝒮 (generated by q and the q^c − 1) is
strictly positive at x ≥ 2 (O-12 L5), so denominators never vanish —
O-12's L7(i), Lean face `MemRcyc.definedAt`. Every evaluation point of the
O_δ-side chain is q₀ = p^δ with p prime and δ ≥ 1, hence a rational ≥ 2:
O-12's pole-freeness covers q₀ = p^δ with NO new work — the Lean face even
carries the exact statement (`AbsSolveTable.regAt_primePow`: (REG-p) at
every prime p and every depth δ ≥ 1), and `RegAt` is NOT opaque (pass-1
finding 6 folded) — its definition, quoted from the face:

    def AbsSolveTable.RegAt (T : AbsSolveTable) (x : ℚ) : Prop :=
      ∀ e, (DefinedAt (T.Phi e) x ∧ (T.Phi e).eval (RingHom.id ℚ) x ≠ 0)
             ∧ ∀ g ∈ T.entries e, DefinedAt g x

— every block determinant DEFINED AND NONZERO at x, every entry defined.
The NONZERO clause is what walk B's pivot inversion needs; Seed 6 extracts
it as a compiled one-liner. Every object §5 evaluates lies in ℛ: the
system's coefficients and block determinants by Display S/S″, EVERY
per-species solution component by Display X, the row series by
[P-INHERIT]'s (PACK-iii) wsh_ok, and the solved values R_τ by Display S
("the final R_τ"). Ring-hom-ness of ev_x on ℛ is the standard localization
evaluation (finite sums and products go through; the seed lemmas below
display the instances §5 uses). The seeds in §4.L consume the Lean face BY
IMPORT at exactly this point.

## §5. PLAN ITEM (4) — the assembly bookkeeping: THE THEOREM

**Theorem ((UB-X)(c) as §3.3's displayed conditional).** Assume rows
[P-AUDIT], [P-LAW], [P-INHERIT] (§1.3). Then for every δ ≥ 1 and every
degree-n splitting type τ over K_δ, the O_δ-side assembled per-τ series
(§1.4 LHS) equals R_τ(p^δ) (§1.4 RHS).

*Proof walk.* Fix p, δ ≥ 1; write q₀ := p^δ.

**A. The O_δ-side system is the symbolic system evaluated at q₀.** Three
sub-matches, one per kind of entry.

- **A1 (states and shape).** By [P-AUDIT], the O_δ-realized species
  catalogue is well-formed and is the audited re-based object (H4-M3's ten
  rows; row 10 supplies the run-realizer at ambient F_δ). By §3.1's (EQ-1)
  slice, its letters are the base-free grammar letters; by [P-INHERIT]'s
  (H5)/(B-INST) identification (Step 5's by-construction pin at q ↦ q^δ),
  the realized pack's state set, block organization, and entry lists are
  those of the intended 𝔅_n instantiation ENTRY-FOR-ENTRY. So the O_δ-side
  system has the SAME index set, the same triangular block order (Display
  S″(a)), and entry slots matched one-for-one with the symbolic system's.
  The catalogue-layer occurrence remainder (§3.1's fence) enters exactly
  here and is priced exactly by these two rows — displayed, not absorbed.
- **A2 (census entries; pass-1 finding 4 folded — three displayed legs,
  no widened quote).** (leg 1) VALIDITY over the base: the census layer is
  stated over an arbitrary absolutely-unramified complete DVR from the
  start — Step 16's honest-scope item (i), "the GD/census layers (Steps 8,
  14) hold over an arbitrary absolutely-unramified complete DVR —
  proved/stated at that generality from the start", GD23's generality
  audit V26-confirmed (VERIFIED, inside leaf #4). (leg 2) POLYNOMIALITY
  with q = the base's residue cardinality: the census laws are
  q-polynomial statements in the residue cardinality by the layer's own
  convention — ROOT §3.4 row 6: "the COUNT laws (CL-6's polynomiality =
  the census) → Step 14", and the (ADM) row's operative form is stated at
  dim_{F_q} over the base's residue field; over O_δ that cardinality is
  q₀ = |F_δ| = p^δ. (leg 3) INTERFACE: that the solve consumes censuses
  ONLY through this q-read, in their audited re-based statements, is
  [P-AUDIT]'s rows 7–8 (O-1thr; O-10 K-COUNT/K-JAC — H4-M3's audited
  census-interface leaves). Together: the O_δ-side census numbers are the
  same census polynomials evaluated at q₀ — no leg claims more than its
  display. Conditionality carried: (FRESH)/(ADM) at orders ≥ 2 —
  [P-INHERIT]'s (H2)/(H3) rows, the §0.4 adjudication.
- **A3 (alphabet/β-leg entries — where [P-LAW] fires; pass-1 finding 5
  folded — shape vs numbers split).** SHAPE: WHICH q-expression sits in
  each entry slot — including the verdict rows' β-legs read at accumulated
  residue degrees, the (PACK-iv) display's β_μ(σ)(q^{D}) form — is part of
  the entry-for-entry identification of A1, i.e. [P-INHERIT]'s
  (H5)/(PACK-iv) at q ↦ q^δ; A3 does NOT re-derive it from cardinalities.
  NUMBERS: what A3 proves is that the O_δ-side NUMERIC reads instantiate
  those expressions at q = q₀. Per-letter alphabet reads: by [P-LAW], at
  every realized position y, a_δ(y) = δ·a_sym(letter_δ(y)), with a_sym the
  p-free symbolic exponent the ONE system's entries carry (H4-M5 Def SYM +
  its [SYM-ID] row, traveling inside [P-LAW]); by Lemma STAB (H4-M1 §5.4,
  PROVED there; consumed at on-file status) every realized alphabet
  cardinality is an exact p-power with the ledger exponent, so
      |𝔸_δ(y)| = p^{a_δ(y)} = p^{δ·a_sym(ℓ)} = (p^δ)^{a_sym(ℓ)} = q₀^{a_sym(ℓ)}
  — the bridging identity p^(δ·a) = (p^δ)^a (Seed 1, `card_rebase`).
  Accumulated-degree reads: the O_δ-side continuation field at accumulated
  residue degree D is F_{(p^δ)^D} = F_{p^{δ·D}} (degrees multiply along
  unramified towers; the letter datum D is a base-free integer by §3.1),
  cardinality q₀^D — the same identity. So every NUMERIC entry of the
  O_δ-side system equals its (H5)-identified symbolic q-expression
  evaluated at q = q₀. NO δ-stability is invoked: [P-LAW] is intrinsic
  per-base (Route B's displayed deletion).

  Conclusion of A: entry-for-entry, the O_δ-side system IS ev_{q₀} of the
  symbolic system: coefficients A(q₀), inhomogeneous data b(q₀), same
  unknowns and same triangular order.

**B. Solving commutes with ev_{q₀}** (pass-1 findings 1/2/6 folded). The
symbolic solution x(q) (the per-species solved values, R_τ their
type-aggregates) satisfies A(q)·x(q) = b(q), with every coefficient/datum
entry in ℛ (Displays S/S″) AND every solution component in ℛ (Display X —
so ev_{q₀} applies componentwise and the later sums stay in its domain).
ev_{q₀} is a ring hom on ℛ (Display E), so applying it to each defining
equation gives A(q₀)·x(q₀) = b(q₀): THE EVALUATED SOLUTION SOLVES THE
EVALUATED SYSTEM (per-entry transport = Seed 2, `solve_step_commutes`,
summed over the finite row). Uniqueness of the evaluated system's
solution, at Display S″'s displayed altitude: the system is
block-triangular with SCALAR per-block determinants Φ_e (S″'s carrier-
shape quote), so a solution is determined block-by-block along the strict
triangular order once each evaluated Φ_e(q₀) is invertible in ℚ; and
Φ_e(q₀) ≠ 0 is exactly the `RegAt` NONZERO clause at q₀ = p^δ (Display E;
Seed 4 instantiates `regAt_primePow` there, Seed 6 extracts the clause,
Seed 3 is the per-block cancellation). Hence the O_δ-side solved values —
a solution of the O_δ-side system, which by A IS the evaluated system —
equal x(q₀), the unique one. That the realized system presents in the
`AbsSolveTable` carrier shape with the ℛ-discipline rides [P-INHERIT]'s
(H5)/(B-INST) + Display S, as displayed at S″.

**C. Aggregation commutes.** By Display A the type map is the same
function of the composition data on both sides; by Display T its index set
Types(n) is the same finite set. The per-τ total is a FINITE sum of solved
values over the type-map fiber; ev_{q₀} is additive on ℛ (Display E). So
  (O_δ-side per-τ series) = Σ_{type(σ⃗)=τ} x_{σ⃗}(q₀)
    = ev_{q₀}( Σ_{type(σ⃗)=τ} x_{σ⃗}(q) ) = ev_{q₀}(R_τ) = R_τ(p^δ),
the SAME ℚ(q) element specialized. ∎

REMARK (where each premise fired): [P-AUDIT] at A1 (well-formedness) and
A2 leg 3 (the census-interface rows); [P-LAW] at A3 (the only value-level
use, and the only place δ multiplies an exponent); [P-INHERIT] at A1
((H5)/(B-INST) entry-for-entry), A2 ((H2)/(H3)), A3 ((H5)/(PACK-iv) entry
shape), and B ((PACK-iii) membership + the carrier-shape identification).
The unit-internal inputs fired at: §3.1 slice (A1/A3's letter
base-freeness), Displays S/S′/S″/X (A1/B), Display E (B/C), Displays T/A
(C).

## §6. CONSUMPTION AUDIT (the finding-8 fence, executed)

Complete list of everything consumed above, with grade:

| input | where | grade at consumption |
|---|---|---|
| [P-AUDIT], [P-LAW], [P-INHERIT] | §5 A1/A3/A1-A2-B | HYPOTHESES of the conditional (named rows; on-file status §0.2 — (i) unsatisfied, (ii) partial, (iii) standing) |
| H4-M1 §8.3 (EQ-1) slice table + fence | §3.1, §5 A1/A3 | PROVED on file at M1's §0.4 perimeter (consumed at status) |
| H4-M1 §5.4 Lemma STAB | §5 A3 | PROVED on file (same perimeter) |
| H4-M5 §4 Theorem (RB) + Def SYM | §5 A3, inside [P-LAW] | PROVED-CONDITIONAL on file (its rows travel inside [P-LAW]) |
| Step 5 Displays S/S′/S″ ((SL≥2), (B-INST)) + Display X (derived from them in-note) | §2, §5 A1/B | VERIFIED leaf #2 at honest scope (poles/units only; value correctness NOT consumed); X is this note's own induction over S/S″'s displays |
| Step 16 honest-scope item (i) (GD/census arbitrary-DVR; GD23 V26) | §5 A2 leg 1 | VERIFIED (leaf #4); (FRESH)/(ADM) conditionality carried into [P-INHERIT] |
| ROOT §3.4 row 6 census-polynomiality display ("CL-6's polynomiality = the census") + the (ADM) row's dim_{F_q} form | §5 A2 leg 2 | displayed ledger rows, consumed AS displays (the q-read convention) |
| O-12 pole-freeness + Lean face (`MemRcyc.definedAt`, `AbsSolveTable` carrier + `RegAt` def + `regAt_primePow`; `MemRcyc.powSubst` available) | §2 S″, §4, §5 B | VERIFIED leaf #2; Lean face compiled, axiom-clean per its footer |
| Display T (local-field type catalogue) | §3.2, §5 C | (a) known — standard theory (Serre pins; one section number flagged for lookup) |
| Seeds 1–6 (`card_rebase`, `solve_step_commutes`, `pivot_unique`, `solveTable_regular_at_qdelta`, `memRcyc_definedAt_qdelta`, `regAt_pivot_ne_zero`) | §5 A3/B | PROVED below, this file, Lean-core |

NOT consumed anywhere (the circularity fence, checked line-by-line against
§5): Step 16's clause-(UB) package or its transported chain; Step 17/18/18b
(no series-tie, no mass identification, no Haar statement); (UB-X)(b) or
(K3-δ) (no δ-stability); H4-M2's dictionary (no cross-base matching);
Theorem C / the counting layer (beyond [SYM-ID]'s pin inside [P-LAW], which
H4-M5 already displays as row content, not consumption).

## §7. WHAT THIS NOTE DOES NOT DO (fences)

1. NO discharge of (UB-X)(c): premise (i) is OPEN on file (Lemma RRE-δ,
   H4-M3 row 10) and premise (ii)'s ROOT re-scope has not landed. The
   conditional stands ready; the discharge claim belongs to the Wave-4/5
   gates (H4-M7's ROOT-sync brief), never to this note.
2. NO new Lean face: the seeds are generic algebra; the (UB-X)(c) Lean
   face, if ever wanted, is a fenced-design decision downstream of the H4-F5/
   F6 carriers (blueprint §L.5) — made against this note, not in it.
3. NO claim about the tree series or densities: the LHS is the solve
   output (§1.4); the series-tie (Step 18) and the density bracket (Step
   18b/19) are untouched, at every base.
4. NO base-freeness claim for the catalogue-layer occurrence data (μ, side
   selection, polygon conventions): §3.1's fence stands; that remainder is
   priced inside [P-AUDIT]/[P-INHERIT], displayed at §5 A1.
5. The numeric-gate line: this unit's blueprint row names NO numeric gate
   (gate = hostile pass ×1); no numerics were run, none are cited beyond
   the sealed suites quoted inside consumed artifacts.

## §8. GATE RECORD — hostile pass ×1 (charged count), passes run: 2

**Pass 1** (Codex, fresh context, quote-and-classify charge, note text
only): VERDICT **REJECT — 1 CRITICAL, 5 GAPS**. Every finding ACCEPTED and
FOLDED IN PLACE in this revision; dispositions:
1. CRIT — walk B's uniqueness over-read Displays S/S″ ("every diagonal
   pivot is an ℛ-unit" was not displayed; scalar back-substitution did not
   follow). FIXED: S″ rewritten to route uniqueness through the BLOCK
   DETERMINANTS Φ_e (which Display S does cover) + the O-12 face's own
   scalar-kernel carrier shape (`AbsSolveTable` docstring, now quoted) +
   `RegAt`'s nonzero clause; walk B restated at that altitude; the
   realized-side carrier identification displayed as riding
   [P-INHERIT]'s (H5)/(B-INST).
2. GAP — solution components x(q) not placed in ℛ before componentwise
   evaluation. FIXED: new Display X (back-substitution induction: entries
   ∈ ℛ, Φ_e⁻¹ ∈ ℛ, ℛ a ring ⇒ every component ∈ ℛ); walk B cites it.
3. GAP — S′ sourced p-freeness at grammar membership (insufficient).
   FIXED: S′ re-sourced at the (B-INST) by-construction display (𝔅_n is
   ONE object defined over ℚ(q); the grammar supplies only entry SHAPE).
4. GAP — A2's "same census polynomials at residue cardinality" exceeded
   the quoted arbitrary-DVR scope. FIXED: A2 split into three displayed
   legs (validity = Step 16 item (i); polynomiality-in-q convention =
   ROOT §3.4 CL-6 row + the (ADM) dim_{F_q} form; interface =
   [P-AUDIT] rows 7–8), each consuming only its display.
5. GAP — A3 derived β-leg VALUES from cardinalities. FIXED: A3 split into
   SHAPE (the (H5)/(PACK-iv) entry identification, hypothesized inside
   [P-INHERIT]) vs NUMBERS (what A3 proves: the numeric reads instantiate
   the identified expressions at q₀ — [P-LAW] + Lemma STAB + Seed 1).
6. GAP — Seeds 4/5 did not establish nonzero pivots (`RegAt` opaque,
   `DefinedAt` ≠ nonzero). FIXED: `RegAt`'s definition quoted in Display E
   (its nonzero clause displayed) + new Seed 6 `regAt_pivot_ne_zero`
   extracting exactly that clause, compiled.

**Pass 2** (on the post-fold text): PENDING at this revision; its real
verdict and per-finding dispositions are appended here after it runs. A
revision in which this line still reads PENDING has not completed its
gate sequence.
-/

import Mathlib
import LeanUrat.MovesU.O12PoleFree

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H4.UBXc

open LeanUrat.MovesU

/-! ## §4.L/§5.L — the seed layer (generic; no H4 carrier, no law shape)

Six seeds, each a display point of §5's walk. They are deliberately
GENERIC: none mentions letters, ledgers, packs, or (UB-X); per the H4-M5
precedent the H4 Lean faces stay fenced. -/

/-- **Seed 1 (§5 A3's bridging identity).** The single arithmetic fact that
turns the O_δ-side cardinality reads into evaluations of the symbolic
q-expressions at q₀ = p^δ: p^(δ·a) = (p^δ)^a. -/
theorem card_rebase (p δ a : ℕ) : p ^ (δ * a) = (p ^ δ) ^ a :=
  pow_mul p δ a

example : (3 : ℕ) ^ (2 * 4) = (3 ^ 2) ^ 4 := card_rebase 3 2 4

/-- **Seed 2 (§5 B's transport, per-entry).** A ring homomorphism carries a
solved (pivot · unknown = data) equation to the evaluated equation. Walk B
applies this per entry and sums over the finite row. -/
theorem solve_step_commutes {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {u x b : R} (h : u * x = b) : φ u * φ x = φ b := by
  rw [← map_mul]
  exact congrArg φ h

/-- **Seed 3 (§5 B's uniqueness, per pivot).** At a unit pivot the solved
value is unique — the back-substitution step of Display S″ after
evaluation. -/
theorem pivot_unique {S : Type*} [CommRing S] {v y₁ y₂ c : S}
    (hv : IsUnit v) (h₁ : v * y₁ = c) (h₂ : v * y₂ = c) : y₁ = y₂ :=
  hv.mul_left_cancel (h₁.trans h₂.symm)

/-- **Seed 4 (§4's Display E at the corpus Lean face).** O-12's (REG-p)
instantiated at q₀ = p^δ for p carried as a `Fact`-prime: any solve table
under the ℛ-discipline is regular (pivots defined and nonzero, entries
defined) at every depth δ ≥ 1. Pure consumption of
`AbsSolveTable.regAt_primePow` (VERIFIED leaf #2's Lean face). -/
theorem solveTable_regular_at_qdelta (T : AbsSolveTable)
    (hT : T.RcycDiscipline) (p : ℕ) [hp : Fact p.Prime] {δ : ℕ}
    (hδ : 1 ≤ δ) : T.RegAt ((p ^ δ : ℕ) : ℚ) :=
  T.regAt_primePow hT hp.out.two_le hδ

/-- **Seed 5 (§4's Display E, membership form).** Every member of O-12's
regular subring ℛ is defined at q₀ = p^δ — the "SAME ℚ(q) element
specialized" is well-defined at every prime power. Pure consumption of
`MemRcyc.definedAt`. -/
theorem memRcyc_definedAt_qdelta {f : RatFunc ℚ} (hf : MemRcyc f)
    (p : ℕ) [hp : Fact p.Prime] {δ : ℕ} (hδ : 1 ≤ δ) :
    DefinedAt f ((p ^ δ : ℕ) : ℚ) := by
  refine hf.definedAt ?_
  have h2 : (2 : ℕ) ≤ p ^ δ :=
    le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
  exact_mod_cast h2

/-- **Seed 6 (§5 B's nonzero-pivot extraction; pass-1 finding 6).** The
`RegAt` predicate is not opaque: its first clause's second component IS
the nonzero evaluation of the block determinant — extracted here so the
prose's "each evaluated Φ_e(q₀) is invertible in ℚ" claim is a compiled
one-liner over the face, not a gloss. -/
theorem regAt_pivot_ne_zero (T : AbsSolveTable) {x : ℚ} (h : T.RegAt x)
    (e : Fin T.nBlocks) : (T.Phi e).eval (RingHom.id ℚ) x ≠ 0 :=
  (h e).1.2

end LeanUrat.Scaffold.HDischarge.H4.UBXc

#print axioms LeanUrat.Scaffold.HDischarge.H4.UBXc.card_rebase
#print axioms LeanUrat.Scaffold.HDischarge.H4.UBXc.solve_step_commutes
#print axioms LeanUrat.Scaffold.HDischarge.H4.UBXc.pivot_unique
#print axioms LeanUrat.Scaffold.HDischarge.H4.UBXc.solveTable_regular_at_qdelta
#print axioms LeanUrat.Scaffold.HDischarge.H4.UBXc.memRcyc_definedAt_qdelta
#print axioms LeanUrat.Scaffold.HDischarge.H4.UBXc.regAt_pivot_ne_zero
