/-
# H4-M5 — the SELECTED ROUTE PROVED: Route B, the intrinsic per-base ledger law a_δ(y) = δ·a_sym(letter_δ(y)) over W(F_q) (Fable prover H4-M5, 2026-08-01, Wave 3)

Unit H4-M5 of `lean/blueprints/HDISCHARGE_H4.md` (§M table + §3.2). This file
is a LITERATE LEAN MARKDOWN NOTE (the H4-M2/M4 format): prose in comment
blocks, every Lean declaration compiles. Gate command (from `lean/`):
`lake env lean notes/openmath/H4M5_k3delta_attempt.md` — green, zero sorry.
The unit's OTHER gates: hostile pass ×2 (ledger at the end) and the N-K3
SEALED PREDICTIONS (§6 — sealed here pre-run; no N-K3 artifact exists on
file at composition, re-verified this session).

CHARGE (blueprint §M row, verbatim): "`lean/notes/openmath/
H4M5_k3delta_attempt.md` — the selected route PROVED | Route A: the match
display at K3-c's pools; Route B: the intrinsic per-letter law over W(F_q)
(M14 Theorem vs the symbolic skeleton) | H4-M1 + H4-M4 (+ H4-M2 on Route A)
| MED–HARD (route-dependent) | hostile pass ×2; N-K3 sealed predictions."

ROUTE SELECTION INPUT (H4-M4 §5.5, on file): **ROUTE B** — "Per §5.2 the
dictionary does not land a cheap A … Route A is retained on the record as
the fallback ONLY if the ROOT owner declines the re-scope." This unit
therefore proves ROUTE B; no Route-A artifact is attempted, and H4-M2's
dictionary is NOT a dependency of anything below.

STATEMENT-FENCE RECORD: the blueprint has NO §L Lean spec for H4-M5 (it is
a §M math-note unit); the charge text is transcribed verbatim above and the
blueprint §3.2 Route-B text is transcribed verbatim in §1.1 below. The
Route-B LEAN FACE IS FENCED (H4-F5, blueprint §L.5: "Gated on H4-M4
selecting Route B AND the ROOT re-scope landing; consumers re-point from
`UBXbStmt`/`K3deltaStmt` only then") — only the FIRST of the two gates has
fired (M4's recommendation; the ROOT re-scope has NOT landed). Accordingly
this note lands NO face: every Lean declaration below is note-internal
PROOF-LAYER vocabulary in the fresh namespace
`LeanUrat.Scaffold.HDischarge.H4.RouteB` (its rows are the note's named
[M]-hypotheses, typed; §4.L), and NO consumer may re-point to it — the
H4-F5 designer makes the carrier decisions AGAINST this proven note, per
M4 §3.2's carrier caution. Corpus faces (`RealizedLedger`, `SlotTree`,
`SlotTree.dimOf`, `SlotTree.dimOf_scale`, `AlphabetData`) are consumed by
IMPORT, verbatim, never re-transcribed or weakened.

## §0. Verdict summary

1. **Route B's intrinsic law is PROVED at the displayed perimeter** (§4
   Theorem): for every δ ≥ 1 and every position y the O_δ classifier
   realizes, a_δ(y) = δ·a_sym(letter_δ(y)) — where letter_δ(y) is the
   classifier's OWN realized species letter and a_sym its p-free symbolic
   exponent (§2 Def SYM). The proof is exactly the blueprint's shape:
   H4-M1's (R1)–(R3) over W(F_q) (all q at once) + M14's Theorem induction
   re-run against the SYMBOLIC skeleton (the letter's catalogue slot tree)
   instead of against the ℤ_p realization (§2 Lemma S — the Lemma-1
   leverage). NO cross-base dictionary, NO (R4), NO δ-stability hypothesis
   is consumed anywhere in §§2–4.
2. **Perimeter, honest** (§1.3): two NAMED rows fence the quantifier "the
   O_δ classifier realizes" — [RUN-PROD] (realized positions ride §B2-DEF
   recipe towers with (I-aug) reads; D.8/D.10 bookkeeping over W(F_q),
   REL.1's wider walk, outside H4-M1's §0.4 perimeter) and [LET-DATA] (the
   realized letter determines the integer slot-tree datum; the catalogue
   grammar slice). Plus H4-M1 consumed at its ON-FILE status (its own
   hostile passes ride Wave 1's gate and are NOT asserted here).
3. **NOTHING IS DISCHARGED by this proof as the rows stand** (blueprint
   finding 3, quoted §5.3): the intrinsic law does not imply that realized
   positions are δ-stable, and the authoritative (UB-X)(b)/(K3-δ) texts
   quantify over stability. The worked F₉-shape instance (§5.2) EXHIBITS
   the gap: a realized position satisfying the intrinsic law exactly while
   failing `Stable`. This proof and H4-M7's re-scope brief travel together;
   the ROOT owner's re-scope precedes any discharge claim (M4 §6's order).
4. **N-K3 sealed predictions** (§6): P1 the intrinsic law EXACT at every
   realized δ > 1 pool of the n = 3 pack; P2 δ | a_δ per pool; P3 NO
   prediction on the gcd criterion (Route-B agnosticism, displayed); P4
   the (EQ-2) read at certified-stable pools. Violation handling = M4
   §5.3's precedence branches, quoted.
5. Lean layer: the note's [M]-rows typed as the note-internal interface
   `SymConf` (NOT the H4-F5 face); `intrinsic_law`, `pool_exponent_read`,
   `intrinsic_dvd`, `root_instance`, `eq2ii_of_letter_match`,
   `f9_shape_contrast` all proved outright, zero sorry, Lean-core axioms.

## §1. The statement, made exact

### 1.1 Route B, verbatim (blueprint §3.2, the selected route)

> **Route B — the intrinsic re-scope (recommended target).** Replace the
> cross-base matching by the intrinsic per-base ledger law: for every δ and
> every position y the O_δ classifier REALIZES, a_δ(y) = δ · a_sym(letter_δ(y)),
> where a_sym is the letter's p-free symbolic exponent (the ℤ_p-side
> per-letter law is Theorem C's accepted conformance at q = p). Proof shape:
> (R1)–(R3) at base W(F_q) (H4-M1, all q at once) + M14's Theorem run against
> the SYMBOLIC skeleton (the letter's catalogue slot tree) instead of against
> the ℤ_p realization — the skeleton comparison is H4-M1's Lemma-1 leverage;
> NO cross-base dictionary and no δ-stability hypothesis remain. STATUS OF
> ROUTE B, exact (corrected at the Codex fold, finding 3): Route B does NOT
> discharge the rows AS STATED — the intrinsic law does not imply that
> realized positions are δ-stable, and the authoritative (UB-X)(b)/(K3-δ)
> texts quantify over stability. Route B is a REPLACEMENT obligation [...]
> Until the ROOT owner lands that re-scope, nothing is discharged by a
> Route-B proof; the proof + re-scope brief travel together (H4-M5 + H4-M7).

### 1.2 The objects, pinned

Notation: q := p^δ (δ ≥ 1 absolute, MovesRBase convention), O_δ := W(F_q),
A^(q) := O_δ[x]. All tower/residue objects are the REBUILT ones of H4-M1
(mutatis-mutandis rule; laws verbatim, objects rebuilt).

- **A realized position y.** A position class the O_δ classifier's own run
  realizes: y rides a tower over O_δ presented by the §B2-DEF recipe (H4-M1
  §0.3: base datum (φ, e₁, h₁) with φ̄ irreducible over F_q of degree d;
  increment data ψ_j monic irreducible OVER THE REBUILT F_j of degree g_j,
  reads (e_j, h_j) with gcd = 1 and (I-aug)), at a stage index k+1 ≤ K+1
  and height γ. That every classifier-realized position rides such a
  presented tower is row [RUN-PROD] (§1.3).
- **Its letter, letter_δ(y).** The classifier's OWN realized species letter
  of y — the catalogue species the run assigns to the position it actually
  built. CARRIER CAUTION (M4 §3.2, binding): this is NOT automatically the
  M14 §7.2 `posLetter` (which, at a §7.2-conforming instance, returns the
  designated OFF-DOMAIN letter at split prefixes — exactly the positions
  where the intrinsic law must still read a GENUINE letter). Here
  letter_δ(y) is genuine at every realized position: a split residual is
  realized as its own (per-branch) species with its own letter (§5.2 shows
  this live). Row [LET-DATA] (§1.3) pins what the letter determines.
- **The letter's integer datum.** data(ℓ) := (d; (e_j, h_j, g_j)_{j≤k}; the
  position's stage index and height γ) — the catalogue slot-tree datum. By
  the species grammar these are integer fields (stage tuples, degree data);
  no residue-field SIZE enters any of them — H4-M1 §8.3's (EQ-1) slice
  verdict ("within the walked §B2-DEF slice, no species definition consumes
  q"), walked there display-by-display.
- **a_sym(ℓ), the p-free symbolic exponent.** Defined in §2 (Def SYM) by
  running the D.9(a)/D.3(e) integer recursion on data(ℓ) alone: symbolic
  weight sets, anchors, slot heights, attainable index sets, the finite
  slot tree T(ℓ), and a_sym(ℓ) := (number of leaves of T(ℓ))·d. Pure
  integer arithmetic — no p, no q, no δ.
- **a_δ(y).** The ledger's F_p-normalized alphabet exponent at y over O_δ:
  |𝔸^{(δ)}(y)| = p^{a_δ(y)} (the `AlphabetData.card_eq` normalization; by
  H4-M1 §5.4 Lemma STAB the alphabet is an F_q-subspace, so equivalently
  a_δ = δ·dim_{F_q} 𝔸^{(δ)}(y)).

**THE STATEMENT (Route B's intrinsic per-base ledger law).** For every
prime p, every δ ≥ 1, and every position y the O_δ classifier realizes:

  **(RB)   a_δ(y) = δ · a_sym(letter_δ(y)).**

### 1.3 The named perimeter rows (the [M]-hypotheses of this note)

- **[RUN-PROD]** — every position the O_δ classifier realizes rides a
  §B2-DEF recipe tower over W(F_q) with rebuilt residue data and (I-aug)
  reads (H4-M1 §0.3's presentation). This is the run-production layer
  D.4 + D.8 + D.10 over W(F_q) — REL.1's wider walk, explicitly OUTSIDE
  H4-M1's proven perimeter (§0.4 fence; D.4's three-bullet argument is
  itself walked base-free at M1 §3.4, so the residue of this row is
  D.8/D.10 bookkeeping only). At q = p the row is the ACCEPTED base
  theory's own run-production. Named, never absorbed.
- **[LET-DATA]** — the realized letter of a realized position determines
  its integer slot-tree datum data(ℓ) = (d; (e_j, h_j, g_j)_{j≤k}; stage
  index; height), and the presented tower's own stage data CONFORM to it
  (the letter IS the species of the tower the run built, and the species
  grammar's defining fields are exactly these integers — grounding:
  `SpeciesSyntax.shape`/`letter_det` typing plus H4-M1 §8.3's table).
  Definitional at the grammar, but the catalogue-layer letter-assignment
  bookkeeping (which fields the β-leg letters carry at the pack's verdict
  rows) is NOT walked in this note — named, never absorbed.
- **[M1-STATUS]** — H4-M1 is consumed at its on-file status: (R1)–(R3)
  PROVED over W(F_q) at its §0.4 perimeter, gate N-T4 run and passed; its
  hostile passes (×2) ride Wave 1's gate and are NOT asserted here (the
  M4 precedent for M2, applied to M1).

Everything below §1 is proved OUTRIGHT given these rows. No other
conditionality enters; in particular NOTHING from H4-M2 (no dictionary, no
same-keys transport, no gcd condition) and nothing from the counting layer
(Theorem C(a)/(b), PIN-WELLDEF, (ZC) — not consumed, matching M1 §7's
NOT-CONSUMED verification).
-/

import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.Scaffold.HDischarge.H4.Kernel

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H4.RouteB

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-!
## §2. The symbolic skeleton, and Lemma S (the Lemma-1 leverage)

### 2.1 Def SYM — the letter's catalogue slot tree and its exponent

Fix an integer datum D = (d; (e_j, h_j, g_j)_{j≤k}; stage index k+1;
height γ), all entries integers with e_j, g_j, d ≥ 1, gcd(e_j, h_j) = 1
(Bézout companions t_j exist and are functions of the datum). Define, by
the D.9(a) recursion READ AS A DEFINITION (this is verbatim the corpus's
typed skeleton — `wSet`, `anchorSlot`, `slotHeight`, `attainIdx`,
`SlotTree`, `SlotTree.dimOf` of `Scaffold/HDischarge/H4/Defs.lean`,
consumed by import):

- symbolic weight sets: W₁(D) := e₁·ℤ≥0;
  W_{j+1}(D) := e_{j+1}·⋃_{0≤i<e_j g_j} (W_j(D) + i·h_j);
- at a node of stage j+1 and height γ′: the stretch γ′* (the D.0 scale
  conversion — at coefficient spaces γ′* = γ′/e_{j+1}, at the top space
  the current scale; M1 §5.3's walked bookkeeping), the anchor slot
  j₀ ≡ t_j·γ′* (mod e_j), the slot heights γ_i := γ′* − (j₀ + i·e_j)·h_j
  (0 ≤ i < g_j), and the attainable index set
  I(γ′) := {i < g_j : γ_i ∈ W_j(D)};
- the SLOT TREE T(D): the node (j+1, γ′) has children {(j, γ_i) : i ∈
  I(γ′)} carrying the stage-truncated datum; stage-1 nodes (1, e₁v) are
  leaves. The tree is finite (stage index strictly drops; ≤ g_j children
  per node) — the corpus `SlotTree` shape;
- **a_sym(D) := (number of leaves of T(D)) · d** — in `SlotTree` terms,
  `T(D).dimOf d`. For a letter ℓ with datum data(ℓ) ([LET-DATA]):
  a_sym(ℓ) := a_sym(data(ℓ)).

**p-freeness, displayed:** every clause above consumes only the integers
of D (Bézout arithmetic, lattice membership, finite unions). No p, q, δ,
residue field, or cardinality appears — the (EQ-1) slice fact, M1 §8.3.
The same definition at the SAME datum serves every base; that is the whole
point.

### 2.2 Lemma S — the realized skeleton IS the symbolic skeleton

**Lemma S.** Let 𝒯 be a §B2-DEF recipe tower over W(F_q) (any finite F_q)
whose stage data conform to the datum D (base degree d, tuples
(e_j, h_j, g_j)). Then for every j ≤ k the REALIZED weight set satisfies
𝒲_j^{(q)}(𝒯) = W_j(D); at every node the realized stretch, anchor slot,
slot heights, and attainable index set coincide with Def SYM's; and the
realized slot tree below any position of 𝒯 equals the symbolic tree T(D)
at the corresponding node of the datum.

*Proof.* (R3) over W(F_q) — PROVED, M1 §6.1–6.2 — states that the
realized weight sets satisfy EXACTLY the displayed integer recursion with
base clause 𝒲₁^{(q)} = e₁·ℤ≥0. W_j(D) is DEFINED by that recursion with
the same base; equality follows by induction on j (two sequences
satisfying the same first-order recurrence from the same seed). The
per-node items are the same Bézout/stride arithmetic in the shared
integers (γ′, e_j, h_j, t_j) on both sides — M14 Lemma 1(b)'s computation
verbatim ("γ* uses only e_{j+1}; t_j is the mod-e_j inverse of h_j,
shared; j₀ and each γ_i are arithmetic in (γ*, t_j, e_j, h_j)") — and
I^{(q)}(γ′) = I(γ′) then follows from the weight-set equality. The tree
equality is induction on the stage index: both trees' children at a node
are indexed by the SAME attainable set at the SAME slot heights, and the
stage-truncation of a conforming tower conforms to the stage-truncated
datum. ∎

*Status: (c) claimed new in this packaging, but it is exactly M14 Lemma 1
(unconditional, on file) with the second tower replaced by the symbolic
recursion itself — the "Lemma-1 leverage" the blueprint names (M1 §8.2:
"the two-sided comparison consumes NOTHING further from this pass — in
particular NO cross-base dictionary"). One side is a realization, the
other is pure syntax; nothing cross-base is compared.*

### 2.3 What Lemma S does NOT need, displayed

No second realization. No matched ℤ_p-side tower. No letter persistence.
No (R4). The datum D enters as the letter's own integer data ([LET-DATA]);
the tower enters as the run's own product ([RUN-PROD]). Contrast M14
Lemma 1's USE in M14's Theorem, where the two towers were the ℤ_p-side and
the O_δ-side realizations and (R4) supplied the matched data — that
matching is precisely what Route B deletes.

## §3. Lemma B — the base dimension, intrinsically

**Lemma B.** At a base-stage position (1, e₁v) of a presented tower over
W(F_q), q = p^δ: 𝔸₁^{(q)}(e₁v) = F₁ = F_q[x]/(φ̄), so

  dim_{F_q} 𝔸₁^{(q)}(e₁v) = d   and   dim_{F_p} 𝔸₁^{(q)}(e₁v) = δ·d.

*Proof.* The base clause 𝔸₁^{(q)}(e₁v) = F₁ is M1 §5.5 (PROVED over
W(F_q): the x-dependent realizer family p^v·B with the θ-basis reading
onto F₁ — Lemma ONTO; the finding-4 corrected mechanism). [F₁ : F_q] = d
because φ̄ is irreducible of degree d over F_q — the presented tower's OWN
base datum (M1 §0.2/§0.3), which is the letter's d by [LET-DATA]. Then
dim_{F_p} = [F_q : F_p]·dim_{F_q} = δ·d. ∎

INTRINSIC READING, displayed: M14's Lemma 3 obtained the same numbers from
(R4)'s MATCHED base degree ("using (R4)'s matched base degree
[F₁^{(δ)} : F_q] = d"). Here d is the realized tower's own datum — nothing
is matched against a ℤ_p-side object. This is the first of the four (R4)
consumption sites deleted (§5.1's table).

## §4. THE THEOREM — the intrinsic per-base ledger law (RB)

**Theorem (Route B).** Assume rows [RUN-PROD], [LET-DATA], [M1-STATUS]
(§1.3). For every prime p, every δ ≥ 1, and every position y the O_δ
classifier realizes:

  a_δ(y) = δ · a_sym(letter_δ(y)).

*Proof.* Write q := p^δ. By [RUN-PROD], y rides a presented tower 𝒯 over
W(F_q); by [LET-DATA], 𝒯's stage data conform to D := data(letter_δ(y)).

CLAIM (induction on the stage index j): at every node (j+1, γ′) of the
realized recursion below or at y — and at every stage-1 node — 

  dim_{F_q} 𝔸^{(q)}(node) = (number of leaves of T(D) below the
  corresponding symbolic node) · d.

Base (stage 1, height e₁v): Lemma B gives dim_{F_q} = d; the symbolic node
is a leaf (count 1). ✓

Step (node (j+1, γ′)): let I(γ′) be the attainable set — by Lemma S the
realized and symbolic sets coincide, at coinciding slot heights γ_i.

- If I(γ′) = ∅: the realized alphabet is {0} (M1 §5.4's product display
  over the empty attainable set; the forced unit u(γ′) multiplies {0} to
  {0}), so dim_{F_q} = 0; the symbolic node has no children and no leaves
  below it, count 0. ✓
- If I(γ′) ≠ ∅: (R2)'s product display over W(F_q) — PROVED, M1 §5.4 —
  gives |𝔸^{(q)}(j+1, γ′)| = Π_{i∈I(γ′)} |𝔸_j^{(q)}(γ_i)|, with the
  injectivity mechanism riding (1, z̄, …, z̄^{g_j−1}) an F_j-basis of
  F_{j+1}. THE MECHANISM'S IRREDUCIBILITY INPUT IS INTRINSIC: ψ_j
  irreducible of degree g_j OVER THE REBUILT F_j is the presented tower's
  own increment datum (M1 §0.3; the mutatis-mutandis rule bites exactly
  here, M1 §5.4) — NOT a persistence statement about a matched ℤ_p-side
  residual. By Lemma STAB (M1 §5.4, PROVED) every alphabet in sight is an
  F_q-subspace of its tower field, so every cardinality is an exact
  q-power and the product display reads at F_q-dimensions:

    dim_{F_q} 𝔸^{(q)}(j+1, γ′) = Σ_{i∈I(γ′)} dim_{F_q} 𝔸_j^{(q)}(γ_i).

  Each slot node (j, γ_i) is a stage-j node of the SAME tower 𝒯 (its
  stage-truncation conforms to the truncated datum), so the induction
  hypothesis applies to it — INTRINSICALLY: no stability of any
  sub-position is invoked, because the comparison is never against another
  base. Summing the leaf counts of the symbolic children (Lemma S: same
  index set, same heights) closes the step. ✓

Top: at y itself (the top-space read rides the same recursion at the
current scale — M1 §5.3/§5.4 "likewise at the top", exactly as in M14's
Theorem "including x itself at the top space"), the CLAIM gives
dim_{F_q} 𝔸^{(q)}(y) = (leaves of T(D))·d = a_sym(letter_δ(y)) (Def SYM).
By Lemma STAB, |𝔸^{(q)}(y)| = q^{dim_{F_q}} = p^{δ·dim_{F_q}}, and the
ledger's F_p-normalization (a_δ = log_p |𝔸|, the `card_eq` reading; M1
§5.4's "M14's F_p-normalization is a = f·a_q") gives

  a_δ(y) = δ · dim_{F_q} 𝔸^{(q)}(y) = δ · a_sym(letter_δ(y)). ∎

**Corollary DIV (stability-free divisibility).** δ | a_δ(y) at EVERY
realized position. (Also directly: Lemma STAB's F_q-subspace property —
consistent with M14's Corollary, which derived δ | a_δ from (R1)–(R2)
alone; the Theorem sharpens the quotient to the p-free value a_sym(ℓ).)

**Corollary ROOT (the q = p instance).** At δ = 1 the Theorem reads
a₁(y) = a_sym(letter_1(y)) at every ℤ_p-realized position — the per-letter
symbolic-exponent conformance shape at base ℤ_p. CONSISTENCY DISPLAY: the
Route-B text pins a_sym by "the ℤ_p-side per-letter law is Theorem C's
accepted conformance at q = p"; Def SYM's a_sym is computed by the SAME
D.3(e)/D.9(a) skeleton recursion that the accepted base-side displays ride,
so at q = p the two exponent assignments agree at every realized letter.
This note does NOT consume Theorem C (counting layer untouched); Corollary
ROOT re-derives the δ = 1 conformance from M1's q = p instance, and the
identification with the catalogue's exponent slot rides [LET-DATA] only.

REMARK (where each M14 input went): M14's Theorem consumed (R1)–(R4) with
the induction running over the δ-STABLE PREFIX. Here (R1) enters through
M1 §§1–4 (as the substrate of (R2)/(R3)'s proofs), (R2)/(R3) enter as
displayed, and (R4) enters NOWHERE — §5.1 itemizes the deletion.
-/

/-!
## §4.L. The typed shadow (note-internal; NOT the H4-F5 face)

The note's [M]-rows and the Theorem's arithmetic spine, typed. FENCE,
binding: `SymConf` is note-internal PROOF vocabulary — its rows are
[RUN-PROD]+[LET-DATA]+the M1-proved conformances in typed form, to be
discharged by the eventual H4-F5/H4-F2/H4-F6 instances AFTER the ROOT
re-scope; consumers keep reading `UBXbStmt`/`K3deltaStmt` (H4-L7/L8) until
then. The `letter` field is ABSTRACT (type `L`), per M4 §3.2's carrier
caution: it is the classifier's OWN realized letter, NOT hard-wired to
`AlphabetData.posLetter` (whose §7.2 off-domain sentinel is exactly what
the intrinsic law must NOT read at split prefixes).
-/

/-- Note-internal Route-B conformance interface (NOT the fenced H4-F5
face; see §4.L fence). Rows, with their math discharge sites:
`dim_conf` — the realized exponent reads off the realized slot tree
((R2) product display + Lemma STAB at dimensions, M1 §5.4, under
[RUN-PROD]); `tree_sym` — the realized tree IS the letter's symbolic tree
(Lemma S, §2.2, under [LET-DATA]); `dbase_sym` — the realized base
dimension is δ·(the letter's own d) (Lemma B, §3). All three are
REALIZED-CONDITIONED (`x ∈ RL.realized δ`) — Route B's quantifier, the
H4-F5 shape `∀ δ, ∀ x ∈ realized δ`, never all positions. -/
structure SymConf {Sp : SpeciesSyntax} (AD : AlphabetData p Sp)
    (RL : RealizedLedger p AD) where
  Letter : Type
  letter : ℕ+ → AD.Pos → Letter
  symTree : Letter → SlotTree
  symDbase : Letter → ℕ
  tree : ℕ+ → AD.Pos → SlotTree
  dbase : ℕ+ → AD.Pos → ℕ
  dim_conf : ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ →
    AD.aDim δ x = (tree δ x).dimOf (dbase δ x)
  tree_sym : ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ →
    tree δ x = symTree (letter δ x)
  dbase_sym : ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ →
    dbase δ x = (δ : ℕ) * symDbase (letter δ x)

/-- The letter's p-free symbolic exponent a_sym (Def SYM, §2.1): the
letter's catalogue slot tree read at its own base degree. (`p` implicit
here so that `S.aSym l` reads as the note's a_sym(ℓ).) -/
def SymConf.aSym {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} {RL : RealizedLedger p AD}
    (S : SymConf p AD RL) (l : S.Letter) : ℕ :=
  (S.symTree l).dimOf (S.symDbase l)

/-- **THE THEOREM's typed shadow (RB):** the intrinsic per-base ledger law
`a_δ(y) = δ·a_sym(letter_δ(y))` at every realized position — stability-free.
Arithmetic spine: `SlotTree.dimOf_scale` (H4-L3), exactly M14 Theorem (ii)'s
factor-δ propagation, now run against the SYMBOLIC tree. -/
theorem intrinsic_law {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {RL : RealizedLedger p AD} (S : SymConf p AD RL) :
    ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ →
      AD.aDim δ x = (δ : ℕ) * S.aSym (S.letter δ x) := by
  intro δ x hx
  rw [S.dim_conf δ x hx, S.tree_sym δ x hx, S.dbase_sym δ x hx,
    SlotTree.dimOf_scale]
  rfl

/-- The per-pool exponent read Step 18 K3-c consumes (M4 §5.4's consumer
shape), at the typed faces: every realized δ > 1 pool reads
`a_δ = δ·a_sym` at ITS OWN realized letter. No stability, no dictionary. -/
theorem pool_exponent_read {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {RL : RealizedLedger p AD} (S : SymConf p AD RL) :
    ∀ P : RL.Pool, AD.aDim (RL.poolIdx P) (RL.poolPos P) =
      ((RL.poolIdx P) : ℕ) * S.aSym (S.letter (RL.poolIdx P) (RL.poolPos P)) :=
  fun P => intrinsic_law p S (RL.poolIdx P) (RL.poolPos P) (RL.pool_realized P)

/-- Corollary DIV's typed shadow: δ divides a_δ at every realized position
(N-K3 sealed prediction P2's shape). -/
theorem intrinsic_dvd {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {RL : RealizedLedger p AD} (S : SymConf p AD RL) :
    ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ → (δ : ℕ) ∣ AD.aDim δ x :=
  fun δ x hx => ⟨S.aSym (S.letter δ x), intrinsic_law p S δ x hx⟩

/-- Corollary ROOT's typed shadow: the δ = 1 instance is the base-ℤ_p
per-letter conformance a₁ = a_sym(letter₁). -/
theorem root_instance {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {RL : RealizedLedger p AD} (S : SymConf p AD RL) :
    ∀ x : AD.Pos, x ∈ RL.realized 1 → AD.aDim 1 x = S.aSym (S.letter 1 x) := by
  intro x hx
  simpa using intrinsic_law p S 1 x hx

/-- The M4 §5.3 branch-(iii) escalation logic, typed: at a position
realized at BOTH bases whose realized letter PERSISTS, the intrinsic law
specializes to (EQ-2)(ii)'s read a_δ = δ·a₁ — "there the intrinsic law is
(EQ-2)'s restatement". Letter persistence is a HYPOTHESIS here (`hl`),
never derived: the intrinsic law does not supply it (§5.3). -/
theorem eq2ii_of_letter_match {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    {RL : RealizedLedger p AD} (S : SymConf p AD RL) {δ : ℕ+} {x : AD.Pos}
    (hδ : x ∈ RL.realized δ) (h1 : x ∈ RL.realized 1)
    (hl : S.letter δ x = S.letter 1 x) :
    AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x := by
  rw [intrinsic_law p S δ x hδ, root_instance p S x h1, hl]

/-- The §5.2 worked F₉-shape instance's arithmetic shadow (decide-checked):
the intrinsic read 2 = 2·1 holds at the branch letter while the
stability-law read 2 = 2·2 fails — the scope mismatch, in numbers. NOT a
realization claim (the realization walk is §5.2's prose). -/
theorem f9_shape_contrast : (2 : ℕ) = 2 * 1 ∧ (2 : ℕ) ≠ 2 * 2 := by decide

/-!
## §5. Stability: what was deleted, what the law does NOT give, what travels

### 5.1 The four (R4)-consumption sites of M14's Theorem, deleted one by one

| M14 consumption site (verbatim anchor) | what (R4)/stability supplied | the intrinsic replacement (this note) |
|---|---|---|
| Theorem step: "each slot position … IS a stage-k position of the same prefix, hence δ-stable under (R4)'s prefix reading, so the induction hypothesis applies" | stability of every SUB-position (M14 §7.2's constraint) | the induction runs inside the ONE tower 𝒯; sub-positions are its own stage-truncations; no stability predicate exists in the statement (§4 CLAIM step) |
| Theorem step: "(R2) product display; its mechanism consumes ψ_k^{(δ)} irreducible of degree g_k over F_k^{(δ)} — exactly (R4)'s letter persistence" | irreducibility of the re-based residual AT THE MATCHED degree | ψ_j irreducible over the REBUILT F_j is the tower's OWN increment datum (M1 §0.3), read intrinsically (§4 step) |
| Theorem step: "Lemma 1(b): I^{(δ)}(γ) = I(γ)" (two realizations, matched data) | equal stage tuples across the base change | Lemma S: realization vs the SYMBOLIC recursion at the letter's own data — one realization only (§2.2) |
| Lemma 3: "using (R4)'s matched base degree [F₁^{(δ)} : F_q] = d" | the matched base degree | d is the letter's own datum (Lemma B, §3) |

Residue: (R4) and the (a6)/(EQ-1) dictionary appear NOWHERE above. The
blueprint's Route-B promise — "NO cross-base dictionary and no δ-stability
hypothesis remain" — is DISCHARGED as stated.

### 5.2 The worked F₉-shape instance: intrinsic-exact, stability-broken

M14 §6's out-of-domain instance, re-read intrinsically. p = 3, δ = 2,
O_δ = W(F₉); tower base key x (d = 1), read (e₁, h₁) = (2, 1), ℤ₃-side
residual ψ = z² + 1 (irreducible over F₃, g = 2). Over the REBUILT base
field F₉, z² + 1 SPLITS into two linear factors (M14 T3's recorded
verification), so the O_δ classifier does NOT realize the g = 2 letter: it
realizes, per branch, a g = 1 species (linear residual z − c) — a GENUINE
letter of its own run ([LET-DATA]'s reading; the §1.2 carrier caution
live: a §7.2 `posLetter` would return the off-domain sentinel here).
Recorded numbers (M14 T3): per-branch continuation field F₉, per-branch
full-height alphabet F₉, a_branch = 2.

- INTRINSIC READ (this note's Theorem): the branch letter's datum is
  (d = 1; (e, h, g) = (2, 1, 1); full height) — its symbolic tree has ONE
  leaf, a_sym = 1·1 = 1. Predicted a_δ = δ·a_sym = 2·1 = 2 = a_branch. ✓
  EXACT — the instance is IN-DOMAIN for (RB).
- STABILITY READ ((EQ-2)/the current rows): the letter did not persist
  (g: 2 → two branches at g = 1), `Stable` FAILS, and indeed
  a_branch = 2 ≠ δ·a₁ = 2·2 = 4 (M14's record). The instance is
  out-of-domain for the stability-quantified law — exactly as M14 §6 and
  M4 §2.3 record.

(`f9_shape_contrast` is the arithmetic shadow.) So ONE instance exhibits
BOTH halves of the route call: the intrinsic law reads split-realized
positions exactly where the stability law goes silent (the M4 §5.4 "scope
mismatch dissolved at the source"), AND a realized position can satisfy
(RB) while failing `Stable` — hence:

### 5.3 NOTHING IS DISCHARGED AS THE ROWS STAND (finding 3, honored)

Blueprint §3.2, verbatim, binding on this unit: "Route B does NOT
discharge the rows AS STATED — the intrinsic law does not imply that
realized positions are δ-stable, and the authoritative (UB-X)(b)/(K3-δ)
texts quantify over stability. […] Until the ROOT owner lands that
re-scope, nothing is discharged by a Route-B proof; the proof + re-scope
brief travel together (H4-M5 + H4-M7)." §5.2's instance is the concrete
witness of the non-implication direction (realized + (RB)-exact + not
`Stable` — at the F₉ shape; whether such positions occur in the n = 3
pack's REALIZED pools is N-K3's empirical question, not asserted here).
Deliverable routing, per M4 §6: this note = the proof; H4-M7 = the
re-scope brief (row-text substitution, withdrawal display, clause-(R)
re-attribution, the Step-16/Step-18 consumer-need walk at exact texts);
the ROOT owner = the authorization. H4-F5 stays fenced; H4-L7/L8 stay the
CURRENT typed rows; nothing here re-points any consumer.

## §6. N-K3 SEALED PREDICTIONS (this unit's gate item; sealed PRE-RUN)

Spec (blueprint §N, verbatim head): "enumerate the n = 3 pack's
verdict-row β-legs' δ > 1 pools; per pool, check the realized species
against Lemma 4's gcd criterion and against Route B's intrinsic exponent
law (a_δ = δ·a_sym at the realized letter)." ON-FILE STATUS re-verified at
composition (2026-08-01): NO N-K3 run artifact exists
(`verification/openmath/` has no N-K3 script or results; M4 §5.3 found the
same). Per the standing falsifier discipline the predictions are SEALED
here, before any run:

- **P1 (the law — the falsifier of this note).** At EVERY realized δ > 1
  pool: a_δ(pool position) = δ·a_sym(realized letter) EXACTLY, δ = the
  pool's index, a_sym computed by Def SYM on the realized letter's own
  datum (per-branch letters at split-realized pools, per §5.2's reading —
  the prediction is NOT "δ·a_sym(the ℤ_p letter)").
- **P2 (divisibility, the cheap read).** δ | a_δ at every realized pool
  (Corollary DIV; implied by P1, checkable without computing a_sym).
- **P3 (agnostic clause, displayed).** This note makes NO prediction on
  Lemma 4's gcd(m, δ) criterion at the realized pools: BOTH outcomes are
  consistent with everything proved here (the gcd criterion is
  dictionary-side, H4-M2/Route-A material; a non-coprime realized pool
  would kill Route A — M4 §5.3 branch (i) — and touch nothing in §§2–4).
- **P4 (stable-pool consistency).** At any pool position additionally
  certified letter-persistent and realized at δ = 1: a_δ = δ·a₁
  (`eq2ii_of_letter_match`'s shape — the (EQ-2) read).

VIOLATION HANDLING, pre-committed (M4 §5.3's precedence order, quoted:
check (iii) first, then (i), then (ii)): a P1/P2 violation fires M4's
branch (iii) — "Route B is REFUTED AS STATED, and the adjudication
RE-OPENS — with NO automatic fallback to Route A", escalation scoped by
the violating position's stability exactly as recorded there; since §§2–4
rest on M1's proven walk, the fault would sit in [RUN-PROD]/[LET-DATA] or
in M1's walk itself — stop-the-line, re-adjudicate, nothing absorbed. A
gcd-only violation (P3's non-prediction) fires branch (i): Route A dead,
this note untouched. A clean pass is n = 3 empirical support only — the
Theorem's warrant remains §§2–4's derivation, not the run.

## §7. Consumption map, gate record, declaration list

CONSUMED (each at its displayed site): H4-M1 at its ON-FILE status
([M1-STATUS], §1.3) — §0.2/0.3 (presentation, Lemma ONTO), §5.3–5.5
((R2): (ii.2)^(q), product display + injectivity mechanism, base clause),
§5.4 (Lemma STAB, F_p/F_q normalization), §6 ((R3)), §8.2 (δ-instances +
Lemma-1 leverage), §8.3 ((EQ-1) slice verdict), §0.4 (perimeter fence);
M14 attempt (on file) — Lemma 1 (unconditional; its (b) arithmetic),
Lemma 3 + Theorem (the induction pattern, re-run intrinsically §4; the
(R4) sites deleted per §5.1), Corollary (δ | a_δ consistency), §6 + T3
(the F₉ worked instance's recorded numbers), §7.2 (carrier constraint,
honored via the abstract `letter`); H4-M4 — §5.5 (ROUTE B selected), §5.3
(branch table, quoted §6), §3.2 (carrier caution, quoted §1.2), §1 (K3-c
row text); blueprint §3.2 Route-B text (verbatim §1.1) + §N (N-K3 spec);
Lean corpus BY IMPORT — `MovesRBase.Defs` carriers,
`Scaffold/HDischarge/H4/Defs+Kernel` (`SlotTree`, `dimOf`, `dimOf_scale`,
`RealizedLedger`; H4-L1/L3/L7). NOT CONSUMED: H4-M2 (no dictionary, no
(R4), no gcd anywhere in §§2–4; Lemma 4 named only inside §6's P3
non-prediction); `AlphabetData.Stable` (appears in NO hypothesis or proof
— only in §5's non-implication discussion); the counting layer (Theorem
C(a)/(b), PIN-WELLDEF, (ZC)); REL.2(e) internals (the pools' presentation
is consumed as typed at `RealizedLedger`, nothing re-derived); any
Route-A artifact.

GATES: (1) `lake env lean notes/openmath/H4M5_k3delta_attempt.md` — GREEN,
zero sorry (re-run after every fold edit). (2) Hostile pass ×2 (fresh
contexts, one Codex) — ledger below. (3) N-K3 sealed predictions — §6
(sealed pre-run; the run itself is the numerics fleet's, not this unit's).

DECLARATION LIST (all in `LeanUrat.Scaffold.HDischarge.H4.RouteB`, this
file, zero sorry): `SymConf` (structure; the note's [M]-rows as NAMED
fields — never axioms, never discharged by fiat), `SymConf.aSym` (def),
`intrinsic_law`, `pool_exponent_read`, `intrinsic_dvd`, `root_instance`,
`eq2ii_of_letter_match`, `f9_shape_contrast`. Every theorem proved
outright (no sorry, no new axiom); the [M]-semantic content stays in NAMED
hypothesis position (`SymConf`'s rows + the §1.3 prose rows), never
discharged by fiat. NOT declared: any H4-F5-shaped consumer face (§4.L
fence).

AXIOM FOOTPRINT (external `#print axioms` run, 2026-08-01): Lean-core only
— `intrinsic_law`, `pool_exponent_read`, `intrinsic_dvd`, `root_instance`,
`eq2ii_of_letter_match` each at {propext, Classical.choice, Quot.sound};
`f9_shape_contrast` axiom-free; `SymConf`/`aSym` defs.

## HOSTILE-PASS LEDGER (gate: ×2, fresh contexts, one Codex)

- Pass 1 (Codex, fresh context, quote-and-classify charge): recorded below
  after the run.
- Pass 2 (fresh context, on the folded text): recorded below after pass
  1's repairs, if any.
-/

end LeanUrat.Scaffold.HDischarge.H4.RouteB
