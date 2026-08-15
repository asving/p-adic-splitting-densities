# CHAPTER D — GAUGE + CERTIFICATE T-CHAIN (T1 cocycle, T3 telescope, T4 certificate witness, T5 w-frame)

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **D = GAUGE + CERTIFICATE
T-CHAIN** (notes `T1, T3, T4, T5`; **181 DAG nodes** = 55 + 36 + 45 + 45, exactly the four specs'
unit counts; consumer-first order position third, between the σ-ladder master `E` and the tower
grammar `C`).
**Sources transcribed:** `spec/EFF-T1.md` (55 units, MERGED from 3 shards — cite contiguous IDs
per GC-12), `spec/EFF-T3.md` (36 units), `spec/EFF-T4.md` (45 units), `spec/EFF-T5.md` (45
units). All four are **ACCEPTED T-units: GC-10 transcription grade governs the whole chapter** —
the EFF canonical statements are the spec; deviations only via dated AMENDMENT blocks.
**Supplier chapters consumed:** **A** (the landed Lean kernel), **B** (committed nodes, by node
ID — the level-1 development/height API), **C** (NOT yet frozen — every GENTOW*/HETOW-sourced
supply enters as a GC-13 placeholder `EFF.<NOTE>.<nn> [supplied-by: chapter C]`, never a guessed
node ID), **H** (nothing — no chapter-H node is consumed; the H §8 slot layer is B/E's entry
point, not D's).
**Special owner duty:** this chapter authors **THE ϑ FOUR-WAY ORIENTATION TABLE** (GC-14; the
canonical copy, anchor **`D-THETA-TABLE`**, node D.06). C, E and F cite the anchor; no chapter
restates the content.
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle).
**Authored:** 2026-08-15, chapter-D composer (Fable arm, parallel-author fleet per
CONVENTIONS Part V). **CODEX CROSS-READ OWED.**

---

## 0. How to read this chapter

### 0.1 The five standing environments

Environment tags are chapter-prefixed per GC-6.3; the bare `ENV-A/B/C` vocabulary is retired.
Environments bind **per node** (GC-6.4), never per section.

**ENV-D1 — the arithmetic arena** (the level-1 exponent calculus: `i(k)`, `a(k)`, `wrap`,
`q(k)`, `W(t)`, the threshold arithmetic `Θ_j = (μ₂−j)E₂ + δ`). No `O`, no polynomials:

```lean
import Uniformity
namespace Uniformity.Density.Gauge
```

**ENV-D2 — the abstract cocycle arena** (a bare commutative group: every normalizer-section,
cocycle, telescope, bracket and coboundary identity is group algebra valid with no valuation in
sight):

```lean
import Uniformity
namespace Uniformity.Density.Gauge
variable {G : Type*} [CommGroup G]
```

**ENV-D3 — the residue-field arena** (the letter field `K` = the corpus's `K_i`; the ϑ/Θ
residue layer, the dictionary, the B-law, the w-twist). No finiteness — nothing in this chapter
counts:

```lean
import Uniformity
namespace Uniformity.Density.Gauge
open Polynomial
variable {K : Type*} [Field K]
```

**ENV-D4 — the concrete level-1 arena over the bundle** (T1's C5/C6 exact-lift layer; consumes
chapter B's development/height API). Alias: **ENV-D4 = CHAP-B's ENV-A′, verbatim** (the
complete-DVR bundle with `π` promoted to the explicit hypothesis `(hπ : Irreducible π)`; the
stub agent copies the block byte-exactly from CHAP-B §0.1):

```lean
import Uniformity
namespace Uniformity.Density.Leaf   -- theorems about B-owned objects live in B's namespace? NO —
-- see the ⚠ below: chapter D READS `Uniformity.Density.Leaf`, never extends it. D's own
-- declarations stay in `Uniformity.Density.Gauge`; ENV-D4 nodes import B's names qualified.
namespace Uniformity.Density.Gauge
open IsLocalRing Polynomial
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
```

⚠ Per GC-6.2, chapter D's sub-namespace is **`Uniformity.Density.Gauge`** (assigned,
collision-free); another chapter's sub-namespace (B's `.Leaf`, G's `.Menu`, H's `.Induction`)
is READ, never extended. New theorems about landed kernel objects (none are currently planned
in this chapter) would live directly in `Uniformity.Density`.

**ENV-D5 — the gate arena** (concrete finite fields for the letter tables: `ZMod 3`, `ZMod 5`,
`GaloisField 2 2`; plus `ℤ ×ₗ ℤ`-monomial arenas). Concrete per gate node; no `variable` block.

### 0.2 File layout and naming

* One Lean file per node: `leanfinal/Uniformity/ChapD/D<nn>.lean`, module
  `Uniformity.ChapD.D<nn>` (the LANDED convention per GC-6.1; micro-nodes suffix a letter).
* Chapter roll-up `leanfinal/Uniformity/ChapD.lean` imports every node module in this file's
  topological order; `Uniformity.lean` gains one line. `ChapD.lean` imports `Uniformity.ChapB`
  (the §4 consumption) and nothing from C/E/F/H.
* One PUBLIC declaration per node (GC-6.5); private helpers below it in the same file; a
  reusable helper triggers RE-PLAN, never a silent second public name.

### 0.3 Names that already exist and must not be redefined

**From `Uniformity.Density` (the landed kernel, chapter A)** — consumed by name where cited:
`FactorizationType`, `typeOf`, `monicFactors`, `residueCard`, `DecidedAt`, `proj`, `Coeff`,
`Res`, plus the `addVal` cluster (`pow_dvd_iff_le_addVal`, `addVal_eq_of_dvd_not_dvd`,
`exists_unit_mul_pow_of_addVal_eq`). This chapter defines **no** σ-valued output and touches no
density object — its terminal supply is algebraic interfaces (GC-4 note: the chapter has no
dictionary obligation because it emits no σ; F consumes `stageSigma` outputs from C/E, not D).

**From chapter B (committed blueprint, consumed by node ID per GC-13(b)):** B.06 (`dev` +
`dev_unique`), B.08 (`le_gaussVal_iff`), B.15 (`dev_X`/`npHgt_X`), B.22/B.23 (`resField`, its
field/finite instances, `finrank_resField`) — the §4 nodes name their exact consumption. The
quantities T1 calls `dv_1` on coefficient polynomials are B's weighted Gauss valuation at
`φ = X` with weight pair `(u, ℓ) = (h, e₁)`; the §4 nodes state the identification explicitly
rather than re-deriving a valuation layer.

**Two near-miss names to keep apart.** (i) T1's two-index `ϑ_{i,s}` and GENTOW2's single-index
`ϑ(t)` are **mutually inverse** conventions for the same letter — the entire content of node
D.06; in Lean they get two distinct names (`vartheta` and `varthetaG2`) and one lemma relating
them, and no consumer may alias one to the other silently. (ii) T3's `χ` (pointwise section
ratio, ONE argument) is deliberately not called `τ` (T1's TWO-argument cocycle) — the spec
itself renames to avoid the collision (`EFF.T3.12`); the Lean names are `chi` and `tau`.

### 0.4 The chapter's mathematical spine, in one page

The T-chain is the corpus's **gauge algebra**: the bookkeeping that converts between the three
residual readings of a corrected key (multiplicative, coherent, canonical) and transports
factorization data across normalizer conventions. Its content splits into **four layers of
completely different Lean character**, and that split *is* this chapter's architecture:

| layer | corpus content | Lean character | sections |
|---|---|---|---|
| **arithmetic** | the level-1 exponent calculus (`i(k)`, `wrap`, `q(k)`, `W(t)`, C5-carry), the T4 thresholds | `ℕ`/`ℤ` statements; provable outright (`omega`/`decide`) | §4 (head), §7 (head) |
| **group algebra** | the normalizer cocycle `τ`, the telescope `ϑ`/`Θ`, the descending bracket, the section-ratio coboundary, the comparison law | statements in a bare `CommGroup`; provable outright (`group`) | §3, §6 |
| **field/polynomial algebra** | the dictionary, the B-law shape, the three reads, the w-twist and its factorization transport, C4-origin/support, C6 lifts | statements over `[Field K]` / the bundle `O` from explicit hypothesis fields; provable from landed API + chapter B | §4 (tail), §5, §6, §8 |
| **interface** | the read bundle (five sitewise clauses), (FLOOR), BR1–BR5, `[GENTOW5-W(i)]`, `𝒲_{≤i}`, `(H-VARTHETA-RES)_i`, the absorption records A1–A7 | **NOT provable at transcription grade** — the corpus carries these as sitewise hypotheses/external suppliers; they become structure fields and named `Prop` carriers (the CHAP-H `StageInterface` lesson) | §5, §6, §7, §9 |

**The organising insight (and DECISION D-1's licence).** Every identity in the T-chain's
group-algebra layer is an identity between elements *constructed from a normalizer section*
`n : ℤ → G` with `n 0 = 1` — no valuation, no residue, no tower is consumed by the algebra
itself. The residue map enters only through images of **value-zero** combinations, and on those
the corpus's own instances (level 1: `η`-powers of `x^{e₁}/π^h`; level 2: GENTOW2's γ-calculus
letter group `⟨γ₁, γ₂⟩` with `res γ₁ = z₁`, `res γ₂ = z₂` — `EFF.GENTOW2.42`) realize `res` as
a **group homomorphism into `Kˣ`**. Chapter D therefore proves the algebra once, abstractly
(§3), and carries the residue interface as the structure `GaugeArena` (D.07) whose
instantiation at depth `i ≥ 3` is exactly the `(H-VARTHETA-RES)_i` conditionality — see
DECISION D-1 (honesty item D-H3) for the faithfulness discussion.

What the chapter proves outright, by headline:

| result | statement | node |
|---|---|---|
| the cocycle law | `τ(a,b)τ(a+b,c) = τ(b,c)τ(a,b+c)`, endpoints `τ(0,a) = τ(a,0) = 1` | D.02, D.03 |
| the telescope | `ϑ_0 = ϑ_1 = 1`, `ϑ_{s+1} = ϑ_s·τ(su,u)` — T3 §8.1 checks 1–2 as theorems | D.05, D.09, D.10 |
| **the ϑ orientation table** | four conventions, one object, two inversions — the GC-14 canonical copy | **D.06** |
| the level-1 gauge | `wrap ∈ {0,1}`, C2-wrap, C5-carry `q(a+b) = q(a)+q(b)+wrap(a,b)`, `ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}` | D.13–D.19 |
| C4-origin | `z^{t_Def} = z^ν ε(β)`; raw equality iff `z^ν = 1` | D.22 |
| the C6 exact lift | integrality, degree, exact height, residue, the x-free criterion | D.24, D.25 |
| the B-law from the bundle | `u(β_t) = Θ_i(t)·w_i^{f_{i+1}−t}` — proved FROM the five read clauses | D.33 |
| the three reads + transport | slotwise `Γ_t Θ(t)` cancellation; `P ↦ w^{deg P}P(y/w)` transports factorizations | D.34, D.35 |
| the boundary-read telescope | `U_i(β_s) = Θ_N(s;q)·w_i^s` from BR1–BR5 — T3's central lemma | D.38 |
| the comparison/routing pair | `R(Z) = χ(H₀)·R̂(Z/δ)`; separability/factor-multiset transport | D.40, D.41 |
| the certificate laws | T4.2(a)–(d) from (FLOOR) + linearity, over the abstract certificate frame | D.50–D.53 |
| the w-frame | `WF-psi` coefficients; `𝒲_{≤i} → WF-lawᵢ`; the realized-residual cancellation | D.58, D.62, D.63 |

**Why the interface layer is thick and why that is the right call.** The T-units are ACCEPTED
precisely as *gauge algebra plus named external obligations*: T1's own A7 record says "T1 does
not prove the supplier identity itself. Thus the B-law is no longer labeled 'absorbed
verbatim'" (`EFF.T1.31`); T3's port hypotheses BR1–BR5 are "source-local residual-read
hypotheses" with the B-law explicitly excluded as a premise (`EFF.T3.11`); T4's (FLOOR) is
"assumed — with a named supplier" (`EFF.T4.13`); T5's `𝒲_{≤i}` is never discharged
("Certification of the WI companion does not discharge these conjuncts" — `EFF.T5.29`).
Formalizing hypotheses as fields is the honest transcription of hypotheses.

---

## 1. HONESTY BLOCK (read before consuming any node)

**D-H1 — transcription grade is the law of the chapter (GC-10).** All four sources are accepted
T-units; the EFF canonical statements ARE the spec. Every node's SOURCE cites its
`EFF.<NOTE>.<nn>` ID(s); no fresh mathematics enters without a dated AMENDMENT block; every
re-packaging decision (there are exactly two: D-1 below and the schema reading of T4.2(c)/(d)
in D-H7) is a DECISION block with the source text quoted and a cross-read flag. Per the GC-10
riders: trichotomies/case splits are re-derived from the notes' own displays, never from
verifier phrasing, and no false-reason-true-conclusion parenthetical is transcribed.

**D-H2 — THE ϑ-ORIENTATION TRAP IS THE TRAP (append #54; GC-14).** Two notes carry mutually
inverse conventions for the same letter and a third carries the reciprocal of one of them; a
sign error here is caught by **no battery** (append #54's own words). The canonical four-way
table is node **D.06** (anchor `D-THETA-TABLE`), transcribed from `EFF-GENTOW2.md`'s
orientation records (`.25`, `.34`, `.41`, `.42` — the `.25` table at L1065–1075 including the
L1072 GENTOW5-A1 reciprocal row) plus T1 `(C3-Theta)`/`(C3-B-law)` (`EFF.T1.14`), T3
`(T1-THETA)`/`(ABS-G2)` (`EFF.T3.04`, `.19`), and T5's closing reconciliation (source note
L991–993, carried at `EFF.GENTOW2.25`'s table row 5). **Every ϑ-touching node of this chapter
carries a one-line `ORIENTATION:` field naming its convention against D.06**; C/E/F cite the
anchor and never restate. Separately and NOT to be conflated: the **B-law direction** is
`u(β) := R_{3,β}(n̂₂(β̂))` read `FGMN = u · repo` — NOT the inverse (the r2 F3 finding,
`EFF.GENTOW2.34`'s orientation record); D.06 carries it as a separate labelled row-block.

**D-H3 — DECISION D-1: the `GaugeArena` packaging (the chapter's one structural choice).**
The corpus states the residue obligations SITEWISE (five clauses "at each consumed B-law site",
`EFF.T1.03`; ϑ-membership fenced per depth, `EFF.T1.09`). Chapter D packages the ambient
residue map as a structure field `res : V →* Kˣ` on the value-zero subgroup `V` of the arena
(D.07). **This is formally stronger than the sitewise clauses** (it asserts multiplicativity
and `Kˣ`-membership on all of `V`, not only at consumed sites). Licence, with the source
quoted: (i) at `i = 1` the consumed arena is the group `⟨x^{e₁}/π^h⟩` and
`res((x^{e₁}/π^h)^t) = η^t` — a genuine homomorphism (`EFF.T1.01`); (ii) at `i = 2` GENTOW2's
γ-calculus proves "the value-0 Laurent monomials `x^i π^a Φ′^b` form exactly the group
`⟨γ₁, γ₂⟩`" with `res(γ₁(x₀)) = z₁`, `res(γ₂(x₀)) = z₂` (`EFF.GENTOW2.42`) — again a genuine
homomorphism on the consumed arena; (iii) at `i ≥ 3` **no instance is claimed** — supplying the
structure is the Lean form of `(H-VARTHETA-RES)_i` (D.67), and the chapter's conditional nodes
carry the structure as a hypothesis exactly where the corpus carries the named hypothesis.
**The alternative** (sitewise multiplicativity hypotheses attached clause-by-clause to every
consuming node) is recorded as viable but was rejected: it multiplies every §3/§6 signature by
three to five hypothesis slots and makes the group-algebra layer unprovable as group algebra.
**FAITHFULNESS flag:** any instantiation of `GaugeArena` at depth `i ≥ 3` in a later chapter
must be checked against the sitewise scope of `(H-VARTHETA-RES)_i` — flagged for the cross-read
(§13 item 2) and for chapter I's conjunct bookkeeping (the carrier D.67/D.68 states the
correspondence).

**D-H4 — what this chapter does NOT prove, item by item.** All carried as fences/interfaces,
none as nodes:
1. **The B-law supplier identity.** "T1 does not prove `u(β_t) = Θ(t)w^{f₃−t}` and does not
   import general factor-pattern preservation into the pinned GENTOW2-B span" (`EFF.T1.31`,
   NON-IMPORTS A7). D.33 proves the B-law **from the read-bundle fields**; discharging the
   fields at `i = 2` is GENTOW2's (→ chapter C placeholder, D.42), at `i ≥ 3` it is
   `[GENTOW5-W(i)]`-conditional (D.44/D.62).
2. **Cross-face coherence, gauge uniqueness, torsor classification** — `(C7-scope)`,
   `EFF.T1.23`: "T1 organizes five named fields around one tower cocycle; it proves no
   cross-face coherence theorem … no uniqueness of the gauge". The C7 interface table
   (`EFF.T1.22`) is transcribed as prose supply documentation in §5, NOT as nodes.
3. **The surrounding tower correctness theorem** (residual factor pattern → p-adic splitting
   type): unnamed in both T1 and T3 (T1 OPEN-CALL 4, T3 OPEN-CALL 1 — "Assigning a source or
   formal interface would be invention"). Routed to chapter I / the 0d trust boundary; recorded
   at D.69, **no node**.
4. **GENTOW-6.4** is **not an instance** of the telescope (`EFF.T3.26`, `(G6-NONINSTANCE)`):
   its projection/cap laws are additive-filtration facts with an independent proof. Signed
   non-applicability in §12; no node; a fleet agent asked to derive GENTOW-6.4 from D.05/D.11
   must return the fence.
5. **Arbitrary-depth canonical-letter monomiality** — only under `(H-JA-CONJ)_i`
   (`EFF.T1.05`); **whole-polynomial support comparison** — only under `(H-JA-RES-CONJ)`
   (`EFF.T1.17`); **polygon clearance** — only under `(H-GENHN-CLEAR)` (`EFF.T1.21`); **the
   HETOW bridge** — only under `(H-HETOW-LOCAL)` (`EFF.T1.26`). Each is an explicit hypothesis
   argument of the consuming node (inline, sitewise — see D-H10's carrier ruling), never a
   proved fact.

**D-H5 — the depth fences and the non-discharge discipline.** Three stacked conditionalities,
kept apart by name everywhere:
1. `ϑ_{i,s} ∈ K_iˣ` is proved at `i ∈ {1,2}` **only** (`EFF.T1.09`, R9-2); at `i ≥ 3` every
   consumer carries `(H-VARTHETA-RES)_i` (D.67). This fence rides on top of `𝒲_{≤i}` — "a
   SECOND conditional stack on the same displays and must not be conflated with `𝒲_{≤i}`"
   (`EFF.T5.10`).
2. `𝒲_{≤i} := ⋀_{3≤q≤i} [GENTOW5-W(q)]` (D.60) is **never discharged in this chapter**:
   "Certification of the WI companion does not discharge these conjuncts from the frozen
   GENTOW5 statements" (`EFF.T5.29`). ⚠ The T5 source note still PHYSICALLY CONTAINS the
   superseded opposite sentence ("The certified WI note discharges these conjuncts…", source
   L299, ledger `HYP.100`); the effective text is the r1 replacement, and any consumer reading
   the raw note linearly gets the single most consequential question in the note WRONG. This
   chapter transcribes only the r1 form.
3. The base rung `i = 2` is unconditional (WF-law₂, `EFF.T5.12`) — supplied by GENTOW2-B″, a
   chapter-C placeholder (D.61); `𝒲_{≤2}` is the empty conjunction (`EFF.T5.13`).

**D-H6 — the T5 two-clause staleness (`HYP.99`), disclosed and typed away, not repaired.** T5
pins T1 at r1–r10 and carries only `(C3-ladder-nonvanishing)` for `w_i ∈ K_iˣ`; T1 HEAD (r12)
makes the gate **two-clause** (`(C3-read-codomain)` places `w_i ∈ K_i`,
`(C3-ladder-nonvanishing)` makes it nonzero — `EFF.T5.09`'s staleness flag). The Lean bundle
(D.29) types `w : Kˣ`, which carries BOTH clauses by construction — the honest strengthening
direction (a Lean instance must supply both; nothing is weakened). The staleness itself is a
note-owner repair (`EFF-T5` §8 item 2, OPEN-CALL 1 there) and is NOT executed here; §12 records
the disposition. The per-level suppliers of nonvanishing (`i = 2`: GENTOW2-B′(3)/B″; `i ≥ 3`:
GENTOW5 S11.2's proved fixed-unit list, routed AROUND `𝒲_{≤i}`; `i = 1`: **NONE** — no `i = 1`
instance of WF-w/WF-twist/WF-psi is asserted, and the `ψ₂` leg of WF-index rides S11.3's letter-
power form, `WFRAME OPEN-2`) are transcribed at D.61/D.66's interface notes exactly as
`EFF.T5.09` states them.

**D-H7 — T4's certificate layer: the disc-free member class and the repaired exposure
semantics.** Three source facts the schema must not lose:
1. **`𝔐` carries NO discriminant hypothesis and no decidedness hypothesis** (`EFF.T4.05`):
   `disc(f_key) = 0` and the `(Φ₂+c)²` perturbation prove no disc condition COULD be part of
   membership. The (FLOOR) quantifier is bound to `f ∈ 𝔐` (the R2-G1 → R5-F1 rebinding chain);
   D.46's field states it at exactly that quantification.
2. **The exposure repair chain (r3/r4)**: "uniqueness merely among single-extraction
   contributions does not imply full exposure" (`EFF.T4.08`); the no-contribution criterion
   needs **all-provenance** exclusion (`EFF.T4.17`). In the schema (D.46), `gr` is the
   *complete assembled* digit by definition of the field, so T4.2(c)/(d) (D.52/D.53) become
   short lemmas about finitely-supported functions — **the mathematical weight moves, honestly,
   to the instantiation obligation**: whoever instantiates `gr` must supply complete assembly
   (every branch, carry, recarry), and the two instance interfaces (D.54/D.55) say so in their
   statements. This is the same weight-relocation the corpus itself performed (the r3
   definition exists to make the criterion's premise carry the assembly).
3. **The FR-M3 separator** (`EFF.T4.11`): shadow pin `12`, threshold `Θ₀ = 10`, `ω₀ = 0` — a
   nonzero shadow coordinate whose assembled digit cancels. It is the committed reason (c)'s
   premise cannot be weakened; carried as a §12 regression row and named in D.52's ⚠.

**D-H8 — JD0-BOX-2 routing: checked, and it goes to chapter I.** Per the CONVENTIONS Part II
routing rule ("goes to chapter I unless a T-unit cites it"), a mechanical grep of all four
T-specs for `JD0`/`J-D0` returns **zero hits**. No T-unit cites a JD0 designation; chapter D
opens **no JD0 node**, and `JD0-BOX-2` lands in chapter I as the named hypothesis (its
machine-grade bar is SIGNED, Q6/`HYP.39`). Recorded here so the orchestrator's routing table
has the check, not just the rule.

**D-H9 — the HYP.01/HYP.12 escalations are I's, not D's.** The trust-boundary theorem naming
(`typeOf` faithfulness, the `(e,f)` ordering) originated in T3/T1 OPEN-CALLs and was answered
by placement into the core-set audit (`HYP.98`). Chapter D opens no node for them (Brief D trap
(iii)); D.69 records the OPEN-CALL → chapter-I routing table for all residual open calls of the
four specs (T1 OPEN-CALLs 1–5, T3 OPEN-CALL 1, T5 OPEN-CALL 1/HYP.99 — each either an inline
hypothesis of a D node, a chapter-C placeholder, or an I-routed trust-boundary item).

**D-H10 — carrier ruling: which hypotheses get named `Prop` carriers and which stay inline.**
Named carriers (public declarations, consumed by E/I by name): `(H-VARTHETA-RES)_i` (D.67),
`[GENTOW5-W(i)]` (D.44), `𝒲_{≤i}` (D.60), the combined Display-A conjunct family
`(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` for `i ≥ 3` (D.68), `(G5-COND)`/WF-chain (D.65). Inline
hypotheses (explicit arguments of their sole consuming node, per the corpus's sitewise
semantics; NO public carrier): `(H-JA-CONJ)_i` (D.20's specialization clause),
`(H-JA-RES-CONJ)` (D.23), `(H-GENHN-CLEAR)` (D.28's clearance note — the clearance itself is
not even a D statement), `(H-HETOW-LOCAL)` (D.27), (FLOOR) (a field of D.46), BR1–BR5 (fields
of D.37). Rationale: a public carrier is owed exactly to the hypotheses that Display A or
another chapter consumes BY NAME; the sitewise ones are consumed only at their sites, and
naming them globally would misstate their scope (the corpus's own "site obligations" wording,
`EFF.T1.03`).

**D-H11 — GC-13 placeholders: everything tower-sourced is chapter C's.** T3/T5 consume
GENTOW/HETOW content ONLY as placeholders (Brief D trap (ii)): GENTOW2-B′/B″
(`EFF.GENTOW2.34/.43 [supplied-by: chapter C]`), the GENTOW3 (FLOOR) discharge
(`EFF.GENTOW3 [supplied-by: chapter C]` — T4's X21 span), the GENTOW6 R5-63A legs, HETOW-4's
bridge/floor arithmetic, GENTOW5 S11.2/S11.3/S12.1/S12.2 spans. No such content is re-proved
here; the orchestrator resolves the placeholders to C node IDs when C freezes.

**D-H12 — unit-type census, and what does NOT become a node.** Of the 181 source units:
T1 = 21 mathematical units (`.01–.21`) + 3 interface tables/fences (`.22–.24`) + 9
absorption/battery-frame records (`.25–.33`) + 12 battery rows (`.34–.45`) + 10
acceptance/changes/scope records (`.46–.55`); T3 = 18 mathematical (`.01–.18`) + 8
absorption/scope (`.19–.26`) + 10 records (`.27–.36`); T4 = 17 mathematical (`.01–.17`) + 1
lemma (`.41`) + 27 instance/record/fence/battery units; T5 = 17 mathematical/hypothesis
(`.03–.19`, less fences) + 28 record/instance/fence units. Battery rows, acceptance boxes,
changes-records, run-records and scope-records become **§12 TEETH dispositions and §1/§13
honesty items, not nodes** (the CHAP-B/CHAP-H precedent); absorption records become
**interface nodes or supply-table prose** per D-H4(2). The chapter's 73 nodes therefore cover
181 units without a unit-to-node bijection; §11's DAG rows carry the full unit-level SOURCE
mapping so nothing is silently dropped.

**D-H13 — codex cross-read status: OWED.** Like every blueprint of this fleet, this chapter is
single-family-authored. §13 lists the specific items; the ϑ table (D.06) and DECISION D-1 are
the two highest-stakes reads.

---

## 2. NODE INDEX

| § | nodes | content |
|---|---|---|
| 3 | D.01–D.12 | the abstract cocycle arena; **THE ϑ ORIENTATION TABLE (D.06, anchor `D-THETA-TABLE`)**; telescope, bracket, coboundary |
| 4 | D.13–D.28 | the level-1 gauge layer: exponent calculus, the ℤ²-monomial arena, C2-level-1, C4, C5, C6, the HETOW consumption, the level-1 corrected key |
| 5 | D.29–D.36 | the read bundle and the B-law: `ReadBundle`, `LiftContract`, the dictionary, the corrected key, C3-Theta/B-law, three reads, the twist transport |
| 6 | D.37–D.44 | the telescope port (T3): BR1–BR5, T3-BR, comparison, routing, ABS-G2/ABS-HE4/ABS-G5W |
| 7 | D.45–D.56 | the certificate witness (T4): thresholds, `CertFrame`, ω/ν, T4.2(a)–(d), the two supplier interfaces |
| 8 | D.57–D.66 | the w-frame (T5): twist, WF-psi, WF-law₂/ᵢ, realized residuals, WF-index, WF-chain |
| 9 | D.67–D.69 | the `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` carriers (Display A's `∀ i ≥ 3` conjunct) and the OPEN-CALL routing |
| 10 | D.70–D.73 | gates: `q = 2` (F4-JOINT shape, `e > 1 ∧ f > 1`), `q = 3` (X-frame), FRAME-C regression, axiom census |
| 11 | — | DAG additions |
| 12 | — | leanspec stub list (stage 0e) |
| 13 | — | TEETH dispositions; flagged for the codex cross-read |

**Kind census (planning figure, to be recounted mechanically at §11):** ≈ 24 `def` (of which 4
carry a `structure`: D.07 `GaugeArena`, D.29 `ReadBundle`, D.37 `BoundaryReadPort`, D.46
`CertFrame`), ≈ 32 `lemma`, ≈ 9 `theorem`, ≈ 4 `gate`, ≈ 4 interface nodes with GC-13
placeholder dependencies — **73 nodes**. Split candidates flagged at D.25, D.26, D.34, D.46,
D.50 in their SIZE fields.

**Graph shape (planning estimate; computed mechanically into `spec/DAG_BLUEPRINT_D.tsv` at
§11):** the §3 arena and §4 arithmetic are terminal supply (≈ 18 nodes fireable immediately);
the critical path runs D.01 → D.02 → D.04 → D.07 → D.29 → D.33 → D.34 → D.63 (≈ 8 nodes). The
schedule risks are D.25/D.26 (the C6/C5 concrete layer over chapter B's API — the only nodes
whose dependencies are outside this chapter and landed-B) and D.46 (the certificate frame's
dependent-type design).

---
## 3. §3 — THE ABSTRACT COCYCLE ARENA AND THE ϑ ORIENTATION TABLE

> **Design note (why a bare `CommGroup`).** Every §3 identity is an identity between elements
> constructed from a height-indexed section into a commutative group; the corpus proves them by
> "exact-height arithmetic" plus residue multiplicativity, and the exact-height part is pure
> group algebra. Proving the group half once, abstractly, is what makes the level-1 instance
> (§4), the `i = 2` GENTOW2 instance (chapter C's, consumed at D.42) and the depth-`i ≥ 3`
> conditional layer (§9) *instances of one theorem* instead of three parallel calculations —
> exactly D-1's licence (honesty item D-H3).

### NODE D.01 [def] [fresh]

**STATEMENT.** *The normalizer section.* A **normalizer section** on a commutative group `G` is
a map `n : ℤ → G` (heights are integers — `EFF.T1.02`'s integrality clause scopes every consumed
height to `ℤ`) with the height-zero normalization `n 0 = 1` (`(C2-zero-normalizer)`,
`EFF.T1.02`). This is the whole §3 carrier: exact heights, residues, and the tower do not enter
until D.07.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Gauge

/-- A **normalizer section** at a fixed tower level: heights to monomials, normalized at
height zero (`C2-zero-normalizer`, `EFF.T1.02`; `N(0) = 1`, `EFF.T3.01`). -/
structure NormSection (G : Type*) [CommGroup G] where
  n : ℤ → G
  n_zero : n 0 = 1
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 10 lines.

**SOURCE.** `EFF.T1.02` (the boxed `(C2-zero-normalizer)`: "n̂_i(0) = 1"); `EFF.T3.01`
("`N(k) := n̂_i(k)`, `N(0) = 1`"); `EFF.T1.01` (the level-1 instance this abstracts — the
exact-height clause `i(k)h + a(k)e₁ = k` becomes D.07's `exact_height` field, not a field
here).

**TEETH.** T3 §8.1(1) (normalized endpoints) → Lean theorem at D.05/D.09.

**ENVIRONMENT.** ENV-D2.

---

### NODE D.02 [def+lemma] [fresh]

**STATEMENT.** *The normalizer cocycle `τ` and its endpoints.* For a normalizer section `N`,
`τ(a,b) := n(a)·n(b)·n(a+b)⁻¹`, with `τ(0,a) = τ(a,0) = 1`. (The corpus's quotient
`n̂(a)n̂(b)/n̂(a+b)` — division is `·⁻¹` in `G`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Gauge

/-- The T1 normalizer two-cocycle `τ_N(a,b) = N(a)N(b)/N(a+b)` (`EFF.T1.08`, `EFF.T3.02`). -/
def NormSection.tau {G : Type*} [CommGroup G] (N : NormSection G) (a b : ℤ) : G :=
  N.n a * N.n b * (N.n (a + b))⁻¹

theorem NormSection.tau_zero_left {G : Type*} [CommGroup G] (N : NormSection G) (a : ℤ) :
    N.tau 0 a = 1
-- and the mirror `tau_zero_right`, a private corollary in the same file (commutativity)
```

**DEPENDS.** D.01.

**PROOF.** 1. Unfold: `τ(0,a) = n 0 * n a * (n (0+a))⁻¹`. 2. `N.n_zero` + `zero_add` +
`mul_inv_cancel`-shape closes it (`simp [NormSection.tau, N.n_zero]`). 3. Mirror by
`add_comm`/`mul_comm`.

**SIZE.** 14 lines.

**SOURCE.** `EFF.T1.08` ("`τ_i(0,a) = τ_i(a,0) = 1`" — the endpoint half; R1-2's derivation
"`n̂(0) = 1` gives both endpoints"); `EFF.T3.02` (the imported `(T1-C2)` display).

**TEETH.** T3 §8.1(3) (no competing frame — the τ used everywhere below is THIS τ) →
executable regression retained (§12); the endpoint half → Lean theorem (this node).

**ENVIRONMENT.** ENV-D2.

---

### NODE D.03 [lemma] [fresh]

**STATEMENT.** *The cocycle law `(C2-cocycle)`.* For all `a b c : ℤ`:
`τ(a,b)·τ(a+b,c) = τ(b,c)·τ(a,b+c)`.

**SIGNATURE.**
```lean
theorem NormSection.tau_cocycle {G : Type*} [CommGroup G] (N : NormSection G) (a b c : ℤ) :
    N.tau a b * N.tau (a + b) c = N.tau b c * N.tau a (b + c)
```

**DEPENDS.** D.02.

**PROOF.** 1. Unfold `tau`: both sides are products of `n a, n b, n c` and one inverse
`(n (a+b+c))⁻¹` (the middle terms `n (a+b)`/`n (b+c)` cancel against their inverses).
2. Rewrite the two argument spellings by `add_assoc` (`(a+b)+c = a+(b+c)`), then `group`.
This is the corpus derivation verbatim: "Associativity compares the two parenthesizations of
three normalizers" (`EFF.T1.08`).

**SIZE.** 12 lines.

**SOURCE.** `EFF.T1.08` (the boxed `(C2-cocycle)`); `EFF.T3.02` (re-imported as `(T1-C2)`).

**TEETH.** T1's "misindexed telescope tooth" (`EFF.T1.08` TEETH) → the mutation this statement
kills is a shifted argument; Lean theorem (this node) + gate D.72's numeric leg.

**ENVIRONMENT.** ENV-D2.

---

### NODE D.04 [def] [fresh]

**STATEMENT.** *The two telescope orientations, at the group level.* For a section `N`, a
ladder step `q : ℤ` and `s : ℕ`:

* `varthetaEl N q s := (n q)^s · (n (s·q))⁻¹` — **T1's orientation** (`(C2-vartheta)`,
  `EFF.T1.09`: numerator the TOP-STEP power `n̂(u)^s`, denominator the slot-height normalizer
  `n̂(su)`);
* `thetaEl N q s := n (s·q) · ((n q)^s)⁻¹` — **the B-law (inverse) orientation**
  (`(C3-Theta)`/`(T1-THETA)`: `Θ = ϑ⁻¹`).

The suffix `El` marks the group ELEMENT; the `K`-valued residues are D.08's `vartheta`/`theta`.

**SIGNATURE.**
```lean
/-- T1's telescope orientation: the group element under `ϑ_{i,s} = res(n̂(u)^s / n̂(su))`
(`EFF.T1.09` (C2-vartheta)). ORIENTATION: T1 two-index; see D.06 (`D-THETA-TABLE`). -/
def NormSection.varthetaEl {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) (s : ℕ) : G :=
  (N.n q) ^ s * (N.n (s * q))⁻¹

/-- The B-law orientation `Θ_N(s;q) = ϑ_N(s;q)⁻¹` (`EFF.T3.04` (T1-THETA), `EFF.T1.14`
(C3-Theta)). ORIENTATION: inverse of `varthetaEl`; see D.06. -/
def NormSection.thetaEl {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) (s : ℕ) : G :=
  N.n (s * q) * ((N.n q) ^ s)⁻¹
```

**DEPENDS.** D.01.

**PROOF.** definitional.

**SIZE.** 12 lines.

**SOURCE.** `EFF.T1.09` (the boxed `(C2-vartheta)` — the fraction `n̂_i(u_{i+1})^s /
n̂_i(su_{i+1})`); `EFF.T3.03` (`ϑ_N(s;q) := res(N(q)^s / N(sq))`); `EFF.T3.04`
(`Θ_N(s;q) := ϑ_N(s;q)⁻¹ = res(N(sq)/N(q)^s)`); `EFF.T1.14` (`(C3-Theta)`).

**ORIENTATION.** T1 two-index convention for `varthetaEl`; `thetaEl` is its inverse — rows 1–2
of D.06. The slot reindexing `s = f_{i+1} − t` is applied at consumers (D.33, D.58), never
baked into these definitions.

**TEETH.** T1 "inverse-orientation tooth" (`EFF.T1.11/.14/.15` TEETH) → Lean theorem at D.10 +
gate D.72.

**ENVIRONMENT.** ENV-D2.

---

### NODE D.05 [lemma] [fresh]

**STATEMENT.** *Telescope endpoints and recursion `(C2-recursion)`/`(T1-TEL)`, group level.*
`varthetaEl N q 0 = 1`; `varthetaEl N q 1 = 1`; and
`varthetaEl N q (s+1) = varthetaEl N q s · tau N (s·q) q`.

**SIGNATURE.**
```lean
theorem NormSection.varthetaEl_succ {G : Type*} [CommGroup G]
    (N : NormSection G) (q : ℤ) (s : ℕ) :
    N.varthetaEl q (s + 1) = N.varthetaEl q s * N.tau (s * q) q
-- with `varthetaEl_zero` and `varthetaEl_one` as sibling lemmas in the same file
-- (one public declaration = the recursion; the endpoints are its two `simp` corollaries,
--  public per the STATEMENT — the stub signs all three)
```

**DEPENDS.** D.01, D.02, D.04.

**PROOF.** 1. `varthetaEl q 0 = (n q)^0 · (n 0)⁻¹ = 1` by `pow_zero`, `N.n_zero`
(`Nat.cast`-arithmetic: `(0 : ℕ) * q = 0`). 2. `varthetaEl q 1 = n q · (n q)⁻¹ = 1`
(`one_mul` cast). 3. Recursion: unfold; RHS
`= (n q)^s (n (sq))⁻¹ · n (sq) · n q · (n (sq + q))⁻¹ = (n q)^{s+1} (n ((s+1)q))⁻¹` by
`group` after the cast rewrite `((s+1 : ℕ) : ℤ) * q = s*q + q` (`push_cast; ring_nf`). This is
the corpus derivation: "Factor `N(u)^{s+1}/N((s+1)u)` through `N(su)`" (`EFF.T1.10`).

**SIZE.** 20 lines.

**SOURCE.** `EFF.T1.10` (the boxed `(C2-recursion)`: `ϑ_{i,0} = ϑ_{i,1} = 1`,
`ϑ_{i,s+1} = ϑ_{i,s}·res(τ_i(su_{i+1},u_{i+1}))` — this node is its group-level half; the
residue half is D.08); `EFF.T3.03` (`(T1-TEL)`).

**ORIENTATION.** T1 two-index (D.06 row 1).

**TEETH.** T3 §8.1(1) (endpoints) and §8.1(2) (recurrence) → Lean theorem (this node) +
executable at gates D.70–D.72; T1 §4.2 check 2 (positive-wrap/wrong-sign) → the recursion's
`τ`-factor is on the RIGHT of the product, the sign discipline the check guards.

**ENVIRONMENT.** ENV-D2.

---

<a id="D-THETA-TABLE"></a>
### NODE D.06 [table] [fresh] — ★ THE ϑ FOUR-WAY ORIENTATION TABLE (GC-14 canonical copy)

**ANCHOR: `D-THETA-TABLE`.** This node is the ONE canonical copy of the orientation table
(GC-14; PROJECT_STATE append #54's mandate: *"the gauge chapter's blueprint carry the four-way
orientation table as a node annotation, else a sign error no battery catches"*). Chapters C, E
and F cite this anchor; **no chapter restates the content in its own words.** Transcribed from
`EFF-GENTOW2.md`'s orientation records (`.25` — the `[TABLE]` at its L1065–1075, including
L1072 — with `.34`, `.41`, `.42`), T1 `EFF.T1.14`, T3 `EFF.T3.04`/`.19`, and T5's closing
reconciliation (T5 source L991–993, carried as row 5's verification record).

**THE TABLE.** GENTOW2's single-argument, slot-indexed unit is the reference. Slots `t < f₃`;
under the substitution `s := f₃ − t`, its defining display (`EFF.GENTOW2.41`) is
`ϑ(t) := res((n̂₂(u₃(f₃−t)) / n̂₂(u₃)^{f₃−t})(x₀)) = res(n̂₂(su₃)/n̂₂(u₃)^s)` — numerator at
the SLOT height, denominator the `(f₃−t)`-th power of the TOP-SLOT normalizer.

| # | note · symbol | definition | relation to GENTOW2's `ϑ(t)` | Lean name (this chapter) |
|---|---|---|---|---|
| 1 | **GENTOW2** `ϑ(t)` | `res((n̂₂(u₃(f₃−t))/n̂₂(u₃)^{f₃−t})(x₀))` | — (the reference) | `varthetaG2` (D.10) |
| 2 | **T1** `(C3-Theta)` · `Θ_i(t)` | `ϑ_{i,f_{i+1}−t}^{−1} = res(n̂_i((f_{i+1}−t)u_{i+1})/n̂_i(u_{i+1})^{f_{i+1}−t})` | **`ϑ(t) = Θ₂(t)`** — same object; hence GENTOW2's ϑ is the **INVERSE** of T1's two-index `ϑ_{i,s}` | `theta` at `s = f_{i+1}−t`; T1's `ϑ_{i,s}` = `vartheta` |
| 3 | **T3** `(T1-THETA)`/`(ABS-G2)` · `Θ_N(s;q)` = `ϑ_{G2}(t)` | `ϑ_N(s;q)^{−1} = res(N(sq)/N(q)^s)`; `ϑ_{G2}(t) := res(n̂₂(su₃)/n̂₂(u₃)^s) = Θ_N(s;u₃)` | **`ϑ(t) = ϑ_{G2}(t) = Θ_N(f₃−t; u₃)`**; T3 records the inverse orientation explicitly at its §8.1 check 2 | `theta` (same object as row 2) |
| 4 | **GENTOW5** `LEMMA GENTOW5-A1` · `vartheta_t` (source L214–215) | `theta_t := [n̂₂(λ)(x₀)]^t · [n̂₂(tλ)(x₀)]^{−1} = ι(vartheta_t)` | **RECIPROCAL**: A1's `theta_t = res(n̂₂(λ)^t/n̂₂(tλ))`, so **`ϑ(t) = vartheta_{f₃−t}^{−1}` at `λ = u₃`** — the exact pair append #54's trap names. GENTOW2 itself **DECLINES to adjudicate** this correspondence (its NON-IMPORT N-7) — which is why THIS TABLE, not either note alone, is the authority | A1's `theta_t` = `vartheta u₃ t` (T1 orientation, argument `t` not `f₃−t`) |
| 5 | **T5** L991–993 (the reconciliation) | "B″'s single-argument `ϑ(t)` is this note's `Θ₂(t)`, the inverse-telescope orientation" | the acceptance-pass verdict that closes the loop — **VERIFIED** (T5 ledger item 2, byte span `33f86204` L729–738, ledger md5-8 `d4c8b885`, raw-span md5 `8978f8ba…`; both legs re-checked at EFF compile time, `EFF.GENTOW2.25`) | — (a verification record, not a new object) |

**THE B-LAW DIRECTION — separate, and NOT to be conflated with the Θ/ϑ inversion.**
`u(β) := R_{3,β}(n̂₂(β̂))` is an FGMN-side read of a repo-side object, and direction (3) of
`LEMMA GENTOW2-B′` reads **`FGMN = u · repo`**, i.e. `R_{3,β}(g) = u(β)·digit(g)` — **NOT the
inverse** (`EFF.GENTOW2.34`'s orientation record; the r2 F3 finding exists because a fallback
clause once wrote the inverse convention). T1's `(C3-B-law)` `u(β_t) = Θ_i(t)·w_i^{f_{i+1}−t}`
and T3's `(ABS-G2)` `u(β_t) = ϑ_{G2}(t)·w^{f₃−t}` agree in that orientation — all three sides
consistent, and D.33 states the Lean form in exactly it.

**TOP-SLOT NORMALIZATION ANCHOR.** `ϑ(f₃−1) = 1`: the top slot `t = f₃−1` has `s = 1`, and
`κ̄ = β_{f₃−1}` gives `ϑ(f₃−1) = res(n̂₂(u₃)/n̂₂(u₃)¹) = 1` (`EFF.GENTOW2.41`'s orientation
record) — T3's §8.1 item 1 (`ϑ_N(0;q) = ϑ_N(1;q) = 1`) is the same anchor in T1 orientation
(both orientations agree at `s ∈ {0,1}` since `1⁻¹ = 1`). Lean form: D.09.

**THE LEAN CONTENT OF THIS NODE** (the inversion, as a theorem — the executable half of the
sign discipline):

**SIGNATURE.**
```lean
/-- ★ D-THETA-TABLE. The two telescope orientations are mutually inverse:
`Θ_N(s;q) · ϑ_N(s;q) = 1` (T3 §8.1 check 2's content, group level). Consumers: see the
four-way orientation table at blueprint anchor `D-THETA-TABLE` (CHAP-D node D.06). -/
theorem NormSection.thetaEl_mul_varthetaEl {G : Type*} [CommGroup G]
    (N : NormSection G) (q : ℤ) (s : ℕ) :
    N.thetaEl q s * N.varthetaEl q s = 1
```

**DEPENDS.** D.04.

**PROOF.** Unfold both; `group`.

**SIZE.** 8 Lean lines (the table is blueprint annotation, not Lean text; the docstring
carries the anchor pointer).

**SOURCE.** GC-14 (the czar pin — content re-transcribed from the specs, not from the pin);
`EFF.GENTOW2.25` (the `[TABLE]` and the T5-verification record), `.34` (the B-law direction
record), `.41` (the defining display + top-slot anchor), `.42` (ϑ is x₀-free and
letter-valued — the fact that makes row 1's object land in the letter group, D-1's `i = 2`
licence); `EFF.T1.14` (`(C3-Theta)`, `(C3-B-law)`); `EFF.T3.04` (`(T1-THETA)`), `EFF.T3.19`
(`(ABS-G2)`); GENTOW5-A1 row: `EFF-GENTOW2.md:1072` (per GC-14 — GENTOW5's own spec carries
the merged-ID twin; C's author resolves it, GC-12).

**TEETH.** The trap has NO battery (append #54: "a sign error no battery catches") — the
teeth are (i) this node's Lean inversion theorem, (ii) D.10's `K`-valued form, (iii) gate
D.72's numeric orientation leg (`U(s) = Θ_s w^s` at the FRAME-C tables), and (iv) the
`ORIENTATION:` field discipline on every ϑ-touching node of chapters C/D/E/F.

**ENVIRONMENT.** ENV-D2.

---
<!-- RESUME: §3 through D.06 committed; next = D.07–D.12 -->

<!-- CHAP-D APPEND POINT — do not remove; sections are appended here in order -->
