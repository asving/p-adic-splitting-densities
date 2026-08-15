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
### NODE D.07 [def] [fresh]

**STATEMENT.** *The gauge arena (DECISION D-1's structure).* A **gauge arena** over a section
`N : NormSection G` with letter field `K` consists of: a height homomorphism
`v : G →* Multiplicative ℤ`; the **exact-height** clause `v (n k) = ofAdd k` for every `k`
(`EFF.T1.01`'s "exact height because its defining exponents satisfy `i(k)h + a(k)e₁ = k`",
abstracted); and a residue homomorphism `res : v.ker →* Kˣ` on the value-zero subgroup. Every
§3 combination (`τ`, `varthetaEl`, `thetaEl`, the bracket, `χ` for two sections with the same
`v`) lies in `v.ker` by exact-height arithmetic, so its `K`-valued residue is defined.

**SIGNATURE.**
```lean
/-- DECISION D-1's residue interface. Instantiations: level 1 = D.17 (η-powers); level 2 =
GENTOW2's letter group `⟨γ₁, γ₂⟩` (`EFF.GENTOW2.42`, supplied by chapter C); depth `i ≥ 3` =
exactly the `(H-VARTHETA-RES)_i` conditionality (D.67) — supplying this structure at depth IS
the hypothesis. FAITHFULNESS: formally stronger than the sitewise clauses; see CHAP-D honesty
item D-H3 and §13 item 2. -/
structure GaugeArena (G : Type*) [CommGroup G] (K : Type*) [Field K]
    (N : NormSection G) where
  v : G →* Multiplicative ℤ
  exact_height : ∀ k : ℤ, v (N.n k) = Multiplicative.ofAdd k
  res : MonoidHom.ker v →* Kˣ
```

**DEPENDS.** D.01 · mathlib `MonoidHom.ker` (`Subgroup`-valued).

**PROOF.** definitional.

**SIZE.** 14 lines.

**FAITHFULNESS.** (i) The corpus's five C3 read clauses (`EFF.T1.03`) are SITEWISE; this
structure asserts hom-ness on all of `v.ker`. The two proved instances justify it (D-H3:
`EFF.T1.01` at level 1, `EFF.GENTOW2.42` at level 2 — the value-0 monomials form exactly
`⟨γ₁,γ₂⟩` and `res` is multiplicative there); at `i ≥ 3` NO instance is claimed. (ii) The
graded reads `R_{i+1,β}` at NONZERO grade are NOT fields of this structure — the arena covers
only the value-zero residue algebra (τ/ϑ/χ); the positive-grade read obligations stay in
D.29's `ReadBundle`, sitewise, exactly as `EFF.T1.03` states them. Flagged for cross-read
(§13 item 2).

**SOURCE.** `EFF.T1.01`–`.03` (packaging per DECISION D-1); `EFF.GENTOW2.42` (the `i = 2`
licence).

**TEETH.** none directly (a definition); its instances carry the batteries (D.17, gates).

**ENVIRONMENT.** ENV-D2 + ENV-D3 (`{K} [Field K]`).

---

### NODE D.08 [def+lemma] [fresh]

**STATEMENT.** *The `K`-valued telescope.* For an arena `A`: (i) `varthetaEl N q s ∈ v.ker`
(exact-height arithmetic: `v((n q)^s (n (sq))⁻¹) = ofAdd (s·q − s·q) = 1`); define
`A.vartheta q s : Kˣ := A.res ⟨varthetaEl …⟩` and `A.theta q s := A.res ⟨thetaEl …⟩`;
(ii) the residue recursion `(C2-recursion)`, `K`-half:
`A.vartheta q (s+1) = A.vartheta q s * A.res ⟨tau (s·q) q, _⟩`.

**SIGNATURE.**
```lean
noncomputable def GaugeArena.vartheta {G K N} [CommGroup G] [Field K]
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) : Kˣ :=
  A.res ⟨N.varthetaEl q s, A.varthetaEl_mem_ker q s⟩
-- sibling: `GaugeArena.theta`; membership lemmas `varthetaEl_mem_ker`, `tauEl_mem_ker`
-- (private); public recursion lemma `vartheta_succ` per the STATEMENT
```

**DEPENDS.** D.02, D.04, D.05, D.07.

**PROOF.** 1. Membership: `map_mul`/`map_pow`/`map_inv` on `v` + `exact_height` + `omega` on
the `ofAdd` exponents. 2. Recursion: `A.res` is a `MonoidHom`; apply it to D.05's group
identity (`map_mul` + `Subgroup` coercion bookkeeping).

**SIZE.** 30 lines.

**SOURCE.** `EFF.T1.09` (the residue-level `(C2-vartheta)`), `EFF.T1.10` (the residue
recursion), `EFF.T3.03`.

**ORIENTATION.** `vartheta` = T1 two-index (D.06 row 2's `ϑ_{i,s}`); `theta` = the B-law
orientation (D.06 rows 2–3).

**TEETH.** T3 §8.1(2) → Lean theorem (this node's recursion); T1 §4.2 checks 5/8/9 (the read
bundle sites) → those guard D.29's bundle, not this node — the split is deliberate (this node
is value-zero algebra only, D.07 FAITHFULNESS (ii)).

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.09 [lemma] [fresh]

**STATEMENT.** *The top-slot anchor (T3 §8.1 check 1; GENTOW2's `ϑ(f₃−1) = 1`).*
`A.vartheta q 0 = 1` and `A.vartheta q 1 = 1` — and since `theta = vartheta⁻¹` (D.10), the
same endpoints hold in BOTH orientations, which is exactly why the top slot (`t = f_{i+1}−1`,
`s = 1`) is the safe normalization anchor of the whole table (D.06's anchor paragraph).

**SIGNATURE.**
```lean
theorem GaugeArena.vartheta_zero {G K N} [CommGroup G] [Field K]
    (A : GaugeArena G K N) (q : ℤ) : A.vartheta q 0 = 1
-- sibling `vartheta_one` in the same file, same shape (public; the stub signs both)
```

**DEPENDS.** D.05, D.08.

**PROOF.** Push `A.res` through D.05's endpoint identities (`map_one` after showing the
subtype element is `1` — `Subtype.ext` + D.05).

**SIZE.** 12 lines.

**SOURCE.** `EFF.T3.03` (`ϑ_N(0;q) = ϑ_N(1;q) = 1`); `EFF.GENTOW2.41` ("`κ̄ = β_{f₃−1}` means
`ϑ(f₃−1) = res(n̂₂(u₃)/n̂₂(u₃)¹) = 1` — the top-slot normalization … T3 checks at its §8.1
item 1"); `EFF.T1.10` (`ϑ_{i,0} = ϑ_{i,1} = 1`).

**ORIENTATION.** both (they agree at `s ∈ {0,1}`; D.06 anchor paragraph).

**TEETH.** T3 §8.1(1) → **Lean theorem** (this node); executable at gate D.72.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.10 [lemma] [fresh]

**STATEMENT.** *The orientation involution and the GENTOW2 alias (T3 §8.1 check 2 as a Lean
lemma).* (i) `A.theta q s * A.vartheta q s = 1` — the `K`-valued inversion; (ii) the
slot-indexed alias `varthetaG2 A q f t := A.theta q (f − t)` (GENTOW2's single-argument unit,
D.06 row 1: argument the SLOT `t`, value the INVERSE-orientation telescope at `s = f − t`),
with the defining lemma `varthetaG2 A q f t = (A.vartheta q (f − t))⁻¹`.

**SIGNATURE.**
```lean
theorem GaugeArena.theta_mul_vartheta {G K N} [CommGroup G] [Field K]
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    A.theta q s * A.vartheta q s = 1

/-- GENTOW2's single-argument slot-indexed ϑ (D-THETA-TABLE row 1): `ϑ(t) = Θ(f−t)`. -/
noncomputable def GaugeArena.varthetaG2 {G K N} [CommGroup G] [Field K]
    (A : GaugeArena G K N) (q : ℤ) (f t : ℕ) : Kˣ := A.theta q (f - t)
```

**DEPENDS.** D.06 (the group inversion), D.08.

**PROOF.** (i) push `res` through D.06's `thetaEl_mul_varthetaEl` (`map_mul`, `map_one`).
(ii) definitional + `eq_inv_of_mul_eq_one_left` from (i).

**SIZE.** 18 lines. ⚠ Two public declarations (a theorem + the alias def) — the alias is the
table's row-1 name and must be a REAL name for C/E/F to cite; recorded as a sanctioned GC-6.5
exception scoped to exactly `varthetaG2` (the D.06 table mandates the name exists).

**SOURCE.** `EFF.T3.04` (+ its §8.1 check 2, "recurrence/inverse orientation");
`EFF.GENTOW2.25`/`.41` (the single-argument convention and `s := f₃ − t` reindexing).

**ORIENTATION.** the involution itself — D.06 rows 1–3 made a theorem.

**TEETH.** T3 §8.4(4) "inverse-orientation mutant" → **Lean theorem** (this node); gate D.72.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.11 [lemma] [fresh]

**STATEMENT.** *The descending bracket telescope `(T3-BKT)`, group level.* For `H₀ q : ℤ` and
`t : ℕ`, with `H_r := H₀ − r·q`:
`∏_{r=0}^{t−1} τ(H_{r+1}, q) = n(H_t) · (n q)^t · (n H₀)⁻¹`.

**SIGNATURE.**
```lean
theorem NormSection.tau_bracket_telescope {G : Type*} [CommGroup G]
    (N : NormSection G) (H₀ q : ℤ) (t : ℕ) :
    (Finset.range t).prod (fun r => N.tau (H₀ - (r + 1) * q) q)
      = N.n (H₀ - t * q) * (N.n q) ^ t * (N.n H₀)⁻¹
```

**DEPENDS.** D.02.

**PROOF.** Induction on `t`. Base: empty product `= 1 = n H₀ · (n H₀)⁻¹` (`pow_zero`,
`sub_zero` casts). Step: `Finset.prod_range_succ`, then the corpus's own cancellation
("`H_r = H_{r+1} + q`, so `τ(H_{r+1},q) = n(H_{r+1})n(q)/n(H_r)`; multiplication cancels the
intermediate normalizers" — `EFF.T3.15`'s verbatim derivation): `group` after the cast rewrite
`H₀ − (t+1)q + q = H₀ − tq`. "This is an iteration of the imported cocycle seam, not a new
proof of its normalization or cocycle law" — accordingly this node depends only on D.02's
definition, not on D.03.

**SIZE.** 22 lines.

**SOURCE.** `EFF.T3.15` (the boxed `(T3-BKT)` with `H_t = H₀ − tq`, product over
`r = 0,…,t−1` of `τ_N(H_{r+1}, q)`).

**TEETH.** T3 §8.3(2) (HETOW-4 clause (c) "coefficient telescope … fully supplied by
(T3-BKT)") → Lean theorem (this node) + the ABS-HE4 interface (D.43).

**ENVIRONMENT.** ENV-D2.

---

### NODE D.12 [def+lemma] [fresh]

**STATEMENT.** *The section ratio `χ` and the coboundary `(T3-COB)`.* For TWO sections
`N N̂ : NormSection G` (same group, same height set — `EFF.T3.12`'s "two normalized
exact-height sections on the same set of heights"): `χ(k) := n̂(k) · (n(k))⁻¹`, and
`χ(a)·χ(b)·χ(a+b)⁻¹ = τ_{N̂}(a,b) · τ_N(a,b)⁻¹`. In particular **no character law for `χ` is
assumed**: `χ` is a character exactly when the two cocycles have equal residue (the corpus's
own warning, kept as a ⚠ non-claim — T3's battery even exhibits the failure, `χ(1)² = 1 ≠ 2 =
χ(2)` at FRAME-C, gate D.72).

**SIGNATURE.**
```lean
/-- The pointwise section ratio (`EFF.T3.12`; T3's `χ`, renamed from HETOW's `τ` to avoid
collision with the two-argument cocycle — the spec's own renaming). -/
def NormSection.chi {G : Type*} [CommGroup G] (Nhat N : NormSection G) (k : ℤ) : G :=
  Nhat.n k * (N.n k)⁻¹

theorem NormSection.chi_coboundary {G : Type*} [CommGroup G]
    (Nhat N : NormSection G) (a b : ℤ) :
    chi Nhat N a * chi Nhat N b * (chi Nhat N (a + b))⁻¹
      = Nhat.tau a b * (N.tau a b)⁻¹
```

**DEPENDS.** D.01, D.02.

**PROOF.** Unfold; `group` (the corpus derivation is the displayed two-line residue
computation, `EFF.T3.16` — here at group level, with the residue image following through
D.07's `res` at consumers).

**SIZE.** 16 lines.

**SOURCE.** `EFF.T3.12` (χ's definition + the renaming note), `EFF.T3.16` (the boxed
`(T3-COB)` + "no character law for χ is assumed. It is a character exactly when the two
imported cocycles have equal residue").

**TEETH.** T3 §8.4(1) "character mutant" → **Lean theorem** (this node) + gate D.72's
`χ(1)² ≠ χ(2)` numeric leg (the mutant that assumes the character law dies there).

**ENVIRONMENT.** ENV-D2.

---
## 4. §4 — THE LEVEL-1 GAUGE LAYER

> **Design note (the point-free discipline).** T1's level-1 layer has two faces: exponent
> arithmetic (`i(k)`, `a(k)`, `wrap`, `q(k)`, `W(t)` — pure `ℕ`/`ℤ`, D.13–D.16) and monomial
> algebra in the group `x^ℤ π^ℤ`, represented EXACTLY by the exponent lattice
> `Multiplicative (ℤ × ℤ)` (D.17). The C5/C6 reads at tower points `ξ` with embeddings `ι_ξ`
> are the ONE part that needs a valued extension carrier — which `leanfinal` does not have and
> chapter C owns (GC-7). This chapter therefore transcribes C5/C6 **point-free**: the
> normalized-digit read `γ_k` and the exact lift `L_M` are defined on coordinates over the
> bundle (D.24–D.26, via chapter B's digit API), the identity `γ_M(L_M(λ)) = λ` is proved
> there, and the `ξ`-evaluation clauses `(C5-normalizer-read)`/`(C6-residue)`-at-`ξ` are
> carried as the embedding interface for chapter C (each node's ⚠ states the exact clause
> left to the tower carrier). Nothing is weakened: the corpus's own derivations of C2-wrap,
> C5-carry, C2-level-1 and the A3/A4 pins are exponent/coordinate computations.

### NODE D.13 [def] [fresh]

**STATEMENT.** *The level-1 exponent pair.* For `e₁ h : ℕ` with `0 < e₁` and
`Nat.Coprime h e₁`, and a height `k : ℤ`: `iexp e₁ h k` is the unique `i` with `0 ≤ i < e₁`
and `i·h ≡ k (mod e₁)`, and `aexp e₁ h k := (k − iexp·h) / e₁ : ℤ`, so that the **exact-height
identity** `(iexp e₁ h k)·h + (aexp e₁ h k)·e₁ = k` holds (`EFF.T1.01`'s
`i(k)h + a(k)e₁ = k`, `0 ≤ i(k) < e₁`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Gauge

/-- `i(k)`: the reduced x-exponent of the level-1 normalizer `n̂₁(k) = x^{i(k)}π^{a(k)}`. -/
def iexp (e₁ h : ℕ) (k : ℤ) : ℕ := ((k : ZMod e₁) * (h : ZMod e₁)⁻¹).val

/-- `a(k)`: the π-exponent, fixed by the exact-height identity. -/
def aexp (e₁ h : ℕ) (k : ℤ) : ℤ := (k - iexp e₁ h k * h) / e₁

theorem iexp_aexp_spec (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (k : ℤ) :
    iexp e₁ h k < e₁ ∧ (iexp e₁ h k : ℤ) * h + aexp e₁ h k * e₁ = k
```
⚠ Three public declarations — permitted on the B.15 precedent (the pair + its spec are one
interface; every §4 node consumes all three). `ZMod e₁` needs `NeZero e₁` — supplied from
`he` at use sites (`haveI`); the def itself is total (garbage at `e₁ = 0`, spec'd only under
`he`).

**DEPENDS.** mathlib `ZMod.val`, `ZMod.inv` (coprime inverse: `ZMod.inv_mul_of_unit` /
`ZMod.coe_unit_of_coprime` cluster — the stub agent verifies the exact names at the pin).

**PROOF.** 1. `iexp < e₁`: `ZMod.val_lt` (under `NeZero`). 2. Congruence `iexp·h ≡ k`:
`(h : ZMod e₁)` is a unit by `hcop`; multiply the definition back. 3. Divisibility
`e₁ ∣ k − iexp·h` from the congruence (`ZMod.intCast_zmod_eq_zero_iff_dvd`); the identity by
`Int.ediv_mul_cancel`.

**SIZE.** 30 lines.

**SOURCE.** `EFF.T1.01` (the displayed `n̂₁(k) = x^{i(k)}π^{a(k)}, 0 ≤ i(k) < e₁,
i(k)h + a(k)e₁ = k`).

**TEETH.** T1 §4.2 check 1 (live-domain boundary) → gates D.70/D.71 evaluate `iexp`/`aexp`
tables; check 10 (grade-data value group) → the `ℤ`-typing of `aexp` (heights are integers,
`EFF.T1.02`'s integrality clause).

**ENVIRONMENT.** ENV-D1.

---

### NODE D.14 [def+lemma] [fresh]

**STATEMENT.** *The wrap bit and `(C2-wrap)`.* `wrap e₁ h a b := (iexp a + iexp b) / e₁`
(`ℕ`-division). Then (i) `wrap ∈ {0,1}`; (ii) the **wrap identity**
`iexp a + iexp b = iexp (a+b) + e₁ * wrap a b` — the exponent form of `(C2-wrap)`'s monomial
display `n̂₁(a)n̂₁(b) = n̂₁(a+b)·(x^{e₁}/π^h)^{wrap(a,b)}` (the monomial form itself is a
D.17-arena corollary, proved there as the `tau` computation).

**SIGNATURE.**
```lean
def wrap (e₁ h : ℕ) (a b : ℤ) : ℕ := (iexp e₁ h a + iexp e₁ h b) / e₁

theorem iexp_add_wrap (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (a b : ℤ) :
    iexp e₁ h a + iexp e₁ h b = iexp e₁ h (a + b) + e₁ * wrap e₁ h a b
    ∧ wrap e₁ h a b ≤ 1
```

**DEPENDS.** D.13.

**PROOF.** 1. Both sides of the identity are `< 2e₁`-bounded and congruent mod `e₁`
(`iexp (a+b) ≡ iexp a + iexp b`, from D.13's congruence + `ZMod` ring arithmetic); `omega`
closes from the two D.13 bounds. 2. `wrap ≤ 1` from `iexp a + iexp b < 2e₁` (`Nat.div_lt_iff`
shape). This is the corpus derivation: "the reduced exponent satisfies
`i(a)+i(b) = i(a+b) + e₁ wrap(a,b)`" (`EFF.T1.07`).

**SIZE.** 22 lines.

**SOURCE.** `EFF.T1.07` (the boxed `(C2-wrap)` and `wrap(a,b) = ⌊(i(a)+i(b))/e₁⌋ ∈ {0,1}`).

**TEETH.** T1 §4.2 check 2 + the "positive-wrap" and "wrong-sign" teeth → Lean theorem (this
node; the sign convention is `+e₁·wrap` on the RIGHT of `iexp (a+b)`) + gates D.70/D.71
(wrap tables at both primes).

**ENVIRONMENT.** ENV-D1.

---

### NODE D.15 [def+lemma] [fresh]

**STATEMENT.** *The carry exponent `q(k)` and `(C5-carry)`.* With `i₀ := iexp e₁ h 1`:
`qexp e₁ h k := (i₀ * k − iexp e₁ h k) / e₁ : ℤ` (integral: `i₀·k ≡ iexp k (mod e₁)` since
both `≡ h⁻¹·k`), and the **carry law**
`qexp (a+b) = qexp a + qexp b + wrap a b`.

**SIGNATURE.**
```lean
def qexp (e₁ h : ℕ) (k : ℤ) : ℤ := (iexp e₁ h 1 * k - iexp e₁ h k) / e₁

theorem qexp_add (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (a b : ℤ) :
    qexp e₁ h (a + b) = qexp e₁ h a + qexp e₁ h b + wrap e₁ h a b
```

**DEPENDS.** D.13, D.14.

**PROOF.** 1. Integrality of the defining division: `i₀ ≡ h⁻¹`, `iexp k ≡ h⁻¹k (mod e₁)` (D.13)
⇒ `e₁ ∣ i₀k − iexp k`. 2. The law: multiply by `e₁` and substitute D.14's wrap identity —
"multiply the difference by `e₁` and use `i(a)+i(b)−i(a+b) = e₁ wrap(a,b)`" (`EFF.T1.19`'s
verbatim derivation); `omega`/`ring` after clearing the exact divisions
(`Int.ediv_mul_cancel` on the three integrality facts).

**SIZE.** 24 lines.

**SOURCE.** `EFF.T1.19` (the boxed `(C5-carry)` `q(a+b) = q(a)+q(b)+wrap(a,b)`;
`q(k) = (i₀k − i(k))/e₁`).

**TEETH.** T1's A2 consumption regression + §4.2 check 4 (the `−q(k)` sign) → Lean theorem
(this node + D.19); gate D.71.

**ENVIRONMENT.** ENV-D1.

---

### NODE D.16 [def] [fresh]

**STATEMENT.** *The level-1 telescope exponent.* `Wfloor e₁ h u₂ f₂ t := (f₂ − t) * iexp e₁ h u₂ / e₁ : ℕ`
— the corpus's `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` (`EFF.T1.10`). A definition only; the law
`ϑ_{1,f₂−t} = η^{W(t)}` is D.18.

**SIGNATURE.**
```lean
def Wfloor (e₁ h : ℕ) (u₂ : ℤ) (f₂ t : ℕ) : ℕ := (f₂ - t) * iexp e₁ h u₂ / e₁
```

**DEPENDS.** D.13.

**PROOF.** definitional. (`ℕ`-subtraction `f₂ − t` is the corpus's `s = f₂ − t ≥ 0`; consumers
always have `t < f₂` in scope — `t ≤ f₂` truncation junk is never consumed, noted for the stub.)

**SIZE.** 6 lines.

**SOURCE.** `EFF.T1.10` (`W(t) = ⌊(f₂−t)i(u₂)/e₁⌋`, `ϑ_{1,f₂−t} = η^{W(t)}`, "The exponent
has the displayed positive sign").

**TEETH.** the wrong-sign tooth → D.18 + gates.

**ENVIRONMENT.** ENV-D1.

---

### NODE D.17 [def] [fresh]

**STATEMENT.** *The level-1 arena.* The level-1 monomials `x^i π^a` are represented exactly by
the exponent lattice `Multiplicative (ℤ × ℤ)` (first coordinate the `x`-exponent, second the
`π`-exponent). Define (i) the **level-1 section** `levelOneSection e₁ h : NormSection _` by
`n k := (iexp e₁ h k, aexp e₁ h k)`; (ii) for a field `K` with a distinguished unit `η : Kˣ`
(the corpus's `η = res(x^{e₁}/π^h)`, `K₁ = F_Q(η)` — `EFF.T1.01`), the **level-1 arena**
`levelOneArena e₁ h he hcop η : GaugeArena _ K _` with height hom `v (i,a) := i·h + a·e₁` and
residue hom `res : ker v →* Kˣ` sending `(i,a) ↦ η^{i/e₁}` — well-defined because
`ih + ae₁ = 0` and `Nat.Coprime h e₁` force `e₁ ∣ i` and `(i,a) = (i/e₁)·(e₁,−h)`, i.e. the
kernel is the cyclic group generated by the exponent pair of `x^{e₁}/π^h`, mapped by
`t ↦ η^t`.

**SIGNATURE.**
```lean
def levelOneSection (e₁ h : ℕ) : NormSection (Multiplicative (ℤ × ℤ)) where
  n k := Multiplicative.ofAdd (iexp e₁ h k, aexp e₁ h k)
  n_zero := by simp [iexp, aexp]

noncomputable def levelOneArena (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) :
    GaugeArena (Multiplicative (ℤ × ℤ)) K (levelOneSection e₁ h)
```
⚠ Two public declarations (section + arena) — sanctioned: they are one instance split only by
where the field `K` enters; C and the gates cite both by name.

**DEPENDS.** D.01, D.07, D.13 (`iexp_aexp_spec` gives `exact_height`).

**PROOF.** 1. `n_zero`: `iexp 0 = 0`, `aexp 0 = 0` (compute). 2. `v` is a hom: componentwise
`ℤ`-linear. 3. `exact_height`: D.13's identity verbatim. 4. Kernel description: for
`ih + ae₁ = 0`, `e₁ ∣ ih` and `Nat.Coprime h e₁` give `e₁ ∣ i` (`Nat.Coprime.dvd_of_dvd_mul_right`,
`ℤ`-cast); set `t := i / e₁`, then `a = −t·h` (from the kernel equation, `e₁ ≠ 0`). 5. `res`
hom-ness: `t` is additive in `(i,a)` (the quotient of a linear form), so `t ↦ η^t` is a
`zpow` hom.

**SIZE.** 40 lines. Fragile signature (dependent `GaugeArena` fields + `Multiplicative`
coercions) — elaborate FIRST at the stub stage (§12).

**FAITHFULNESS.** The exponent lattice is an exact model of the monomial group: all §4
consumed identities are monomial-exponent identities (`EFF.T1.07/.10/.19`'s own derivations
are exponent computations). What the lattice does NOT model is evaluation of monomials at
field elements — deliberately (the §4 design note); no node consumes it. The distinguished
`η` is DATA here; its corpus meaning (`res(x^{e₁}/π^h)` inside `K₁ = F_Q(η)` with basis
`1,…,η^{f₁−1}`) is restored at D.26 where the coordinate reads land.

**SOURCE.** `EFF.T1.01` (the carrier: `dv₁(x) = h`, `dv₁(π) = e₁`, `η`, `K₁`, the basis,
`n̂₁(k)`); `EFF.T1.04` (`z₁ := η`, `(C1-base-letter)`).

**TEETH.** T1 §4.2 checks 1/2/4 (all level-1 checks run through this instance) → gates
D.70/D.71 instantiate it at both primes.

**ENVIRONMENT.** ENV-D1 + ENV-D3 (`{K} [Field K]`, `η : Kˣ`).

---

### NODE D.18 [lemma] [fresh]

**STATEMENT.** *`(C2-level-1)`: the level-1 telescope is an explicit `η`-power.* In the
level-1 arena, for `u₂ : ℤ` and `s : ℕ`:
`(levelOneArena …).vartheta u₂ s = η ^ (s * iexp e₁ h u₂ / e₁)`, and in slot-indexed form
`(levelOneArena …).vartheta u₂ (f₂ − t) = η ^ Wfloor e₁ h u₂ f₂ t`. **"The exponent has the
displayed positive sign"** (`EFF.T1.10` — transcribed as stated; the wrong-sign mutation is
the tooth).

**SIGNATURE.**
```lean
theorem levelOneArena_vartheta (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (u₂ : ℤ) (s : ℕ) :
    (levelOneArena e₁ h he hcop η).vartheta u₂ s = η ^ (s * iexp e₁ h u₂ / e₁)
```

**DEPENDS.** D.08, D.13, D.16, D.17.

**PROOF.** 1. The group element `varthetaEl u₂ s` has exponent pair
`(s·iexp u₂ − iexp (s·u₂), s·aexp u₂ − aexp (s·u₂))`. 2. `iexp (s·u₂) ≡ s·iexp u₂ (mod e₁)`
(D.13's congruence, `ZMod` arithmetic), and both `iexp`-values are reduced, so
`s·iexp u₂ − iexp (s·u₂) = e₁·(s·iexp u₂ / e₁)` — "reducing `s·i(u₂)` modulo `e₁` yields the
floor count" (`EFF.T1.10`'s verbatim derivation). 3. The kernel-generator exponent is
therefore `t = s·iexp u₂ / e₁`; D.17's `res` gives `η^t`. 4. Slot form: substitute
`s := f₂ − t` and fold D.16.

**SIZE.** 30 lines.

**SOURCE.** `EFF.T1.10` (the boxed `(C2-level-1)` `ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}` + the `W(t)`
display).

**ORIENTATION.** T1 two-index (D.06 row 2). The GENTOW2-orientation value at this instance is
the INVERSE `η^{−W(t)}` — a consumer wanting GENTOW2's `ϑ(t)` reads `varthetaG2` (D.10), never
this lemma with a silent sign flip.

**TEETH.** T1 §4.2 check 2 → **Lean theorem** (this node); gauge-naive and wrong-sign teeth →
gates D.70/D.71 evaluate the `η`-power tables at both primes.

**ENVIRONMENT.** ENV-D1 + ENV-D3.

---

### NODE D.19 [lemma] [fresh]

**STATEMENT.** *`(C5-monomial-ratio)`: the `ϖ`-comparison.* Let `ϖ := n̂₁(1)` (the level-1
normalizer avatar) and let `varpiSection` be the section `k ↦ ϖ^k` (also a `NormSection` —
powers of a fixed element, `n 0 = 1`). Then in the exponent lattice
`chi (levelOneSection e₁ h) varpiSection k = ((e₁, −h) : ℤ × ℤ) ^ (−qexp e₁ h k)` — the
corpus's `n(k)/ϖ^k = (x^{e₁}/π^h)^{−q(k)}` — and hence, applying D.17's `res`,
the residue is `η^{−qexp k}`. Moreover `(C5-carry)` (D.15) is exactly the coboundary law
(D.12) of this section pair: `χ(a)χ(b)/χ(a+b) = (x^{e₁}/π^h)^{wrap(a,b)}` — the consistency
triangle wrap/carry/coboundary closes, which is the A2 regression's content.

**SIGNATURE.**
```lean
theorem chi_varpi (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (k : ℤ) :
    NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k
      = Multiplicative.ofAdd ((-(qexp e₁ h k)) • ((e₁ : ℤ), -(h : ℤ)))
-- sibling (same file, public): `varpiSection` [def] and the residue corollary `res_chi_varpi`
```
⚠ Direction check for the stub: `chi Nhat N k = n̂(k)·(n(k))⁻¹` (D.12) with
`Nhat := levelOneSection` (the exact-height section) and `N := varpiSection` — matching the
corpus's `n(k)/ϖ^k`.

**DEPENDS.** D.12, D.13, D.15, D.17.

**PROOF.** 1. Exponent subtraction: `(iexp k − i₀k, aexp k − a₀k)`. 2. First coordinate
`= −e₁·qexp k` (D.15's defining division, cleared). 3. Second coordinate `= h·qexp k`: from
the two exact-height identities `iexp k·h + aexp k·e₁ = k` and `k·(i₀h + a₀e₁) = k`,
subtract: `(iexp k − i₀k)h + (aexp k − a₀k)e₁ = 0`; substitute step 2 — "Exponent subtraction
gives the monomial ratio" (`EFF.T1.19`). 4. The coboundary consistency: D.12 + D.15 + D.14
(`omega` on exponents).

**SIZE.** 32 lines.

**SOURCE.** `EFF.T1.19` (the boxed `(C5-monomial-ratio)`); `EFF.T1.26` (the first two pinned
HETOW displays are exactly this statement + its residue — consumed at D.27).

**TEETH.** T1 §4.2 check 4 ("guards the `−q(k)` sign") → **Lean theorem** (this node); the A2
consumption regression → D.27 + §12.

**ENVIRONMENT.** ENV-D1 + ENV-D2.

---

### NODE D.20 [lemma] [fresh]

**STATEMENT.** *`(C1-general)`: the letter factorization.* In any arena `A` over `(G, K, N)`:
for `a b c : G` of EQUAL height (`v a = v b = v c`), writing the three value-zero ratios
`z := res(a·c⁻¹)`, `η' := res(a·b⁻¹)`, `ρ := res(b·c⁻¹)`:
`z = η' · ρ`. Instantiated at `a := Φ_i^{e_{i+1}}`, `b := n̂_i(u_{i+1})`, `c := π_{i+1}^{u_{i+1}}`
(all of height `u_{i+1}` — `EFF.T1.02`'s stage typing) this is
`z_{i+1} = η_{i+1}·ρ_i` (`EFF.T1.05`). **Fences transcribed:** "No arbitrary-depth
canonical-letter monomial assertion follows from the T1 carrier"; the specialization
`ρ_i = J_i(z₁,…,z_i)` `(C1-JA-specialization)` requires the external `(H-JA-CONJ)_i` — an
inline hypothesis of any consumer (D-H10), NOT stated or proved here.

**SIGNATURE.**
```lean
theorem GaugeArena.res_ratio_factor {G K N} [CommGroup G] [Field K]
    (A : GaugeArena G K N) (a b c : G) (hab : A.v a = A.v b) (hbc : A.v b = A.v c) :
    A.res ⟨a * c⁻¹, by …⟩ = A.res ⟨a * b⁻¹, by …⟩ * A.res ⟨b * c⁻¹, by …⟩
-- the three membership side goals are `map_mul`/`map_inv` + the height equalities;
-- the stub spells them as explicit `mem_ker` arguments, not tactic holes
```

**DEPENDS.** D.07.

**PROOF.** `a·c⁻¹ = (a·b⁻¹)·(b·c⁻¹)`; `map_mul` on `res`. "The three defining fractions have
value zero, and residue multiplicativity gives `z_{i+1} = η_{i+1}ρ_i`" (`EFF.T1.05`,
verbatim).

**SIZE.** 16 lines.

**SOURCE.** `EFF.T1.05` (the boxed `(C1-general)` + the R2-1 fence + `(C1-JA-specialization)`);
`EFF.T1.04` (the definitions of `η_{i+1}`, `z_{i+1}`, `z₁ := η`).

**TEETH.** T1 §7 attack 1 (no dedicated battery row — the fence IS the tooth: a consumer
deriving depth-monomiality from this node alone is the defect the R2-1 withdrawal killed) →
§12 signed row.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---
### NODE D.21 [lemma] [fresh]

**STATEMENT.** *`(C1-level-2)`: the level-2 letter in level-1 letters.* With
`π₂ := x^{ℓ₁}π^{ℓ′₁}` where `ℓ₁·h + ℓ′₁·e₁ = 1`, `0 ≤ ℓ₁ < e₁` (i.e. `ℓ₁ = iexp e₁ h 1`,
`ℓ′₁ = aexp e₁ h 1` — D.13 at `k = 1`), the level-1 ratio
`ρ₁ = res(n̂₁(u₂)·π₂^{−u₂})` evaluates to `η^{−⌊ℓ₁u₂/e₁⌋}`; hence by D.20's factorization
`z₂ = η₂ · z₁^{−⌊ℓ₁u₂/e₁⌋}` (`z₁ = η`, `(C1-base-letter)`).

**SIGNATURE.**
```lean
theorem levelOne_rho (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (u₂ : ℤ) (hu : 0 ≤ u₂) :
    (levelOneArena e₁ h he hcop η).res
      ⟨(levelOneSection e₁ h).n u₂ * ((varpiSection e₁ h).n u₂)⁻¹, by …⟩
      = η ^ (-((iexp e₁ h 1 * u₂) / e₁))
-- ⚠ here `varpiSection` is REUSED with `ϖ := π₂ = n̂₁(1)`: `π₂^{u₂}` is the `u₂`-th power of
-- the height-1 normalizer, so the LHS is D.19's `chi` at `k = u₂` — the whole lemma is
-- D.19 + the arithmetic identity `qexp e₁ h u₂ = ⌊ℓ₁u₂/e₁⌋` (with `ℓ₁ = i₀`), `zpow` form
```

**DEPENDS.** D.13, D.15, D.19, D.20.

**PROOF.** 1. `π₂ = n̂₁(1)` by D.13 at `k = 1` (the corpus's `ℓ₁h + ℓ′₁e₁ = 1, 0 ≤ ℓ₁ < e₁`
IS the exact-height spec at height 1). 2. D.19 gives residue `η^{−qexp u₂}`. 3.
`qexp e₁ h u₂ = (i₀u₂ − iexp u₂)/e₁ = ⌊i₀u₂/e₁⌋` since `iexp u₂ = i₀u₂ − e₁⌊i₀u₂/e₁⌋`
(D.13's reduction, the `EFF.T1.06` derivation "`i(u) = ℓ₁u − e₁⌊ℓ₁u/e₁⌋`"). 4. The `z₂`
display is D.20 applied at the stage triple — recorded as the named corollary in the same
file.

**SIZE.** 26 lines.

**SOURCE.** `EFF.T1.06` (the boxed `(C1-level-2)` `z₂ = η₂z₁^{−⌊ℓ₁u₂/e₁⌋}` + its
derivation); `EFF.T1.31` SPAN PIN 1 (the A7 GENTOW2 pin is this display verbatim — the
OUT-interface: chapter C's GENTOW2 layer consumes this node by name).

**TEETH.** T1 §7 attacks 1 and 8 → §12; the GENTOW2 `S5.1` consumer pin (grep count 42) →
the statement-level edge recorded at §11.

**ENVIRONMENT.** ENV-D1 + ENV-D3.

---

### NODE D.22 [lemma] [fresh]

**STATEMENT.** *`(C4-origin)`: the modular-origin comparison.* For `e ℓ β : ℤ` with `e > 0`
and a unit `z : Kˣ` (any group element — stated over `CommGroup`): put
`s_min(β) := (ℓ·β) % e`, `t_min(β) := (ℓ·β − s_min(β))/e`, `ε(β) := z^{−t_min(β)}`. If
`s_act = s_min(β) + ν·e` with `ν : ℕ`, and `t_Def := (s_act − ℓ·β)/e`, then
`z^{t_Def} = z^ν · ε(β)`, i.e. `ε(β) = z^{t_Def − ν}`; and **raw equality
`z^{t_Def} = ε(β)` holds exactly when `z^ν = 1`** — "it holds in particular when `ν = 0`"
(the exact root-of-unity criterion, `EFF.T1.32`'s "JA-EPS-CORR is absorbed verbatim in (C4),
including the exact root-of-unity criterion `z^ν = 1`").

**SIGNATURE.**
```lean
theorem c4_origin {G : Type*} [CommGroup G] (z : G) (e ℓ β : ℤ) (he : 0 < e)
    (ν : ℕ) (s_act : ℤ) (hs : s_act = (ℓ * β) % e + ν * e) :
    z ^ ((s_act - ℓ * β) / e) = z ^ (ν : ℤ) * z ^ (-((ℓ * β - (ℓ * β) % e) / e))
-- sibling (public, same file): `c4_origin_raw_iff : z ^ t_Def = ε(β) ↔ z ^ (ν : ℤ) = 1`
```

**DEPENDS.** none beyond mathlib `Int.emod_emod_of_dvd`/`Int.ediv` arithmetic + `zpow` laws.

**PROOF.** "Substitute `s_act = s_min + νe` into `t_Def = (s_act − ℓβ)/e` to obtain
`t_Def = ν − t_min`, then exponentiate by `z`" (`EFF.T1.16`, verbatim). In Lean:
`t_Def = ν − t_min` by `omega`-grade `Int` division arithmetic (the divisions are exact:
`e ∣ ℓβ − s_min` by `Int.emod`, `e ∣ s_act − ℓβ` from `hs`); then `zpow_add`/`zpow_neg`. The
iff: cancel `ε(β)`.

**SIZE.** 24 lines.

**SOURCE.** `EFF.T1.16` (the boxed `(C4-origin)` + the raw-equality clause); `EFF.T1.29`
(the A5 pin `z^{t_Def} = z^ν ε(β)` — the GENTOW-4.1(c)/S3 gauge input: OUT-interface to
chapter C).

**TEETH.** T1 §4.2 check 3; §7 attacks 1 and 6 → Lean theorem (this node) + §12.

**ENVIRONMENT.** ENV-D2 (`z` in any `CommGroup` — the corpus's `z ∈ K^×` instance follows).

---

### NODE D.23 [lemma] [fresh]

**STATEMENT.** *`(C4-support)`: support transport under the JA conjugation.* Let `K` be a
field and `H P Q : K[y]` nonzero with — **the inline hypothesis `(H-JA-RES-CONJ)`, exactly
the corpus's supplier interface, never proved here** — `H = y^ν * Q` and `P = C a * Q.comp (C b * y)`
for units `a b : Kˣ`. Then `H.support = ν + P.support` (as sets/`Finset`s, elementwise shift)
and `H.natDegree = P.natDegree + ν`. "Neither the polynomial identities nor their support
consequences follow from `(C4-origin)` alone" — the two C4 lemmas are deliberately separate
nodes with separate hypotheses.

**SIGNATURE.**
```lean
theorem c4_support {K : Type*} [Field K] {H P Q : Polynomial K} (hH : H ≠ 0) (hQ : Q ≠ 0)
    (a b : Kˣ) (ν : ℕ)
    (hHQ : H = Polynomial.X ^ ν * Q)
    (hPQ : P = Polynomial.C (a : K) * Q.comp (Polynomial.C (b : K) * Polynomial.X)) :
    H.support = P.support.map (addLeftEmbedding ν)
    ∧ H.natDegree = P.natDegree + ν
```

**DEPENDS.** mathlib `Polynomial.support_C_mul` (unit), `Polynomial.natDegree_comp`,
`Polynomial.support_X_pow_mul` — names verified at stub time.

**PROOF.** "Multiplication by `y^ν` translates support; multiplication by a unit and
substitution by a unit preserve it" (`EFF.T1.17`, verbatim). 1. `Supp(y^ν Q) = ν + Supp Q`.
2. `Supp(C a · Q.comp(C b · y)) = Supp Q`: coefficientwise, `coeff j ↦ a·b^j·coeff j`, a unit
multiple per degree. 3. Degrees add.

**SIZE.** 28 lines.

**SOURCE.** `EFF.T1.17` (the boxed `(C4-support)`, the named `(H-JA-RES-CONJ)` hypothesis
displayed, the non-consequence fence — "sole live C4-support after R2-2/R12-5/R13-2").

**TEETH.** T1 §4.2 check 3; §7 attacks 1 and 6 → Lean theorem (this node); the R2-2
withdrawal (the UNFENCED base support claim) is the mutation this node's explicit
hypothesis kills.

**ENVIRONMENT.** ENV-D3.

---

### NODE D.24 [def] [fresh]

**STATEMENT.** *`(C6-lift)`: the exact lift, point-free.* Over the bundle (`ENV-D4`), for
`e₁ h f₁ : ℕ`, a residue section `σ : ResidueField O → O` (with `residue ∘ σ = id`,
`σ 0 = 0` — hypotheses of the property lemmas, not of the def), a height `M : ℕ` and a
coordinate vector `λ : Fin f₁ → ResidueField O`:

`liftC6 e₁ h σ M λ := Σ_{r : Fin f₁} C (σ (λ r) * π ^ (aexp e₁ h M − r·h).toNat) * X ^ (iexp e₁ h M + e₁·r)`

— the corpus's `L_M(λ) = Σ_r λ̃_r x^{i(M)+e₁r} π^{a−rh}` on coordinates in the basis
`1, η, …, η^{f₁−1}` (`EFF.T1.20`). The `ξ`-evaluation clause `(C6-residue)` is transcribed
point-free at D.26 (`γ ∘ L = id` on coordinates); the tower-point/embedding form is chapter
C's carrier (§4 design note).

**SIGNATURE.**
```lean
noncomputable def liftC6 (e₁ h : ℕ) (σ : ResidueField O → O) (M : ℕ)
    (l : Fin f₁ → ResidueField O) : Polynomial O :=
  ∑ r : Fin f₁,
    Polynomial.C (σ (l r) * π ^ (aexp e₁ h M - r * h).toNat)
      * Polynomial.X ^ (iexp e₁ h M + e₁ * r)
```

**DEPENDS.** D.13.

**PROOF.** definitional. (`(aexp M − rh).toNat` is exact on the live domain `M > D′h` —
D.25 proves `0 ≤ aexp M − rh` there; below the live domain the def is junk and NO lemma
reads it: "A full integral `K₁`-digit slot is asserted below only on the proved live domain
`k > D′h`. No full `K₁`-slot is asserted at `k ≤ D′h`" — `EFF.T1.01`, transcribed as the
absence of any sub-domain lemma.)

**SIZE.** 14 lines.

**SOURCE.** `EFF.T1.20` (the boxed `(C6-lift)` with the fixed residue section
`σ : F_Q → Ô`, `res(σ(a)) = a`, `σ(0) = 0`); `EFF.T1.30` (the A6/GENTOW6 lift pin is this
display + D.25's support clause).

**TEETH.** T1 §4.2 checks 1, 7, 10 → D.25 + gates.

**ENVIRONMENT.** ENV-D4 (+ `f₁` as a section variable; no `Finite` instance — nothing
counts).

---

### NODE D.25 [lemma] [fresh]

**STATEMENT.** *`(C6-lift)` properties on the live domain.* Under `hσ : ∀ a, residue O (σ a) = a`,
`hσ0 : σ 0 = 0`, `hπ : Irreducible π`, `he : 0 < e₁`, `hcop : Nat.Coprime h e₁`,
`hf : 0 < f₁`, and the **live-domain hypothesis** `hM : e₁ * f₁ * h < M`:

1. **integrality exponents:** `∀ r : Fin f₁, 0 ≤ aexp e₁ h M − r·h` (so D.24's `toNat` is
   exact) and **degree:** `(liftC6 …).natDegree < e₁ * f₁` (`= D′`);
2. **exact height** (`λ ≠ 0`): `suppVal X (liftC6 e₁ h σ M l) h e₁ = (M : ℕ∞)` — the
   `(u,ℓ) = (h,e₁)` cleared support value IS the corpus's `dv₁` (chapter B's B.14 at
   `φ = X`); and `liftC6 … 0 = 0` (empty support, valuation `⊤`);
3. **x-support:** `(liftC6 …).support = {iexp M + e₁·r : r < f₁, l r ≠ 0}` (the A6/GENTOW6
   support pin, `EFF.T1.30`);
4. **x-free criterion `(C6-x-free)`** (`l ≠ 0`): `liftC6 …` is a monomial in `π` alone
   (`natDegree = 0` with a single support point `0`) **iff** `iexp e₁ h M = 0` and
   `∀ r ≠ 0, l r = 0`.

**SIGNATURE.**
```lean
theorem liftC6_spec (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → ResidueField O) (hl : l ≠ 0) :
    (liftC6 (O := O) (π := π) e₁ h σ M l).natDegree < e₁ * f₁
    ∧ Uniformity.Density.Leaf.suppVal Polynomial.X (liftC6 e₁ h σ M l) h e₁ = (M : ℕ∞)
-- clauses 3–4 are sibling public lemmas `liftC6_support`, `liftC6_xfree` in the same file
-- (SPLIT MANDATED → 2: `D25a` = clauses 1–2, `D25b` = clauses 3–4)
```

**DEPENDS.** D.13, D.24 · B.07/B.08 (`gaussVal`, `le_gaussVal_iff`), B.11 (`npHgt`), B.14
(`suppVal`), B.15 (`npHgt_X`) · mathlib `Polynomial.natDegree_sum_le`-cluster.

**PROOF.** The corpus's own four steps (`EFF.T1.20`'s derivation, verbatim in substance):
1. `i + e₁r ≤ D′ − 1` and `a − rh ≥ 0`: from `M > D′h`, `iexp < e₁`, `r < f₁` — `omega`
   after D.13's identity (`a·e₁ = M − ih > D′h − (e₁−1)h ≥ e₁(f₁−1)h` ⇒ `a ≥ (f₁−1)h + 1`
   when `h > 0`; the `h = 0` degenerate is excluded by `hcop` + `hM` arithmetic — the stub
   checks this corner: `h ≥ 1` per `EFF.T1.01`'s carrier, carried as a hypothesis if `omega`
   needs it. ⚠ carry `hh : 0 < h` explicitly — flagged for the cross-read, §13 item 6).
2. Exact height: every present term has `(h,e₁)`-weight `e₁·(a−rh) + h·(i+e₁r) = ae₁+ih = M`
   exactly (nonzero coefficient representatives are units: `hσ` + `residue`-unit criterion);
   distinct `x`-exponents (distinct `r` give distinct `i+e₁r < D′`) prevent cancellation —
   coordinatewise, no `ι_θ` needed (the point-free payoff).
3. Support: the same distinctness.
4. x-free: "Distinct nonnegative `x` exponents prove the x-free equivalence" — the single
   support point is `iexp M + e₁r₀` for the unique nonzero coordinate; it is `0` iff
   `iexp M = 0 ∧ r₀ = 0`.

**SIZE.** 55 lines. **SPLIT MANDATED → 2** (D25a/D25b as in the SIGNATURE).

**SOURCE.** `EFF.T1.20` (all four boxed clauses + derivation); `EFF.T1.30` (the A6 support
display `Supp_x L_M(λ) = {i(M)+e₁r : λ_r ≠ 0}` and the zero/nonzero split); `EFF.T1.25`
(A1 row 1: `GENHN-LIFT` is "**Verbatim** on `M > D′h`: same component formula, integrality,
degree, exact height, and residue" — the OUT-interface: this node + D.26 are what
`GENHN-LIFT` consumers get).

**TEETH.** T1 §4.2 checks 1, 7, 10 → **Lean theorem** (this node); the A1/A6 consumption
regressions → §12 (retained; PARI-side).

**ENVIRONMENT.** ENV-D4.

---

### NODE D.26 [def+lemma] [fresh]

**STATEMENT.** *`(C5-gamma)`, point-free, and `γ ∘ L = id`.* (i) The **normalized coordinate
read**: for `A : Polynomial O`, a height `k : ℕ`, and `t : Fin f₁`, with `j := iexp e₁ h k + e₁·t`
and `w := (k − j·h) / e₁ : ℤ` (the exact π-exponent making slot `j` height-`k`):
`gammaCoord e₁ h f₁ k A t := if 0 ≤ w then digAt π w.toNat (A.coeff j) else 0` — B.21's
digit at the height; the corpus's `res(a_{i+e₁t} π^{−(k−(i+e₁t)h)/e₁})` (junk `0` at `w < 0`,
where the corpus's term "vanishes"; and slots `j ≥ D′` read the zero coefficient). The
assembled `K₁`-element `γ_k(A) = Σ_t gammaCoord·η^t` is a two-line corollary for any carrier
`(K₁, η, basis)` and is NOT a separate public name. (ii) **The residue identity, point-free
`(C6-residue)`:** on the live domain, `gammaCoord e₁ h f₁ M (liftC6 e₁ h σ M l) t = l t` for
every `t`.

⚠ **What stays with chapter C:** the `ξ`-evaluation forms `(C5-normalizer-read)`
`res(A(ξ)/n(k)(ξ)) = ι_ξ(γ_k(A))` and `(C5-varpi-read)` `res(A(ξ)/ϖ(ξ)^k) = ι_ξ(γ_k(A))·η_ξ^{−q(k)}`
quantify over tower points with compatible embeddings (`res(ξ^{e₁}/π^h) = ι_ξ(η)`), a valued
extension carrier `leanfinal` does not have (GC-7). They are the embedding interface
`EFF.T1.18 [supplied-by: chapter C]`; the `η^{−q(k)}` factor is D.19's, so C's discharge is
this node + D.19 + its own point carrier. The HE6 F-1 provenance ("normalized slot
coefficients in LEMMA HE6-0″", grep count 1) rides the same placeholder.

**SIGNATURE.**
```lean
noncomputable def gammaCoord (e₁ h f₁ : ℕ) (k : ℕ) (A : Polynomial O) (t : Fin f₁) :
    ResidueField O :=
  let j := iexp e₁ h k + e₁ * t
  let w : ℤ := ((k : ℤ) - j * h) / e₁
  if 0 ≤ w then Uniformity.Density.Leaf.digAt π w.toNat (A.coeff j) else 0

theorem gammaCoord_liftC6 (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hh : 0 < h)
    (hf : 0 < f₁) (hcop : Nat.Coprime h e₁) (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → ResidueField O) (t : Fin f₁) :
    gammaCoord (π := π) e₁ h f₁ M (liftC6 e₁ h σ M l) t = l t
```

**DEPENDS.** D.13, D.24, D.25 (clause 1's exponent facts) · B.21 (`digAt`), B.22 (`digAt_eq`,
`digAt_eq_zero_iff`).

**PROOF.** 1. The coefficient of `X^{iexp M + e₁t}` in `liftC6` is the single summand
`σ(l t)·π^{aexp M − th}` (distinct exponents, D.25 step 3). 2. The slot exponent:
`(M − (iexp M + e₁t)h)/e₁ = aexp M − th` — exact by D.13's identity (`omega`). 3.
`digAt π (aexp M − th) (σ(l t)·π^{aexp M − th}) = residue (σ (l t)) = l t` — B.22's
`digAt_eq` + `hσ`. This is the corpus's "Direct division turns each tying term into its
normalized coefficient residue" (`EFF.T1.18`), run on coordinates.

**SIZE.** 40 lines. Split candidate (def / theorem).

**SOURCE.** `EFF.T1.18` (the boxed `(C5-gamma)`; the two read displays → the ⚠ interface);
`EFF.T1.20` (`(C6-residue)` — this is its point-free content); `EFF.T1.30` (A6: "C5-gamma
and its two reads prove the scalar pin" — the GENTOW-6.3 OUT-interface).

**TEETH.** T1 §4.2 check 4; §7 attack 2 → **Lean theorem** (the identity); the `ξ`-read
half → chapter-C placeholder, recorded in §11's edges.

**ENVIRONMENT.** ENV-D4.

---

### NODE D.27 [lemma] [fresh]

**STATEMENT.** *The A2/HETOW consumption check — T1's side of it.* The T1-side content of
`EFF.T1.26`'s effective check "`(H-HETOW-LOCAL)` + `(C5-monomial-ratio)` + `(C5-carry)` ⟹
the three pinned HETOW displays" is the **binary-carry composite law**: for `a b u₂ : ℤ` and
a carry bit `c₂ ≤ 1`:
`qexp (a + b − c₂·u₂) = qexp a + qexp b + wrap a b − c₂·(qexp u₂ + wrap (a + b − c₂·u₂) u₂)`
— "Two applications of C5-carry in the two binary cases" (`EFF.T1.26`'s derivation,
verbatim). The first two pinned displays are D.19 verbatim (the monomial ratio and its
residue); the third pin's exponent is this law read through the supplier's identification.
**The supplier interface** — the level-two bridge `n̂₂(k)/n₂(k) = n̂(m(k))/ϖ^{m(k)}`, the
function `m`, `0 ≤ s(a) < e₂`, `c₂ᴴᴱᵀ = ⌊(s(k)+s(k′))/e₂⌋ ∈ {0,1}`, and the identification
of `τ` — is `(H-HETOW-LOCAL)`, "external and essential": `EFF.HETOW [supplied-by: chapter C]`;
this node does NOT state it, and the assembled three-display conclusion is chapter C's to
fire with this node + D.19 as the T1 legs. Non-import transcribed: "T1 does not absorb
HETOW-4(c)–(d). The side-assembly brackets, telescoping coefficient identity, side-letter
equality, routing transport, and common refinement polynomial remain HETOW/HE7 supplier
conclusions."

**SIGNATURE.**
```lean
theorem qexp_binary_carry (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    (a b u₂ : ℤ) (c₂ : ℕ) (hc : c₂ ≤ 1) :
    qexp e₁ h (a + b - c₂ * u₂)
      = qexp e₁ h a + qexp e₁ h b + wrap e₁ h a b
        - c₂ * (qexp e₁ h u₂ + wrap e₁ h (a + b - c₂ * u₂) u₂)
```

**DEPENDS.** D.14, D.15.

**PROOF.** `interval_cases c₂`. Case `c₂ = 0`: D.15. Case `c₂ = 1`: apply D.15 to the pair
`(a+b−u₂, u₂)` (whose sum is `a+b`) and to `(a,b)`; solve the linear system (`omega`).

**SIZE.** 18 lines.

**SOURCE.** `EFF.T1.26` (the three pinned displays, the boxed effective check, the supplier
interface `0 ≤ s(a) < e₂`, `c₂ᴴᱟᵀ ∈ {0,1}`, the binary-carry conditionality "the linear
carry formula is asserted only for the binary carry", and the HETOW-4(c)–(d) non-import).

**TEETH.** T1 §7 attacks 5 and 8 → §12; the third-pin display itself → chapter-C placeholder
edge (§11).

**ENVIRONMENT.** ENV-D1.

---

### NODE D.28 [lemma] [fresh]

**STATEMENT.** *`(C3-level-1-key)` — the A3 pin, and the naive/corrected comparison.* Fix a
carrier `(K₁, η)` with an `F`-basis `b : Basis (Fin f₁) F K₁`, `b r = η^r` (the corpus's
fixed basis `1, η, …, η^{f₁−1}`, `EFF.T1.01`), `F := ResidueField O`. For a slot `t < f₂`
with `M_t := (f₂−t)·u₂ > D′h` and a digit `c_t : F ⊆ K₁`:

1. the **corrected level-1 coefficient** is `k̂_t := liftC6 e₁ h σ M_t (b.repr (c_t • η^(Wfloor …)))`
   — the corpus's `k̂_t = L_{M_t}(c_t η^{W(t)})` on coordinates; `c_t ≠ 0 ⇒` exact height
   `M_t` (D.25), `c_t = 0 ⇒ k̂_t = 0` with valuation `⊤` (`hσ0` + `b.repr 0 = 0`) — the A3
   zero branch;
2. the **multiplicative coefficient is exactly `c_t`**: `(c_t·η^{W(t)})·η^{−W(t)} = c_t` —
   in `K₁ˣ`-form, `Γ_t · ((levelOneArena …).vartheta u₂ (f₂−t))⁻¹ = c_t` by D.18 (the A3
   display `c^mult = Γ_t η^{−W(t)} = c_t`);
3. **naive/corrected agreement in slot `t` iff `c_t·(ϑ_{1,f₂−t} − 1) = 0`** (`EFF.T1.13`'s
   criterion — over the field: iff `c_t = 0 ∨ η^{W(t)} = 1`).

**SIGNATURE.**
```lean
theorem levelOne_corrected_key (e₁ h f₁ f₂ : ℕ) (hπ : Irreducible π) …
    {K₁ : Type*} [Field K₁] [Algebra (ResidueField O) K₁] (η : K₁ˣ)
    (b : Basis (Fin f₁) (ResidueField O) K₁) (hb : ∀ r, b r = (η : K₁) ^ (r : ℕ))
    (σ : ResidueField O → O) (hσ : …) (hσ0 : σ 0 = 0)
    (u₂ : ℕ) (t : Fin f₂) (hM : e₁ * f₁ * h < (f₂ - t) * u₂) (c : ResidueField O) :
    (c ≠ 0 → Uniformity.Density.Leaf.suppVal Polynomial.X
        (liftC6 e₁ h σ ((f₂ - t) * u₂)
          (b.repr (algebraMap _ K₁ c * (η : K₁) ^ Wfloor e₁ h u₂ f₂ t))) h e₁
        = (((f₂ - t) * u₂ : ℕ) : ℕ∞))
    ∧ (c = 0 → liftC6 e₁ h σ ((f₂ - t) * u₂)
        (b.repr (algebraMap _ K₁ c * (η : K₁) ^ Wfloor e₁ h u₂ f₂ t)) = 0)
-- clauses 2–3 are sibling public lemmas (`levelOne_cmult`, `levelOne_naive_agree_iff`)
```
⚠ Fragile signature (Basis + repr + algebraMap stack) — elaborate FIRST (§12).

**DEPENDS.** D.16, D.18, D.24, D.25 · mathlib `Basis.repr`, `Finsupp` coercions.

**PROOF.** 1. Clause 1 is D.25 at `l := b.repr (…)` (nonzero iff the element is nonzero —
`Basis.repr` is a linear equiv; zero branch by `map_zero` + `liftC6`'s `hσ0`). 2. Clause 2:
field algebra + D.18. 3. Clause 3: `c·(η^W − 1) = 0 ↔ c = 0 ∨ η^W = 1` in a field
(`mul_eq_zero`, `sub_eq_zero`).

**SIZE.** 45 lines.

**SOURCE.** `EFF.T1.13` (the boxed `(C3-level-1-key)`, "Its multiplicative coefficient is
exactly `c_t`", the agreement criterion `c_t(ϑ_{i,f_{i+1}−t}−1) = 0`); `EFF.T1.27` (the A3
block: both branches + `c^mult = Γ_t η^{−W(t)} = c_t`; "T1 **supplies the gauge input to**
LEMMA GENTOW-1" — the OUT-interface, with `EFF.GENTOW1 [supplied-by: chapter C]` on the
consumer side); `EFF.T1.28` (the A4 block: this node + D.25's x-free clause are "the
corrected-key and x-free inputs to THEOREM GENTOW-3").

**TEETH.** T1 §4.2 checks 1 and 2 → **Lean theorem** (this node); gauge-naive tooth → clause
3 is the exact agreement criterion (the naive recipe is NOT a chapter object — only the
criterion is); §7 attacks 2, 3, 8 → §12.

**ENVIRONMENT.** ENV-D4 + the `(K₁, η, b)` carrier data.

---
## 5. §5 — THE READ BUNDLE AND THE B-LAW

> **Design note.** `EFF.T1.03`'s five clauses are "site obligations … not assertions about
> every homogeneous initial form". The bundle D.29 carries exactly the clauses the B-law
> derivation consumes, at one site (one level `i`, one ladder step `q`), as fields; D.33's
> B-law is then a two-step proof FROM the fields, and the corpus's own non-import — "T1 does
> not prove the supplier identity itself" (`EFF.T1.31`) — is the statement that INSTANTIATING
> the bundle is someone else's theorem (chapter C at `i = 2`; `[GENTOW5-W(i)]` behind
> `𝒲_{≤i}` at `i ≥ 3`; see D.42/D.44/D.62).

### NODE D.29 [def] [fresh]

**STATEMENT.** *The sitewise read bundle.* Over an arena `A : GaugeArena G K N` and a ladder
step `q : ℤ`, a **read bundle** carries: the site read `R : G → K`; the ladder unit `w : Kˣ`
with its defining read `R (n q) = w` (`(C3-ladder-unit)`: the `Kˣ`-typing carries BOTH
`(C3-read-codomain)` and `(C3-ladder-nonvanishing)` — the two-clause gate of T1 r12, D-H6);
**ladder multiplicativity** `R ((n q)^s) = w^s` (`(C3-ladder-multiplicativity)`); and **graded
scalar covariance** `R (X·g) = R X · res g` for every `X : G` and value-zero `g`
(`(C3-graded-scalar-covariance)` + `(C3-read-codomain)` at the consumed sites).

**SIGNATURE.**
```lean
/-- The sitewise C3 read bundle (`EFF.T1.03`): exactly the clauses the B-law consumes, as
fields. Instantiation = the external supplier's theorem (never proved in chapter D):
`i = 2` — GENTOW2-B′/B″ [supplied-by: chapter C]; `i ≥ 3` — `[GENTOW5-W(i)]` behind
`𝒲_{≤i}` (D.44/D.62) plus `(H-VARTHETA-RES)_i` (D.67). -/
structure ReadBundle {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) where
  R : G → K
  w : Kˣ
  read_n : R (N.n q) = w
  ladder_mult : ∀ s : ℕ, R ((N.n q) ^ s) = (w : K) ^ s
  scalar_cov : ∀ (X : G) (g : (MonoidHom.ker A.v)), R (X * g) = R X * (A.res g : K)
```

**DEPENDS.** D.01, D.07.

**PROOF.** definitional.

**SIZE.** 20 lines.

**FAITHFULNESS.** (i) `(C3-zero-read)` (`R(0) = 0`) has no group-level zero; in this
packaging the zero digit multiplies at the `K` level (D.34's coefficient `u(β_t)·c_t` with
`c_t = 0`), which is exactly the corpus's zero-branch bookkeeping (`EFF.T1.12`'s "For
`c_t = 0`, `k̂_t = 0` and no finite height is assigned") — no consumer of this chapter reads
a zero slice through `R`. Flagged for the cross-read (§13 item 3). (ii) The countermodels the
corpus records for INDEPENDENCE of the clauses ("a read vanishing on every positive-grade
component defeats nonvanishing; the initial-form read into `gr(μ_i)` … defeats the scalar
codomain", `EFF.T1.03`) become the §12 disposition that no field is derivable from the
others — the structure must carry all of them.

**SOURCE.** `EFF.T1.03` (the five boxed clauses, `w_i := R_{i+1,κ̄_i}(N_i)`,
`(C3-ladder-unit)`, the sitewise sentence); `EFF.T5.04` (`(WF-w)` — the same `w`, T5's
naming); `EFF.T5.09` (the per-level nonvanishing suppliers, transcribed at D.61's interface).

**TEETH.** T1 §4.2 checks 5, 8, 9 (read-bundle checks) → carried to instances (gates run
the FRAME-C tables against a concrete bundle, D.72).

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.30 [def+lemma] [fresh]

**STATEMENT.** *The corrected key polynomial and its degree/monicity.* For a commutative ring
`S`, a monic `Φ : S[x]` with `d := Φ.natDegree ≥ 1`, `e f ≥ 1`, and coefficients
`k̂ : Fin f → S[x]` with `∀ t, (k̂ t).natDegree < d` (`(C3-corrected-coefficient-bound)` —
`(C3-lift-coefficient-space)`'s consumed form): the **corrected key**
`correctedKey Φ e f k̂ := Φ^(e·f) − Σ_t k̂ t · Φ^(e·t)` is monic of degree `e·f·d` — "The
coefficient degree bound makes every lower term's degree strictly below the monic leading
term, **including `e_{i+1} = 1`, `t = f_{i+1}−1`**" (`EFF.T1.12`'s derivation, the boundary
case named).

**SIGNATURE.**
```lean
noncomputable def correctedKey {S : Type*} [CommRing S] (Φ : Polynomial S) (e f : ℕ)
    (khat : Fin f → Polynomial S) : Polynomial S :=
  Φ ^ (e * f) - ∑ t : Fin f, khat t * Φ ^ (e * (t : ℕ))

theorem correctedKey_monic {S : Type*} [CommRing S] [Nontrivial S] {Φ : Polynomial S}
    (hΦ : Φ.Monic) (hd : 0 < Φ.natDegree) {e f : ℕ} (he : 0 < e) (hf : 0 < f)
    {khat : Fin f → Polynomial S} (hdeg : ∀ t, (khat t).natDegree < Φ.natDegree) :
    (correctedKey Φ e f khat).Monic
    ∧ (correctedKey Φ e f khat).natDegree = e * f * Φ.natDegree
```

**DEPENDS.** mathlib `Polynomial.Monic.pow`, `Polynomial.natDegree_sum_le`,
`Monic.natDegree_mul`-cluster.

**PROOF.** 1. Each lower term: `natDegree (k̂ t · Φ^{et}) ≤ (d−1) + e·t·d ≤ (d−1) + e(f−1)d
< e·f·d` (`omega` from `he, hf, hd`). 2. `Monic.sub_of_left`-shape: a monic minus a
strictly-lower-degree sum is monic of the same degree.

**SIZE.** 26 lines.

**SOURCE.** `EFF.T1.12` (the boxed `(C3-key)` and the degree derivation). The height clause
`(C3-common-height)` `dv_i(k̂_t Φ_i^{e_{i+1}t}) = f_{i+1}u_{i+1}` for `c_t ≠ 0` is the
arithmetic `(f−t)u + tu = fu` on the typed heights of `EFF.T1.02` — recorded here as a
one-line private lemma over `ℤ`, not a public node (the level-`i` valuation carrier that
would TYPE it is chapter C's; at level 1 it is D.25's exact-height clause, already proved).
`(C3-corrected-lift)`'s lift-contract clauses (`(C3-lift-residue/height/zero)`) are
level-carrier statements: at level 1 they are D.24–D.26 (proved); at level `i ≥ 2` they are
`EFF.T1.02` hypothesis data `[supplied-by: chapter C]`.

**TEETH.** T1 §4.2 checks 7–10 → the level-1 instance (D.28) + gates; the degree lemma is a
Lean theorem here.

**ENVIRONMENT.** ENV-D3 (stated over `CommRing S` — consumed at `S = O` and at chapter C's
level rings).

---

### NODE D.31 [lemma] [fresh]

**STATEMENT.** *`(C3-dictionary)`.* For `Γ c : K` and a unit `ϑ : Kˣ`:
`Γ = c * ϑ ↔ c = Γ * ϑ⁻¹` — the coherent/multiplicative digit dictionary
`Γ_t = c_t^{mult}·ϑ_{i,s}`, `c_t^{mult} = Γ_t·ϑ_{i,s}^{−1}`. Stated as an iff so neither
orientation can be consumed without the other being available.

**SIGNATURE.**
```lean
theorem dict_iff {K : Type*} [Field K] (Γ c : K) (ϑ : Kˣ) :
    Γ = c * ϑ ↔ c = Γ * (ϑ⁻¹ : Kˣ)
```

**DEPENDS.** none (field algebra).

**PROOF.** `Units.mul_inv_cancel`-shape; `field_simp`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.T1.11` (the boxed `(C3-dictionary)`; conditionality "`ϑ_{i,s}` must be a
`K_i`-unit under EFF.T1.09" — the `ϑ : Kˣ` argument IS that condition; at `i ≥ 3` supplying
it is `(H-VARTHETA-RES)_i`, D.67); `EFF.T3.05` (`(T1-DICT)`, with T3's fence "T3 does NOT
cite that conditional conclusion [the B-law] as a premise" — respected: this node is
dictionary-only).

**ORIENTATION.** the dictionary pairs GENTOW2-orientation `ϑ(t)`-values with T1's `ϑ_{i,s}`
per D.06; consumers must pass the CORRECT unit (T1's `vartheta` at `s = f−t`, i.e.
`varthetaG2⁻¹`) — the inverse-orientation tooth's site.

**TEETH.** T1 §4.2 checks 2 and 5; inverse-orientation tooth → D.06/D.10 + gate D.72.

**ENVIRONMENT.** ENV-D3.

---

### NODE D.32 [theorem] [fresh]

**STATEMENT.** *`(C3-Theta)`/`(C3-B-law)`: the B-law from the bundle.* Over a bundle
`B : ReadBundle A q`: define the **per-grade unit read** `u_B(s) := B.R (N.n (s·q))` (T5's
`u_i(β_t) := R_{i+1,β_t}(n̂_i(s_t u_{i+1}))`, `EFF.T5.11`). Then for every `s : ℕ`:

`u_B(s) = (A.theta q s : K) * (B.w : K)^s`

— and in slot-indexed form with `s = f_{i+1} − t`: `u(β_t) = Θ_i(t)·w_i^{f_{i+1}−t}`,
**exactly the `(C3-B-law)` orientation** (D.06's B-law block: `FGMN = u · repo`, never the
inverse).

**SIGNATURE.**
```lean
theorem ReadBundle.blaw {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} (B : ReadBundle A q) (s : ℕ) :
    B.R (N.n (s * q)) = (A.theta q s : K) * (B.w : K) ^ s
```

**DEPENDS.** D.04, D.08, D.10, D.29.

**PROOF.** 1. `n(sq) = (n q)^s · thetaEl q s` (D.04's definition rearranged: `thetaEl =
n(sq)·((n q)^s)⁻¹`; `group`). 2. `thetaEl q s ∈ ker v` (D.08's membership lemma, inverse
form). 3. `scalar_cov` at `X := (n q)^s`, `g := thetaEl`: `R(n(sq)) = R((n q)^s)·res(thetaEl)
= w^s · theta` (`ladder_mult`). 4. Commute. This is `EFF.T1.14`'s derivation run forwards
("Ladder multiplicativity gives `R(N^s) = w^s`; scalar covariance … invert the telescope" —
here stated directly in the `Θ` orientation, no inversion step left to the consumer).

**SIZE.** 20 lines.

**SOURCE.** `EFF.T1.14` (the boxed `(C3-Theta)`, `(C3-slot-grade)` — the grade bookkeeping
`β_t = (f_{i+1}−t)·κ̄_i` is carried in the SLOT indexing, not as a separate Lean object —
and `(C3-B-law)`); `EFF.T3.14` is the SAME algebra from port hypotheses (D.38 — see its ⚠
for the deliberate duplication); `EFF.T5.14`'s consequent (D.62 fires this node).

**ORIENTATION.** B-law direction per D.06's B-law block; `theta` = inverse-telescope
orientation (rows 2–3).

**TEETH.** T1 §4.2 check 5 + inverse-orientation tooth → **Lean theorem** (this node);
gate D.72's `U(s) = Θ_s w^s` numeric leg.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.33 [theorem] [fresh]

**STATEMENT.** *`(C3-canonical-read)` and the three-reads cancellation.* Over a bundle `B`
and the dictionary: for slot `t < f` with `s := f − t`, coherent digit `Γ_t = c_t·ϑ_{i,s}`
(D.31, with `ϑ := A.vartheta q s`):

1. **canonical read:** `u_B(s) · Γ_t = (B.w : K)^s · c_t · (A.theta q s) · (A.vartheta q s)
   = w^s·Θ(t)·Γ_t`-form — and by D.10's involution the telescopes cancel slotwise:
   `u_B(s) · Γ_t = c_t · (B.w : K)^s`;
2. **three reads:** hence the assembled residual `y^f − Σ_t u_B(f−t)·Γ_t·y^t` equals
   `y^f − Σ_t c_t·w^{f−t}·y^t` — which is `(WF-psi)`'s display `w^f·ψ(y/w)` for
   `ψ = y^f − Σ c_t y^t` (the polynomial identity is D.58's; this node proves the
   COEFFICIENT identity `u_B(f−t)·Γ_t = c_t·w^{f−t}`).

**SIGNATURE.**
```lean
theorem ReadBundle.canonical_coeff {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} (B : ReadBundle A q) (f t : ℕ) (ht : t < f)
    (c : K) :
    B.R (N.n ((f - t : ℕ) * q)) * (c * (A.vartheta q (f - t) : K))
      = c * (B.w : K) ^ (f - t)
```

**DEPENDS.** D.08, D.10, D.31, D.32.

**PROOF.** D.32 + D.10's `theta_mul_vartheta` (`Units.val`-cast bookkeeping); `ring`.
"At the corrected key, `Γ_t = c_t ϑ` and `Θ = ϑ^{−1}` cancel slotwise" (`EFF.T1.15`,
verbatim).

**SIZE.** 16 lines.

**SOURCE.** `EFF.T1.15` (the boxed `(C3-canonical-read)` and `(C3-three-reads)`: the
multiplicative residual `ψ_{i+1}(y)`, coherent digits `(c_t ϑ_{i,f_{i+1}−t})`, canonical
residual `ψ^{(w_i)}`); `EFF.T5.18` (the same cancellation, T5's `Γ_t u_i(β_t) = c_t w_i^{s_t}`
— D.63 is its packaging); `EFF.T1.31` SPAN PIN 2 (`ψ₃^{(w)} = w^{f₃}ψ₃(y/w)` — supplied to
GENTOW2's A7 span by D.58 + this node).

**ORIENTATION.** consumes both orientations through D.10's involution — the ONE place they
meet; the ⚠ in the file body repeats D.06's warning verbatim.

**TEETH.** T1 §4.2 checks 5, 8, 9 + inverse-orientation tooth → **Lean theorem**; gate D.72.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.34 [def+lemma] [fresh]

**STATEMENT.** *The w-twist `(WF-twist)` and its transport package.* For a unit `w : Kˣ` and
monic `P : K[y]` of degree `f`: `wtwist w P := w^f • P.comp (C (w⁻¹ : K) * X)` — the map
`P(y) ↦ w^{deg P}·P(y/w)`. The **transport package** (one lemma family, this node):
`wtwist w P` is monic of degree `f`; the map transports factorizations bijectively and
preserves degrees, multiplicities, irreducibility, separability, and a nonzero constant term
(`wtwist w P).coeff 0 = w^f · P.coeff 0`); on roots it is `s ↦ w·s`. ("The map
`P(y) ↦ w^{deg P}P(y/w)` transports factorizations bijectively and preserves degrees,
multiplicities, irreducibility, and a nonzero constant term" — `EFF.T1.15`; separability +
the monic factor correspondence `r(Z) = δ^m r̂(Z/δ)` and root map `ŝ ↦ δŝ` — `EFF.T3.18`
`(T3-ROUTE)`; "Unit substitution preserves monicity, degree, irreducibility, nonzero constant
term, and irreducible-factor degrees and multiplicities" — `EFF.T5.08`.)

**SIGNATURE.**
```lean
noncomputable def wtwist {K : Type*} [Field K] (w : Kˣ) (P : Polynomial K) : Polynomial K :=
  (w : K) ^ P.natDegree • P.comp (Polynomial.C (w⁻¹ : K) * Polynomial.X)

theorem wtwist_monic {K : Type*} [Field K] (w : Kˣ) {P : Polynomial K} (hP : P.Monic) :
    (wtwist w P).Monic ∧ (wtwist w P).natDegree = P.natDegree
-- sibling public lemmas (SPLIT MANDATED → 3: D34a def+monic/degree, D34b irreducible/
-- separable/roots, D34c the factor-multiset correspondence `wtwist w (P*Q) = wtwist w P *
-- wtwist w Q` for monic P Q + `map (algEquiv …)` route note)
```
⚠ Route note for the fleet: `P ↦ P.comp (C w⁻¹ * X)` is the `AlgEquiv`
`Polynomial.compAlgEquiv`-shape (substitution by a unit is a `K`-algebra automorphism —
`EFF.T3.18`'s own derivation sentence); irreducibility/separability transport should come
from mathlib's `AlgEquiv`/`Polynomial.Separable.map` machinery, not hand induction. The
monic renormalization `w^{deg P}` is multiplicative BECAUSE degrees add — the factor
correspondence needs `natDegree_mul` under `Monic` (no zero divisors issue in a field).

**DEPENDS.** mathlib `Polynomial.comp`, `Polynomial.Monic.comp`, `Polynomial.Separable.map`,
`Polynomial.roots_smul_nonzero` — exact names at stub time.

**PROOF.** 1. Monic/degree: leading coefficient `w^f · P.leadingCoeff · (w⁻¹)^f = 1`.
2. Multiplicativity on monics: `(PQ).comp = P.comp · Q.comp` + degree additivity. 3.
Irreducible/separable: transport along the substitution automorphism, then the nonzero
scalar. 4. Roots: `(wtwist w P).eval (w·s) = w^f · P.eval s`.

**SIZE.** 50 lines. **SPLIT MANDATED → 3** (as in the SIGNATURE).

**SOURCE.** `EFF.T1.15` (the transport sentence), `EFF.T3.18` (`(T3-ROUTE)` — this node IS
its content, stated once; D.41 is its two-section instance), `EFF.T5.05` (`(WF-twist)` —
same display; §8 consumes this node), `EFF.T5.08` (+ its gate: the preservation list is
"fenced by (C3-ladder-nonvanishing)" — here the `w : Kˣ` argument carries it by type).

**TEETH.** T3 §8.3(2) (HETOW clause (d) "separability/factor/root routing … fully supplied
by (T3-ROUTE)") → **Lean theorem** (this node); T5 §7 Pass 1(1) → §12; honesty: "Turning
factor data into a p-adic splitting type still requires the surrounding tower theorem"
(`EFF.T5.08`) — the D-H4(3) fence, repeated in this node's file docstring.

**ENVIRONMENT.** ENV-D3.

---

### NODE D.35 [lemma] [fresh]

**STATEMENT.** *`(WF-psi)`: the twist coefficients.* For `w : Kˣ` and
`ψ = y^f − Σ_{t<f} c_t y^t` (monic, coefficients `c : Fin f → K`):
`wtwist w ψ = y^f − Σ_{t<f} c_t·w^{f−t}·y^t` — T5's boxed computation, and the polynomial
into which D.33's coefficient identity assembles: the B-law residual
`y^f − Σ u(β_t)c_t^{coh-normalized} y^t` IS `wtwist w ψ` under the multiplicative
prescription.

**SIGNATURE.**
```lean
theorem wtwist_psi {K : Type*} [Field K] (w : Kˣ) (f : ℕ) (c : Fin f → K) :
    wtwist w (Polynomial.X ^ f - ∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ))
      = Polynomial.X ^ f
        - ∑ t : Fin f, Polynomial.C (c t * (w : K) ^ (f - (t : ℕ)))
            * Polynomial.X ^ (t : ℕ)
```

**DEPENDS.** D.34.

**PROOF.** "Substitute … `w^f((y/w)^f − Σ c_t (y/w)^t) = y^f − Σ c_t w^{f−t} y^t`"
(`EFF.T5.06`'s displayed computation): `Polynomial.comp` linearity + `simp` with
`mul_pow`/`inv_pow`; per-coefficient `field_simp`. The degree computation feeding
`wtwist`'s `w^{natDegree}` scalar: `natDegree (X^f − Σ …) = f` (monic by construction —
private helper).

**SIZE.** 24 lines.

**SOURCE.** `EFF.T5.06` (the boxed `(WF-psi)` + its `[COMPUTATION]` derivation; the r4
census's confirmation that T1's `(C3-three-reads)` boxes the same display).

**TEETH.** T5 §7 Pass 1(1)/(6) → Lean theorem (this node); gate D.72 evaluates a `(WF-psi)`
instance numerically.

**ENVIRONMENT.** ENV-D3.

---

<a id="D-C7-TABLE"></a>
### NODE D.36 [table] [fresh] — the C7 package interface and scope fence (anchor `D-C7-TABLE`)

**STATEMENT.** *What T1 supplies to each WELD-M-PKG field — the interface chapter F cites.*
Transcribed from `EFF.T1.22`'s effective C7 table (per-row fences INCLUDED — "the table does
not merge field types"):

| Package field | T1 datum available to that field (Lean home) |
|---|---|
| `M0`, division chains | common tower and canonical division-chain anchor; **no new identity is proved here** |
| `M1` | the unconditional value-zero ratio and level-two letter formula in (C1) — D.20, D.21; arbitrary-depth letter monomiality **only under `(H-JA-CONJ)_i`** (inline, D-H10) |
| `M2` | the dictionary and canonical read in (C3) — D.31, D.32, D.33 — plus (C4-origin) — D.22; support transport **only under `(H-JA-RES-CONJ)`** — D.23. The graded-read bundle consumed, in full: ladder-multiplicativity, slot-grade, scalar-covariance, zero-read, nonvanishing, codomain = D.29's fields (+ D-H3's packaging notes); corrected-key coefficients additionally use the coefficient space — D.30. At depth `i ≥ 3` the scalars `ϑ_{i,s}`, `Θ_i(t)`, `c_tϑ` are `K_i`-scalars **only under `(H-VARTHETA-RES)_i`** — D.67 |
| `M3` | the cocycle/telescope (C2) — D.03, D.05, D.08 — and canonical twist in (C3) — D.34 — only on the scored stratum; at `i ≥ 3` the `K_iˣ`-valued telescope **only under `(H-VARTHETA-RES)_i`** |
| `M4` | the exact-height formulas (C5)–(C6) — D.19, D.24–D.26 — at W2-C3's accepted fence; polygon clearance **only under `(H-GENHN-CLEAR)`** (no D node — D-H4(5)) |

**THE SCOPE FENCE `(C7-scope)`, verbatim:** "T1 organizes five named fields around one tower
cocycle; it proves no cross-face coherence theorem. It also proves no uniqueness of the gauge
and makes no classification of the fiber of gauges having a fixed coboundary." Chapter F's
weld faces cite THIS anchor for what the T-chain supplies; a NODE asking chapter D for a
cross-face compatibility square is a blueprint defect.

**SIGNATURE.** none (a blueprint interface table — no Lean declaration; the B.86-precedent
class of node-with-no-public-decl, here with no file at all: `dag_build.py` accepts edge-less
declared nodes).

**DEPENDS.** D.20–D.23, D.29–D.34 (row targets).

**PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T1.22` (the effective C7 table, all five rows with their fences),
`EFF.T1.23` (`(C7-scope)` + the uniqueness/torsor non-claims).

**TEETH.** T1 §4.2 check 6; §7 attack 4 → §12 (signed rows: interface, nothing to execute).

**ENVIRONMENT.** n/a.

---
## 6. §6 — THE TELESCOPE PORT (T3)

> **Design note (why D.38 exists next to D.32).** T3 deliberately does NOT consume T1's
> conditional B-law: "T3 does **not** cite that conditional conclusion as a premise for
> `[GENTOW5-W(i)]`. Instead, the boundary-read port below discharges the obligation from the
> source's primitive read package" (`EFF.T3.05`). The port hypotheses BR1–BR5 are a DIFFERENT
> (weaker, source-local) interface than D.29's bundle, and the two derivations of the same
> display are the point: D.32 (bundle ⇒ B-law) serves T1's consumers; D.38 (port ⇒ B-law)
> serves the GENTOW2/GENTOW5 discharges without circularity — the §8.4(3)
> "endpoint-as-input" mutant is exactly a consumer who erases this distinction.

### NODE D.37 [def] [fresh]

**STATEMENT.** *The boundary-read port `(BR1)–(BR5)`.* Over an arena `A` at ladder step
`q : ℤ` and exponent `s : ℕ`, a **boundary-read port** carries the source-local read data of
`G := N(q)^s`: the peel unit `w : Kˣ` and peeled read `ctR : K` with **(BR1)**
`ctR = w^s`; the expansion reads `ctRQ : ℕ → K` over a finite support `expSupport : Finset ℕ`
with **(BR2)** `ctR = Σ_{j ∈ expSupport} ctRQ j`; **(BR3)** positive-degree elimination
`∀ j ≠ 0, ctRQ j = 0`; the per-grade factor `U : K` and digit `digit : K` with **(BR4)**
`ctRQ 0 = U * digit`; and **(BR5)** evaluation `digit = (A.vartheta q s : K)`. Fence
transcribed as a NON-field: "These are source-local residual-read hypotheses. **Neither the
B-law nor a one-`w_i` power law is included among them**" (`EFF.T3.11`) — the structure has
no B-law field, and adding one is the §8.4(3) mutant.

**SIGNATURE.**
```lean
structure BoundaryReadPort {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (s : ℕ) where
  w : Kˣ
  ctR : K
  ctRQ : ℕ → K
  expSupport : Finset ℕ
  br1 : ctR = (w : K) ^ s
  br2 : ctR = ∑ j ∈ expSupport, ctRQ j
  br3 : ∀ j ≠ 0, ctRQ j = 0
  U : K
  digit : K
  br4 : ctRQ 0 = U * digit
  br5 : digit = (A.vartheta q s : K)
```

**DEPENDS.** D.07, D.08.

**PROOF.** definitional.

**SIZE.** 22 lines.

**FAITHFULNESS.** BR2's `Σ_{j≥0}` (infinitely indexed, finitely supported) is carried as an
explicit `Finset` support — the corpus's `Φ_i`-adic expansion is finite by degree. BR4's
"`Q₀` has exact grade `β_s`" is carried IN `br4`'s shape (the read factors through `U·digit`
exactly when the grade is exact — the corpus's own reading); the exactness itself is the
supplier's obligation when constructing the port.

**SOURCE.** `EFF.T3.06` (the port declaration: expansion + `ct`), `.07` (BR1 peel + `w_i`),
`.08` (BR2 expansion), `.09` (BR3), `.10` (BR4 exact constant digit + `U_i(β_s)`), `.11`
(BR5 + the non-circularity fence).

**TEETH.** T3 §8.1(4) ("no conditional B-law input") and §8.4(3) ("endpoint-as-input
mutant") → the structure's field list IS the tooth (no B-law field); §12.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.38 [theorem] [fresh]

**STATEMENT.** *`(T3-BR)`: the boundary-read telescope.* For a port `P : BoundaryReadPort A q s`:
`P.U = (A.theta q s : K) * (P.w : K)^s`. ("Under (BR1)–(BR5), `U_i(β_s) = Θ_N(s;q)·w_i^s`."
The endpoint equation is DERIVED, never supplied — "its two sides arose independently from
the peeled read of `N(q)^s` and the coherent digit of the surviving constant coefficient.")

**SIGNATURE.**
```lean
theorem BoundaryReadPort.t3_br {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {s : ℕ} (P : BoundaryReadPort A q s) :
    P.U = (A.theta q s : K) * (P.w : K) ^ s
```

**DEPENDS.** D.08, D.10, D.37.

**PROOF.** T3's four displayed steps, verbatim (`EFF.T3.14`'s `[VERBATIM]` derivation):
1. `ctR = w^s` (br1). 2. `ctR = ctRQ 0`: br2 + br3 collapse the sum — if `0 ∉ expSupport`
the sum is `0`, contradicting `w^s ≠ 0` (unit), so `0 ∈ expSupport` and
`Finset.sum_eq_single_of_mem`. 3. `ctRQ 0 = U·ϑ` (br4 + br5). 4. `w^s = U·ϑ`, hence
`U = ϑ⁻¹·w^s = Θ·w^s` (D.10's involution; `Units.eq`-division in `K`).

**SIZE.** 20 lines.

**SOURCE.** `EFF.T3.14` (the boxed `(T3-BR)` + the verbatim proof + the endpoint
non-supply sentence).

**ORIENTATION.** conclusion in the B-law orientation (D.06 rows 2–3); the `ϑ⁻¹` step is the
recorded inverse orientation of T3 §8.1 check 2 (D.10).

**TEETH.** T3 §8.3(1)/(3) (GENTOW2-B″/GENTOW5-W legs), §8.4(2) (theta-free mutant), §8.4(3),
§8.4(4) → **Lean theorem** (this node); gate D.72 runs the FRAME-C `U/ϑ` tables against it.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.39 [def] [fresh]

**STATEMENT.** *The two-section comparison data.* Over an arena `A : GaugeArena G K N` and a
SECOND exact-height section `N̂` for the SAME height hom (`hNhat : ∀ k, A.v (N̂.n k) =
Multiplicative.ofAdd k` — `EFF.T3.12`'s "two normalized exact-height sections on the same
set of heights"): the `K`-valued ratio `chiK k := A.res ⟨chi N̂ N k, _⟩` (membership: heights
cancel), `δ := chiK q`; and for descent data `H₀ q : ℤ`, `D : ℕ`, `Acoef : Fin (D+1) → G`
with exact heights `hA : ∀ t, A.v (Acoef t) = ofAdd (H₀ − t·q)` (`EFF.T3.13`'s "`A_t` has
height `H_t`"): the assembled coefficients
`rho t := A.res ⟨Acoef t * (N.n q)^t * (N.n H₀)⁻¹, _⟩` and
`rhoHat t := A.res ⟨Acoef t * (N̂.n q)^t * (N̂.n H₀)⁻¹, _⟩`, and the two polynomials
`Rpoly := Σ_t (rho t) Z^t`, `RpolyHat := Σ_t (rhoHat t) Z^t` — "All displayed residual
quotients have height zero."

**SIGNATURE.**
```lean
noncomputable def compData {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k, A.v (Nhat.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (D : ℕ) (Acoef : Fin (D + 1) → G)
    (hA : ∀ t, A.v (Acoef t) = Multiplicative.ofAdd (H₀ - t * q)) :
    (Fin (D + 1) → Kˣ) × (Fin (D + 1) → Kˣ) × Kˣ
-- packaged `(rho, rhoHat, δ)`; the two polynomials are `∑ t, C ((rho t : K)) * X ^ (t : ℕ)`
-- shapes formed at the consumers (D.40) — no separate public name
```
⚠ Fragile signature (kernel-membership proof terms inside a `def`) — elaborate FIRST (§12);
the membership lemmas are private helpers with explicit statements, not tactic holes.

**DEPENDS.** D.01, D.07, D.12.

**PROOF.** definitional; the three membership facts are `map_mul`/`map_pow`/`map_inv` +
`hNhat`/`hA`/`exact_height` + `omega` on exponents.

**SIZE.** 34 lines.

**SOURCE.** `EFF.T3.12` (χ, δ, the renaming fence), `EFF.T3.13` (`H_t = H₀ − tq`,
`ρ_t`, `ρ̂_t`, `R(Z)`, `R̂(Z)`, `δ = χ(q)`, the height-zero clause).

**TEETH.** T3 §8.2 (the port frames) → gate D.72 instantiates this data at FRAME-C's
`p = 5` tables.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.40 [theorem] [fresh]

**STATEMENT.** *`(T3-CMP)`: the assembled comparison.* With D.39's data:
`(rho t : K) = (rhoHat t : K) * (chiK H₀ : K) * ((δ : K))⁻¹ ^ (t : ℕ)` for every `t`, and
the polynomial identity `Rpoly = C (chiK H₀ : K) * RpolyHat.comp (C ((δ : K))⁻¹ * X)` —
"`R(Z) = χ(H₀)·R̂(Z/δ)`".

**SIGNATURE.**
```lean
theorem compData_cmp {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G) (hNhat : …) (H₀ q : ℤ) (D : ℕ)
    (Acoef : Fin (D + 1) → G) (hA : …) (t : Fin (D + 1)) :
    ((compData A Nhat hNhat H₀ q D Acoef hA).1 t : K)
      = ((compData …).2.1 t : K) * ((compData …).2.2 : K)⁻¹ ^ (t : ℕ)
          * (chiK-of-H₀-term)
-- the polynomial identity is the sibling public lemma `compData_cmp_poly`
-- (the exact spelled signature is fixed at stub time from D.39's packaging — the field
--  projections above are schematic; SPLIT: coefficient identity / polynomial identity)
```

**DEPENDS.** D.12, D.39.

**PROOF.** The corpus's displayed two-line computation (`EFF.T3.17` `[VERBATIM]`):
`ρ_t/ρ̂_t = res((N(q)/N̂(q))^t · (N̂(H₀)/N(H₀))) = χ(q)^{−t}·χ(H₀)` — in Lean: form the
kernel-element quotient, apply `map_mul`-algebra, recognize D.12's `chi` at `q` (to the
`−t`) and at `H₀`; "summing over `t` proves its polynomial identity" — `Finset.sum_congr`
+ `Polynomial.comp` coefficient arithmetic (`mul_pow`, `C_mul`).

**SIZE.** 30 lines. SPLIT (coefficient leg / polynomial leg) as in the SIGNATURE.

**SOURCE.** `EFF.T3.17` (the boxed `(T3-CMP)` + verbatim derivation).

**TEETH.** T3 §8.2, §8.3(2), §8.4(1) → **Lean theorem**; gate D.72 checks
`ρ_t = 3·ρ̂_t·2^{−t}` and `R(Z) = 3R̂(Z/2)` in `𝔽₅[Z]` (FRAME-C's displayed obligation).

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.41 [lemma] [fresh]

**STATEMENT.** *`(T3-ROUTE)`: polynomial routing along the comparison.* Multiplication by
the nonzero scalar `chiK H₀` and the substitution `Z ↦ Z/δ` preserve separability and the
multiset of irreducible-factor degrees and multiplicities; a monic factor `r̂` of degree `m`
of `RpolyHat` corresponds to the monic factor `r := wtwist δ r̂ = δ^m·r̂(Z/δ)` of `Rpoly`
(up to the global scalar), with root correspondence `ŝ ↦ δ·ŝ`; "Rationality over any field
containing `K` is preserved" — the correspondence commutes with `Polynomial.map
(algebraMap K L)` for any field extension `L/K`.

**SIGNATURE.**
```lean
theorem t3_route {K : Type*} [Field K] (δ : Kˣ) {rhat : Polynomial K} (h : rhat.Monic) :
    wtwist δ rhat = (δ : K) ^ rhat.natDegree • rhat.comp (Polynomial.C ((δ : K))⁻¹ * Polynomial.X)
    ∧ ((wtwist δ rhat).Separable ↔ rhat.Separable)
-- roots leg + map-commutation leg: sibling public lemmas `t3_route_roots`, `t3_route_map`
-- (this node is D.34's package INSTANTIATED at w := δ and re-exported under T3's name —
--  one-line proofs; the point is the T3-citable name and the rationality clause)
```

**DEPENDS.** D.34 (the transport package — the mathematical content lives there), D.40
(the consumer shape).

**PROOF.** Each clause is D.34's corresponding clause at `w := δ`; the map-commutation leg:
`wtwist` commutes with `Polynomial.map` of a ring hom sending `δ ↦ algebraMap δ`
(coefficientwise).

**SIZE.** 16 lines.

**SOURCE.** `EFF.T3.18` (the boxed `(T3-ROUTE)`: `r(Z) = δ^m r̂(Z/δ)`, `ŝ ↦ δŝ`, the
rationality sentence; derivation "Because `δ ∈ K^×`, substitution by `Z/δ` is a `K`-algebra
automorphism").

**TEETH.** T3 §8.2, §8.3(2), honesty item 10 → Lean theorem; the HETOW clause-(d) supply
(D.43's table row).

**ENVIRONMENT.** ENV-D3.

---

### NODE D.42 [interface] [fresh — GC-13 placeholders]

**STATEMENT.** *`(ABS-G2)`: the `i = 2` discharge — chapter C's port construction.* T3's §3
absorption (`EFF.T3.19`): at `s = f₃ − t`, `q = u₃`, `N = n̂₂`, GENTOW2's certified
"expansion, peel, positive-degree elimination, exact-grade digit law, and root-evaluation
calculation are **precisely (BR1)–(BR5)**"; therefore D.38 yields
`u(β_t) = ϑ_{G2}(t)·w^{f₃−t}` and, with D.35/D.34, the rescaling display
`y^{f₃} − Σ ϑ_{G2}(t)w^{f₃−t}c_t y^t = w^{f₃}P(y/w)` — "This absorbs GENTOW2-B″ and its
factor-pattern invariance. No value of `w` is required." **Unconditional at the landed
`i = 2` rung.** What chapter C owes (the placeholder): the port instance —
`EFF.GENTOW2.43 [supplied-by: chapter C]` (LEMMA GENTOW2-B″, whose proof `.44` step (iv)
consumes B′(3) = `EFF.GENTOW2.34 [supplied-by: chapter C]`) constructing
`BoundaryReadPort (levelTwoArena) u₃ (f₃−t)` per slot. Chapter D declares NO Lean name here;
the orchestrator wires C's construction to D.38 at the resolution pass.

**SIGNATURE.** none in chapter D (the conclusion is D.38 + D.35 applied to C's instance; a
D-side alias theorem would duplicate a name across the chapter boundary).

**DEPENDS.** D.38, D.35, D.10 · `EFF.GENTOW2.43 [supplied-by: chapter C]` ·
`EFF.GENTOW2.34 [supplied-by: chapter C]` · `EFF.GENTOW2.42 [supplied-by: chapter C]` (the
letter-group arena instance, D-H3(ii)).

**PROOF.** n/a (interface). **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T3.19` (the `(ABS-G2)` block, the BR-discharge sentence, the
unconditionality clause, `ϑ_{G2}(t) = Θ_N(s;u₃)`).

**ORIENTATION.** `ϑ_{G2}` is D.06 row 3 = `varthetaG2`/`theta` — the ANNOTATION IS the
content here; C's port construction must land its digit clause in T1-orientation `vartheta`
(BR5) and read its conclusion in GENTOW2-orientation (the involution D.10 mediates).

**TEETH.** T3 §8.3(1) (GENTOW2-B″ leg) → executable regression retained (§12); the landed
absorption append (T3 X29) → provenance note.

**ENVIRONMENT.** n/a.

---

### NODE D.43 [interface] [fresh — GC-13 placeholders]

**STATEMENT.** *`(ABS-HE4)`: the HETOW comparison discharge.* T3's §4 absorption
(`EFF.T3.20`): at `N = n₂`, `N̂ = n̂₂`, `τ_H = chiK` ("T3's χ, not T1's two-variable
cocycle"), `q = u₃`, `δ = τ_H(u₃)`, `H_t = H₀ − tu₃`: HETOW's assembled coefficients
instantiate D.39's data, and D.40/D.41 supply `(ABS-HE4)`'s displays (`ρ_t = ρ̂_t
τ_H(H₀)δ^{−t}`, `R_{λ₂}(Z) = τ_H(H₀)R̂_{λ₂}(Z/δ)`, the monic-factor and root routing) plus
`(HE4-COB)` = D.12's instance. **The absorption boundary table, transcribed verbatim** (each
row a supply/fence, chapter C's HETOW transcription cites it):

| HETOW-4 component | status |
|---|---|
| clause (a), `τ_H(k) = η^{−Q(m(k))}` | source-specific ladder arithmetic; NOT supplied by T3/D — the level-1 shape is D.19 + D.27's carry leg, the bridge is `EFF.HETOW [supplied-by: chapter C]` |
| clause (b), coboundary-comparison shape | supplied by D.12 (`(T3-COB)`) |
| clause (b), explicit two-floor exponent | obtained after substituting HETOW's floor arithmetic — supplier-side |
| clause (c), coefficient telescope + polynomial rescaling | fully supplied by D.11 (`(T3-BKT)`) + D.40 (`(T3-CMP)`) |
| clause (d), separability/factor/root routing | fully supplied by D.41 (`(T3-ROUTE)`) |
| common polynomial lift and later iterate independence | remain on HETOW-4's lift and finite-chain inputs — supplier-side |

**SIGNATURE.** none in chapter D (same rationale as D.42).

**DEPENDS.** D.11, D.12, D.39, D.40, D.41 · `EFF.HETOW [supplied-by: chapter C]` (the
bridge, `m`, the `τ` identification — `(H-HETOW-LOCAL)`'s fields; see D.27).

**PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T3.20` (the `(ABS-HE4)` displays, `(HE4-COB)`, the "No character law for
`τ_H` is asserted" fence, and the verbatim absorption-boundary table).

**TEETH.** T3 §8.3(2) → executable regression retained; §8.4(1) character mutant → D.12 +
gate D.72.

**ENVIRONMENT.** n/a.

---

### NODE D.44 [def+theorem] [fresh]

**STATEMENT.** *`[GENTOW5-W(i)]` as a named carrier, and `(ABS-G5W)`.* (i) The **sitewise
B-law predicate**: `GentowW A q R w := ∀ s : ℕ, R (N.n (s·q)) = (A.theta q s : K)·(w : K)^s`
— "the sitewise B-law holds for the level's read data". The corpus's `[GENTOW5-W(i)]` is
this predicate AT chapter C's level-`i` tower instantiation (arena + FGMN read + `w_i`);
chapter C/E/I consume the NAME `GentowW` with their own instances (the GC-13 resolution
wires `EFF.T3.21`'s `θ_i(t) = Θ_N(s;u_{i+1})`, `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))` data).
(ii) **`(ABS-G5W)`, the derivation theorem:** a family of ports at every `s` yields the
predicate — `(∀ s, ∃ P : BoundaryReadPort A q s, P.U = R (N.n (s·q)) ∧ P.w = w) → GentowW A q R w`
("The certified level-`i` expansion, peel, positive-degree elimination, exact-grade law, and
root-evaluation package instantiate (BR1)–(BR5). Hence `[GENTOW5-W(i)]`"). At `i = 2` this
is the landed GENTOW2-B″ instance (D.42); "the `i = 1` residual remains GENTOW5 S11.3's
fixed `z₁`-letter-power statement; T3 does not identify that unit with a displayed `w₁`"
(the `ω₁`/OPEN-2 fence — §8).

**SIGNATURE.**
```lean
/-- The sitewise B-law predicate whose level-`i` tower instance is `[GENTOW5-W(i)]`
(`EFF.T3.21`). SUPPLY STATUS transcribed: "SUPPLIED by T3-A0 and §7; consumption check +
dated append outstanding." -/
def GentowW {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (R : G → K) (w : Kˣ) : Prop :=
  ∀ s : ℕ, R (N.n (s * q)) = (A.theta q s : K) * (w : K) ^ s

theorem gentowW_of_ports {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {R : G → K} {w : Kˣ}
    (h : ∀ s : ℕ, ∃ P : BoundaryReadPort A q s, P.U = R (N.n (s * q)) ∧ P.w = w) :
    GentowW A q R w
```

**DEPENDS.** D.37, D.38.

**PROOF.** per `s`: destructure, rewrite with D.38.

**SIZE.** 20 lines.

**SOURCE.** `EFF.T3.21` (the `(ABS-G5W)` display `u_i(β_t) = θ_i(t)w_i^{f_{i+1}−t}`,
`i ≥ 3`, its BR-instantiation derivation, the `i = 2`/`i = 1` boundary sentences, SUPPLY
STATUS); the GENTOW5_WI §S2 span is `PERIMETER-UNRESOLVED` in T3's own XREF (X18) — the
port-family hypothesis above is the blueprint's exact rendering of "the certified …
package", and the perimeter resolution is `EFF.GENTOW5 [supplied-by: chapter C]` (T3 §8
deferred obligation 1).

**ORIENTATION.** `θ_i(t)` = B-law orientation (D.06 row 3); the predicate is stated in `s`,
consumers reindex by `s = f_{i+1} − t`.

**TEETH.** T3 §8.3(3), §8.4(2)–(4) → Lean theorem (the derivation); §8.3(4) (conditionality)
→ D.60/D.62/D.65 carry it — nothing here discharges any instance.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---
## 7. §7 — THE CERTIFICATE WITNESS (T4)

> **Design note (the composite read `grΔ`).** T4's machinery has five layers of definitions
> (`𝒟_{≤μ₂}`, `𝒜_j`, `C_j/ShC_j`, `Δ_j`, `gr_m`) but its four lemmas consume ONE composite:
> the assembled height-`m` digit of the `j`-th discrepancy, `gr_m(Δ_j(·))`, plus its
> additivity — the spec itself says "Linearity is the ONLY property used downstream"
> (`EFF.T4.06`). The frame D.46 therefore carries the composite as a single additive-map
> field `grΔ`, finitely-supported over canonical slots so that "distinct canonical slots form
> separate components" (`EFF.T4.07`) is the CODOMAIN's structure, and complete assembly
> ("all branches, carries, recarries … added before the class is taken") is the
> INSTANTIATION obligation on whoever supplies `grΔ` — the honest relocation of the r3/r4
> exposure repairs (honesty item D-H7(2)). The un-collapsed layers (`ShC_j`, the grid
> `𝒜_j`, the member slot condition) are the suppliers' concrete objects: `EFF.T4.03–.09
> [supplied-by: chapter C]` at the GT3/GT6 instances (D.53/D.54).

### NODE D.45 [def+lemma] [fresh]

**STATEMENT.** *The composed thresholds.* `thresholdTheta μ₂ E₂ δ j := (μ₂ − j)·E₂ + δ` —
T4's `Θ_j = (μ₂−j)E₂ + δ` with `E₂ = e₂f₂u₂`, `δ = u₂ − e₂D′h ≥ 1` (`EFF.T4.01`); plus the
consumed arithmetic: `δ ≥ 1 → j < j′ < μ₂ → thresholdTheta … j′ < thresholdTheta … j`
(strict antitone on the coordinate range) and `thresholdTheta … j ≥ 1 + (μ₂ − j)·E₂ − E₂`
shapes as `omega`-corollaries.

**SIGNATURE.**
```lean
def thresholdTheta (μ₂ E₂ δ j : ℕ) : ℕ := (μ₂ - j) * E₂ + δ

theorem thresholdTheta_anti (μ₂ E₂ δ : ℕ) (hE : 0 < E₂) {j j' : ℕ}
    (h : j < j') (h' : j' < μ₂) :
    thresholdTheta μ₂ E₂ δ j' < thresholdTheta μ₂ E₂ δ j
```

**DEPENDS.** none. **PROOF.** `omega`. **SIZE.** 10 lines.

**SOURCE.** `EFF.T4.01` (the setting: `D′ = e₁f₁`, `E₂ = e₂f₂u₂`, `δ = u₂ − e₂D′h ≥ 1`,
`Θ_j = (μ₂−j)E₂ + δ` for `j < μ₂`).

**TEETH.** T4 S8 PE1(4) → gate D.66's `Θ` table at the X-frame numbers.

**ENVIRONMENT.** ENV-D1.

---

### NODE D.46 [def] [fresh]

**STATEMENT.** *The certificate frame.* Over a dividend group `Dv` (`AddCommGroup` — the
`𝒟_{≤μ₂}` module), a slot type `Slot`, and a digit field `K`: a **certificate frame**
carries `μ₂ : ℕ`; thresholds `Θ : ℕ → ℕ`; the member class `M : Set Dv` (the affine
development slice `𝔐` — **a pure coefficient condition: NO discriminant hypothesis and no
decidedness hypothesis**, `EFF.T4.05`; the concrete slot-weight definition is the
suppliers'); the distinguished member `fkey : Dv` with `fkey_mem : fkey ∈ M` (membership
fact 1 — and `disc(f_key) = 0` at the instances, the recorded proof no disc condition COULD
be a field); the composite assembled read `grΔ : ℕ → ℕ → Dv →+ (Slot →₀ K)` ("`(m,j) ↦
gr_m(Δ_j ·)` after complete slot assembly and cancellation"); and **(FLOOR)** as a field:
`∀ f ∈ M, ∀ j < μ₂, ∀ m < Θ j, grΔ m j f = 0` — at exactly the R5-F1-rebound
quantification ("for every `f ∈ 𝔐`, every `j < μ₂`, and every `m < Θ_j`", `EFF.T4.13`).

**SIGNATURE.**
```lean
/-- T4's certificate frame (`EFF.T4.01–.13`, composite-read packaging per the §7 design
note). Instantiating `grΔ` = supplying COMPLETE assembly (every branch, carry, recarry —
`EFF.T4.07/.08`); instantiating `floor` = GENTOW-3(i) at 𝔐 [supplied-by: chapter C]. -/
structure CertFrame (Dv : Type*) [AddCommGroup Dv] (Slot : Type*)
    (K : Type*) [Field K] where
  μ₂ : ℕ
  Θ : ℕ → ℕ
  M : Set Dv
  fkey : Dv
  fkey_mem : fkey ∈ M
  grΔ : ℕ → ℕ → Dv →+ (Slot →₀ K)
  floor : ∀ f ∈ M, ∀ j < μ₂, ∀ m < Θ j, grΔ m j f = 0
```

**DEPENDS.** D.45 (the instances set `Θ := thresholdTheta …`) · mathlib `Finsupp`,
`AddMonoidHom`.

**PROOF.** definitional.

**SIZE.** 24 lines.

**FAITHFULNESS.** Three disclosed deltas, all consumption-neutral: (i) `C_j/ShC_j/Δ_j/gr_m`
collapse to `grΔ` (only the composite + additivity are consumed downstream — the spec's own
sentence); the identity `Δ_j(f_key) = ShC_j(Φ₂^{μ₂})` (`EFF.T4.09`'s `C_j(f_key) = 0`) is an
instantiation-side fact. (ii) Membership fact 2 (in-budget closure of `𝔐`) is a supplier
lemma consumed as a hypothesis at D.50's specialization, not a frame field (the corpus
derives it from the concrete slot condition, "pure coefficient arithmetic"). (iii) The slot
type is abstract; "distinct canonical slots form separate components" is the `Finsupp`
codomain. Flagged for cross-read (§13 item 4).

**SOURCE.** `EFF.T4.03` (`𝒟_{≤μ₂}`, `𝒟_{<μ₂}`), `.04` (`𝒜_j`, one `K₂`-digit per height),
`.05` (`𝔐` + the three membership facts + NO-disc), `.06` (`ShC_j`, `Δ_j`, linearity), `.07`
(`gr_m`, complete assembly), `.08` (full exposure — all-provenance), `.09` (`f_key`), `.13`
((FLOOR), the R2-G1/R5-F1 binding chain).

**TEETH.** S8 PE1(1)–(3) → carried to the instances (D.53/D.54) and §12.

**ENVIRONMENT.** ENV-D3 + the `(Dv, Slot)` parameters.

---

### NODE D.47 [def] [fresh]

**STATEMENT.** *The first-discrepancy height, totalized.* For a frame `F` and `q : Dv`:
`nuIdx F j q := sInf {m : ℕ∞ | ∃ m' : ℕ, m = m' ∧ F.grΔ m' j q ≠ 0}` — `ν_j(q) :=
min{m : gr_m(Δ_j(q)) ≠ 0}` with `min ∅ := +∞` (`EFF.T4.12`'s totalization: "`ν_j(q) = +∞`
exactly when `Δ_j(q)` is identically zero" — in this packaging, when every `grΔ m j q = 0`).

**SIGNATURE.**
```lean
noncomputable def CertFrame.nuIdx {Dv Slot K} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) (q : Dv) : ℕ∞ :=
  sInf {m : ℕ∞ | ∃ m' : ℕ, m = (m' : ℕ∞) ∧ F.grΔ m' j q ≠ 0}
```

**DEPENDS.** D.46.

**PROOF.** definitional (`sInf ∅ = ⊤` in `ℕ∞` is the mathlib convention — exactly the
corpus's `min ∅ := +∞`).

**SIZE.** 10 lines.

**SOURCE.** `EFF.T4.12` (R1-m1's totalization; "so the equivalence in T4.2(a) can be stated
without a disjunction").

**TEETH.** S8 PE1(2) → D.49.

**ENVIRONMENT.** as D.46.

---

### NODE D.48 [def] [fresh]

**STATEMENT.** *The certificate witness `ω_j` and touched/untouched.*
`CertFrame.omega F j := F.grΔ (F.Θ j) j F.fkey : Slot →₀ K` — "the fully assembled
height-`Θ_j` `K₂`-digit of the key power. Its assembly includes every input landing in the
canonical composed grid … Every collision and cancellation is completed before the digit is
taken" (`EFF.T4.10`, r3 text — the assembly sentence is `grΔ`'s instantiation obligation,
§7 design note). `Touched F j := F.omega j ≠ 0`; untouched `:= ¬ Touched`.

**SIGNATURE.**
```lean
noncomputable def CertFrame.omega {Dv Slot K} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : Slot →₀ K :=
  F.grΔ (F.Θ j) j F.fkey

def CertFrame.Touched {Dv Slot K} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : Prop := F.omega j ≠ 0
```

**DEPENDS.** D.46.

**PROOF.** definitional.

**SIZE.** 12 lines.

**SOURCE.** `EFF.T4.10` (DEFINITION T4.1: `ω_j := gr_{Θ_j}(Δ_j(f_key)) =
gr_{Θ_j}(ShC_j(Φ₂^{μ₂}))` — the second form via `EFF.T4.09`'s `C_j(f_key) = 0`,
instantiation-side; touched ⟺ `ω_j ≠ 0`); `EFF.T4.11` (the fence: "deliberately stronger
than … `ShC_j(Φ₂^{μ₂}) ≠ 0` [or] some unassembled single-extraction branch is nonzero. A
shadow coordinate may be nonzero while its height-`Θ_j` digit cancels. **FR-M3 at `j = 0` is
the committed separator: the self-shadow has pin 12, but `Θ₀ = 10` and `ω₀ = 0`**" — the
separator is a §12 retained regression + D.53's instance row).

**TEETH.** S8 PE1(1) → the codomain structure + D.53/D.54; the FR-M3 separator → §12.

**ENVIRONMENT.** as D.46.

---

### NODE D.49 [theorem] [fresh]

**STATEMENT.** *LEMMA T4.2(a): exact attainment for the key power.*
`Touched F j ↔ nuIdx F j F.fkey = (F.Θ j : ℕ∞)` (for `j < F.μ₂`); and at an untouched
coordinate `nuIdx F j F.fkey > (F.Θ j : ℕ∞)` — "where `+∞ > Θ_j` includes the case of an
identically zero discrepancy".

**SIGNATURE.**
```lean
theorem CertFrame.touched_iff_nu_eq {Dv Slot K} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} (hj : j < F.μ₂) :
    F.Touched j ↔ F.nuIdx j F.fkey = (F.Θ j : ℕ∞)
-- sibling public corollary: `nu_gt_of_untouched`
```

**DEPENDS.** D.46, D.47, D.48.

**PROOF.** T4's three steps (`EFF.T4.14`'s assembled proof, verbatim in substance):
1. `floor` at `fkey_mem` specializes: `grΔ m j fkey = 0` for `m < Θ j` — so every element of
   D.47's set is `≥ Θ j`, giving `nuIdx ≥ Θ j` (`le_sInf`). 2. Equality holds iff `Θ j`
   itself is in the set (`sInf`-membership at the bottom of a bounded-below set of naturals
   in `ℕ∞`), i.e. iff `grΔ (Θ j) j fkey ≠ 0`. 3. That digit IS `omega j` (D.48,
   definitional); the untouched corollary: `nuIdx ≥ Θ j` and `≠ Θ j` give `>`, including
   `⊤`.

**SIZE.** 26 lines.

**SOURCE.** `EFF.T4.14` (statement + the three-step proof; "including the identically-zero
case through the convention `ν_j(f_key) = +∞`").

**TEETH.** S8 PE1(2) ("uses the GENTOW-3 floor and does not infer a member-general
converse" — the statement is about `fkey` ALONE; the no-converse warning is D.52's ⚠ and
`EFF.T4.19`'s fence at D.53) → **Lean theorem**.

**ENVIRONMENT.** as D.46.

---

### NODE D.50 [theorem] [fresh]

**STATEMENT.** *LEMMA T4.2(b): perturbation stability.* For `g : Dv` with
`f := F.fkey + g ∈ F.M` ("a pure coefficient condition"): if `F.grΔ (F.Θ j) j g = 0` then
`F.grΔ (F.Θ j) j f = F.omega j`. **Specialization** (the in-budget case): if moreover
`∀ m, m ≤ F.Θ j → F.grΔ m j g = 0` (the supplier's "S8.1 repaired margin ledger places
every discrepancy of `g` at height at least `Θ_j + 1`") and `F.Touched j` and `j < F.μ₂`,
then `F.nuIdx j f = (F.Θ j : ℕ∞)` — "every touched coordinate remains divergent exactly at
`Θ_j` under such an in-budget perturbation".

**SIGNATURE.**
```lean
theorem CertFrame.perturb_stable {Dv Slot K} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {g : Dv} (hf : F.fkey + g ∈ F.M)
    (hg : F.grΔ (F.Θ j) j g = 0) :
    F.grΔ (F.Θ j) j (F.fkey + g) = F.omega j
-- sibling public corollary `perturb_nu_eq` with the margin hypothesis, per the STATEMENT
```

**DEPENDS.** D.46, D.47, D.48, D.49.

**PROOF.** "`Δ_j(f) = Δ_j(f_key) + Δ_j(g)`; taking the height-`Θ_j` graded component proves
the first assertion" (`EFF.T4.15`) — `map_add` on `grΔ` + `hg`. The corollary: `floor` at
`hf` excludes digits below `Θ j`; the margin hypothesis excludes `g`-digits at `Θ j` and the
first assertion + `Touched` makes the `Θ j` digit nonzero; conclude by D.49's `sInf`
arithmetic. **IMPORT FENCE transcribed:** the withdrawn "same shift" inference is NOT used
(PE1(3)'s exact check); the margin enters ONLY as the displayed hypothesis, whose discharge
is the supplier's S8.1 box (`EFF.T4.15`'s conditionality: "the in-budget case is a
*specialization*, supplied by S8.1's box" — membership fact 2 + the ledger,
`[supplied-by: chapter C]` at D.53).

**SIZE.** 28 lines.

**SOURCE.** `EFF.T4.15` (statement + proof, R2-G2 as rebound by R5-F1(2)/(3); the deep-
perturbation parenthetical decoupling note).

**TEETH.** S8 PE1(3) → **Lean theorem**; PE2 GT3 consumption → D.53/§12.

**ENVIRONMENT.** as D.46.

---

### NODE D.51 [lemma] [fresh]

**STATEMENT.** *LEMMA T4.2(c): the fully-exposed assembled-slot criterion.* If a canonical
slot `σ` of coordinate `j` at height `Θ_j` is **fully exposed** by a contribution with
nonzero normalized digit — in the frame: `(F.omega j) σ = ξ` with `ξ ≠ 0`, where equality
against the ASSEMBLED value is the full-exposure semantics (`EFF.T4.08`: "the complete list
of summands landing in that slot consists of `ξ` alone", every provenance propagated) —
then `F.Touched j`, and by D.49 the floor is attained there. **⚠ The premise is
all-provenance** (ledger `HYP.113` records this as a live conditional-theorem leg):
"Uniqueness only among single-extraction contributions does not discharge this premise: the
exposure calculation must also exclude every other term and every incoming carry or recarry
from the slot" — in this packaging, the burden sits in proving the INSTANCE equation
`(omega j) σ = ξ` against the complete `grΔ`, which is exactly where the corpus puts it
(D.54's R5-63A discharge).

**SIGNATURE.**
```lean
theorem CertFrame.touched_of_exposed {Dv Slot K} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) {j : ℕ} {σ : Slot} {ξ : K}
    (hexp : (F.omega j) σ = ξ) (hne : ξ ≠ 0) : F.Touched j
```

**DEPENDS.** D.48 (+ D.49 for the attainment corollary).

**PROOF.** "Its normalized digit is nonzero, so the selected slot is a nonzero component …
Distinct canonical slots are separate components; hence `ω_j ≠ 0`" (`EFF.T4.16`) —
`Finsupp.ne_iff`: a function with a nonzero value is nonzero.

**SIZE.** 10 lines.

**SOURCE.** `EFF.T4.16` (R3-G1's replaced statement + proof; conditionality "full exposure
in the sense of EFF.T4.08 — an all-provenance premise, NOT single-extraction uniqueness";
`HYP.113`).

**TEETH.** S8 PE1(5) (r3 form) → **Lean theorem** at frame level + the instance burden at
D.54; §12.

**ENVIRONMENT.** as D.46.

---

### NODE D.52 [lemma] [fresh]

**STATEMENT.** *LEMMA T4.2(d): the no-contribution criterion.* If, after complete
propagation, no summand of any provenance lands in any height-`Θ_j` slot of coordinate `j`
— or the complete assembled contribution cancels — then `ω_j = 0`; in the frame both legs
ARE the single equation `F.grΔ (F.Θ j) j F.fkey = 0`, so the lemma is the definitional
unfolding `F.omega j = 0 ↔ ¬ F.Touched j`. **The two ⚠ warnings transcribed** (they are the
r4 content, `HYP.114`): (i) "Absence of single-extraction sources alone does not discharge
the first hypothesis: the exclusion must cover every provenance named in DEFINITION T4.1's
assembly" — instance burden, as in D.51; (ii) "**No attainment statement for another member
follows: entry-driven content may still attain `Θ_j`**" — `ω_j` classifies the KEY-POWER
witness only (the FR-M3 `W`-member attains `Θ₀ = 10` through entry-driven content while
`ω₀ = 0`, `EFF.T4.19` — retained at D.53/§12).

**SIGNATURE.**
```lean
theorem CertFrame.omega_zero_iff_untouched {Dv Slot K} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : F.omega j = 0 ↔ ¬ F.Touched j
```

**DEPENDS.** D.48.

**PROOF.** `not_not` on D.48's definition.

**SIZE.** 8 lines.

**SOURCE.** `EFF.T4.17` (R4-G1's replaced clause (d): the all-provenance/cancellation legs,
the two warnings, and the record that consumers "invoke (d) only through its cancellation
leg (FR-M3's measured `ω₀ = 0`) and its no-other-member warning, never through the
no-source leg"; `HYP.114`).

**TEETH.** S8 PE1(1); PE2 GT3 (FR-M3 `ω₀ = 0`) and GT6 (FAM-E/FAM-D no-overflow controls)
→ retained regressions, §12.

**ENVIRONMENT.** as D.46.

---

### NODE D.53 [interface] [fresh — GC-13 placeholders]

**STATEMENT.** *Instance `GT3-THRESHOLD`* (`EFF.T4.18`): the certificate frame instantiated
at GENTOW-3's composed tower — `Δ_j = ShC_j − C_j`, `Θ_j = thresholdTheta μ₂ E₂ δ j`
(D.45), `ω_j` the key power's assembled digit. **Consumed facts, each a chapter-C
placeholder:** (1) `(FLOOR)` on `𝔐` = GENTOW-3(i) read at its Steps 0–2 quantification
domain (`EFF.GENTOW3 [supplied-by: chapter C]`; the R5-F1 supplier cite); (2) the per-genre
per-coordinate computation of `ω_j` = GENTOW-3(iv) through GT3-r2/r3; (3) the `Θ_j + 1`
perturbation margin = GENTOW-3 S8.1 (feeds D.50's specialization hypothesis); (4) the
x-free extreme = GENTOW-3(iii): every discrepancy zero, every `ω_j = 0`. **Result** (the
absorption, verbatim): "GENTOW-3(iv)'s phrase 'touched coordinate(s)' is exactly DEFINITION
T4.1. Its attainment conclusion is LEMMA T4.2(a), and its repaired deep-perturbation
persistence is LEMMA T4.2(b)." **Fences carried:** the one-sidedness scope (`EFF.T4.19`:
`ω_j = 0` does not bar other members — the `W` member attains `Θ₀` entry-driven); the
measured-configuration set (`EFF.T4.20`: FAM-A5/A7/B/C, FR-GL attained; FR-M3 `[10,7,4]` vs
`[12,7,4]`, `ω₀ = 0`, `ω₁,ω₂ ≠ 0`; FR5X identically zero rows) — inherited evidence,
retained as §12 regressions; the six-span GT3 pin stack (`EFF.T4.21`) is the placeholder's
provenance, fail-closed per `EFF.T4.29`; the `ω_j` wording seam (`EFF.T4.18`'s NOTE —
pre-r3 vocabulary in the Substitution block, governed by D.48's r3 definition) carried to
§13.

**SIGNATURE.** none in chapter D (the instance is C's `CertFrame` term; D supplies the frame
and lemmas).

**DEPENDS.** D.45–D.52 · `EFF.GENTOW3 [supplied-by: chapter C]` (spans per `EFF.T4.21`).

**PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T4.18` (+ `.19`, `.20`, `.21`).

**TEETH.** S8 PE2 GT3 consumption, in full → §12 (executable regressions retained: the
FR-M3 slack `[12,7,4]` vs `[10,7,4]` check is also gate material, D.66's ⚠).

**ENVIRONMENT.** n/a.

---

### NODE D.54 [interface] [fresh — GC-13 placeholders]

**STATEMENT.** *Instance `GT6-CERT-TOP`* (`EFF.T4.22/.23/.41`): the sealed
`f₁ = 1, μ₂ = 2` instance. Data (source-owned algebra, retained per N-5): `T = {t < f₂ :
ĉ_t ≠ 0}`, `t* = max T`, lift monomials `ĉ_t π^{a_t} x^{i_t}`, hypothesis `2i_{t*} ≥ D′`;
the `(t*,t*)` pair extracts into `j* = ⌊(2e₂t*+1)/(e₂f₂)⌋`, `b* = (2e₂t*+1) mod e₂f₂`,
`a* = 2i_{t*} − D′`, with normalized digit `(ĉ_{t*})²π^{2a_{t*}}·(wrap unit) ≠ 0` ("A
product of units in `K₂ˣ`: nonzero — no binomial coefficient, no characteristic condition").
**The conditional invocation and its discharge:** invoking D.51 needs FULL EXPOSURE (r3
text: "the displayed contribution is the sole summand in its canonical height-`Θ_{j*}`
slot"); **R5-63A discharges it — "YES at the sealed scope — `f₁ = 1`, `μ₂ = 2`,
`2i_{t*} ≥ D′` — and NO elsewhere"** (`EFF.T4.41`'s five byte-quoted legs: whole-layer
classification, weight separation `≥ Θ + δ` for multi-extraction, tracked carries, slot
uniqueness, unconditional nonzero digit). Conclusion at that scope: `ω_{j*} ≠ 0`, `j*`
touched, `ν_{j*}(f_key) = Θ_{j*}` (D.51 + D.49). **Withdrawn text carried:** the r0
sentence claiming a "literal exposed-slot instance" on the pre-r3 basis is WITHDRAWN
(R5-F2); the governing status is "resolved at the `f₁ = 1` scope, **and only there**".

**SIGNATURE.** none in chapter D (the exposure equation `(omega j*) σ* = digit` is the
C-side calculation `EFF.GENTOW6 [supplied-by: chapter C]` — the R5-63A legs live in
GENTOW6's spans; D supplies D.51's firing).

**DEPENDS.** D.45–D.49, D.51 · `EFF.GENTOW6 [supplied-by: chapter C]` (spans 1 and 3 of
T4's GT6 stack; the R5-63A legs X33–X39).

**PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T4.22` (the instance data), `.23` (the conditional + withdrawal), `.41`
(R5-63A — the discharge, its scope fence, and its acceptance re-adjudication note).

**TEETH.** S8 PE1(5)/(6), PE2 GT6 consumption → §12; the scope fence ("NO elsewhere") is a
signed row — a fleet agent instantiating CERT-TOP outside `f₁ = 1, μ₂ = 2, 2i_{t*} ≥ D′`
must return BLOCKED.

**ENVIRONMENT.** n/a.

---
## 8. §8 — THE W-FRAME (T5)

> **Design note.** The twist machinery (WF-twist/WF-psi and the transport package) landed in
> §5 (D.34/D.35) because T1's three-reads and T3's routing consume it first; §8 adds T5's
> OWN content: the cumulative hypothesis and its non-discharge discipline, the two-scope law
> split, the realized-residual cancellation, and the corrected index/chain carriers. T5's
> `(WF-w)` is D.29's `w` field; `(WF-twist)`/`(WF-psi)` are D.34/D.35 — each §8 node names
> its T5 display so the unit-level SOURCE map stays total.

### NODE D.55 [def] [fresh]

**STATEMENT.** *The cumulative hypothesis `𝒲_{≤i}`.* For a rung-indexed family of laws
`W : ℕ → Prop` (instantiated at `[GENTOW5-W(q)]` = D.44's `GentowW` at chapter C's rung-`q`
data): `Wle W i := ∀ q, 3 ≤ q → q ≤ i → W q` — `𝒲_{≤i} = ⋀_{3≤q≤i}[GENTOW5-W(q)]`, with
`Wle W 2` the EMPTY conjunction (trivially true — `EFF.T5.13`'s r4-G1 base repair). **The
non-discharge discipline, transcribed (D-H5(2)):** "Certification of the WI companion does
not discharge these conjuncts from the frozen GENTOW5 statements" (`EFF.T5.29`, the r1
replacement of the stale opposite at source L299 — ledger `HYP.100`); ledger `HYP.63`
carries `𝒲_{≤i}` with disposition "CARRY — WI proves only the induction step, not induction
from empty base". Nothing in this chapter, and nothing in any chapter, discharges an
instance of this predicate; chapter I carries it (D.63).

**SIGNATURE.**
```lean
/-- `𝒲_{≤i}` (`EFF.T3.22`, `EFF.T5.13/.29`). CARRY (`HYP.63`); never discharged. -/
def Wle (W : ℕ → Prop) (i : ℕ) : Prop := ∀ q, 3 ≤ q → q ≤ i → W q

theorem Wle_two (W : ℕ → Prop) : Wle W 2   -- the empty conjunction
```

**DEPENDS.** D.44 (the intended instantiation of `W`).

**PROOF.** `Wle_two`: `omega` kills `3 ≤ q ∧ q ≤ 2`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.T3.22` (the `𝒲_{≤n}` display), `EFF.T5.13` (+ the empty base), `EFF.T5.29`
(the non-discharge sentence + the superseded-but-physically-present predecessor,
`HYP.100`).

**TEETH.** T3 §8.3(4)/§8.4(5) and T5 §7 Pass 1(3)/Pass 2(5) (conditionality lints) → the
def's shape + §12 signed rows (no discharge theorem exists to lint).

**ENVIRONMENT.** ENV-D1.

---

### NODE D.56 [interface] [fresh — GC-13 placeholders]

**STATEMENT.** *`(WF-law₂)`: the unconditional base rung.* At `i = 2`,
`u₂(β_t) = Θ₂(t)·w₂^{f₃−t} = ϑ_{2,f₃−t}^{−1}·w₂^{f₃−t}` (`t < f₃`) — **unconditional: no
`𝒲` hypothesis** (`Wle W 2` is empty). Supplied by LEMMA GENTOW2-B″
(`EFF.GENTOW2.43 [supplied-by: chapter C]`, object-addressed at `33f86204` L729–738 — the
same span the D.06 table's row-5 verification pins); in D-terms: chapter C constructs
`GentowW A₂ u₃ R₃ w₂` at its level-2 arena, D.42's port route being the derivation. The
site obligation `(C3-ladder-nonvanishing)` is discharged here by GENTOW2-B′(3)/B″ — "the
discharge T1 r8 itself names at the accepted GENTOW2 site" (`EFF.T5.09`).

**SIGNATURE.** none in chapter D (the statement is `GentowW` at C's instance; D.44 named
the predicate precisely so this row is a C-side term, not a D-side axiom).

**DEPENDS.** D.44 · `EFF.GENTOW2.43 [supplied-by: chapter C]`, `EFF.GENTOW2.34 [supplied-by:
chapter C]` (B′(3), the nonvanishing leg).

**PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T5.12` (the boxed `(WF-law₂)`, its unconditionality, the r1 two-scope
split superseding the base's single unscoped law); `EFF.T5.15` (the supplier record:
"`i = 2`: LEMMA GENTOW2-B″, unconditionally").

**ORIENTATION.** `Θ₂(t) = ϑ_{2,f₃−t}^{−1}` — D.06 rows 1–2 (the reconciliation row 5 is
the verification this display rests on).

**TEETH.** T5 §7 Pass 1(2)/Pass 2(3) → §12; gate D.72's orientation leg.

**ENVIRONMENT.** n/a.

---

### NODE D.57 [theorem] [fresh]

**STATEMENT.** *`(WF-lawᵢ)`: the higher rung retains its hypothesis.* For `i ≥ 3`:
`Wle W i → W i` — the rung-`i` law is the LAST CONJUNCT of the cumulative hypothesis; "the
new rung hypothesis is `[GENTOW5-W(i)]`; the earlier members remain the ambient induction
history. The existence or certification of the companion note does not remove these
hypotheses from the statement" (`EFF.T5.15`). With `W i := GentowW (level-i data)` the
consequent unfolds to the boxed display `𝒲_{≤i} ⟹ [u_i(β_t) = Θ_i(t)w_i^{s_t}]`. **The
stacked conditionality transcribed** (`EFF.T5.14`): additionally `(H-VARTHETA-RES)_i` at
every `i ≥ 3` use of `Θ_i(t)` (D.62 — "a SECOND conditional stack on the same displays and
must not be conflated with `𝒲_{≤i}`", `EFF.T5.10`), and `(C3-ladder-nonvanishing)` at
every `w_i` site (typed into D.29/D.44's `w : Kˣ`; D-H6).

**SIGNATURE.**
```lean
theorem wf_law_i (W : ℕ → Prop) (i : ℕ) (hi : 3 ≤ i) (h : Wle W i) : W i
```

**DEPENDS.** D.55 (+ D.44 for the intended `W`).

**PROOF.** `h i hi le_rfl`.

**SIZE.** 6 lines. (The triviality is the POINT: the corpus's r1 repair replaced a
discharge claim by hypothesis-retention, and hypothesis-retention in Lean is conjunct
extraction — anything more would be the r4-G1-refuted "induction from empty base".)

**SOURCE.** `EFF.T5.14` (the boxed `(WF-lawᵢ)` implication + the three-layer
conditionality; `HYP.63`), `EFF.T5.15` (the supplier split + certification-not-discharge).

**TEETH.** T5 §7 Pass 1(2), Pass 2(3), Pass 2(5) → §12 signed rows.

**ENVIRONMENT.** ENV-D1.

---

### NODE D.58 [theorem] [fresh]

**STATEMENT.** *`(WF-realized)`: the realized-residual cancellation.* Given the sitewise
B-law `GentowW A q R w` (D.44) and digits `c : Fin f → K` under the **coherent recipe**
`Γ_t = c_t·ϑ_{i,s_t}` (`EFF.T5.18`'s "Whenever the relevant (WF-law) equality is
available"): the read coefficients cancel slotwise,
`R (N.n (s_t·q)) * (c t * (A.vartheta q s_t : K)) = c t * (w : K)^{s_t}` (D.33's shape, now
from `GentowW`), and hence the assembled residual equals the twist:
`X^f − Σ_t C (R (N.n ((f−t)·q)) * Γ_t) * X^t = wtwist w (X^f − Σ_t C (c t) * X^t)` —
`R_ν(Φ_{i+1}) = ψ_{i+1}^{(w_i)}` at the coefficient level. **Scope split transcribed:**
at `i = 2` unconditional (`(WF-realized₂)`, via D.56's instance); at `i ≥ 3` inside
`Wle W i` (`(WF-realizedᵢ)`'s two-arrow display `𝒲_{≤i} ⟹ (WF-law)ᵢ ⟹ R_{ν_i}(Φ_{i+1}) =
ψ_{i+1}^{(w_i)}` — D.57 then this node).

**SIGNATURE.**
```lean
theorem gentowW_realized {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {R : G → K} {w : Kˣ}
    (hW : GentowW A q R w) (f : ℕ) (c : Fin f → K) :
    (Polynomial.X ^ f
      - ∑ t : Fin f, Polynomial.C
          (R (N.n ((f - (t : ℕ)) * q)) * (c t * (A.vartheta q (f - (t : ℕ)) : K)))
          * Polynomial.X ^ (t : ℕ))
    = wtwist w (Polynomial.X ^ f - ∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ))
```

**DEPENDS.** D.10, D.34, D.35, D.44.

**PROOF.** 1. Coefficientwise: `hW` at `s = f − t`, then `Θ·ϑ = 1` (D.10) — "Substituting
(WF-law) into `Γ_t u_i(β_t)` cancels `ϑ_{i,s_t}ϑ_{i,s_t}^{−1} = 1`, leaving `c_t w_i^{s_t}`
— exactly the coefficient of `y^t` in (WF-psi)" (`EFF.T5.18`, verbatim). 2. Assemble with
D.35's `wtwist_psi`.

**SIZE.** 26 lines.

**SOURCE.** `EFF.T5.18` (the corollary + the boxed `(WF-realized₂)`), `EFF.T5.19` (the
boxed `(WF-realizedᵢ)` two-arrow form), `EFF.T5.20` (the supplier attribution: "T1 supplies
the dictionary and the final cancellation. GENTOW2-B″ supplies the unconditional `i = 2`
B-law. At `i ≥ 3`, `[GENTOW5-W(i)]` supplies the sitewise B-law only within the displayed
cumulative hypothesis" — which is exactly this node's dependency shape: D.10/D.34/D.35 the
T1 side, `hW` the supplier side).

**ORIENTATION.** the cancellation site — both orientations meet through D.10, as at D.33.

**TEETH.** T5 §7 Pass 1(2)/Pass 2(2) → **Lean theorem**; gate D.72 (the FRAME-C `U·ϑ = w^s`
identity is this cancellation's numeric shadow).

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.59 [def] [fresh]

**STATEMENT.** *`(WF-index)`: the corrected-index residual-power carrier.* For a top rung
`n`, level reads `Rlev : ℕ → Polynomial K` (chapter C's `R_{j−1}(Φ_{n+1})`), residuals
`ψ : ℕ → Polynomial K`, twist units `ω : ℕ → Kˣ`, and multiplicities `l : ℕ → ℕ`:
`WfIndex Rlev ψ ω l n := ∀ j, 2 ≤ j → j ≤ n + 1 → Rlev (j−1) = (wtwist (ω (j−1)) (ψ j)) ^ (∏_{k=j+1}^{n+1} l k)`
— the clause-(b) residual display `R_{j−1}(Φ_{n+1}) = (ψ_j^{(ω_{j−1})})^{l_{j+1}⋯l_{n+1}}`
**at the corrected index `ω_{j−1}`** with `ω₁ =` S11.3's fixed letter-power unit,
`ω₂ = w₂`, `ω_q = w_q (q ≥ 3)`. The correction's reason, transcribed: "The display as first
written demanded `w_{n+1}` at the top term, **exceeding the assumed `𝒲_{≤n}`**" — an
off-by-one that would have consumed a conjunct outside the hypothesis; "No display in T3
uses the superseded index `ψ_j^{(ω_j)}`" and neither does any D node. The `j = 2` leg is
scoped to `ω₁`'s OWN letter-power form — "NOT via (C3-ladder-nonvanishing) applied to a
displayed `w₁`. Its identification with `w₁` is exactly WFRAME OPEN-2; the `i = 1` display
stays open with it" (`EFF.T5.09`; the outer `ψ₁` leg is separately governed and UNNAMED —
T3 §8 deferred obligation 2, `[supplied-by: chapter C]` if GENTOW5's spec exposes it).

**SIGNATURE.**
```lean
/-- The clause-(b) corrected-index display (`EFF.T5.32` (WF-index), `EFF.T3.24` (G5-TWIST)).
A CARRIER: instances are chapter C's; consumed under `Wle` per D.60's chain. -/
def WfIndex {K : Type*} [Field K] (Rlev : ℕ → Polynomial K) (ψ : ℕ → Polynomial K)
    (ω : ℕ → Kˣ) (l : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j ≤ n + 1 →
    Rlev (j - 1) = (wtwist (ω (j - 1)) (ψ j)) ^ (∏ k ∈ Finset.Icc (j + 1) (n + 1), l k)
```

**DEPENDS.** D.34.

**PROOF.** definitional.

**SIZE.** 14 lines.

**SOURCE.** `EFF.T5.32` (the boxed `(WF-index)` + the `ω` assignment + the corrigendum
reason), `EFF.T3.24` (`(G5-TWIST)` — the same display, T3's copy, with the `ψ_j`-carries
list and the `ψ₁` fence).

**ORIENTATION.** the twists are `wtwist` at the units `ω_{j−1}` — no ϑ enters; the index
correction is an `ω`-INDEX matter, kept apart from D.06's ϑ-orientation rows (a conflation
of the two is the T5 §7 Pass 1(4)/Pass 2(6) "twist-index mutant").

**TEETH.** T3 §8.3(5)/§8.4(6), T5 §7 Pass 1(4)/Pass 2(6) (index lints) → the def fixes
`j−1` structurally; §12.

**ENVIRONMENT.** ENV-D3.

---

### NODE D.60 [def] [fresh]

**STATEMENT.** *`(G5-COND)`/`(WF-chain)`: the conditional consumer chain, as a carrier.*
The eight stations `𝒲_{≤n} ⟹ (a)@n ⟹ Corollary 6.4 ⟹ (b)@n ⟹ S11.1.1/S11.1.3 ⟹ (c)@n ⟹
(e)@n ⟹ the next automatic floor` — carried as the chain-of-implications predicate
`WfChain (P : Fin 8 → Prop) : Prop := ∀ k : Fin 7, P k.castSucc → P k.succ`, with the
station vector instantiated by chapter C (`P 0 := Wle W n`, `P 3 := WfIndex …`-content at
clause (b), etc. — the GC-13 resolution wires the stations to C's clause nodes). **Two
transcription notes carried with the carrier:** (i) T5's display deliberately PROMOTES the
source's single-conjunct antecedent `[GENTOW5-W(n)]` to the cumulative `𝒲_{≤n}` "on the
corrigendum's own instruction … the one place T5's display is *stronger in hypothesis* than
the raw source line" (`EFF.T5.30`) — the carrier uses the cumulative form; (ii) the scope
rows: clauses (a)/(b)/(c)/(e)'s listed conclusions ALL consume `𝒲_{≤n}`, with exactly two
carve-outs — "S11.1.2's numerical ρ-ladder remains unconditional floor arithmetic" and "a
floor inequality explicitly included in the fixed datum remains independently available"
(`EFF.T5.31`; `EFF.T3.23`'s ride-list is the same content at T3 granularity).

**SIGNATURE.**
```lean
/-- The (G5-COND)/(WF-chain) implication chain (`EFF.T3.23`, `EFF.T5.30/.31`). Stations
supplied by chapter C; chapter I consumes the assembled conditional. -/
def WfChain (P : Fin 8 → Prop) : Prop := ∀ k : Fin 7, P k.castSucc → P k.succ
```

**DEPENDS.** D.55, D.59 (station content).

**PROOF.** definitional.

**SIZE.** 8 lines.

**SOURCE.** `EFF.T3.23` (the boxed `(G5-COND)` + the ride-list + the "w-blind" fence:
""w-blind" means invariant after the single-`w_i` geometric law has been proved. It does
not construct that law from an arbitrary fixed per-grade family"), `EFF.T5.30` (`(WF-chain)`
+ the strengthening note), `EFF.T5.31` (the four scope rows + two carve-outs).

**TEETH.** T3 §8.3(4)/§8.4(5), T5 §7 Pass 1(3) → §12 signed rows (a carrier has no
executable content; the lint is that NO chapter-D node discharges a station).

**ENVIRONMENT.** ENV-D1.

---

### NODE D.61 [record] [fresh]

**STATEMENT.** *The per-level nonvanishing suppliers, the two-clause gate, and the avatar
fences — T5's site-obligation record, transcribed for the consumers.* No Lean declaration;
five rows every consumer of `w`-sites must read:

1. **`i = 2` supplier:** GENTOW2-B′(3)/B″ — B′(3) the per-grade-unit clause, B″ the single
   slot-independent `w ∈ K₂ˣ` (`EFF.T5.09`; placeholders as at D.56).
2. **`i ≥ 3` supplier:** GENTOW5 S11.2's PROVED fixed-unit list — "the `s = 1` grade of
   that family is exactly the base ladder read … A fixed `K_iˣ`-value is in particular
   nonzero" — deliberately routed AROUND `𝒲_{≤i}` ("on S11.2's PROVED side of the fence,
   while the single-`w` geometric law itself stays behind `𝒲_{≤i}`"). **The fence with
   teeth:** "Per-grade fixedness alone does not prove (WF-law). In particular, this note
   does not revive S11.2's withdrawn "w-blind" argument" (`EFF.T5.16`) — a D/E/C node
   deriving `GentowW` from fixedness is a defect.
3. **`i = 1`: NONE.** No supplier; no `i = 1` instance of (WF-w)/(WF-twist)/(WF-psi) is
   asserted anywhere; `ω₁` rides S11.3's letter-power form (D.59); `ω₁ = w₁?` is WFRAME
   OPEN-2 — OPEN, chapter I's ledger.
4. **The two-clause gate staleness** (`HYP.99`, D-H6): T5 carries one clause; T1 HEAD
   carries two; D.29/D.44 type `w : Kˣ` (both clauses by construction). The note-owner
   repair is NOT executed here.
5. **The avatar fence** (`EFF.T5.07`, `HYP.66`): "«Cross-frame» means that `w_i` converts
   the multiplicative residual frame to the canonical residual frame. It does not identify
   `w_i` with a separately normalized uniformizer avatar" — live counterexample LW3:
   `w_av = 2 ≠ w₃ = 1` (`EFF.T5.28`). No D node mentions an avatar; the fence is for C/E
   consumers of D.29's `w`.

**SIGNATURE.** none. **DEPENDS.** D.29, D.44, D.55 ·
`EFF.GENTOW2.34/.43 [supplied-by: chapter C]` · `EFF.GENTOW5 [supplied-by: chapter C]`
(S11.2/S11.3 spans). **PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF.T5.09` (the carry + the three supplier rows + the staleness flag),
`EFF.T5.10` (the HVR stack), `EFF.T5.16` (the fixedness fence), `EFF.T5.07`/`.28` (the
avatar fence + LW3), `HYP.63/.66/.99/.100`.

**TEETH.** T5 §7 Pass 1(1)/(2)/(5)/(6), Pass 2(3)/(6) → §12 (signed rows + the LW3
regression retained).

**ENVIRONMENT.** n/a.

---

## 9. §9 — THE `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` CARRIERS (Display A's `∀ i ≥ 3` conjunct)

### NODE D.62 [def] [fresh]

**STATEMENT.** *The `(H-VARTHETA-RES)_i` carrier.* The corpus's fence (`EFF.T1.09`): at
depth `i ≥ 3` every consumer of `ϑ_{i,s}`/`Θ_i(t)` carries
"`(H-VARTHETA-RES)_i : res(n̂_i(u_{i+1})^s / n̂_i(su_{i+1})) ∈ K_i (s ≥ 0)`". In the
DECISION-D-1 packaging the Lean carrier is **arena existence over the level's height data**:
`HVarthetaRes G K N v := ∃ A : GaugeArena G K N, A.v = v` — supplying the level-`i`
residue interface IS the hypothesis. **Strength delta, disclosed (D-H3):** the arena form
asserts the residue hom on the whole value-zero subgroup; the corpus's clause asserts it at
the ϑ-quotients only. The delta is in the SAFE direction for the capstone (a stronger
carried hypothesis claims less), but chapter I's ledger row must state the corpus form as
the ledger-strength content and THIS name as the Lean-consumed form — handed to I with that
exact note (§13 item 2; the czar's fresh-eyes audit arm is the natural reviewer).

**SIGNATURE.**
```lean
/-- The Lean carrier of `(H-VARTHETA-RES)_i` (`EFF.T1.09` R9-2 fence; DECISION D-1
packaging — see the chapter's D-H3 and the strength-delta note). Consumed by E (ladder
displays at `i ≥ 3`) and I (Display A's `∀ i ≥ 3` conjunct, via D.63). -/
def HVarthetaRes (G : Type*) [CommGroup G] (K : Type*) [Field K]
    (N : NormSection G) (v : G →* Multiplicative ℤ) : Prop :=
  ∃ A : GaugeArena G K N, A.v = v
```

**DEPENDS.** D.01, D.07.

**PROOF.** definitional.

**SIZE.** 10 lines.

**SOURCE.** `EFF.T1.09` (the fence + the displayed hypothesis), `EFF.T5.10` (the carry at
every `i ≥ 3` `Θ`-use, "not adjudicated here" whether S11.2's S2.1 computation discharges
it — that adjudication is nobody's in this chapter: OPEN, routed at D.64).

**TEETH.** T1 §4.2 checks 5/8/9 (the depth fence's checks) → §12; no discharge exists to
test.

**ENVIRONMENT.** ENV-D2 + ENV-D3.

---

### NODE D.63 [def] [fresh]

**STATEMENT.** *Display A's `∀ i ≥ 3` conjunct, assembled.* The indexed family
`VarthetaWConjunct HVR W i := HVR i ∧ Wle W i` over abstract rung-indexed `HVR W : ℕ → Prop`
— instantiated at `HVR i := HVarthetaRes (level-i data)` (D.62) and `W q := GentowW
(level-q data)` (D.44), both instantiations chapter C's. This is the name chapters E and I
consume for the capstone conjunct `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` (`∀ i ≥ 3`); per the Part V
owner ruling, its terminal disposition in chapter I is DISCHARGE NODE or LITERATURE CITE —
this chapter only supplies the carrier at exact ledger strength (modulo D.62's disclosed
delta).

**SIGNATURE.**
```lean
def VarthetaWConjunct (HVR W : ℕ → Prop) (i : ℕ) : Prop := HVR i ∧ Wle W i
```

**DEPENDS.** D.55, D.62 (+ D.44).

**PROOF.** definitional.

**SIZE.** 6 lines.

**SOURCE.** `EFF.T1.09` + `EFF.T3.22` + `EFF.T5.10/.13` (the two stacked families);
Display A's conjunct list (`spec/HYPOTHESIS_LEDGER.md` capstone preview — the `∀ i ≥ 3`
row; CONVENTIONS Part IV item 4's sign-off surface names `(H-VARTHETA-RES)/𝒲` explicitly).

**TEETH.** none (a carrier); I's gates re-fire the `n ≤ 2` slices where the conjunct is
empty.

**ENVIRONMENT.** ENV-D1.

---

### NODE D.64 [record] [fresh]

**STATEMENT.** *OPEN-CALL and orphan routing — the chapter's residual-obligation table.* No
Lean declaration; one row per surviving open item of the four specs, each routed:

| item | content | routing |
|---|---|---|
| T1 OPEN-CALL 1 (`(H-JA-CONJ)_i` source designation) | the JA supplier for letter monomiality | inline hypothesis at D.20's consumers; designation resolution FOR-0d — chapter I gate (b) if cited as literature |
| T1 OPEN-CALL 2 (`(H-JA-RES-CONJ)` source) | the conjugation supplier | inline at D.23; same routing |
| T1 OPEN-CALL 3 (`(H-GENHN-CLEAR)` source) | the clearance supplier | NO D node (D-H4(5)); consumers in C |
| T1 OPEN-CALL 4 = T3 OPEN-CALL 1 (**NEEDS ASVIN**) | "the surrounding tower correctness theorem" converting residual factor patterns to p-adic splitting types — unnamed in both notes; "Assigning a source or formal interface would be invention" | **chapter I / the 0d trust boundary** (owner gate (b) — a literature cite if one exists); D and E consume factor-pattern statements only, never splitting types, until it lands |
| T1 OPEN-CALL 5 (level-general residual-read supplier) | the `i ≥ 3` read bundle | D.29-instantiation obligation = `[GENTOW5-W(i)]`/HVR stack (D.44/D.62); C's spans |
| T3 deferred obligation 1 (GENTOW5 §S2 perimeter, XREF X18 `PERIMETER-UNRESOLVED`) | the five-fold certified package's fine designations | `EFF.GENTOW5 [supplied-by: chapter C]` — C's DEPENDS re-home it |
| T3 deferred obligation 2 (the outer `ψ₁` statement) | unnamed source theorem | `[supplied-by: chapter C]` if GENTOW5's spec exposes it; else I ledger |
| T3 deferred obligation 3 (ABS-G5W consumption check + dated append) | protocol action | ORCHESTRATOR item (not mathematical) |
| T5 OPEN-CALL 1 / `HYP.99` (two-clause staleness) | note-owner repair | recorded at D.61(4); NOT executed |
| WFRAME OPEN-2 (`ω₁ = w₁?`), OPEN-3/`HYP.66` (avatar) | open identifications | I ledger rows; D.59/D.61 fence them |
| `JD0-BOX-2` | zero T-unit cites (D-H8's grep) | **chapter I**, named hypothesis (`HYP.39`) |
| `HYP.01`/`HYP.12` escalations | trust-boundary naming from T3/T1 open calls | **chapter I** core-set (`HYP.98`); NO D node (Brief D trap (iii)) |
| T3 `(T3-JOINT-OPEN)` | a realized p-adic B″ frame with `Θ ≠ 1 ∧ w ≠ 1` simultaneously — "a machine-coverage gap, not a proof gap" | gate D.72 carries the record; coverage stays open |

**SIGNATURE.** none. **DEPENDS.** n/a. **PROOF.** n/a. **SIZE.** 0 Lean lines.

**SOURCE.** `EFF-T1.md` §8 (OPEN-CALLs 1–5 + FOR-0d routing), `EFF-T3.md` §8–§9 (deferred
obligations + OPEN-CALL 1), `EFF-T5.md` §8–§9 + `HYP.63/.66/.99/.100`, `EFF.T3.30`.

**TEETH.** n/a (a routing table; §13 asks the cross-read to verify it is EXHAUSTIVE against
the four specs' self-audit sections).

**ENVIRONMENT.** n/a.

---
## 10. §10 — GATES: `q = 2` AND `q = 3` FIRING INSTANCES, THE FRAME-C REGRESSION, AND THE CENSUS

**What a §10 gate is here.** Chapter D's arithmetic content is the gauge calculus — exponent
tables, telescope values, orientation identities — so the gates instantiate the level-1
arena at the T-units' OWN inherited battery frames (`EFF.T1.33`) and execute the expected
values by `decide` (never `native_decide`). Per GC-11: `q = 2` AND `q = 3`; the `e > 1 ∧
f > 1` witness is D.65's frame itself (`e₁ = 2, f₁ = 2` — the F4-JOINT axes; at the gauge
layer the meaningful pair is the level datum `(e₁, f₁)`, both `> 1` simultaneously). The
field-level legs run over concrete finite fields (`ZMod 3`, `ZMod 5`, and an `𝔽₄` carrier);
⚠ the `𝔽₄` carrier choice (`GaloisField 2 2` vs an explicit quotient construction) is a
known `decide`-fragility — the stub agent picks the computable route and records it; the
exponent-table legs are pure `ℕ` and decide regardless.

### NODE D.65 [gate] [fresh]

**STATEMENT.** *The `q = 2` gate — the F4-JOINT frame (`e₁ = 2, f₁ = 2, h = 1`,
`K₁ = 𝔽₄`, `η = ω` of order 3, `u₂ = 3`; "live wrap"), `EFF.T1.33/.34`'s expected values
reproduced by the general engine.* Executed checks:

1. **exponent tables** (`ℕ`, `decide`): `iexp 2 1 k = k % 2`; `wrap 2 1 a b = 1` exactly on
   odd/odd (the live wrap); `Wfloor`-table `⌊s·i(3)/2⌋ = (0,0,1,1)` for `s = 0…3`.
2. **the telescope vector** (`𝔽₄`): `(ϑ_{1,0},…,ϑ_{1,3}) = (1, 1, ω, ω)` — via D.18 the
   exponent table of leg 1 exponentiated at `η = ω`; **exactly `EFF.T1.34`'s `μ = 3` leg**.
3. **the μ = 3 canonical vector** (`𝔽₄`): with `w = ω` and unit digits: `Γ = (1, ω, ω)`,
   `u(β) = (ω, ω, ω²)` (D.32's B-law at the instance), full canonical coefficient vector
   `(ω, ω², 1)` — assembling to `(y + ω)³` (D.58 + D.35).
4. **the quadratic triple** (`𝔽₄`): `R_corr = y² + y + ω`, `R_naive = y² + y + 1`,
   `ψ^{(w)} = y² + ωy + 1` — the corrected/naive/canonical separation (the gauge-naive
   mutant's kill site: `R_naive ≠ R_corr` because `ϑ₂ = ω ≠ 1`, D.28 clause 3's criterion).

**SIGNATURE.**
```lean
-- leanfinal/Uniformity/ChapD/D65.lean — one #eval/decide/example block per check above;
-- public declarations: `gate_f4_theta_vector` (leg 2) and `gate_f4_canonical` (leg 3) as
-- `example`-promoted theorems over the chosen 𝔽₄ carrier; legs 1 by `decide` lines
example : (List.range 4).map (fun s => s * (iexp 2 1 3) / 2) = [0, 0, 1, 1] := by decide
```

**DEPENDS.** D.13, D.14, D.16, D.17, D.18, D.28, D.32, D.35, D.58.

**PROOF.** legs 1: `decide`; legs 2–4: unfold D.17's arena at the concrete data, rewrite
with D.18, evaluate in the `𝔽₄` carrier (`decide` if computable, else `simp`/`norm_num`
over the explicit multiplication table).

**SIZE.** 60 lines. **SPLIT candidate → 2** (ℕ-legs / 𝔽₄-legs).

**SOURCE.** `EFF.T1.33` (F4-JOINT frame axes), `EFF.T1.34` (all expected values, including
the full-orientation check-5 discipline "score all three entries of the canonical `μ = 3`
vector, not only the `s = 2` B-unit" — leg 3 scores all three), `EFF.T1.36` (check 2:
"Exact coefficient equality, not merely factor pattern, must be scored" — legs 3–4 are
coefficient equalities).

**TEETH.** T1 §4.2 checks 2 and 5 + all four planted teeth (`EFF.T1.45`: gauge-naive,
wrong-sign, misindexed telescope, inverse orientation — each would flip a value in legs
2–4) → **executed Lean gate**; GC-11's `e > 1 ∧ f > 1` obligation.

**ENVIRONMENT.** ENV-D5 (concrete; the `𝔽₄` carrier per the section ⚠).

---

### NODE D.66 [gate] [fresh]

**STATEMENT.** *The `q = 3` gate — the X frame (`p = 3`, `e₁ = 2, f₁ = 1, h = 1`,
`η = 2 ∈ 𝔽₃`, `u₂ = 3`) plus the T4 threshold table.* Executed checks (all over
`ℤ`/`ZMod 3`, fully `decide`-friendly):

1. **exponent tables:** `iexp 2 1` / `aexp 2 1` / `wrap 2 1` / `qexp 2 1` values on
   `k = −2…6` (incl. the carry law `qexp (a+b) = qexp a + qexp b + wrap a b` on a grid —
   D.15 executed);
2. **the telescope vector** (`𝔽₃ = ZMod 3`): `(ϑ_{1,0},…,ϑ_{1,4}) = (1, 1, 2, 2, 1)`
   (`2^{⌊s/2⌋} mod 3`), and the involution table `Θ_s·ϑ_s = 1` with `Θ = (1, 1, 2, 2, 1)`
   (`2⁻¹ = 2` in `𝔽₃`) — D.10 executed;
3. **the corrected/naive split** (the X frame's axis): D.28 clause 3's criterion fires —
   at `s ≥ 2` slots with `c_t ≠ 0`, `c_t(ϑ − 1) ≠ 0` since `ϑ₂ = 2 ≠ 1` (`decide`);
4. **the T4 threshold table:** `thresholdTheta 3 3 1 = (10, 7, 4)` on `j = 0,1,2` —
   **FR-M3's committed thresholds `[10,7,4]`** — plus the separator arithmetic: self-shadow
   pins `[12, 7, 4]` give `ν₀ = 12 > 10 = Θ₀` (untouched with slack, `ω₀ = 0` — the D.48
   fence's separator) while `j = 1, 2` attain (`7 = Θ₁`, `4 = Θ₂`) — as `ℕ∞` facts
   (`decide` on the underlying `ℕ` comparisons).

**SIGNATURE.**
```lean
-- leanfinal/Uniformity/ChapD/D66.lean
example : (List.range 5).map (fun s => (2 : ZMod 3) ^ (s * (iexp 2 1 3) / 2))
    = [1, 1, 2, 2, 1] := by decide
example : (List.range 3).map (thresholdTheta 3 3 1) = [10, 7, 4] := by decide
-- + the carry-law grid, the involution table, the D.28-criterion instances
```

**DEPENDS.** D.10, D.13, D.14, D.15, D.18, D.28, D.45, D.48.

**PROOF.** `decide` throughout (ℕ/ℤ/`ZMod 3`).

**SIZE.** 45 lines.

**SOURCE.** `EFF.T1.33` (frame X: "`p = 3, e₁ = 2, f₁ = 1, h = 1, η = 2, u₂ = 3`; corrected
versus naive p-adic split"); `EFF.T4.20` (FR-M3: thresholds `[10,7,4]`, self-shadow pins
`[12,7,4]`, `ω₀ = 0`, `ω₁, ω₂ ≠ 0` — the retained measured configuration this gate's leg 4
anchors); `EFF.T4.11` (the separator's meaning).

**TEETH.** GC-11's second prime (never `q = 2` alone); T1 wrong-sign/misindexed teeth at
`q = 3`; T4 S8 PE1(2)'s slack check ("specifically inspect FR-M3's measured slack `[12,7,4]`
against `[10,7,4]`") → **executed Lean gate**.

**ENVIRONMENT.** ENV-D5.

---

### NODE D.67 [gate] [fresh]

**STATEMENT.** *The FRAME-C regression (`p = 5`) — T3's declared battery frame, executed.*
`EFF.T3.29`'s two port instances over `𝔽₅ = ZMod 5`, at the level-1 arena
`e₁ = 2, h = 1, η = 2` (matching `res(x²/5) = 2`; `w = res(x/T) = 3`):

1. **the BR leg (`q_BR = 1`):** the tables `U = (1, 3, 2, 1, 4)`, `ϑ = (1, 1, 2, 2, 4)`
   on `s = 0…4`; the runner obligations **verified from the assembled definitions, never
   from the endpoint formula** (`EFF.T3.29`'s own instruction "without defining `U(s)` from
   the endpoint formula" — the §8.4(3) endpoint-as-input mutant's kill): `w^s = U(s)·ϑ_s`
   and `U(s) = Θ_s·w^s` for all five `s` (`3^s` vs the products, `decide`);
2. **the CMP leg (`q_CMP = 2`, `N̂(k) = x^k`, `H₀ = 6`, `D = 3`):** `χ(k) = 2^{⌊k/2⌋}`
   (D.12's `chi` at the two exponent-pair sections, residue via D.17); **the non-character
   check `χ(1)·χ(1) = 1 ≠ 2 = χ(2)`** (D.12's "no character law" fence, executed);
   `δ = χ(2) = 2`, `χ(6) = 2³ = 3`; the comparison `ρ_t = 3·ρ̂_t·2^{−t}` and
   `R(Z) = 3·R̂(Z/2)` in `𝔽₅[Z]` from D.40 at explicit `Acoef` data;
3. **the coverage record carried:** FRAME-C has both axes live (`Θ ≠ 1` at `s ≥ 2`, `w =
   3 ≠ 1`) but "its reference `T` is formal … This machine-coverage gap is not a proof gap"
   — `(T3-JOINT-OPEN)` stays open (D.64's last row); this gate does NOT claim a realized
   p-adic tower.

**SIGNATURE.**
```lean
-- leanfinal/Uniformity/ChapD/D67.lean
example : (List.range 5).map (fun s => ((3 : ZMod 5) ^ s, /- U·ϑ product -/ …))
    = … := by decide
example : ((2 : ZMod 5) ^ (1 / 2)) * ((2 : ZMod 5) ^ (1 / 2)) ≠ (2 : ZMod 5) ^ (2 / 2) := by
  decide   -- χ(1)² ≠ χ(2): the character mutant dies here
-- + the δ/χ(6) values and one explicit-coefficient (T3-CMP) instance
```

**DEPENDS.** D.08, D.10, D.12, D.17, D.38, D.39, D.40.

**PROOF.** `decide` over `ZMod 5` + `Polynomial` coefficient extensionality on leg 2's
explicit instance (small: `D = 3`).

**SIZE.** 55 lines.

**SOURCE.** `EFF.T3.29` (the whole frame, verbatim values), `EFF.T3.30` (`(T3-JOINT-OPEN)`).

**TEETH.** T3 §8.4(1) (character mutant — leg 2's `≠`), §8.4(2)–(4) (theta-free /
endpoint-as-input / inverse-orientation mutants — leg 1's two identities scored from
assembled definitions) → **executed Lean gate**; this node is the chapter's FRAME-C
executable-regression retention (GC-8: named `verification/chapD_frameC` at fleet close,
§12).

**ENVIRONMENT.** ENV-D5.

---

### NODE D.68 [gate] [fresh]

**STATEMENT.** *The chapter-D census gate* (B.86/G.78/H.99 pattern). A file with no public
declaration that (i) prints the axiom footprint of every capstone-facing chapter-D
declaration — each must print exactly `[propext, Classical.choice, Quot.sound]`; (ii)
re-executes the three gates' headline `decide` lines (the two telescope vectors, the
threshold table, the non-character check) as regression anchors; (iii) asserts non-vacuity
by `#check`ing the gate theorems and the six carrier definitions (D.44, D.55, D.59, D.60,
D.62, D.63) at their stated types.

**SIGNATURE.**
```lean
-- leanfinal/Uniformity/ChapD/D68.lean (no public declaration)
import Uniformity.ChapD
#print axioms Uniformity.Density.Gauge.NormSection.tau_cocycle            -- D.03
#print axioms Uniformity.Density.Gauge.NormSection.thetaEl_mul_varthetaEl -- D.06
#print axioms Uniformity.Density.Gauge.NormSection.tau_bracket_telescope  -- D.11
#print axioms Uniformity.Density.Gauge.iexp_aexp_spec                     -- D.13
#print axioms Uniformity.Density.Gauge.qexp_add                           -- D.15
#print axioms Uniformity.Density.Gauge.levelOneArena_vartheta             -- D.18
#print axioms Uniformity.Density.Gauge.c4_origin                          -- D.22
#print axioms Uniformity.Density.Gauge.liftC6_spec                        -- D.25
#print axioms Uniformity.Density.Gauge.gammaCoord_liftC6                  -- D.26
#print axioms Uniformity.Density.Gauge.qexp_binary_carry                  -- D.27
#print axioms Uniformity.Density.Gauge.ReadBundle.blaw                    -- D.32
#print axioms Uniformity.Density.Gauge.ReadBundle.canonical_coeff         -- D.33
#print axioms Uniformity.Density.Gauge.wtwist_monic                       -- D.34
#print axioms Uniformity.Density.Gauge.BoundaryReadPort.t3_br             -- D.38
#print axioms Uniformity.Density.Gauge.gentowW_of_ports                   -- D.44
#print axioms Uniformity.Density.Gauge.CertFrame.touched_iff_nu_eq        -- D.49
#print axioms Uniformity.Density.Gauge.CertFrame.perturb_stable           -- D.50
#print axioms Uniformity.Density.Gauge.gentowW_realized                   -- D.58
-- (ii) regression anchors: the four headline decide lines of D.65–D.67, re-executed
-- (iii) #check the gate theorems + the six carriers at their stated types
```

**DEPENDS.** every node named above (imports the roll-up).

**PROOF.** none (a census). **TEST:** compiles; every `#print axioms` line prints exactly
Lean core; every `decide` anchor evaluates; `native_decide` anywhere in chapter D is a
**stop-the-line** event (repo policy; the H.99 precedent).

**SIZE.** 55 lines.

**SOURCE.** repo policy (`CLAUDE.md` axiom census discipline); GC-6.6's gate order (this
block is step (c), executed at the leanspec stub stage before the `axiom` stubs are
signed); GC-11.

**TEETH.** this gate IS the chapter's teeth roll-up; §12's disposition table is its index.

**ENVIRONMENT.** the census imports the roll-up; no `variable`s.

---
<!-- RESUME: §10 COMPLETE (D.65–D.68). 68 nodes total. Next = closing sections: §11 DAG additions (generate spec/DAG_BLUEPRINT_D.tsv), §12 leanspec stubs, §13 TEETH, §14 cross-read queue, + A-1 index renumber amendment -->

<!-- CHAP-D APPEND POINT — do not remove; sections are appended here in order -->
