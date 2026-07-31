# O13 Phase-B attempt, REV 2 — skeleton/menu finiteness at general n (leaf O-13 / node D-12)

*(2026-07-31, Phase-B prover, THE MATHEMATICAL COMPLETION campaign. Rev 2 of
`O13_phaseB_attempt.md`, responding to the hostile verification V8
(`V8_o13_verify.jsonl`; verdict SOUND-WITH-GAPS — Theorems 1–3 + 5 verified correct,
no critical error, all findings justification gaps). Companion self-contained verifier
package: `O13_phaseB_verifybrief_rev2.md`. Falsifier artifact unchanged:
`O13_menu_check.py` (all checks pass, n ≤ 6). This rev supersedes rev 1 as the
statement of record; rev 1 is retained for the audit trail.)*

## What changed in rev 2 (the complete delta)

The three charged repairs, plus closure of V8's §1 gaps:

1. **(a) The "wildness enters only through values" claim is NARROWED to exactly what is
   proved.** Theorem-grade content: the displayed combinatorial index sets — 𝒮_n^raw,
   the menu graph, Sk(n) — are p-free (Theorems 1–3), and run lengths enter only as a
   collapse PARAMETER with the p-free domain ℤ≥1 ∪ {∞} (new D10). The broader division
   ("ALL p-dependence of the assembled theory sits in values on p-free parameter
   domains") is now the LABELED AMBIENT CLAIM **(VAL-DIV)** — conjecture status, a
   forward pointer to node **D-3 (UNRAM-TRANSFER)** (with O-12/D-6 owning the solve's
   coefficient/denominator side) — consumed by NOTHING in this package (§4). The
   heights/slopes domain sentence is DELETED from Theorem 3's statement (V8 §6 was
   right: it was semantic import, not a consequence of the typing clauses). Theorem 5's
   role is narrowed to exactly the discriminant/different budget (V8 §9).
2. **(b) (COMP) stays the explicit named condition; its chain is now displayed in
   full**: Corollary ⇐ (COMP) ⇐ [T-4 SP-COMP + the §D4-R branching architecture] ⇐ the
   one undischarged residual, the D4R.0-K(c) verdict-pin TOTALITY (owner [3t] VP).
   Consumers of the completeness clause inherit the whole chain; Theorems 1, 2, 3, 5
   and every lemma consume none of it.
3. **(c) The misdescribed O3 resummation display — CHECKED, ABSENT.** V7 (the sibling
   O-12 verification) flagged the display "Σ_{L≥1} q^{−EL} = 1/(q^E−1)" for the O3
   self-loop family (the correct kernel resummation there is
   Σ_{L≥1} κ₀^{L−1}κ₁ = (q−1)/(q^E−1)). That display appears NOWHERE in the O13 texts
   (grep-verified). The one adjacent phrase (rev 1 §4 item 3: depth distributions
   "resummed by the solve's matrix fixpoint (I − K_e)^{−1}") asserted no formula but
   belonged to the broad claim; it is retyped under (VAL-DIV) with no resummation value
   or mechanism asserted in this package.
4. **V8 §1 gap closures — run collapse made formal.** New **D9** (pre-skeletons:
   possibly-infinite labeled annotated trees satisfying (S1)(S2)(S3)(S5)); new **Lemma
   E** (an equal-label child edge witnesses a self-loop directly via (S2), and such a
   child is an ONLY child); new **D10** (run-collapse by the explicit ENTRY-NODE
   construction — a definition, not an informal quotient); **Lemma B's scope extended
   to pre-skeletons** (its proof never used finiteness — V8 said exactly this); new
   **Lemma T′**: the collapse of EVERY pre-skeleton, infinite branches included, is a
   member of Sk(n) (depth ≤ 6n² by Theorem 2(iii), branching ≤ n by Lemma B + E, hence
   ≤ Σ_{d<6n²} n^d nodes — finite with no König appeal). This closes V8's three §1
   gaps: the undefined tree collapse, the singleton-run overstatement ("a run's letter
   has a self-loop" — the tree-level argument now uses only equal-label EDGES, where
   (S2) gives the self-loop outright), and the missing whole-tree finiteness step.

Everything else — the falsifier table, Theorems 1/2/3/5 statements and proofs, the
Lemma B/L ledgers — carries over from rev 1 unchanged in substance.

## VERDICT: REPAIRED — PROVED at the narrowed scope, conditionality displayed

The leaf's claim is proved at general n in the T-4 (§M-SPECIES) vocabulary at three
nested levels — letters, branch words, TREE skeletons — each finite with an explicit
p-free bound, now including the formal collapse theorem (Lemma T′) that node D-12
demanded. Unconditional: Theorems 1–3, Lemmas B/E/L/T/T′, the Serre envelope (Thm 5),
given the dual-accepted §B2-DEF/§M-SPECIES/§D4-R vocabulary as DEFINITIONS. Conditional
(inherited only): Theorem 4 (completeness) on the (COMP) chain above. Ambient (not a
theorem here): (VAL-DIV). The Serre bound is NOT consumed by Theorems 1–4; its live
role is the value-side envelope for the discriminant/different budget specifically
(§4) — the rev-1 phrasing that made it certify ALL forgotten budgets is withdrawn.

## §0 Grounding (what this leaf is, and who consumes it)

The campaign's target (U-GEN)(iii) produces each density R_σ as the σ-entry of a finite
linear solve (I − K(q))C = b(q) over ℚ(q) "whose state menu, coefficients, and
non-vanishing pivots carry NO dependence on p". O-13 owes the STATE-MENU half — and
rev 2 is explicit that it delivers ONLY that half: the index set of the solve (species
letters, menu edges, tree shapes) is ONE finite list serving every prime, wild
included. The coefficient and pivot halves of (U-GEN)(iii) are the territory of
O-12/D-6 (cyclotomic-type denominators, proved there at the 𝔅_n scope) and D-3
(unramified-base semantic transfer); this package neither states nor uses them. The
Lean-side consumer is the standing hypothesis row `hfin : Finite (Skeleton n)`
(consumed by `MovesV/TV_E2.lean`, `TV_G3.lean`; `Skeleton n` := a catalogue-membered
`MovesSp.Species`, i.e. exactly a letter of 𝒮_n^raw — so `hfin` = Theorem 1; it is
Lean-proved only at n = 1, 3 via the sealed catalogue, which is why the tree lists the
leaf as open at general n).

Prior state: T-4 (§M-SPECIES, dual-accepted 2026-07-27) already holds SP-FIN (letters
finite, ≤ (n+2)^{n²+3n+12}, p-free by typing) and SP-DAG (loop-collapsed menu graph is
a DAG; collapsed walks ≤ 6n² letters). New in O13 (rev 1 + rev 2): the tree-level
composition — branching (B), leaf budget (L), the FORMAL run collapse (E, D9/D10, T′),
the skeleton count (Thm 3) — plus the narrowed wild-corner analysis with Serre pinned.

## §1 FALSIFIER FIRST (unchanged from rev 1) — all checks PASS

`O13_menu_check.py` enumerates 𝒮_n^raw mechanically from the (G1)–(G6)+(B1)–(B5)
clauses as transcribed in `lean/LeanUrat/MovesSp/Defs.lean`, builds the menu graph, and
checks the load-bearing lemmas. Results (2026-07-31, python3, this machine):

| n | \|𝒮_n^raw\| | reachable stages | longest collapsed path | SP-DAG bound 6n² | menu edges |
|---|------------|------------------|------------------------|------------------|-----------|
| 1 | 1          | 1                | 1                      | 6                | 0         |
| 2 | 15         | 5                | 4                      | 24               | 21        |
| 3 | **53**     | 8                | 6                      | 54               | 121       |
| 4 | 197        | 18               | 8                      | 96               | 616       |
| 5 | 509        | 26               | 10                     | 150              | 2246      |
| 6 | 1460       | 36               | 12                     | 216              | 8224      |

- Sealed-catalogue reproduction: |𝒮₃^raw| = 53 exactly, over exactly the 8 sealed
  stages with the sealed group counts. |𝒮₁| = 1 (= Lean's `sk1`).
- Self-loop characterization (SP-DAG(i)): at every n ≤ 6, {s : s ∈ SUCC(s)} = exactly
  the full POST-REC letters, every field forced, uniqueness per stage confirmed.
- Rank monotonicity (SP-DAG(ii)): ρ = (D, tagord, n−W, 1−[full]) strictly
  lex-increases along ALL non-self-loop edges (8224/8224 at n = 6) ⇒ DAG confirmed.
- Headroom: n = 4 gives 197 letters vs the crude bound; longest collapsed path 8 vs 96.
  Longest path = 2n for 2 ≤ n ≤ 6 stands as an EMPIRICAL pattern (conjecture, consumed
  nowhere; 6n² is what is proved and used).
- Encoding-range audit: every letter's SP-FIN encoding entries lie in {0..n+1}.
- Window-locality observation: per-stage letter count depends only on W
  (1, 6, 21, 68, 189, 513 for W = 1..6).

No check failed; the falsifier found nothing to refute.

## §2 The statement package (complete self-contained proofs in the rev-2 brief)

All objects as in §M-SPECIES SP.1–SP.4 (= `MovesSp/Defs.lean`). Fix n ≥ 1.

- **Theorem 1 (letters; = T-4 SP-FIN, known, restated).** 𝒮_n^raw is finite,
  |𝒮_n^raw| ≤ (n+2)^{n²+3n+12}, defined by clauses mentioning no prime.
  [Discharges the math of the Lean row `hfin : Finite (Skeleton n)`.]
- **Theorem 2 (branch words; = T-4 SP-DAG, known, restated).** Self-loops = exactly the
  full POST-REC letters (all fields forced); ρ strictly increases along every other
  edge; collapsed walks have ≤ 6n² pairwise-distinct letters; collapsed-word menu
  ≤ (|𝒮_n^raw|+1)^{6n²}.
- **D9 (pre-skeletons, NEW in rev 2).** A pre-skeleton is a rooted tree — FINITE OR
  INFINITE — with nodes labeled by 𝒮_n^raw letters and leaves partially annotated by
  {z, ep, ns}, satisfying (S1) root label a root letter, (S2) edges are menu edges,
  (S3) sibling coherence, (S5) annotations on leaves only. (A skeleton = a finite
  pre-skeleton also satisfying (S4) no equal-label edge.)
- **Lemma B (branching; rev-2 scope: pre-skeletons).** In any pre-skeleton, every node
  has ≤ μ ≤ n children (μ = its label's selection multiplicity). The rev-1 proof is
  unchanged — it uses only (S2)/(S3) and the letter clauses AT the node, never
  finiteness of the tree (this is the scope extension V8 identified as available).
- **Lemma E (equal-label children, NEW in rev 2).** If a child ν′ of ν has
  s(ν′) = s(ν) = s, then s → s by (S2) alone — a self-loop, so s is full POST-REC with
  all fields forced (Thm 2) — and ν′ is the ONLY child of ν: the child window is
  W(s) ≥ 2 so no sibling is terminal; the group's λ = {(1, W)} caps the group at one
  child; the group interval [0, μ) leaves no room for a second group.
- **D10 (run-collapse, NEW in rev 2 — the formal definition).** ENTRY nodes of a
  pre-skeleton T̂: the root, plus every node whose label differs from its parent's.
  T̄ := the tree on entry nodes, parent = deepest entry strict-ancestor, labels
  inherited; run(x) := the maximal chain of equal-label descendants below entry node x
  (a chain by Lemma E); run length |run(x)| ∈ ℤ≥1 ∪ {∞} is a PARAMETER, not data of T̄;
  annotation of x := the annotation of run(x)'s final member when that is an annotated
  leaf.
- **Lemma L (leaf budget; skeletons).** Every skeleton has ≤ n leaves, ≤ 6n³ nodes.
  (Rev-1 proof unchanged; applied only to finite trees.)
- **Lemma T (walk tails; rev-2 wording fixed).** Any (even infinite) walk in the menu
  graph has ≤ 6n² maximal runs of consecutive equal letters; an infinite walk is
  eventually constant. Every run OF LENGTH ≥ 2 contains an edge s → s, so its letter
  has a self-loop (the rev-1 phrase claiming this of every run, singleton runs
  included, is withdrawn — V8 §1; no argument ever needed the singleton case).
- **Lemma T′ (the collapse theorem, NEW in rev 2 — node D-12's demanded object).** For
  EVERY pre-skeleton T̂ — infinite branches and non-terminating loci included — T̄ is a
  skeleton: (S1)–(S5) hold, every branch has ≤ 6n² nodes (its label sequence is a
  collapsed walk), every node has ≤ n children (Lemma B at the run's final member;
  infinite runs are childless in T̄ by Lemma E), hence |T̄| ≤ Σ_{d<6n²} n^d < ∞ — no
  König, no choice. So T̄ ∈ Sk(n).
- **Theorem 3 (skeletons; statement NARROWED in rev 2).** Sk(n) — finite rooted trees,
  𝒮_n^raw-labeled, menu-edged, sibling-coherent, run-collapsed, leaves optionally
  annotated — is finite: |Sk(n)| ≤ (n+2)^{7n³(n²+3n+16)}, and p-independent: no clause
  of D1–D10 mentions p. [The rev-1 sentence placing height/slope parameters on named
  p-free domains is REMOVED from this statement: it was ambient semantic import (V8
  §6), now part of (VAL-DIV) in §4. What remains theorem-grade about parameters: run
  lengths enter only as the D10 parameter with domain ℤ≥1 ∪ {∞}.]
- **Theorem 4 (completeness, conditional — inherited only).** For every p and monic
  degree-n f over ℤ_p, the run-collapse of T_can(f)'s catalogue-word tree ∈ Sk(n).
  Chain: Theorem 4 ⇐ (COMP) [realized trees are pre-skeletons] ⇐ T-4 SP-COMP (per-read
  letter/edge membership) + §D4-R branching architecture (sibling coherence) ⇐ the
  D4R.0-K(c) verdict-pin totality residual (owner [3t] VP) — the ONE open link, already
  on the ledger; rev 2 adds no new conditionality. Sk(n) is a SUPERSET menu: clauses
  are necessary conditions; emptiness of a shape at a given p is value data,
  zero-extended by the consumer.
- **Theorem 5 (Serre envelope; role narrowed in rev 2).** See §4.

## §3 Proof notes (full verbatim proofs live in the rev-2 brief §§2–4)

Lemma B, Lemma L, Theorems 1/2/3/5: bodies unchanged from rev 1 (V8 verified each
correct; Thm 3's STATEMENT narrowed as above, its counting proof untouched). New
bodies (E, D10 well-definedness, T′) are in the brief §4; the two load-bearing new
steps, displayed:

**Lemma E's only-child step.** s full ⇒ (Thm 2(i)) e(s) = 1, s₀(s) = 0, ℓ(s) = W(s),
λ(s) = {(1, W)}, sel = (1, W) ⇒ μ(ν) = W(s), and every child of ν sits at window
W′ = μ = W(s) ≥ 2, so no child is terminal ((C5)). The child ν′ carries s itself, so
its group's side data is s's: interval [0, 1·W) = [0, μ) — full span. A second child in
the SAME group must select a member of λ = {(1, W)} within its multiplicity (one),
already taken by ν′; a second GROUP needs a disjoint nonempty subinterval of [0, μ) —
none exists. ∎

**Lemma T′'s finiteness step.** Every root-to-node path in T̄ spells consecutive
DISTINCT (S4, by run-maximality) menu-edge-related (S2, via the run's final member)
letters — a collapsed walk — so has ≤ 6n² nodes (Thm 2(iii)). Every T̄-node has ≤ n
children: its T̄-children are exactly the T̂-children of its run's final member when
the run is finite (Lemma E forces every non-final member's unique child to be
run-internal) — bounded by Lemma B at that member — and NONE when the run is infinite.
Nodes at depth d number ≤ n^d by induction; total ≤ Σ_{d=0}^{6n²−1} n^d, finite. (S1),
(S3), (S5) transfer clause-by-clause (brief §4); Lemma L then gives ≤ n leaves,
≤ 6n³ nodes. ∎

## §4 The wild corner (Theorem 5) — the proved/ambient boundary, drawn (rev 2)

**The pinned classical statement (known — Serre, Local Fields (GTM 67), Ch. III §6,
Prop. 13; verified numerically tight in `L5fix_complete.md` §5(b), e.g. x⁴−2/ℚ₂:
d = 11 = 3 + 4·2).** L/K finite separable totally ramified of degree e, K complete
discretely valued, residue char p: e − 1 ≤ d = v_L(𝔇_{L/K}) ≤ e − 1 + v_L(e), tame iff
p ∤ e. Tower corollary for a leaf of degree d° = e·f ≤ n over an absolutely unramified
base: v_K(disc) ≤ f(e−1) + f·e·v_p(e) ≤ (d°−1) + d°·v_p(d°), so
B(n,p) := max_{d°≤n}[(d°−1) + d°·v_p(d°)] ≤ (n−1) + n·log₂ n — p-uniform, since
wildness fires only at p | e ≤ n.

**Theorem-grade wild-corner facts (what this package PROVES):**
1. No clause of D1–D10 records a different exponent, discriminant valuation, slope
   height, digit value, or run length; run lengths appear only as the D10 parameter,
   domain ℤ≥1 ∪ {∞}, p-free. D1–D10 mention no prime (inspection).
2. Nothing in D1–D10 or Theorems 1–3 assumes tame ramification; no clause degenerates
   at p ≤ n. The residual pattern λ is well-typed at every p (residue fields of local
   fields are finite hence perfect; repeated factors ride the multiplicity coordinate).
3. Theorem 5: the discriminant/different budget of any realized degree-≤ n extension
   obeys the p-uniform envelope (n−1) + n·log₂ n, all wildness confined to the
   d°·v_p(d°) term. This bounds ONE family of forgotten values — it does NOT bound run
   lengths (which may be ∞), heights, or distributions, and it is consumed by NO
   theorem of this package (audit-checked independence; the June-vocabulary proof B-6
   genuinely consumed it for its depth cap — the modern depth cap is Thm 2(iii), pure
   integer combinatorics).
4. The stage laws (B1)–(B5), D′ = e·g·D etc. carry no tameness hypothesis — they
   transcribe §B2-DEF move laws proved uniformly in p (dual-accepted; interface).

**(VAL-DIV) — the value-division picture. AMBIENT CLAIM: labeled CONJECTURE at this
package's level; forward pointer to node D-3 (UNRAM-TRANSFER), co-owned by O-12/D-6
for the solve's coefficient side. Consumed by NOTHING in this package.** Intended
statement: every p-dependence of the assembled density theory sits in VALUES attached
to the p-free index sets — which letters/skeletons carry mass at a given p, the masses
as functions of the residue cardinality q, and the parameter distributions on p-free
domains (heights in ℕ², normalized slopes in (1/lcm(1..n))ℤ, run lengths in
ℤ≥1 ∪ {∞}) — never in 𝒮_n^raw, the menu graph, or Sk(n). Of this, O13 PROVES exactly
the index-set half (Theorems 1–3) plus the run-length domain clause (D10); the
height/slope domain clauses and the exhaustiveness of the division are semantic
statements about the factorization process that this package neither defines nor
proves (V8 §6/§9 — accepted in full). Likewise "the linear solve is a single
p-independent finite system" is narrowed to: the solve's INDEX SET is single, finite,
p-independent (Theorems 1–3); coefficient p-independence is (U-GEN)(iii)'s other half,
owned by O-12/D-6 + D-3. No resummation formula or mechanism is asserted here (the
rev-1 "(I − K_e)^{−1}" gloss is retired to this paragraph; cf. delta item (c)).

## §5 Conditionality ledger, labels, consumers (rev 2)

- **Unconditional** (over the dual-accepted §B2-DEF/§M-SPECIES/§D4-R vocabulary as
  DEFINITIONS): Theorems 1, 2, 3, 5; Lemmas B, E, L, T, T′; D9/D10 well-definedness.
  No new axiom, no new open lemma.
- **Conditional, inherited only**: Theorem 4, on the displayed chain
  (COMP) ⇐ SP-COMP + §D4-R architecture ⇐ D4R.0-K(c) verdict-pin totality (owner [3t]
  VP). Nothing else consumes (COMP).
- **Ambient, consumed by nothing here**: (VAL-DIV) — conjecture label, D-3 pointer.
- **Labels**: Thm 1/Thm 2 = (a) known within the campaign (T-4, dual-accepted),
  restated with complete proofs in the brief. Serre Prop. 13 + B(n,p) = (a) known
  (literature + June B-6). Lemmas B/L/T + Thm 3 = (c) claimed new (rev 1, V8-verified
  correct). Lemma E, D9/D10, Lemma T′ = (c) claimed new (rev 2 — the D-12 object,
  closing V8 §1). Longest-collapsed-path = 2n: numerically-supported conjecture,
  consumed nowhere.
- **Consumers**: `hfin : Finite (Skeleton n)` (TV_E2/TV_G3) is mathematically
  discharged by Theorem 1 at every n (Lean formalization of the encoding injection =
  natural follow-up, NOT done here; no Lean edits per charge). (U-GEN)(iii)'s
  STATE-MENU clause consumes Thms 1–3; its coefficient/pivot clauses are NOT certified
  by this leaf (rev-2 correction of the rev-1 gloss). [1v]/CTS consume the word menu
  (Thm 2); [3]'s tree assembly consumes Sk(n) (Thms 3–4 + T′). Node D-12 =
  supplied (Lemma T′ + Thm 3); D-12r (completeness residue) = Theorem 4's chain,
  a SEPARATE node, untouched here.

## §6 Files

- `lean/notes/openmath/O13_phaseB_attempt_rev2.md` — this note (statement of record).
- `lean/notes/openmath/O13_phaseB_verifybrief_rev2.md` — rev-2 self-contained verifier
  package (all definitions incl. D9/D10 unfolded, complete proofs, no repo pointers).
- `lean/notes/openmath/O13_phaseB_attempt.md`, `O13_phaseB_verifybrief.md` — rev 1,
  audit trail. `V8_o13_verify.jsonl` — the hostile pass this rev answers.
- `lean/notes/openmath/O13_menu_check.py` — falsifier (unchanged; all checks pass).
